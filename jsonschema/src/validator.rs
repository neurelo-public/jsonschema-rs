use crate::{
    error::ErrorIterator,
    keywords::BoxedValidator,
    output::Annotations,
    paths::{AbsolutePath, InstancePath, JSONPointer},
    schema_node::SchemaNode,
    ValidationError,
};
use serde_json::Value;
use std::{cmp::Ordering, collections::VecDeque, fmt};

/// The Validate trait represents a predicate over some JSON value. Some validators are very simple
/// predicates such as "a value which is a string", whereas others may be much more complex,
/// consisting of several other validators composed together in various ways.
///
/// Much of the time all an application cares about is whether the predicate returns true or false,
/// in that case the `is_valid` function is sufficient. Sometimes applications will want more
/// detail about why a schema has failed, in which case the `validate` method can be used to
/// iterate over the errors produced by this validator. Finally, applications may be interested in
/// annotations produced by schemas over valid results, in this case the `apply` method can be used
/// to obtain this information.
///
/// If you are implementing `Validate` it is often sufficient to implement `validate` and
/// `is_valid`. `apply` is only necessary for validators which compose other validators. See the
/// documentation for `apply` for more information.
pub(crate) trait Validate: Send + Sync + core::fmt::Display {
    fn get_location(&self, instance_path: &InstancePath) -> Location;

    fn validate<'instance>(
        &self,
        instance: &'instance Value,
        instance_path: &InstancePath,
    ) -> ErrorIterator<'instance>;

    // The same as above, but does not construct ErrorIterator.
    // It is faster for cases when the result is not needed (like anyOf), since errors are
    // not constructed
    fn is_valid(&self, instance: &Value) -> bool;

    /// `apply` applies this validator and any sub-validators it is composed of to the value in
    /// question and collects the resulting annotations or errors. Note that the result of `apply`
    /// is a `PartialApplication`.
    ///
    /// What does "partial" mean in this context? Each validator can produce annotations or errors
    /// in the case of successful or unsuccessful validation respectively. We're ultimately
    /// producing these errors and annotations to produce the "basic" output format as specified in
    /// the 2020-12 draft specification. In this format each annotation or error must include a
    /// json pointer to the keyword in the schema and to the property in the instance. However,
    /// most validators don't know where they are in the schema tree so we allow them to return the
    /// errors or annotations they produce directly and leave it up to the parent validator to fill
    /// in the path information. This means that only validators which are composed of other
    /// validators must implement `apply`, for validators on the leaves of the validator tree the
    /// default implementation which is defined in terms of `validate` will suffice.
    ///
    /// If you are writing a validator which is composed of other validators then your validator will
    /// need to store references to the `SchemaNode`s which contain those other validators.
    /// `SchemaNode` stores information about where it is in the schema tree and therefore provides an
    /// `apply_rooted` method which returns a full `BasicOutput`. `BasicOutput` implements `AddAssign`
    /// so a typical pattern is to compose results from sub validators using `+=` and then use the
    /// `From<BasicOutput> for PartialApplication` impl to convert the composed outputs into a
    /// `PartialApplication` to return. For example, here is the implementation of
    /// `IfThenValidator`
    ///
    /// ```rust,ignore
    /// // Note that self.schema is a `SchemaNode` and we use `apply_rooted` to return a `BasicOutput`
    /// let mut if_result = self.schema.apply_rooted(instance, instance_path);
    /// if if_result.is_valid() {
    ///     // here we use the `AddAssign` implementation to combine the results of subschemas
    ///     if_result += self
    ///         .then_schema
    ///         .apply_rooted(instance, instance_path);
    ///     // Here we use the `From<BasicOutput> for PartialApplication impl
    ///     if_result.into()
    /// } else {
    ///     self.else_schema
    ///         .apply_rooted(instance, instance_path)
    ///         .into()
    /// }
    /// ```
    ///
    /// `BasicOutput` also implements `Sum<BasicOutput>` and `FromIterator<BasicOutput<'a>> for PartialApplication<'a>`
    /// so you can use `sum()` and `collect()` in simple cases.
    fn apply<'instance>(
        &self,
        instance: &'instance Value,
        instance_path: &InstancePath,
    ) -> PartialApplication<'instance> {
        let errors: Vec<_> = self.validate(instance, instance_path).collect();
        if errors.is_empty() {
            PartialApplication::valid_empty(self.get_location(instance_path))
        } else {
            PartialApplication::invalid_empty(self.get_location(instance_path), errors)
        }
    }
}

/// Location that correlates a schema node to an instance node
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Location {
    pub(crate) keyword_location: JSONPointer,
    pub(crate) instance_location: JSONPointer,
    pub(crate) absolute_keyword_location: Option<AbsolutePath>,
}

impl Location {
    pub(crate) fn new(
        keyword_location: JSONPointer,
        instance_location: JSONPointer,
        absolute_keyword_location: Option<AbsolutePath>,
    ) -> Self {
        Self {
            keyword_location,
            instance_location,
            absolute_keyword_location,
        }
    }
}

#[derive(Debug, PartialEq, Default)]
pub(crate) struct ApplicationStats {
    /// If a const or enum matches the value
    matches_enum: bool,
    /// Keep track of possible const or enum values
    possible_enums: Vec<Value>,
    /// Property name matches
    properties_matches: usize,
    /// Property and value matches
    properties_value_matches: usize,
    /// The value of a property matches an enum or a const
    primary_value_matches: usize,
}

/// The result of applying a validator to an instance. As explained in the documentation for
/// `Validate::apply` this is a "partial" result because it does not include information about
/// where the error or annotation occurred.
#[derive(Debug)]
pub(crate) enum PartialApplication<'a> {
    Valid {
        /// Location that produced this partial application
        location: Location,
        /// Annotations produced by this validator
        annotations: Option<Annotations<'a>>,
        /// Any outputs produced by validators which are children of this validator
        child_results: VecDeque<PartialApplication<'a>>,
        /// Stats that will be used to figure out best match
        stats: ApplicationStats,
    },
    Invalid {
        /// Location that produced this partial application
        location: Location,
        /// Errors which caused this schema to be invalid
        errors: Vec<ValidationError<'a>>,
        /// Any error outputs produced by child validators of this validator
        child_results: VecDeque<PartialApplication<'a>>,
        /// Stats that will be used to figure out best match
        stats: ApplicationStats,
    },
}

impl<'a> PartialApplication<'a> {
    /// Create an empty `PartialApplication` which is valid
    pub(crate) fn valid(
        location: Location,
        annotations: Option<Annotations<'a>>,
    ) -> PartialApplication<'a> {
        PartialApplication::Valid {
            location,
            annotations,
            child_results: VecDeque::new(),
            stats: ApplicationStats::default(),
        }
    }

    /// Create an empty `PartialApplication` which is valid
    pub(crate) fn valid_empty(location: Location) -> PartialApplication<'a> {
        PartialApplication::Valid {
            location,
            annotations: None,
            child_results: VecDeque::new(),
            stats: ApplicationStats::default(),
        }
    }

    /// Create  `PartialApplication` which is invalid
    pub(crate) fn invalid(
        location: Location,
        errors: Vec<ValidationError<'a>>,
        child_results: VecDeque<PartialApplication<'a>>,
    ) -> PartialApplication<'a> {
        PartialApplication::Invalid {
            errors,
            location,
            child_results: child_results,
            stats: ApplicationStats::default(),
        }
    }

    /// Create an empty `PartialApplication` which is invalid
    pub(crate) fn invalid_empty(
        location: Location,
        errors: Vec<ValidationError<'a>>,
    ) -> PartialApplication<'a> {
        Self::invalid(location, errors, VecDeque::new())
    }

    /// A shortcut to check whether the partial represents passed validation.
    #[must_use]
    pub(crate) const fn is_valid(&self) -> bool {
        match self {
            Self::Valid { .. } => true,
            Self::Invalid { .. } => false,
        }
    }

    /// Set the annotation that will be returned for the current validator. If this
    /// `PartialApplication` is invalid then this method does nothing
    pub(crate) fn annotate(&mut self, new_annotations: Annotations<'a>) {
        match self {
            Self::Valid { annotations, .. } => *annotations = Some(new_annotations),
            Self::Invalid { .. } => {}
        }
    }

    /// Set the error that will be returned for the current validator. If this
    /// `PartialApplication` is valid then this method converts this application into
    /// `PartialApplication::Invalid`
    pub(crate) fn mark_errored(&mut self, error: ValidationError<'a>) {
        match self {
            Self::Invalid { errors, .. } => errors.push(error),
            Self::Valid {
                location, stats, ..
            } => {
                *self = Self::Invalid {
                    location: location.clone(),
                    errors: vec![error],
                    child_results: VecDeque::new(),
                    stats: std::mem::take(stats),
                }
            }
        }
    }

    pub(crate) fn get_errors(&mut self) -> Vec<ValidationError<'a>> {
        match self {
            Self::Valid { .. } => vec![],
            Self::Invalid { errors, .. } => std::mem::take(errors),
        }
    }

    pub(crate) fn get_stats(&mut self) -> &mut ApplicationStats {
        match self {
            Self::Valid { stats, .. } => stats,
            Self::Invalid { stats, .. } => stats,
        }
    }

    pub(crate) fn merge(&mut self, other: &mut Self) {
        for error in other.get_errors() {
            self.mark_errored(error);
        }

        let stats = self.get_stats();
        let other_stats = other.get_stats();

        stats.properties_matches += other_stats.properties_matches;
        stats.primary_value_matches += other_stats.primary_value_matches;
    }

    pub(crate) fn merge_enum_values(&mut self, other: &mut Self) {
        let stats = self.get_stats();
        let other_stats = other.get_stats();

        if !stats.matches_enum
            && !other_stats.matches_enum
            && !stats.possible_enums.is_empty()
            && !other_stats.possible_enums.is_empty()
        {
            stats
                .possible_enums
                .extend(std::mem::take(&mut other_stats.possible_enums));
        }
    }

    pub(crate) fn merge_matches_enum(&mut self, other: &mut Self) {
        let stats = self.get_stats();
        let other_stats = other.get_stats();

        stats.matches_enum |= other_stats.matches_enum;
        stats
            .possible_enums
            .extend(std::mem::take(&mut other_stats.possible_enums));
    }

    pub(crate) fn merge_property_match(&mut self, other: &mut Self) {
        for error in other.get_errors() {
            self.mark_errored(error);
        }

        let stats = self.get_stats();
        let other_is_valid = other.is_valid();
        let other_stats = other.get_stats();

        stats.properties_matches += 1;
        if other_stats.matches_enum || (other_is_valid && other_stats.properties_matches > 0) {
            stats.properties_value_matches += 1;
        }
        if other_stats.matches_enum && other_stats.possible_enums.len() == 1 {
            stats.primary_value_matches += 1;
        }
    }

    pub(crate) fn mark_valid_enum(&mut self) {
        match self {
            Self::Valid { stats, .. } => stats.matches_enum = true,
            Self::Invalid { .. } => {}
        }
    }

    pub(crate) fn mark_property_value_matches(&mut self) {
        match self {
            Self::Valid { stats, .. } => stats.properties_value_matches += 1,
            Self::Invalid { stats, .. } => stats.properties_value_matches += 1,
        }
    }

    pub(crate) fn add_possible_enum(&mut self, value: impl Into<Value>) {
        match self {
            Self::Valid { stats, .. } => stats.possible_enums.push(value.into()),
            Self::Invalid { stats, .. } => stats.possible_enums.push(value.into()),
        }
    }
}

impl<'a> PartialOrd for ApplicationStats {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self.matches_enum.partial_cmp(&other.matches_enum) {
            Some(Ordering::Equal) => {}
            ord => return ord,
        }
        match self
            .primary_value_matches
            .partial_cmp(&other.primary_value_matches)
        {
            Some(Ordering::Equal) => {}
            ord => return ord,
        }
        match self
            .properties_value_matches
            .partial_cmp(&other.properties_value_matches)
        {
            Some(Ordering::Equal) => {}
            ord => return ord,
        }
        let xx = self
            .properties_matches
            .partial_cmp(&other.properties_matches);

        xx
    }
}

impl<'a> PartialEq for PartialApplication<'a> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::Valid { stats, .. },
                Self::Valid {
                    stats: other_stats, ..
                },
            )
            | (
                PartialApplication::Invalid { stats, .. },
                PartialApplication::Invalid {
                    stats: other_stats, ..
                },
            ) => matches!(stats.partial_cmp(other_stats), Some(Ordering::Equal)),
            (_, _) => false,
        }
    }
}

impl<'a> PartialOrd for PartialApplication<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (
                Self::Valid { stats, .. },
                Self::Valid {
                    stats: other_stats, ..
                },
            )
            | (
                PartialApplication::Invalid { stats, .. },
                PartialApplication::Invalid {
                    stats: other_stats, ..
                },
            ) => stats.partial_cmp(other_stats),
            (_, PartialApplication::Valid { .. }) => Some(Ordering::Less),
            (PartialApplication::Valid { .. }, _) => Some(Ordering::Greater),
        }
    }
}

impl fmt::Debug for dyn Validate + Send + Sync {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_string())
    }
}

pub(crate) fn format_validators<'a, I: ExactSizeIterator + Iterator<Item = &'a BoxedValidator>>(
    mut validators: I,
) -> String {
    match validators.len() {
        0 => "{}".to_string(),
        1 => {
            // Unwrap is okay due to the check on len
            let validator = validators.next().unwrap();
            let name = validator.to_string();
            match name.as_str() {
                // boolean validators are represented as is, without brackets because if they
                // occur in a vector, then the schema is not a key/value mapping
                "true" | "false" => name,
                _ => format!("{{{}}}", name),
            }
        }
        _ => format!(
            "{{{}}}",
            validators
                .map(|validator| format!("{:?}", validator))
                .collect::<Vec<String>>()
                .join(", ")
        ),
    }
}

pub(crate) fn format_iter_of_validators<'a, G, I>(validators: I) -> String
where
    I: Iterator<Item = G>,
    G: ExactSizeIterator + Iterator<Item = &'a BoxedValidator>,
{
    validators
        .map(format_validators)
        .collect::<Vec<String>>()
        .join(", ")
}

pub(crate) fn format_key_value_validators(validators: &[(String, SchemaNode)]) -> String {
    validators
        .iter()
        .map(|(name, node)| format!("{}: {}", name, format_validators(node.validators())))
        .collect::<Vec<String>>()
        .join(", ")
}

/// Apply and modify resulting application
#[macro_export]
macro_rules! apply_with_side_effect {
    ($F:ident) => {
        fn apply<'instance>(
            &self,
            instance: &'instance Value,
            instance_path: &InstancePath,
        ) -> PartialApplication<'instance> {
            use crate::validator::PartialApplication;
            use crate::ValidationError;

            let errors: Vec<ValidationError> = self
                .validate(instance, instance_path)
                .map(ValidationError::from)
                .collect();
            if errors.is_empty() {
                let mut application =
                    PartialApplication::valid_empty(self.get_location(instance_path));

                application.$F();

                application
            } else {
                PartialApplication::invalid_empty(self.get_location(instance_path), errors)
            }
        }
    };
}

/// Get the node location from the schema path
#[macro_export]
macro_rules! get_location_from_path {
    () => {
        fn get_location(&self, instance_path: &InstancePath) -> Location {
            Location::new(self.schema_path.clone(), instance_path.into(), None)
        }
    };
}

/// Get the node location from the node
#[macro_export]
macro_rules! get_location_from_node {
    () => {
        fn get_location(&self, instance_path: &InstancePath) -> Location {
            self.node.get_location(instance_path)
        }
    };
}

/// Get the node location from the schema node
#[macro_export]
macro_rules! get_location_from_schema {
    () => {
        fn get_location(&self, instance_path: &InstancePath) -> Location {
            self.schema.get_location(instance_path)
        }
    };
}
