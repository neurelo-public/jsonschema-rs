use crate::{
    compilation::{compile_validators, context::CompilationContext},
    error::{error, ErrorIterator},
    keywords::CompilationResult,
    output::BasicOutput,
    paths::{InstancePath, JSONPointer},
    primitive_type::PrimitiveType,
    resolver::Resolver,
    schema_node::SchemaNode,
    validator::{PartialApplication, Validate},
    CompilationOptions, Draft, ValidationError,
};
use parking_lot::RwLock;
use serde_json::{Map, Value};
use std::sync::Arc;
use url::Url;

pub(crate) struct RefValidator {
    original_reference: String,
    reference: Url,
    /// Precomputed validators.
    /// They are behind a RwLock as is not possible to compute them
    /// at compile time without risking infinite loops of references
    /// and at the same time during validation we iterate over shared
    /// references (&self) and not owned references (&mut self).
    sub_nodes: RwLock<Option<SchemaNode>>,
    schema_path: JSONPointer,
    config: Arc<CompilationOptions>,
    pub(crate) resolver: Arc<Resolver>,
}

impl RefValidator {
    #[inline]
    pub(crate) fn compile<'a>(
        reference: &str,
        context: &CompilationContext,
    ) -> CompilationResult<'a> {
        Ok(Box::new(RefValidator {
            original_reference: reference.to_string(),
            reference: context.build_url(reference)?,
            sub_nodes: RwLock::new(None),
            schema_path: context.schema_path.clone().into(),
            config: Arc::clone(&context.config),
            resolver: Arc::clone(&context.resolver),
        }))
    }

    fn resolve_sub_nodes(&self) -> Result<(), ValidationError> {
        if self.sub_nodes.read().is_none() {
            match self.resolver.resolve_fragment(
                self.config.draft(),
                &self.reference,
                &self.original_reference,
            ) {
                Ok((scope, resolved)) => {
                    let context = CompilationContext::new(
                        scope.into(),
                        Arc::clone(&self.config),
                        Arc::clone(&self.resolver),
                    );
                    match compile_validators(&resolved, &context) {
                        Ok(node) => {
                            *self.sub_nodes.write() = Some(node);
                        }
                        Err(err) => return Err(err.into_owned()),
                    }
                }
                Err(err) => return Err(err.into_owned()),
            }
        }

        Ok(())
    }
}

impl Validate for RefValidator {
    fn is_valid(&self, instance: &Value) -> bool {
        if let Err(_) = self.resolve_sub_nodes() {
            return false;
        }

        if let Some(sub_nodes) = self.sub_nodes.read().as_ref() {
            return sub_nodes.is_valid(instance);
        }

        false
    }

    fn validate<'instance>(
        &self,
        instance: &'instance Value,
        instance_path: &InstancePath,
    ) -> ErrorIterator<'instance> {
        if let Err(err) = self.resolve_sub_nodes() {
            return error(err.into_owned());
        }

        if let Some(node) = self.sub_nodes.read().as_ref() {
            return Box::new(
                node.validate(instance, instance_path)
                    .collect::<Vec<_>>()
                    .into_iter(),
            );
        }

        error(ValidationError::invalid_reference(
            self.reference.to_string(),
        ))
    }

    fn apply<'a>(
        &'a self,
        instance: &Value,
        instance_path: &InstancePath,
    ) -> PartialApplication<'a> {
        if let Err(err) = self.resolve_sub_nodes() {
            return PartialApplication::invalid_empty(vec![err.into()]);
        }

        if let Some(node) = self.sub_nodes.read().as_ref() {
            // Only BasicOutput::Invalid can be handled here because BasicOutput::Valid depends on the lifetime of the SchemaNode
            // it was generated from. Given that the SchemaNode comes from a RwLock that sets its lifetime, it cannot guarantee
            // it will live enough for BasicOutput::Valid to be used as the returned value
            if let BasicOutput::Invalid(x) = node.apply_rooted(instance, instance_path) {
                return BasicOutput::Invalid(x).into();
            }

            // Generate an empty instance to circumvent the lifetime issue described above
            return PartialApplication::valid_empty();
        }

        PartialApplication::invalid_empty(vec!["Failed resolve reference".into()])
    }
}

impl core::fmt::Display for RefValidator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "$ref: {}", self.reference)
    }
}

#[inline]
pub(crate) fn compile<'a>(
    _: &'a Map<String, Value>,
    schema: &'a Value,
    context: &CompilationContext,
) -> Option<CompilationResult<'a>> {
    Some(
        schema
            .as_str()
            .ok_or_else(|| {
                ValidationError::single_type_error(
                    JSONPointer::default(),
                    context.clone().into_pointer(),
                    schema,
                    PrimitiveType::String,
                )
            })
            .and_then(|reference| RefValidator::compile(reference, context)),
    )
}

pub(crate) const fn supports_adjacent_validation(draft: Draft) -> bool {
    match draft {
        #[cfg(feature = "draft201909")]
        Draft::Draft201909 => true,
        #[cfg(feature = "draft202012")]
        Draft::Draft202012 => true,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use crate::tests_util;
    use serde_json::json;

    #[test]
    fn schema_path() {
        tests_util::assert_schema_path(
            &json!({"properties": {"foo": {"$ref": "#/definitions/foo"}}, "definitions": {"foo": {"type": "string"}}}),
            &json!({"foo": 42}),
            "/properties/foo/type",
        )
    }
}
