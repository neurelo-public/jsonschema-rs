use crate::{
    compilation::{compile_validators, context::CompilationContext},
    error::{no_error, ErrorIterator, ValidationError},
    get_location_from_node, get_location_from_path,
    keywords::CompilationResult,
    paths::{InstancePath, JSONPointer},
    primitive_type::PrimitiveType,
    schema_node::SchemaNode,
    validator::{format_validators, Location, PartialApplication, Validate},
};
use fancy_regex::Regex;
use serde_json::{Map, Value};

pub(crate) struct PatternPropertiesValidator {
    schema_path: JSONPointer,
    patterns: Vec<(Regex, SchemaNode)>,
}

impl PatternPropertiesValidator {
    #[inline]
    pub(crate) fn compile<'a>(
        map: &'a Map<String, Value>,
        context: &CompilationContext,
    ) -> CompilationResult<'a> {
        let keyword_context = context.with_path("patternProperties");
        let mut patterns = Vec::with_capacity(map.len());
        for (pattern, subschema) in map {
            let pattern_context = keyword_context.with_path(pattern.to_string());
            patterns.push((
                match Regex::new(pattern) {
                    Ok(r) => r,
                    Err(_) => {
                        return Err(ValidationError::format(
                            JSONPointer::default(),
                            keyword_context.clone().into_pointer(),
                            subschema,
                            "regex",
                        ))
                    }
                },
                compile_validators(subschema, &pattern_context)?,
            ));
        }
        Ok(Box::new(PatternPropertiesValidator {
            schema_path: keyword_context.into_pointer(),
            patterns,
        }))
    }
}

impl Validate for PatternPropertiesValidator {
    get_location_from_path!();

    fn is_valid(&self, instance: &Value) -> bool {
        if let Value::Object(item) = instance {
            self.patterns.iter().all(move |(re, node)| {
                item.iter()
                    .filter(move |(key, _)| re.is_match(key).unwrap_or(false))
                    .all(move |(_key, value)| node.is_valid(value))
            })
        } else {
            true
        }
    }

    #[allow(clippy::needless_collect)]
    fn validate<'instance>(
        &self,
        instance: &'instance Value,
        instance_path: &InstancePath,
    ) -> ErrorIterator<'instance> {
        if let Value::Object(item) = instance {
            let errors: Vec<_> = self
                .patterns
                .iter()
                .flat_map(move |(re, node)| {
                    item.iter()
                        .filter(move |(key, _)| re.is_match(key).unwrap_or(false))
                        .flat_map(move |(key, value)| {
                            let instance_path = instance_path.push(key.clone());
                            node.validate(value, &instance_path)
                        })
                })
                .collect();
            Box::new(errors.into_iter())
        } else {
            no_error()
        }
    }

    fn apply<'instance>(
        &self,
        instance: &'instance Value,
        instance_path: &InstancePath,
    ) -> PartialApplication<'instance> {
        let mut result = PartialApplication::valid_empty(self.get_location(instance_path));

        if let Value::Object(item) = instance {
            let mut matched_propnames = Vec::with_capacity(item.len());
            for (pattern, node) in &self.patterns {
                for (key, value) in item {
                    if pattern.is_match(key).unwrap_or(false) {
                        let path = instance_path.push(key.clone());
                        matched_propnames.push(key.clone());
                        result.merge_property_match(&mut node.apply(value, &path));
                    }
                }
            }
            result.annotate(Value::from(matched_propnames).into());
        }

        result
    }
}

impl core::fmt::Display for PatternPropertiesValidator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "patternProperties: {{{}}}",
            self.patterns
                .iter()
                .map(|(key, node)| { format!("{}: {}", key, format_validators(node.validators())) })
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
}

pub(crate) struct SingleValuePatternPropertiesValidator {
    pattern: Regex,
    node: SchemaNode,
}

impl SingleValuePatternPropertiesValidator {
    #[inline]
    pub(crate) fn compile<'a>(
        pattern: &'a str,
        schema: &'a Value,
        context: &CompilationContext,
    ) -> CompilationResult<'a> {
        let keyword_context = context.with_path("patternProperties");
        let pattern_context = keyword_context.with_path(pattern.to_string());
        Ok(Box::new(SingleValuePatternPropertiesValidator {
            pattern: match Regex::new(pattern) {
                Ok(r) => r,
                Err(_) => {
                    return Err(ValidationError::format(
                        JSONPointer::default(),
                        keyword_context.clone().into_pointer(),
                        schema,
                        "regex",
                    ))
                }
            },
            node: compile_validators(schema, &pattern_context)?,
        }))
    }
}

impl Validate for SingleValuePatternPropertiesValidator {
    get_location_from_node!();

    fn is_valid(&self, instance: &Value) -> bool {
        if let Value::Object(item) = instance {
            item.iter()
                .filter(move |(key, _)| self.pattern.is_match(key).unwrap_or(false))
                .all(move |(_key, value)| self.node.is_valid(value))
        } else {
            true
        }
    }

    #[allow(clippy::needless_collect)]
    fn validate<'instance>(
        &self,
        instance: &'instance Value,
        instance_path: &InstancePath,
    ) -> ErrorIterator<'instance> {
        if let Value::Object(item) = instance {
            let errors: Vec<_> = item
                .iter()
                .filter(move |(key, _)| self.pattern.is_match(key).unwrap_or(false))
                .flat_map(move |(key, value)| {
                    let instance_path = instance_path.push(key.clone());
                    self.node.validate(value, &instance_path)
                })
                .collect();
            Box::new(errors.into_iter())
        } else {
            no_error()
        }
    }

    fn apply<'instance>(
        &self,
        instance: &'instance Value,
        instance_path: &InstancePath,
    ) -> PartialApplication<'instance> {
        let mut result = PartialApplication::valid_empty(self.get_location(instance_path));

        if let Value::Object(item) = instance {
            let mut matched_propnames = Vec::with_capacity(item.len());
            for (key, value) in item {
                if self.pattern.is_match(key).unwrap_or(false) {
                    let path = instance_path.push(key.clone());
                    matched_propnames.push(key.clone());
                    result.merge_property_match(&mut self.node.apply(value, &path));
                }
            }
            result.annotate(Value::from(matched_propnames).into());
        }

        result
    }
}

impl core::fmt::Display for SingleValuePatternPropertiesValidator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "patternProperties: {{{}: {}}}",
            self.pattern,
            format_validators(self.node.validators())
        )
    }
}

#[inline]
pub(crate) fn compile<'a>(
    parent: &'a Map<String, Value>,
    schema: &'a Value,
    context: &CompilationContext,
) -> Option<CompilationResult<'a>> {
    match parent.get("additionalProperties") {
        // This type of `additionalProperties` validator handles `patternProperties` logic
        Some(Value::Bool(false)) | Some(Value::Object(_)) => None,
        _ => {
            if let Value::Object(map) = schema {
                if map.len() == 1 {
                    let (key, value) = map.iter().next().expect("Map is not empty");
                    Some(SingleValuePatternPropertiesValidator::compile(
                        key, value, context,
                    ))
                } else {
                    Some(PatternPropertiesValidator::compile(map, context))
                }
            } else {
                Some(Err(ValidationError::single_type_error(
                    JSONPointer::default(),
                    context.clone().into_pointer(),
                    schema,
                    PrimitiveType::Object,
                )))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::tests_util;
    use serde_json::{json, Value};
    use test_case::test_case;

    #[test_case(&json!({"patternProperties": {"^f": {"type": "string"}}}), &json!({"f": 42}), "/patternProperties/^f/type")]
    #[test_case(&json!({"patternProperties": {"^f": {"type": "string"}, "^x": {"type": "string"}}}), &json!({"f": 42}), "/patternProperties/^f/type")]
    fn schema_path(schema: &Value, instance: &Value, expected: &str) {
        tests_util::assert_schema_path(schema, instance, expected)
    }
}
