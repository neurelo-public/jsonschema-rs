use std::cmp::Ordering;

use crate::{
    compilation::{compile_validators, context::CompilationContext},
    error::{error, no_error, ErrorIterator, ValidationError},
    get_location_from_path,
    keywords::CompilationResult,
    paths::{InstancePath, JSONPointer},
    primitive_type::PrimitiveType,
    schema_node::SchemaNode,
    validator::{format_iter_of_validators, Location, PartialApplication, Validate},
};
use serde_json::{Map, Value};

pub(crate) struct OneOfValidator {
    schemas: Vec<SchemaNode>,
    schema_path: JSONPointer,
}

impl OneOfValidator {
    #[inline]
    pub(crate) fn compile<'a>(
        schema: &'a Value,
        context: &CompilationContext,
    ) -> CompilationResult<'a> {
        if let Value::Array(items) = schema {
            let keyword_context = context.with_path("oneOf");
            let mut schemas = Vec::with_capacity(items.len());
            for (idx, item) in items.iter().enumerate() {
                let item_context = keyword_context.with_path(idx);
                let node = compile_validators(item, &item_context)?;
                schemas.push(node)
            }
            Ok(Box::new(OneOfValidator {
                schemas,
                schema_path: keyword_context.into_pointer(),
            }))
        } else {
            Err(ValidationError::single_type_error(
                JSONPointer::default(),
                context.clone().into_pointer(),
                schema,
                PrimitiveType::Array,
            ))
        }
    }

    fn get_first_valid(&self, instance: &Value) -> Option<usize> {
        let mut first_valid_idx = None;
        for (idx, node) in self.schemas.iter().enumerate() {
            if node.is_valid(instance) {
                first_valid_idx = Some(idx);
                break;
            }
        }
        first_valid_idx
    }

    #[allow(clippy::integer_arithmetic)]
    fn are_others_valid(&self, instance: &Value, idx: usize) -> bool {
        // `idx + 1` will not overflow, because the maximum possible value there is `usize::MAX - 1`
        // For example we have `usize::MAX` schemas and only the last one is valid, then
        // in `get_first_valid` we enumerate from `0`, and on the last index will be `usize::MAX - 1`
        self.schemas
            .iter()
            .skip(idx + 1)
            .any(|n| n.is_valid(instance))
    }
}

impl Validate for OneOfValidator {
    get_location_from_path!();

    fn is_valid(&self, instance: &Value) -> bool {
        let first_valid_idx = self.get_first_valid(instance);
        first_valid_idx.map_or(false, |idx| !self.are_others_valid(instance, idx))
    }
    fn validate<'instance>(
        &self,
        instance: &'instance Value,
        instance_path: &InstancePath,
    ) -> ErrorIterator<'instance> {
        let first_valid_idx = self.get_first_valid(instance);
        if let Some(idx) = first_valid_idx {
            if self.are_others_valid(instance, idx) {
                return error(ValidationError::one_of_multiple_valid(
                    self.schema_path.clone(),
                    instance_path.into(),
                    instance,
                ));
            }
            no_error()
        } else {
            error(ValidationError::one_of_not_valid(
                self.schema_path.clone(),
                instance_path.into(),
                instance,
            ))
        }
    }
    fn apply<'instance>(
        &self,
        instance: &'instance Value,
        instance_path: &InstancePath,
    ) -> PartialApplication<'instance> {
        let mut failures = Vec::new();
        let mut successes = Vec::new();
        for node in &self.schemas {
            match node.apply(instance, instance_path) {
                output @ PartialApplication::Valid { .. } => successes.push(output),
                output @ PartialApplication::Invalid { .. } => failures.push(output),
            };
        }

        if successes.len() == 1 {
            let success = successes.remove(0);
            return success.into();
        } else if successes.len() > 1 {
            return PartialApplication::invalid_empty(
                self.get_location(instance_path),
                vec![ValidationError::one_of_multiple_valid(
                    self.schema_path.clone(),
                    instance_path.into(),
                    instance,
                )],
            );
        }

        if !failures.is_empty() {
            dbg!(&failures);
            failures.sort_by(|a, b| a.partial_cmp(b).unwrap_or(Ordering::Equal));
            failures.pop().unwrap()
        } else {
            unreachable!("compilation should fail for oneOf with no subschemas")
        }
    }
}

impl core::fmt::Display for OneOfValidator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "oneOf: [{}]",
            format_iter_of_validators(self.schemas.iter().map(SchemaNode::validators))
        )
    }
}

#[inline]
pub(crate) fn compile<'a>(
    _: &'a Map<String, Value>,
    schema: &'a Value,
    context: &CompilationContext,
) -> Option<CompilationResult<'a>> {
    Some(OneOfValidator::compile(schema, context))
}

#[cfg(test)]
mod tests {
    use crate::tests_util;
    use serde_json::{json, Value};
    use test_case::test_case;

    #[test_case(&json!({"oneOf": [{"type": "string"}]}), &json!(0), "/oneOf")]
    #[test_case(&json!({"oneOf": [{"type": "string"}, {"maxLength": 3}]}), &json!(""), "/oneOf")]
    fn schema_path(schema: &Value, instance: &Value, expected: &str) {
        tests_util::assert_schema_path(schema, instance, expected)
    }

    #[test]
    fn is_not_valid() {
        let schema = tests_util::compile_schema(&json!({
            "oneOf": [
                {
                    "type": "string"
                },
                {
                    "type": "object",
                    "properties": {
                        "env": {
                            "type": "string"
                        }
                    },
                    "additionalProperties": false
                }
            ]
        }));

        let val = json!({"env": 1});
        let res = schema.apply(&val);

        dbg!(res);
    }

    #[test]
    fn add_complexity() {
        let schema = tests_util::compile_schema(
            &serde_json::from_str(include_str!("../../../schemapsql.json")).unwrap(),
        );

        let val = json!({
          "objects": {
            "obj1": {
              "properties": {
                "prop1": {"type": "number", "format": "other"}
              }
            }
          }
        });
        let res = schema.apply(&val);
        let res = res.basic();

        dbg!(res);
    }
}
