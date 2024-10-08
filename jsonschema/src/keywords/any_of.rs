use crate::{
    compilation::{compile_validators, context::CompilationContext},
    error::{error, no_error, ErrorIterator, ValidationError},
    get_location_from_path,
    paths::InstancePath,
    primitive_type::PrimitiveType,
    schema_node::SchemaNode,
    validator::{format_iter_of_validators, Location, PartialApplication, Validate},
};
use serde_json::{Map, Value};

use super::CompilationResult;
use crate::paths::JSONPointer;

pub(crate) struct AnyOfValidator {
    schemas: Vec<SchemaNode>,
    schema_path: JSONPointer,
}

impl AnyOfValidator {
    #[inline]
    pub(crate) fn compile<'a>(
        schema: &'a Value,
        context: &CompilationContext,
    ) -> CompilationResult<'a> {
        if let Value::Array(items) = schema {
            let keyword_context = context.with_path("anyOf");
            let mut schemas = Vec::with_capacity(items.len());
            for (idx, item) in items.iter().enumerate() {
                let item_context = keyword_context.with_path(idx);
                let node = compile_validators(item, &item_context)?;
                schemas.push(node)
            }
            Ok(Box::new(AnyOfValidator {
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
}

impl Validate for AnyOfValidator {
    get_location_from_path!();

    fn is_valid(&self, instance: &Value) -> bool {
        self.schemas.iter().any(|s| s.is_valid(instance))
    }

    fn validate<'instance>(
        &self,
        instance: &'instance Value,
        instance_path: &InstancePath,
    ) -> ErrorIterator<'instance> {
        if self.is_valid(instance) {
            no_error()
        } else {
            error(ValidationError::any_of(
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
        let mut result = PartialApplication::valid_empty(self.get_location(instance_path));
        let mut successes = Vec::new();
        let mut failures = Vec::new();
        for node in &self.schemas {
            let application = node.apply(instance, instance_path);
            if application.is_valid() {
                successes.push(application);
            } else {
                failures.push(application);
            }
        }
        if successes.is_empty() {
            failures.into_iter().for_each(|mut f| result.merge(&mut f));
        } else {
            successes.into_iter().for_each(|mut s| result.merge(&mut s));
        }

        result
    }
}

impl core::fmt::Display for AnyOfValidator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "anyOf: [{}]",
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
    Some(AnyOfValidator::compile(schema, context))
}

#[cfg(test)]
mod tests {
    use crate::tests_util;
    use serde_json::{json, Value};
    use test_case::test_case;

    #[test_case(&json!({"anyOf": [{"type": "string"}]}), &json!(1), "/anyOf")]
    #[test_case(&json!({"anyOf": [{"type": "integer"}, {"type": "string"}]}), &json!({}), "/anyOf")]
    fn schema_path(schema: &Value, instance: &Value, expected: &str) {
        tests_util::assert_schema_path(schema, instance, expected)
    }
}
