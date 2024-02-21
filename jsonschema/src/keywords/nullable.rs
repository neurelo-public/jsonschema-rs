use crate::{
    compilation::context::CompilationContext,
    error::{error, no_error, ErrorIterator, ValidationError},
    keywords::CompilationResult,
    paths::{InstancePath, JSONPointer},
    primitive_type::PrimitiveType,
    validator::Validate,
};
use serde_json::{Map, Value};

pub(crate) struct NullableValidator {
    schema_path: JSONPointer,
}

impl NullableValidator {
    #[inline]
    pub(crate) fn compile<'a>(
        schema: &'a Value,
        context: &CompilationContext,
    ) -> CompilationResult<'a> {
        let Some(nullable) = schema.as_bool() else {
            return Err(ValidationError::single_type_error(
                JSONPointer::default(),
                context.clone().into_pointer(),
                schema,
                PrimitiveType::Boolean,
            ));
        };

        if !nullable {
            return Err(ValidationError::constant_boolean(
                JSONPointer::default(),
                context.clone().into_pointer(),
                schema,
                true,
            ));
        }

        Ok(Box::new(NullableValidator {
            schema_path: context.as_pointer_with("nullable"),
        }))
    }
}

impl Validate for NullableValidator {
    fn is_valid(&self, instance: &Value) -> bool {
        instance.is_null()
    }

    fn validate<'instance>(
        &self,
        instance: &'instance Value,
        instance_path: &InstancePath,
    ) -> ErrorIterator<'instance> {
        if self.is_valid(instance) {
            no_error()
        } else {
            error(ValidationError::nullable(
                self.schema_path.clone(),
                instance_path.into(),
                instance,
            ))
        }
    }
}

impl core::fmt::Display for NullableValidator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "nullable: true")
    }
}

#[inline]
pub(crate) fn compile<'a>(
    _: &'a Map<String, Value>,
    schema: &'a Value,
    context: &CompilationContext,
) -> Option<CompilationResult<'a>> {
    Some(NullableValidator::compile(schema, context))
}

#[cfg(feature = "nullable")]
#[cfg(test)]
mod tests {
    use crate::tests_util;
    use serde_json::json;

    #[test]
    fn test_valid() {
        tests_util::is_valid_with_nullable(&json!({"nullable": true}), &json!(null));
    }

    #[test]
    fn test_invalid() {
        tests_util::is_not_valid_with_nullable(&json!({"nullable": true}), &json!(1));
    }
}
