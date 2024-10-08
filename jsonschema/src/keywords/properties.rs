use crate::{
    compilation::{compile_validators, context::CompilationContext},
    error::{no_error, ErrorIterator, ValidationError},
    get_location_from_path,
    keywords::CompilationResult,
    paths::{InstancePath, JSONPointer},
    primitive_type::PrimitiveType,
    schema_node::SchemaNode,
    validator::{format_key_value_validators, Location, PartialApplication, Validate},
};
use serde_json::{Map, Value};

pub(crate) struct PropertiesValidator {
    schema_path: JSONPointer,
    pub(crate) properties: Vec<(String, SchemaNode)>,
}

impl PropertiesValidator {
    #[inline]
    pub(crate) fn compile<'a>(
        schema: &'a Value,
        context: &CompilationContext,
    ) -> CompilationResult<'a> {
        match schema {
            Value::Object(map) => {
                let context = context.with_path("properties");
                let mut properties = Vec::with_capacity(map.len());
                for (key, subschema) in map {
                    let property_context = context.with_path(key.clone());
                    properties.push((
                        key.clone(),
                        compile_validators(subschema, &property_context)?,
                    ));
                }
                Ok(Box::new(PropertiesValidator {
                    schema_path: context.into_pointer(),
                    properties,
                }))
            }
            _ => Err(ValidationError::single_type_error(
                JSONPointer::default(),
                context.clone().into_pointer(),
                schema,
                PrimitiveType::Object,
            )),
        }
    }
}

impl Validate for PropertiesValidator {
    get_location_from_path!();

    fn is_valid(&self, instance: &Value) -> bool {
        if let Value::Object(item) = instance {
            self.properties.iter().all(move |(name, node)| {
                let option = item.get(name);
                option.into_iter().all(move |item| node.is_valid(item))
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
                .properties
                .iter()
                .flat_map(move |(name, node)| {
                    let option = item.get(name);
                    option.into_iter().flat_map(move |item| {
                        let instance_path = instance_path.push(name.clone());
                        node.validate(item, &instance_path)
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

        if let Value::Object(props) = instance {
            let mut matched_props = Vec::with_capacity(props.len());
            for (prop_name, node) in &self.properties {
                if let Some(prop) = props.get(prop_name) {
                    let path = instance_path.push(prop_name.clone());
                    matched_props.push(prop_name.clone());
                    let mut application = node.apply(prop, &path);
                    result.merge_property_match(&mut application);
                }
            }
            result.annotate(Value::from(matched_props).into());
        }

        result
    }
}

impl core::fmt::Display for PropertiesValidator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "properties: {{{}}}",
            format_key_value_validators(&self.properties)
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
        // This type of `additionalProperties` validator handles `properties` logic
        Some(Value::Bool(false)) | Some(Value::Object(_)) => None,
        _ => Some(PropertiesValidator::compile(schema, context)),
    }
}

#[cfg(test)]
mod tests {
    use crate::tests_util;
    use serde_json::json;

    #[test]
    fn schema_path() {
        tests_util::assert_schema_path(
            &json!({"properties": {"foo": {"properties": {"bar": {"required": ["spam"]}}}}}),
            &json!({"foo": {"bar": {}}}),
            "/properties/foo/properties/bar/required",
        )
    }
}
