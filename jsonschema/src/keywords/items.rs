use crate::{
    compilation::{compile_validators, context::CompilationContext},
    error::{no_error, ErrorIterator},
    get_location_from_node, get_location_from_path,
    keywords::CompilationResult,
    paths::{InstancePath, JSONPointer},
    schema_node::SchemaNode,
    validator::{
        format_iter_of_validators, format_validators, Location, PartialApplication, Validate,
    },
};
use serde_json::{Map, Value};

pub(crate) struct ItemsArrayValidator {
    schema_path: JSONPointer,
    items: Vec<SchemaNode>,
}
impl ItemsArrayValidator {
    #[inline]
    pub(crate) fn compile<'a>(
        schemas: &'a [Value],
        context: &CompilationContext,
    ) -> CompilationResult<'a> {
        let keyword_context = context.with_path("items");
        let mut items = Vec::with_capacity(schemas.len());
        for (idx, item) in schemas.iter().enumerate() {
            let item_context = keyword_context.with_path(idx);
            let validators = compile_validators(item, &item_context)?;
            items.push(validators)
        }
        Ok(Box::new(ItemsArrayValidator {
            schema_path: keyword_context.into_pointer(),
            items,
        }))
    }
}
impl Validate for ItemsArrayValidator {
    get_location_from_path!();

    fn is_valid(&self, instance: &Value) -> bool {
        if let Value::Array(items) = instance {
            items
                .iter()
                .zip(self.items.iter())
                .all(move |(item, node)| node.is_valid(item))
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
        if let Value::Array(items) = instance {
            let errors: Vec<_> = items
                .iter()
                .zip(self.items.iter())
                .enumerate()
                .flat_map(move |(idx, (item, node))| node.validate(item, &instance_path.push(idx)))
                .collect();
            Box::new(errors.into_iter())
        } else {
            no_error()
        }
    }
}

impl core::fmt::Display for ItemsArrayValidator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "items: [{}]",
            format_iter_of_validators(self.items.iter().map(SchemaNode::validators))
        )
    }
}

pub(crate) struct ItemsObjectValidator {
    node: SchemaNode,
}

impl ItemsObjectValidator {
    #[inline]
    pub(crate) fn compile<'a>(
        schema: &'a Value,
        context: &CompilationContext,
    ) -> CompilationResult<'a> {
        let keyword_context = context.with_path("items");
        let node = compile_validators(schema, &keyword_context)?;
        Ok(Box::new(ItemsObjectValidator { node }))
    }
}
impl Validate for ItemsObjectValidator {
    get_location_from_node!();

    fn is_valid(&self, instance: &Value) -> bool {
        if let Value::Array(items) = instance {
            items.iter().all(|i| self.node.is_valid(i))
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
        if let Value::Array(items) = instance {
            let errors: Vec<_> = items
                .iter()
                .enumerate()
                .flat_map(move |(idx, item)| self.node.validate(item, &instance_path.push(idx)))
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

        if let Value::Array(items) = instance {
            for (idx, item) in items.iter().enumerate() {
                let path = instance_path.push(idx);
                result.merge_property_match(&mut self.node.apply(item, &path));
            }
            // Per draft 2020-12 section https://json-schema.org/draft/2020-12/json-schema-core.html#rfc.section.10.3.1.2
            // we must produce an annotation with a boolean value indicating whether the subschema
            // was applied to any positions in the underlying array. Since the struct
            // `ItemsObjectValidator` is not used when prefixItems is defined, this is true if
            // there are any items in the instance.
            let schema_was_applied = !items.is_empty();
            result.annotate(serde_json::json! {schema_was_applied}.into());
        }

        result
    }
}

impl core::fmt::Display for ItemsObjectValidator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "items: {}", format_validators(self.node.validators()))
    }
}

pub(crate) struct ItemsObjectSkipPrefixValidator {
    node: SchemaNode,
    skip_prefix: usize,
}

impl ItemsObjectSkipPrefixValidator {
    #[inline]
    pub(crate) fn compile<'a>(
        schema: &'a Value,
        skip_prefix: usize,
        context: &CompilationContext,
    ) -> CompilationResult<'a> {
        let keyword_context = context.with_path("items");
        let node = compile_validators(schema, &keyword_context)?;
        Ok(Box::new(ItemsObjectSkipPrefixValidator {
            node,
            skip_prefix,
        }))
    }
}

impl Validate for ItemsObjectSkipPrefixValidator {
    get_location_from_node!();

    fn is_valid(&self, instance: &Value) -> bool {
        if let Value::Array(items) = instance {
            items
                .iter()
                .skip(self.skip_prefix)
                .all(|i| self.node.is_valid(i))
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
        if let Value::Array(items) = instance {
            let errors: Vec<_> = items
                .iter()
                .skip(self.skip_prefix)
                .enumerate()
                .flat_map(move |(idx, item)| {
                    self.node
                        .validate(item, &instance_path.push(idx + self.skip_prefix))
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

        if let Value::Array(items) = instance {
            for (idx, item) in items.iter().skip(self.skip_prefix).enumerate() {
                let path = instance_path.push(idx + self.skip_prefix);
                result.merge_property_match(&mut self.node.apply(item, &path));
            }
            // Per draft 2020-12 section https://json-schema.org/draft/2020-12/json-schema-core.html#rfc.section.10.3.1.2
            // we must produce an annotation with a boolean value indicating whether the subschema
            // was applied to any positions in the underlying array.
            let schema_was_applied = items.len() > self.skip_prefix;
            result.annotate(serde_json::json! {schema_was_applied}.into());
        }

        result
    }
}

impl core::fmt::Display for ItemsObjectSkipPrefixValidator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "items: {}", format_validators(self.node.validators()))
    }
}

#[inline]
pub(crate) fn compile<'a>(
    parent: &'a Map<String, Value>,
    schema: &'a Value,
    context: &CompilationContext,
) -> Option<CompilationResult<'a>> {
    match schema {
        Value::Array(items) => Some(ItemsArrayValidator::compile(items, context)),
        Value::Object(_) | Value::Bool(false) => {
            #[cfg(feature = "draft202012")]
            if let Some(Value::Array(prefix_items)) = parent.get("prefixItems") {
                return Some(ItemsObjectSkipPrefixValidator::compile(
                    schema,
                    prefix_items.len(),
                    context,
                ));
            }
            Some(ItemsObjectValidator::compile(schema, context))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use crate::tests_util;
    use serde_json::{json, Value};
    use test_case::test_case;

    #[test_case(&json!({"items": false}), &json!([1]), "/items")]
    #[test_case(&json!({"items": {"type": "string"}}), &json!([1]), "/items/type")]
    #[test_case(&json!({"items": [{"type": "string"}]}), &json!([1]), "/items/0/type")]
    fn schema_path(schema: &Value, instance: &Value, expected: &str) {
        tests_util::assert_schema_path(schema, instance, expected)
    }
}
