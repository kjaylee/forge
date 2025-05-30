use handlebars::{
    Context, Handlebars, Helper, HelperDef, HelperResult, Output, RenderContext, RenderErrorReason, Renderable,
};
use serde_json::Value as Json;

#[derive(Clone, Copy)]
pub struct ArrayContainsHelper;

impl HelperDef for ArrayContainsHelper {
    fn call<'reg: 'rc, 'rc>(
        &self,
        h: &Helper<'rc>,
        r: &'reg Handlebars<'reg>,
        ctx: &'rc Context,
        rc: &mut RenderContext<'reg, 'rc>,
        out: &mut dyn Output,
    ) -> HelperResult {
        // Get array parameter
        let array = h
            .param(0)
            .ok_or(RenderErrorReason::ParamNotFoundForIndex("array_contains", 0))?;
        
        // Get search value parameter
        let search_value = h
            .param(1)
            .ok_or(RenderErrorReason::ParamNotFoundForIndex("array_contains", 1))?;

        let contains = match array.value() {
            Json::Array(arr) => arr.iter().any(|item| item == search_value.value()),
            _ => false, // Return false if first parameter is not an array
        };

        let tmpl = if contains { h.template() } else { h.inverse() };
        match tmpl {
            Some(t) => t.render(r, ctx, rc, out),
            None => Ok(()),
        }
    }
}

pub static ARRAY_CONTAINS_HELPER: ArrayContainsHelper = ArrayContainsHelper;
