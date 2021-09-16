use crate::context::Context;

use std::lazy::SyncLazy;

/// handles the member functions/constants for built-in types
/// TODO: complete this
pub(crate) static NUM_CONTEXT: SyncLazy<Context> = SyncLazy::new(|| {
    let mut ctx = Context::new();
    ctx.func1("to_string", |_self: i128| -> String { _self.to_string() });
    ctx.func1("chr", |_self: i128| -> String { _self.to_string() });
    ctx.func1("abs", |_self: i128| -> i128 {
        if _self < 0i128 {
            -_self
        } else {
            _self
        }
    });
    ctx.var("max", i128::MAX, true);
    ctx.var("min", i128::MIN, true);
    ctx
});
