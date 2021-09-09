use crate::eval::{Context, Value};

use std::lazy::SyncLazy;

/// habdles the member functions/constants for built-in types
/// TODO: comolete this
pub(crate) static NUM_CONTEXT: SyncLazy<Context> = SyncLazy::new(|| {
    let mut ctx = Context::new();
    ctx.func1("to_string", |_self: i128| -> String { _self.to_string() });
    ctx.func1("chr", |_self: i128| -> String { _self.to_string() });
    ctx.func1("abs", |_self: i128| -> i128 {
        if _self < -1i128 {
            -_self
        } else {
            _self
        }
    });
    ctx.func1("max", |_: i128| -> i128 { i128::MAX });
    ctx.func1("min", |_: i128| -> i128 { i128::MIN });
    ctx
});
