use crate::context::Context;
use crate::value::Value;

use std::convert::TryInto;
use std::error::Error;

use std::lazy::SyncLazy;

/// handles the member functions/constants for built-in types
/// TODO: complete this
pub(crate) static NUM_CONTEXT: SyncLazy<Context> = SyncLazy::new(|| {
    let mut ctx = Context::new();
    ctx.func2(
        '+',
        |_self: i128, other: i128| -> Result<i128, Box<dyn Error>> { Ok(_self + other) },
    );
    ctx.func1(
        "to_string",
        |_self: i128| -> Result<String, Box<dyn Error>> { Ok(_self.to_string()) },
    );
    ctx.func1("to_bool", |_self: i128| -> Result<bool, Box<dyn Error>> {
        Ok(if _self != 0 { true } else { false })
    });
    ctx.func1("to_bin", |_self: i128| -> Result<String, Box<dyn Error>> {
        Ok(format!("{:b}", _self))
    });
    ctx.func1("to_hex", |_self: i128| -> Result<String, Box<dyn Error>> {
        Ok(format!("{:x}", _self))
    });
    ctx.func1("to_oct", |_self: i128| -> Result<String, Box<dyn Error>> {
        Ok(format!("{:o}", _self))
    });
    ctx.func1("chr", |_self: i128| -> Result<char, Box<dyn Error>> {
        let value: u32 = _self.try_into()?;
        Ok(char::from_u32(value).unwrap())
    });
    ctx.func1("abs", |_self: i128| -> Result<i128, Box<dyn Error>> {
        if _self < 0i128 {
            Ok(-_self)
        } else {
            Ok(_self)
        }
    });
    ctx.func2(
        "pow",
        |_self: i128, n: i128| -> Result<i128, Box<dyn Error>> { Ok(_self.pow(n.try_into()?)) },
    );
    ctx.def("max", Value::Number(i128::MAX));
    ctx.def("min", Value::Number(i128::MIN));
    ctx
});

pub(crate) static FLOAT_CONTEXT: SyncLazy<Context> = SyncLazy::new(|| {
    let mut ctx = Context::new();
    ctx.func1(
        "to_string",
        |_self: f64| -> Result<String, Box<dyn Error>> { Ok(_self.to_string()) },
    );
    ctx.func1("abs", |_self: f64| -> Result<f64, Box<dyn Error>> {
        if _self < 0f64 {
            Ok(-_self)
        } else {
            Ok(_self)
        }
    });
    ctx.func2("pow", |_self: f64, n: f64| -> Result<f64, Box<dyn Error>> {
        Ok(_self.powf(n))
    });
    ctx.func1("to_radians", |_self: f64| -> Result<f64, Box<dyn Error>> {
        Ok(_self.to_radians())
    });
    ctx.func1("round", |_self: f64| -> Result<f64, Box<dyn Error>> {
        Ok(_self.round())
    });
    ctx.func1("floor", |_self: f64| -> Result<f64, Box<dyn Error>> {
        Ok(_self.floor())
    });
    ctx.def("max", Value::Float(f64::MAX));
    ctx.def("min", Value::Float(f64::MIN));
    ctx
});

pub(crate) static CHAR_CONTEXT: SyncLazy<Context> = SyncLazy::new(|| {
    let mut ctx = Context::new();
    ctx.func1("ord", |c: char| -> Result<i128, Box<dyn Error>> {
        Ok((c as u32) as i128)
    });
    ctx
});

pub(crate) static BOOL_CONTEXT: SyncLazy<Context> = SyncLazy::new(|| {
    let mut ctx = Context::new();
    ctx.func1("to_number", |c: bool| -> Result<i128, Box<dyn Error>> {
        Ok(if c { 1 } else { 0 })
    });
    ctx.func1("to_string", |c: bool| -> Result<String, Box<dyn Error>> {
        Ok(c.to_string())
    });
    ctx
});

pub(crate) static STRING_CONTEXT: SyncLazy<Context> = SyncLazy::new(|| {
    let mut ctx = Context::new();
    ctx.func1("to_number", |s: String| -> Result<i128, Box<dyn Error>> {
        s.parse::<i128>().map_err(|e| e.into())
    });
    ctx.func1("len", |s: String| -> Result<i128, Box<dyn Error>> {
        Ok(s.len() as i128)
    });
    ctx.func1("to_string", |s: String| -> Result<String, Box<dyn Error>> {
        Ok(s)
    });
    ctx
});

pub(crate) static ARRAY_CONTEXT: SyncLazy<Context> = SyncLazy::new(|| {
    let mut ctx = Context::new();
    ctx.func1("len", |array: Vec<Value>| -> Result<i128, Box<dyn Error>> {
        Ok(array.len() as i128)
    });
    ctx
});

pub(crate) static CTX_MAP: [&SyncLazy<Context>; 5] = [
    &NUM_CONTEXT,
    &FLOAT_CONTEXT,
    &CHAR_CONTEXT,
    &BOOL_CONTEXT,
    &STRING_CONTEXT,
];
