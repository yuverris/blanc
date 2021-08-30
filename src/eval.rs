use crate::{
    error::{self, Error},
    lexer::Operator,
    parser::Expression,
    source_location::SourceLocation,
};

use std::{
    cmp::{Ordering, PartialEq, PartialOrd},
    collections::HashMap,
    f64::consts,
    fmt,
    iter::Peekable,
    ops::{Add, Div, Mul, Neg, Not, Sub},
    rc::Rc,
    slice::Iter,
    string::ToString,
};

#[derive(Clone)]
pub enum Value {
    Number(f64),
    Bool(bool),
    Func(FunctionType),
    Null,
}

impl fmt::Debug for Value {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            &Value::Number(n) => write!(fmt, "Number({})", n),
            &Value::Bool(b) => write!(fmt, "Bool({})", b),
            &Value::Null => write!(fmt, "Null"),
            &Value::Func(_) => write!(fmt, "Function"),
        }
    }
}

pub trait Fact {
    type Output;

    fn fact(&self) -> Self::Output;
}

pub trait Callable {
    fn call(&self, args: Vec<Value>, loc: SourceLocation) -> error::Result<Value>;
}

impl Callable for Value {
    fn call(&self, args: Vec<Value>, loc: SourceLocation) -> error::Result<Value> {
        match self {
            Value::Func(fnc) => fnc(&args[..]).map_err(|err| Error::RuntimeError(loc, err)),
            _ => Err(Error::TypeError(
                loc,
                format!("{:?} isn't a callable object", self),
            )),
        }
    }
}

impl Add for Value {
    type Output = Result<Self, &'static str>;

    fn add(self, other: Self) -> Self::Output {
        match (self, other) {
            (Value::Number(n), Value::Number(m)) => Ok(Value::Number(n + m)),
            _ => Err("invalid operands for binary operation '+'"),
        }
    }
}

impl Sub for Value {
    type Output = Result<Self, &'static str>;

    fn sub(self, other: Self) -> Self::Output {
        match (self, other) {
            (Value::Number(n), Value::Number(m)) => Ok(Value::Number(n - m)),
            _ => Err("invalid operands for binary operation '-'"),
        }
    }
}

impl Mul for Value {
    type Output = Result<Self, &'static str>;

    fn mul(self, other: Self) -> Self::Output {
        match (self, other) {
            (Value::Number(n), Value::Number(m)) => Ok(Value::Number(n * m)),
            _ => Err("invalid operands for binary operation '*'"),
        }
    }
}

impl Div for Value {
    type Output = Result<Self, &'static str>;

    fn div(self, other: Self) -> Self::Output {
        match (self, other) {
            (Value::Number(n), Value::Number(m)) => Ok(Value::Number(n / m)),
            _ => Err("invalid operands for binary operation '/'"),
        }
    }
}

impl Neg for Value {
    type Output = Result<Self, &'static str>;

    fn neg(self) -> Self::Output {
        match self {
            Value::Number(n) => Ok(Value::Number(-n)),
            _ => Err("invalid operand for unary operation '-'"),
        }
    }
}

impl Not for Value {
    type Output = Result<Self, &'static str>;

    fn not(self) -> Self::Output {
        match self {
            Value::Bool(b) => Ok(Value::Bool(!b)),
            Value::Null => Ok(Value::Bool(true)),
            _ => Err("invalid operand for unary operation '!'"),
        }
    }
}

impl Fact for Value {
    type Output = Result<Self, &'static str>;

    fn fact(&self) -> Self::Output {
        match self {
            Value::Number(n) => {
                if *n < 0f64 {
                    return Err("operand must not be negative");
                }
                let mut u = 1u64;
                for i in 1..=(*n as u64) {
                    u = u
                        .checked_mul(i)
                        .ok_or("cannot proccess the operation since value is overflowed")?;
                }
                Ok(Value::Number(u as f64))
            }
            _ => Err("invalid operand for postfix operator '!'"),
        }
    }
}

fn add(lhs: Value, rhs: Value, loc: SourceLocation) -> error::Result<Value> {
    let outcome = lhs + rhs;
    match outcome {
        Ok(value) => Ok(value),
        Err(err) => Err(Error::TypeError(loc, err.into())),
    }
}

fn sub(lhs: Value, rhs: Value, loc: SourceLocation) -> error::Result<Value> {
    let outcome = lhs - rhs;
    match outcome {
        Ok(value) => Ok(value),
        Err(err) => Err(Error::TypeError(loc, err.into())),
    }
}

fn mul(lhs: Value, rhs: Value, loc: SourceLocation) -> error::Result<Value> {
    let outcome = lhs * rhs;
    match outcome {
        Ok(value) => Ok(value),
        Err(err) => Err(Error::TypeError(loc, err.into())),
    }
}

fn div(lhs: Value, rhs: Value, loc: SourceLocation) -> error::Result<Value> {
    let outcome = lhs / rhs;
    match outcome {
        Ok(value) => Ok(value),
        Err(err) => Err(Error::TypeError(loc, err.into())),
    }
}

fn neg(lhs: Value, loc: SourceLocation) -> error::Result<Value> {
    let outcome = lhs.neg();
    match outcome {
        Ok(value) => Ok(value),
        Err(err) => Err(Error::TypeError(loc, err.into())),
    }
}

fn not(lhs: Value, loc: SourceLocation) -> error::Result<Value> {
    let outcome = lhs.not();
    match outcome {
        Ok(value) => Ok(value),
        Err(err) => Err(Error::TypeError(loc, err.into())),
    }
}

fn fact(lhs: Value, loc: SourceLocation) -> error::Result<Value> {
    let outcome = lhs.fact();
    match outcome {
        Ok(value) => Ok(value),
        Err(err) => Err(Error::TypeError(loc, err.into())),
    }
}

impl ToString for Value {
    fn to_string(&self) -> String {
        match self {
            Value::Number(n) => n.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Null => "null".into(),
            Value::Func(_) => "function".into(),
        }
    }
}

type FunctionType = Rc<dyn Fn(&[Value]) -> Result<Value, String>>;

pub struct Context {
    variables: HashMap<String, Value>,
    functions: HashMap<String, FunctionType>,
}

impl Context {
    pub fn new() -> Self {
        Self {
            variables: HashMap::new(),
            functions: HashMap::new(),
        }
    }

    pub fn var(&mut self, name: String, value: Value) -> &mut Self {
        self.variables.insert(name, value);
        self
    }

    pub fn get_var(&self, name: &String) -> Option<&Value> {
        self.variables.get(name)
    }

    pub fn get_func(&self, name: &String) -> Option<&FunctionType> {
        self.functions.get(name)
    }

    pub fn func(
        &mut self,
        name: String,
        func: &'static dyn Fn(&[Value]) -> Result<Value, String>,
        arg_count: usize,
    ) -> &mut Self {
        let fnc = move |args: &[Value]| {
            if args.len() != arg_count {
                Err(format!("umatched arguments count fucntion requires {} arguments, you supplied {} arguments",
                            arg_count, args.len()))
            } else {
                func(args)
            }
        };
        self.functions.insert(name, Rc::new(fnc));
        self
    }
}

pub struct Eval {
    expr: Expression,
    context: Context,
}

impl Eval {
    pub fn new(expr: Expression) -> Self {
        let mut ctx = Context::new();
        ctx.var("pi".into(), Value::Number(consts::PI));
        ctx.var("e".into(), Value::Number(consts::E));
        ctx.var("tau".into(), Value::Number(consts::TAU));
        ctx.func(
            "sqrt".into(),
            &|args| match args[0] {
                Value::Number(n) => Ok(Value::Number(n.sqrt())),
                _ => Err("expected argument of type Number".into()),
            },
            1,
        );

        Self {
            expr: expr,
            context: ctx,
        }
    }

    pub fn eval_expr(&mut self, expr: Expression) -> error::Result<Value> {
        match expr {
            Expression::Number(_, x) => Ok(Value::Number(x)),
            Expression::Bool(_, b) => Ok(Value::Bool(b)),
            Expression::Null(_) => Ok(Value::Null),
            Expression::Ident(loc, i) => {
                if let Some(v) = self.context.get_var(&i) {
                    Ok(v.clone())
                } else if let Some(f) = self.context.get_func(&i) {
                    Ok(Value::Func(f.clone()))
                } else {
                    Err(Error::RuntimeError(
                        loc.clone(),
                        format!("undefined value '{}'", i),
                    ))
                }
            }
            Expression::FuncCall(loc, box expr, args) => self.eval_expr(expr)?.call(
                args.iter()
                    .map(|arg| -> error::Result<Value> { self.eval_expr(arg.clone()) })
                    .collect::<error::Result<Vec<Value>>>()?,
                loc.clone(),
            ),
            Expression::Unary(loc, Operator::Negative, box expr) => {
                neg(self.eval_expr(expr)?, loc.clone())
            }

            Expression::Unary(loc, Operator::Positive, box expr) => self.eval_expr(expr),

            Expression::Unary(loc, Operator::Not, box expr) => {
                not(self.eval_expr(expr)?, loc.clone())
            }

            Expression::Unary(loc, Operator::Factorial, box expr) => {
                fact(self.eval_expr(expr)?, loc.clone())
            }

            Expression::Binary(loc, Operator::Plus, box lhs, box rhs) => {
                add(self.eval_expr(lhs)?, self.eval_expr(rhs)?, loc.clone())
            }

            Expression::Binary(loc, Operator::Minus, box lhs, box rhs) => {
                sub(self.eval_expr(lhs)?, self.eval_expr(rhs)?, loc.clone())
            }

            Expression::Binary(loc, Operator::Star, box lhs, box rhs) => {
                mul(self.eval_expr(lhs)?, self.eval_expr(rhs)?, loc.clone())
            }

            Expression::Binary(loc, Operator::Slash, box lhs, box rhs) => {
                div(self.eval_expr(lhs)?, self.eval_expr(rhs)?, loc.clone())
            }

            _ => Err(Error::Error("invalid expression".into())),
        }
    }

    pub fn eval(&mut self) -> error::Result<Value> {
        self.eval_expr(self.expr.clone())
    }
}
