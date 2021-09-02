use crate::{
    error::{self, Error},
    lexer::Operator,
    parser::Expression,
    source_location::SourceLocation,
};

use std::{
    cmp::{Ordering, PartialEq, PartialOrd},
    collections::HashMap,
    convert::TryFrom,
    f64::consts,
    fmt,
    rc::Rc,
    string::ToString,
};
/// Enum for handling objects
///
/// # Example
///
/// ```rust
/// let mut value = Value::number(5.0);
/// println!("{}", value.to_string());
/// value = Value::Bool(true);
/// println!("{}", value.to_string());
/// ```
#[derive(Clone)]
pub enum Value {
    Number(f64),
    Bool(bool),
    Func(FunctionType),
    UserFunc {
        params: Vec<String>,
        body: Expression,
    },
    Null,
}
/// main trait for defining callable objects
pub trait Callable {
    fn call(&self, args: Vec<Value>, loc: SourceLocation, eval: &mut Eval) -> error::Result<Value>;
}

impl Callable for Value {
    fn call(&self, args: Vec<Value>, loc: SourceLocation, eval: &mut Eval) -> error::Result<Value> {
        match self {
            Value::Func(fnc) => fnc(&args[..]).map_err(|err| Error::RuntimeError(loc, err)),

            Value::UserFunc { params, body } => {
                if params.len() != args.len() {
                    return Err(Error::RuntimeError(
                        loc.clone(),
                        format!(
                            "function requires {} arguments, you supplied {}",
                            params.len(),
                            args.len()
                        ),
                    ));
                }
                /// store old state of the context and bind parameters names to the current context
                /// then reset the context to its old state after function call
                let context = eval.get_context_mut();
                let previous = context.clone();
                for (param, arg) in params.into_iter().zip(args) {
                    context.var(param.clone(), arg);
                }
                let out = eval.eval_expr(body);
                eval.set_context(previous);
                out
            }

            _ => Err(Error::TypeError(
                loc,
                format!("{} isn't a callable object", self.get_type()),
            )),
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Number(n), Value::Number(u)) => n == u,
            (Value::Bool(n), Value::Bool(u)) => n == u,
            (Value::Null, Value::Null) => true,
            _ => false,
        }
    }
}

impl Value {
    pub fn get_type(&self) -> &'static str {
        match &self {
            &Value::Number(_) => "number",
            &Value::Bool(_) => "bool",
            &Value::Func(_) => "function",
            &Value::Null => "null",
            &Value::UserFunc { .. } => "function",
        }
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            &Value::Number(n) => write!(fmt, "Number({})", n),
            &Value::Bool(b) => write!(fmt, "Bool({})", b),
            &Value::Null => write!(fmt, "Null"),
            &Value::Func(_) => write!(fmt, "Function"),
            &Value::UserFunc { .. } => write!(fmt, "Function"),
        }
    }
}

impl Into<Value> for f64 {
    fn into(self) -> Value {
        Value::Number(self)
    }
}

impl TryFrom<Value> for f64 {
    type Error = String;
    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Number(n) => Ok(n),
            _ => Err("invalid try_from type".to_string()),
        }
    }
}

impl Into<Value> for bool {
    fn into(self) -> Value {
        Value::Bool(self)
    }
}

impl ToString for Value {
    fn to_string(&self) -> String {
        match self {
            Value::Number(n) => n.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Null => "null".into(),
            Value::Func(_) => "function".into(),
            &Value::UserFunc { .. } => "function".into(),
        }
    }
}

type FunctionType = Rc<dyn Fn(&[Value]) -> Result<Value, String>>;

/// Struct for storing functions/constants to be used in an expression
#[derive(Clone)]
pub struct Context {
    variables: HashMap<String, Value>,
    functions: HashMap<String, FunctionType>,
}

impl Context {
    /// construct a new Context with empty variables/functions
    pub fn new() -> Self {
        Self {
            variables: HashMap::new(),
            functions: HashMap::new(),
        }
    }

    /// construct a new Context with builtin math functions and constants
    pub fn with_builtins() -> Self {
        let mut ctx = Context::new();
        ctx.var("pi".to_string(), consts::PI.into());
        ctx.var('π'.to_string(), consts::PI.into());
        ctx.var("tau".to_string(), consts::TAU.into());
        ctx.var('τ'.to_string(), consts::TAU.into());
        ctx.var("e".to_string(), consts::E.into());
        ctx.var("inf".to_string(), f64::INFINITY.into());
        ctx.var('∞'.to_string(), f64::INFINITY.into());
        ctx.var("nan".to_string(), f64::NAN.into());
        ctx.func1("sqrt".to_string(), f64::sqrt);
        ctx.func1("cbrt".to_string(), f64::cbrt);
        ctx.func1("ceil".to_string(), f64::ceil);
        ctx.func1("floor".to_string(), f64::floor);
        ctx.func1("round".to_string(), f64::round);
        ctx.func1("cos".to_string(), f64::cos);
        ctx.func1("sin".to_string(), f64::sin);
        ctx.func1("tan".to_string(), f64::tan);
        ctx.func1("acos".to_string(), f64::acos);
        ctx.func1("asin".to_string(), f64::asin);
        ctx.func1("atan".to_string(), f64::atan);
        ctx.func2("atan2".to_string(), f64::atan2);
        ctx.func1("cosh".to_string(), f64::cosh);
        ctx.func1("sinh".to_string(), f64::sinh);
        ctx.func1("tanh".to_string(), f64::tanh);
        ctx.func1("abs".to_string(), f64::abs);
        ctx.func2("log".to_string(), f64::log);
        ctx.func1("log2".to_string(), f64::log2);
        ctx.func1("log10".to_string(), f64::log10);
        ctx
    }

    /// Adds a new variable
    ///
    /// # Example
    ///
    /// ```rust
    /// use blanc::eval::{Context, Value};
    /// let mut ctx = Context::new();
    /// ctx.var("foo".to_string(), Value::Number(5.0));
    /// ```
    pub fn var(&mut self, name: String, value: Value) {
        self.variables.insert(name, value);
    }

    /// Fetch a variable
    ///
    /// # Example
    ///
    /// ```rust
    /// use blanc::eval::{Context, Value};
    /// let mut ctx = Context::new();
    /// let name = String::from("foo");
    /// ctx.var(name.clone(), Value::Number(5.0));
    /// assert_eq!(ctx.get(name.clone()), Some(&Value::Number(5.0)));
    /// ```
    pub fn get_var(&self, name: &String) -> Option<&Value> {
        self.variables.get(name)
    }

    /// Fetch a function
    ///
    /// # Example
    ///
    /// ```rust
    /// use blanc::eval::{Context, Value};
    /// let ctx = Context::with_builtins();
    /// let function = ctx.get_function("sqrt".to_string()).unwrap();
    /// assert_eq!(function(&[Value::Number(25.0)]), Ok(Value::Number(5.0)));
    /// ```
    pub fn get_func(&self, name: &String) -> Option<&FunctionType> {
        self.functions.get(name)
    }

    /// Adds a new function
    ///
    /// # Exampke
    ///
    /// ```rust
    /// fn function(_: &[Value]) -> Result<Value, String> {
    ///      Ok(Value::Number(5.0))
    /// }
    /// fn main() {
    ///      use blanc::eval::{Context, Value};
    ///      let mut ctx = Context::new();
    ///      ctx.func("get_five".to_string(), &function, 0);
    /// }
    /// ```
    pub fn func(
        &mut self,
        name: String,
        func: &'static dyn Fn(&[Value]) -> Result<Value, String>,
        arg_count: usize,
    ) {
        let fnc = move |args: &[Value]| {
            if args.len() != arg_count {
                Err(format!("umatched arguments count function requires {} arguments, you supplied {} arguments",
                            arg_count, args.len()))
            } else {
                func(args)
            }
        };
        self.functions.insert(name, Rc::new(fnc));
    }

    /// Adds a new function that accepts a single argument
    ///
    /// # Example
    ///
    /// ```rust
    /// /// any argument type/return type is allowed as long as it's convertible to eval::Value
    /// fn function(arg: f64) -> f64 {
    ///      arg + 2.0
    /// }
    /// fn main() {
    ///      use blanc::eval::{Context, Value};
    ///      let mut ctx = Context::new();
    ///      ctx.func1("add_two".to_string(), &function);
    /// }
    /// ```
    pub fn func1<F, T, U>(&mut self, name: String, func: F)
    where
        T: TryFrom<Value, Error = String>,
        U: Into<Value>,
        F: Fn(T) -> U + 'static,
    {
        let fnc = move |args: &[Value]| -> Result<Value, String> {
            if args.len() != 1 {
                Err(format!("umatched arguments count function requires a single argument, you supplied {} arguments",
                            args.len()))
            } else {
                let arg: T = T::try_from(args[0].clone())?;
                Value::try_from(func(arg))
                    .map_err(|_| "failed to convert function return type".to_string())
            }
        };
        self.functions.insert(name, Rc::new(fnc));
    }

    /// Adds a new function that accepts two arguments
    ///
    /// # Example
    ///
    /// ```rust
    /// /// any argument type/return type is allowed as long as it's convertible to eval::Value
    /// fn function(a: f64, b: f64) -> f64 {
    ///      a + b
    /// }
    /// fn main() {
    ///      use blanc::eval::{Context, Value};
    ///      let mut ctx = Context::new();
    ///      ctx.func2("sum2".to_string(), &function);
    /// }
    /// ```
    pub fn func2<F, T, U, J>(&mut self, name: String, func: F)
    where
        T: TryFrom<Value, Error = String>,
        U: TryFrom<Value, Error = String>,
        J: Into<Value>,
        F: Fn(T, U) -> J + 'static,
    {
        let fnc = move |args: &[Value]| {
            if args.len() != 2 {
                Err(format!("umatched arguments count function requires 2 arguments, you supplied {} arguments",
                            args.len()))
            } else {
                let arg1: T = T::try_from(args[0].clone())?;
                let arg2: U = U::try_from(args[1].clone())?;
                Value::try_from(func(arg1, arg2))
                    .map_err(|_| "failed to convert function return type".to_string())
            }
        };
        self.functions.insert(name, Rc::new(fnc));
    }

    /// Adds a new function that accepts three arguments
    ///
    /// # Example
    ///
    /// ```rust
    /// /// any argument type/return type is allowed as long as it's convertible to eval::Value
    /// fn function(a: f64, b: f64, c: f64) -> f64 {
    ///      a + b + c
    /// }
    /// fn main() {
    ///      use blanc::eval::{Context, Value};
    ///      let mut ctx = Context::new();
    ///      ctx.func3("sum3".to_string(), &function);
    /// }
    /// ```
    pub fn func3<F, T, U, J, V>(&mut self, name: String, func: F)
    where
        T: TryFrom<Value, Error = String>,
        U: TryFrom<Value, Error = String>,
        J: TryFrom<Value, Error = String>,
        V: Into<Value>,
        F: Fn(T, U, J) -> V + 'static,
    {
        let fnc = move |args: &[Value]| {
            if args.len() != 3 {
                Err(format!("umatched arguments count function requires 3 arguments, you supplied {} arguments",
                            args.len()))
            } else {
                let arg1: T = T::try_from(args[0].clone())?;
                let arg2: U = U::try_from(args[1].clone())?;
                let arg3: J = J::try_from(args[2].clone())?;
                Value::try_from(func(arg1, arg2, arg3))
                    .map_err(|_| "failed to convert function return type".to_string())
            }
        };
        self.functions.insert(name, Rc::new(fnc));
    }

    /// Adds a new function that accepts four arguments
    ///
    /// # Example
    ///
    /// ```rust
    /// /// any argument type/return type is allowed as long as it's convertible to eval::Value
    /// fn function(a: f64, b: f64, c: f64, d: f64) -> f64 {
    ///      a + b + c + d
    /// }
    /// fn main() {
    ///      use blanc::eval::{Context, Value};
    ///      let mut ctx = Context::new();
    ///      ctx.func4("sum4".to_string(), &function);
    /// }
    /// ```
    pub fn func4<F, T, U, J, V, Z>(&mut self, name: String, func: F)
    where
        T: TryFrom<Value, Error = String>,
        U: TryFrom<Value, Error = String>,
        J: TryFrom<Value, Error = String>,
        V: TryFrom<Value, Error = String>,
        Z: Into<Value>,
        F: Fn(T, U, J, V) -> Z + 'static,
    {
        let fnc = move |args: &[Value]| {
            if args.len() != 4 {
                Err(format!("umatched arguments count function requires 4 arguments, you supplied {} arguments",
                            args.len()))
            } else {
                let arg1: T = T::try_from(args[0].clone())?;
                let arg2: U = U::try_from(args[1].clone())?;
                let arg3: J = J::try_from(args[2].clone())?;
                let arg4: V = V::try_from(args[3].clone())?;
                Value::try_from(func(arg1, arg2, arg3, arg4))
                    .map_err(|_| "failed to convert function return type".to_string())
            }
        };
        self.functions.insert(name, Rc::new(fnc));
    }

    /// Adds a new function that accepts five arguments
    ///
    /// # Example
    ///
    /// ```rust
    /// /// any argument type/return type is allowed as long as it's convertible to eval::Value
    /// fn function(a: f64, b: f64, c: f64, d: f64, j: f64) -> f64 {
    ///      a + b + c + d + j
    /// }
    /// fn main() {
    ///      use blanc::eval::{Context, Value};
    ///      let mut ctx = Context::new();
    ///      ctx.func5("sum5".to_string(), &function);
    /// }
    /// ```
    pub fn func5<F, T, U, J, V, Z, Y>(&mut self, name: String, func: F)
    where
        T: TryFrom<Value, Error = String>,
        U: TryFrom<Value, Error = String>,
        J: TryFrom<Value, Error = String>,
        V: TryFrom<Value, Error = String>,
        Z: TryFrom<Value, Error = String>,
        Y: Into<Value>,
        F: Fn(T, U, J, V, Z) -> Y + 'static,
    {
        let fnc = move |args: &[Value]| {
            if args.len() != 4 {
                Err(format!("umatched arguments count function requires 5 arguments, you supplied {} arguments",
                            args.len()))
            } else {
                let arg1: T = T::try_from(args[0].clone())?;
                let arg2: U = U::try_from(args[1].clone())?;
                let arg3: J = J::try_from(args[2].clone())?;
                let arg4: V = V::try_from(args[3].clone())?;
                let arg5: Z = Z::try_from(args[4].clone())?;
                Value::try_from(func(arg1, arg2, arg3, arg4, arg5))
                    .map_err(|_| "failed to convert function return type".to_string())
            }
        };
        self.functions.insert(name, Rc::new(fnc));
    }
}

/// struct for evaluating expressions
pub struct Eval {
    expr: Vec<Expression>,
    context: Context,
    max_precision: f64,
}

impl Eval {
    /// constructs a new Eval from the given vector of expressions along side with builtin context
    pub fn new(expr: Vec<Expression>) -> Self {
        Self {
            expr: expr,
            context: Context::with_builtins(),
            max_precision: 1e8,
        }
    }

    /// constructs a new Eval from the given vector of expressions along side with custom context
    pub fn with_context(expr: Vec<Expression>, ctx: Context) -> Self {
        Self {
            expr: expr,
            context: ctx,
            max_precision: 1e8,
        }
    }

    /// get a reference to eval's context
    pub fn get_context(&self) -> &Context {
        &self.context
    }

    /// get a mutable reference to eval's context
    pub fn get_context_mut(&mut self) -> &mut Context {
        &mut self.context
    }

    /// set eval's context
    pub fn set_context(&mut self, ctx: Context) {
        self.context = ctx;
    }

    /// main function for evaluation expressions
    pub fn eval_expr(&mut self, expr: &Expression) -> error::Result<Value> {
        match expr {
            Expression::Number(_, x) => Ok(Value::Number(f64::trunc(*x * 1e7) / 1e7)),
            Expression::Bool(_, b) => Ok(Value::Bool(*b)),
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
                    .map(|arg| -> error::Result<Value> { self.eval_expr(arg) })
                    .collect::<error::Result<Vec<Value>>>()?,
                loc.clone(),
                self,
            ),
            Expression::Unary(loc, Operator::Negative, box expr) => {
                let temp = self.eval_expr(expr)?;
                self.neg(temp, loc.clone())
            }

            Expression::Unary(_, Operator::Positive, box expr) => self.eval_expr(expr),

            Expression::Unary(loc, Operator::Not, box expr) => {
                let temp = self.eval_expr(expr)?;
                self.not(temp, loc.clone())
            }

            Expression::Unary(loc, Operator::Factorial, box expr) => {
                let temp = self.eval_expr(expr)?;
                self.fact(temp, loc.clone())
            }

            Expression::Binary(loc, Operator::Plus, box lhs, box rhs) => {
                let temp_lhs = self.eval_expr(lhs)?;
                let temp_rhs = self.eval_expr(rhs)?;
                self.add(temp_lhs, temp_rhs, loc.clone())
            }

            Expression::Binary(loc, Operator::Minus, box lhs, box rhs) => {
                let temp_lhs = self.eval_expr(lhs)?;
                let temp_rhs = self.eval_expr(rhs)?;
                self.sub(temp_lhs, temp_rhs, loc.clone())
            }

            Expression::Binary(loc, Operator::Star, box lhs, box rhs) => {
                let temp_lhs = self.eval_expr(lhs)?;
                let temp_rhs = self.eval_expr(rhs)?;
                self.mul(temp_lhs, temp_rhs, loc.clone())
            }

            Expression::Binary(loc, Operator::Slash, box lhs, box rhs) => {
                let temp_lhs = self.eval_expr(lhs)?;
                let temp_rhs = self.eval_expr(rhs)?;
                self.div(temp_lhs, temp_rhs, loc.clone())
            }

            Expression::Binary(loc, Operator::Power, box lhs, box rhs) => {
                let temp_lhs = self.eval_expr(lhs)?;
                let temp_rhs = self.eval_expr(rhs)?;
                self.power(temp_lhs, temp_rhs, loc.clone())
            }

            Expression::Binary(loc, Operator::And, box lhs, box rhs) => {
                let temp_lhs = self.eval_expr(lhs)?;
                let temp_rhs = self.eval_expr(rhs)?;
                self.and(temp_lhs, temp_rhs, loc.clone())
            }

            Expression::Binary(loc, Operator::Or, box lhs, box rhs) => {
                let temp_lhs = self.eval_expr(lhs)?;
                let temp_rhs = self.eval_expr(rhs)?;
                self.or(temp_lhs, temp_rhs, loc.clone())
            }

            Expression::Binary(loc, Operator::Equal, box lhs, box rhs) => {
                let temp_lhs = self.eval_expr(lhs)?;
                let temp_rhs = self.eval_expr(rhs)?;
                self.equals(temp_lhs, temp_rhs, loc.clone())
            }

            Expression::Binary(loc, Operator::NotEqual, box lhs, box rhs) => {
                let temp_lhs = self.eval_expr(lhs)?;
                let temp_rhs = self.eval_expr(rhs)?;
                self.not_equals(temp_lhs, temp_rhs, loc.clone())
            }

            Expression::Binary(loc, Operator::Greater, box lhs, box rhs) => {
                let temp_lhs = self.eval_expr(lhs)?;
                let temp_rhs = self.eval_expr(rhs)?;
                self.greater(temp_lhs, temp_rhs, loc.clone())
            }

            Expression::Binary(loc, Operator::GreaterOrEqual, box lhs, box rhs) => {
                let temp_lhs = self.eval_expr(lhs)?;
                let temp_rhs = self.eval_expr(rhs)?;
                self.greater_or_equal(temp_lhs, temp_rhs, loc.clone())
            }

            Expression::Binary(loc, Operator::Less, box lhs, box rhs) => {
                let temp_lhs = self.eval_expr(lhs)?;
                let temp_rhs = self.eval_expr(rhs)?;
                self.less(temp_lhs, temp_rhs, loc.clone())
            }

            Expression::Binary(loc, Operator::LessOrEqual, box lhs, box rhs) => {
                let temp_lhs = self.eval_expr(lhs)?;
                let temp_rhs = self.eval_expr(rhs)?;
                self.less_or_equal(temp_lhs, temp_rhs, loc.clone())
            }

            Expression::Binary(loc, Operator::Assign, box lhs, box rhs) => match lhs {
                Expression::Ident(_, ref ident) => {
                    let expr = self.eval_expr(rhs)?;
                    self.context.var(ident.clone(), expr);
                    self.eval_expr(lhs)
                }
                _ => Err(Error::SyntaxError(
                    loc.clone(),
                    "invalid assign syntax".to_string(),
                )),
            },

            Expression::Binary(loc, Operator::Arrow, box lhs, box body) => match lhs {
                Expression::FuncCall(_, box expr, args) => {
                    if !args.iter().all(|arg| matches!(arg, Expression::Ident(..))) {
                        return Err(Error::SyntaxError(
                            loc.clone(),
                            "expected identifier in function parameter".to_string(),
                        ));
                    }
                    if !matches!(expr, Expression::Ident(..)) {
                        return Err(Error::SyntaxError(
                            loc.clone(),
                            "expected identifier in function name".to_string(),
                        ));
                    }
                    let ident_args: Vec<String> = args
                        .into_iter()
                        .map(|expr| match expr {
                            Expression::Ident(_, name) => name.clone(),
                            _ => unreachable!(),
                        })
                        .collect();
                    let function = Value::UserFunc {
                        params: ident_args,
                        body: body.clone(),
                    };
                    let name = match expr {
                        Expression::Ident(_, name) => name.clone(),
                        _ => unreachable!(),
                    };
                    self.context.var(name, function);
                    Ok(Value::Null)
                }
                _ => Err(Error::SyntaxError(
                    loc.clone(),
                    "invalid expression".to_string(),
                )),
            },

            _ => Err(Error::Error("invalid expression".into())),
        }
    }

    pub fn add(&self, lhs: Value, rhs: Value, loc: SourceLocation) -> error::Result<Value> {
        match (&lhs, &rhs) {
            (&Value::Number(n), &Value::Number(m)) => Ok(Value::Number(
                ((n + m) * self.max_precision).trunc() / self.max_precision,
            )),
            _ => Err(Error::TypeError(
                loc,
                format!(
                    "invalid operands for binary operation '+': {} and {}",
                    lhs.get_type(),
                    rhs.get_type()
                ),
            )),
        }
    }

    pub fn sub(&self, lhs: Value, rhs: Value, loc: SourceLocation) -> error::Result<Value> {
        match (&lhs, &rhs) {
            (&Value::Number(n), &Value::Number(m)) => Ok(Value::Number(
                ((n - m) * self.max_precision).trunc() / self.max_precision,
            )),
            _ => Err(Error::TypeError(
                loc,
                format!(
                    "invalid operands for binary operation '-': {} and {}",
                    lhs.get_type(),
                    rhs.get_type()
                ),
            )),
        }
    }

    pub fn div(&self, lhs: Value, rhs: Value, loc: SourceLocation) -> error::Result<Value> {
        match (&lhs, &rhs) {
            (&Value::Number(n), &Value::Number(m)) => Ok(Value::Number(
                (n / m * self.max_precision).trunc() / self.max_precision,
            )),
            _ => Err(Error::TypeError(
                loc,
                format!(
                    "invalid operands for binary operation '/': {} and {}",
                    lhs.get_type(),
                    rhs.get_type()
                ),
            )),
        }
    }

    pub fn mul(&self, lhs: Value, rhs: Value, loc: SourceLocation) -> error::Result<Value> {
        match (&lhs, &rhs) {
            (&Value::Number(n), &Value::Number(m)) => Ok(Value::Number(
                ((n * m) * self.max_precision).trunc() / self.max_precision,
            )),
            _ => Err(Error::TypeError(
                loc,
                format!(
                    "invalid operands for binary operation '-': {} and {}",
                    lhs.get_type(),
                    rhs.get_type()
                ),
            )),
        }
    }

    pub fn power(&self, lhs: Value, rhs: Value, loc: SourceLocation) -> error::Result<Value> {
        match (&lhs, &rhs) {
            (&Value::Number(n), &Value::Number(m)) => Ok(Value::Number(
                (n.powf(m) * self.max_precision).trunc() / self.max_precision,
            )),
            _ => Err(Error::TypeError(
                loc,
                format!(
                    "invalid operands for binary operation '^': {} and {}",
                    lhs.get_type(),
                    rhs.get_type()
                ),
            )),
        }
    }

    pub fn neg(&self, lhs: Value, loc: SourceLocation) -> error::Result<Value> {
        match &lhs {
            &Value::Number(n) => Ok(Value::Number(
                (-n * self.max_precision).trunc() / self.max_precision,
            )),
            _ => Err(Error::TypeError(
                loc,
                format!(
                    "invalid operands for unary operation '-': {}",
                    lhs.get_type(),
                ),
            )),
        }
    }

    pub fn not(&self, lhs: Value, loc: SourceLocation) -> error::Result<Value> {
        match &lhs {
            &Value::Bool(b) => Ok(Value::Bool(!b)),
            _ => Err(Error::TypeError(
                loc,
                format!(
                    "invalid operands for unary operation '!': {}",
                    lhs.get_type(),
                ),
            )),
        }
    }

    pub fn fact(&self, lhs: Value, loc: SourceLocation) -> error::Result<Value> {
        match &lhs {
            &Value::Number(n) => {
                let mut u = 1usize;
                if n < 0f64 {
                    return Err(Error::RuntimeError(
                        loc.clone(),
                        "factorial operand must not be negative".to_string(),
                    ));
                }
                for i in 1..=(n as usize) {
                    u = u.checked_mul(i).ok_or(Error::RuntimeError(
                        loc.clone(),
                        "operation results in an overflow".to_string(),
                    ))?;
                }

                Ok(Value::Number(u as f64))
            }
            _ => Err(Error::TypeError(
                loc,
                format!("invalid operands for factorial '!': {}", lhs.get_type(),),
            )),
        }
    }

    pub fn equals(&self, lhs: Value, rhs: Value, loc: SourceLocation) -> error::Result<Value> {
        match (&lhs, &rhs) {
            (&Value::Number(n), &Value::Number(u)) => Ok(Value::Bool(n == u)),
            (&Value::Bool(n), &Value::Bool(u)) => Ok(Value::Bool(n == u)),
            (&Value::Null, &Value::Null) => Ok(Value::Bool(true)),
            _ => Err(Error::TypeError(
                loc,
                format!(
                    "invalid operands for comparison '==': {} and {}",
                    lhs.get_type(),
                    rhs.get_type()
                ),
            )),
        }
    }

    pub fn not_equals(&self, lhs: Value, rhs: Value, loc: SourceLocation) -> error::Result<Value> {
        match (&lhs, &rhs) {
            (&Value::Number(n), &Value::Number(u)) => Ok(Value::Bool(n != u)),
            (&Value::Bool(n), &Value::Bool(u)) => Ok(Value::Bool(n != u)),
            (&Value::Null, &Value::Null) => Ok(Value::Bool(false)),
            _ => Err(Error::TypeError(
                loc,
                format!(
                    "invalid operands for comparison '!=': {} and {}",
                    lhs.get_type(),
                    rhs.get_type()
                ),
            )),
        }
    }

    pub fn greater(&self, lhs: Value, rhs: Value, loc: SourceLocation) -> error::Result<Value> {
        match (&lhs, &rhs) {
            (&Value::Number(n), &Value::Number(u)) => Ok(Value::Bool(n > u)),
            (&Value::Bool(n), &Value::Bool(u)) => Ok(Value::Bool(n > u)),
            (&Value::Null, &Value::Null) => Ok(Value::Bool(false)),
            _ => Err(Error::TypeError(
                loc,
                format!(
                    "invalid operands for comparison '>': {} and {}",
                    lhs.get_type(),
                    rhs.get_type()
                ),
            )),
        }
    }

    pub fn greater_or_equal(
        &self,
        lhs: Value,
        rhs: Value,
        loc: SourceLocation,
    ) -> error::Result<Value> {
        match (&lhs, &rhs) {
            (&Value::Number(n), &Value::Number(u)) => Ok(Value::Bool(n >= u)),
            (&Value::Bool(n), &Value::Bool(u)) => Ok(Value::Bool(n >= u)),
            (&Value::Null, &Value::Null) => Ok(Value::Bool(true)),
            _ => Err(Error::TypeError(
                loc,
                format!(
                    "invalid operands for comparison '>=': {} and {}",
                    lhs.get_type(),
                    rhs.get_type()
                ),
            )),
        }
    }

    pub fn less(&self, lhs: Value, rhs: Value, loc: SourceLocation) -> error::Result<Value> {
        match (&lhs, &rhs) {
            (&Value::Number(n), &Value::Number(u)) => Ok(Value::Bool(n < u)),
            (&Value::Bool(n), &Value::Bool(u)) => Ok(Value::Bool(n < u)),
            (&Value::Null, &Value::Null) => Ok(Value::Bool(false)),
            _ => Err(Error::TypeError(
                loc,
                format!(
                    "invalid operands for comparison '<': {} and {}",
                    lhs.get_type(),
                    rhs.get_type()
                ),
            )),
        }
    }

    pub fn less_or_equal(
        &self,
        lhs: Value,
        rhs: Value,
        loc: SourceLocation,
    ) -> error::Result<Value> {
        match (&lhs, &rhs) {
            (&Value::Number(n), &Value::Number(u)) => Ok(Value::Bool(n <= u)),
            (&Value::Bool(n), &Value::Bool(u)) => Ok(Value::Bool(n <= u)),
            (&Value::Null, &Value::Null) => Ok(Value::Bool(true)),
            _ => Err(Error::TypeError(
                loc,
                format!(
                    "invalid operands for comparison '<=': {} and {}",
                    lhs.get_type(),
                    rhs.get_type()
                ),
            )),
        }
    }

    pub fn and(&self, lhs: Value, rhs: Value, loc: SourceLocation) -> error::Result<Value> {
        match (&lhs, &rhs) {
            (&Value::Bool(n), &Value::Bool(u)) => Ok(Value::Bool(n && u)),
            _ => Err(Error::TypeError(
                loc,
                format!(
                    "invalid operands for logical and '&&': {} and {}",
                    lhs.get_type(),
                    rhs.get_type()
                ),
            )),
        }
    }

    pub fn or(&self, lhs: Value, rhs: Value, loc: SourceLocation) -> error::Result<Value> {
        match (&lhs, &rhs) {
            (&Value::Bool(n), &Value::Bool(u)) => Ok(Value::Bool(n || u)),
            _ => Err(Error::TypeError(
                loc,
                format!(
                    "invalid operands for logical or '||': {} and {}",
                    lhs.get_type(),
                    rhs.get_type()
                ),
            )),
        }
    }

    pub fn eval(&mut self) -> error::Result<Value> {
        let mut iter = self.expr.clone().into_iter();
        let next = match iter.next() {
            Some(x) => x,
            None => return Ok(Value::Null),
        };
        let mut out: Value = self.eval_expr(&next)?;
        for expr in iter {
            out = self.eval_expr(&expr)?;
        }
        Ok(out)
    }
}
