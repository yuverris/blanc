use crate::{
    error::{self, Error},
    lexer::Operator,
    parser::Expression,
    source_location::SourceLocation,
    try_err, try_return,
    utils::{FloatExt, RResult},
};

use std::{collections::HashMap, convert::TryFrom, fmt, rc::Rc, string::ToString};
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
    /// for representing numeric values
    Number(i128),
    /// for representing floating point values
    Float(f64),
    /// for representing boolean values
    Bool(bool),
    /// for handeling strings
    String(String),
    /// for handeling characters
    Char(char),
    /// for representing binded functions
    Func(FunctionType),
    /// for representing user defined functions
    UserFunc {
        params: Vec<String>,
        body: Expression,
    },
    /// for representing arrays
    Array(Vec<Self>),
    Null,
    Void,
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
                        loc,
                        format!(
                            "function requires {} arguments, you supplied {}",
                            params.len(),
                            args.len()
                        ),
                    ));
                }
                // store old state of the context and bind parameters names to the current context
                // then reset the context to its old state after function call
                let context = eval.get_context_mut();
                let previous = context.clone();
                for (param, arg) in params.iter().zip(args) {
                    context.var(param.clone(), arg, false);
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
impl FloatExt for f64 {
    fn approx_eq(self, other: Self) -> bool {
        (self - other).abs() < f64::EPSILON
    }

    fn checked_add(self, other: Self) -> Option<Self> {
        let res = self + other;
        if res.is_infinite() || res.approx_eq(Self::MAX) || res.approx_eq(Self::MIN) {
            None
        } else {
            Some(res)
        }
    }

    fn checked_sub(self, other: Self) -> Option<Self> {
        let res = self - other;
        if res.is_infinite() || res.approx_eq(f64::MAX) || res.approx_eq(Self::MIN) {
            None
        } else {
            Some(res)
        }
    }

    fn checked_mul(self, other: Self) -> Option<Self> {
        let res = self * other;
        if res.is_infinite() {
            None
        } else {
            Some(res)
        }
    }

    fn checked_div(self, other: Self) -> Option<Self> {
        let res = self / other;
        if res.is_nan() {
            None
        } else {
            Some(res)
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Float(n), Value::Float(u)) => n == u,
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
            Value::Float(_) => "float",
            Value::Number(_) => "number",
            Value::String(_) => "string",
            Value::Char(_) => "char",
            Value::Array(_) => "array",
            Value::Bool(_) => "bool",
            Value::Func(_) => "function",
            Value::Null => "null",
            Value::UserFunc { .. } => "function",
            Value::Void => "void",
        }
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Value::Float(n) => write!(fmt, "Float({})", n),
            Value::Number(n) => write!(fmt, "Number({})", n),
            Value::Char(c) => write!(fmt, "Char({})", c),
            Value::String(s) => write!(fmt, "String({})", s),
            Value::Array(a) => write!(fmt, "Array({:?})", a),
            Value::Bool(b) => write!(fmt, "Bool({})", b),
            Value::Null => write!(fmt, "Null"),
            Value::Func(_) => write!(fmt, "Function"),
            Value::UserFunc { .. } => write!(fmt, "Function"),
            Value::Void => write!(fmt, "Void"),
        }
    }
}

impl From<f64> for Value {
    fn from(value: f64) -> Value {
        Value::Float(value)
    }
}

impl From<i128> for Value {
    fn from(value: i128) -> Value {
        Value::Number(value)
    }
}

impl From<String> for Value {
    fn from(value: String) -> Value {
        Value::String(value)
    }
}

impl From<char> for Value {
    fn from(value: char) -> Value {
        Value::Char(value)
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Value {
        Value::Bool(value)
    }
}

impl From<()> for Value {
    fn from(_: ()) -> Value {
        Value::Void
    }
}

impl<T> From<Vec<T>> for Value
where
    Value: From<T>,
{
    fn from(value: Vec<T>) -> Value {
        Value::Array(value.into_iter().map(Value::from).collect())
    }
}

impl<T: Into<Value>> From<Option<T>> for Value {
    fn from(value: Option<T>) -> Value {
        match value {
            Some(t) => t.into(),
            None => Value::Null,
        }
    }
}

impl TryFrom<Value> for f64 {
    type Error = String;
    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Float(n) => Ok(n),
            _ => Err("invalid try_from type".to_string()),
        }
    }
}

impl TryFrom<Value> for i128 {
    type Error = String;
    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Number(n) => Ok(n),
            _ => Err("invalid try_from type".to_string()),
        }
    }
}
impl ToString for Value {
    fn to_string(&self) -> String {
        match self {
            Value::Float(n) => n.to_string(),
            Value::String(s) => s.clone(),
            Value::Char(c) => c.to_string(),
            Value::Array(elements) => {
                let mut res = String::from('[');
                for (index, elm) in elements.iter().enumerate() {
                    if let Value::String(s) = elm {
                        res.push_str(format!("\"{}\"", s).as_str());
                    } else if let Value::Char(c) = elm {
                        res.push_str(format!("'{}'", c).as_str());
                    } else {
                        res.push_str(elm.to_string().as_str());
                    }
                    if index != elements.len() - 1 {
                        res.push_str(", ");
                    }
                }
                res.push(']');
                res
            }
            Value::Number(n) => n.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Null => "null".into(),
            Value::Func(_) => "function".into(),
            Value::UserFunc { .. } => "function".into(),
            Value::Void => '\0'.into(),
        }
    }
}

type FunctionType = Rc<dyn Fn(&[Value]) -> Result<Value, String>>;

#[derive(Clone)]
pub struct VariableHandle {
    pub value: Value,
    pub is_immutable: bool,
}

/// Struct for storing functions/constants to be used in an expression
#[derive(Clone)]
pub struct Context {
    variables: HashMap<String, VariableHandle>,
    functions: HashMap<String, FunctionType>,
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
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
        ctx.func(
            "print",
            &|args: &[Value]| {
                args.iter().for_each(|a| print!("{} ", a.to_string()));
                println!();
                Ok(Value::Null)
            },
            0,
            true,
        );
        ctx
    }

    /// Adds a new variable
    ///
    /// # Example
    ///
    /// ```rust
    /// use blanc::eval::{Context, Value};
    /// let mut ctx = Context::new();
    /// ctx.var("foo", 5.0, false);
    /// ```
    pub fn var<S, T>(&mut self, name: S, value: T, immutable: bool)
    where
        S: ToString,
        T: Into<Value>,
    {
        self.variables.insert(
            name.to_string(),
            VariableHandle {
                value: value.into(),
                is_immutable: immutable,
            },
        );
    }

    /// Fetch a variable
    ///
    /// # Example
    ///
    /// ```rust
    /// use blanc::eval::{Context, Value};
    /// let mut ctx = Context::new();
    /// let name = String::from("foo");
    /// ctx.var(name.clone(), 5.0, false));
    /// assert_eq!(ctx.get(name.clone()), Some(&Value::from(5.0)));
    /// ```
    pub fn get_var(&self, name: String) -> Option<&Value> {
        match self.variables.get(&name) {
            Some(handle) => Some(&handle.value),
            _ => None,
        }
    }

    /// Get a mutable reference to the variable handle
    pub fn get_mut_var_handle(&mut self, name: String) -> Option<&mut VariableHandle> {
        self.variables.get_mut(&name)
    }

    /// Get a reference to the variable handle
    pub fn get_var_handle(&self, name: String) -> Option<&VariableHandle> {
        self.variables.get(&name)
    }

    /// Fetch a function
    ///
    /// # Example
    ///
    /// ```rust
    /// use blanc::eval::{Context, Value};
    /// let ctx = Context::with_builtins();
    /// let function = ctx.get_function("sqrt".to_string()).unwrap();
    /// assert_eq!(function(&[Value::Float(25.0)]), Ok(Value::from(5.0)));
    /// ```
    pub fn get_func(&self, name: String) -> Option<&FunctionType> {
        self.functions.get(&name)
    }

    /// Adds a new function
    ///
    /// # Exampke
    ///
    /// ```rust
    /// fn function(_: &[Value]) -> Result<Value, String> {
    ///      Ok(Value::Float(5.0))
    /// }
    /// fn main() {
    ///      use blanc::eval::{Context, Value};
    ///      let mut ctx = Context::new();
    ///      ctx.func("get_five".to_string(), function, 0, false);
    /// }
    /// ```
    pub fn func<S>(
        &mut self,
        name: S,
        func: &'static dyn Fn(&[Value]) -> Result<Value, String>,
        arg_count: usize,
        inf_args: bool,
    ) where
        S: ToString,
    {
        let fnc = move |args: &[Value]| {
            if args.len() != arg_count && !inf_args {
                Err(format!("umatched arguments count function requires {} arguments, you supplied {} arguments",
                            arg_count, args.len()))
            } else {
                func(args)
            }
        };
        self.functions.insert(name.to_string(), Rc::new(fnc));
    }

    /// Adds a new function that accepts a single argument
    ///
    /// # Example
    ///
    /// ```rust
    /// // any argument type/return type is allowed as long as it's convertible to eval::Value
    /// fn function(arg: f64) -> f64 {
    ///      arg + 2.0
    /// }
    /// fn main() {
    ///      use blanc::eval::{Context, Value};
    ///      let mut ctx = Context::new();
    ///      ctx.func1("add_two".to_string(), function);
    /// }
    /// ```
    pub fn func1<S, F, T, U>(&mut self, name: S, func: F)
    where
        S: ToString,
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
        self.functions.insert(name.to_string(), Rc::new(fnc));
    }

    /// Adds a new function without arguments
    ///
    /// # Example
    ///
    /// ```rust
    /// // any argument type/return type is allowed as long as it's convertible to eval::Value
    /// fn function() -> i128 {
    ///      
    /// }
    /// fn main() {
    ///      use blanc::eval::{Context, Value};
    ///      let mut ctx = Context::new();
    ///      ctx.func0("foo".to_string(), function);
    /// }
    /// ```
    pub fn func0<S, F, U>(&mut self, name: S, func: F)
    where
        S: ToString,
        U: Into<Value>,
        F: Fn() -> U + 'static,
    {
        let fnc = move |args: &[Value]| -> Result<Value, String> {
            if !args.is_empty() {
                Err(format!("umatched arguments count function doesn't require any arguments, you supplied {} arguments",
                            args.len()))
            } else {
                Value::try_from(func())
                    .map_err(|_| "failed to convert function return type".to_string())
            }
        };
        self.functions.insert(name.to_string(), Rc::new(fnc));
    }

    /// Adds a new function that accepts two arguments
    ///
    /// # Example
    ///
    /// ```rust
    /// // any argument type/return type is allowed as long as it's convertible to eval::Value
    /// fn function(a: i128, b: i128) -> i128 {
    ///      a + b
    /// }
    /// fn main() {
    ///      use blanc::eval::{Context, Value};
    ///      let mut ctx = Context::new();
    ///      ctx.func2("sum2", function);
    /// }
    /// ```
    pub fn func2<S, F, T, U, J>(&mut self, name: S, func: F)
    where
        S: ToString,
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
        self.functions.insert(name.to_string(), Rc::new(fnc));
    }

    /// Adds a new function that accepts three arguments
    ///
    /// # Example
    ///
    /// ```rust
    /// // any argument type/return type is allowed as long as it's convertible to eval::Value
    /// fn function(a: i128, b: i128, c: i128) -> i128 {
    ///      a + b + c
    /// }
    /// fn main() {
    ///      use blanc::eval::{Context, Value};
    ///      let mut ctx = Context::new();
    ///      ctx.func3("sum3", function);
    /// }
    /// ```
    pub fn func3<S, F, T, U, J, V>(&mut self, name: String, func: F)
    where
        S: ToString,
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
    /// // any argument type/return type is allowed as long as it's convertible to eval::Value
    /// fn function(a: i128, b: i128, c: i128, d: i128) -> i128 {
    ///      a + b + c + d
    /// }
    /// fn main() {
    ///      use blanc::eval::{Context, Value};
    ///      let mut ctx = Context::new();
    ///      ctx.func4("sum4", function);
    /// }
    /// ```
    pub fn func4<S, F, T, U, J, V, Z>(&mut self, name: S, func: F)
    where
        S: ToString,
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
        self.functions.insert(name.to_string(), Rc::new(fnc));
    }

    /// Adds a new function that accepts five arguments
    ///
    /// # Example
    ///
    /// ```rust
    /// // any argument type/return type is allowed as long as it's convertible to eval::Value
    /// fn function(a: i128, b: i128, c: i128, d: i128, j: i128) -> f64 {
    ///      a + b + c + d + j
    /// }
    /// fn main() {
    ///      use blanc::eval::{Context, Value};
    ///      let mut ctx = Context::new();
    ///      ctx.func5("sum5", function);
    /// }
    /// ```
    pub fn func5<S, F, T, U, J, V, Z, Y>(&mut self, name: S, func: F)
    where
        S: ToString,
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
        self.functions.insert(name.to_string(), Rc::new(fnc));
    }
}

/// struct for evaluating expressions
pub struct Eval {
    /// list of expressions to evaluate
    expr: Vec<Expression>,
    /// context to lookup for variables/functions
    context: Context,
    /// maximum precision that a number can hold
    max_precision: f64,
}

use RResult::*;
impl Eval {
    /// constructs a new Eval from the given vector of expressions along side with builtin context
    pub fn new(expr: Vec<Expression>) -> Self {
        Self {
            expr,
            context: Context::with_builtins(),
            max_precision: 1e8,
        }
    }

    /// constructs a new empty Eval with builtin context
    pub fn new_empty() -> Self {
        Self {
            expr: Vec::new(),
            context: Context::with_builtins(),
            max_precision: 1e8,
        }
    }

    /// constructs a new Eval from the given vector of expressions along side with custom context
    pub fn with_context(expr: Vec<Expression>, ctx: Context) -> Self {
        Self {
            expr,
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
    pub fn eval_expr(&mut self, expr: &Expression) -> RResult<Value, Error, Value> {
        match expr {
            Expression::Float(_, x) => Ok(Value::Float(*x)),
            Expression::String(_, s) => Ok(Value::String(s.clone())),
            Expression::Char(_, c) => Ok(Value::Char(*c)),
            Expression::Array(_, exprs) => {
                let inner = try_err!(exprs
                    .iter()
                    .map(|elm| -> RResult<Value, Error, Value> { self.eval_expr(elm) })
                    .collect::<RResult<Vec<Value>, Error, Value>>());
                Ok(Value::Array(inner))
            }
            Expression::Number(_, x) => Ok(Value::Number(*x)),
            Expression::Bool(_, b) => Ok(Value::Bool(*b)),
            Expression::Null(_) => Ok(Value::Null),
            Expression::Ident(loc, i) => {
                if let Some(v) = self.context.get_var(i.clone()) {
                    Ok(v.clone())
                } else if let Some(f) = self.context.get_func(i.clone()) {
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
                let temp = try_err!(self.eval_expr(expr));
                self.neg(temp, loc.clone())
            }

            Expression::Unary(_, Operator::Positive, box expr) => self.eval_expr(expr),

            Expression::Unary(loc, Operator::Not, box expr) => {
                let temp = try_err!(self.eval_expr(expr));
                self.not(temp, loc.clone())
            }

            Expression::Binary(loc, Operator::Plus, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = self.eval_expr(rhs)?;
                self.add(temp_lhs, temp_rhs, loc.clone())
            }

            Expression::Binary(loc, Operator::Minus, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = try_err!(self.eval_expr(rhs));
                self.sub(temp_lhs, temp_rhs, loc.clone())
            }

            Expression::Binary(loc, Operator::Star, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = try_err!(self.eval_expr(rhs));
                self.mul(temp_lhs, temp_rhs, loc.clone())
            }

            Expression::Binary(loc, Operator::Slash, box lhs, box rhs) => {
                let temp_lhs = self.eval_expr(lhs)?;
                let temp_rhs = self.eval_expr(rhs)?;
                self.div(temp_lhs, temp_rhs, loc.clone())
            }

            Expression::Binary(loc, Operator::BitXor, box lhs, box rhs) => {
                let temp_lhs = self.eval_expr(lhs)?;
                let temp_rhs = self.eval_expr(rhs)?;
                self.bit_xor(temp_lhs, temp_rhs, loc.clone())
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

            Expression::Binary(loc, Operator::Assign, box lhs, box rhs) => {
                let name = match lhs {
                    Expression::Ident(_, name) => name,
                    _ => {
                        return Err(Error::RuntimeError(
                            loc.clone(),
                            "expected identifier as left operand".to_string(),
                        ))
                    }
                };
                let expr = self.eval_expr(rhs)?;
                let var = match self.context.get_mut_var_handle(name.clone()) {
                    Some(handle) => handle,
                    None => {
                        return Err(Error::RuntimeError(
                            loc.clone(),
                            format!("undefined variable {}", name),
                        ))
                    }
                };
                if var.is_immutable {
                    Err(Error::RuntimeError(
                        loc.clone(),
                        "cannot assign to immutable variable".to_string(),
                    ))
                } else {
                    var.value = expr;
                    Ok(Value::Null)
                }
            }

            Expression::Subscript(loc, box lhs, box inner) => {
                let lhs = self.eval_expr(lhs)?;
                let inner = self.eval_expr(inner)?;
                self.index(lhs, inner, loc.clone())
            }

            Expression::Variable(_, name, value, immutable) => {
                let value = match value {
                    Some(expr) => self.eval_expr(expr)?,
                    None => Value::Null,
                };
                self.context.var(name, value, *immutable);
                Ok(Value::Null)
            }

            Expression::Block(_, stmts) => {
                let previous = self.context.clone();
                let mut iter = stmts.iter();
                let next: Expression = match iter.next() {
                    Some(Expression::Return(_, box expr)) => return self.eval_expr(expr),
                    Some(expr) => expr.clone(),
                    None => return Ok(Value::Null),
                };
                let mut out: Value = self.eval_expr(&next)?;
                for expr in iter {
                    match expr {
                        Expression::Return(_, box expr) => {
                            return self.eval_expr(expr);
                        }
                        _ => {
                            out = self.eval_expr(expr)?;
                        }
                    };
                }
                self.context = previous;
                Ok(out)
            }

            Expression::IfStmt(loc, box condition, box body, else_clause) => {
                match self.eval_expr(condition)? {
                    Value::Bool(true) => self.eval_expr(body),
                    Value::Bool(false) => match else_clause {
                        Some(box body) => self.eval_expr(body),
                        None => Ok(Value::Null),
                    },
                    _ => Err(Error::RuntimeError(
                        loc.clone(),
                        "expected boolean in if condition".to_string(),
                    )),
                }
            }

            _ => Err(Error::Error("invalid expression".into())),
        }
    }

    pub fn add(&self, lhs: Value, rhs: Value, loc: SourceLocation) -> error::Result<Value> {
        match (&lhs, &rhs) {
            (Value::Number(n), Value::Number(m)) => {
                let res = n.checked_add(*m).ok_or_else(|| {
                    Error::RuntimeError(loc.clone(), "operation results in an overflow".to_string())
                })?;
                Ok(Value::from(res))
            }
            (Value::Float(n), Value::Float(m)) => {
                let res = n.checked_add(*m).ok_or_else(|| {
                    Error::RuntimeError(loc.clone(), "operation results in an overflow".to_string())
                })?;
                Ok(Value::from(res))
            }
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
            (Value::Number(n), Value::Number(m)) => {
                let res = n.checked_sub(*m).ok_or_else(|| {
                    Error::RuntimeError(
                        loc.clone(),
                        "operation results in an underflow".to_string(),
                    )
                })?;
                Ok(Value::from(res))
            }
            (Value::Float(n), Value::Float(m)) => {
                let res = n.checked_sub(*m).ok_or_else(|| {
                    Error::RuntimeError(
                        loc.clone(),
                        "operation results in an underflow".to_string(),
                    )
                })?;
                Ok(Value::from(res))
            }
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
            (Value::Number(n), Value::Number(m)) => {
                let res = n.checked_div(*m).ok_or_else(|| {
                    Error::RuntimeError(
                        loc.clone(),
                        "operation results in an underflow".to_string(),
                    )
                })?;
                Ok(Value::from(res))
            }
            (Value::Float(n), Value::Float(m)) => {
                let res = n.checked_div(*m).ok_or_else(|| {
                    Error::RuntimeError(
                        loc.clone(),
                        "operation results in an underflow".to_string(),
                    )
                })?;
                Ok(Value::from(res))
            }
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
            (Value::Number(n), Value::Number(m)) => {
                let res = n.checked_mul(*m).ok_or_else(|| {
                    Error::RuntimeError(loc.clone(), "operation results in an overflow".to_string())
                })?;
                Ok(Value::from(res))
            }
            (Value::Float(n), Value::Float(m)) => Ok(Value::Float(
                (n.checked_mul(*m).ok_or_else(|| {
                    Error::RuntimeError(loc.clone(), "operation results in an overflow".to_string())
                })? * self.max_precision)
                    .trunc()
                    / self.max_precision,
            )),
            _ => Err(Error::TypeError(
                loc,
                format!(
                    "invalid operands for binary operation '*': {} and {}",
                    lhs.get_type(),
                    rhs.get_type()
                ),
            )),
        }
    }

    pub fn bit_xor(&self, lhs: Value, rhs: Value, loc: SourceLocation) -> error::Result<Value> {
        match (&lhs, &rhs) {
            (Value::Number(n), Value::Number(m)) => Ok(Value::from(*n ^ *m)),
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
            Value::Float(n) => Ok(Value::from(-n)),
            Value::Number(n) => Ok(Value::from(-n)),
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
            Value::Bool(b) => Ok(Value::Bool(!b)),
            _ => Err(Error::TypeError(
                loc,
                format!(
                    "invalid operands for unary operation '!': {}",
                    lhs.get_type(),
                ),
            )),
        }
    }

    pub fn equals(&self, lhs: Value, rhs: Value, loc: SourceLocation) -> error::Result<Value> {
        match (&lhs, &rhs) {
            (Value::Number(n), Value::Number(u)) => Ok(Value::Bool(n == u)),
            (Value::Float(n), Value::Float(u)) => Ok(Value::Bool(n.approx_eq(*u))),
            (Value::Bool(n), Value::Bool(u)) => Ok(Value::Bool(n == u)),
            (Value::Null, Value::Null) => Ok(Value::Bool(true)),
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
            (Value::Number(n), Value::Number(u)) => Ok(Value::Bool(n != u)),
            (Value::Float(n), Value::Float(u)) => Ok(Value::Bool(n.approx_not_eq(*u))),
            (Value::Bool(n), Value::Bool(u)) => Ok(Value::Bool(n != u)),
            (Value::Null, Value::Null) => Ok(Value::Bool(false)),
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
            (Value::Float(n), Value::Float(u)) => Ok(Value::Bool(n > u)),
            (Value::Number(n), Value::Number(u)) => Ok(Value::Bool(n > u)),
            (Value::Bool(n), Value::Bool(u)) => Ok(Value::Bool(n & !u)),
            (Value::Null, Value::Null) => Ok(Value::Bool(false)),
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
            (Value::Float(n), Value::Float(u)) => Ok(Value::Bool(n >= u)),
            (Value::Number(n), Value::Number(u)) => Ok(Value::Bool(n >= u)),
            (Value::Bool(n), Value::Bool(u)) => Ok(Value::Bool(n >= u)),
            (Value::Null, Value::Null) => Ok(Value::Bool(true)),
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
            (Value::Float(n), Value::Float(u)) => Ok(Value::Bool(n < u)),
            (Value::Number(n), Value::Number(u)) => Ok(Value::Bool(n < u)),
            (Value::Bool(n), Value::Bool(u)) => Ok(Value::Bool(!n & u)),
            (Value::Null, Value::Null) => Ok(Value::Bool(false)),
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
            (Value::Float(n), Value::Float(u)) => Ok(Value::Bool(n <= u)),
            (Value::Number(n), Value::Number(u)) => Ok(Value::Bool(n <= u)),
            (Value::Bool(n), Value::Bool(u)) => Ok(Value::Bool(n <= u)),
            (Value::Null, Value::Null) => Ok(Value::Bool(true)),
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
            (Value::Bool(n), Value::Bool(u)) => Ok(Value::Bool(*n && *u)),
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
            (Value::Bool(n), Value::Bool(u)) => Ok(Value::Bool(*n || *u)),
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

    pub fn index(&self, lhs: Value, index: Value, loc: SourceLocation) -> error::Result<Value> {
        match (&lhs, &index) {
            (Value::Array(array), Value::Number(n)) => {
                if *n >= (array.len() as i128) || n.abs() > (array.len() as i128) {
                    return Err(Error::RuntimeError(
                        loc,
                        format!("out of bounds index {}", n.to_string()),
                    ));
                }
                let n = if *n < 0 {
                    (array.len() as i128) - n.abs()
                } else {
                    *n
                };
                Ok(array[usize::try_from(n)
                    .map_err(|_| Error::TypeError(loc.clone(), "value overflowed".to_string()))?]
                .clone())
            }
            _ => Err(Error::TypeError(
                loc,
                format!(
                    "invalid types for index operator: {} and {}",
                    lhs.get_type(),
                    index.get_type()
                ),
            )),
        }
    }

    pub fn set_input(&mut self, input: Vec<Expression>) {
        self.expr = input;
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
