use crate::value::{FunctionType, Value};
use std::{collections::HashMap, convert::TryFrom, rc::Rc};

/// Struct for storing functions/constants to be used in an expression
#[derive(Clone)]
pub struct Context {
    variables: HashMap<String, Value>,
    functions: HashMap<String, FunctionType>,
    user_functions: HashMap<String, Value>,
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
            user_functions: HashMap::new(),
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
        ctx.func(
            "copy",
            &|args: &[Value]| {
                let arg = &args[0];
                match arg {
                    r @ Value::Ref(_) => r.clone().read().map_err(ToString::to_string),
                    _ => Ok(arg.clone()),
                }
            },
            1,
            false,
        );
        ctx.func1("prompt", |inp: String| -> String {
            use std::io::Write;
            let mut out = String::new();
            print!("{}", inp);
            std::io::stdout().flush().unwrap();
            std::io::stdin().read_line(&mut out).unwrap();
            out = out.trim_end().into();
            out
        });
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
        self.variables.insert(name.to_string(), value.into());
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
    /// assert_eq!(ctx.get_var(name.clone()), Some(&Value::from(5.0)));
    /// ```
    pub fn get_var(&self, name: String) -> Option<&Value> {
        self.variables.get(&name)
    }

    pub fn get_mut_var(&mut self, name: String) -> Option<&mut Value> {
        self.variables.get_mut(&name)
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

    pub fn get_user_function(&self, name: String) -> Option<&Value> {
        self.user_functions.get(&name)
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

    pub fn user_function(&mut self, name: String, fnc: Value) {
        self.user_functions.insert(name, fnc);
    }

    ///
    /// Adds a new function without arguments
    ///
    /// # Example
    ///
    /// ```rust
    /// // any argument type/return type is allowed as long as it's convertible to eval::Value
    /// fn function() -> &str {
    ///     "hello"
    /// }
    /// fn main() {
    ///      use blanc::eval::{Context, Value};
    ///      let mut ctx = Context::new();
    ///      ctx.func0("hello".to_string(), function);
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
                Ok(func(arg).into())
                //.map_err(|_| "failed to convert function return type".to_string())
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

unsafe impl Sync for Context {}
unsafe impl Send for Context {}
