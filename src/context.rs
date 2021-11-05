use crate::source_location::SourceLocation;
use crate::value::{ConvertionError, FunctionType, Value};
use std::error::Error;
use std::{
    collections::HashMap,
    convert::{TryFrom, TryInto},
    rc::Rc,
};

type BError = crate::error::Error;

type FResult<T> = Result<T, Box<dyn Error>>;

/// Struct for storing functions/constants to be used in an expression
#[derive(Clone)]
pub struct Context {
    pub defs: HashMap<String, Value>,
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
            defs: HashMap::new(),
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
        /*ctx.func(
            "copy",
            &|args: &[Value]| {
                let arg = &args[0];
                match arg {
                    r @ Value::Ref(_) => r.clone().read(),
                    _ => Ok(arg.clone()),
                }
            },
            1,
            false,
        );*/
        ctx.func1("prompt", |inp: String| -> Result<String, Box<dyn Error>> {
            use std::io::Write;
            let mut out = String::new();
            print!("{}", inp);
            std::io::stdout().flush()?;
            std::io::stdin().read_line(&mut out)?;
            out = out.trim_end().into();
            Ok(out)
        });
        ctx.func0("time", || -> Result<f64, Box<dyn Error>> {
            use std::time::SystemTime;
            Ok(SystemTime::now()
                .duration_since(SystemTime::UNIX_EPOCH)
                .map(|d| d.as_secs_f64())?)
        });
        ctx.def(
            "line",
            Value::Func(
                Rc::new(&|_: &[Value], loc: SourceLocation| -> FResult<Value> {
                    Ok(Value::Number(loc.line as i128))
                }),
                None,
            ),
        );
        ctx.def(
            "column",
            Value::Func(
                Rc::new(&|_: &[Value], loc: SourceLocation| -> FResult<Value> {
                    Ok(Value::Number(loc.column as i128))
                }),
                None,
            ),
        );
        ctx.def(
            "file",
            Value::Func(
                Rc::new(&|_: &[Value], loc: SourceLocation| -> FResult<Value> {
                    Ok(loc.file.map(|f| Value::String(f)).unwrap_or(Value::Null))
                }),
                None,
            ),
        );
        ctx
    }

    /// Defines a new value and assign it to an indetifier
    ///
    /// # Example
    ///
    /// ```rust
    /// use blanc::{context::Context, value::Value};
    /// let mut ctx = Context::new();
    /// ctx.def("foo", 5.0, false);
    /// ```
    pub fn def<S>(&mut self, name: S, value: Value)
    where
        S: ToString,
    {
        self.defs.insert(name.to_string(), value);
    }

    /// Fetches a definition
    ///
    /// # Example
    ///
    /// ```rust
    /// use blanc::{context::Context, value::Value};
    /// let mut ctx = Context::new();
    /// let name = String::from("foo");
    /// ctx.var(name.clone(), 5.0, false));
    /// assert_eq!(ctx.get_var(name.clone()), Some(&Value::from(5.0)));
    /// ```
    pub fn get_def(&self, name: String) -> Option<&Value> {
        self.defs.get(&name)
    }

    pub fn get_mut_def(&mut self, name: String) -> Option<&mut Value> {
        self.defs.get_mut(&name)
    }

    /// Fetches a definition and cast it as a function
    ///
    /// # Example
    ///
    /// ```rust
    /// use blanc::{context::Context, value::Value};
    /// let ctx = Context::with_builtins();
    /// let function = ctx.get_function("print".to_string()).unwrap();
    /// assert_eq!(function(&[Value::Float(25.0)]), Ok(Value::from(5.0)));
    /// ```
    pub fn get_func(&self, name: String) -> Option<&FunctionType> {
        match self.defs.get(&name) {
            Some(Value::Func(f, _)) => Some(f),
            _ => None,
        }
    }

    /// Returns a new Context that contains definitions that aren't present in both context, useful
    /// for getting a single block's definitions excluding parent's definition
    /*pub fn difference(&self, other: &Context) -> Context {
        Context { defs: self.defs }
    }*/

    /// Adds a new function
    ///
    /// # Exampke
    ///
    /// ```rust
    /// use blanc::{context::Context, value::Value, source_location::SourceLocation};
    /// fn function(_: &[Value], _: SourceLocation) -> Result<Value, String> {
    ///      Ok(Value::Float(5.0))
    /// }
    /// fn main() {
    ///      let mut ctx = Context::new();
    ///      ctx.func("get_five".to_string(), function, 0, false);
    /// }
    /// ```
    pub fn func<S>(
        &mut self,
        name: S,
        func: &'static dyn Fn(&[Value]) -> FResult<Value>,
        arg_count: usize,
        inf_args: bool,
    ) where
        S: ToString,
    {
        let fnc = move |args: &[Value], loc: SourceLocation| {
            if args.len() != arg_count && !inf_args {
                Err(BError::Error(loc, format!("umatched arguments count function requires {} arguments, you supplied {} arguments",
                            arg_count, args.len())).into())
            } else {
                func(args).map_err(|e| e)
            }
        };
        self.defs
            .insert(name.to_string(), Value::Func(Rc::new(fnc), None));
    }

    ///
    /// Adds a new function without arguments
    ///
    /// # Example
    ///
    /// ```rust
    /// use blanc::{context::Context, value::Value, source_location::SourceLocation};
    /// // any argument type/return type is allowed as long as it's convertible to eval::Value
    /// fn function(_: SourceLocation) -> Result<&'static str, Error> {
    ///     Ok("hello")
    /// }
    /// fn main() {
    ///      let mut ctx = Context::new();
    ///      ctx.func0("say_hello".to_string(), function);
    /// }
    /// ```
    pub fn func0<S, F, U>(&mut self, name: S, func: F)
    where
        S: ToString,
        U: TryInto<Value, Error = ConvertionError>,
        F: Fn() -> FResult<U> + 'static,
    {
        let fnc = move |args: &[Value], loc: SourceLocation| -> FResult<Value> {
            if !args.is_empty() {
                Err(BError::Error(loc, format!("umatched arguments count function doesn't require any arguments, you supplied {} arguments",
                            args.len())).into())
            } else {
                func()?.try_into().map_err(|e| e.into())
            }
        };
        self.defs
            .insert(name.to_string(), Value::Func(Rc::new(fnc), None));
    }

    /// Adds a new function that accepts a single argument
    ///
    /// # Example
    ///
    /// ```rust
    /// use blanc::{context::Context, value::Value, source_location::SourceLocation};
    /// // any argument type/return type is allowed as long as it's convertible to eval::Value
    /// fn function(arg: f64) -> f64 {
    ///      arg + 2.0
    /// }
    /// fn main() {
    ///      use blanc::{context::Context, value::Value};
    ///      let mut ctx = Context::new();
    ///      ctx.func1("add_two".to_string(), function);
    /// }
    /// ```
    pub fn func1<S, F, T, U>(&mut self, name: S, func: F)
    where
        S: ToString,
        T: TryFrom<Value, Error = ConvertionError>,
        U: TryInto<Value, Error = ConvertionError>,
        F: Fn(T) -> FResult<U> + 'static,
    {
        let fnc = move |args: &[Value], loc: SourceLocation| -> FResult<Value> {
            if args.len() != 1 {
                Err(BError::Error(loc, format!("umatched arguments count function requires a single argument, you supplied {} arguments",
                            args.len())).into())
            } else {
                let arg: T = T::try_from(args[0].clone())?;
                func(arg)?.try_into().map_err(|e| e.into())
            }
        };
        self.defs
            .insert(name.to_string(), Value::Func(Rc::new(fnc), None));
    }

    /// Adds a new function that accepts two arguments
    ///
    /// # Example
    ///
    /// ```rust
    /// use blanc::{context::Context, value::Value, source_location::SourceLocation};
    /// // any argument type/return type is allowed as long as it's convertible to eval::Value
    /// fn function(a: i128, b: i128) -> i128 {
    ///      a + b
    /// }
    /// fn main() {
    ///      use blanc::{context::Context, value::Value};
    ///      let mut ctx = Context::new();
    ///      ctx.func2("sum2", function);
    /// }
    /// ```
    pub fn func2<S, F, T, U, J>(&mut self, name: S, func: F)
    where
        S: ToString,
        T: TryFrom<Value, Error = ConvertionError>,
        U: TryFrom<Value, Error = ConvertionError>,
        J: TryInto<Value, Error = ConvertionError>,
        F: Fn(T, U) -> FResult<J> + 'static,
    {
        let fnc = move |args: &[Value], loc: SourceLocation| -> FResult<Value> {
            if args.len() != 2 {
                Err(BError::Error(loc, format!("umatched arguments count function requires 2 arguments, you supplied {} arguments",
                            args.len())).into())
            } else {
                let arg1: T = T::try_from(args[0].clone())?;
                let arg2: U = U::try_from(args[1].clone())?;
                func(arg1, arg2)?.try_into().map_err(|e| e.into())
            }
        };
        self.defs
            .insert(name.to_string(), Value::Func(Rc::new(fnc), None));
    }

    /// Adds a new function that accepts three arguments
    ///
    /// # Example
    ///
    /// ```rust
    /// use blanc::{context::Context, value::Value, source_location::SourceLocation};
    /// // any argument type/return type is allowed as long as it's convertible to eval::Value
    /// fn function(a: i128, b: i128, c: i128) -> i128 {
    ///      a + b + c
    /// }
    /// fn main() {
    ///      use blanc::{context::Context, value::Value};
    ///      let mut ctx = Context::new();
    ///      ctx.func3("sum3", function);
    /// }
    /// ```
    pub fn func3<S, F, T, U, J, V>(&mut self, name: S, func: F)
    where
        S: ToString,
        T: TryFrom<Value, Error = ConvertionError>,
        U: TryFrom<Value, Error = ConvertionError>,
        J: TryFrom<Value, Error = ConvertionError>,
        V: TryInto<Value, Error = ConvertionError>,
        F: Fn(T, U, J) -> FResult<V> + 'static,
    {
        let fnc = move |args: &[Value], loc: SourceLocation| -> FResult<Value> {
            if args.len() != 3 {
                Err(BError::Error(loc, format!("umatched arguments count function requires 3 arguments, you supplied {} arguments",
                            args.len())).into())
            } else {
                let arg1: T = T::try_from(args[0].clone())?;
                let arg2: U = U::try_from(args[1].clone())?;
                let arg3: J = J::try_from(args[2].clone())?;
                func(arg1, arg2, arg3)?.try_into().map_err(|e| e.into())
            }
        };
        self.defs
            .insert(name.to_string(), Value::Func(Rc::new(fnc), None));
    }

    /// Adds a new function that accepts four arguments
    ///
    /// # Example
    ///
    /// ```rust
    /// use blanc::{context::Context, value::Value, source_location::SourceLocation};
    /// // any argument type/return type is allowed as long as it's convertible to eval::Value
    /// fn function(a: i128, b: i128, c: i128, d: i128, _: SourceLocation) -> Result<i128, Error> {
    ///      Ok(a + b + c + d)
    /// }
    /// fn main() {
    ///      use blanc::{context::Context, value::Value};
    ///      let mut ctx = Context::new();
    ///      ctx.func4("sum4", function);
    /// }
    /// ```
    pub fn func4<S, F, T, U, J, V, Z>(&mut self, name: S, func: F)
    where
        S: ToString,
        T: TryFrom<Value, Error = ConvertionError>,
        U: TryFrom<Value, Error = ConvertionError>,
        J: TryFrom<Value, Error = ConvertionError>,
        V: TryFrom<Value, Error = ConvertionError>,
        Z: TryInto<Value, Error = ConvertionError>,
        F: Fn(T, U, J, V) -> FResult<Z> + 'static,
    {
        let fnc = move |args: &[Value], loc: SourceLocation| -> FResult<Value> {
            if args.len() != 4 {
                Err(BError::Error(loc, format!("umatched arguments count function requires 4 arguments, you supplied {} arguments",
                            args.len())).into())
            } else {
                let arg1: T = T::try_from(args[0].clone())?;
                let arg2: U = U::try_from(args[1].clone())?;
                let arg3: J = J::try_from(args[2].clone())?;
                let arg4: V = V::try_from(args[3].clone())?;
                func(arg1, arg2, arg3, arg4)?
                    .try_into()
                    .map_err(|e| e.into())
            }
        };
        self.defs
            .insert(name.to_string(), Value::Func(Rc::new(fnc), None));
    }

    /// Adds a new function that accepts five arguments
    ///
    /// # Example
    ///
    /// ```rust
    /// use blanc::{context::Context, value::Value};
    /// // any argument type/return type is allowed as long as it's convertible to eval::Value
    /// fn function(a: i128, b: i128, c: i128, d: i128, j: i128) -> Result<i128, Box<dyn Error>> {
    ///      Ok(a + b + c + d + j)
    /// }
    /// fn main() {
    ///      use blanc::{context::Context, value::Value};
    ///      let mut ctx = Context::new();
    ///      ctx.func5("sum5", function);
    /// }
    /// ```
    pub fn func5<S, F, T, U, J, V, Z, Y>(&mut self, name: S, func: F)
    where
        S: ToString,
        T: TryFrom<Value, Error = ConvertionError>,
        U: TryFrom<Value, Error = ConvertionError>,
        J: TryFrom<Value, Error = ConvertionError>,
        V: TryFrom<Value, Error = ConvertionError>,
        Z: TryFrom<Value, Error = ConvertionError>,
        Y: TryInto<Value, Error = ConvertionError>,
        F: Fn(T, U, J, V, Z) -> FResult<Y> + 'static,
    {
        let fnc = move |args: &[Value], loc: SourceLocation| -> FResult<Value> {
            if args.len() != 4 {
                Err(BError::Error(loc, format!("umatched arguments count function requires 5 arguments, you supplied {} arguments",
                            args.len())).into())
            } else {
                let arg1: T = T::try_from(args[0].clone())?;
                let arg2: U = U::try_from(args[1].clone())?;
                let arg3: J = J::try_from(args[2].clone())?;
                let arg4: V = V::try_from(args[3].clone())?;
                let arg5: Z = Z::try_from(args[4].clone())?;
                func(arg1, arg2, arg3, arg4, arg5)?
                    .try_into()
                    .map_err(|e| e.into())
            }
        };
        self.defs
            .insert(name.to_string(), Value::Func(Rc::new(fnc), None));
    }
}

unsafe impl Sync for Context {}
unsafe impl Send for Context {}
