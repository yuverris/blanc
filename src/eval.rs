use crate::{
    context::Context,
    error::Error,
    lexer::Operator,
    parser::{ArgHandler, Expression},
    source_location::SourceLocation,
    try_err, try_return,
    utils::RResult,
    value::Value,
};

use std::{convert::TryFrom, string::ToString};
type ResultType = RResult<Value, Error, Value>;

/// macro for converting std::result::Result to RResult
/*macro_rules! unwrap_result {
    ($expr:expr) => {
        match $expr {
            Result::Ok(v) => v,
            Result::Err(err) => return ResultType::Err(err.into()),
        }
    };
}

macro_rules! unwrap_result_read {
    ($expr1:expr, $expr2:expr, $loc:ident) => {
        match ($expr1.read(), $expr2.read()) {
            (Result::Ok(u), Result::Ok(v)) => (u, v),
            (Result::Err(err), _) => {
                return ResultType::Err(Error::RuntimeError($loc.clone(), err.to_string()))
            }
            (_, Result::Err(err)) => {
                return ResultType::Err(Error::RuntimeError($loc.clone(), err.to_string()))
            }
        }
    };
    ($expr:expr, $loc:ident) => {
        match $expr.read() {
            Result::Ok(u) => u,
            Result::Err(err) => {
                return ResultType::Err(Error::RuntimeError($loc.clone(), err.to_string()))
            }
        }
    };
}*/

/// main trait for defining callable objects
pub trait Callable {
    fn call(&self, args: Vec<ArgHandler>, loc: SourceLocation, eval: &mut Eval) -> ResultType;
}

impl Callable for Value {
    fn call(&self, args: Vec<ArgHandler>, loc: SourceLocation, eval: &mut Eval) -> ResultType {
        match self {
            Value::Func(fnc, _self) => {
                let mut _args = Vec::<Value>::new();
                for arg in args {
                    let expr = try_err!(eval.eval_expr(&arg.value.unwrap()));
                    _args.push(expr);
                }
                if _self.is_some() {
                    _args.insert(0, *_self.clone().unwrap());
                }
                let out = fnc(&_args[..], loc.clone());
                match out {
                    Ok(out) => ResultType::Ok(out),
                    Err(err) => match err {
                        berr if err.is::<Error>() => {
                            let _err = berr.downcast::<crate::error::Error>().unwrap();
                            ResultType::Err(*_err)
                        }
                        _ => ResultType::Err(Error::RuntimeError(loc, err.to_string())),
                    },
                }
            }

            Value::UserFunc { params, body } => {
                if params.len() != args.len() {
                    return ResultType::Err(Error::RuntimeError(
                        loc,
                        format!(
                            "function requires {} arguments, you supplied {}",
                            params.len(),
                            args.len()
                        ),
                    ));
                }

                for (param, arg) in params.iter().zip(args.iter()) {
                    if let ArgHandler {
                        name: Some(ident), ..
                    } = arg
                    {
                        if param.name.as_ref().unwrap() != ident {
                            return ResultType::Err(Error::RuntimeError(
                                loc,
                                format!("unexpected keyword argument '{}'", ident),
                            ));
                        }
                    }
                }
                // store old state of the context and bind parameters names to the current context
                // then reset the context to its old state after function call
                let previous = eval.get_context_mut().clone();
                let iter = args.iter();
                let mut index = 0usize;
                for arg in iter {
                    match arg {
                        ArgHandler {
                            name: Some(ident),
                            value: Some(expr),
                        } => {
                            let expr = try_err!(eval.eval_expr(&expr));
                            eval.get_context_mut().def(ident, expr);
                            if params[index].name.as_ref().unwrap() == ident {
                                index += 1;
                            }
                        }
                        ArgHandler {
                            name: None,
                            value: Some(expr),
                        } => {
                            let expr = try_err!(eval.eval_expr(&expr));
                            eval.get_context_mut()
                                .def(params[index].name.as_ref().unwrap().clone(), expr);
                            index += 1;
                        }
                        _ => unreachable!(),
                    };
                }
                let out = eval.eval_expr(body);
                eval.set_context(previous);
                out
            }

            _ => ResultType::Err(Error::TypeError(
                loc,
                format!("{} isn't a callable object", self.get_type()),
            )),
        }
    }
}

/// struct for evaluating expressions
pub struct Eval {
    /// list of expressions to evaluate
    expr: Vec<Expression>,
    /// context to lookup for variables/functions
    context: Context,
}

impl Eval {
    /// constructs a new Eval from the given vector of expressions along side with builtin context
    pub fn new(expr: Vec<Expression>) -> Self {
        Self {
            expr,
            context: Context::with_builtins(),
        }
    }

    /// constructs a new empty Eval with builtin context
    pub fn new_empty() -> Self {
        Self {
            expr: Vec::new(),
            context: Context::with_builtins(),
        }
    }

    /// constructs a new Eval from the given vector of expressions along side with custom context
    pub fn with_context(expr: Vec<Expression>, ctx: Context) -> Self {
        Self { expr, context: ctx }
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
    pub fn eval_expr(&mut self, expr: &Expression) -> ResultType {
        use RResult::*;
        match expr {
            Expression::Float(_, x) => Ok(Value::Float(*x)),
            Expression::String(_, s) => Ok(Value::String(s.clone())),
            Expression::Char(_, c) => Ok(Value::Char(*c)),
            Expression::Array(_, exprs) => {
                let mut inner: Vec<Value> = Vec::new();
                for expr in exprs {
                    let temp = try_err!(self.eval_expr(expr));
                    inner.push(temp);
                }
                ResultType::Ok(Value::Array(inner))
            }
            Expression::Number(_, x) => Ok(Value::Number(*x)),
            Expression::Bool(_, b) => Ok(Value::Bool(*b)),
            Expression::Null(_) => Ok(Value::Null),
            Expression::Ident(loc, i) => {
                if let Some(v) = self.context.get_def(i.clone()) {
                    Ok(v.clone())
                } else {
                    Err(Error::RuntimeError(
                        loc.clone(),
                        format!("undefined value '{}'", i),
                    ))
                }
            }
            Expression::FuncCall(loc, box expr, args) => {
                let target = try_err!(self.eval_expr(expr));
                target.call(args.clone(), loc.clone(), self)
            }
            Expression::FuncDef(_, name, args, box body) => {
                let function = Value::UserFunc {
                    params: args.clone(),
                    body: body.clone(),
                };
                if let Some(name) = name {
                    self.context.def(name.clone(), function);
                    Ok(Value::Null)
                } else {
                    Ok(function)
                }
            }
            Expression::Unary(loc, Operator::Negative, box expr) => {
                let temp = try_err!(self.eval_expr(expr));
                match -temp {
                    Result::Ok(v) => Ok(v),
                    Result::Err(err) => Err(Error::Error(loc.clone(), err)),
                }
            }

            Expression::Unary(_, Operator::Positive, box expr) => self.eval_expr(expr),

            Expression::Unary(loc, Operator::Not, box expr) => {
                let temp = try_err!(self.eval_expr(expr));
                match !temp {
                    Result::Ok(v) => Ok(v),
                    Result::Err(err) => Err(Error::Error(loc.clone(), err)),
                }
            }

            Expression::Binary(loc, Operator::Plus, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = try_err!(self.eval_expr(rhs));
                match temp_lhs + temp_rhs {
                    Result::Ok(v) => Ok(v),
                    Result::Err(err) => Err(Error::Error(loc.clone(), err)),
                }
            }

            Expression::Binary(loc, Operator::Minus, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = try_err!(self.eval_expr(rhs));
                match temp_lhs - temp_rhs {
                    Result::Ok(v) => Ok(v),
                    Result::Err(err) => Err(Error::Error(loc.clone(), err)),
                }
            }

            Expression::Binary(loc, Operator::Star, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = try_err!(self.eval_expr(rhs));
                match temp_lhs * temp_rhs {
                    Result::Ok(v) => Ok(v),
                    Result::Err(err) => Err(Error::Error(loc.clone(), err)),
                }
            }

            Expression::Binary(loc, Operator::Slash, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = try_err!(self.eval_expr(rhs));
                match temp_lhs / temp_rhs {
                    Result::Ok(v) => Ok(v),
                    Result::Err(err) => Err(Error::Error(loc.clone(), err)),
                }
            }

            Expression::Binary(loc, Operator::BitXor, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = try_err!(self.eval_expr(rhs));
                match temp_lhs ^ temp_rhs {
                    Result::Ok(v) => Ok(v),
                    Result::Err(err) => Err(Error::Error(loc.clone(), err)),
                }
            }

            Expression::Binary(loc, Operator::BitOr, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = try_err!(self.eval_expr(rhs));
                match temp_lhs | temp_rhs {
                    Result::Ok(v) => Ok(v),
                    Result::Err(err) => Err(Error::Error(loc.clone(), err)),
                }
            }

            Expression::Binary(loc, Operator::BitAnd, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = try_err!(self.eval_expr(rhs));
                match temp_lhs & temp_rhs {
                    Result::Ok(v) => Ok(v),
                    Result::Err(err) => Err(Error::Error(loc.clone(), err)),
                }
            }

            Expression::Binary(loc, Operator::RShift, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = try_err!(self.eval_expr(rhs));
                match temp_lhs >> temp_rhs {
                    Result::Ok(v) => Ok(v),
                    Result::Err(err) => Err(Error::Error(loc.clone(), err)),
                }
            }

            Expression::Binary(loc, Operator::LShift, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = try_err!(self.eval_expr(rhs));
                match temp_lhs << temp_rhs {
                    Result::Ok(v) => Ok(v),
                    Result::Err(err) => Err(Error::Error(loc.clone(), err)),
                }
            }

            Expression::Binary(loc, Operator::Remainder, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = try_err!(self.eval_expr(rhs));
                match temp_lhs % temp_rhs {
                    Result::Ok(v) => Ok(v),
                    Result::Err(err) => Err(Error::Error(loc.clone(), err)),
                }
            }

            Expression::Binary(loc, Operator::And, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_lhs = match temp_lhs {
                    Value::Bool(b) => b,
                    _ => {
                        return Err(Error::TypeError(
                            loc.clone(),
                            "expected bool in logical comparison".to_string(),
                        ))
                    }
                };
                let temp_rhs = try_err!(self.eval_expr(rhs));
                let temp_rhs = match temp_rhs {
                    Value::Bool(b) => b,
                    _ => {
                        return Err(Error::TypeError(
                            loc.clone(),
                            "expected bool in logical comparison".to_string(),
                        ))
                    }
                };
                Ok(Value::Bool(temp_lhs && temp_rhs))
            }

            Expression::Binary(loc, Operator::Or, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_lhs = match temp_lhs {
                    Value::Bool(b) => b,
                    _ => {
                        return Err(Error::TypeError(
                            loc.clone(),
                            "expected bool in logical comparison".to_string(),
                        ))
                    }
                };
                let temp_rhs = try_err!(self.eval_expr(rhs));
                let temp_rhs = match temp_rhs {
                    Value::Bool(b) => b,
                    _ => {
                        return Err(Error::TypeError(
                            loc.clone(),
                            "expected bool in logical comparison".to_string(),
                        ))
                    }
                };
                Ok(Value::Bool(temp_lhs || temp_rhs))
            }

            Expression::Binary(_, Operator::Equal, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = try_err!(self.eval_expr(rhs));
                Ok(Value::Bool(temp_lhs == temp_rhs))
            }

            Expression::Binary(_, Operator::NotEqual, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = try_err!(self.eval_expr(rhs));
                Ok(Value::Bool(temp_lhs != temp_rhs))
            }

            Expression::Binary(_, Operator::Greater, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = try_err!(self.eval_expr(rhs));
                Ok(Value::Bool(temp_lhs > temp_rhs))
            }

            Expression::Binary(_, Operator::GreaterOrEqual, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = try_err!(self.eval_expr(rhs));
                Ok(Value::Bool(temp_lhs >= temp_rhs))
            }

            Expression::Binary(_, Operator::Less, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = try_err!(self.eval_expr(rhs));
                Ok(Value::Bool(temp_lhs < temp_rhs))
            }

            Expression::Binary(_, Operator::LessOrEqual, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = try_err!(self.eval_expr(rhs));
                Ok(Value::Bool(temp_lhs <= temp_rhs))
            }

            // member access operator: target.value
            // TODO: figure out a way to implement this
            Expression::Binary(loc, Operator::Dot, box lhs, box rhs) => {
                let temp_lhs = try_err!(self.eval_expr(lhs));
                let temp_rhs = match rhs {
                    Expression::Ident(_, name) => name.clone(),
                    _ => {
                        return Err(Error::SyntaxError(
                            loc.clone(),
                            "invalid type for '.' operator".to_string(),
                        ))
                    }
                };
                self.member_access(temp_lhs, temp_rhs, loc.clone())
            }
            Expression::Binary(loc, Operator::Assign, box lhs, box rhs) => {
                let expr = try_err!(self.eval_expr(rhs));
                let target = try_err!(self.eval_expr(lhs));
                let mut var = match target {
                    r @ Value::Ref(_) => r,
                    _ => {
                        return Err(Error::RuntimeError(
                            loc.clone(),
                            "invalid left type of assignement expression".to_string(),
                        ))
                    }
                };
                match var.set_ref(expr) {
                    Result::Ok(_) => (),
                    Result::Err(err) => {
                        return Err(Error::RuntimeError(loc.clone(), err.to_string()))
                    }
                };
                Ok(Value::Null)
            }

            Expression::Subscript(loc, box lhs, box inner) => {
                let lhs = try_err!(self.eval_expr(lhs));
                let inner = try_err!(self.eval_expr(inner));
                self.index(lhs, inner, loc.clone())
            }

            Expression::Variable(_, name, value, _) => {
                let value = match value {
                    Some(expr) => try_err!(self.eval_expr(expr)),
                    None => Value::Null,
                };
                self.context.def(name, value);
                Ok(Value::Null)
            }

            // TODO: destroy all of the values initialized in the block
            // FIXME: local references
            Expression::Block(_, stmts) => {
                let previous = self.context.clone();
                for expr in stmts {
                    match expr {
                        Expression::Return(_, box expr) => {
                            let item = try_return!(self.eval_expr(expr));
                            self.context = previous;
                            return Return(item);
                        }
                        _ => try_return!(self.eval_expr(expr)),
                    };
                }
                self.context = previous;
                Ok(Value::Null)
            }

            Expression::IfStmt(loc, box condition, box body, else_clause) => {
                let cond = try_err!(self.eval_expr(condition));
                match cond {
                    Value::Bool(true) => match body {
                        Expression::Block(_, stmts) => {
                            for expr in stmts {
                                match expr {
                                    Expression::Return(_, box expr) => {
                                        let item = try_return!(self.eval_expr(expr));
                                        return Return(item);
                                    }
                                    _ => try_return!(self.eval_expr(expr)),
                                };
                            }
                            Ok(Value::Null)
                        }
                        _ => unreachable!(), // parser does the job
                    },
                    Value::Bool(false) => match else_clause {
                        Some(box body) => match body {
                            Expression::Block(_, stmts) => {
                                for expr in stmts {
                                    match expr {
                                        Expression::Return(_, box expr) => {
                                            let item = try_return!(self.eval_expr(expr));
                                            return Return(item);
                                        }
                                        _ => try_return!(self.eval_expr(expr)),
                                    };
                                }
                                Ok(Value::Null)
                            }
                            _ => unreachable!(), // parser does the job
                        },
                        None => Ok(Value::Null),
                    },
                    _ => Err(Error::RuntimeError(
                        loc.clone(),
                        "expected boolean in if condition".to_string(),
                    )),
                }
            }

            Expression::WhileStmt(loc, condition, box body) => {
                let body_exprs = match body {
                    Expression::Block(_, stmts) => stmts,
                    _ => {
                        return Err(Error::SyntaxError(
                            loc.clone(),
                            "expected block statement after `while`".to_string(),
                        ))
                    }
                };
                match condition {
                    Some(box expr) => {
                        'l: loop {
                            let cond = try_err!(self.eval_expr(expr));
                            let cond = match cond {
                                Value::Bool(v) => v,
                                _ => {
                                    return Err(Error::RuntimeError(
                                        loc.clone(),
                                        format!(
                                            "while statement condtion must return a bool found {}",
                                            cond.get_type()
                                        ),
                                    ))
                                }
                            };
                            if !cond {
                                break;
                            }
                            for expr in body_exprs {
                                match expr {
                                    Expression::Return(_, box expr) => {
                                        let item = try_return!(self.eval_expr(expr));
                                        return Return(item);
                                    }
                                    Expression::Break(_) => {
                                        break 'l;
                                    }
                                    Expression::Continue(_) => continue,
                                    _ => try_return!(self.eval_expr(expr)),
                                };
                            }
                        }
                        Ok(Value::Void)
                    }
                    None => loop {
                        try_return!(self.eval_expr(body));
                    },
                }
            }

            _ => panic!("invalid expression"), // let it panic for now
        }
    }

    pub fn index(&self, lhs: Value, index: Value, loc: SourceLocation) -> ResultType {
        use RResult::*;
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
                let index = usize::try_from(n)
                    .map_err(|_| Error::TypeError(loc.clone(), "value overflowed".to_string()));
                match index {
                    std::result::Result::Ok(v) => Ok(Value::Ref(&mut array[v] as *mut _)),
                    std::result::Result::Err(err) => Err(err),
                }
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

    // TODO: support ufcs, use a map to map Values to their context instead of match
    pub fn member_access(&mut self, lhs: Value, rhs: String, loc: SourceLocation) -> ResultType {
        use RResult::*;
        match lhs.get_member_field_or_context(rhs.clone(), &self.context) {
            Some(s) => match s {
                Value::Func(f, None) => Ok(Value::Func(f.clone(), Some(Box::new(lhs.clone())))),
                _ => Ok(s.clone()),
            },
            None => Err(Error::Error(
                loc,
                format!(
                    "no field/method named '{}' exists in '{}'",
                    rhs,
                    lhs.get_type()
                ),
            )),
        }
    }

    pub fn set_input(&mut self, input: Vec<Expression>) {
        self.expr = input;
    }

    pub fn eval(&mut self) -> ResultType {
        use RResult::*;
        let mut iter = self.expr.clone().into_iter();
        let next = match iter.next() {
            Some(x) => x,
            None => return Ok(Value::Null),
        };
        let mut out: Value = try_err!(self.eval_expr(&next));
        for expr in iter {
            out = try_err!(self.eval_expr(&expr));
        }
        Ok(out)
    }
}
