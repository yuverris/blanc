#![feature(box_syntax, box_patterns)]

//! Blanc math interpreter written in Rust with an easy to use API

/// module related to error handeling
pub mod error;
/// module related to expressiom evalutation and handle most of the logic
pub mod eval;
/// module for lexing characters into usable tokens
pub mod lexer;
/// module for parsing tokens and syntax checking
pub mod parser;
/// module for source location for better and helpful error messages
pub mod source_location;

/// blanc current version
pub static VERSION: &'static str = env!("CARGO_PKG_VERSION");

/// function for evaluating expressions
///
/// # Example
///
///  ```rust
/// let out = blanc::evaluate("-1-2;".to_string());
/// match out {
///      Ok(v) => println!("{}", v),
///      Err(err) => eprintln!("{}", err),
/// }
/// ```
pub fn evaluate(
    input: String,
    file: Option<String>,
    context: Option<crate::eval::Context>,
) -> Result<String, String> {
    use crate::{eval::Eval, lexer::Lexer, parser::Parser};
    let mut lexer = Lexer::new(input, file);
    let tokens = lexer.lex().unwrap();
    let mut iter = tokens.iter().peekable();
    let mut parser = Parser::new(&mut iter);
    let parsed = match parser.parse() {
        Ok(out) => out,
        Err(err) => return Err(err.to_string()),
    };
    let mut eval = match context {
        Some(ctx) => Eval::with_context(parsed, ctx),
        _ => Eval::new(parsed),
    };
    match eval.eval() {
        Ok(result) => Ok(result.to_string()),
        Err(err) => Err(err.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::{
        error::Error,
        eval::{Eval, Value},
        lexer::Lexer,
        parser::Parser,
    };

    fn eval(input: String) -> Result<Value, Error> {
        let mut lexer = Lexer::new(input, None);
        let tokens = lexer.lex().unwrap();
        let mut iter = tokens.iter().peekable();
        let mut parser = Parser::new(&mut iter);
        let parsed = parser.parse()?;
        let mut eval = Eval::new(parsed);
        eval.eval()
    }

    #[test]
    fn basic_arithmetic() -> Result<(), Error> {
        assert_eq!(eval("5 * 2 + 2;".to_string())?, Value::Number(12.0));
        assert_eq!(eval("5 * (2 + 2);".to_string())?, Value::Number(20.0));
        assert_eq!(eval("-2 / 2 + 1 * 4;".to_string())?, Value::Number(3.0));
        assert_eq!(eval("1e-3 * 1e5;".to_string())?, Value::Number(100.0));
        assert_eq!(eval("5^2 - 3;".to_string())?, Value::Number(22.0));
        assert_eq!(eval("3.04 - 2.90;".to_string())?, Value::Number(0.14));
        assert_eq!(eval("1.0 + 2.0;".to_string())?, Value::Number(3.0));
        assert_eq!(eval("5!;".to_string())?, Value::Number(120.0));
        Ok(())
    }

    #[test]
    fn comparison_logical_operators() -> Result<(), Error> {
        assert_eq!(eval("5 == 5;".to_string())?, Value::Bool(true));
        assert_eq!(eval("5 != 5;".to_string())?, Value::Bool(false));
        assert_eq!(eval("nan == nan;".to_string())?, Value::Bool(false));
        assert_eq!(eval("nan != nan;".to_string())?, Value::Bool(true));
        assert_eq!(eval("5 < 5;".to_string())?, Value::Bool(false));
        assert_eq!(eval("5 <= 5;".to_string())?, Value::Bool(true));
        assert_eq!(eval("5 > 5;".to_string())?, Value::Bool(false));
        assert_eq!(eval("5 >= 5;".to_string())?, Value::Bool(true));
        assert_eq!(eval("true && true;".to_string())?, Value::Bool(true));
        assert_eq!(eval("true && false;".to_string())?, Value::Bool(false));
        assert_eq!(eval("false && false;".to_string())?, Value::Bool(false));
        assert_eq!(eval("true || true;".to_string())?, Value::Bool(true));
        assert_eq!(eval("false || true;".to_string())?, Value::Bool(true));
        assert_eq!(eval("false || false;".to_string())?, Value::Bool(false));

        Ok(())
    }

    #[test]
    fn syntax() -> Result<(), Error> {
        assert_eq!(eval("------1 + +--2;".to_string())?, Value::Number(3.0));
        assert_eq!(
            eval("(-(-(-(-(-(-(-(-(-(-(-(-(1)))))))))))));".to_string())?,
            Value::Number(1.0)
        );
        Ok(())
    }

    #[test]
    fn variables() -> Result<(), Error> {
        assert_eq!(eval("x = 5; x * 2;".to_string())?, Value::Number(10.0));
        assert_eq!(
            eval("x = 5; y = x; x = 3; y+x;".to_string())?,
            Value::Number(8.0)
        );
        Ok(())
    }

    #[test]
    fn functions() -> Result<(), Error> {
        assert_eq!(eval("sqrt(25);".to_string())?, Value::Number(5.0));
        assert_eq!(eval("sin(π/2);".to_string())?, Value::Number(1.0));
        assert_eq!(
            eval("sum(x, y, z) -> x + y + z; sum(1,2,3);".to_string())?,
            Value::Number(6.0)
        );
        Ok(())
    }
}
