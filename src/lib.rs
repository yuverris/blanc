#![feature(
    box_syntax,
    box_patterns,
    iter_intersperse,
    once_cell,
    label_break_value
)]

//! Blanc math interpreter written in Rust with an easy to use API

/// module for defining built-in member constants/functions for built-in types
pub(crate) mod builtins;
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
/// module for utilties
pub mod utils;

/// blanc current version
pub static VERSION: &str = env!("CARGO_PKG_VERSION");

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
) -> crate::utils::RResult<String, String, ()> {
    use crate::{
        error::{format_err, Error},
        eval::Eval,
        lexer::Lexer,
        parser::Parser,
        utils::RResult::*,
    };
    let mut lexer = Lexer::new(input.clone(), file);
    let tokens = lexer.lex().map_err(|err| err.to_string());
    let tokens = match tokens {
        Result::Ok(tok) => tok,
        Result::Err(err) => return Err(err),
    };
    let iter = tokens.iter().peekable();
    let mut parser = Parser::new(iter);
    let parsed = match parser.parse() {
        Result::Ok(out) => out,
        Result::Err(err) => match err {
            Error::SyntaxError(ref loc, ..) => {
                return Err(format_err(err.clone(), input, loc.clone()))
            }
            _ => return Err(err.to_string()),
        },
    };
    let mut eval = match context {
        Some(ctx) => Eval::with_context(parsed, ctx),
        _ => Eval::new(parsed),
    };
    match eval.eval() {
        Ok(result) => Ok(result.to_string()),
        Err(err) => match err {
            Error::TypeError(ref loc, ..) => {
                return Err(format_err(err.clone(), input, loc.clone()))
            }
            Error::RuntimeError(ref loc, ..) => {
                return Err(format_err(err.clone(), input, loc.clone()))
            }
            _ => return Err(err.to_string()),
        },
        Return(_) => unreachable!(),
    }
}
