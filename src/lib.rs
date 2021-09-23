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
/// module for value representation
pub mod value;

pub mod context;

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
    context: Option<crate::context::Context>,
) -> crate::utils::RResult<String, String, ()> {
    use crate::{error::format_err, eval::Eval, lexer::Lexer, parser::Parser, utils::RResult::*};
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
        Result::Err(err) => return Err(format_err(err, input)),
    };
    let mut eval = match context {
        Some(ctx) => Eval::with_context(parsed, ctx),
        _ => Eval::new(parsed),
    };
    // TODO: new way of handling source location
    match eval.eval() {
        Ok(result) => Ok(result.to_string()),
        Err(err) => Err(format_err(err, input)),
        Return(_) => unreachable!(),
    }
}

#[cfg(test)]
mod tests {
    #[bench]
    fn parse_n_eval() {
        super::evaluate("5+5;", None, None);
    }
}
