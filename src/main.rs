use blanc::{error::Error, eval::Eval, eval::Value, lexer::Lexer, parser::Parser};
use std::f64::consts;

fn eval(input: String) -> Result<Value, Error> {
    let mut lexer = Lexer::new(input, None);
    let tokens = lexer.lex().unwrap();
    let mut iter = tokens.iter().peekable();
    let mut parser = Parser::new(&mut iter);
    let parsed = parser.parse()?;
    let mut eval = Eval::new(parsed);
    eval.eval()
}

fn main() {
    match eval("-sqrt(25)+5".into()) {
        Ok(v) => println!("{}", v),
        Err(err) => eprintln!("{}", err),
    };
}
