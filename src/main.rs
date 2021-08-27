use blanc::{Lexer, Parser};
fn main() {
    let mut lexer = Lexer::new("!null == true".to_string());
    match lexer.lex() {
        Ok(tokens) => {
            println!("{:?}", tokens);
            let mut iter = tokens.iter().peekable();
            let mut parser = Parser::new(&mut iter);
            let expr = parser.parse();
            match expr {
                Ok(expr) => match expr.eval() {
                    Ok(out) => println!("{:?}\n{}", expr, out.to_string()),
                    Err(err) => eprintln!("error: {}", err),
                },
                Err(err) => eprintln!("error: {}", err),
            }
        }
        Err(err) => eprintln!("error: {}", err),
    }
}
