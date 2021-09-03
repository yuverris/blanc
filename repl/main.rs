use blanc::{eval::Eval, lexer::Lexer, parser::Parser};
fn main() -> std::io::Result<()> {
    println!("blanc math interpreter repl session.\nblanc version: {}\ntype 'quit' or Ctrl-C to terminate this session\n",
        blanc::VERSION);
    let mut rl = rustyline::Editor::<()>::new();
    let mut eval = Eval::new_empty();
    loop {
        let mut input = match rl.readline("in: ") {
            Ok(x) => x,
            Err(err) => {
                println!("{}", err);
                break;
            }
        };
        input = input.trim_end().into();
        rl.add_history_entry(input.as_str());
        if input == "quit" {
            break;
        }
        let mut lexer = Lexer::new(input, Some("repl".to_string()));
        let tokens = match lexer.lex() {
            Ok(tokens) => tokens,
            Err(err) => {
                eprintln!("{}", err.to_string());
                continue;
            }
        };
        let mut iter = tokens.iter().peekable();
        let mut parser = Parser::new(&mut iter);
        let parsed = match parser.parse() {
            Ok(out) => out,
            Err(err) => {
                eprintln!("{}", err.to_string());
                continue;
            }
        };
        eval.set_input(parsed);
        let out = eval.eval();
        match out {
            Ok(a) => println!("out: {}", a.to_string()),
            Err(e) => eprintln!("{}", e.to_string()),
        }
    }
    Ok(())
}
