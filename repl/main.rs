fn main() -> std::io::Result<()> {
    println!("blanc math interpreter repl session.\nblanc version: {}\ntype 'quit' or Ctrl-C to terminate this session\n",
        blanc::VERSION);
    let mut rl = rustyline::Editor::<()>::new();
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
        let out = blanc::evaluate(input, None, None);
        match out {
            Ok(a) => println!("out: {}", a),
            Err(e) => eprintln!("{}", e),
        }
    }
    Ok(())
}
