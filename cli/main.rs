use blanc::utils::RResult;
use colored::Colorize;
use std::borrow::Cow::{self, Owned};

use rustyline::highlight::Highlighter;
use rustyline::hint::{Hinter, HistoryHinter};
use rustyline::validate::{self, MatchingBracketValidator, Validator};
use rustyline::{Context, Editor};
use rustyline_derive::{Completer, Helper};

#[derive(Helper, Completer)]
struct BHelper {
    validator: MatchingBracketValidator,
    hinter: HistoryHinter,
}

impl Hinter for BHelper {
    type Hint = String;

    fn hint(&self, line: &str, pos: usize, ctx: &Context<'_>) -> Option<String> {
        self.hinter.hint(line, pos, ctx)
    }
}

impl Validator for BHelper {
    fn validate(
        &self,
        ctx: &mut validate::ValidationContext,
    ) -> rustyline::Result<validate::ValidationResult> {
        self.validator.validate(ctx)
    }

    fn validate_while_typing(&self) -> bool {
        self.validator.validate_while_typing()
    }
}

impl Highlighter for BHelper {
    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        Owned(hint.bright_black().to_string())
    }
}

fn repl() -> std::io::Result<()> {
    use blanc::{eval::Eval, lexer::Lexer, parser::Parser};
    println!(
        "blanc repl session.\nblanc version: {}\ntype 'quit' or Ctrl-C to terminate this session\n",
        blanc::VERSION
    );
    let hl = BHelper {
        validator: MatchingBracketValidator::new(),
        hinter: HistoryHinter {},
    };
    let mut rl = Editor::<BHelper>::new();
    rl.set_helper(Some(hl));
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
        let iter = tokens.iter().peekable();
        let mut parser = Parser::new(iter);
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
            RResult::Ok(a) => println!("out: {}", a.to_string()),
            RResult::Err(e) => eprintln!("{}", e.to_string()),
            RResult::Return(_) => unreachable!(),
        }
    }
    Ok(())
}
fn evaluate_file(name: String) -> std::io::Result<()> {
    let out = blanc::evaluate(std::fs::read_to_string(&name)?, Some(name), None);
    match out {
        RResult::Err(e) => eprintln!("{}", e.to_string()),
        _ => (),
    };
    Ok(())
}

fn main() -> std::io::Result<()> {
    use clap::{App, Arg};
    let app = App::new("blanc")
        .version(blanc::VERSION)
        .author("dammi-i")
        .arg(
            Arg::with_name("eval")
                .short("e")
                .long("eval")
                .value_name("input")
                .help("evaluates an input")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("file")
                .help("file containing the program to evaluate")
                .index(1),
        )
        .arg(
            Arg::with_name("info")
                .short("i")
                .help("shows informations about the interpreter"),
        )
        .get_matches();
    if let Some(value) = app.value_of("file") {
        match evaluate_file(value.to_string()) {
            Ok(()) => (),
            Err(err) => eprintln!("{}", err),
        };
    } else if let Some(value) = app.value_of("eval") {
        let out = blanc::evaluate(value.to_string(), None, None);
        match out {
            RResult::Ok(a) => println!("{}", a.to_string()),
            RResult::Err(e) => {
                eprintln!("{}", e.to_string());
                std::process::exit(1);
            }
            RResult::Return(_) => unreachable!(),
        }
    } else if app.value_of("version").is_some() {
        println!("blanc {}", blanc::VERSION);
    } else if app.value_of("info").is_some() {
        /* println!(
            "version: {}\nrepo: {}\narch: {}\nplatform: {}",
            blanc::VERSION
        );*/
    } else {
        repl()?;
    }
    Ok(())
}
