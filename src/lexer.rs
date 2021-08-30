use crate::{
    error::{self, Error},
    source_location::SourceLocation,
};

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum Token {
    Number(f64),
    Ident(String),
    Bool(bool),
    Null,
    Comma,
    LParen,
    RParen,
    Dot,
    Semicolon,
    Op(Operator),
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum Operator {
    Negative,
    Positive,
    Plus,
    Minus,
    Star,
    Slash,
    Power,
    Equal,
    Greater,
    GreaterOrEqual,
    Less,
    LessOrEqual,
    NotEqual,
    Not,
    Assign,
    Factorial,
}

impl Operator {
    pub fn precedence(&self) -> u8 {
        match self {
            Operator::Assign => 1,
            Operator::Equal | Operator::NotEqual => 2,

            Operator::Greater
            | Operator::GreaterOrEqual
            | Operator::Less
            | Operator::LessOrEqual => 3,

            Operator::Minus | Operator::Plus => 4,

            Operator::Negative | Operator::Positive | Operator::Not => 5,

            Operator::Star | Operator::Slash => 6,

            Operator::Power => 7,
            Operator::Factorial => 8,
        }
    }

    pub fn is_binary(&self) -> bool {
        match self {
            Operator::Negative | Operator::Positive | Operator::Not => false,
            _ => true,
        }
    }

    pub fn is_postfix_unary(&self) -> bool {
        match self {
            // since '!' is first seen as a not operator
            Operator::Not => true,
            _ => false,
        }
    }
}
pub struct Lexer {
    input: String,
    loc: SourceLocation,
}

impl Lexer {
    pub fn new(input: String, file: Option<String>) -> Self {
        Self {
            input: input,
            loc: SourceLocation::new(file),
        }
    }

    pub fn lex(&mut self) -> error::Result<Vec<(SourceLocation, Token)>> {
        let mut out = Vec::<(SourceLocation, Token)>::new();
        let mut iter = self.input.chars().peekable();
        let loc = self.loc.clone();
        macro_rules! add_token {
            ($e:expr) => {
                out.push((self.loc.clone(), $e));
            };
        }

        while let Some(ch) = iter.next() {
            match ch {
                'a'..='z' | 'A'..='Z' | '_' => {
                    let mut ident = String::from(ch);
                    while let Some(&ch) = iter.peek() {
                        if !ch.is_alphabetic() {
                            break;
                        }
                        ident.push(ch);
                        iter.next();
                    }
                    match ident.as_str() {
                        "true" => add_token!(Token::Bool(true)),
                        "false" => add_token!(Token::Bool(false)),
                        "null" => add_token!(Token::Null),
                        _ => add_token!(Token::Ident(ident)),
                    }
                }
                '0'..='9' => {
                    let mut num: String = String::new();
                    while let Some(&c) = iter.peek() {
                        if c.is_ascii_digit() {
                            num.push(c);
                        } else if c == 'e' || c == '.' {
                            num.push(c);
                        } else if c == '-' {
                            match num.chars().last() {
                                Some(previous) => {
                                    if previous != 'e' {
                                        break;
                                    } else {
                                        num.push('-');
                                    }
                                }
                                None => break,
                            }
                        } else {
                            break;
                        }
                        iter.next();
                    }
                    add_token!(Token::Number(
                        format!("{}{}", ch, num)
                            .parse()
                            .expect("invalid number format"),
                    ));
                }
                '(' => add_token!(Token::RParen),
                ')' => add_token!(Token::LParen),
                ',' => add_token!(Token::Comma),
                '.' => add_token!(Token::Dot),
                '+' => add_token!(Token::Op(Operator::Plus)),
                '-' => add_token!(Token::Op(Operator::Minus)),
                '*' => add_token!(Token::Op(Operator::Star)),
                '/' => add_token!(Token::Op(Operator::Slash)),
                '^' => add_token!(Token::Op(Operator::Power)),
                '=' => {
                    if matches!(iter.peek(), Some(&c) if c == '=') {
                        add_token!(Token::Op(Operator::Equal));
                        iter.next();
                    } else {
                        add_token!(Token::Op(Operator::Assign));
                    }
                }
                '>' => {
                    if matches!(iter.peek(), Some(&c) if c == '=') {
                        add_token!(Token::Op(Operator::GreaterOrEqual));
                        iter.next();
                    } else {
                        add_token!(Token::Op(Operator::Greater));
                    }
                }
                '<' => {
                    if matches!(iter.peek(), Some(&c) if c == '=') {
                        add_token!(Token::Op(Operator::LessOrEqual));
                        iter.next();
                    } else {
                        add_token!(Token::Op(Operator::Less));
                    }
                }
                '!' => {
                    if matches!(iter.peek(), Some(&c) if c == '=') {
                        add_token!(Token::Op(Operator::NotEqual));
                        iter.next();
                    } else {
                        add_token!(Token::Op(Operator::Not));
                    }
                }
                '\n' => self.loc.line += 1,
                ' ' => continue,
                ';' => add_token!(Token::Semicolon),
                _ => {
                    return Err(Error::SyntaxError(
                        self.loc.clone(),
                        format!("invalid character '{}'", ch),
                    ))
                }
            }
            self.loc.column += 1;
        }
        Ok(out)
    }
}
