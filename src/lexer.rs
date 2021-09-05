use crate::{
    error::{self, Error},
    source_location::SourceLocation,
};

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum Token {
    Number(i128),
    Float(f64),
    Ident(String),
    Bool(bool),
    Char(char),
    String(String),
    DoubleQuote,
    SingleQuote,
    Fnc,
    Break,
    Return,
    Continue,
    While,
    For,
    Lm,
    Let,
    Imm,
    If,
    Else,
    RBrace,
    LBrace,
    RBracket,
    LBracket,
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
    BitOr,
    BitXor,
    BitAnd,
    BitNot,
    Equal,
    Greater,
    GreaterOrEqual,
    Less,
    LessOrEqual,
    NotEqual,
    And,
    Or,
    Remainder,
    LShift,
    RShift,
    Not,
    Assign,
}

impl Operator {
    pub fn precedence(&self) -> u8 {
        match self {
            Operator::Assign => 10,

            Operator::Or => 11,
            Operator::And => 12,

            Operator::BitOr => 13,
            Operator::BitXor => 14,
            Operator::BitAnd => 15,

            Operator::Equal | Operator::NotEqual => 16,

            Operator::Greater
            | Operator::GreaterOrEqual
            | Operator::Less
            | Operator::LessOrEqual => 17,

            Operator::LShift | Operator::RShift => 18,

            Operator::Minus | Operator::Plus => 19,

            Operator::Star | Operator::Slash | Operator::Remainder => 20,

            Operator::Negative | Operator::Positive | Operator::Not | Operator::BitNot => 21,
        }
    }

    pub fn is_binary(&self) -> bool {
        !matches!(
            self,
            Operator::Not | Operator::Negative | Operator::Positive | Operator::BitNot
        )
    }

    pub fn is_prefix_unary(&self) -> bool {
        matches!(
            self,
            Operator::Not | Operator::Negative | Operator::Positive | Operator::BitNot
        )
    }
}
pub struct Lexer {
    input: String,
    loc: SourceLocation,
}

impl Lexer {
    pub fn new(input: String, file: Option<String>) -> Self {
        Self {
            input,
            loc: SourceLocation::new(file),
        }
    }

    pub fn lex(&mut self) -> error::Result<Vec<(SourceLocation, Token)>> {
        let mut out = Vec::<(SourceLocation, Token)>::new();
        let mut iter = self.input.chars().peekable();
        macro_rules! add_token {
            ($e:expr) => {
                out.push((self.loc.clone(), $e));
            };
        }

        while let Some(ch) = iter.next() {
            match ch {
                c if c.is_alphabetic() || c == '_' => {
                    let mut ident = String::from(ch);
                    while let Some(&ch) = iter.peek() {
                        if !ch.is_alphabetic() && !ch.is_ascii_digit() {
                            break;
                        }
                        ident.push(ch);
                        iter.next();
                    }
                    self.loc.column += ident.len() - 1;
                    match ident.as_str() {
                        "true" => add_token!(Token::Bool(true)),
                        "false" => add_token!(Token::Bool(false)),
                        "if" => add_token!(Token::If),
                        "else" => add_token!(Token::Else),
                        "null" => add_token!(Token::Null),
                        "fnc" => add_token!(Token::Fnc),
                        "continue" => add_token!(Token::Continue),
                        "break" => add_token!(Token::Break),
                        "return" => add_token!(Token::Return),
                        "let" => add_token!(Token::Let),
                        "imm" => add_token!(Token::Imm),
                        "lm" => add_token!(Token::Lm),
                        _ => add_token!(Token::Ident(ident)),
                    }
                }
                '0'..='9' => {
                    let mut num: String = String::new();
                    while let Some(&c) = iter.peek() {
                        if matches!(c, c if c.is_ascii_digit() ||
                            c == 'e' || c == '.')
                        {
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
                    self.loc.column += num.len();
                    let mut number = format!("{}{}", ch, num);
                    let is_float =
                        !number.ends_with('.') && number.chars().any(|e| matches!(e, '.' | 'e'));
                    if is_float {
                        add_token!(Token::Float(number.parse().expect("invalid number format"),));
                    } else if number.ends_with('.') {
                        number.pop();
                        add_token!(Token::Number(
                            number.parse().expect("invalid number format"),
                        ));
                        add_token!(Token::Dot);
                    } else {
                        add_token!(Token::Number(
                            number.parse().expect("invalid number format"),
                        ));
                    }
                }
                '(' => add_token!(Token::RParen),
                ')' => add_token!(Token::LParen),
                '{' => add_token!(Token::RBrace),
                '}' => add_token!(Token::LBrace),
                '[' => add_token!(Token::RBracket),
                ']' => add_token!(Token::LBracket),
                ',' => add_token!(Token::Comma),
                '.' => add_token!(Token::Dot),
                '+' => add_token!(Token::Op(Operator::Plus)),
                '-' => add_token!(Token::Op(Operator::Minus)),
                '*' => add_token!(Token::Op(Operator::Star)),
                '/' => add_token!(Token::Op(Operator::Slash)),
                '^' => add_token!(Token::Op(Operator::BitXor)),
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
                '&' => {
                    if matches!(iter.next(), Some(c) if c == '&') {
                        add_token!(Token::Op(Operator::And));
                    } else {
                        add_token!(Token::Op(Operator::BitAnd));
                    }
                }
                '\'' => {
                    let c: char = iter.next().ok_or_else(|| {
                        Error::SyntaxError(
                            self.loc.clone(),
                            "expected character literal after \"'\"".to_string(),
                        )
                    })?;
                    match iter.next() {
                        Some('\'') => add_token!(Token::Char(c)),
                        _ => {
                            return Err(Error::SyntaxError(
                                self.loc.clone(),
                                "expected closing \"'\"".to_string(),
                            ))
                        }
                    };
                }
                '"' => {
                    let mut out: String = String::new();
                    while let Some(c) = iter.next() {
                        if c == '"' {
                            break;
                        }
                        out.push(c);
                    }
                    add_token!(Token::String(out));
                }
                '|' => {
                    if matches!(iter.next(), Some(c) if c == '|') {
                        add_token!(Token::Op(Operator::Or));
                    } else {
                        add_token!(Token::Op(Operator::BitOr));
                    }
                }
                '\n' => {
                    self.loc.column = 1;
                    self.loc.line += 1;
                }
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
