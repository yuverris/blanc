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
    LBracket,
    Null,
    Comma,
    LParen,
    Semicolon,
    Colon,
    Imp,    // import
    Exp,    // export
    Als,    // alias
    Arrow,  // ->
    Warlus, // :=
    Pack,   // ...
    End,
    Op(Operator),
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum Operator {
    Negative,
    Positive,
    Plus,
    PlusAssign,
    Minus,
    MinusAssign,
    Star,
    StarAssign,
    Slash,
    SlashAssign,
    BitOr,
    BitOrAssign,
    BitXor,
    BitXorAssign,
    BitAnd,
    BitAndAssign,
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
    RemainderAssign,
    LShift,
    LShiftAssign,
    RShift,
    RShiftAssign,
    Not,
    Assign,
    //Range,
    Dot,
    RParen,
    RBracket,
}

impl Operator {
    pub fn precedence(&self) -> u8 {
        match self {
            Operator::Dot => 50,

            Operator::Assign
            | Operator::PlusAssign
            | Operator::MinusAssign
            | Operator::StarAssign
            | Operator::SlashAssign
            | Operator::RemainderAssign
            | Operator::BitOrAssign
            | Operator::BitXorAssign
            | Operator::BitAndAssign
            | Operator::RShiftAssign
            | Operator::LShiftAssign => 10,

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

            Operator::RParen => 22,

            Operator::RBracket => 23,
        }
    }

    pub fn is_binary(&self) -> bool {
        !matches!(
            self,
            Operator::Not
                | Operator::Negative
                | Operator::Positive
                | Operator::BitNot
                | Operator::RParen
                | Operator::RBracket
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
                        if ch == '_' {
                            ident.push('_');
                            iter.next();
                        } else if !ch.is_alphabetic() && !ch.is_ascii_digit() {
                            break;
                        } else {
                            ident.push(ch);
                            iter.next();
                        }
                    }
                    self.loc.column += ident.len();
                    match ident.as_str() {
                        "true" => add_token!(Token::Bool(true)),
                        "false" => add_token!(Token::Bool(false)),
                        "if" => add_token!(Token::If),
                        "while" => add_token!(Token::While),
                        "for" => add_token!(Token::For),
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
                    // TODO: make this cleaner
                    if ch == '0'
                        && matches!(
                            iter.peek(),
                            Some(&'x')
                                | Some(&'o')
                                | Some(&'b')
                                | Some(&'O')
                                | Some(&'B')
                                | Some(&'X')
                        )
                    {
                        match iter.peek().unwrap() {
                            'x' => {
                                iter.next();
                                let mut hex = String::new();
                                while matches!(iter.peek(), Some(&c) if c.is_digit(16)) {
                                    hex.push(iter.next().unwrap());
                                }
                                self.loc.column += hex.len();
                                add_token!(Token::Number(
                                    i128::from_str_radix(hex.as_str(), 16).map_err(|_| {
                                        Error::SyntaxError(
                                            self.loc.clone(),
                                            "invalid hex value".to_string(),
                                        )
                                    })?
                                ));
                            }
                            'b' => {
                                iter.next();
                                let mut bin = String::new();
                                while matches!(iter.peek(), Some(&c) if c.is_digit(2)) {
                                    bin.push(iter.next().unwrap());
                                }
                                self.loc.column += bin.len();
                                add_token!(Token::Number(
                                    i128::from_str_radix(bin.as_str(), 2).map_err(|_| {
                                        Error::SyntaxError(
                                            self.loc.clone(),
                                            "invalid binary value".to_string(),
                                        )
                                    })?
                                ));
                            }

                            'o' => {
                                iter.next();
                                let mut oct = String::new();
                                while matches!(iter.peek(), Some(&c) if c.is_digit(8)) {
                                    oct.push(iter.next().unwrap());
                                }
                                self.loc.column += oct.len();
                                add_token!(Token::Number(
                                    i128::from_str_radix(oct.as_str(), 8).map_err(|_| {
                                        Error::SyntaxError(
                                            self.loc.clone(),
                                            "invalid octal value".to_string(),
                                        )
                                    })?
                                ));
                            }
                            _ => unreachable!(), //cuz of the matches! above
                        };
                    } else {
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
                        let ends_with_dot = number.ends_with('.');

                        if ends_with_dot {
                            number.pop();
                        }

                        let is_float = number.chars().any(|e| matches!(e, '.' | 'e'));

                        if is_float {
                            add_token!(Token::Float(number.parse().expect("invalid float format")));
                        } else {
                            add_token!(Token::Number(
                                number.parse().expect("invalid number format"),
                            ));
                        }

                        if ends_with_dot {
                            add_token!(Token::Op(Operator::Dot))
                        }
                    }
                }
                '(' => add_token!(Token::Op(Operator::RParen)),
                ')' => add_token!(Token::LParen),
                '{' => add_token!(Token::RBrace),
                '}' => add_token!(Token::LBrace),
                '[' => add_token!(Token::Op(Operator::RBracket)),
                ']' => add_token!(Token::LBracket),
                ',' => add_token!(Token::Comma),
                '.' => add_token!(Token::Op(Operator::Dot)),
                '+' => {
                    if matches!(iter.peek(), Some(&'=')) {
                        add_token!(Token::Op(Operator::PlusAssign));
                        iter.next();
                    } else {
                        add_token!(Token::Op(Operator::Plus));
                    }
                }
                '-' => {
                    if matches!(iter.peek(), Some(&'=')) {
                        add_token!(Token::Op(Operator::MinusAssign));
                        iter.next();
                    } else {
                        add_token!(Token::Op(Operator::Minus));
                    }
                }
                '*' => {
                    if matches!(iter.peek(), Some(&'=')) {
                        add_token!(Token::Op(Operator::StarAssign));
                        iter.next();
                    } else {
                        add_token!(Token::Op(Operator::Star));
                    }
                }
                '/' => {
                    if matches!(iter.peek(), Some(&'=')) {
                        add_token!(Token::Op(Operator::SlashAssign));
                        iter.next();
                    } else if matches!(iter.peek(), Some(&'/')) {
                        while !matches!(iter.next(), Some('\n') | None) {}
                    } else if matches!(iter.peek(), Some(&'*')) {
                        iter.next();
                        while !matches!(
                            (iter.next(), iter.next()),
                            (Some('*'), Some('/')) | (_, None)
                        ) {}
                    } else {
                        add_token!(Token::Op(Operator::Slash));
                    }
                }
                '%' => add_token!(Token::Op(Operator::Remainder)),
                '&' => {
                    if matches!(iter.peek(), Some(&'&')) {
                        add_token!(Token::Op(Operator::And));
                        iter.next();
                    } else if matches!(iter.peek(), Some(&'=')) {
                        add_token!(Token::Op(Operator::BitAndAssign));
                        iter.next();
                    } else {
                        add_token!(Token::Op(Operator::BitAnd));
                    }
                }
                '|' => {
                    if matches!(iter.peek(), Some(&'|')) {
                        add_token!(Token::Op(Operator::Or));
                        iter.next();
                    } else if matches!(iter.peek(), Some(&'=')) {
                        add_token!(Token::Op(Operator::BitOrAssign));
                        iter.next();
                    } else {
                        add_token!(Token::Op(Operator::BitOr));
                    }
                }
                '^' => {
                    if matches!(iter.peek(), Some(&'=')) {
                        add_token!(Token::Op(Operator::BitXorAssign));
                        iter.next();
                    } else {
                        add_token!(Token::Op(Operator::BitXor));
                    }
                }
                '~' => add_token!(Token::Op(Operator::Not)),
                '=' => {
                    if matches!(iter.peek(), Some(&'=')) {
                        add_token!(Token::Op(Operator::Equal));
                        iter.next();
                    } else {
                        add_token!(Token::Op(Operator::Assign));
                    }
                }
                '<' => {
                    if matches!(iter.peek(), Some(&'=')) {
                        add_token!(Token::Op(Operator::LessOrEqual));
                        iter.next();
                    } else if matches!(iter.peek(), Some(&'<')) {
                        iter.next();
                        if matches!(iter.peek(), Some(&'=')) {
                            add_token!(Token::Op(Operator::LShiftAssign));
                            iter.next();
                        } else {
                            add_token!(Token::Op(Operator::LShift));
                        }
                    } else {
                        add_token!(Token::Op(Operator::Less));
                    }
                }
                '>' => {
                    if matches!(iter.peek(), Some(&'=')) {
                        add_token!(Token::Op(Operator::GreaterOrEqual));
                        iter.next();
                    } else if matches!(iter.peek(), Some(&'>')) {
                        iter.next();
                        if matches!(iter.peek(), Some(&'=')) {
                            add_token!(Token::Op(Operator::RShiftAssign));
                            iter.next();
                        } else {
                            add_token!(Token::Op(Operator::RShift));
                        }
                    } else {
                        add_token!(Token::Op(Operator::Greater));
                    }
                }
                '!' => {
                    if matches!(iter.peek(), Some(&'=')) {
                        add_token!(Token::Op(Operator::NotEqual));
                        iter.next();
                    } else {
                        add_token!(Token::Op(Operator::Not));
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
                    self.loc.column += out.len();
                    add_token!(Token::String(out));
                }
                '\n' => {
                    self.loc.column = 1;
                    self.loc.line += 1;
                }
                ' ' => continue,
                ';' => add_token!(Token::Semicolon),
                ':' => add_token!(Token::Colon),
                _ => {
                    return Err(Error::SyntaxError(
                        self.loc.clone(),
                        format!("invalid character '{}'", ch),
                    ))
                }
            }
            self.loc.column += 1;
        }
        add_token!(Token::End);
        Ok(out)
    }
}
