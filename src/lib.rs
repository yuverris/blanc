use std::{
    iter::Peekable,
    ops::{Add, Div, Mul, Neg, Not, Sub},
    slice::Iter,
    string::ToString,
};

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone, Copy)]
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
        }
    }
}

#[derive(Debug, Clone, Copy, PartialOrd, PartialEq)]
pub enum Value {
    Number(f64),
    Bool(bool),
    Null,
}

impl Add for Value {
    type Output = Result<Self, &'static str>;

    fn add(self, other: Self) -> Self::Output {
        match (self, other) {
            (Value::Number(n), Value::Number(m)) => Ok(Value::Number(n + m)),
            _ => Err("invalid operands for binary operation '+'"),
        }
    }
}

impl Sub for Value {
    type Output = Result<Self, &'static str>;

    fn sub(self, other: Self) -> Self::Output {
        match (self, other) {
            (Value::Number(n), Value::Number(m)) => Ok(Value::Number(n - m)),
            _ => Err("invalid operands for binary operation '-'"),
        }
    }
}

impl Mul for Value {
    type Output = Result<Self, &'static str>;

    fn mul(self, other: Self) -> Self::Output {
        match (self, other) {
            (Value::Number(n), Value::Number(m)) => Ok(Value::Number(n * m)),
            _ => Err("invalid operands for binary operation '*'"),
        }
    }
}

impl Div for Value {
    type Output = Result<Self, &'static str>;

    fn div(self, other: Self) -> Self::Output {
        match (self, other) {
            (Value::Number(n), Value::Number(m)) => Ok(Value::Number(n / m)),
            _ => Err("invalid operands for binary operation '/'"),
        }
    }
}

impl Neg for Value {
    type Output = Result<Self, &'static str>;

    fn neg(self) -> Self::Output {
        match self {
            Value::Number(n) => Ok(Value::Number(-n)),
            _ => Err("invalid operand for unary operation '-'"),
        }
    }
}

impl Not for Value {
    type Output = Result<Self, &'static str>;

    fn not(self) -> Self::Output {
        match self {
            Value::Bool(b) => Ok(Value::Bool(!b)),
            Value::Null => Ok(Value::Bool(true)),
            _ => Err("invalid operand for unary operation '!'"),
        }
    }
}

impl ToString for Value {
    fn to_string(&self) -> String {
        match self {
            Value::Number(n) => n.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Null => "null".into(),
        }
    }
}

pub struct Lexer {
    input: String,
    line: usize,
    pos: usize,
}

impl Lexer {
    pub fn new(input: String) -> Self {
        Self {
            input: input,
            line: 1,
            pos: 1,
        }
    }

    pub fn lex(&mut self) -> Result<Vec<Token>, String> {
        let mut out = Vec::<Token>::new();
        let mut iter = self.input.chars().peekable();
        while let Some(ch) = iter.next() {
            match ch {
                'a'..='z' | 'A'..='Z' | '_' => {
                    let mut ident = String::from(ch);
                    while let Some(ch) = iter.next() {
                        if !ch.is_digit(10) && !ch.is_alphabetic() {
                            break;
                        }
                        ident.push(ch);
                    }
                    match ident.as_str() {
                        "true" => out.push(Token::Bool(true)),
                        "false" => out.push(Token::Bool(false)),
                        "null" => out.push(Token::Null),
                        _ => out.push(Token::Ident(ident)),
                    }
                }
                '0'..='9' => {
                    let mut num: String = String::new();
                    while let Some(c) = iter.peek() {
                        if c.is_ascii_digit() {
                            num.push(*c);
                        } else if *c == 'e' || *c == '.' {
                            num.push(*c);
                        } else if *c == '-' {
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
                    out.push(Token::Number(
                        format!("{}{}", ch, num)
                            .parse()
                            .expect("invalid number format"),
                    ));
                }
                '(' => out.push(Token::RParen),
                ')' => out.push(Token::LParen),
                ',' => out.push(Token::Comma),
                '.' => out.push(Token::Dot),
                '+' => out.push(Token::Op(Operator::Plus)),
                '-' => out.push(Token::Op(Operator::Minus)),
                '*' => out.push(Token::Op(Operator::Star)),
                '/' => out.push(Token::Op(Operator::Slash)),
                '^' => out.push(Token::Op(Operator::Power)),
                '=' => {
                    if let Some(c) = iter.peek() {
                        if *c == '=' {
                            out.push(Token::Op(Operator::Equal));
                            iter.next();
                        } else {
                            out.push(Token::Op(Operator::Assign));
                        }
                        iter.next();
                    }
                }
                '!' => {
                    if let Some(c) = iter.peek() {
                        if *c == '=' {
                            out.push(Token::Op(Operator::NotEqual));
                            iter.next();
                        } else {
                            out.push(Token::Op(Operator::Not));
                        }
                    }
                }
                '\n' => self.line += 1,
                ' ' => continue,
                ';' => out.push(Token::Semicolon),
                _ => {
                    return Err(format!(
                        "[line: {}, column: {}]: invalid character '{}'",
                        self.line, self.pos, ch
                    ))
                }
            }
            self.pos += 1;
        }
        Ok(out)
    }
}

pub struct Parser<'a> {
    tokens: &'a mut Peekable<Iter<'a, Token>>,
}

impl<'a> Parser<'a> {
    pub fn new(tokens: &'a mut Peekable<Iter<'a, Token>>) -> Self {
        Self { tokens: tokens }
    }

    pub fn primary(&mut self) -> Result<Expression, String> {
        match self
            .tokens
            .next()
            .ok_or("unexpected end of statement".to_string())?
        {
            Token::Op(Operator::Minus) => {
                let op = Operator::Negative;
                Ok(Expression::Unary(
                    op,
                    Box::new(self.expression(op.precedence())?),
                ))
            }
            Token::Op(Operator::Plus) => {
                let op = Operator::Positive;
                Ok(Expression::Unary(
                    op,
                    Box::new(self.expression(op.precedence())?),
                ))
            }
            Token::Op(Operator::Not) => {
                let op = Operator::Not;
                Ok(Expression::Unary(
                    op,
                    Box::new(self.expression(op.precedence())?),
                ))
            }
            Token::RParen => {
                let expr = self.expression(0)?;
                match self.tokens.next() {
                    Some(Token::LParen) => {
                        return Ok(expr);
                    }
                    _ => {
                        return Err("expected closing parenthese ')' after expression".into());
                    }
                }
            }
            Token::Number(n) => Ok(Expression::Number(*n)),
            Token::Bool(b) => Ok(Expression::Bool(*b)),
            Token::Null => Ok(Expression::Null),
            t => Err(format!("unexpected token {:?}", t)),
        }
    }

    pub fn expression(&mut self, precedence: u8) -> Result<Expression, String> {
        let mut lhs = self.primary()?;
        while let Some(token) = self.tokens.peek() {
            if let Token::Op(op) = token {
                if op.precedence() < precedence {
                    break;
                }
                self.tokens.next();
                let rhs = self.expression(op.precedence())?;
                lhs = Expression::Binary(*op, Box::new(lhs), Box::new(rhs));
            } else {
                break;
            }
        }
        Ok(lhs)
    }

    pub fn parse(&mut self) -> Result<Expression, String> {
        Ok(self.expression(0)?)
    }
}

#[derive(Debug, Clone)]
pub enum Expression {
    Binary(Operator, Box<Expression>, Box<Expression>),
    Unary(Operator, Box<Expression>),
    Bool(bool),
    Number(f64),
    Null,
}

impl Expression {
    pub fn eval(&self) -> Result<Value, &'static str> {
        match self {
            Expression::Number(x) => Ok(Value::Number(*x)),
            Expression::Bool(b) => Ok(Value::Bool(*b)),
            Expression::Null => Ok(Value::Null),
            Expression::Unary(Operator::Negative, expr) => expr.eval()?.neg(),
            Expression::Unary(Operator::Positive, expr) => expr.eval(),
            Expression::Unary(Operator::Not, expr) => expr.eval()?.not(),
            Expression::Binary(Operator::Plus, lhs, rhs) => lhs.eval()? + rhs.eval()?,
            Expression::Binary(Operator::Minus, lhs, rhs) => lhs.eval()? - rhs.eval()?,
            Expression::Binary(Operator::Slash, lhs, rhs) => lhs.eval()? / rhs.eval()?,
            Expression::Binary(Operator::Star, lhs, rhs) => lhs.eval()? * rhs.eval()?,
            Expression::Binary(Operator::Equal, lhs, rhs) => {
                Ok(Value::Bool(lhs.eval()? == rhs.eval()?))
            }
            Expression::Binary(Operator::NotEqual, lhs, rhs) => {
                Ok(Value::Bool(lhs.eval()? != rhs.eval()?))
            }
            Expression::Binary(Operator::Greater, lhs, rhs) => {
                Ok(Value::Bool(lhs.eval()? > rhs.eval()?))
            }
            Expression::Binary(Operator::GreaterOrEqual, lhs, rhs) => {
                Ok(Value::Bool(lhs.eval()? >= rhs.eval()?))
            }
            Expression::Binary(Operator::Less, lhs, rhs) => {
                Ok(Value::Bool(lhs.eval()? < rhs.eval()?))
            }
            Expression::Binary(Operator::LessOrEqual, lhs, rhs) => {
                Ok(Value::Bool(lhs.eval()? <= rhs.eval()?))
            }
            _ => Err(""),
        }
    }
}
