use crate::{
    error::{self, Error},
    lexer::{Operator, Token},
    source_location::SourceLocation,
};
use std::{iter::Peekable, slice::Iter};

#[derive(Debug, Clone)]
pub enum Expression {
    Binary(SourceLocation, Operator, Box<Self>, Box<Self>),
    Unary(SourceLocation, Operator, Box<Self>),
    FuncCall(SourceLocation, Box<Self>, Vec<Self>),
    Bool(SourceLocation, bool),
    Number(SourceLocation, f64),
    Ident(SourceLocation, String),
    Null(SourceLocation),
}

pub struct Parser<'a> {
    tokens: &'a mut Peekable<Iter<'a, (SourceLocation, Token)>>,
}

impl<'a> Parser<'a> {
    pub fn new(tokens: &'a mut Peekable<Iter<'a, (SourceLocation, Token)>>) -> Self {
        Self { tokens: tokens }
    }

    pub fn primary(&mut self) -> error::Result<Expression> {
        let (loc, token) = self.tokens.next().ok_or(Error::ParseError(
            SourceLocation::new(None),
            "unexpected end of input".into(),
        ))?;
        match token {
            Token::Op(Operator::Minus) => {
                let op = Operator::Negative;
                Ok(Expression::Unary(
                    loc.clone(),
                    op.clone(),
                    Box::new(self.expression(op.precedence())?),
                ))
            }
            Token::Op(Operator::Plus) => {
                let op = Operator::Positive;
                Ok(Expression::Unary(
                    loc.clone(),
                    op.clone(),
                    Box::new(self.expression(op.precedence())?),
                ))
            }
            Token::Op(Operator::Not) => {
                let op = Operator::Not;
                Ok(Expression::Unary(
                    loc.clone(),
                    op.clone(),
                    Box::new(self.expression(op.precedence())?),
                ))
            }
            Token::RParen => {
                let expr = self.expression(0)?;
                match self.tokens.next() {
                    Some((_, Token::LParen)) => {
                        return Ok(expr);
                    }
                    Some((loc, _)) => {
                        return Err(Error::SyntaxError(
                            loc.clone(),
                            "expected closing parenthese ')' after expression".into(),
                        ));
                    }
                    _ => Err(Error::Error("unexpected end of input".into())),
                }
            }
            Token::Number(n) => Ok(Expression::Number(loc.clone(), *n)),
            Token::Ident(i) => Ok(Expression::Ident(loc.clone(), i.clone())),
            Token::Bool(b) => Ok(Expression::Bool(loc.clone(), *b)),
            Token::Null => Ok(Expression::Null(loc.clone())),
            token => Err(Error::SyntaxError(
                loc.clone(),
                format!("unexpected token {:?}", token),
            )),
        }
    }

    pub fn expression(&mut self, precedence: u8) -> error::Result<Expression> {
        let mut lhs = self.primary()?;
        while let Some((loc, token)) = self.tokens.peek() {
            if let Token::Op(op) = token.clone() {
                if op.precedence() < precedence {
                    break;
                }
                self.tokens.next();
                if op.is_binary() {
                    let rhs = self.expression(op.precedence())?;

                    lhs = Expression::Binary(loc.clone(), op.clone(), Box::new(lhs), Box::new(rhs));
                } else if op.is_postfix_unary() {
                    let op = match op.clone() {
                        Operator::Not => Operator::Factorial,
                        op => op,
                    };

                    lhs = Expression::Unary(loc.clone(), op, Box::new(lhs));
                } else {
                    return Err(Error::SyntaxError(loc.clone(), "invalid syntax".into()));
                }
            } else if self._match(&[Token::RParen]) {
                let mut args = Vec::<Expression>::new();

                if !self.check(&Token::LParen) {
                    while {
                        args.push(self.expression(0)?);
                        self.check_current(&Token::Comma)
                    } {}
                }
                self.consume(
                    &Token::LParen,
                    Error::SyntaxError(loc.clone(), "expected ')' after arguments list".into()),
                );
                lhs = Expression::FuncCall(loc.clone(), Box::new(lhs), args);
            } else {
                break;
            }
        }
        Ok(lhs)
    }

    fn check(&mut self, token_: &Token) -> bool {
        matches!(self.tokens.peek(), Some((_, token)) if token == token_)
    }

    fn _match(&mut self, tokens: &[Token]) -> bool {
        for token in tokens {
            if self.check(token) {
                self.tokens.next();
                return true;
            }
        }
        false
    }

    fn check_current(&mut self, token_: &Token) -> bool {
        matches!(self.tokens.nth(0), Some((_, token)) if token == token_)
    }

    fn consume(&mut self, token: &Token, error: Error) -> error::Result<Token> {
        if !self.check(token) {
            Err(error)
        } else {
            let prev = self.tokens.nth(0).unwrap();
            self.tokens.next();
            Ok(prev.1.clone())
        }
    }

    pub fn parse(&mut self) -> error::Result<Expression> {
        self.expression(0)
    }
}
