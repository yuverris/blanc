#![allow(unused_assignments)]
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
    Assign(SourceLocation, Box<Self>, Box<Self>),
    IfStmt(SourceLocation, Box<Self>, Box<Self>, Option<Box<Self>>),
    Block(SourceLocation, Vec<Self>),
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
        let (loc, token) = self
            .tokens
            .next()
            .ok_or(Error::Error("unexpected end of input".to_string()))?;
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
            Token::RBracket => {
                let mut stmts = vec![];
                while !self.check(&Token::LBracket) {
                    let stmt = self.expression(0)?;
                    if !self.check_current(&Token::Semicolon).1 {
                        return Err(Error::SyntaxError(
                            loc.clone(),
                            "expected ';' after statement".to_string(),
                        ));
                    }
                    stmts.push(stmt)
                }
                match self.tokens.next() {
                    Some((_, Token::LBracket)) => {
                        return Ok(Expression::Block(loc.clone(), stmts));
                    }
                    Some((loc, _)) => {
                        return Err(Error::SyntaxError(
                            loc.clone(),
                            "expected closing parenthese '}' after block".into(),
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

                if !self.check(&Token::LParen) || !self.check_current(&Token::LParen).1 {
                    let mut curr = None::<&(SourceLocation, Token)>;
                    loop {
                        args.push(self.expression(0)?);
                        let temp = self.check_current(&Token::Comma);
                        curr = temp.0;
                        if !temp.1 {
                            break;
                        }
                    }
                    match curr {
                        Some((_, Token::LParen)) => (),
                        Some((loc, _)) => {
                            return Err(Error::SyntaxError(
                                loc.clone(),
                                "expected ')' after arguments list".to_string(),
                            ))
                        }
                        _ => {
                            return Err(Error::Error(
                                "expected ')' after arguments list".to_string(),
                            ))
                        }
                    };
                }
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

    fn check_current(&mut self, token_: &Token) -> (Option<&(SourceLocation, Token)>, bool) {
        let token = self.tokens.nth(0);
        (token, matches!(token, Some((_, token)) if token == token_))
    }

    pub fn parse(&mut self) -> error::Result<Vec<Expression>> {
        let mut exprs = vec![];
        while let Some((loc, _)) = self.tokens.peek() {
            let expr = self.expression(0)?;
            if !self.check_current(&Token::Semicolon).1 {
                return Err(Error::SyntaxError(
                    loc.clone(),
                    "expected ';' after statement".to_string(),
                ));
            }
            exprs.push(expr)
        }
        Ok(exprs)
    }
}
