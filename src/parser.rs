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
    FuncDef(SourceLocation, String, Vec<Self>, Box<Self>),
    Bool(SourceLocation, bool),
    Number(SourceLocation, i128),
    Float(SourceLocation, f64),
    Ident(SourceLocation, String),
    Assign(SourceLocation, Box<Self>, Box<Self>),
    Variable(SourceLocation, String, Option<Box<Self>>, bool),
    IfStmt(SourceLocation, Box<Self>, Box<Self>, Option<Box<Self>>),
    Block(SourceLocation, Vec<Self>),
    Array(SourceLocation, Vec<Self>),
    Subscript(SourceLocation, Box<Self>, Box<Self>),
    String(SourceLocation, String),
    Return(SourceLocation, Box<Self>),
    Char(SourceLocation, char),
    Null(SourceLocation),
}

pub struct Parser<'a> {
    tokens: &'a mut Peekable<Iter<'a, (SourceLocation, Token)>>,
}

impl<'a> Parser<'a> {
    pub fn new(tokens: &'a mut Peekable<Iter<'a, (SourceLocation, Token)>>) -> Self {
        Self { tokens }
    }

    pub fn primary(&mut self) -> error::Result<Expression> {
        let (loc, token) = self
            .tokens
            .next()
            .ok_or_else(|| Error::Error("unexpected end of input".to_string()))?;
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
                    Some((_, Token::LParen)) => Ok(expr),
                    Some((loc, _)) => Err(Error::SyntaxError(
                        loc.clone(),
                        "expected closing parenthese ')' after expression".into(),
                    )),
                    _ => Err(Error::Error("unexpected end of input".into())),
                }
            }
            Token::RBrace => self.parse_block_stmt(loc.clone()),
            Token::RBracket => {
                let mut elements = Vec::<Expression>::new();
                if !self.check(&Token::LBracket) {
                    let mut curr = None::<&(SourceLocation, Token)>;
                    loop {
                        elements.push(self.expression(0)?);
                        let temp = self.check_current(&Token::Comma);
                        curr = temp.0;
                        if !temp.1 {
                            break;
                        }
                    }
                    match curr {
                        Some((_, Token::LBracket)) => (),
                        _ => {
                            return Err(Error::SyntaxError(
                                loc.clone(),
                                "expected ']' after list".to_string(),
                            ))
                        }
                    };
                }
                Ok(Expression::Array(loc.clone(), elements))
            }
            Token::Let => self.parse_variable(loc.clone()),
            Token::If => {
                let condition = self.expression(0)?;
                let body = self.expression(0)?;
                let mut else_clause: Option<Box<Expression>> = None;
                if let Some((_, Token::Else)) = self.tokens.peek() {
                    self.tokens.next();
                    else_clause = Some(Box::new(self.expression(0)?));
                };
                Ok(Expression::IfStmt(
                    loc.clone(),
                    Box::new(condition),
                    Box::new(body),
                    else_clause,
                ))
            }
            /*Token::Fnc => {
                self.parse_function(
            }*/
            Token::String(s) => Ok(Expression::String(loc.clone(), s.clone())),
            Token::Char(c) => Ok(Expression::Char(loc.clone(), *c)),
            Token::Number(n) => Ok(Expression::Number(loc.clone(), *n)),
            Token::Float(n) => Ok(Expression::Float(loc.clone(), *n)),
            Token::Ident(i) => Ok(Expression::Ident(loc.clone(), i.clone())),
            Token::Bool(b) => Ok(Expression::Bool(loc.clone(), *b)),
            Token::Null => Ok(Expression::Null(loc.clone())),
            Token::Return => Ok(Expression::Return(
                loc.clone(),
                Box::new(self.expression(0)?),
            )),
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
                } else if op.is_prefix_unary() {
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
            } else if self._match(&[Token::RBracket]) {
                let inner = self.expression(0)?;
                lhs = match self.check_current(&Token::LBracket) {
                    (Some(_), true) => {
                        Expression::Subscript(loc.clone(), Box::new(lhs), Box::new(inner))
                    }
                    (Some((loc, _)), false) => {
                        return Err(Error::SyntaxError(
                            loc.clone(),
                            "expected ']' after subscript operator".to_string(),
                        ))
                    }
                    _ => {
                        return Err(Error::Error(
                            "expected ']' after subscript operator".to_string(),
                        ))
                    }
                }
            } else {
                break;
            }
        }
        Ok(lhs)
    }

    fn parse_variable(&mut self, loc: SourceLocation) -> error::Result<Expression> {
        let is_immutable = match self.tokens.peek() {
            Some((_, Token::Imm)) => {
                self.tokens.next();
                true
            }
            _ => false,
        };
        let name = match self.tokens.next() {
            Some((_, Token::Ident(ident))) => ident.clone(),
            Some((loc, _)) => {
                return Err(Error::SyntaxError(
                    loc.clone(),
                    "expected identifier in variable name".to_string(),
                ))
            }
            _ => return Err(Error::Error("unexpected end of input".to_string())),
        };
        let next: Option<Box<Expression>> = match self.tokens.peek() {
            Some((_, Token::Op(Operator::Assign))) => {
                self.tokens.next();
                Some(Box::new(self.expression(0)?))
            }
            _ => None,
        };
        Ok(Expression::Variable(loc, name, next, is_immutable))
    }

    fn parse_block_stmt(&mut self, loc: SourceLocation) -> error::Result<Expression> {
        let mut stmts = vec![];
        while !self.check(&Token::LBrace) {
            let stmt = self.expression(0)?;
            if !self.check_current(&Token::Semicolon).1 {
                return Err(Error::SyntaxError(
                    loc,
                    "expected ';' after statement".to_string(),
                ));
            }
            stmts.push(stmt)
        }
        match self.tokens.next() {
            Some((_, Token::LBrace)) => Ok(Expression::Block(loc, stmts)),
            Some((loc, _)) => Err(Error::SyntaxError(
                loc.clone(),
                "expected closing parenthese '}' after block".into(),
            )),
            _ => Err(Error::Error("unexpected end of input".into())),
        }
    }

    fn parse_function(&mut self, loc: SourceLocation) -> error::Result<Expression> {
        let name = match self.tokens.next() {
            Some((_, Token::Ident(name))) => name.clone(),
            _ => {
                return Err(Error::SyntaxError(
                    loc.clone(),
                    "expected identifier after 'fnc' keyword".to_string(),
                ))
            }
        };
        let mut args: Vec<Expression> = Vec::new();
        if !self.check(&Token::LParen) || !self.check_current(&Token::LParen).1 {
            let mut curr = None::<&(SourceLocation, Token)>;
            loop {
                let ident = match self.tokens.next() {
                    Some((loc, Token::Ident(ident))) => {
                        Expression::Ident(loc.clone(), ident.clone())
                    }
                    _ => {
                        return Err(Error::SyntaxError(
                            loc.clone(),
                            "expected identifier in function argument".to_string(),
                        ))
                    }
                };
                args.push(ident);
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
        Ok(Expression::FuncDef(
            loc.clone(),
            name,
            args,
            Box::new(self.parse_block_stmt(loc)?),
        ))
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
        let token = self.tokens.next();
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
