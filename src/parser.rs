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
    FuncDef(SourceLocation, String, Vec<String>, Box<Self>),
    Bool(SourceLocation, bool),
    Number(SourceLocation, i128),
    Float(SourceLocation, f64),
    Ident(SourceLocation, String),
    Variable(SourceLocation, String, Option<Box<Self>>, bool),
    IfStmt(SourceLocation, Box<Self>, Box<Self>, Option<Box<Self>>),
    WhileStmt(SourceLocation, Option<Box<Self>>, Box<Self>),
    ForStmt(SourceLocation, Box<Self>, Box<Self>),
    Block(SourceLocation, Vec<Self>),
    Array(SourceLocation, Vec<Self>),
    Subscript(SourceLocation, Box<Self>, Box<Self>),
    String(SourceLocation, String),
    Return(SourceLocation, Box<Self>),
    Char(SourceLocation, char),
    Break(SourceLocation),
    Continue(SourceLocation),
    Null(SourceLocation),
}

pub struct Parser<'a> {
    tokens: Peekable<Iter<'a, (SourceLocation, Token)>>,
}

impl<'a> Parser<'a> {
    pub fn new(tokens: Peekable<Iter<'a, (SourceLocation, Token)>>) -> Self {
        Self { tokens }
    }

    fn get_next(&mut self) -> (SourceLocation, Token) {
        if let Some(_) = self.tokens.peek() {
            self.tokens.next().unwrap().clone()
        } else {
            self.tokens.clone().last().unwrap().clone()
        }
    }

    fn get(&mut self) -> (SourceLocation, Token) {
        if let Some(o) = self.tokens.nth(0) {
            o.clone()
        } else {
            self.tokens.clone().last().unwrap().clone()
        }
    }

    fn advance(&mut self) -> (SourceLocation, Token) {
        self.tokens.next().unwrap().clone()
    }

    fn _check_current(&self, token: &Token) -> bool {
        matches!(self.get_without_consuming(), Some((_, tok)) if &tok == token)
    }

    fn get_without_consuming(&self) -> Option<(SourceLocation, Token)> {
        self.tokens.clone().nth(0).map(|t| t.clone())
    }

    fn check_next(&self, token: &Token) -> bool {
        matches!(self.tokens.clone().next(), Some((_,tok)) if tok==token)
    }

    pub fn primary(&mut self) -> error::Result<Expression> {
        let (loc, token) = self.tokens.next().unwrap();
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
            Token::Op(Operator::RParen) => {
                let expr = self.expression(0)?;
                match self.get() {
                    (_, Token::LParen) => Ok(expr),
                    (loc, _) => Err(Error::SyntaxError(
                        loc.clone(),
                        "expected closing parenthese ')' after expression".into(),
                    )),
                }
            }
            Token::RBrace => self.parse_block_stmt(),
            Token::Op(Operator::RBracket) => {
                let mut elements = Vec::<Expression>::new();
                if !self._check_current(&Token::LBracket) {
                    loop {
                        elements.push(self.expression(0)?);
                        if !self._check_current(&Token::Comma) {
                            break;
                        }
                        self.advance();
                    }
                }
                match self.get_without_consuming() {
                    Some((_, Token::LBracket)) => self.advance(),
                    Some((loc, _)) => {
                        return Err(Error::SyntaxError(
                            loc.clone(),
                            "expected ']' after list".to_string(),
                        ))
                    }
                    _ => unreachable!(),
                };

                Ok(Expression::Array(loc.clone(), elements))
            }
            Token::Let => self.parse_variable(loc.clone()),
            Token::If => {
                let condition = self.expression(0)?;
                let body = self.expression(0)?;
                let mut else_clause: Option<Box<Expression>> = None;
                if let Some((_, Token::Else)) = self.tokens.peek() {
                    self.advance();
                    else_clause = Some(Box::new(self.expression(0)?));
                };
                Ok(Expression::IfStmt(
                    loc.clone(),
                    Box::new(condition),
                    Box::new(body),
                    else_clause,
                ))
            }
            Token::Fnc => self.parse_function(loc.clone()),
            Token::While => self.parse_while(loc.clone()),
            //Token::For => self.parse_for(loc.clone()),
            Token::String(s) => Ok(Expression::String(loc.clone(), s.clone())),
            Token::Char(c) => Ok(Expression::Char(loc.clone(), *c)),
            Token::Number(n) => Ok(Expression::Number(loc.clone(), *n)),
            Token::Float(n) => Ok(Expression::Float(loc.clone(), *n)),
            Token::Ident(i) => Ok(Expression::Ident(loc.clone(), i.clone())),
            Token::Bool(b) => Ok(Expression::Bool(loc.clone(), *b)),
            Token::Null => Ok(Expression::Null(loc.clone())),
            Token::Break => Ok(Expression::Break(loc.clone())),
            Token::Continue => Ok(Expression::Continue(loc.clone())),
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
        while !self._check_current(&Token::Semicolon) {
            let (loc, token) = self.tokens.peek().unwrap();
            if let Token::Op(op) = token.clone() {
                if op.precedence() < precedence {
                    break;
                }
                if op.is_binary() {
                    self.advance();
                    let rhs = self.expression(op.precedence())?;

                    lhs = Expression::Binary(loc.clone(), op.clone(), Box::new(lhs), Box::new(rhs));
                } else if op.is_prefix_unary() {
                    lhs = Expression::Unary(loc.clone(), op, Box::new(lhs));
                } else if &op == &Operator::RParen {
                    let mut args = Vec::<Expression>::new();
                    self.advance();

                    if !self._check_current(&Token::LParen) {
                        loop {
                            args.push(self.expression(0)?);
                            if !self._check_current(&Token::Comma) {
                                break;
                            }
                            self.advance();
                        }
                    }
                    match self.get_without_consuming() {
                        Some((_, Token::LParen)) => self.advance(),
                        Some((loc, _)) => {
                            return Err(Error::SyntaxError(
                                loc.clone(),
                                "expected ')' after arguments list".to_string(),
                            ))
                        }
                        _ => unreachable!(),
                    };

                    lhs = Expression::FuncCall(loc.clone(), Box::new(lhs), args);
                } else if &op == &Operator::RBracket {
                    self.advance();
                    let inner = self.expression(0)?;
                    lhs = match self.get_without_consuming() {
                        Some((loc, Token::LBracket)) => {
                            self.advance();
                            Expression::Subscript(loc, Box::new(lhs), Box::new(inner))
                        }
                        Some((loc, _)) => {
                            return Err(Error::SyntaxError(
                                loc.clone(),
                                "expected ']' after subscript operator".to_string(),
                            ))
                        }
                        _ => unreachable!(),
                    }
                } else {
                    return Err(Error::SyntaxError(loc.clone(), "invalid syntax".into()));
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
                self.advance();
                true
            }
            _ => false,
        };
        let name = match self.advance() {
            (_, Token::Ident(ident)) => ident.clone(),
            (loc, _) => {
                return Err(Error::SyntaxError(
                    loc.clone(),
                    "expected identifier in variable name".to_string(),
                ))
            }
        };
        let next: Option<Box<Expression>> = match self.tokens.peek() {
            Some((_, Token::Op(Operator::Assign))) => {
                self.advance();
                Some(Box::new(self.expression(0)?))
            }
            _ => None,
        };
        Ok(Expression::Variable(loc, name, next, is_immutable))
    }

    fn parse_block_stmt(&mut self) -> error::Result<Expression> {
        let mut stmts = vec![];
        while !self._check_current(&Token::LBrace) {
            let stmt = self.expression(0)?;
            if !self._check_current(&Token::Semicolon) {
                return Err(Error::SyntaxError(
                    self.get().0,
                    "expected ';' after statement".to_string(),
                ));
            }
            self.advance();
            stmts.push(stmt)
        }
        match self.get() {
            (loc, Token::LBrace) => Ok(Expression::Block(loc, stmts)),
            (loc, _) => Err(Error::SyntaxError(
                loc.clone(),
                "expected closing parenthese '}' after block".into(),
            )),
        }
    }

    fn parse_while(&mut self, loc: SourceLocation) -> error::Result<Expression> {
        let condition = match self.get_without_consuming() {
            Some((_, Token::RBrace)) => None,
            _ => {
                let expr = Box::new(self.expression(0)?);
                self.advance();
                Some(expr)
            }
        };
        let body = self.parse_block_stmt()?;
        Ok(Expression::WhileStmt(loc, condition, Box::new(body)))
    }

    fn parse_function(&mut self, loc: SourceLocation) -> error::Result<Expression> {
        let name = match self.advance() {
            (_, Token::Ident(name)) => {
                self.advance();
                name.clone()
            }
            (loc, _) => {
                return Err(Error::SyntaxError(
                    loc,
                    "expected identifier after 'fnc' keyword".to_string(),
                ))
            }
        };
        let mut args: Vec<String> = Vec::new();
        if !self._match(&[Token::LParen]) {
            let mut curr = None::<&(SourceLocation, Token)>;
            loop {
                let ident = match self.advance() {
                    (_, Token::Ident(ident)) => ident.clone(),
                    (loc, _) => {
                        return Err(Error::SyntaxError(
                            loc,
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
        let body = match self.advance() {
            (_, Token::RBrace) => self.parse_block_stmt()?,
            (loc, _) => {
                return Err(Error::SyntaxError(
                    loc.clone(),
                    "expected '{' after function declaration".to_string(),
                ));
            }
        };
        Ok(Expression::FuncDef(loc.clone(), name, args, Box::new(body)))
    }

    fn check(&mut self, token_: &Token) -> bool {
        matches!(self.tokens.peek(), Some((_, token)) if token == token_)
    }

    fn _match(&mut self, tokens: &[Token]) -> bool {
        for token in tokens {
            if self.check(token) {
                self.advance();
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
        while !self._check_current(&Token::End) {
            let expr = self.expression(0)?;
            if !self._check_current(&Token::Semicolon) {
                return Err(Error::SyntaxError(
                    self.get_without_consuming().unwrap().0,
                    "expected ';' after statement".to_string(),
                ));
            }
            self.advance();
            exprs.push(expr);
        }
        Ok(exprs)
    }
}
