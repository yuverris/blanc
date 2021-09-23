#![allow(unused_assignments)]
use crate::{
    error::{self, Error},
    lexer::{Operator, Token},
    source_location::SourceLocation,
};
use std::{iter::Peekable, slice::Iter};

#[derive(Debug, Clone)]
pub struct ArgHandler {
    pub name: Option<String>,
    pub value: Option<Expression>,
}

#[derive(Debug, Clone)]
pub struct InFor {
    ident: String,
    iterable: Expression,
}

#[derive(Debug, Clone)]
pub enum Expression {
    Binary(SourceLocation, Operator, Box<Self>, Box<Self>),
    Unary(SourceLocation, Operator, Box<Self>),
    FuncCall(SourceLocation, Box<Self>, Vec<ArgHandler>),
    FuncDef(SourceLocation, Option<String>, Vec<ArgHandler>, Box<Self>),
    Bool(SourceLocation, bool),
    Number(SourceLocation, i128),
    Float(SourceLocation, f64),
    Ident(SourceLocation, String),
    Variable(SourceLocation, String, Option<Box<Self>>, bool),
    IfStmt(SourceLocation, Box<Self>, Box<Self>, Option<Box<Self>>),
    WhileStmt(SourceLocation, Option<Box<Self>>, Box<Self>),
    ForStmt(SourceLocation, Box<InFor>, Box<Self>),
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

    #[allow(dead_code)]
    fn get_next(&mut self) -> (SourceLocation, Token) {
        if self.tokens.peek().is_some() {
            self.tokens.next().unwrap().clone()
        } else {
            self.tokens.clone().last().unwrap().clone()
        }
    }

    fn peek(&self, len: usize) -> Option<(SourceLocation, Token)> {
        self.tokens.clone().nth(len).cloned()
    }

    fn get(&mut self) -> (SourceLocation, Token) {
        self.tokens.next().unwrap().clone()
    }

    fn advance(&mut self) -> (SourceLocation, Token) {
        self.tokens.next().unwrap().clone()
    }

    fn check_current(&self, token: &Token) -> bool {
        matches!(self.get_without_consuming(), Some((_, tok)) if &tok == token)
    }

    fn get_without_consuming(&self) -> Option<(SourceLocation, Token)> {
        self.tokens.clone().next().cloned()
    }

    #[allow(dead_code)]
    fn check_next(&self, token: &Token) -> bool {
        matches!(self.tokens.clone().next(), Some((_,tok)) if tok==token)
    }

    pub fn primary(&mut self) -> error::Result<Expression> {
        let (loc, token) = self.tokens.next().cloned().unwrap();
        let mut in_loop = false;
        match token {
            Token::Op(Operator::Minus) => {
                let op = Operator::Negative;
                Ok(Expression::Unary(
                    loc,
                    op.clone(),
                    Box::new(self.expression(op.precedence())?),
                ))
            }
            Token::Op(Operator::Plus) => {
                let op = Operator::Positive;
                Ok(Expression::Unary(
                    loc,
                    op.clone(),
                    Box::new(self.expression(op.precedence())?),
                ))
            }
            Token::Op(Operator::Not) => {
                let op = Operator::Not;
                Ok(Expression::Unary(
                    loc,
                    op.clone(),
                    Box::new(self.expression(op.precedence())?),
                ))
            }
            Token::Op(Operator::RParen) => {
                if !self.check_current(&Token::LParen) {
                    let expr = self.expression(0)?;
                    match self.get_without_consuming() {
                        Some((_, Token::LParen)) => {
                            self.advance();
                            Ok(expr)
                        }
                        Some((loc, _)) => Err(Error::SyntaxError(
                            loc,
                            "expected closing parenthese ')' after expression".into(),
                        )),
                        _ => unreachable!(),
                    }
                } else {
                    Ok(Expression::Null(loc))
                }
            }
            Token::RBrace => self.parse_block_stmt(),
            Token::Op(Operator::RBracket) => {
                let mut elements = Vec::<Expression>::new();
                if !self.check_current(&Token::LBracket) {
                    loop {
                        elements.push(self.expression(0)?);
                        if !self.check_current(&Token::Comma) {
                            break;
                        }
                        self.advance();
                    }
                }
                match self.get_without_consuming() {
                    Some((_, Token::LBracket)) => self.advance(),
                    Some((loc, _)) => {
                        return Err(Error::SyntaxError(
                            loc,
                            "expected ']' after list".to_string(),
                        ))
                    }
                    _ => unreachable!(),
                };

                Ok(Expression::Array(loc, elements))
            }
            Token::Let => self.parse_variable(loc),
            Token::If => {
                let condition = self.expression(0)?;
                let body = self.expression(0)?;
                let mut else_clause: Option<Box<Expression>> = None;
                if let Some((_, Token::Else)) = self.tokens.peek() {
                    self.advance();
                    else_clause = Some(Box::new(self.expression(0)?));
                };
                Ok(Expression::IfStmt(
                    loc,
                    Box::new(condition),
                    Box::new(body),
                    else_clause,
                ))
            }
            Token::Fnc => self.parse_function(loc),
            Token::While => {
                in_loop = true;
                let out = self.parse_while(loc);
                in_loop = false;
                out
            }
            Token::For => {
                in_loop = true;
                let out = self.parse_for(loc);
                in_loop = false;
                out
            }
            Token::String(s) => Ok(Expression::String(loc, s)),
            Token::Char(c) => Ok(Expression::Char(loc, c)),
            Token::Number(n) => Ok(Expression::Number(loc, n)),
            Token::Float(n) => Ok(Expression::Float(loc, n)),
            Token::Ident(i) => Ok(Expression::Ident(loc, i)),
            Token::Bool(b) => Ok(Expression::Bool(loc, b)),
            Token::Null => Ok(Expression::Null(loc)),
            Token::Break => {
                if !in_loop {
                    Err(Error::SyntaxError(
                        loc,
                        "use of `break` outside loop statement".to_string(),
                    ))
                } else {
                    Ok(Expression::Break(loc))
                }
            }
            Token::Continue => {
                if !in_loop {
                    Err(Error::SyntaxError(
                        loc,
                        "use of `continue` outside loop statement".to_string(),
                    ))
                } else {
                    Ok(Expression::Continue(loc))
                }
            }
            Token::Return => Ok(Expression::Return(loc, Box::new(self.expression(0)?))),
            Token::End => Err(Error::SyntaxError(
                loc,
                "unexpected end of input".to_string(),
            )),
            token => Err(Error::SyntaxError(
                loc,
                format!("unexpected token {:?}", token),
            )),
        }
    }

    pub fn expression(&mut self, precedence: u8) -> error::Result<Expression> {
        let mut lhs = self.primary()?;
        while !self.check_current(&Token::Semicolon) {
            let (loc, token) = self.tokens.peek().unwrap();
            if let Token::Op(op) = token.clone() {
                if op.precedence() <= precedence {
                    break;
                }
                self.advance();
                if op.is_binary() {
                    let rhs = self.expression(op.precedence())?;

                    lhs = Expression::Binary(loc.clone(), op.clone(), Box::new(lhs), Box::new(rhs));
                } else if op.is_prefix_unary() {
                    lhs = Expression::Unary(loc.clone(), op, Box::new(lhs));
                } else if op == Operator::RParen {
                    let mut args = Vec::<ArgHandler>::new();

                    if !self.check_current(&Token::LParen) {
                        loop {
                            if matches!(self.peek(0), Some((_, Token::Ident(_))))
                                && matches!(self.peek(1), Some((_, Token::Colon)))
                            {
                                let name = match self.advance() {
                                    (_, Token::Ident(ident)) => Some(ident),
                                    _ => unreachable!(),
                                };
                                let value = match self.advance() {
                                    (_, Token::Colon) => Some(self.expression(0)?),
                                    _ => unreachable!(),
                                };
                                args.push(ArgHandler { name, value });
                            } else {
                                args.push(ArgHandler {
                                    name: None,
                                    value: Some(self.expression(0)?),
                                });
                            }
                            if !self.check_current(&Token::Comma) {
                                break;
                            }
                            self.advance();
                        }
                    }
                    match self.get_without_consuming() {
                        Some((_, Token::LParen)) => self.advance(),
                        Some((loc, _)) => {
                            return Err(Error::SyntaxError(
                                loc,
                                "expected ')' after arguments list".to_string(),
                            ))
                        }
                        _ => unreachable!(),
                    };

                    lhs = Expression::FuncCall(loc.clone(), Box::new(lhs), args);
                } else if op == Operator::RBracket {
                    self.advance();
                    let inner = self.expression(0)?;
                    lhs = match self.get_without_consuming() {
                        Some((loc, Token::LBracket)) => {
                            self.advance();
                            Expression::Subscript(loc, Box::new(lhs), Box::new(inner))
                        }
                        Some((loc, _)) => {
                            return Err(Error::SyntaxError(
                                loc,
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
            (_, Token::Ident(ident)) => ident,
            (loc, _) => {
                return Err(Error::SyntaxError(
                    loc,
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
        while !self.check_current(&Token::LBrace) {
            let stmt = self.expression(0)?;
            if !self.check_current(&Token::Semicolon) {
                self.advance();
                return Err(Error::SyntaxError(
                    self.get_without_consuming().unwrap().0,
                    "expected ';' after statement".to_string(),
                ));
            }
            stmts.push(stmt);
            self.advance();
        }
        match self.get() {
            (loc, Token::LBrace) => Ok(Expression::Block(loc, stmts)),
            (loc, _) => Err(Error::SyntaxError(
                loc,
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
            (_, Token::Ident(name)) => Some(name),
            (_, Token::Op(Operator::RParen)) => None,
            (loc, _) => {
                return Err(Error::SyntaxError(
                    loc,
                    "expected identifier or '(' after 'fnc' keyword".to_string(),
                ))
            }
        };
        if name.is_some() {
            match self.get() {
                (_, Token::Op(Operator::RParen)) => {
                    self.advance();
                }
                (loc, _) => {
                    return Err(Error::SyntaxError(
                        loc,
                        "expected '(' after function name".to_string(),
                    ))
                }
            };
        }
        let mut args: Vec<ArgHandler> = Vec::new();
        if !self.check_current(&Token::LParen) {
            loop {
                match self.get_without_consuming() {
                    Some((_, Token::Ident(ident))) => {
                        self.advance();
                        if matches!(
                            self.get_without_consuming(),
                            Some((_, Token::Op(Operator::Assign)))
                        ) {
                            let value = match self.advance() {
                                (_, Token::Op(Operator::Assign)) => Some(self.expression(0)?),
                                _ => unreachable!(),
                            };
                            args.push(ArgHandler {
                                name: Some(ident),
                                value,
                            });
                        } else {
                            args.push(ArgHandler {
                                name: Some(ident),
                                value: None,
                            })
                        }
                    }
                    Some((loc, _)) => {
                        return Err(Error::SyntaxError(
                            loc,
                            "expected identifier in function argument".to_string(),
                        ));
                    }
                    _ => unreachable!(),
                };
                if !self.check_current(&Token::Comma) {
                    break;
                }
                self.advance();
            }
        }
        match self.get_without_consuming() {
            Some((_, Token::LParen)) => self.advance(),
            Some((loc, _)) => {
                return Err(Error::SyntaxError(
                    loc,
                    "expected ')' after arguments list".to_string(),
                ))
            }
            _ => unreachable!(),
        };

        let body = match self.advance() {
            (_, Token::RBrace) => self.parse_block_stmt()?,
            (_, Token::Arrow) => self.expression(0)?,
            (loc, _) => {
                return Err(Error::SyntaxError(
                    loc,
                    "expected '{' or '->' after function declaration".to_string(),
                ));
            }
        };
        Ok(Expression::FuncDef(loc, name, args, Box::new(body)))
    }

    fn parse_for(&mut self, loc: SourceLocation) -> error::Result<Expression> {
        let ident = match self.advance() {
            (_, Token::Ident(s)) => s,
            (loc, _) => return Err(Error::SyntaxError(loc, "expected identifier".to_string())),
        };
        match self.advance() {
            (_, Token::In) => (),
            (loc, _) => return Err(Error::SyntaxError(loc, "expected keyword 'in'".to_string())),
        };
        let iterable = self.expression(0)?;
        let body = match self.advance() {
            (_, Token::RBrace) => self.parse_block_stmt()?,
            (loc, _) => {
                return Err(Error::SyntaxError(
                    loc,
                    "expected '{' after for statement".to_string(),
                ))
            }
        };
        Ok(Expression::ForStmt(
            loc,
            Box::new(InFor { ident, iterable }),
            Box::new(body),
        ))
    }

    pub fn parse(&mut self) -> error::Result<Vec<Expression>> {
        let mut exprs = vec![];
        while !self.check_current(&Token::End) {
            let expr = self.expression(0)?;
            if !self.check_current(&Token::Semicolon) {
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
