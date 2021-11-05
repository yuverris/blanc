//! utilities for easier integration

use std::fmt::Debug;

/// Extensions to floats
pub trait FloatExt
where
    Self: Sized,
{
    fn approx_eq(self, other: Self) -> bool;
    fn approx_not_eq(self, other: Self) -> bool {
        !self.approx_eq(other)
    }
    fn checked_add(self, other: Self) -> Option<Self>;
    fn checked_mul(self, other: Self) -> Option<Self>;
    fn checked_div(self, other: Self) -> Option<Self>;
    fn checked_sub(self, other: Self) -> Option<Self>;
    fn checked_rem(self, other: Self) -> Option<Self>;
}

/// Enum for handling Ok, Err and Return values
#[derive(Debug, Clone)]
pub enum RResult<T, E, U> {
    Ok(T),
    Err(E),
    Return(U),
}

impl<T, E, U> RResult<T, E, U> {
    pub fn unwrap(self) -> T
    where
        E: Debug,
        U: Debug,
    {
        match self {
            Self::Ok(value) => value,
            Self::Err(err) => panic!("unwrap called on an Err(E) value: {:?}", err),
            Self::Return(value) => panic!("unwrap called on an Return(U) value: {:?}", value),
        }
    }

    pub fn unwrap_err(self) -> E
    where
        T: Debug,
        U: Debug,
    {
        match self {
            Self::Ok(value) => panic!("unwrap_err called on an Ok(T) value: {:?}", value),
            Self::Err(err) => err,
            Self::Return(value) => panic!("unwrap_err called on an Return(U) value: {:?}", value),
        }
    }

    pub fn unwrap_return(self) -> U
    where
        T: Debug,
        E: Debug,
    {
        match self {
            Self::Ok(value) => panic!("unwrap_return called on an Ok(T) value: {:?}", value),
            Self::Err(err) => panic!("unwrap_return called on an Err(E) value: {:?}", err),
            Self::Return(value) => value,
        }
    }

    pub fn expect(self, msg: &str) -> T
    where
        E: Debug,
        U: Debug,
    {
        match self {
            Self::Ok(value) => value,
            Self::Err(err) => panic!("{}: {:?}", msg, err),
            Self::Return(value) => panic!("{}: {:?}", msg, value),
        }
    }

    pub fn expect_return(self, msg: &str) -> U
    where
        T: Debug,
        E: Debug,
    {
        match self {
            Self::Ok(value) => panic!("{}: {:?}", msg, value),
            Self::Err(err) => panic!("{}: {:?}", msg, err),
            Self::Return(value) => value,
        }
    }

    pub fn is_ok(&self) -> bool {
        matches!(*self, Self::Ok(_))
    }

    pub fn is_return(&self) -> bool {
        matches!(*self, Self::Return(_))
    }

    pub fn is_err(&self) -> bool {
        matches!(*self, Self::Err(_))
    }

    pub fn map<J, F: FnOnce(T) -> J>(self, function: F) -> RResult<J, E, U> {
        match self {
            Self::Ok(v) => RResult::Ok(function(v)),
            Self::Err(err) => RResult::Err(err),
            Self::Return(v) => RResult::Return(v),
        }
    }

    pub fn map_err<D, F: FnOnce(E) -> D>(self, function: F) -> RResult<T, D, U> {
        match self {
            Self::Ok(v) => RResult::Ok(v),
            Self::Err(err) => RResult::Err(function(err)),
            Self::Return(v) => RResult::Return(v),
        }
    }

    pub fn map_return<I, F: FnOnce(U) -> I>(self, function: F) -> RResult<T, E, I> {
        match self {
            Self::Ok(v) => RResult::Ok(v),
            Self::Err(err) => RResult::Err(err),
            Self::Return(v) => RResult::Return(function(v)),
        }
    }
}

#[macro_export]
macro_rules! try_return {
    ($expr:expr) => {
        match $expr {
            RResult::Ok(v) => v,
            err @ RResult::Err(_) => return err,
            ret @ RResult::Return(_) => return ret,
        }
    };
}
#[macro_export]
macro_rules! try_err {
    ($expr:expr) => {
        match $expr {
            RResult::Ok(v) => v,
            err @ RResult::Err(_) => return err,
            RResult::Return(v) => v,
        }
    };
}

pub enum Either<T, U> {
    Right(T),
    Left(U),
}

/*impl<T, U> Either<T, U> {
    pub fn is_right(&self) -> bool {
        matches!(self, Self::Right(_))
    }

    pub fn is_left(&self) -> bool {
        matches!(self, Self::Left(_))
    }

    pub fn map_right<F, E>(&self, func: F) -> Either<E, U>
    where
        F: Fn(T) -> E,
    {
        if self.is_right() {
            Self::Right(func(self.unwrap_right()))
        } else {
            self
        }
    }

    pub fn map_left<F, I>(&self, func: F) -> Either<T, U>
    where
        F: Fn(U) -> I,
    {
        if self.is_left() {
            Self::Left(func(self.unwrap_left()))
        } else {
            self
        }
    }
}*/
