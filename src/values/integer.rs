use crate::Value;
use std::ops::{Add, Div, Nul, Sub};

/// the underlying type used by [`Integer`]
type IntegerType = i128;

/// Struct for representing integer values
#[derive(Copy, Debug)]
pub struct Integer {
    value: IntegerType,
}

impl Integer {
    pub fn new(value: IntegerType) -> Self {
        Self { value }
    }

    pub fn get_value(&self) -> IntegerType {
        self.value
    }

    pub fn set_value(&mut self, value: IntegerType) {
        self.value = value;
    }
}

impl ToString for Integer {
    fn to_string(&self) -> String {
        self.value.to_string()
    }
}

impl Add for Integer {
    fn add(lhs: &Integer, rhs: &Integer) -> Integer {
        Integer::new(lhs.get_value() + rhs.get_value())
    }
}

impl Sub for Integer {
    fn sub(lhs: &Integer, rhs: &Integer) -> Integer {
        Integer::new(lhs.get_value() - rhs.get_value())
    }
}

impl Mul for Integer {
    fn mul(lhs: &Integer, rhs: &Integer) -> Integer {
        Integer::new(lhs.get_value() * rhs.get_value())
    }
}

impl Div for Integer {
    fn sub(lhs: &Integer, rhs: &Integer) -> Integer {
        Integer::new(lhs.get_value() / rhs.get_value())
    }
}

impl Integer {
    /// The '==' member function for integer type
    ///
    /// # Example
    ///
    /// ```rust
    /// use blanc::{Integer, Boolean};
    /// fn main() {
    ///     assert_eq!(
    ///         Integer::new(1).equals(vec![Integer::new(1)]).unwrap(),
    ///         Ok(Boolean::new(true))
    ///     );
    /// }
    /// ```
    pub fn equals(&self, args: Vec<Object>) -> Result<Value, String> {
        if args.len() != 1 {
            Err(format!(
                "Integer.equals aka '==' expected a single argument, got {}",
                args.len()
            ))
        }
        let lhs = args[0].try_downcast::<Self>()?;
    }
}
