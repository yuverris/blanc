use crate::parser::{ArgHandler, Expression};
use crate::utils::FloatExt;
use std::cmp::Ordering;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Rem, Shl, Shr, Sub};
use std::{convert::TryFrom, fmt, rc::Rc};

/// Enum for handling objects
///
/// # Example
///
/// ```rust
/// let mut value = Value::number(5.0);
/// println!("{}", value.to_string());
/// value = Value::Bool(true);
/// println!("{}", value.to_string());
/// ```
#[derive(Clone)]
pub enum Value {
    /// for representing numeric values
    Number(i128),
    /// for representing floating point values
    Float(f64),
    /// for representing boolean values
    Bool(bool),
    /// for handeling strings
    String(String),
    /// for handeling characters
    Char(char),
    /// for representing binded functions
    Func(FunctionType, Option<Box<Value>>),
    /// for representing user defined functions
    UserFunc {
        params: Vec<ArgHandler>,
        body: Expression,
    },
    /// for representing arrays
    Array(Vec<Self>),
    Null,
    Void,
    Ref(*mut Value),
}

pub type FunctionType = Rc<dyn Fn(&[Value]) -> Result<Value, String>>;

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Float(n), Value::Float(u)) => n.approx_eq(*u),
            (Value::Number(n), Value::Number(u)) => n == u,
            (Value::Bool(n), Value::Bool(u)) => n == u,
            (Value::Null, Value::Null) => true,
            _ => false,
        }
    }
}

impl FloatExt for f64 {
    fn approx_eq(self, other: Self) -> bool {
        (self - other).abs() < f64::EPSILON
    }

    fn checked_add(self, other: Self) -> Option<Self> {
        let res = self + other;
        if res.is_infinite() || res.approx_eq(Self::MAX) || res.approx_eq(Self::MIN) {
            None
        } else {
            Some(res)
        }
    }

    fn checked_sub(self, other: Self) -> Option<Self> {
        let res = self - other;
        if res.is_infinite() || res.approx_eq(f64::MAX) || res.approx_eq(Self::MIN) {
            None
        } else {
            Some(res)
        }
    }

    fn checked_mul(self, other: Self) -> Option<Self> {
        let res = self * other;
        if res.is_infinite() {
            None
        } else {
            Some(res)
        }
    }

    fn checked_div(self, other: Self) -> Option<Self> {
        let res = self / other;
        if res.is_nan() {
            None
        } else {
            Some(res)
        }
    }

    fn checked_rem(self, other: Self) -> Option<Self> {
        let res = self % other;
        if res.is_nan() {
            None
        } else {
            Some(res)
        }
    }
}

impl Value {
    pub fn get_type(&self) -> &'static str {
        match &self {
            Value::Float(_) => "float",
            Value::Number(_) => "number",
            Value::String(_) => "string",
            Value::Char(_) => "char",
            Value::Array(_) => "array",
            Value::Bool(_) => "bool",
            Value::Func(..) => "function",
            Value::Null => "null",
            Value::UserFunc { .. } => "function",
            Value::Void => "void",
            Value::Ref(inner) => unsafe { inner.as_ref().unwrap().get_type() },
        }
    }

    /// reads the inner type of a Reference to avoid reading destroyed values, return self if self
    /// isn't a reference
    pub fn read(self) -> Result<Value, &'static str> {
        match self {
            Value::Ref(ptr) => {
                if ptr.is_null() {
                    Err("attempt to read a reference to a destoryed value")
                } else {
                    unsafe { Ok((*ptr).clone()) }
                }
            }
            value => Ok(value),
        }
    }

    pub fn set_ref(&mut self, value: Value) -> Result<(), &'static str> {
        if let Value::Ref(ptr) = *self {
            if ptr.is_null() {
                return Err("attempt to read a reference to a destoryed value");
            } else {
                unsafe {
                    *ptr = value;
                }
            }
        }
        Ok(())
    }
}

impl Add for Value {
    type Output = Result<Value, String>;

    fn add(self, value: Self) -> Self::Output {
        let (type1, type2) = (self.get_type(), value.get_type());

        match (self, value) {
            (Value::Number(n), Value::Number(u)) => {
                Ok(Value::Number(n.checked_add(u).ok_or_else(|| {
                    "add operation results in overflow".to_string()
                })?))
            }

            (Value::Float(n), Value::Float(u)) => {
                Ok(Value::Float(n.checked_add(u).ok_or_else(|| {
                    "add operation results in overflow".to_string()
                })?))
            }

            (Value::String(s1), Value::String(s2)) => Ok(Value::String(s1 + &s2)),

            _ => Err(format!("invalid types for '+': {} and {}", type1, type2)),
        }
    }
}
impl Sub for Value {
    type Output = Result<Value, String>;

    fn sub(self, value: Self) -> Self::Output {
        let (type1, type2) = (self.get_type(), value.get_type());

        match (self, value) {
            (Value::Number(n), Value::Number(u)) => {
                Ok(Value::Number(n.checked_sub(u).ok_or_else(|| {
                    "sub operation results in overflow".to_string()
                })?))
            }

            (Value::Float(n), Value::Float(u)) => {
                Ok(Value::Float(n.checked_sub(u).ok_or_else(|| {
                    "sub operation results in overflow".to_string()
                })?))
            }

            _ => Err(format!("invalid types for '-': {} and {}", type1, type2)),
        }
    }
}

impl Mul for Value {
    type Output = Result<Value, String>;

    fn mul(self, value: Self) -> Self::Output {
        let (type1, type2) = (self.get_type(), value.get_type());

        match (self, value) {
            (Value::Number(n), Value::Number(u)) => {
                Ok(Value::Number(n.checked_mul(u).ok_or_else(|| {
                    "multiply operation results in overflow".to_string()
                })?))
            }

            (Value::Float(n), Value::Float(u)) => {
                Ok(Value::Float(n.checked_mul(u).ok_or_else(|| {
                    "multiply operation results in overflow".to_string()
                })?))
            }

            (Value::Char(c), Value::Number(n)) => {
                if n <= 0 {
                    Err("cannot multiply be negative or 0 number".to_string())
                } else {
                    Ok(Value::String(c.to_string().repeat(n as usize)))
                }
            }

            _ => Err(format!("invalid types for '*': {} and {}", type1, type2)),
        }
    }
}

impl Div for Value {
    type Output = Result<Value, String>;

    fn div(self, value: Self) -> Self::Output {
        let (type1, type2) = (self.get_type(), value.get_type());

        match (self, value) {
            (Value::Number(n), Value::Number(u)) => {
                Ok(Value::Number(n.checked_div(u).ok_or_else(|| {
                    "div operation results in overflow".to_string()
                })?))
            }

            (Value::Float(n), Value::Float(u)) => {
                Ok(Value::Float(n.checked_div(u).ok_or_else(|| {
                    "division operation results in overflow".to_string()
                })?))
            }

            _ => Err(format!("invalid types for '/': {} and {}", type1, type2)),
        }
    }
}

impl Rem for Value {
    type Output = Result<Value, String>;

    fn rem(self, value: Self) -> Self::Output {
        let (type1, type2) = (self.get_type(), value.get_type());

        match (self, value) {
            (Value::Number(n), Value::Number(u)) => {
                Ok(Value::Number(n.checked_rem(u).ok_or_else(|| {
                    "remainder operation results in overflow".to_string()
                })?))
            }

            (Value::Float(n), Value::Float(u)) => {
                Ok(Value::Float(n.checked_rem(u).ok_or_else(|| {
                    "remainder operation results in overflow".to_string()
                })?))
            }

            _ => Err(format!("invalid types for '%': {} and {}", type1, type2)),
        }
    }
}

impl BitOr for Value {
    type Output = Result<Value, String>;

    fn bitor(self, value: Self) -> Self::Output {
        let (type1, type2) = (self.get_type(), value.get_type());

        match (self, value) {
            (Value::Number(n), Value::Number(u)) => Ok(Value::Number(n | u)),

            _ => Err(format!("invalid types for '|': {} and {}", type1, type2)),
        }
    }
}

impl BitXor for Value {
    type Output = Result<Value, String>;

    fn bitxor(self, value: Self) -> Self::Output {
        let (type1, type2) = (self.get_type(), value.get_type());

        match (self, value) {
            (Value::Number(n), Value::Number(u)) => Ok(Value::Number(n ^ u)),

            _ => Err(format!("invalid types for '^': {} and {}", type1, type2)),
        }
    }
}

impl BitAnd for Value {
    type Output = Result<Value, String>;

    fn bitand(self, value: Self) -> Self::Output {
        let (type1, type2) = (self.get_type(), value.get_type());

        match (self, value) {
            (Value::Number(n), Value::Number(u)) => Ok(Value::Number(n & u)),

            _ => Err(format!("invalid types for '&': {} and {}", type1, type2)),
        }
    }
}

impl Shr for Value {
    type Output = Result<Value, String>;

    fn shr(self, value: Self) -> Self::Output {
        let (type1, type2) = (self.get_type(), value.get_type());

        match (self, value) {
            (Value::Number(n), Value::Number(u)) => {
                let u32_repr: u32 = u32::try_from(u)
                    .map_err(|_| "invalid integer value of shift operation".to_string())?;
                Ok(Value::Number(n.checked_shr(u32_repr).ok_or_else(|| {
                    "right shift operation results in overflow".to_string()
                })?))
            }

            _ => Err(format!("invalid types for '>>': {} and {}", type1, type2)),
        }
    }
}

impl Shl for Value {
    type Output = Result<Value, String>;

    fn shl(self, value: Self) -> Self::Output {
        let (type1, type2) = (self.get_type(), value.get_type());

        match (self, value) {
            (Value::Number(n), Value::Number(u)) => {
                let u32_repr: u32 = u32::try_from(u)
                    .map_err(|_| "invalid integer value of shift operation".to_string())?;
                Ok(Value::Number(n.checked_shl(u32_repr).ok_or_else(|| {
                    "left shift operation results in overflow".to_string()
                })?))
            }

            _ => Err(format!("invalid types for '<<': {} and {}", type1, type2)),
        }
    }
}

impl Neg for Value {
    type Output = Result<Value, String>;

    fn neg(self) -> Self::Output {
        let type1 = self.get_type();
        match self {
            Value::Number(n) => Ok(Value::Number(-n)),

            Value::Float(n) => Ok(Value::Float(-n)),

            _ => Err(format!("invalid type for '-': {}", type1)),
        }
    }
}

impl Not for Value {
    type Output = Result<Value, String>;

    fn not(self) -> Self::Output {
        let type1 = self.get_type();
        match self {
            Value::Bool(n) => Ok(Value::Bool(!n)),

            _ => Err(format!("invalid type for '!': {}  ", type1)),
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Value::Number(n), Value::Number(u)) => Some(n.cmp(u)),

            (Value::Bool(n), Value::Bool(u)) => Some(n.cmp(u)),

            (Value::Char(n), Value::Char(u)) => Some(n.cmp(u)),

            (Value::String(s1), Value::String(s2)) => Some(s1.cmp(s2)),

            (Value::Float(n), Value::Float(u)) => {
                if n < u {
                    Some(Ordering::Less)
                } else if n > u {
                    Some(Ordering::Greater)
                } else if n.approx_eq(*u) {
                    Some(Ordering::Equal)
                } else {
                    None
                }
            }

            _ => None,
        }
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Value::Float(n) => write!(fmt, "Float({})", n),
            Value::Number(n) => write!(fmt, "Number({})", n),
            Value::Char(c) => write!(fmt, "Char({})", c),
            Value::String(s) => write!(fmt, "String({})", s),
            Value::Array(a) => write!(fmt, "Array({:?})", a),
            Value::Bool(b) => write!(fmt, "Bool({})", b),
            Value::Null => write!(fmt, "Null"),
            Value::Func(..) => write!(fmt, "Function"),
            Value::UserFunc { .. } => write!(fmt, "Function"),
            Value::Void => write!(fmt, "Void"),
            Value::Ref(inner) => write!(fmt, "Ref({:?})", unsafe { inner.as_ref() }),
        }
    }
}

impl From<f64> for Value {
    fn from(value: f64) -> Self {
        Self::Float(value)
    }
}

impl From<i128> for Value {
    fn from(value: i128) -> Self {
        Self::Number(value)
    }
}

impl From<String> for Value {
    fn from(value: String) -> Self {
        Self::String(value)
    }
}

impl From<&str> for Value {
    fn from(value: &str) -> Self {
        Self::String(value.to_string())
    }
}

impl From<char> for Value {
    fn from(value: char) -> Self {
        Self::Char(value)
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Self::Bool(value)
    }
}

impl From<()> for Value {
    fn from(_: ()) -> Self {
        Self::Void
    }
}

impl<T> From<Vec<T>> for Value
where
    Value: From<T>,
{
    fn from(value: Vec<T>) -> Self {
        Self::Array(value.into_iter().map(Value::from).collect())
    }
}

impl<T: Into<Value>> From<Option<T>> for Value {
    fn from(value: Option<T>) -> Self {
        match value {
            Some(t) => t.into(),
            None => Self::Null,
        }
    }
}

impl TryFrom<Value> for f64 {
    type Error = String;
    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Float(n) => Ok(n),
            _ => Err(format!(
                "expected type 'float', found '{}'",
                value.get_type()
            )),
        }
    }
}

impl TryFrom<Value> for i128 {
    type Error = String;
    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Number(n) => Ok(n),
            _ => Err(format!(
                "expected type 'number', found '{}'",
                value.get_type()
            )),
        }
    }
}

impl TryFrom<Value> for String {
    type Error = String;
    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match &value {
            Value::String(s) => Ok(s.clone()),
            _ => Err(format!(
                "expected type 'string', found '{}'",
                value.get_type()
            )),
        }
    }
}

impl TryFrom<Value> for bool {
    type Error = String;
    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Bool(b) => Ok(b),
            _ => Err(format!(
                "expected type 'bool', found '{}'",
                value.get_type()
            )),
        }
    }
}

impl ToString for Value {
    fn to_string(&self) -> String {
        match self {
            Value::Float(n) => n.to_string(),
            Value::String(s) => s.clone(),
            Value::Char(c) => c.to_string(),
            Value::Array(elements) => {
                let mut res = String::from('[');
                for (index, elm) in elements.iter().enumerate() {
                    if let Value::String(s) = elm {
                        res.push_str(format!("\"{}\"", s).as_str());
                    } else if let Value::Char(c) = elm {
                        res.push_str(format!("'{}'", c).as_str());
                    } else {
                        res.push_str(elm.to_string().as_str());
                    }
                    if index != elements.len() - 1 {
                        res.push_str(", ");
                    }
                }
                res.push(']');
                res
            }
            Value::Number(n) => n.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Null => "null".into(),
            Value::Func(..) => "function".into(),
            Value::UserFunc { .. } => "function".into(),
            Value::Void => '\0'.into(),
            r @ Value::Ref(_) => r.clone().read().unwrap().to_string(),
        }
    }
}
