use std::{
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    ops::{Add, Div, Mul, Neg, Rem, Shl, Shr, Sub},
};

pub type Int = i64;
pub type Float = f64;
#[derive(Debug, Copy, Clone)]

pub enum Number {
    Float(Float),
    Int(Int),
}

impl Ord for Number {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (&Number::Int(a), Number::Float(b)) => (a as Float).total_cmp(b),
            (&Number::Float(a), &Number::Int(b)) => a.total_cmp(&(b as Float)),
            (&Number::Int(a), Number::Int(b)) => a.cmp(b),
            (&Number::Float(a), Number::Float(b)) => a.total_cmp(b),
        }
    }
}

impl PartialOrd for Number {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Number {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (&Number::Int(a), &Number::Float(b)) => (a as Float) == b,
            (&Number::Float(a), &Number::Int(b)) => a == (b as Float),
            (&Number::Int(a), &Number::Int(b)) => a == b,
            (&Number::Float(a), &Number::Float(b)) => a == b,
        }
    }
}

impl Eq for Number {}

impl fmt::Display for Number {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Number::Float(f) => write!(fmt, "{f}"),
            Number::Int(i) => write!(fmt, "{i}"),
        }
    }
}

impl Hash for Number {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Number::Int(a) => a.hash(state),
            Number::Float(a) => a.to_bits().hash(state),
        };
    }
}

impl Add for Number {
    type Output = Number;
    fn add(self, other: Self) -> Self {
        match (self, other) {
            (Number::Int(a), Number::Int(b)) => Number::Int(a + b),
            (Number::Float(a), Number::Float(b)) => Number::Float(a + b),
            (Number::Int(a), Number::Float(b)) => Number::Float(a as Float + b),
            (Number::Float(a), Number::Int(b)) => Number::Float(a + b as Float),
        }
    }
}

impl Sub for Number {
    type Output = Number;
    fn sub(self, other: Self) -> Self {
        match (self, other) {
            (Number::Int(a), Number::Int(b)) => Number::Int(a - b),
            (Number::Float(a), Number::Float(b)) => Number::Float(a - b),
            (Number::Int(a), Number::Float(b)) => Number::Float(a as Float - b),
            (Number::Float(a), Number::Int(b)) => Number::Float(a - b as Float),
        }
    }
}

impl Mul for Number {
    type Output = Number;
    fn mul(self, other: Self) -> Self {
        match (self, other) {
            (Number::Int(a), Number::Int(b)) => Number::Int(a * b),
            (Number::Float(a), Number::Float(b)) => Number::Float(a * b),
            (Number::Int(a), Number::Float(b)) => Number::Float(a as Float * b),
            (Number::Float(a), Number::Int(b)) => Number::Float(a * b as Float),
        }
    }
}

impl Div for Number {
    type Output = Number;
    fn div(self, other: Self) -> Self {
        match (self, other) {
            (Number::Int(a), Number::Int(b)) => Number::Float(a as Float / b as Float),
            (Number::Float(a), Number::Float(b)) => Number::Float(a / b),
            (Number::Int(a), Number::Float(b)) => Number::Float(a as Float / b),
            (Number::Float(a), Number::Int(b)) => Number::Float(a / b as Float),
        }
    }
}

impl Neg for Number {
    type Output = Number;
    fn neg(self) -> Self {
        match self {
            Number::Int(i) => Number::Int(-i),
            Number::Float(i) => Number::Float(-i),
        }
    }
}
impl Rem for Number {
    type Output = Number;
    fn rem(self, other: Self) -> Self {
        match (self, other) {
            (Number::Int(a), Number::Int(b)) => Number::Int(a % b),
            (Number::Float(a), Number::Float(b)) => Number::Float(a % b),
            (Number::Int(a), Number::Float(b)) => Number::Float(a as Float % b),
            (Number::Float(a), Number::Int(b)) => Number::Float(a % b as Float),
        }
    }
}

impl Shr for Number {
    type Output = Number;
    fn shr(self, other: Self) -> Self {
        match (self, other) {
            (Number::Int(a), Number::Int(b)) => Number::Int(a >> b),
            (Number::Float(a), Number::Float(b)) => Number::Int(a as Int >> b as Int),
            (Number::Int(a), Number::Float(b)) => Number::Int(a >> (b as Int)),
            (Number::Float(a), Number::Int(b)) => Number::Int(a as Int >> b as Int),
        }
    }
}

impl Shl for Number {
    type Output = Number;
    fn shl(self, other: Self) -> Self {
        match (self, other) {
            (Number::Int(a), Number::Int(b)) => Number::Int(a << b),
            (Number::Float(a), Number::Float(b)) => Number::Int((a as Int) << (b as Int)),
            (Number::Int(a), Number::Float(b)) => Number::Int(a << (b as Int)),
            (Number::Float(a), Number::Int(b)) => Number::Int((a as Int) << (b as Int)),
        }
    }
}

impl Number {
    pub fn to_int(self) -> Number {
        match self {
            Number::Float(i) => Number::Int(i as Int),
            Number::Int(_) => self,
        }
    }

    pub fn to_float(self) -> Number {
        match self {
            Number::Int(i) => Number::Float(i as Float),
            Number::Float(_) => self,
        }
    }

    pub fn div_exact(self, other: Self) -> Self {
        match (self, other) {
            (Number::Int(a), Number::Int(b)) => Number::Int(a / b),
            (Number::Float(a), Number::Float(b)) => Number::Int(a as Int / b as Int),
            (Number::Int(a), Number::Float(b)) => Number::Int(a / b as Int),
            (Number::Float(a), Number::Int(b)) => Number::Int(a as Int / b),
        }
    }

    pub fn pow(self, other: Self) -> Self {
        match (self, other) {
            (Number::Int(a), Number::Int(b)) => Number::Float((a as Float).powf(b as Float)),
            (Number::Float(a), Number::Float(b)) => Number::Float(a.powf(b)),
            (Number::Int(a), Number::Float(b)) => Number::Float((a as Float).powf(b)),
            (Number::Float(a), Number::Int(b)) => Number::Float(a.powf(b as Float)),
        }
    }

    pub fn sqrt(self) -> Self {
        match self {
            Number::Float(i) => Number::Float(i.sqrt()),
            Number::Int(i) => Number::Float((i as Float).sqrt()),
        }
    }

    pub fn tan(self) -> Self {
        match self {
            Number::Float(i) => Number::Float(i.tan()),
            Number::Int(i) => Number::Float((i as Float).tan()),
        }
    }

    pub fn cos(self) -> Self {
        match self {
            Number::Float(i) => Number::Float(i.cos()),
            Number::Int(i) => Number::Float((i as Float).cos()),
        }
    }

    pub fn sin(self) -> Self {
        match self {
            Number::Float(i) => Number::Float(i.sin()),
            Number::Int(i) => Number::Float((i as Float).sin()),
        }
    }

    pub fn log(self, base: Number) -> Self {
        match (self, base) {
            (Number::Int(a), Number::Int(b)) => Number::Float((a as Float).log(b as Float)),
            (Number::Float(a), Number::Float(b)) => Number::Float(a.log(b)),
            (Number::Int(a), Number::Float(b)) => Number::Float((a as Float).log(b)),
            (Number::Float(a), Number::Int(b)) => Number::Float(a.log(b as Float)),
        }
    }

    pub fn abs(self) -> Self {
        match self {
            Number::Float(i) => Number::Float(i.abs()),
            Number::Int(i) => Number::Int(i.abs()),
        }
    }

    pub fn round(self) -> Self {
        match self {
            Number::Float(i) => Number::Int(i.round() as Int),
            Number::Int(_) => self,
        }
    }
    pub fn ceil(self) -> Self {
        match self {
            Number::Float(i) => Number::Int(i.ceil() as Int),
            Number::Int(_) => self,
        }
    }
    pub fn floor(self) -> Self {
        self.to_int()
    }
    pub fn into_float(self) -> Float {
        match self {
            Number::Float(i) => i,
            Number::Int(i) => i as f64,
        }
    }

    pub fn into_int(self) -> Int {
        match self {
            Number::Float(i) => i as i64,
            Number::Int(i) => i,
        }
    }

    pub fn is_float(self) -> bool {
        match self {
            Number::Float(_) => true,
            _ => false,
        }
    }

    pub fn is_int(self) -> bool {
        match self {
            Number::Int(_) => true,
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn size_of_number() {
        dbg!(std::mem::size_of::<Number>());
    }
}
