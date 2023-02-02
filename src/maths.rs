use crate::variant::{Float, Variant};
use anyhow::{anyhow, Result};
use std::f64;

macro_rules! impl_unary_math_functions {
    ($($func:ident),+) => {
        impl Variant {
            fn unary_math_function_wrapper(self, function: fn(f64) -> f64, name: &str) -> Result<Self>{
                match self {
                    Variant::Float(i) => Ok(Variant::Float(function(i))),
                    Variant::Int(i) => Ok(Variant::Float(function(i as Float))),
                    _ => Err(anyhow!("Cannot calculate {name} of {self:?}"))
                }
            }
            $(
                pub fn $func(self) -> Result<Self> {
                    self.unary_math_function_wrapper(f64::$func, stringify!($func))
                }
            )+
        }
    };
}

impl_unary_math_functions!(abs, acos, asin, atan, ceil, cos, exp, floor, ln, round, sin, sqrt, tan);

impl Variant {
    pub const PI: Variant = Variant::Float(f64::consts::PI);
    pub const E: Variant = Variant::Float(f64::consts::E);

    pub fn log(self, base: Variant) -> Result<Self> {
        let result = match (self, base) {
            (Variant::Int(a), Variant::Int(b)) => Variant::Float((a as Float).log(b as Float)),
            (Variant::Float(a), Variant::Float(b)) => Variant::Float(a.log(b)),
            (Variant::Int(a), Variant::Float(b)) => Variant::Float((a as Float).log(b)),
            (Variant::Float(a), Variant::Int(b)) => Variant::Float(a.log(b as Float)),
            (value, base) => {
                return Err(anyhow!(
                    "Cannot calculate log of {value:?} with base {base:?}"
                ))
            }
        };
        Ok(result)
    }

    pub fn pow(&self, other: &Variant) -> Result<Variant> {
        let result = match (self, other) {
            (Variant::Int(a), Variant::Int(b)) => Variant::Float((*a as Float).powf(*b as Float)),
            (Variant::Float(a), Variant::Float(b)) => Variant::Float(a.powf(*b)),
            (Variant::Int(a), Variant::Float(b)) => Variant::Float((*a as Float).powf(*b)),
            (Variant::Float(a), Variant::Int(b)) => Variant::Float(a.powf(*b as Float)),
            _ => return Err(anyhow!("Cannot elevate {self:?} to {other:?}")),
        };
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ln() {
        assert_eq!(Variant::E.ln().unwrap(), Variant::Float(1.0));
    }
    #[test]
    fn test_exp() {
        assert_eq!(Variant::Int(1).exp().unwrap(), Variant::E);
    }
}
