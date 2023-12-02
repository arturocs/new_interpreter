use crate::{
    memory::Memory,
    variant::{Float, Variant},
};
use anyhow::{bail, Result};
use std::f64;

macro_rules! impl_unary_math_functions {
    ($($func:ident),+) => {
        impl Variant {
            fn unary_math_function_wrapper(&self, function: fn(f64) -> f64, name: &str) -> Result<Self>{
                match self {
                    &Variant::Float(i) => Ok(Variant::Float(function(i))),
                    &Variant::Int(i) => Ok(Variant::Float(function(i as Float))),
                    _ => bail!("Cannot calculate {name} of {self:?}")
                }
            }
            $(
                pub fn $func(&self) -> Result<Self> {
                    self.unary_math_function_wrapper(f64::$func, stringify!($func))
                }
            )+
        }
    };
}

impl_unary_math_functions!(abs, acos, asin, atan, ceil, cos, exp, floor, ln, round, sin, sqrt, tan, trunc);

impl Variant {
    pub const PI: Variant = Variant::Float(f64::consts::PI);
    pub const E: Variant = Variant::Float(f64::consts::E);

    pub fn log(&self, base: &Variant) -> Result<Self> {
        let result = match (self, base) {
            (&Variant::Int(a), &Variant::Int(b)) => Variant::Float((a as Float).log(b as Float)),
            (&Variant::Float(a), &Variant::Float(b)) => Variant::Float(a.log(b)),
            (&Variant::Int(a), &Variant::Float(b)) => Variant::Float((a as Float).log(b)),
            (&Variant::Float(a), &Variant::Int(b)) => Variant::Float(a.log(b as Float)),
            (value, base) => {
                bail!("Cannot calculate log of {value:?} with base {base:?}")
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
            _ => bail!("Cannot elevate {self:?} to {other:?}"),
        };
        Ok(result)
    }
}

fn wrap_unary_math_function(
    f: fn(&Variant) -> Result<Variant>,
) -> impl Fn(&[Variant], &mut Memory) -> Variant {
    move |args: &[Variant], _: &mut Memory| {
        if args.len() != 1 {
            Variant::error(format!("Expected 1 argument, got {}", args.len()));
        }
        f(&args[0]).unwrap_or_else(|e| Variant::error(e))
    }
}

fn wrap_binary_math_function(
    f: fn(&Variant, &Variant) -> Result<Variant>,
) -> impl Fn(&[Variant], &mut Memory) -> Variant {
    move |args: &[Variant], _: &mut Memory| {
        if args.len() != 2 {
            Variant::error(format!("Expected 2 arguments, got {}", args.len()));
        }
        f(&args[0], &args[1]).unwrap_or_else(|e| Variant::error(e))
    }
}

pub fn export_math_lib() -> Variant {
    let unary_functions = [
        ("abs", Variant::abs as fn(&Variant) -> Result<Variant>),
        ("acos", Variant::acos),
        ("asin", Variant::asin),
        ("atan", Variant::atan),
        ("ceil", Variant::ceil),
        ("cos", Variant::cos),
        ("exp", Variant::exp),
        ("floor", Variant::floor),
        ("ln", Variant::ln),
        ("round", Variant::round),
        ("sin", Variant::sin),
        ("sqrt", Variant::sqrt),
        ("tan", Variant::tan),
        ("trunc", Variant::trunc)
    ]
    .map(|(name, f)| (name, Variant::native_fn(wrap_unary_math_function(f))));

    let log = Variant::log as fn(&Variant, &Variant) -> Result<Variant>;
    let binary_functions = [("log", log), ("pow", Variant::pow)]
        .map(|(name, f)| (name, Variant::native_fn(wrap_binary_math_function(f))));

    let constants = [("PI", Variant::PI), ("E", Variant::E)];

    Variant::dict(
        &unary_functions
            .into_iter()
            .chain(binary_functions)
            .chain(constants)
            .map(|(name, f)| (Variant::str(name), f))
            .collect::<Vec<_>>(),
    )
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
