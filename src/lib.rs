// Copyright 2016 Matthew D. Michelotti
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! This crate contains floating point types that panic if they are set
//! to an illegal value, such as NaN.
//!
//! The name "Noisy Float" comes from
//! the terms "quiet NaN" and "signaling NaN"; "signaling" was too long
//! to put in a struct/crate name, so "noisy" is used instead, being the opposite
//! of "quiet."
//!
//! The standard types defined in `noisy_float::types` follow the principle
//! demonstrated by Rust's handling of integer overflow:
//! a bad arithmetic operation is considered an error,
//! but it is too costly to check everywhere in optimized builds.
//! For each floating point number that is created, a `debug_assert!` invocation is used
//! to check if it is valid or not.
//! This way, there are guarantees when developing code that floating point
//! numbers have valid values,
//! but during a release run there is *no overhead* for using these floating
//! point types compared to using `f32` or `f64` directly.
//!
//! This crate makes use of the floating point and number traits in the
//! popular `num_traits` crate.
//!
//! #Examples
//! An example using the `R64` type, which corresponds to *finite* `f64` values.
//!
//! ```
//! use noisy_float::prelude::*;
//!
//! fn geometric_mean(a: R64, b: R64) -> R64 {
//!     (a * b).sqrt() //used just like regular floating-point numbers
//! }
//! 
//! println!("geometric_mean(10.0, 20.0) = {}", geometric_mean(r64(10.0), r64(20.0)));
//! //prints 14.142...
//! ```
//!
//! An example using the `N32` type, which corresponds to *non-NaN* `f32` values.
//! The float types in this crate are able to implement `Eq` and `Ord` properly,
//! since NaN is not allowed.
//!
//! ```
//! use noisy_float::prelude::*;
//!
//! let values = vec![n32(3.0), n32(-1.5), n32(71.3), N32::infinity()];
//! assert!(values.iter().cloned().min() == Some(n32(-1.5)));
//! assert!(values.iter().cloned().max() == Some(N32::infinity()));
//! ```

extern crate num_traits;

pub mod checkers;
pub mod types;
mod float_impl;

/// Prelude for the `noisy_float` crate.
///
/// This includes all of the types defined in the `noisy_float::types` module,
/// as well as a re-export of the `Float` trait from the `num_traits` crate.
/// It is important to have this re-export here, because it allows the user
/// to access common floating point methods like `abs()`, `sqrt()`, etc.
pub mod prelude {
    pub use types::*;
    
    pub use num_traits::Float;
}

use std::marker::PhantomData;
use std::fmt;
use num_traits::Float;

/// Trait for checking whether a floating point number is *valid*.
///
/// The implementation defines its own criteria for what constitutes a *valid* value.
pub trait FloatChecker<F> {
    /// Returns `true` if (and only if) the given floating point number is *valid*
    /// according to this checker's criteria.
    ///
    /// The only hard requirement is that NaN *must* be considered *invalid*
    /// for all implementations of `FloatChecker`.
    fn check(value: F) -> bool;
    
    /// A function that may panic if the floating point number is *invalid*.
    ///
    /// Should either call `assert!(check(value), ...)` or `debug_assert!(check(value), ...)`.
    fn assert(value: F);
}

/// A floating point number with a restricted set of legal values.
///
/// Typical users will not need to access this struct directly, but
/// can instead use the type aliases found in the module `noisy_float::types`.
/// However, this struct together with a `FloatChecker` implementation can be used
/// to define custom behavior.
///
/// The underlying float type is `F`, usually `f32` or `f64`.
/// Valid values for the float are determined by the float checker `C`.
/// If an invalid value would ever be returned from a method on this type,
/// the method will panic instead, using either `assert!` or `debug_assert!`
/// as defined by the float checker.
/// The exception to this rule is for methods that return an `Option` containing
/// a `NoisyFloat`, in which case the result would be `None` if the value is invalid.
pub struct NoisyFloat<F: Float, C: FloatChecker<F>> {
    value: F,
    checker: PhantomData<C>
}

impl<F: Float, C: FloatChecker<F>> NoisyFloat<F, C> {
    /// Constructs a `NoisyFloat` with the given value.
    ///
    /// Uses the `FloatChecker` to assert that the value is valid.
    #[inline]
    pub fn new(value: F) -> Self {
        C::assert(value);
        Self::unchecked_new(value)
    }
    
    #[inline]
    fn unchecked_new(value: F) -> Self {
        NoisyFloat {
            value: value,
            checker: PhantomData
        }
    }
    
    /// Tries to construct a `NoisyFloat` with the given value.
    ///
    /// Returns `None` if the value is invalid.
    #[inline]
    pub fn try_new(value: F) -> Option<Self> {
        if C::check(value) {
            Some(NoisyFloat {
                value: value,
                checker: PhantomData
            })
        } else {
            None
        }
    }
    
    /// Constructs a `NoisyFloat` with the given `f32` value.
    ///
    /// May panic not only by the `FloatChecker` but also
    /// by unwrapping the result of a `NumCast` invocation for type `F`,
    /// although the later should not occur in normal situations.
    #[inline]
    pub fn from_f32(value: f32) -> Self {
        Self::new(F::from(value).unwrap())
    }
    
    /// Constructs a `NoisyFloat` with the given `f64` value.
    ///
    /// May panic not only by the `FloatChecker` but also
    /// by unwrapping the result of a `NumCast` invocation for type `F`,
    /// although the later should not occur in normal situations.
    #[inline]
    pub fn from_f64(value: f64) -> Self {
        Self::new(F::from(value).unwrap())
    }

    /// Returns the underlying float value.
    #[inline]
    pub fn raw(self) -> F {
        self.value
    }
}

/// Note: due to complications with Rust's type system, cannot implement `Into` generically like
/// `impl<F: Float, C: FloatChecker<F>> Into<F> for NoisyFloat<F, C>`.
impl<C: FloatChecker<f32>> Into<f32> for NoisyFloat<f32, C> {
    #[inline]
    fn into(self) -> f32 {
        self.value
    }
}

/// Note: due to complications with Rust's type system, cannot implement `Into` generically like
/// `impl<F: Float, C: FloatChecker<F>> Into<F> for NoisyFloat<F, C>`.
impl<C: FloatChecker<f64>> Into<f64> for NoisyFloat<f64, C> {
    #[inline]
    fn into(self) -> f64 {
        self.value
    }
}

impl<F: Float + fmt::Debug, C: FloatChecker<F>> fmt::Debug for NoisyFloat<F, C> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        fmt::Debug::fmt(&self.value, f)
    }
}

impl<F: Float + fmt::Display, C: FloatChecker<F>> fmt::Display for NoisyFloat<F, C> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        fmt::Display::fmt(&self.value, f)
    }
}

impl<F: Float + fmt::LowerExp, C: FloatChecker<F>> fmt::LowerExp for NoisyFloat<F, C> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        fmt::LowerExp::fmt(&self.value, f)
    }
}

impl<F: Float + fmt::UpperExp, C: FloatChecker<F>> fmt::UpperExp for NoisyFloat<F, C> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        fmt::UpperExp::fmt(&self.value, f)
    }
}


#[cfg(test)]
mod tests {
    use prelude::*;
    use std::f32;
    use std::f64::{self, consts};

    #[test]
    fn smoke_test() {
        assert!(n64(1.0) + n64(2.0) == n64(3.0));
        assert!(n64(3.0) != n64(2.9));
        assert!(r64(1.0) < r64(2.0));
        let mut value = n64(18.0);
        value %= n64(5.0);
        assert!(-value == n64(-3.0));
        assert!(r64(1.0).exp() == r64(consts::E));
        assert!((N64::try_new(1.0).unwrap() / N64::infinity()) == n64(0.0));
        assert!(N64::from_f32(f32::INFINITY) == N64::from_f64(f64::INFINITY));
        assert!(R64::try_new(f64::NEG_INFINITY) == None);
        assert!(N64::try_new(f64::NAN) == None);
        assert!(R64::try_new(f64::NAN) == None);
    }
    
    #[test]
    #[should_panic]
    fn n64_nan() {
        n64(0.0) / n64(0.0);
    }
    
    #[test]
    #[should_panic]
    fn r64_nan() {
        r64(0.0) / r64(0.0);
    }
    
    #[test]
    #[should_panic]
    fn r64_infinity() {
        r64(1.0) / r64(0.0);
    }
}
