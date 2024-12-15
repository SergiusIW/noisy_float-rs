// Copyright 2016-2021 Matthew D. Michelotti
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
//! This crate makes use of the num, bounded, signed and floating point traits
//! in the popular `num_traits` crate.
//! This crate can be compiled with no_std.
//!
//! # Examples
//! An example using the `R64` type, which corresponds to *finite* `f64` values.
//!
//! ```
//! use noisy_float::prelude::*;
//!
//! fn geometric_mean(a: R64, b: R64) -> R64 {
//!     (a * b).sqrt() //used just like regular floating point numbers
//! }
//!
//! fn mean(a: R64, b: R64) -> R64 {
//!     (a + b) * 0.5 //the RHS of ops can be the underlying float type
//! }
//!
//! println!(
//!     "geometric_mean(10.0, 20.0) = {}",
//!     geometric_mean(r64(10.0), r64(20.0))
//! );
//! //prints 14.142...
//! assert!(mean(r64(10.0), r64(20.0)) == 15.0);
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
//!
//! An example converting from R64 to primitive types.
//!
//! ```
//! use noisy_float::prelude::*;
//! use num_traits::cast::ToPrimitive;
//!
//! let value_r64: R64 = r64(1.0);
//! let value_f64_a: f64 = value_r64.into();
//! let value_f64_b: f64 = value_r64.raw();
//! let value_u64: u64 = value_r64.to_u64().unwrap();
//!
//! assert!(value_f64_a == value_f64_b);
//! assert!(value_f64_a as u64 == value_u64);
//! ```
//!
//! # Features
//!
//! This crate has the following cargo features:
//!
//! - `serde`: Enable serialization for all `NoisyFloats` using serde 1.0 and
//!   will transparently serialize then as floats
//! - `approx`: Adds implementations to use `NoisyFloat` with the `approx`
//!   crate

#![no_std]

#[cfg(feature = "serde")]
use serde::{de::Error, Deserialize, Deserializer, Serialize, Serializer};

pub mod checkers;
mod float_impl;
pub mod types;

/// Prelude for the `noisy_float` crate.
///
/// This includes all of the types defined in the `noisy_float::types` module,
/// as well as a re-export of the `Float` trait from the `num_traits` crate.
/// It is important to have this re-export here, because it allows the user
/// to access common floating point methods like `abs()`, `sqrt()`, etc.
pub mod prelude {
    pub use crate::types::*;

    #[doc(no_inline)]
    pub use num_traits::Float;
}

use core::{fmt, marker::PhantomData};
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
#[repr(transparent)]
pub struct NoisyFloat<F: Float, C: FloatChecker<F>> {
    value: F,
    checker: PhantomData<C>,
}

impl<F: Float, C: FloatChecker<F>> NoisyFloat<F, C> {
    /// Constructs a `NoisyFloat` with the given value.
    ///
    /// Uses the `FloatChecker` to assert that the value is valid.
    #[inline]
    pub fn new(value: F) -> Self {
        C::assert(value);
        Self::unchecked_new_generic(value)
    }

    #[inline]
    fn unchecked_new_generic(value: F) -> Self {
        NoisyFloat {
            value,
            checker: PhantomData,
        }
    }

    /// Tries to construct a `NoisyFloat` with the given value.
    ///
    /// Returns `None` if the value is invalid.
    #[inline]
    pub fn try_new(value: F) -> Option<Self> {
        if C::check(value) {
            Some(NoisyFloat {
                value,
                checker: PhantomData,
            })
        } else {
            None
        }
    }

    /// Converts the value in-place to a reference to a `NoisyFloat`.
    ///
    /// Uses the `FloatChecker` to assert that the value is valid.
    #[inline]
    pub fn borrowed(value: &F) -> &Self {
        C::assert(*value);
        Self::unchecked_borrowed(value)
    }

    #[inline]
    fn unchecked_borrowed(value: &F) -> &Self {
        // This is safe because `NoisyFloat` is a thin wrapper around the
        // floating-point type.
        unsafe { &*(value as *const F as *const Self) }
    }

    /// Tries to convert the value in-place to a reference to a `NoisyFloat`.
    ///
    /// Returns `None` if the value is invalid.
    #[inline]
    pub fn try_borrowed(value: &F) -> Option<&Self> {
        if C::check(*value) {
            Some(Self::unchecked_borrowed(value))
        } else {
            None
        }
    }

    /// Converts the value in-place to a mutable reference to a `NoisyFloat`.
    ///
    /// Uses the `FloatChecker` to assert that the value is valid.
    #[inline]
    pub fn borrowed_mut(value: &mut F) -> &mut Self {
        C::assert(*value);
        Self::unchecked_borrowed_mut(value)
    }

    #[inline]
    fn unchecked_borrowed_mut(value: &mut F) -> &mut Self {
        // This is safe because `NoisyFloat` is a thin wrapper around the
        // floating-point type.
        unsafe { &mut *(value as *mut F as *mut Self) }
    }

    /// Tries to convert the value in-place to a mutable reference to a `NoisyFloat`.
    ///
    /// Returns `None` if the value is invalid.
    #[inline]
    pub fn try_borrowed_mut(value: &mut F) -> Option<&mut Self> {
        if C::check(*value) {
            Some(Self::unchecked_borrowed_mut(value))
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

    /// Compares and returns the minimum of two values.
    ///
    /// This method exists to disambiguate between `num_traits::Float.min` and `std::cmp::Ord.min`.
    #[inline]
    pub fn min(self, other: Self) -> Self {
        Ord::min(self, other)
    }

    /// Compares and returns the maximum of two values.
    ///
    /// This method exists to disambiguate between `num_traits::Float.max` and `std::cmp::Ord.max`.
    #[inline]
    pub fn max(self, other: Self) -> Self {
        Ord::max(self, other)
    }
}

impl<F: Float + Default, C: FloatChecker<F>> Default for NoisyFloat<F, C> {
    #[inline]
    fn default() -> Self {
        Self::new(F::default())
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

#[cfg(feature = "serde")]
impl<F: Float + Serialize, C: FloatChecker<F>> Serialize for NoisyFloat<F, C> {
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        self.value.serialize(ser)
    }
}

#[cfg(feature = "serde")]
impl<'de, F: Float + Deserialize<'de>, C: FloatChecker<F>> Deserialize<'de> for NoisyFloat<F, C> {
    fn deserialize<D: Deserializer<'de>>(de: D) -> Result<Self, D::Error> {
        let value = F::deserialize(de)?;
        Self::try_new(value).ok_or_else(|| D::Error::custom("invalid NoisyFloat"))
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use std::prelude::v1::*;

    use crate::prelude::*;
    #[cfg(feature = "serde")]
    use serde_derive::{Deserialize, Serialize};
    #[cfg(feature = "serde")]
    use serde_json;
    use std::{
        f32,
        f64::{self, consts},
        hash::{Hash, Hasher},
        mem::{align_of, size_of},
    };

    #[test]
    fn smoke_test() {
        assert_eq!(n64(1.0) + 2.0, 3.0);
        assert_ne!(n64(3.0), n64(2.9));
        assert!(r64(1.0) < 2.0);
        let mut value = n64(18.0);
        value %= n64(5.0);
        assert_eq!(-value, n64(-3.0));
        assert_eq!(r64(1.0).exp(), consts::E);
        assert_eq!((N64::try_new(1.0).unwrap() / N64::infinity()), 0.0);
        assert_eq!(N64::from_f32(f32::INFINITY), N64::from_f64(f64::INFINITY));
        assert_eq!(R64::try_new(f64::NEG_INFINITY), None);
        assert_eq!(N64::try_new(f64::NAN), None);
        assert_eq!(R64::try_new(f64::NAN), None);
        assert_eq!(N64::try_borrowed(&f64::NAN), None);
        let mut nan = f64::NAN;
        assert_eq!(N64::try_borrowed_mut(&mut nan), None);
    }

    #[test]
    fn ensure_layout() {
        assert_eq!(size_of::<N32>(), size_of::<f32>());
        assert_eq!(align_of::<N32>(), align_of::<f32>());

        assert_eq!(size_of::<N64>(), size_of::<f64>());
        assert_eq!(align_of::<N64>(), align_of::<f64>());
    }

    #[test]
    fn borrowed_casts() {
        assert_eq!(R64::borrowed(&3.14), &3.14);
        assert_eq!(N64::borrowed(&[f64::INFINITY; 2][0]), &f64::INFINITY);
        assert_eq!(N64::borrowed_mut(&mut 2.72), &mut 2.72);
    }

    #[test]
    fn test_convert() {
        assert_eq!(f32::from(r32(3.0)), 3.0f32);
        assert_eq!(f64::from(r32(5.0)), 5.0f64);
        assert_eq!(f64::from(r64(7.0)), 7.0f64);
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic]
    fn n64_nan() {
        let _ = n64(0.0) / n64(0.0);
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic]
    fn r64_nan() {
        let _ = r64(0.0) / r64(0.0);
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic]
    fn r64_infinity() {
        let _ = r64(1.0) / r64(0.0);
    }

    #[test]
    fn resolves_min_max() {
        assert_eq!(r64(1.0).min(r64(3.0)), r64(1.0));
        assert_eq!(r64(1.0).max(r64(3.0)), r64(3.0));
    }

    #[test]
    fn epsilon() {
        assert_eq!(R32::epsilon(), f32::EPSILON);
        assert_eq!(R64::epsilon(), f64::EPSILON);
    }

    #[test]
    fn test_try_into() {
        use std::convert::{TryFrom, TryInto};
        let _: R64 = 1.0.try_into().unwrap();
        let _ = R64::try_from(f64::INFINITY).unwrap_err();
    }

    struct TestHasher {
        bytes: Vec<u8>,
    }

    impl Hasher for TestHasher {
        fn finish(&self) -> u64 {
            panic!("unexpected Hasher.finish invocation")
        }
        fn write(&mut self, bytes: &[u8]) {
            self.bytes.extend_from_slice(bytes)
        }
    }

    fn hash_bytes<T: Hash>(value: T) -> Vec<u8> {
        let mut hasher = TestHasher { bytes: Vec::new() };
        value.hash(&mut hasher);
        hasher.bytes
    }

    #[test]
    fn test_hash() {
        assert_eq!(hash_bytes(r64(10.3)), hash_bytes(10.3f64.to_bits()));
        assert_ne!(hash_bytes(r64(10.3)), hash_bytes(10.4f64.to_bits()));
        assert_eq!(hash_bytes(r32(10.3)), hash_bytes(10.3f32.to_bits()));
        assert_ne!(hash_bytes(r32(10.3)), hash_bytes(10.4f32.to_bits()));

        assert_eq!(
            hash_bytes(N64::infinity()),
            hash_bytes(f64::INFINITY.to_bits())
        );
        assert_eq!(
            hash_bytes(N64::neg_infinity()),
            hash_bytes(f64::NEG_INFINITY.to_bits())
        );

        // positive and negative zero should have the same hashes
        assert_eq!(hash_bytes(r64(0.0)), hash_bytes(0.0f64.to_bits()));
        assert_eq!(hash_bytes(r64(-0.0)), hash_bytes(0.0f64.to_bits()));
        assert_eq!(hash_bytes(r32(0.0)), hash_bytes(0.0f32.to_bits()));
        assert_eq!(hash_bytes(r32(-0.0)), hash_bytes(0.0f32.to_bits()));
    }

    #[cfg(feature = "serde")]
    #[test]
    fn serialize_transparently_as_float() {
        let num = R32::new(3.14);
        let should_be = "3.14";

        let got = serde_json::to_string(&num).unwrap();
        assert_eq!(got, should_be);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn deserialize_transparently_as_float() {
        let src = "3.14";
        let should_be = R32::new(3.14);

        let got: R32 = serde_json::from_str(src).unwrap();
        assert_eq!(got, should_be);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn deserialize_invalid_float() {
        use crate::{FloatChecker, NoisyFloat};
        struct PositiveChecker;
        impl FloatChecker<f64> for PositiveChecker {
            fn check(value: f64) -> bool {
                value > 0.
            }
            fn assert(value: f64) {
                debug_assert!(Self::check(value))
            }
        }

        let src = "-1.0";
        let got: Result<NoisyFloat<f64, PositiveChecker>, _> = serde_json::from_str(src);
        assert!(got.is_err());
    }

    // Make sure you can use serde_derive with noisy floats.
    #[cfg(feature = "serde")]
    #[derive(Debug, PartialEq, Serialize, Deserialize)]
    struct Dummy {
        value: N64,
    }

    #[cfg(feature = "serde")]
    #[test]
    fn deserialize_struct_containing_n64() {
        let src = r#"{ "value": 3.14 }"#;
        let should_be = Dummy { value: n64(3.14) };

        let got: Dummy = serde_json::from_str(src).unwrap();
        assert_eq!(got, should_be);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn serialize_struct_containing_n64() {
        let src = Dummy { value: n64(3.14) };
        let should_be = r#"{"value":3.14}"#;

        let got = serde_json::to_string(&src).unwrap();
        assert_eq!(got, should_be);
    }

    #[cfg(feature = "approx")]
    #[test]
    fn approx_assert_eq() {
        use approx::{assert_abs_diff_eq, assert_relative_eq, assert_ulps_eq};

        let lhs = r64(0.1000000000000001);
        let rhs = r64(0.1);

        assert_abs_diff_eq!(lhs, rhs);
        assert_relative_eq!(lhs, rhs);
        assert_ulps_eq!(lhs, rhs);
    }

    #[test]
    fn const_functions() {
        const A: N32 = N32::unchecked_new(1.0);
        const B: N64 = N64::unchecked_new(2.0);
        const C: R32 = R32::unchecked_new(3.0);
        const D: R64 = R64::unchecked_new(4.0);

        const A_RAW: f32 = A.const_raw();
        const B_RAW: f64 = B.const_raw();
        const C_RAW: f32 = C.const_raw();
        const D_RAW: f64 = D.const_raw();

        assert_eq!(A_RAW, 1.0);
        assert_eq!(B_RAW, 2.0);
        assert_eq!(C_RAW, 3.0);
        assert_eq!(D_RAW, 4.0);
    }
}
