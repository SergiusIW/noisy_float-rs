// Copyright 2016-2019 Matthew D. Michelotti
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

//! Standard definitions of `NoisyFloat`.
//!
//! Definitions in this module all use `debug_assert!`
//! to check for valid values, so there is no overhead
//! when running in an optimized build.

use crate::{
    NoisyFloat,
    checkers::{NumChecker, FiniteChecker},
};

/// A floating point number behaving like `f32` that does not allow NaN.
///
/// The "N" in the name stands for "Number", since all values of this type
/// are "numbers", i.e. they are not "not-a-number".
pub type N32 = NoisyFloat<f32, NumChecker>;

/// A floating point number behaving like `f64` that does not allow NaN.
///
/// The "N" in the name stands for "Number", since all values of this type
/// are "numbers", i.e. they are not "not-a-number".
pub type N64 = NoisyFloat<f64, NumChecker>;

/// A floating point number behaving like `f32` that does not allow NaN or +/- Infinity.
///
/// The "R" in the name stands for "Real", since in Mathematics, the Real
/// numbers do not include NaN or +/- Infinity.
pub type R32 = NoisyFloat<f32, FiniteChecker>;

/// A floating point number behaving like `f64` that does not allow NaN or +/- Infinity.
///
/// The "R" in the name stands for "Real", since in Mathematics, the Real
/// numbers do not include NaN or +/- Infinity.
pub type R64 = NoisyFloat<f64, FiniteChecker>;


/// Shorthand for `N32::new(value)`.
#[inline]
pub fn n32(value: f32) -> N32 {
    N32::new(value)
}

/// Shorthand for `N64::new(value)`.
#[inline]
pub fn n64(value: f64) -> N64 {
    N64::new(value)
}

/// Shorthand for `R32::new(value)`.
#[inline]
pub fn r32(value: f32) -> R32 {
    R32::new(value)
}

/// Shorthand for `R64::new(value)`.
#[inline]
pub fn r64(value: f64) -> R64 {
    R64::new(value)
}
