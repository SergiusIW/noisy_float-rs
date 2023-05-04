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

//! Standard implementations of `FloatChecker`.

use crate::{FloatChecker, NoisyFloat};
use num_traits::Float;

/// A `FloatChecker` that considers all values valid except NaN.
///
/// This checks that the value is a "number", i.e. it is not "not-a-number".
///
/// The `assert` method is implemented using `debug_assert!`.
pub struct NumChecker;

impl<F: Float> FloatChecker<F> for NumChecker {
    #[inline]
    fn assert(value: F) {
        debug_assert!(Self::check(value), "unexpected NaN");
    }

    #[inline]
    fn check(value: F) -> bool {
        !value.is_nan()
    }
}

/// A `FloatChecker` that considers all values valid except NaN and +/- Infinity.
///
/// The `assert` method is implemented using `debug_assert!`.
pub struct FiniteChecker;

impl<F: Float> FloatChecker<F> for FiniteChecker {
    #[inline]
    fn assert(value: F) {
        debug_assert!(Self::check(value), "unexpected NaN or infinity");
    }

    #[inline]
    fn check(value: F) -> bool {
        value.is_finite()
    }
}

impl<F: Float> From<NoisyFloat<F, FiniteChecker>> for NoisyFloat<F, NumChecker> {
    fn from(value: NoisyFloat<F, FiniteChecker>) -> Self {
        Self::unchecked_new_generic(value.raw())
    }
}

/// A `FloatChecker` that considers any finite, non-negative values valid.
///
/// Zero and positive finite values are okay, anything else (negative, infinite, NaN) is invalid.
///
/// The `assert` method is implemented using `debug_assert!`.
pub struct NonNegativeChecker;

impl<F: Float> FloatChecker<F> for NonNegativeChecker {
    #[inline]
    fn assert(value: F) {
        debug_assert!(value.is_finite(), "unexpected NaN or infinity");
        debug_assert!(!value.is_sign_negative(), "unexpected negative number");
    }

    #[inline]
    fn check(value: F) -> bool {
        value.is_finite() && !value.is_sign_negative()
    }
}

impl<F: Float> From<NoisyFloat<F, NonNegativeChecker>> for NoisyFloat<F, FiniteChecker> {
    #[inline]
    fn from(value: NoisyFloat<F, NonNegativeChecker>) -> Self {
        Self::unchecked_new_generic(value.raw())
    }
}
impl<F: Float> From<NoisyFloat<F, NonNegativeChecker>> for NoisyFloat<F, NumChecker> {
    #[inline]
    fn from(value: NoisyFloat<F, NonNegativeChecker>) -> Self {
        Self::unchecked_new_generic(value.raw())
    }
}
