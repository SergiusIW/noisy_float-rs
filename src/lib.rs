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

extern crate num_traits;

mod float_impl;

use std::marker::PhantomData;
use num_traits::Float;

//FIXME add doc comments
//FIXME proofread rustdocs, make sure the impls from float_impl are included
//FIXME move NumChecker and FiniteChecker to a "checkers" module
//FIXME move N32 ... r64 to a "types" module, and remove the prelude
//FIXME careful with Eq definition for +/- 0

pub mod prelude {
    pub use ::{N32, N64, R32, R64, n32, n64, r32, r64};
}

pub trait FloatChecker<F> {
    fn assert(value: F);
    fn check(value: F) -> bool;
}

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

pub struct NoisyFloat<F: Float, C: FloatChecker<F>> {
    value: F,
    checker: PhantomData<C>
}

//note: not implementing From<F>, because From conversion is never supposed to fail, according to the docs
impl<F: Float, C: FloatChecker<F>> NoisyFloat<F, C> {
    #[inline]
    pub fn new(value: F) -> NoisyFloat<F, C> {
        C::assert(value);
        Self::unchecked_new(value)
    }
    
    #[inline]
    fn unchecked_new(value: F) -> NoisyFloat<F, C> {
        NoisyFloat {
            value: value,
            checker: PhantomData
        }
    }
    
    #[inline]
    pub fn try_new(value: F) -> Option<NoisyFloat<F, C>> {
        if C::check(value) {
            Some(NoisyFloat {
                value: value,
                checker: PhantomData
            })
        } else {
            None
        }
    }

    #[inline]
    pub fn raw(self) -> F {
        self.value
    }
}

impl<C: FloatChecker<f32>> Into<f32> for NoisyFloat<f32, C> {
    #[inline]
    fn into(self) -> f32 {
        self.value
    }
}

impl<C: FloatChecker<f64>> Into<f64> for NoisyFloat<f64, C> {
    #[inline]
    fn into(self) -> f64 {
        self.value
    }
}

pub type N32 = NoisyFloat<f32, NumChecker>;
pub type N64 = NoisyFloat<f64, NumChecker>;
pub type R32 = NoisyFloat<f32, FiniteChecker>;
pub type R64 = NoisyFloat<f64, FiniteChecker>;

#[inline]
pub fn n32(value: f32) -> N32 {
    N32::new(value)
}

#[inline]
pub fn n64(value: f64) -> N64 {
    N64::new(value)
}

#[inline]
pub fn r32(value: f32) -> R32 {
    R32::new(value)
}

#[inline]
pub fn r64(value: f64) -> R64 {
    R64::new(value)
}


//TODO add tests
#[cfg(test)]
mod tests {
    use prelude::*;

    #[test]
    fn it_works() {
        n64(1.0) + n64(2.0);
    }
}
