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

pub mod checkers;
pub mod types;
mod float_impl;

pub mod prelude {
    pub use types::*;
    
    pub use num_traits::{Float, Num};
    pub use num_traits::cast::{ToPrimitive, NumCast};
    pub use num_traits::identities::{Zero, One};
}

use std::marker::PhantomData;
use std::fmt;
use num_traits::Float;

//FIXME add doc comments
//FIXME proofread rustdocs, make sure the impls from float_impl are included

pub trait FloatChecker<F> {
    fn assert(value: F);
    fn check(value: F) -> bool;
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


//TODO add tests
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
        assert!(R64::one().exp() == r64(consts::E));
        assert!((N64::try_new(1.0).unwrap() / N64::infinity()).is_zero());
        assert!(NumCast::from(f32::INFINITY) == N64::try_new(f64::INFINITY));
        assert!(R64::try_new(f64::NEG_INFINITY) == None);
    }
}
