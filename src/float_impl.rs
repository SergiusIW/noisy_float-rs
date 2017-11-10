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

use std::cmp::Ordering;
use std::iter;
use std::ops::{Add, Sub, Mul, Div, Rem, AddAssign, SubAssign, MulAssign, DivAssign, RemAssign, Neg};
use std::num::FpCategory;
use num_traits::{Float, Num, FloatConst};
use num_traits::cast::{NumCast, ToPrimitive};
use num_traits::identities::{Zero, One};
use ::{FloatChecker, NoisyFloat};

impl<F: Float, C: FloatChecker<F>> Clone for NoisyFloat<F, C> {
    #[inline] fn clone(&self) -> Self { Self::unchecked_new(self.value) }
}

impl<F: Float, C: FloatChecker<F>> Copy for NoisyFloat<F, C> {}

impl<F: Float, C: FloatChecker<F>> PartialEq<F> for NoisyFloat<F, C> {
    #[inline] fn eq(&self, other: &F) -> bool { self.value.eq(&other) }
}

impl<F: Float, C: FloatChecker<F>> PartialEq for NoisyFloat<F, C> {
    #[inline] fn eq(&self, other: &Self) -> bool { self.eq(&other.value) }
}

impl<F: Float, C: FloatChecker<F>> Eq for NoisyFloat<F, C> {}

impl<F: Float, C: FloatChecker<F>> PartialOrd<F> for NoisyFloat<F, C> {
    #[inline] fn partial_cmp(&self, other: &F) -> Option<Ordering> { self.value.partial_cmp(&other) }
    #[inline] fn lt(&self, other: &F) -> bool { self.value.lt(&other) }
    #[inline] fn le(&self, other: &F) -> bool { self.value.le(&other) }
    #[inline] fn gt(&self, other: &F) -> bool { self.value.gt(&other) }
    #[inline] fn ge(&self, other: &F) -> bool { self.value.ge(&other) }
}

impl<F: Float, C: FloatChecker<F>> PartialOrd for NoisyFloat<F, C> {
    #[inline] fn partial_cmp(&self, other: &Self) -> Option<Ordering> { self.value.partial_cmp(&other.value) }
    #[inline] fn lt(&self, other: &Self) -> bool { self.lt(&other.value) }
    #[inline] fn le(&self, other: &Self) -> bool { self.le(&other.value) }
    #[inline] fn gt(&self, other: &Self) -> bool { self.gt(&other.value) }
    #[inline] fn ge(&self, other: &Self) -> bool { self.ge(&other.value) }
}

impl<F: Float, C: FloatChecker<F>> Ord for NoisyFloat<F, C> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        if self.value < other.value {
            Ordering::Less
        } else if self.value == other.value {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    }
}

impl<F: Float, C: FloatChecker<F>> Add<F> for NoisyFloat<F, C> {
    type Output = Self;
    #[inline] fn add(self, rhs: F) -> Self { Self::new(self.value.add(rhs)) }
}

impl<F: Float, C: FloatChecker<F>> Add for NoisyFloat<F, C> {
    type Output = Self;
    #[inline] fn add(self, rhs: Self) -> Self { self.add(rhs.value) }
}

impl<F: Float, C: FloatChecker<F>> Sub<F> for NoisyFloat<F, C> {
    type Output = Self;
    #[inline] fn sub(self, rhs: F) -> Self { Self::new(self.value.sub(rhs)) }
}

impl<F: Float, C: FloatChecker<F>> Sub for NoisyFloat<F, C> {
    type Output = Self;
    #[inline] fn sub(self, rhs: Self) -> Self { self.sub(rhs.value) }
}

impl<F: Float, C: FloatChecker<F>> Mul<F> for NoisyFloat<F, C> {
    type Output = Self;
    #[inline] fn mul(self, rhs: F) -> Self { Self::new(self.value.mul(rhs)) }
}

impl<F: Float, C: FloatChecker<F>> Mul for NoisyFloat<F, C> {
    type Output = Self;
    #[inline] fn mul(self, rhs: Self) -> Self { self.mul(rhs.value) }
}

impl<F: Float, C: FloatChecker<F>> Div<F> for NoisyFloat<F, C> {
    type Output = Self;
    #[inline] fn div(self, rhs: F) -> Self { Self::new(self.value.div(rhs)) }
}

impl<F: Float, C: FloatChecker<F>> Div for NoisyFloat<F, C> {
    type Output = Self;
    #[inline] fn div(self, rhs: Self) -> Self { self.div(rhs.value) }
}

impl<F: Float, C: FloatChecker<F>> Rem<F> for NoisyFloat<F, C> {
    type Output = Self;
    #[inline] fn rem(self, rhs: F) -> Self { Self::new(self.value.rem(rhs)) }
}

impl<F: Float, C: FloatChecker<F>> Rem for NoisyFloat<F, C> {
    type Output = Self;
    #[inline] fn rem(self, rhs: Self) -> Self { self.rem(rhs.value) }
}

impl<F: Float + AddAssign, C: FloatChecker<F>> AddAssign<F> for NoisyFloat<F, C> {
    #[inline] fn add_assign(&mut self, rhs: F) { self.value.add_assign(rhs); C::assert(self.value); }
}

impl<F: Float + AddAssign, C: FloatChecker<F>> AddAssign for NoisyFloat<F, C> {
    #[inline] fn add_assign(&mut self, rhs: Self) { self.add_assign(rhs.value); }
}

impl<F: Float + SubAssign, C: FloatChecker<F>> SubAssign<F> for NoisyFloat<F, C> {
    #[inline] fn sub_assign(&mut self, rhs: F) { self.value.sub_assign(rhs); C::assert(self.value); }
}

impl<F: Float + SubAssign, C: FloatChecker<F>> SubAssign for NoisyFloat<F, C> {
    #[inline] fn sub_assign(&mut self, rhs: Self) { self.sub_assign(rhs.value); }
}

impl<F: Float + MulAssign, C: FloatChecker<F>> MulAssign<F> for NoisyFloat<F, C> {
    #[inline] fn mul_assign(&mut self, rhs: F) { self.value.mul_assign(rhs); C::assert(self.value); }
}

impl<F: Float + MulAssign, C: FloatChecker<F>> MulAssign for NoisyFloat<F, C> {
    #[inline] fn mul_assign(&mut self, rhs: Self) { self.mul_assign(rhs.value); }
}

impl<F: Float + DivAssign, C: FloatChecker<F>> DivAssign<F> for NoisyFloat<F, C> {
    #[inline] fn div_assign(&mut self, rhs: F) { self.value.div_assign(rhs); C::assert(self.value); }
}

impl<F: Float + DivAssign, C: FloatChecker<F>> DivAssign for NoisyFloat<F, C> {
    #[inline] fn div_assign(&mut self, rhs: Self) { self.div_assign(rhs.value); }
}

impl<F: Float + RemAssign, C: FloatChecker<F>> RemAssign<F> for NoisyFloat<F, C> {
    #[inline] fn rem_assign(&mut self, rhs: F) { self.value.rem_assign(rhs); C::assert(self.value); }
}

impl<F: Float + RemAssign, C: FloatChecker<F>> RemAssign for NoisyFloat<F, C> {
    #[inline] fn rem_assign(&mut self, rhs: Self) { self.rem_assign(rhs.value); }
}

impl<F: Float, C: FloatChecker<F>> Neg for NoisyFloat<F, C> {
    type Output = Self;
    #[inline] fn neg(self) -> Self { Self::new(self.value.neg()) }
}

impl<F: Float, C: FloatChecker<F>> Zero for NoisyFloat<F, C> {
    #[inline] fn zero() -> Self { Self::new(F::zero()) }
    #[inline] fn is_zero(&self) -> bool { self.value.is_zero() }
}

impl<F: Float, C: FloatChecker<F>> One for NoisyFloat<F, C> {
    #[inline] fn one() -> Self { Self::new(F::one()) }
}

impl<F: Float, C: FloatChecker<F>> Num for NoisyFloat<F, C> {
    type FromStrRadixErr = F::FromStrRadixErr;
    #[inline] fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> { F::from_str_radix(str, radix).map(|v| Self::new(v)) }
}

impl<F: Float, C: FloatChecker<F>> ToPrimitive for NoisyFloat<F, C> {
    #[inline] fn to_i64(&self) -> Option<i64> { self.value.to_i64() }
    #[inline] fn to_u64(&self) -> Option<u64> { self.value.to_u64() }
    #[inline] fn to_isize(&self) -> Option<isize> { self.value.to_isize() }
    #[inline] fn to_i8(&self) -> Option<i8> { self.value.to_i8() }
    #[inline] fn to_i16(&self) -> Option<i16> { self.value.to_i16() }
    #[inline] fn to_i32(&self) -> Option<i32> { self.value.to_i32() }
    #[inline] fn to_usize(&self) -> Option<usize> { self.value.to_usize() }
    #[inline] fn to_u8(&self) -> Option<u8> { self.value.to_u8() }
    #[inline] fn to_u16(&self) -> Option<u16> { self.value.to_u16() }
    #[inline] fn to_u32(&self) -> Option<u32> { self.value.to_u32() }
    #[inline] fn to_f32(&self) -> Option<f32> { self.value.to_f32() }
    #[inline] fn to_f64(&self) -> Option<f64> { self.value.to_f64() }
}

impl<F: Float, C: FloatChecker<F>> NumCast for NoisyFloat<F, C> {
    #[inline] fn from<T: ToPrimitive>(n: T) -> Option<Self> { F::from(n).and_then(|v| Self::try_new(v)) }
}

impl<F: Float, C: FloatChecker<F>> Float for NoisyFloat<F, C> {
    #[inline] fn nan() -> Self { panic!("unexpected NaN") }
    #[inline] fn infinity() -> Self { Self::new(F::infinity()) }
    #[inline] fn neg_infinity() -> Self { Self::new(F::neg_infinity()) }
    #[inline] fn neg_zero() -> Self { Self::new(F::neg_zero()) }
    #[inline] fn min_value() -> Self { Self::new(F::min_value()) }
    #[inline] fn min_positive_value() -> Self { Self::new(F::min_positive_value()) }
    #[inline] fn max_value() -> Self { Self::new(F::max_value()) }
    #[inline] fn is_nan(self) -> bool { self.value.is_nan() }
    #[inline] fn is_infinite(self) -> bool { self.value.is_infinite() }
    #[inline] fn is_finite(self) -> bool { self.value.is_finite() }
    #[inline] fn is_normal(self) -> bool { self.value.is_normal() }
    #[inline] fn classify(self) -> FpCategory { self.value.classify() }
    #[inline] fn floor(self) -> Self { Self::new(self.value.floor()) }
    #[inline] fn ceil(self) -> Self { Self::new(self.value.ceil()) }
    #[inline] fn round(self) -> Self { Self::new(self.value.round()) }
    #[inline] fn trunc(self) -> Self { Self::new(self.value.trunc()) }
    #[inline] fn fract(self) -> Self { Self::new(self.value.fract()) }
    #[inline] fn abs(self) -> Self { Self::new(self.value.abs()) }
    #[inline] fn signum(self) -> Self { Self::new(self.value.signum()) }
    #[inline] fn is_sign_positive(self) -> bool { self.value.is_sign_positive() }
    #[inline] fn is_sign_negative(self) -> bool { self.value.is_sign_negative() }
    #[inline] fn mul_add(self, a: Self, b: Self) -> Self { Self::new(self.value.mul_add(a.value, b.value)) }
    #[inline] fn recip(self) -> Self { Self::new(self.value.recip()) }
    #[inline] fn powi(self, n: i32) -> Self { Self::new(self.value.powi(n)) }
    #[inline] fn powf(self, n: Self) -> Self { Self::new(self.value.powf(n.value)) }
    #[inline] fn sqrt(self) -> Self { Self::new(self.value.sqrt()) }
    #[inline] fn exp(self) -> Self { Self::new(self.value.exp()) }
    #[inline] fn exp2(self) -> Self { Self::new(self.value.exp2()) }
    #[inline] fn ln(self) -> Self { Self::new(self.value.ln()) }
    #[inline] fn log(self, base: Self) -> Self { Self::new(self.value.log(base.value)) }
    #[inline] fn log2(self) -> Self {Self::new(self.value.log2()) }
    #[inline] fn log10(self) -> Self { Self::new(self.value.log10()) }
    #[inline] fn max(self, other: Self) -> Self { Self::new(self.value.max(other.value)) }
    #[inline] fn min(self, other: Self) -> Self { Self::new(self.value.min(other.value)) }
    #[inline] fn abs_sub(self, other: Self) -> Self { Self::new(self.value.abs_sub(other.value)) }
    #[inline] fn cbrt(self) -> Self { Self::new(self.value.cbrt()) }
    #[inline] fn hypot(self, other: Self) -> Self { Self::new(self.value.hypot(other.value)) }
    #[inline] fn sin(self) -> Self { Self::new(self.value.sin()) }
    #[inline] fn cos(self) -> Self { Self::new(self.value.cos()) }
    #[inline] fn tan(self) -> Self { Self::new(self.value.tan()) }
    #[inline] fn asin(self) -> Self { Self::new(self.value.asin()) }
    #[inline] fn acos(self) -> Self { Self::new(self.value.acos()) }
    #[inline] fn atan(self) -> Self { Self::new(self.value.atan()) }
    #[inline] fn atan2(self, other: Self) -> Self { Self::new(self.value.atan2(other.value)) }
    #[inline] fn sin_cos(self) -> (Self, Self) { let (a, b) = self.value.sin_cos(); (Self::new(a), Self::new(b)) }
    #[inline] fn exp_m1(self) -> Self { Self::new(self.value.exp_m1()) }
    #[inline] fn ln_1p(self) -> Self { Self::new(self.value.ln_1p()) }
    #[inline] fn sinh(self) -> Self { Self::new(self.value.sinh()) }
    #[inline] fn cosh(self) -> Self { Self::new(self.value.cosh()) }
    #[inline] fn tanh(self) -> Self { Self::new(self.value.tanh()) }
    #[inline] fn asinh(self) -> Self { Self::new(self.value.asinh()) }
    #[inline] fn acosh(self) -> Self { Self::new(self.value.acosh()) }
    #[inline] fn atanh(self) -> Self { Self::new(self.value.atanh()) }
    #[inline] fn integer_decode(self) -> (u64, i16, i8) { self.value.integer_decode() }
    #[inline] fn to_degrees(self) -> Self { Self::new(self.value.to_degrees()) }
    #[inline] fn to_radians(self) -> Self { Self::new(self.value.to_radians()) }
}

impl<F: Float + FloatConst, C: FloatChecker<F>> FloatConst for NoisyFloat<F, C> {
    #[inline] fn E() -> Self { Self::new(F::E()) }
    #[inline] fn FRAC_1_PI() -> Self { Self::new(F::FRAC_1_PI()) }
    #[inline] fn FRAC_1_SQRT_2() -> Self { Self::new(F::FRAC_1_SQRT_2()) }
    #[inline] fn FRAC_2_PI() -> Self { Self::new(F::FRAC_2_PI()) }
    #[inline] fn FRAC_2_SQRT_PI() -> Self { Self::new(F::FRAC_2_SQRT_PI()) }
    #[inline] fn FRAC_PI_2() -> Self { Self::new(F::FRAC_PI_2()) }
    #[inline] fn FRAC_PI_3() -> Self { Self::new(F::FRAC_PI_3()) }
    #[inline] fn FRAC_PI_4() -> Self { Self::new(F::FRAC_PI_4()) }
    #[inline] fn FRAC_PI_6() -> Self { Self::new(F::FRAC_PI_6()) }
    #[inline] fn FRAC_PI_8() -> Self { Self::new(F::FRAC_PI_8()) }
    #[inline] fn LN_10() -> Self { Self::new(F::LN_10()) }
    #[inline] fn LN_2() -> Self { Self::new(F::LN_2()) }
    #[inline] fn LOG10_E() -> Self { Self::new(F::LOG10_E()) }
    #[inline] fn LOG2_E() -> Self { Self::new(F::LOG2_E()) }
    #[inline] fn PI() -> Self { Self::new(F::PI()) }
    #[inline] fn SQRT_2() -> Self { Self::new(F::SQRT_2()) }
}

impl<F: Float, C: FloatChecker<F>> iter::Sum for NoisyFloat<F, C> {
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        Self::new(iter.map(|i| i.raw()).fold(F::zero(), |acc, i| acc + i))
    }
}

impl<F: Float, C: FloatChecker<F>> iter::Product for NoisyFloat<F, C> {
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        Self::new(iter.map(|i| i.raw()).fold(F::one(), |acc, i| acc * i))
    }
}
