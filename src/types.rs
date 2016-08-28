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

use ::NoisyFloat;
use checkers::{NumChecker, FiniteChecker};

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
