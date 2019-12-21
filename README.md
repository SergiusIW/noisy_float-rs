# noisy_float-rs
This is a Rust library containing floating point types that panic if they are set
to an illegal value, such as NaN.

### Crate

The Rust crate for this library can be found [here](https://crates.io/crates/noisy_float).

### Documentation

The documentation for this library can be found [here](https://docs.rs/noisy_float).

### Description

The name "Noisy Float" comes from
the terms "quiet NaN" and "signaling NaN"; "signaling" was too long
to put in a struct/crate name, so "noisy" is used instead, being the opposite
of "quiet."

The standard types defined in `noisy_float::types` follow the principle
demonstrated by Rust's handling of integer overflow:
a bad arithmetic operation is considered an error,
but it is too costly to check everywhere in optimized builds.
For each floating point number that is created, a `debug_assert!` invocation is used
to check if it is valid or not.
This way, there are guarantees when developing code that floating point
numbers have valid values,
but during a release run there is *no overhead* for using these floating
point types compared to using `f32` or `f64` directly.

This crate makes use of the num, bounded, signed and floating point traits in the
popular `num_traits` crate.
This crate can be compiled with no_std.

### Examples
An example using the `R64` type, which corresponds to *finite* `f64` values.

```rust
use noisy_float::prelude::*;

fn geometric_mean(a: R64, b: R64) -> R64 {
    (a * b).sqrt() //used just like regular floating-point numbers
}

println!("geometric_mean(10.0, 20.0) = {}", geometric_mean(r64(10.0), r64(20.0)));
//prints 14.142...
```

An example using the `N32` type, which corresponds to *non-NaN* `f32` values.
The float types in this crate are able to implement `Eq` and `Ord` properly,
since NaN is not allowed.

```rust
use noisy_float::prelude::*;

let values = vec![n32(3.0), n32(-1.5), n32(71.3), N32::infinity()];
assert!(values.iter().cloned().min() == Some(n32(-1.5)));
assert!(values.iter().cloned().max() == Some(N32::infinity()));
```

### License 

Noisy_float is licensed under the [Apache 2.0 
License](http://www.apache.org/licenses/LICENSE-2.0.html).
