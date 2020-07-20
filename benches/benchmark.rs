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

use criterion::{black_box, criterion_group, criterion_main, Benchmark, Criterion};
use noisy_float::prelude::*;
use std::iter::Sum;

fn bench_ops(c: &mut Criterion) {
    c.bench(
        "Add [20. + 3.]",
        Benchmark::new("f32", |b| b.iter(|| black_box(20_f32) + black_box(3_f32)))
            .with_function("R32", |b| {
                b.iter(|| r32(black_box(20_f32)) + r32(black_box(3_f32)))
            })
            .with_function("N32", |b| {
                b.iter(|| n32(black_box(20_f32)) + n32(black_box(3_f32)))
            })
            .with_function("f64", |b| b.iter(|| black_box(20_f64) + black_box(3_f64)))
            .with_function("R64", |b| {
                b.iter(|| r64(black_box(20_f64)) + r64(black_box(3_f64)))
            })
            .with_function("N64", |b| {
                b.iter(|| n64(black_box(20_f64)) + n64(black_box(3_f64)))
            }),
    );
    c.bench(
        "Multiply [20. * 3.]",
        Benchmark::new("f64", |b| b.iter(|| black_box(20_f64) * black_box(3_f64)))
            .with_function("R64", |b| {
                b.iter(|| r64(black_box(20_f64)) * r64(black_box(3_f64)))
            }),
    );
    c.bench(
        "Divide [20. / 3.]",
        Benchmark::new("f64", |b| b.iter(|| black_box(20_f64) / black_box(3_f64)))
            .with_function("R64", |b| {
                b.iter(|| r64(black_box(20_f64)) / r64(black_box(3_f64)))
            }),
    );
    c.bench(
        "Divide-Assign [20. /= 3.]",
        Benchmark::new("f64", |b| {
            b.iter(|| {
                let mut x = black_box(20_f64);
                x /= black_box(3_f64);
                x
            })
        })
        .with_function("R64", |b| {
            b.iter(|| {
                let mut x = r64(black_box(20_f64));
                x /= r64(black_box(3_f64));
                x
            })
        }),
    );
    c.bench(
        "Equals [20. == 20.]",
        Benchmark::new("f64", |b| b.iter(|| black_box(20_f64) == black_box(20_f64)))
            .with_function("R64", |b| {
                b.iter(|| r64(black_box(20_f64)) == r64(black_box(20_f64)))
            }),
    );
    c.bench(
        "Less than [20. < 3.]",
        Benchmark::new("f64", |b| b.iter(|| black_box(20_f64) < black_box(3_f64)))
            .with_function("R64", |b| {
                b.iter(|| r64(black_box(20_f64)) < r64(black_box(3_f64)))
            }),
    );
}

fn matrix_vector_multiply<F: Float + Sum>(matrix: &[F], vector: &[F]) -> Vec<F> {
    let dim = vector.len();
    assert!(matrix.len() == dim * dim);
    matrix
        .chunks(dim)
        .map(|row| row.iter().zip(vector).map(|(&a, &b)| a * b).sum())
        .collect()
}

fn bench_algorithm(c: &mut Criterion) {
    let matrix: Vec<f64> = (0..(20 * 20)).map(|i| ((i * 31) % 50) as f64).collect();
    let vector: Vec<f64> = (0..20).map(|i| ((i * 37) % 70) as f64).collect();
    let matrix_r64: Vec<R64> = matrix.iter().map(|&x| r64(x)).collect();
    let vector_r64: Vec<R64> = vector.iter().map(|&x| r64(x)).collect();
    c.bench(
        "Matrix-Vector multiply [20 x 20]",
        Benchmark::new("f64", move |b| {
            b.iter(|| matrix_vector_multiply(black_box(&matrix), black_box(&vector)))
        })
        .with_function("R64", move |b| {
            b.iter(|| matrix_vector_multiply(black_box(&matrix_r64), black_box(&vector_r64)))
        }),
    );
}

criterion_group!(benches, bench_ops, bench_algorithm);
criterion_main!(benches);
