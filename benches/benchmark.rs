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

use criterion::{black_box as bb, criterion_group, criterion_main, Criterion};
use noisy_float::prelude::*;
use std::iter::Sum;

fn bench_ops(c: &mut Criterion) {
    let mut group = c.benchmark_group("Add [20. + 3.]");
    group.bench_function("f32", |b| b.iter(|| bb(20_f32) + bb(3_f32)));
    group.bench_function("R32", |b| b.iter(|| r32(bb(20_f32)) + r32(bb(3_f32))));
    group.bench_function("N32", |b| b.iter(|| n32(bb(20_f32)) + n32(bb(3_f32))));
    group.bench_function("f64", |b| b.iter(|| bb(20_f64) + bb(3_f64)));
    group.bench_function("R64", |b| b.iter(|| r64(bb(20_f64)) + r64(bb(3_f64))));
    group.bench_function("N64", |b| b.iter(|| n64(bb(20_f64)) + n64(bb(3_f64))));
    group.finish();

    let mut group = c.benchmark_group("Multiply [20. * 3.]");
    group.bench_function("f64", |b| b.iter(|| bb(20_f64) * bb(3_f64)));
    group.bench_function("R64", |b| b.iter(|| r64(bb(20_f64)) * r64(bb(3_f64))));
    group.finish();

    let mut group = c.benchmark_group("Divide [20. / 3.]");
    group.bench_function("f64", |b| b.iter(|| bb(20_f64) / bb(3_f64)));
    group.bench_function("R64", |b| b.iter(|| r64(bb(20_f64)) / r64(bb(3_f64))));
    group.finish();

    let mut group = c.benchmark_group("Divide-Assign [20. /= 3.]");
    group.bench_function("f64", |b| b.iter(|| {
        let mut x = bb(20_f64);
        x /= bb(3_f64);
        x
    }));
    group.bench_function("R64", |b| b.iter(|| {
        let mut x = r64(bb(20_f64));
        x /= r64(bb(3_f64));
        x
    }));
    group.finish();

    let mut group = c.benchmark_group("Equals [20. == 20.]");
    group.bench_function("f64", |b| b.iter(|| bb(20_f64) == bb(20_f64)));
    group.bench_function("R64", |b| b.iter(|| r64(bb(20_f64)) == r64(bb(20_f64))));
    group.finish();

    let mut group = c.benchmark_group("Less than [20. < 3.]");
    group.bench_function("f64", |b| b.iter(|| bb(20_f64) < bb(3_f64)));
    group.bench_function("R64", |b| b.iter(|| r64(bb(20_f64)) < r64(bb(3_f64))));
    group.finish();
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

    let mut group = c.benchmark_group("Matrix-Vector multiply [20 x 20]");
    group.bench_function("f64", move |b| b.iter(|| matrix_vector_multiply(bb(&matrix), bb(&vector))));
    group.bench_function("R64", move |b| b.iter(|| matrix_vector_multiply(bb(&matrix_r64), bb(&vector_r64))));
    group.finish();
}

criterion_group!(benches, bench_ops, bench_algorithm);
criterion_main!(benches);
