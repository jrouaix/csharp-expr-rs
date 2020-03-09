// #![cfg(feature = "alloc")]
// #[global_allocator]
// static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

// #![feature(result_map_or_else)]
#![deny(bare_trait_objects)]

#[macro_use]
extern crate lazy_static;

pub mod expressions;
pub mod ffi;
mod functions;
mod parsing;

// got this list from rust : https://github.com/rust-lang/rust/blob/master/src/libsyntax/util/parser.rs
// #[derive(PartialEq, Debug)]
// pub enum AssocOp {
//     /// `+`
//     Add,
//     /// `-`
//     Subtract,
//     /// `*`
//     Multiply,
//     /// `/`
//     Divide,
//     /// `%`
//     Modulus,
//     /// `&&`
//     LAnd,
//     /// `||`
//     LOr,
//     /// `==`
//     Equal,
//     /// `<`
//     Less,
//     /// `<=`
//     LessEqual,
//     /// `!=`
//     NotEqual,
//     /// `>`
//     Greater,
//     /// `>=`
//     GreaterEqual,
// }
