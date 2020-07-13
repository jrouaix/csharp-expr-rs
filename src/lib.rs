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
