#![feature(prelude_import)]
#![no_std]
#[macro_use]
extern crate std;
#[prelude_import]
use ::std::prelude::rust_2015::*;
// Test for issue 80832
//
//@ pretty-mode:expanded
//@ pp-exact:expanded-and-path-remap-80832.pp
//@ compile-flags: --remap-path-prefix {{src-base}}=the/src

fn main() {}
