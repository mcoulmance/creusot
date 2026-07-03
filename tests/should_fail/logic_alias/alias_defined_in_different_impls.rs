#![allow(unused)] // to reduce noise in the error message

extern crate creusot_std;

use creusot_std::prelude::*;

trait T1 {
    #[logic]
    fn is_zero_log(x: Int) -> bool {
        x == 0
    }
}

trait T2 {
    fn is_zero(x: i64) -> bool;
}

struct S;

impl T1 for S {}
impl T2 for S {
    #[logic_alias(Self::is_zero_log(x@))]
    fn is_zero(x: i64) -> bool {
        x == 0
    }
}
