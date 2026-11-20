#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type sint = Int63;

pub type uint = Int63;

// Rocq: Cold.cold_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Cold.cold_implem.count_loop
// Variant: uncurried
pub fn count_loop_1(x: Array<Int63>, n: Int63, i: Int63, acc: Int63) -> Int63 {
  count_loop(x, n, i, acc, ())
}

// Rocq: Cold.cold_implem.count_loop (local: count_loop)
// Variant: uncurried, lifted
pub fn count_loop(x: Array<Int63>, n: Int63, i: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = x.get_cloned(i);
      let tmp_3 = int63!(0);
      let tmp_4 = if tmp_2.ltsb(tmp_3) {
        acc + int63!(1)
      } else {
        acc
      };
      count_loop(x, n, tmp_1, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      acc
    },
  }
}

// Rocq: Cold.cold_implem.count_negatives_impl
pub fn count_negatives_impl(x: Array<Int63>) -> Int63 {
  let n = x.length();
  count_loop_1(x, n, int63!(0), int63!(0))
}
