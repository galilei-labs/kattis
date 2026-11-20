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

pub type uint = Int63;

// Rocq: Oddmanout.oddmanout_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Oddmanout.oddmanout_implem.xor_loop
// Variant: uncurried
pub fn xor_loop_1(a_1: Array<Int63>, n: Int63, i: Int63, acc: Int63) -> Int63 {
  xor_loop(a_1, n, i, acc, ())
}

// Rocq: Oddmanout.oddmanout_implem.xor_loop (local: xor_loop)
// Variant: uncurried, lifted
pub fn xor_loop(a_1: Array<Int63>, n: Int63, i: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = a_1.get_cloned(i);
      xor_loop(a_1, n, tmp_1, acc ^ tmp_2, ())
    },
    sumbool::right => {
      std::mem::drop(a_1);
      acc
    },
  }
}

// Rocq: Oddmanout.oddmanout_implem.odd_one_impl
pub fn odd_one_impl(a_1: Array<Int63>) -> Int63 {
  let tmp = a_1.length();
  xor_loop_1(a_1, tmp, int63!(0), int63!(0))
}
