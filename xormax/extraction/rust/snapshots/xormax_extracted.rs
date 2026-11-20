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

// Rocq: Xormax.xormax_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Xormax.xormax_implem.reduce
// Variant: uncurried
pub fn reduce_1(b_1: Array<Int63>, c: Int63, i: Int63) -> Array<Int63> {
  reduce(b_1, c, i, ())
}

// Rocq: Xormax.xormax_implem.reduce (local: reduce)
// Variant: uncurried, lifted
pub fn reduce(b_1: Array<Int63>, c: Int63, i: Int63, _H: ()) -> Array<Int63> {
  let tmp = int63!(0) < i;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = c >> i - int63!(1);
      if tmp_1 == int63!(0) {
        reduce(b_1, c, i - int63!(1), ())
      } else {
        let bk = b_1.get_cloned(i - int63!(1));
        if bk == int63!(0) {
          b_1.set(i - int63!(1), c)
        } else {
          reduce(b_1, c ^ bk, i - int63!(1), ())
        }
      }
    },
    sumbool::right => {
      b_1
    },
  }
}

// Rocq: Xormax.xormax_implem.build
// Variant: uncurried
pub fn build_1(x: Array<Int63>, n: Int63, j: Int63, b_1: Array<Int63>) -> Array<Int63> {
  build(x, n, j, b_1, ())
}

// Rocq: Xormax.xormax_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(x: Array<Int63>, n: Int63, j: Int63, b_1: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = j < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = j + int63!(1);
      let tmp_2 = x.get_cloned(j);
      build(x, n, tmp_1, reduce_1(b_1, tmp_2, int63!(63)), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      b_1
    },
  }
}

// Rocq: Xormax.xormax_implem.greedy
// Variant: uncurried
pub fn greedy_1(b_1: Array<Int63>, r: Int63, i: Int63) -> Int63 {
  greedy(b_1, r, i, ())
}

// Rocq: Xormax.xormax_implem.greedy (local: greedy)
// Variant: uncurried, lifted
pub fn greedy(b_1: Array<Int63>, r: Int63, i: Int63, _H: ()) -> Int63 {
  let tmp = int63!(0) < i;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = b_1.get_cloned(i - int63!(1));
      let r_ = r ^ tmp_1;
      let tmp_2 = if r < r_ {
        r_
      } else {
        r
      };
      greedy(b_1, tmp_2, i - int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(b_1);
      r
    },
  }
}

// Rocq: Xormax.xormax_implem.xormax_impl
pub fn xormax_impl(x: Array<Int63>) -> Int63 {
  let tmp = x.length();
  let b_1 = build_1(x, tmp, int63!(0), Array::<Int63>::make(int63!(63), int63!(0)));
  greedy_1(b_1, int63!(0), int63!(63))
}
