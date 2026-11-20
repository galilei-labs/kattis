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

pub type sint = Int63;

// Rocq: Plot.plot_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Plot.plot_implem.horner_loop
// Variant: uncurried
pub fn horner_loop_1(y: Array<Int63>, len: Int63, x: Int63, j: Int63, h: Int63) -> Int63 {
  horner_loop(y, len, x, j, h, ())
}

// Rocq: Plot.plot_implem.horner_loop (local: horner_loop)
// Variant: uncurried, lifted
pub fn horner_loop(y: Array<Int63>, len: Int63, x: Int63, j: Int63, h: Int63, _H: ()) -> Int63 {
  let tmp = j < len;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = j + int63!(1);
      let tmp_2 = h * x;
      let tmp_3 = y.get_cloned(j);
      horner_loop(y, len, x, tmp_1, tmp_2 + tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(y);
      h
    },
  }
}

// Rocq: Plot.plot_implem.eval_loop
// Variant: uncurried
pub fn eval_loop_1(y: Array<Int63>, len: Int63, x: Int63, d: Array<Int63>) -> Array<Int63> {
  eval_loop(y, len, x, d, ())
}

// Rocq: Plot.plot_implem.eval_loop (local: eval_loop)
// Variant: uncurried, lifted
pub fn eval_loop(y: Array<Int63>, len: Int63, x: Int63, d: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = x < len;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = x + int63!(1);
      let y_clone = Clone::clone(&y);
      let tmp_2 = horner_loop_1(y_clone, len, x, int63!(0), int63!(0));
      eval_loop(y, len, tmp_1, d.set(x, tmp_2), ())
    },
    sumbool::right => {
      std::mem::drop(y);
      d
    },
  }
}

// Rocq: Plot.plot_implem.diff_inner
// Variant: uncurried
pub fn diff_inner_1(lo: Int63, i: Int63, d: Array<Int63>) -> Array<Int63> {
  diff_inner(lo, i, d, ())
}

// Rocq: Plot.plot_implem.diff_inner (local: diff_inner)
// Variant: uncurried, lifted
pub fn diff_inner(lo: Int63, i: Int63, d: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = lo < i;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = d.get_cloned(i);
      let tmp_2 = d.get_cloned(i - int63!(1));
      let v = tmp_1 - tmp_2;
      diff_inner(lo, i - int63!(1), d.set(i, v), ())
    },
    sumbool::right => {
      d
    },
  }
}

// Rocq: Plot.plot_implem.diff_outer
// Variant: uncurried
pub fn diff_outer_1(len: Int63, s: Int63, d: Array<Int63>) -> Array<Int63> {
  diff_outer(len, s, d, ())
}

// Rocq: Plot.plot_implem.diff_outer (local: diff_outer)
// Variant: uncurried, lifted
pub fn diff_outer(len: Int63, s: Int63, d: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = s < len;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = s + int63!(1);
      let tmp_2 = len - int63!(1);
      diff_outer(len, tmp_1, diff_inner_1(s, tmp_2, d), ())
    },
    sumbool::right => {
      d
    },
  }
}

// Rocq: Plot.plot_implem.plot_impl
// Variant: uncurried
pub fn plot_impl(_n: Int63, y: Array<Int63>) -> Array<Int63> {
  let len = y.length();
  let tmp = Array::<Int63>::make(len, int63!(0));
  let d = eval_loop_1(y, len, int63!(0), tmp);
  diff_outer_1(len, int63!(0), d)
}
