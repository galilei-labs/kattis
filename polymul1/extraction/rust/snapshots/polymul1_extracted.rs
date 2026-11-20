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

// Rocq: Polymul1.polymul1_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Polymul1.polymul1_implem.row_loop
// Variant: uncurried
pub fn row_loop_1(y: Array<Int63>, ai: Int63, i: Int63, lb: Int63, j: Int63, r: Array<Int63>) -> Array<Int63> {
  row_loop(y, ai, i, lb, j, r, ())
}

// Rocq: Polymul1.polymul1_implem.row_loop (local: row_loop)
// Variant: uncurried, lifted
pub fn row_loop(y: Array<Int63>, ai: Int63, i: Int63, lb: Int63, j: Int63, r: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = j < lb;
  match bdec(tmp) {
    sumbool::left => {
      let k = i + j;
      let tmp_1 = j + int63!(1);
      let tmp_2 = r.get_cloned(k);
      let tmp_3 = y.get_cloned(j);
      let tmp_4 = ai * tmp_3;
      row_loop(y, ai, i, lb, tmp_1, r.set(k, tmp_2 + tmp_4), ())
    },
    sumbool::right => {
      std::mem::drop(y);
      r
    },
  }
}

// Rocq: Polymul1.polymul1_implem.rows_loop
// Variant: uncurried
pub fn rows_loop_1(x: Array<Int63>, y: Array<Int63>, la: Int63, lb: Int63, i: Int63, r: Array<Int63>) -> Array<Int63> {
  rows_loop(x, y, la, lb, i, r, ())
}

// Rocq: Polymul1.polymul1_implem.rows_loop (local: rows_loop)
// Variant: uncurried, lifted
pub fn rows_loop(x: Array<Int63>, y: Array<Int63>, la: Int63, lb: Int63, i: Int63, r: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < la;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = x.get_cloned(i);
      let y_clone = Clone::clone(&y);
      let tmp_3 = row_loop_1(y_clone, tmp_2, i, lb, int63!(0), r);
      rows_loop(x, y, la, lb, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      r
    },
  }
}

// Rocq: Polymul1.polymul1_implem.polymul_impl
// Variant: uncurried
pub fn polymul_impl(x: Array<Int63>, y: Array<Int63>) -> Array<Int63> {
  let la = x.length();
  let lb = y.length();
  if la == int63!(0) {
    std::mem::drop(x);
    std::mem::drop(y);
    Array::<Int63>::make(int63!(0), int63!(0))
  } else {
    if lb == int63!(0) {
      std::mem::drop(x);
      std::mem::drop(y);
      Array::<Int63>::make(int63!(0), int63!(0))
    } else {
      let tmp = la + lb;
      rows_loop_1(x, y, la, lb, int63!(0), Array::<Int63>::make(tmp - int63!(1), int63!(0)))
    }
  }
}
