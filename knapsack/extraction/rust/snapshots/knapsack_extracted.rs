#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};
#[allow(unused_imports)] use rocq_bigint as b;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::PositiveTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::NaturalTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::IntegerTag>; };

pub type uint = Int63;

// Rocq: Knapsack.knapsack_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Knapsack.knapsack_implem.item_loop
// Variant: uncurried
pub fn item_loop_1(v: Int63, w: Int63, base: Int63, k: Int63, row: Array<Int63>, dec: Array<bool>) -> (Array<Int63>, Array<bool>) {
  item_loop(v, w, base, k, row, dec, ())
}

// Rocq: Knapsack.knapsack_implem.item_loop (local: item_loop)
// Variant: uncurried, lifted
pub fn item_loop(v: Int63, w: Int63, base: Int63, k: Int63, row: Array<Int63>, dec: Array<bool>, _H: ()) -> (Array<Int63>, Array<bool>) {
  let tmp = w < k;
  match bdec(tmp) {
    sumbool::left => {
      let c = k - int63!(1);
      let tmp_1 = row.get_cloned(c - w);
      let cand = tmp_1 + v;
      let tmp_2 = row.get_cloned(c);
      if tmp_2 < cand {
        let tmp_3 = row.set(c, cand);
        let tmp_4 = base + c;
        item_loop(v, w, base, c, tmp_3, dec.set(tmp_4, true), ())
      } else {
        item_loop(v, w, base, c, row, dec, ())
      }
    },
    sumbool::right => {
      (row, dec)
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Knapsack.knapsack_implem.items_loop
// Variant: uncurried
pub fn items_loop_1(xv: Array<Int63>, xw: Array<Int63>, n: Int63, C1: Int63, i: Int63, row: Array<Int63>, dec: Array<bool>) -> (Array<Int63>, Array<bool>) {
  items_loop(xv, xw, n, C1, i, row, dec, ())
}

// Rocq: Knapsack.knapsack_implem.items_loop (local: items_loop)
// Variant: uncurried, lifted
pub fn items_loop(xv: Array<Int63>, xw: Array<Int63>, n: Int63, C1: Int63, i: Int63, row: Array<Int63>, dec: Array<bool>, _H: ()) -> (Array<Int63>, Array<bool>) {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = xv.get_cloned(i);
      let tmp_2 = xw.get_cloned(i);
      let rd = item_loop_1(tmp_1, tmp_2, i * C1, C1, row, dec);
      let tmp_3 = i + int63!(1);
      let rd_clone = Clone::clone(&rd);
      items_loop(xv, xw, n, C1, tmp_3, fst::<Array<Int63>, Array<bool>>(rd_clone), snd::<Array<Int63>, Array<bool>>(rd), ())
    },
    sumbool::right => {
      std::mem::drop(xv);
      std::mem::drop(xw);
      (row, dec)
    },
  }
}

// Rocq: Knapsack.knapsack_implem.walk
// Variant: uncurried
pub fn walk_1(xw: Array<Int63>, dec: Array<bool>, C1: Int63, i: Int63, c: Int63, k: Int63, out: Array<Int63>) -> (Int63, Array<Int63>) {
  walk(xw, dec, C1, i, c, k, out, ())
}

// Rocq: Knapsack.knapsack_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(xw: Array<Int63>, dec: Array<bool>, C1: Int63, i: Int63, c: Int63, k: Int63, out: Array<Int63>, _H: ()) -> (Int63, Array<Int63>) {
  let tmp = int63!(0) < i;
  match bdec(tmp) {
    sumbool::left => {
      let j = i - int63!(1);
      let tmp_1 = dec.get_cloned(j * C1 + c);
      if tmp_1 {
        let tmp_2 = xw.get_cloned(j);
        let tmp_3 = c - tmp_2;
        let tmp_4 = k + int63!(1);
        let tmp_5 = out.set(k, j);
        walk(xw, dec, C1, j, tmp_3, tmp_4, tmp_5, ())
      } else {
        walk(xw, dec, C1, j, c, k, out, ())
      }
    },
    sumbool::right => {
      std::mem::drop(xw);
      std::mem::drop(dec);
      (k, out)
    },
  }
}

// Rocq: Knapsack.knapsack_implem.copy_loop
// Variant: uncurried
pub fn copy_loop_1(src: Array<Int63>, dst: Array<Int63>, m: Int63, j: Int63) -> Array<Int63> {
  copy_loop(src, dst, m, j, ())
}

// Rocq: Knapsack.knapsack_implem.copy_loop (local: copy_loop)
// Variant: uncurried, lifted
pub fn copy_loop(src: Array<Int63>, dst: Array<Int63>, m: Int63, j: Int63, _H: ()) -> Array<Int63> {
  let tmp = j < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = src.get_cloned(j);
      copy_loop(src, dst.set(j, tmp_1), m, j + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Knapsack.knapsack_implem.knapsack_impl
// Variant: uncurried
pub fn knapsack_impl(Cw: Int63, xv: Array<Int63>, xw: Array<Int63>) -> (Int63, Array<Int63>) {
  let n = xv.length();
  let C1 = Cw + int63!(1);
  let tmp = Array::<Int63>::make(C1, int63!(0));
  let tmp_1 = Array::<bool>::make(n * C1, false);
  let xw_clone = Clone::clone(&xw);
  let rd = items_loop_1(xv, xw_clone, n, C1, int63!(0), tmp, tmp_1);
  let rd_clone = Clone::clone(&rd);
  let tmp_2 = fst::<Array<Int63>, Array<bool>>(rd_clone);
  let bestv = tmp_2.get_cloned(Cw);
  std::mem::drop(tmp_2);
  let tmp_3 = snd::<Array<Int63>, Array<bool>>(rd);
  let tmp_4 = Array::<Int63>::make(n, int63!(0));
  let ko = walk_1(xw, tmp_3, C1, n, Cw, int63!(0), tmp_4);
  let ko_clone = Clone::clone(&ko);
  let k = fst::<Int63, Array<Int63>>(ko_clone);
  (bestv, copy_loop_1(snd::<Int63, Array<Int63>>(ko), Array::<Int63>::make(k, int63!(0)), k, int63!(0)))
}
