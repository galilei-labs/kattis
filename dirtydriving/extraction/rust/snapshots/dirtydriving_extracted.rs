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

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  if b1 {
    b2
  } else {
    false
  }
}

// Rocq: Dirtydriving.dirtydriving_implem.split_ok
// Variant: uncurried
pub fn split_ok(lo: Int63, hi: Int63) -> bool {
  andb(lo < hi, int63!(1) < hi - lo)
}

// Rocq: Dirtydriving.dirtydriving_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Dirtydriving.dirtydriving_implem.midp
// Variant: uncurried
pub fn midp(lo: Int63, hi: Int63) -> Int63 {
  let tmp = hi - lo;
  lo + tmp / int63!(2)
}

// Rocq: Dirtydriving.dirtydriving_implem.take_left
// Variant: uncurried
pub fn take_left(a_1: Array<Int63>, mid: Int63, hi: Int63, i: Int63, j: Int63) -> bool {
  if i < mid {
    if j < hi {
      let tmp = a_1.get_cloned(i);
      let tmp_1 = a_1.get_cloned(j);
      std::mem::drop(a_1);
      tmp <= tmp_1
    } else {
      std::mem::drop(a_1);
      true
    }
  } else {
    std::mem::drop(a_1);
    false
  }
}

// Rocq: Dirtydriving.dirtydriving_implem.merge_loop
// Variant: uncurried
pub fn merge_loop_1(a_1: Array<Int63>, t: Array<Int63>, mid: Int63, hi: Int63, i: Int63, j: Int63, k: Int63) -> Array<Int63> {
  merge_loop(a_1, t, mid, hi, i, j, k, ())
}

// Rocq: Dirtydriving.dirtydriving_implem.merge_loop (local: merge_loop)
// Variant: uncurried, lifted
pub fn merge_loop(a_1: Array<Int63>, t: Array<Int63>, mid: Int63, hi: Int63, i: Int63, j: Int63, k: Int63, _H: ()) -> Array<Int63> {
  let tmp = k < hi;
  match bdec(tmp) {
    sumbool::left => {
      let a_clone = Clone::clone(&a_1);
      if take_left(a_clone, mid, hi, i, j) {
        let tmp_1 = a_1.get_cloned(i);
        merge_loop(a_1, t.set(k, tmp_1), mid, hi, i + int63!(1), j, k + int63!(1), ())
      } else {
        let tmp_2 = a_1.get_cloned(j);
        merge_loop(a_1, t.set(k, tmp_2), mid, hi, i, j + int63!(1), k + int63!(1), ())
      }
    },
    sumbool::right => {
      std::mem::drop(a_1);
      t
    },
  }
}

// Rocq: Dirtydriving.dirtydriving_implem.copy_loop
// Variant: uncurried
pub fn copy_loop_1(src: Array<Int63>, dst: Array<Int63>, hi: Int63, k: Int63) -> Array<Int63> {
  copy_loop(src, dst, hi, k, ())
}

// Rocq: Dirtydriving.dirtydriving_implem.copy_loop (local: copy_loop)
// Variant: uncurried, lifted
pub fn copy_loop(src: Array<Int63>, dst: Array<Int63>, hi: Int63, k: Int63, _H: ()) -> Array<Int63> {
  let tmp = k < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = src.get_cloned(k);
      copy_loop(src, dst.set(k, tmp_1), hi, k + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Dirtydriving.dirtydriving_implem.msort
// Variant: uncurried
pub fn msort_1(a_1: Array<Int63>, t: Array<Int63>, lo: Int63, hi: Int63) -> (Array<Int63>, Array<Int63>) {
  msort(a_1, t, lo, hi, ())
}

// Rocq: Dirtydriving.dirtydriving_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(a_1: Array<Int63>, t: Array<Int63>, lo: Int63, hi: Int63, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = split_ok(lo, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = midp(lo, hi);
      let tmp_2 = msort(a_1, t, lo, tmp_1, ());
      match &tmp_2 {
        (t1, a1) => {
          let tmp_3 = midp(lo, hi);
          let tmp_4 = ();
          let t1_clone = Clone::clone(t1);
          let a1_clone = Clone::clone(a1);
          std::mem::drop(tmp_2);
          let tmp_5 = msort(t1_clone, a1_clone, tmp_3, hi, tmp_4);
          match tmp_5 {
            (v63, v65) => {
              let t2 = &v63;
              let tmp_6 = midp(lo, hi);
              let tmp_7 = midp(lo, hi);
              let t2_clone = Clone::clone(t2);
              let t3 = merge_loop_1(t2_clone, v65, tmp_6, hi, lo, tmp_7, lo);
              let t3_clone = Clone::clone(&t3);
              (copy_loop_1(t3_clone, v63, hi, lo), t3)
            },
          }
        },
      }
    },
    sumbool::right => {
      (a_1, t)
    },
  }
}

// Rocq: Dirtydriving.dirtydriving_implem.need
// Variant: uncurried
pub fn need(p: Int63, s0: Int63, x: Int63, k: Int63) -> Int63 {
  let t = p * (k + int63!(1)) + s0;
  if x < t {
    t - x
  } else {
    int63!(0)
  }
}

// Rocq: Dirtydriving.dirtydriving_implem.max_loop
// Variant: uncurried
pub fn max_loop_1(s: Array<Int63>, p: Int63, s0: Int63, n: Int63, k: Int63, acc: Int63) -> Int63 {
  max_loop(s, p, s0, n, k, acc, ())
}

// Rocq: Dirtydriving.dirtydriving_implem.max_loop (local: max_loop)
// Variant: uncurried, lifted
pub fn max_loop(s: Array<Int63>, p: Int63, s0: Int63, n: Int63, k: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = k < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = s.get_cloned(k);
      let v = need(p, s0, tmp_1, k);
      let tmp_2 = k + int63!(1);
      let tmp_3 = if acc < v {
        v
      } else {
        acc
      };
      max_loop(s, p, s0, n, tmp_2, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(s);
      acc
    },
  }
}

// Rocq: Dirtydriving.dirtydriving_implem.dirtydriving_impl
// Variant: uncurried
pub fn dirtydriving_impl(p: Int63, d: Array<Int63>) -> Int63 {
  let n = d.length();
  let s = fst::<Array<Int63>, Array<Int63>>(msort_1(d, Array::<Int63>::make(n, int63!(0)), int63!(0), n));
  let tmp = s.get_cloned(int63!(0));
  max_loop_1(s, p, tmp, n, int63!(0), int63!(0))
}
