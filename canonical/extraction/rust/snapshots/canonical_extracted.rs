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

// Rocq: Canonical.canonical_implem.bound
pub fn bound(c: Array<Int63>) -> Int63 {
  let n = c.length();
  let tmp = c.get_cloned(n - int63!(1));
  let tmp_1 = c.get_cloned(n - int63!(2));
  std::mem::drop(c);
  tmp + tmp_1
}

// Rocq: Canonical.canonical_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Canonical.canonical_implem.kupd
// Variant: uncurried
pub fn kupd(c: Array<Int63>, n: Int63, x: Int63, k: Int63) -> Int63 {
  let tmp = k + int63!(1);
  if tmp < n {
    let tmp_1 = c.get_cloned(k + int63!(1));
    if tmp_1 <= x {
      std::mem::drop(c);
      k + int63!(1)
    } else {
      std::mem::drop(c);
      k
    }
  } else {
    std::mem::drop(c);
    k
  }
}

// Rocq: Canonical.canonical_implem.minloop
// Variant: uncurried
pub fn minloop_1(c: Array<Int63>, t: Array<Int63>, x: Int63, hi: Int63, j: Int63, acc: Int63) -> Int63 {
  minloop(c, t, x, hi, j, acc, ())
}

// Rocq: Canonical.canonical_implem.minloop (local: minloop)
// Variant: uncurried, lifted
pub fn minloop(c: Array<Int63>, t: Array<Int63>, x: Int63, hi: Int63, j: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = j < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = c.get_cloned(j);
      let v = t.get_cloned(x - tmp_1);
      let tmp_2 = j + int63!(1);
      let tmp_3 = if v < acc {
        v
      } else {
        acc
      };
      minloop(c, t, x, hi, tmp_2, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(c);
      std::mem::drop(t);
      acc
    },
  }
}

// Rocq: Canonical.canonical_implem.outer
// Variant: uncurried
pub fn outer_1(c: Array<Int63>, n: Int63, B: Int63, x: Int63, k: Int63, t: Array<Int63>, g: Array<Int63>) -> bool {
  outer(c, n, B, x, k, t, g, ())
}

// Rocq: Canonical.canonical_implem.outer (local: outer)
// Variant: uncurried, lifted
pub fn outer(c: Array<Int63>, n: Int63, B: Int63, x: Int63, k: Int63, t: Array<Int63>, g: Array<Int63>, _H: ()) -> bool {
  let tmp = x < B;
  match bdec(tmp) {
    sumbool::left => {
      let c_clone = Clone::clone(&c);
      let k_ = kupd(c_clone, n, x, k);
      let tmp_1 = c.get_cloned(k_);
      let tmp_2 = g.get_cloned(x - tmp_1);
      let gx = tmp_2 + int63!(1);
      let tmp_3 = k_ + int63!(1);
      let tmp_4 = t.get_cloned(x - int63!(1));
      let c_clone_1 = Clone::clone(&c);
      let t_clone = Clone::clone(&t);
      let tx = minloop_1(c_clone_1, t_clone, x, tmp_3, int63!(1), tmp_4) + int63!(1);
      if tx < gx {
        std::mem::drop(c);
        std::mem::drop(t);
        std::mem::drop(g);
        false
      } else {
        outer(c, n, B, x + int63!(1), k_, t.set(x, tx), g.set(x, gx), ())
      }
    },
    sumbool::right => {
      std::mem::drop(c);
      std::mem::drop(t);
      std::mem::drop(g);
      true
    },
  }
}

// Rocq: Canonical.canonical_implem.run
pub fn run_1(c: Array<Int63>) -> bool {
  let c_clone = Clone::clone(&c);
  let B = bound(c_clone);
  let tmp = c.length();
  let tmp_1 = Array::<Int63>::make(B, int63!(0));
  let tmp_2 = Array::<Int63>::make(B, int63!(0));
  outer_1(c, tmp, B, int63!(1), int63!(0), tmp_1, tmp_2)
}

// Rocq: Canonical.canonical_implem.canonical_impl
pub fn canonical_impl(c: Array<Int63>) -> bool {
  run_1(c)
}
