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

// Rocq: Ada.ada_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Init.Datatypes.orb
// Variant: uncurried
pub fn orb(b1: bool, b2: bool) -> bool {
  if b1 {
    true
  } else {
    b2
  }
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b_1: bool) -> bool {
  if b_1 {
    false
  } else {
    true
  }
}

// Rocq: Ada.ada_implem.row_loop
// Variant: uncurried
pub fn row_loop_1(m: Int63, j: Int63, t: Array<Int63>, nz: bool) -> (Array<Int63>, bool) {
  row_loop(m, j, t, nz, ())
}

// Rocq: Ada.ada_implem.row_loop (local: row_loop)
// Variant: uncurried, lifted
pub fn row_loop(m: Int63, j: Int63, t: Array<Int63>, nz: bool, _H: ()) -> (Array<Int63>, bool) {
  let tmp = j < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = t.get_cloned(j + int63!(1));
      let tmp_2 = t.get_cloned(j);
      let x = tmp_1 - tmp_2;
      row_loop(m, j + int63!(1), t.set(j, x), orb(nz, negb(x == int63!(0))), ())
    },
    sumbool::right => {
      (t, nz)
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

// Rocq: Ada.ada_implem.rows_loop
// Variant: uncurried
pub fn rows_loop_1(n: Int63, k: Int63, t: Array<Int63>, d: Int63) -> (Array<Int63>, Int63) {
  rows_loop(n, k, t, d, ())
}

// Rocq: Ada.ada_implem.rows_loop (local: rows_loop)
// Variant: uncurried, lifted
pub fn rows_loop(n: Int63, k: Int63, t: Array<Int63>, d: Int63, _H: ()) -> (Array<Int63>, Int63) {
  let tmp = k < n;
  match bdec(tmp) {
    sumbool::left => {
      let r = row_loop_1(n - k, int63!(0), t, false);
      let tmp_1 = k + int63!(1);
      let r_clone = Clone::clone(&r);
      let tmp_2 = fst::<Array<Int63>, bool>(r_clone);
      let tmp_3 = if snd::<Array<Int63>, bool>(r) {
        k
      } else {
        d
      };
      rows_loop(n, tmp_1, tmp_2, tmp_3, ())
    },
    sumbool::right => {
      (t, d)
    },
  }
}

// Rocq: Ada.ada_implem.acopy
pub fn acopy(t: Array<Int63>) -> Array<Int63> {
  let t_ref = &t;
  let tmp = t_ref.copy();
  std::mem::drop(t);
  tmp
}

// Rocq: Ada.ada_implem.sum_loop
// Variant: uncurried
pub fn sum_loop_1(t: Array<Int63>, top: Int63, e: Int63, k: Int63, acc: Int63) -> Int63 {
  sum_loop(t, top, e, k, acc, ())
}

// Rocq: Ada.ada_implem.sum_loop (local: sum_loop)
// Variant: uncurried, lifted
pub fn sum_loop(t: Array<Int63>, top: Int63, e: Int63, k: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = k < e;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = k + int63!(1);
      let tmp_2 = t.get_cloned(top - k);
      sum_loop(t, top, e, tmp_1, acc + tmp_2, ())
    },
    sumbool::right => {
      std::mem::drop(t);
      acc
    },
  }
}

// Rocq: Ada.ada_implem.ada_impl
pub fn ada_impl(a_1: Array<Int63>) -> (Int63, Int63) {
  let n = a_1.length();
  let tmp = rows_loop_1(n, int63!(1), acopy(a_1), int63!(0));
  match tmp {
    (v22, v24) => {
      let tmp_1 = n - int63!(1);
      let tmp_2 = v24 + int63!(1);
      (v24, sum_loop_1(v22, tmp_1, tmp_2, int63!(0), int63!(0)))
    },
  }
}
