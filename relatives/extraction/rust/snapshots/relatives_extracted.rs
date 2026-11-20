#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = Int63;

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  if b1 {
    b2
  } else {
    false
  }
}

// Rocq: Relatives.relatives_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Relatives.relatives_implem.divout
// Variant: uncurried
pub fn divout_1(p: Int63, m: Int63) -> Int63 {
  divout(p, m, ())
}

// Rocq: Relatives.relatives_implem.divout (local: divout)
// Variant: uncurried, lifted
pub fn divout(p: Int63, m: Int63, _H: ()) -> Int63 {
  let tmp = m % p == int63!(0);
  let tmp_1 = andb(int63!(0) < m, int63!(1) < p);
  let tmp_2 = andb(tmp, tmp_1);
  match bdec(tmp_2) {
    sumbool::left => {
      let tmp_3 = m / p;
      divout(p, tmp_3, ())
    },
    sumbool::right => {
      m
    },
  }
}

// Rocq: Relatives.relatives_implem.outer
// Variant: uncurried
pub fn outer_1(p: Int63, m: Int63, res: Int63) -> Int63 {
  outer(p, m, res, ())
}

// Rocq: Relatives.relatives_implem.outer (local: outer)
// Variant: uncurried, lifted
pub fn outer(p: Int63, m: Int63, res: Int63, _H: ()) -> Int63 {
  let tmp = m / p;
  let tmp_1 = andb(p <= tmp, p < m);
  match bdec(tmp_1) {
    sumbool::left => {
      let tmp_2 = m % p;
      if tmp_2 == int63!(0) {
        let m_ = divout_1(p, m);
        outer(p + int63!(1), m_, res / p * (p - int63!(1)), ())
      } else {
        outer(p + int63!(1), m, res, ())
      }
    },
    sumbool::right => {
      if int63!(1) < m {
        res / m * (m - int63!(1))
      } else {
        res
      }
    },
  }
}

// Rocq: Relatives.relatives_implem.relatives_impl
pub fn relatives_impl(n: Int63) -> Int63 {
  if n <= int63!(1) {
    int63!(0)
  } else {
    outer_1(int63!(2), n, n)
  }
}
