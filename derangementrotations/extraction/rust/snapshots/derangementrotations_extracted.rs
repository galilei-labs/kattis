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

// Rocq: Derangementrotations.derangementrotations_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Derangementrotations.derangementrotations_implem.pow_loop
// Variant: uncurried
pub fn pow_loop_1(p: Int63, base: Int63, e: Int63, acc: Int63) -> Int63 {
  pow_loop(p, base, e, acc, ())
}

// Rocq: Derangementrotations.derangementrotations_implem.pow_loop (local: pow_loop)
// Variant: uncurried, lifted
pub fn pow_loop(p: Int63, base: Int63, e: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = e == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      acc
    },
    sumbool::right => {
      let tmp_1 = base * base % p;
      let tmp_2 = e / int63!(2);
      let tmp_3 = e % int63!(2);
      let tmp_4 = int63!(0);
      let tmp_5 = if tmp_3 == tmp_4 {
        acc
      } else {
        acc * base % p
      };
      pow_loop(p, tmp_1, tmp_2, tmp_5, ())
    },
  }
}

// Rocq: Derangementrotations.derangementrotations_implem.pow2mod
// Variant: uncurried
pub fn pow2mod(p: Int63, g: Int63) -> Int63 {
  pow_loop_1(p, int63!(2), g, int63!(1))
}

// Rocq: Derangementrotations.derangementrotations_implem.gcd_loop
// Variant: uncurried
pub fn gcd_loop_1(a_1: Int63, b_1: Int63) -> Int63 {
  gcd_loop(a_1, b_1, ())
}

// Rocq: Derangementrotations.derangementrotations_implem.gcd_loop (local: gcd_loop)
// Variant: uncurried, lifted
pub fn gcd_loop(a_1: Int63, b_1: Int63, _H: ()) -> Int63 {
  let tmp = b_1 == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      a_1
    },
    sumbool::right => {
      let tmp_1 = a_1 % b_1;
      gcd_loop(b_1, tmp_1, ())
    },
  }
}

// Rocq: Derangementrotations.derangementrotations_implem.gcd63
// Variant: uncurried
pub fn gcd63(a_1: Int63, b_1: Int63) -> Int63 {
  gcd_loop_1(a_1, b_1)
}

// Rocq: Derangementrotations.derangementrotations_implem.sum_loop
// Variant: uncurried
pub fn sum_loop_1(n: Int63, m: Int63, p: Int63, d: Int63, acc: Int63) -> Int63 {
  sum_loop(n, m, p, d, acc, ())
}

// Rocq: Derangementrotations.derangementrotations_implem.sum_loop (local: sum_loop)
// Variant: uncurried, lifted
pub fn sum_loop(n: Int63, m: Int63, p: Int63, d: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = d < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = d + int63!(1);
      let tmp_2 = (acc + (m - d) * ((pow2mod(p, gcd63(d, n)) + p - int63!(2)) % p) % p) % p;
      sum_loop(n, m, p, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      acc
    },
  }
}

// Rocq: Derangementrotations.derangementrotations_implem.derangement_rotations_impl
// Variant: uncurried
pub fn derangement_rotations_impl(n: Int63, p: Int63) -> Int63 {
  let tmp = n - int63!(1);
  sum_loop_1(n, tmp, p, int63!(1), int63!(0))
}
