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

// Rocq: Primepower.primepower_implem.M
pub fn M() -> Int63 {
  int63!(1000000007)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.Uint63Axioms.is_zero
pub fn is_zero(i: Int63) -> bool {
  i == int63!(0)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.Uint63Axioms.is_even
pub fn is_even(i: Int63) -> bool {
  is_zero(i & int63!(1))
}

// Rocq: Primepower.primepower_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Primepower.primepower_implem.pow_loop
// Variant: uncurried
pub fn pow_loop_1(b_1: Int63, e: Int63, acc: Int63) -> Int63 {
  pow_loop(b_1, e, acc, ())
}

// Rocq: Primepower.primepower_implem.pow_loop (local: pow_loop)
// Variant: uncurried, lifted
pub fn pow_loop(b_1: Int63, e: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = int63!(0) < e;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = b_1 * b_1 % __rocq_global_104;
      let tmp_2 = e >> int63!(1);
      let tmp_3 = if is_even(e) {
        acc
      } else {
        acc * b_1 % __rocq_global_104
      };
      pow_loop(tmp_1, tmp_2, tmp_3, ())
    },
    sumbool::right => {
      acc
    },
  }
}

// Rocq: Primepower.primepower_implem.powmod
// Variant: uncurried
pub fn powmod(b_1: Int63, e: Int63) -> Int63 {
  pow_loop_1(b_1 % __rocq_global_104, e, int63!(1))
}

// Rocq: Primepower.primepower_implem.prod_loop
// Variant: uncurried
pub fn prod_loop_1(s: Array<Int63>, E: Int63, L: Int63, p: Int63, acc: Int63) -> Int63 {
  prod_loop(s, E, L, p, acc, ())
}

// Rocq: Primepower.primepower_implem.prod_loop (local: prod_loop)
// Variant: uncurried, lifted
pub fn prod_loop(s: Array<Int63>, E: Int63, L: Int63, p: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = s.get_cloned(p);
  let tmp_1 = int63!(0);
  let acc_ = if tmp == tmp_1 {
    acc
  } else {
    powmod(p, E) * acc % __rocq_global_104
  };
  let tmp_2 = L < p;
  match bdec(tmp_2) {
    sumbool::left => {
      prod_loop(s, E, L, p - int63!(1), acc_, ())
    },
    sumbool::right => {
      std::mem::drop(s);
      acc_
    },
  }
}

// Rocq: Primepower.primepower_implem.cross_loop
// Variant: uncurried
pub fn cross_loop_1(i: Int63, R: Int63, j: Int63, s: Array<Int63>) -> Array<Int63> {
  cross_loop(i, R, j, s, ())
}

// Rocq: Primepower.primepower_implem.cross_loop (local: cross_loop)
// Variant: uncurried, lifted
pub fn cross_loop(i: Int63, R: Int63, j: Int63, s: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = j <= R;
  match bdec(tmp) {
    sumbool::left => {
      let j_ = j + i;
      let tmp_1 = j < j_;
      match bdec(tmp_1) {
        sumbool::left => {
          cross_loop(i, R, j_, s.set(j, int63!(0)), ())
        },
        sumbool::right => {
          s.set(j, int63!(0))
        },
      }
    },
    sumbool::right => {
      s
    },
  }
}

// Rocq: Primepower.primepower_implem.sieve_loop
// Variant: uncurried
pub fn sieve_loop_1(R: Int63, i: Int63, s: Array<Int63>) -> Array<Int63> {
  sieve_loop(R, i, s, ())
}

// Rocq: Primepower.primepower_implem.sieve_loop (local: sieve_loop)
// Variant: uncurried, lifted
pub fn sieve_loop(R: Int63, i: Int63, s: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i * i <= R;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = s.get_cloned(i);
      let tmp_2 = int63!(0);
      let s_ = if tmp_1 == tmp_2 {
        s
      } else {
        let tmp_3 = i * i;
        cross_loop_1(i, R, tmp_3, s)
      };
      let tmp_4 = i + int63!(1);
      let tmp_5 = i < tmp_4;
      match bdec(tmp_5) {
        sumbool::left => {
          sieve_loop(R, i + int63!(1), s_, ())
        },
        sumbool::right => {
          s_
        },
      }
    },
    sumbool::right => {
      s
    },
  }
}

// Rocq: Primepower.primepower_implem.sieve
pub fn sieve(R: Int63) -> Array<Int63> {
  let tmp = R + int63!(1);
  sieve_loop_1(R, int63!(2), Array::<Int63>::make(tmp, int63!(1)).set(int63!(0), int63!(0)).set(int63!(1), int63!(0)))
}

// Rocq: Primepower.primepower_implem.primepower_impl
// Variant: uncurried
pub fn primepower_impl(E: Int63, L: Int63, R: Int63) -> Int63 {
  if R < L {
    int63!(1)
  } else {
    prod_loop_1(sieve(R), E, L, R, int63!(1))
  }
}
const __rocq_global_104: Int63 = int63!(1000000007);