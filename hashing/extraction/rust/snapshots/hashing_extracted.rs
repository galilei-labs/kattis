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

pub type char63 = Int63;

// Rocq: Hashing.hashing_implem.P61
pub fn P61() -> Int63 {
  int63!(2305843009213693951)
}

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: rocq_string::RocqString) -> Int63 {
  let tmp = v0.length();
  std::mem::drop(v0);
  tmp
}

// Rocq: Hashing.hashing_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Hashing.hashing_implem.addmod
// Variant: uncurried
pub fn addmod(a_1: Int63, b_1: Int63) -> Int63 {
  let s = a_1 + b_1;
  if __rocq_global_81 <= s {
    s - __rocq_global_81
  } else {
    s
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mulc
// Variant: uncurried
pub fn mulc(x: Int63, x_1: Int63) -> (Int63, Int63) {
  (x.mulc_high(x_1), x.mulc_low(x_1))
}

// Rocq: Hashing.hashing_implem.mulmod
// Variant: uncurried
pub fn mulmod(a_1: Int63, b_1: Int63) -> Int63 {
  let tmp = mulc(a_1, b_1);
  match tmp {
    (v9, v11) => {
      let s = (v9 << int63!(2)) + (v11 >> int63!(61)) + (v11 & __rocq_global_81);
      let t = (s >> int63!(61)) + (s & __rocq_global_81);
      if __rocq_global_81 <= t {
        t - __rocq_global_81
      } else {
        t
      }
    },
  }
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: rocq_string::RocqString, v1: Int63) -> Int63 {
  let tmp = v0.get(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Hashing.hashing_implem.pre_loop
// Variant: uncurried
pub fn pre_loop_1(r: Int63, s: rocq_string::RocqString, n: Int63, i: Int63, t: Array<Int63>, acc: Int63) -> Array<Int63> {
  pre_loop(r, s, n, i, t, acc, ())
}

// Rocq: Hashing.hashing_implem.pre_loop (local: pre_loop)
// Variant: uncurried, lifted
pub fn pre_loop(r: Int63, s: rocq_string::RocqString, n: Int63, i: Int63, t: Array<Int63>, acc: Int63, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = mulmod(acc, r);
      let s_clone = Clone::clone(&s);
      let acc_ = addmod(tmp_1, get(s_clone, i));
      pre_loop(r, s, n, i + int63!(1), t.set(i + int63!(1), acc_), acc_, ())
    },
    sumbool::right => {
      std::mem::drop(s);
      t
    },
  }
}

// Rocq: Hashing.hashing_implem.prefix_hashes
// Variant: uncurried
pub fn prefix_hashes(r: Int63, s: rocq_string::RocqString, n: Int63) -> Array<Int63> {
  let tmp = n + int63!(1);
  pre_loop_1(r, s, n, int63!(0), Array::<Int63>::make(tmp, int63!(0)), int63!(0))
}

// Rocq: Hashing.hashing_implem.pow_loop
// Variant: uncurried
pub fn pow_loop_1(r: Int63, n: Int63, i: Int63, t: Array<Int63>, acc: Int63) -> Array<Int63> {
  pow_loop(r, n, i, t, acc, ())
}

// Rocq: Hashing.hashing_implem.pow_loop (local: pow_loop)
// Variant: uncurried, lifted
pub fn pow_loop(r: Int63, n: Int63, i: Int63, t: Array<Int63>, acc: Int63, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let acc_ = mulmod(acc, r);
      pow_loop(r, n, i + int63!(1), t.set(i + int63!(1), acc_), acc_, ())
    },
    sumbool::right => {
      t
    },
  }
}

// Rocq: Hashing.hashing_implem.powers
// Variant: uncurried
pub fn powers(r: Int63, n: Int63) -> Array<Int63> {
  let tmp = n + int63!(1);
  pow_loop_1(r, n, int63!(0), Array::<Int63>::make(tmp, int63!(1)), int63!(1))
}

// Rocq: Hashing.hashing_implem.submod
// Variant: uncurried
pub fn submod(a_1: Int63, b_1: Int63) -> Int63 {
  if b_1 <= a_1 {
    a_1 - b_1
  } else {
    a_1 + __rocq_global_81 - b_1
  }
}

// Rocq: Hashing.hashing_implem.hash
// Variant: uncurried
pub fn hash(pre: Array<Int63>, pw: Array<Int63>, L: Int63, R: Int63) -> Int63 {
  let k = pw.get_cloned(R - L);
  std::mem::drop(pw);
  let tmp = pre.get_cloned(R);
  let tmp_1 = pre.get_cloned(L);
  std::mem::drop(pre);
  addmod(submod(tmp, mulmod(tmp_1, k)), k)
}

// Rocq: Hashing.hashing_implem.q_loop
// Variant: uncurried
pub fn q_loop_1(pre: Array<Int63>, pw: Array<Int63>, xl: Array<Int63>, xr: Array<Int63>, q: Int63, j: Int63, out: Array<Int63>) -> Array<Int63> {
  q_loop(pre, pw, xl, xr, q, j, out, ())
}

// Rocq: Hashing.hashing_implem.q_loop (local: q_loop)
// Variant: uncurried, lifted
pub fn q_loop(pre: Array<Int63>, pw: Array<Int63>, xl: Array<Int63>, xr: Array<Int63>, q: Int63, j: Int63, out: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = j < q;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = j + int63!(1);
      let tmp_2 = xl.get_cloned(j);
      let tmp_3 = xr.get_cloned(j);
      let pre_clone = Clone::clone(&pre);
      let pw_clone = Clone::clone(&pw);
      q_loop(pre, pw, xl, xr, q, tmp_1, out.set(j, hash(pre_clone, pw_clone, tmp_2, tmp_3)), ())
    },
    sumbool::right => {
      std::mem::drop(pre);
      std::mem::drop(pw);
      std::mem::drop(xl);
      std::mem::drop(xr);
      out
    },
  }
}

// Rocq: Hashing.hashing_implem.hashes_impl
// Variant: uncurried
pub fn hashes_impl(r: Int63, s: rocq_string::RocqString, xl: Array<Int63>, xr: Array<Int63>) -> Array<Int63> {
  let s_clone = Clone::clone(&s);
  let n = length(s_clone);
  let pre = prefix_hashes(r, s, n);
  let pw = powers(r, n);
  let q = xl.length();
  let tmp = Array::<Int63>::make(q, int63!(0));
  q_loop_1(pre, pw, xl, xr, q, int63!(0), tmp)
}
const __rocq_global_81: Int63 = int63!(2305843009213693951);