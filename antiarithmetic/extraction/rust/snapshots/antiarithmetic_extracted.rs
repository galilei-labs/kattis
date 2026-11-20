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

// Rocq: Antiarithmetic.antiarithmetic_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
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

// Rocq: Antiarithmetic.antiarithmetic_implem.inner
// Variant: uncurried
pub fn inner_1(S: Array<Int63>, R: Array<Int63>, rS: Int63, lS: Int63, rR: Int63, lR: Int63, aS: Int63, aR: Int63, rem: Int63) -> bool {
  inner(S, R, rS, lS, rR, lR, aS, aR, rem, ())
}

// Rocq: Antiarithmetic.antiarithmetic_implem.inner (local: inner)
// Variant: uncurried, lifted
pub fn inner(S: Array<Int63>, R: Array<Int63>, rS: Int63, lS: Int63, rR: Int63, lR: Int63, aS: Int63, aR: Int63, rem: Int63, _H: ()) -> bool {
  let tmp = S.get_cloned(aS);
  let tmp_1 = tmp >> rS;
  let tmp_2 = S.get_cloned(aS + int63!(1));
  let tmp_3 = tmp_1 | tmp_2 << lS;
  let tmp_4 = R.get_cloned(aR);
  let tmp_5 = tmp_4 >> rR;
  let tmp_6 = R.get_cloned(aR + int63!(1));
  let w = tmp_3 ^ (tmp_5 | tmp_6 << lR);
  let tmp_7 = rem <= int63!(63);
  match bdec(tmp_7) {
    sumbool::left => {
      std::mem::drop(R);
      std::mem::drop(S);
      negb(w & (int63!(1) << rem) - int63!(1) == int63!(0))
    },
    sumbool::right => {
      if w == int63!(0) {
        inner(S, R, rS, lS, rR, lR, aS + int63!(1), aR + int63!(1), rem - int63!(63), ())
      } else {
        std::mem::drop(R);
        std::mem::drop(S);
        true
      }
    },
  }
}

// Rocq: Antiarithmetic.antiarithmetic_implem.setbit
// Variant: uncurried
pub fn setbit(t: Array<Int63>, v: Int63) -> Array<Int63> {
  let a_1 = v / int63!(63);
  let tmp = t.get_cloned(a_1);
  t.set(a_1, tmp | int63!(1) << v % int63!(63))
}

// Rocq: Antiarithmetic.antiarithmetic_implem.scan
// Variant: uncurried
pub fn scan_1(x: Array<Int63>, n: Int63, S: Array<Int63>, R: Array<Int63>, pos: Int63) -> bool {
  scan(x, n, S, R, pos, ())
}

// Rocq: Antiarithmetic.antiarithmetic_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(x: Array<Int63>, n: Int63, S: Array<Int63>, R: Array<Int63>, pos: Int63, _H: ()) -> bool {
  let tmp = pos < n;
  match bdec(tmp) {
    sumbool::left => {
      let m = x.get_cloned(pos);
      let c = n - int63!(1) - m;
      let L = if m < c {
        m
      } else {
        c
      };
      let oS = m + int63!(1);
      let oR = n - m;
      let rS = oS % int63!(63);
      let rR = oR % int63!(63);
      let tmp_1 = int63!(63) - rS;
      let tmp_2 = int63!(63) - rR;
      let tmp_3 = oS / int63!(63);
      let tmp_4 = oR / int63!(63);
      let S_clone = Clone::clone(&S);
      let R_clone = Clone::clone(&R);
      if inner_1(S_clone, R_clone, rS, tmp_1, rR, tmp_2, tmp_3, tmp_4, L) {
        std::mem::drop(x);
        std::mem::drop(S);
        std::mem::drop(R);
        false
      } else {
        scan(x, n, setbit(S, m), setbit(R, c), pos + int63!(1), ())
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(S);
      std::mem::drop(R);
      true
    },
  }
}

// Rocq: Antiarithmetic.antiarithmetic_implem.antiarithmetic_impl
pub fn antiarithmetic_impl(x: Array<Int63>) -> bool {
  let n = x.length();
  let k = n / int63!(63) + int63!(1);
  scan_1(x, n, Array::<Int63>::make(k, int63!(0)), Array::<Int63>::make(k, int63!(0)), int63!(0))
}
