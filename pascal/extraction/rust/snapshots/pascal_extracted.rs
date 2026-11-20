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

// Rocq: Pascal.pascal_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Pascal.pascal_implem.sd_loop
// Variant: uncurried
pub fn sd_loop_1(n: Int63, p: Int63) -> Int63 {
  sd_loop(n, p, ())
}

// Rocq: Pascal.pascal_implem.sd_loop (local: sd_loop)
// Variant: uncurried, lifted
pub fn sd_loop(n: Int63, p: Int63, _H: ()) -> Int63 {
  let tmp = andb(p < n, p * p <= n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = n % p;
      if tmp_1 == int63!(0) {
        p
      } else {
        sd_loop(n, p + int63!(1), ())
      }
    },
    sumbool::right => {
      n
    },
  }
}

// Rocq: Pascal.pascal_implem.pascal_impl
pub fn pascal_impl(n: Int63) -> Int63 {
  let tmp = sd_loop_1(n, int63!(2));
  let tmp_1 = n / tmp;
  n - tmp_1
}
