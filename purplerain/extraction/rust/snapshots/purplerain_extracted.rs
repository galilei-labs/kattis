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

pub type char63 = Int63;

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: rocq_string::RocqString) -> Int63 {
  let tmp = v0.length();
  std::mem::drop(v0);
  tmp
}

// Rocq: Purplerain.purplerain_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: rocq_string::RocqString, v1: Int63) -> Int63 {
  let tmp = v0.get(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Purplerain.purplerain_implem.scan
// Variant: uncurried
pub fn scan_1(x: rocq_string::RocqString, n: Int63, k: Int63, p: Int63, mx: Int63, imx: Int63, mn: Int63, imn: Int63) -> (Int63, Int63) {
  scan(x, n, k, p, mx, imx, mn, imn, ())
}

// Rocq: Purplerain.purplerain_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(x: rocq_string::RocqString, n: Int63, k: Int63, p: Int63, mx: Int63, imx: Int63, mn: Int63, imn: Int63, _H: ()) -> (Int63, Int63) {
  let tmp = k < n;
  match bdec(tmp) {
    sumbool::left => {
      let x_clone = Clone::clone(&x);
      let tmp_1 = get(x_clone, k);
      let tmp_2 = int63!(82);
      let p_ = if tmp_1 == tmp_2 {
        p + int63!(1)
      } else {
        p - int63!(1)
      };
      let k_ = k + int63!(1);
      if mx < p_ {
        scan(x, n, k_, p_, p_, k_, mn, imn, ())
      } else {
        if p_ < mn {
          scan(x, n, k_, p_, mx, imx, p_, k_, ())
        } else {
          scan(x, n, k_, p_, mx, imx, mn, imn, ())
        }
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      (imx, imn)
    },
  }
}

// Rocq: Purplerain.purplerain_implem.purplerain_impl
pub fn purplerain_impl(x: rocq_string::RocqString) -> (Int63, Int63) {
  let x_clone = Clone::clone(&x);
  let n = length(x_clone);
  let tmp = scan_1(x, n, int63!(0), n, n, int63!(0), n, int63!(0));
  match tmp {
    (v31, v33) => {
      if v31 < v33 {
        (v31 + int63!(1), v33)
      } else {
        (v33 + int63!(1), v31)
      }
    },
  }
}
