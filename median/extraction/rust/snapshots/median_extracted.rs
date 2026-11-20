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

// Rocq: Median.median_implem.seed0
pub fn seed0() -> Int63 {
  int63!(88172645463325252)
}

// Rocq: Median.median_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Median.median_implem.lcg
pub fn lcg(s: Int63) -> Int63 {
  s * int63!(6364136223846793005) + int63!(1442695040888963407)
}

// Rocq: Median.median_implem.tst
// Variant: uncurried
pub fn tst(strict: bool, x: Int63, v: Int63) -> bool {
  if strict {
    v < x
  } else {
    v <= x
  }
}

// Rocq: Median.median_implem.swap_with
// Variant: uncurried
pub fn swap_with(y: Array<Int63>, i: Int63, j: Int63, v: Int63) -> Array<Int63> {
  let w = y.get_cloned(i);
  y.set(i, v).set(j, w)
}

// Rocq: Median.median_implem.part
// Variant: uncurried
pub fn part_1(strict: bool, x: Int63, hi: Int63, y: Array<Int63>, i: Int63, j: Int63) -> (Array<Int63>, Int63) {
  part(strict, x, hi, y, i, j, ())
}

// Rocq: Median.median_implem.part (local: part)
// Variant: uncurried, lifted
pub fn part(strict: bool, x: Int63, hi: Int63, y: Array<Int63>, i: Int63, j: Int63, _H: ()) -> (Array<Int63>, Int63) {
  let tmp = j < hi;
  match bdec(tmp) {
    sumbool::left => {
      let v = y.get_cloned(j);
      if tst(strict, x, v) {
        part(strict, x, hi, swap_with(y, i, j, v), i + int63!(1), j + int63!(1), ())
      } else {
        part(strict, x, hi, y, i, j + int63!(1), ())
      }
    },
    sumbool::right => {
      (y, i)
    },
  }
}

// Rocq: Median.median_implem.sel
// Variant: uncurried
pub fn sel_1(k: Int63, y: Array<Int63>, lo: Int63, hi: Int63, seed: Int63) -> Array<Int63> {
  sel(k, y, lo, hi, seed, ())
}

// Rocq: Median.median_implem.sel (local: sel)
// Variant: uncurried, lifted
pub fn sel(k: Int63, y: Array<Int63>, lo: Int63, hi: Int63, seed: Int63, _H: ()) -> Array<Int63> {
  let tmp = lo < hi;
  match bdec(tmp) {
    sumbool::left => {
      let s = lcg(seed);
      let tmp_1 = s >> int63!(17);
      let tmp_2 = hi - lo;
      let x = y.get_cloned(lo + tmp_1 % tmp_2);
      let tmp_3 = part_1(true, x, hi, y, lo, lo);
      match tmp_3 {
        (v68, v70) => {
          let tmp_4 = part_1(false, x, hi, v68, v70, v70);
          match tmp_4 {
            (v89, v91) => {
              if k < v70 {
                let tmp_5 = v70 < hi;
                match bdec(tmp_5) {
                  sumbool::left => {
                    sel(k, v89, lo, v70, s, ())
                  },
                  sumbool::right => {
                    v89
                  },
                }
              } else {
                if k < v91 {
                  v89
                } else {
                  let tmp_6 = lo < v91;
                  match bdec(tmp_6) {
                    sumbool::left => {
                      sel(k, v89, v91, hi, s, ())
                    },
                    sumbool::right => {
                      v89
                    },
                  }
                }
              }
            },
          }
        },
      }
    },
    sumbool::right => {
      y
    },
  }
}

// Rocq: Median.median_implem.maxl
// Variant: uncurried
pub fn maxl_1(y: Array<Int63>, k: Int63, j: Int63, acc: Int63) -> Int63 {
  maxl(y, k, j, acc, ())
}

// Rocq: Median.median_implem.maxl (local: maxl)
// Variant: uncurried, lifted
pub fn maxl(y: Array<Int63>, k: Int63, j: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = j < k;
  match bdec(tmp) {
    sumbool::left => {
      let v = y.get_cloned(j);
      let tmp_1 = j + int63!(1);
      let tmp_2 = if acc < v {
        v
      } else {
        acc
      };
      maxl(y, k, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      std::mem::drop(y);
      acc
    },
  }
}

// Rocq: Median.median_implem.median_impl
pub fn median_impl(x: Array<Int63>) -> f64 {
  let n = x.length();
  let k = n / int63!(2);
  let x_ref = &x;
  let tmp = x_ref.copy();
  let y = sel_1(k, tmp, int63!(0), n, __rocq_global_343);
  let u = y.get_cloned(k);
  let tmp_1 = n % int63!(2);
  if tmp_1 == int63!(1) {
    std::mem::drop(x);
    std::mem::drop(y);
    rocq_float64::of_uint63(u)
  } else {
    std::mem::drop(x);
    let tmp_2 = y.get_cloned(int63!(0));
    let w = maxl_1(y, k, int63!(1), tmp_2);
    rocq_float64::div(rocq_float64::of_uint63(w + u), rocq_float64::of_uint63(int63!(2)))
  }
}
const __rocq_global_343: Int63 = int63!(88172645463325252);