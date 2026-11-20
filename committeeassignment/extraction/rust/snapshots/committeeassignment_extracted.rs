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

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<std::cmp::Ordering>; };

pub type uint = Int63;

// Rocq: Committeeassignment.committeeassignment_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Strings.PrimString.compare
// Variant: uncurried
pub fn compare(v0: rocq_string::RocqString, v1: rocq_string::RocqString) -> std::cmp::Ordering {
  let tmp = v0.compare(&v1);
  std::mem::drop(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Committeeassignment.committeeassignment_implem.midp
// Variant: uncurried
pub fn midp(lo: Int63, hi: Int63) -> Int63 {
  let tmp = hi - lo;
  lo + tmp / int63!(2)
}

// Rocq: Committeeassignment.committeeassignment_implem.lb
// Variant: uncurried
pub fn lb_1(K: Array<rocq_string::RocqString>, s: rocq_string::RocqString, lo: Int63, hi: Int63) -> Int63 {
  lb(K, s, lo, hi, ())
}

// Rocq: Committeeassignment.committeeassignment_implem.lb (local: lb)
// Variant: uncurried, lifted
pub fn lb(K: Array<rocq_string::RocqString>, s: rocq_string::RocqString, lo: Int63, hi: Int63, _H: ()) -> Int63 {
  let tmp = lo < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = midp(lo, hi);
      let K_ref = &K;
      let tmp_2 = K_ref.get_cloned(tmp_1);
      let s_clone = Clone::clone(&s);
      match compare(tmp_2, s_clone) {
        std::cmp::Ordering::Equal => {
          let tmp_3 = midp(lo, hi);
          lb(K, s, lo, tmp_3, ())
        },
        std::cmp::Ordering::Less => {
          lb(K, s, midp(lo, hi) + int63!(1), hi, ())
        },
        std::cmp::Ordering::Greater => {
          let tmp_4 = midp(lo, hi);
          lb(K, s, lo, tmp_4, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(K);
      std::mem::drop(s);
      lo
    },
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.look
// Variant: uncurried
pub fn look(K: Array<rocq_string::RocqString>, p: Int63, s: rocq_string::RocqString) -> Int63 {
  lb_1(K, s, int63!(0), p)
}

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  if b1 {
    b2
  } else {
    false
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.is_eq
pub fn is_eq(c: std::cmp::Ordering) -> bool {
  match c {
    std::cmp::Ordering::Equal => {
      true
    },
    std::cmp::Ordering::Less => {
      false
    },
    std::cmp::Ordering::Greater => {
      false
    },
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.shift
// Variant: uncurried
pub fn shift_1(K: Array<rocq_string::RocqString>, t: Int63, j: Int63) -> Array<rocq_string::RocqString> {
  shift(K, t, j, ())
}

// Rocq: Committeeassignment.committeeassignment_implem.shift (local: shift)
// Variant: uncurried, lifted
pub fn shift(K: Array<rocq_string::RocqString>, t: Int63, j: Int63, _H: ()) -> Array<rocq_string::RocqString> {
  let tmp = t < j;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = j - int63!(1);
      let K_ref = &K;
      let tmp_2 = K_ref.get_cloned(tmp_1);
      shift(K.set(j, tmp_2), t, j - int63!(1), ())
    },
    sumbool::right => {
      K
    },
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.insert
// Variant: uncurried
pub fn insert(K: Array<rocq_string::RocqString>, p: Int63, s: rocq_string::RocqString) -> (Array<rocq_string::RocqString>, Int63) {
  let K_clone = Clone::clone(&K);
  let s_clone = Clone::clone(&s);
  let t = look(K_clone, p, s_clone);
  let tmp = t < p;
  let K_ref = &K;
  let tmp_1 = K_ref.get_cloned(t);
  let s_clone_1 = Clone::clone(&s);
  let tmp_2 = is_eq(compare(tmp_1, s_clone_1));
  if andb(tmp, tmp_2) {
    std::mem::drop(s);
    (K, p)
  } else {
    (shift_1(K, t, p).set(t, s), p + int63!(1))
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.build
// Variant: uncurried
pub fn build_1(y: Array<rocq_string::RocqString>, z: Array<rocq_string::RocqString>, m: Int63, i: Int63, K: Array<rocq_string::RocqString>, p: Int63) -> (Array<rocq_string::RocqString>, Int63) {
  build(y, z, m, i, K, p, ())
}

// Rocq: Committeeassignment.committeeassignment_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(y: Array<rocq_string::RocqString>, z: Array<rocq_string::RocqString>, m: Int63, i: Int63, K: Array<rocq_string::RocqString>, p: Int63, _H: ()) -> (Array<rocq_string::RocqString>, Int63) {
  let tmp = i < m;
  match bdec(tmp) {
    sumbool::left => {
      let y_ref = &y;
      let tmp_1 = y_ref.get_cloned(i);
      let tmp_2 = insert(K, p, tmp_1);
      match &tmp_2 {
        (p1, K1) => {
          let z_ref = &z;
          let tmp_3 = z_ref.get_cloned(i);
          let p1_clone = Clone::clone(p1);
          let K1_clone = Clone::clone(K1);
          std::mem::drop(tmp_2);
          let tmp_4 = insert(p1_clone, K1_clone, tmp_3);
          match tmp_4 {
            (v49, v51) => {
              build(y, z, m, i + int63!(1), v49, v51, ())
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(y);
      std::mem::drop(z);
      (K, p)
    },
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.fill
// Variant: uncurried
pub fn fill_1(y: Array<rocq_string::RocqString>, z: Array<rocq_string::RocqString>, K: Array<rocq_string::RocqString>, p: Int63, m: Int63, i: Int63, tbl: Array<bool>) -> Array<bool> {
  fill(y, z, K, p, m, i, tbl, ())
}

// Rocq: Committeeassignment.committeeassignment_implem.fill (local: fill)
// Variant: uncurried, lifted
pub fn fill(y: Array<rocq_string::RocqString>, z: Array<rocq_string::RocqString>, K: Array<rocq_string::RocqString>, p: Int63, m: Int63, i: Int63, tbl: Array<bool>, _H: ()) -> Array<bool> {
  let tmp = i < m;
  match bdec(tmp) {
    sumbool::left => {
      let y_ref = &y;
      let tmp_1 = y_ref.get_cloned(i);
      let K_clone = Clone::clone(&K);
      let u = look(K_clone, p, tmp_1);
      let z_ref = &z;
      let tmp_2 = z_ref.get_cloned(i);
      let K_clone_1 = Clone::clone(&K);
      let v = look(K_clone_1, p, tmp_2);
      let tmp_3 = i + int63!(1);
      let tmp_4 = tbl.set(u * p + v, true);
      let tmp_5 = v * p;
      fill(y, z, K, p, m, tmp_3, tmp_4.set(tmp_5 + u, true), ())
    },
    sumbool::right => {
      std::mem::drop(y);
      std::mem::drop(z);
      std::mem::drop(K);
      tbl
    },
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.lim
// Variant: uncurried
pub fn lim(used: Int63, k: Int63) -> Int63 {
  if used < k {
    used + int63!(1)
  } else {
    k
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.okc
// Variant: uncurried
pub fn okc_1(tbl: Array<bool>, p: Int63, v: Int63, c: Int63, col: Array<Int63>, u: Int63) -> bool {
  okc(tbl, p, v, c, col, u, ())
}

// Rocq: Committeeassignment.committeeassignment_implem.okc (local: okc)
// Variant: uncurried, lifted
pub fn okc(tbl: Array<bool>, p: Int63, v: Int63, c: Int63, col: Array<Int63>, u: Int63, _H: ()) -> bool {
  let tmp = u < v;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = tbl.get_cloned(u * p + v);
      let tmp_2 = col.get_cloned(u);
      let tmp_3 = tmp_2 == c;
      if andb(tmp_1, tmp_3) {
        std::mem::drop(col);
        std::mem::drop(tbl);
        false
      } else {
        okc(tbl, p, v, c, col, u + int63!(1), ())
      }
    },
    sumbool::right => {
      std::mem::drop(tbl);
      std::mem::drop(col);
      true
    },
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.bump
// Variant: uncurried
pub fn bump(used: Int63, c: Int63) -> Int63 {
  let tmp = c + int63!(1);
  if used < tmp {
    c + int63!(1)
  } else {
    used
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.srch
// Variant: uncurried
pub fn srch_1(tbl: Array<bool>, p: Int63, k: Int63, v: Int63, c: Int63, used: Int63, col: Array<Int63>) -> (bool, Array<Int63>) {
  srch(tbl, p, k, v, c, used, col, ())
}

// Rocq: Committeeassignment.committeeassignment_implem.srch (local: srch)
// Variant: uncurried, lifted
pub fn srch(tbl: Array<bool>, p: Int63, k: Int63, v: Int63, c: Int63, used: Int63, col: Array<Int63>, _H: ()) -> (bool, Array<Int63>) {
  let tmp = v < p;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = c < lim(used, k);
      match bdec(tmp_1) {
        sumbool::left => {
          let tbl_clone = Clone::clone(&tbl);
          let col_clone = Clone::clone(&col);
          if okc_1(tbl_clone, p, v, c, col_clone, int63!(0)) {
            let tmp_2 = v + int63!(1);
            let tmp_3 = bump(used, c);
            let tmp_4 = col.set(v, c);
            let tbl_clone_1 = Clone::clone(&tbl);
            let tmp_5 = srch(tbl_clone_1, p, k, tmp_2, int63!(0), tmp_3, tmp_4, ());
            match tmp_5 {
              (v100, v102) => {
                if v100 {
                  std::mem::drop(tbl);
                  (true, v102)
                } else {
                  srch(tbl, p, k, v, c + int63!(1), used, v102, ())
                }
              },
            }
          } else {
            srch(tbl, p, k, v, c + int63!(1), used, col, ())
          }
        },
        sumbool::right => {
          std::mem::drop(tbl);
          (false, col)
        },
      }
    },
    sumbool::right => {
      std::mem::drop(tbl);
      (true, col)
    },
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.deepen
// Variant: uncurried
pub fn deepen_1(tbl: Array<bool>, p: Int63, P: Int63, k: Int63, col: Array<Int63>) -> Int63 {
  deepen(tbl, p, P, k, col, ())
}

// Rocq: Committeeassignment.committeeassignment_implem.deepen (local: deepen)
// Variant: uncurried, lifted
pub fn deepen(tbl: Array<bool>, p: Int63, P: Int63, k: Int63, col: Array<Int63>, _H: ()) -> Int63 {
  let tmp = k < P;
  match bdec(tmp) {
    sumbool::left => {
      let tbl_clone = Clone::clone(&tbl);
      let tmp_1 = srch_1(tbl_clone, p, k, int63!(0), int63!(0), int63!(0), col);
      match tmp_1 {
        (v41, v43) => {
          if v41 {
            std::mem::drop(tbl);
            std::mem::drop(v43);
            k
          } else {
            deepen(tbl, p, P, k + int63!(1), v43, ())
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(tbl);
      std::mem::drop(col);
      P
    },
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.committees_impl
// Variant: uncurried
pub fn committees_impl(_n: Int63, y: Array<rocq_string::RocqString>, z: Array<rocq_string::RocqString>) -> Int63 {
  let m = y.length();
  let tmp = m + m;
  let tmp_1 = rocq_string::StringPayload::from_static(b"");
  let tmp_2 = Array::<rocq_string::RocqString>::make(tmp, rocq_string::RocqString::from_payload(tmp_1));
  let y_clone = Clone::clone(&y);
  let z_clone = Clone::clone(&z);
  let tmp_3 = build_1(y_clone, z_clone, m, int63!(0), tmp_2, int63!(0));
  match tmp_3 {
    (v39, v41) => {
      let K = &v41;
      let tmp_4 = v41 * v41;
      let tbl = fill_1(y, z, v39, v41, m, int63!(0), Array::<bool>::make(tmp_4, false));
      let tmp_5 = int63!(1);
      let P = if v41 < tmp_5 {
        int63!(1)
      } else {
        v41
      };
      let tmp_6 = Array::<Int63>::make(P, int63!(0));
      let K_clone = Clone::clone(K);
      deepen_1(tbl, K_clone, P, int63!(1), tmp_6)
    },
  }
}
