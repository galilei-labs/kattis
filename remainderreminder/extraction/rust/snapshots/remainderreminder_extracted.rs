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

// Rocq: Remainderreminder.remainderreminder_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Remainderreminder.remainderreminder_implem.upd
// Variant: uncurried
pub fn upd(t: ((Int63, Int63), Int63), v: Int63) -> ((Int63, Int63), Int63) {
  match &t {
    (t3, p) => {
      match t3 {
        (t2, t1) => {
          let t2_clone = Clone::clone(t2);
          if t2_clone < v {
            let tmp = (v, Clone::clone(t2));
            let t1_clone = Clone::clone(t1);
            std::mem::drop(t);
            (tmp, t1_clone)
          } else {
            let t2_clone_1 = Clone::clone(t2);
            if v == t2_clone_1 {
              t
            } else {
              let t1_clone_1 = Clone::clone(t1);
              if t1_clone_1 < v {
                let tmp_1 = (Clone::clone(t2), v);
                let t1_clone_2 = Clone::clone(t1);
                std::mem::drop(t);
                (tmp_1, t1_clone_2)
              } else {
                let t1_clone_3 = Clone::clone(t1);
                if v == t1_clone_3 {
                  t
                } else {
                  let p_clone = Clone::clone(p);
                  if p_clone < v {
                    let t2_clone_2 = Clone::clone(t2);
                    let t1_clone_4 = Clone::clone(t1);
                    std::mem::drop(t);
                    ((t2_clone_2, t1_clone_4), v)
                  } else {
                    t
                  }
                }
              }
            }
          }
        },
      }
    },
  }
}

// Rocq: Remainderreminder.remainderreminder_implem.vol
// Variant: uncurried
pub fn vol(a_1: Int63, b_1: Int63, x: Int63) -> Int63 {
  let tmp = int63!(2) * x;
  x * (a_1 - tmp) * (b_1 - int63!(2) * x)
}

// Rocq: Remainderreminder.remainderreminder_implem.scan
// Variant: uncurried
pub fn scan_1(a_1: Int63, b_1: Int63, m: Int63, x: Int63, t: ((Int63, Int63), Int63)) -> ((Int63, Int63), Int63) {
  scan(a_1, b_1, m, x, t, ())
}

// Rocq: Remainderreminder.remainderreminder_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(a_1: Int63, b_1: Int63, m: Int63, x: Int63, t: ((Int63, Int63), Int63), _H: ()) -> ((Int63, Int63), Int63) {
  let tmp = x < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = x + int63!(1);
      let tmp_2 = vol(a_1, b_1, x);
      scan(a_1, b_1, m, tmp_1, upd(t, tmp_2), ())
    },
    sumbool::right => {
      t
    },
  }
}

// Rocq: Remainderreminder.remainderreminder_implem.egcd
// Variant: uncurried
pub fn egcd_1(m: Int63, r0: Int63, s0: Int63, r1: Int63, s1: Int63) -> (Int63, Int63) {
  egcd(m, r0, s0, r1, s1, ())
}

// Rocq: Remainderreminder.remainderreminder_implem.egcd (local: egcd)
// Variant: uncurried, lifted
pub fn egcd(m: Int63, r0: Int63, s0: Int63, r1: Int63, s1: Int63, _H: ()) -> (Int63, Int63) {
  let tmp = r1 == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      (r0, s0)
    },
    sumbool::right => {
      let tmp_1 = r0 % r1;
      let tmp_2 = (s0 + m - r0 / r1 % m * s1 % m) % m;
      egcd(m, r1, s1, tmp_1, tmp_2, ())
    },
  }
}

// Rocq: Remainderreminder.remainderreminder_implem.merge
// Variant: uncurried
pub fn merge(r1: Int63, m1: Int63, r2: Int63, m2: Int63) -> (Int63, Int63) {
  let tmp = int63!(1) % m2;
  let tmp_1 = egcd_1(m2, m1, tmp, m2, int63!(0));
  match tmp_1 {
    (v27, v29) => {
      let dd = (r2 + m2 - r1 % m2) % m2;
      let tmp_2 = dd % v27;
      if tmp_2 == int63!(0) {
        let m2_ = m2 / v27;
        (r1 + m1 * (dd / v27 * v29 % m2_), m1 * m2_)
      } else {
        (int63!(0), int63!(0))
      }
    },
  }
}

// Rocq: Remainderreminder.remainderreminder_implem.lift
// Variant: uncurried
pub fn lift(f: Int63, r: Int63, l: Int63) -> Int63 {
  let tmp = r + l;
  let tmp_1 = f % l;
  f + (tmp - tmp_1) % l
}

// Rocq: Remainderreminder.remainderreminder_implem.rr_impl
// Variant: uncurried
pub fn rr_impl(a_1: Int63, b_1: Int63, c: Int63, d: Int63, e: Int63, f: Int63, _g: Int63) -> Int63 {
  let m = (a_1 + int63!(1)) / int63!(2);
  let tmp = scan_1(a_1, b_1, m, int63!(1), ((int63!(0), int63!(0)), int63!(0)));
  match tmp {
    (v56, v58) => {
      match v56 {
        (v61, v63) => {
          let tmp_1 = merge(c, v61, d, v63);
          match &tmp_1 {
            (l12, r12) => {
              let l12_clone = Clone::clone(l12);
              let r12_clone = Clone::clone(r12);
              std::mem::drop(tmp_1);
              let tmp_2 = merge(l12_clone, r12_clone, e, v58);
              match tmp_2 {
                (v92, v94) => {
                  lift(f, v92, v94)
                },
              }
            },
          }
        },
      }
    },
  }
}
