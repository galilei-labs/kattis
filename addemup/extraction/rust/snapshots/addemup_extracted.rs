#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

pub enum option<A: 'static> {
  Some(A),
  None,
}

impl<A: Clone + 'static> Clone for option<A> {
  fn clone(&self) -> Self {
    match self {
      option::Some(__field0) => option::Some(Clone::clone(__field0)),
      option::None => option::None,
    }
  }
}

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = Int63;

// Rocq: Addemup.addemup_implem.K
pub fn K() -> Int63 {
  int63!(131072)
}

// Rocq: Addemup.addemup_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Addemup.addemup_implem.rotd
pub fn rotd(d: Int63) -> Rc<option<Int63>> {
  if d == int63!(0) {
    Rc::new(option::<Int63>::Some(int63!(0)))
  } else {
    if d == int63!(1) {
      Rc::new(option::<Int63>::Some(int63!(1)))
    } else {
      if d == int63!(2) {
        Rc::new(option::<Int63>::Some(int63!(2)))
      } else {
        if d == int63!(5) {
          Rc::new(option::<Int63>::Some(int63!(5)))
        } else {
          if d == int63!(6) {
            Rc::new(option::<Int63>::Some(int63!(9)))
          } else {
            if d == int63!(8) {
              Rc::new(option::<Int63>::Some(int63!(8)))
            } else {
              if d == int63!(9) {
                Rc::new(option::<Int63>::Some(int63!(6)))
              } else {
                Rc::new(option::<Int63>::None)
              }
            }
          }
        }
      }
    }
  }
}

// Rocq: Addemup.addemup_implem.rloop
// Variant: uncurried
pub fn rloop_1(x: Int63, r: Int63) -> Rc<option<Int63>> {
  rloop(x, r, ())
}

// Rocq: Addemup.addemup_implem.rloop (local: rloop)
// Variant: uncurried, lifted
pub fn rloop(x: Int63, r: Int63, _H: ()) -> Rc<option<Int63>> {
  let tmp = int63!(0) < x;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rotd(x % int63!(10));
      let (v28, v29) = __rocq_reuse::reset(tmp_1, |__payload| Clone::clone(__payload));
      match v28 {
        option::Some(v34) => {
          std::mem::drop(v29);
          rloop(x / int63!(10), r * int63!(10) + v34, ())
        },
        option::None => {
          __rocq_reuse::rebuild(v29, option::<Int63>::None)
        },
      }
    },
    sumbool::right => {
      Rc::new(option::<Int63>::Some(r))
    },
  }
}

// Rocq: Addemup.addemup_implem.alt
pub fn alt(c: Int63) -> Int63 {
  let tmp = rloop_1(c, int63!(0));
  let (v9, v10) = __rocq_reuse::reset(tmp, |__payload| Clone::clone(__payload));
  std::mem::drop(v10);
  match v9 {
    option::Some(v15) => {
      v15
    },
    option::None => {
      c
    },
  }
}

// Rocq: Addemup.addemup_implem.build
// Variant: uncurried
pub fn build_1(y: Array<Int63>, T: Array<Int63>, n: Int63, i: Int63) -> Array<Int63> {
  build(y, T, n, i, ())
}

// Rocq: Addemup.addemup_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(y: Array<Int63>, T: Array<Int63>, n: Int63, i: Int63, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let c = y.get_cloned(i);
      build(y, T.set(int63!(2) * i, c * __rocq_global_68 + i).set(int63!(2) * i + int63!(1), alt(c) * __rocq_global_68 + i), n, i + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(y);
      T
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Addemup.addemup_implem.merge_loop
// Variant: uncurried
pub fn merge_loop_1(src: Array<Int63>, dst: Array<Int63>, i: Int63, mid: Int63, j: Int63, hi: Int63, k: Int63) -> Array<Int63> {
  merge_loop(src, dst, i, mid, j, hi, k, ())
}

// Rocq: Addemup.addemup_implem.merge_loop (local: merge_loop)
// Variant: uncurried, lifted
pub fn merge_loop(src: Array<Int63>, dst: Array<Int63>, i: Int63, mid: Int63, j: Int63, hi: Int63, k: Int63, _H: ()) -> Array<Int63> {
  let tmp = k < hi;
  match bdec(tmp) {
    sumbool::left => {
      if i < mid {
        if j < hi {
          let tmp_1 = src.get_cloned(i);
          let tmp_2 = src.get_cloned(j);
          if tmp_1 <= tmp_2 {
            let tmp_3 = src.get_cloned(i);
            merge_loop(src, dst.set(k, tmp_3), i + int63!(1), mid, j, hi, k + int63!(1), ())
          } else {
            let tmp_4 = src.get_cloned(j);
            merge_loop(src, dst.set(k, tmp_4), i, mid, j + int63!(1), hi, k + int63!(1), ())
          }
        } else {
          let tmp_5 = src.get_cloned(i);
          merge_loop(src, dst.set(k, tmp_5), i + int63!(1), mid, j, hi, k + int63!(1), ())
        }
      } else {
        let tmp_6 = src.get_cloned(j);
        merge_loop(src, dst.set(k, tmp_6), i, mid, j + int63!(1), hi, k + int63!(1), ())
      }
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Addemup.addemup_implem.copy_loop
// Variant: uncurried
pub fn copy_loop_1(src: Array<Int63>, dst: Array<Int63>, hi: Int63, k: Int63) -> Array<Int63> {
  copy_loop(src, dst, hi, k, ())
}

// Rocq: Addemup.addemup_implem.copy_loop (local: copy_loop)
// Variant: uncurried, lifted
pub fn copy_loop(src: Array<Int63>, dst: Array<Int63>, hi: Int63, k: Int63, _H: ()) -> Array<Int63> {
  let tmp = k < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = src.get_cloned(k);
      copy_loop(src, dst.set(k, tmp_1), hi, k + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Addemup.addemup_implem.msort
// Variant: uncurried
pub fn msort_1(a_1: Array<Int63>, b_1: Array<Int63>, lo: Int63, hi: Int63) -> (Array<Int63>, Array<Int63>) {
  msort(a_1, b_1, lo, hi, ())
}

// Rocq: Addemup.addemup_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(a_1: Array<Int63>, b_1: Array<Int63>, lo: Int63, hi: Int63, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = lo < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = int63!(1) < hi - lo;
      match bdec(tmp_1) {
        sumbool::left => {
          let tmp_2 = hi - lo;
          let mid = lo + tmp_2 / int63!(2);
          let tmp_3 = msort(a_1, b_1, lo, mid, ());
          match &tmp_3 {
            (b1, a1) => {
              let tmp_4 = ();
              let b1_clone = Clone::clone(b1);
              let a1_clone = Clone::clone(a1);
              std::mem::drop(tmp_3);
              let tmp_5 = msort(b1_clone, a1_clone, mid, hi, tmp_4);
              match tmp_5 {
                (v90, v92) => {
                  let b2 = &v90;
                  let b2_clone = Clone::clone(b2);
                  let b3 = merge_loop_1(b2_clone, v92, lo, mid, mid, hi, lo);
                  let b3_clone = Clone::clone(&b3);
                  (copy_loop_1(b3_clone, v90, hi, lo), b3)
                },
              }
            },
          }
        },
        sumbool::right => {
          (a_1, b_1)
        },
      }
    },
    sumbool::right => {
      (a_1, b_1)
    },
  }
}

// Rocq: Addemup.addemup_implem.lbloop
// Variant: uncurried
pub fn lbloop_1(S: Array<Int63>, x: Int63, lo: Int63, hi: Int63) -> Int63 {
  lbloop(S, x, lo, hi, ())
}

// Rocq: Addemup.addemup_implem.lbloop (local: lbloop)
// Variant: uncurried, lifted
pub fn lbloop(S: Array<Int63>, x: Int63, lo: Int63, hi: Int63, _H: ()) -> Int63 {
  let tmp = lo < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = hi - lo;
      let tmp_2 = S.get_cloned(lo + tmp_1 / int63!(2));
      if tmp_2 < x {
        let tmp_3 = hi - lo;
        lbloop(S, x, lo + tmp_3 / int63!(2) + int63!(1), hi, ())
      } else {
        let tmp_4 = hi - lo;
        let tmp_5 = lo + tmp_4 / int63!(2);
        lbloop(S, x, lo, tmp_5, ())
      }
    },
    sumbool::right => {
      std::mem::drop(S);
      lo
    },
  }
}

// Rocq: Addemup.addemup_implem.inrange
// Variant: uncurried
pub fn inrange(S: Array<Int63>, m: Int63, lo: Int63, hi: Int63) -> bool {
  let S_clone = Clone::clone(&S);
  let p = lbloop_1(S_clone, lo, int63!(0), m);
  if p < m {
    let tmp = S.get_cloned(p);
    std::mem::drop(S);
    tmp < hi
  } else {
    std::mem::drop(S);
    false
  }
}

// Rocq: Addemup.addemup_implem.found
// Variant: uncurried
pub fn found(S: Array<Int63>, m: Int63, w: Int63, i: Int63) -> bool {
  let tmp = w * __rocq_global_68;
  let tmp_1 = w * __rocq_global_68 + i;
  let S_clone = Clone::clone(&S);
  if inrange(S_clone, m, tmp, tmp_1) {
    std::mem::drop(S);
    true
  } else {
    inrange(S, m, w * __rocq_global_68 + i + int63!(1), (w + int63!(1)) * __rocq_global_68)
  }
}

// Rocq: Addemup.addemup_implem.okv
// Variant: uncurried
pub fn okv(S: Array<Int63>, m: Int63, s: Int63, v: Int63, i: Int63) -> bool {
  if v <= s {
    found(S, m, s - v, i)
  } else {
    std::mem::drop(S);
    false
  }
}

// Rocq: Addemup.addemup_implem.scan
// Variant: uncurried
pub fn scan_1(y: Array<Int63>, S: Array<Int63>, s: Int63, m: Int63, n: Int63, i: Int63) -> bool {
  scan(y, S, s, m, n, i, ())
}

// Rocq: Addemup.addemup_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(y: Array<Int63>, S: Array<Int63>, s: Int63, m: Int63, n: Int63, i: Int63, _H: ()) -> bool {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let c = y.get_cloned(i);
      let S_clone = Clone::clone(&S);
      if okv(S_clone, m, s, c, i) {
        std::mem::drop(y);
        std::mem::drop(S);
        true
      } else {
        let tmp_1 = alt(c);
        let S_clone_1 = Clone::clone(&S);
        if okv(S_clone_1, m, s, tmp_1, i) {
          std::mem::drop(y);
          std::mem::drop(S);
          true
        } else {
          scan(y, S, s, m, n, i + int63!(1), ())
        }
      }
    },
    sumbool::right => {
      std::mem::drop(y);
      std::mem::drop(S);
      false
    },
  }
}

// Rocq: Addemup.addemup_implem.addemup_impl
// Variant: uncurried
pub fn addemup_impl(s: Int63, y: Array<Int63>) -> bool {
  let n = y.length();
  let m = int63!(2) * n;
  let tmp = Array::<Int63>::make(m, int63!(0));
  let y_clone = Clone::clone(&y);
  let T = build_1(y_clone, tmp, n, int63!(0));
  let S = fst::<Array<Int63>, Array<Int63>>(msort_1(T, Array::<Int63>::make(m, int63!(0)), int63!(0), m));
  scan_1(y, S, s, m, n, int63!(0))
}
const __rocq_global_68: Int63 = int63!(131072);