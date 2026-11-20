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

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Ultraquicksort.ultraquicksort_implem.bdec
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

// Rocq: Ultraquicksort.ultraquicksort_implem.merge
// Variant: uncurried
pub fn merge_1(src: Array<Int63>, dst: Array<Int63>, mid: Int63, hi: Int63, i: Int63, j: Int63, k: Int63, c: Int63) -> (Array<Int63>, Int63) {
  merge(src, dst, mid, hi, i, j, k, c, ())
}

// Rocq: Ultraquicksort.ultraquicksort_implem.merge (local: merge)
// Variant: uncurried, lifted
pub fn merge(src: Array<Int63>, dst: Array<Int63>, mid: Int63, hi: Int63, i: Int63, j: Int63, k: Int63, c: Int63, _H: ()) -> (Array<Int63>, Int63) {
  let tmp = i < mid;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = j < hi;
      match bdec(tmp_1) {
        sumbool::left => {
          let x = src.get_cloned(i);
          let y = src.get_cloned(j);
          if y < x {
            let tmp_2 = dst.set(k, y);
            let tmp_3 = j + int63!(1);
            let tmp_4 = k + int63!(1);
            let tmp_5 = mid - i;
            merge(src, tmp_2, mid, hi, i, tmp_3, tmp_4, c + tmp_5, ())
          } else {
            merge(src, dst.set(k, x), mid, hi, i + int63!(1), j, k + int63!(1), c, ())
          }
        },
        sumbool::right => {
          let tmp_6 = src.get_cloned(i);
          merge(src, dst.set(k, tmp_6), mid, hi, i + int63!(1), j, k + int63!(1), c, ())
        },
      }
    },
    sumbool::right => {
      let tmp_7 = j < hi;
      match bdec(tmp_7) {
        sumbool::left => {
          let tmp_8 = src.get_cloned(j);
          merge(src, dst.set(k, tmp_8), mid, hi, i, j + int63!(1), k + int63!(1), c, ())
        },
        sumbool::right => {
          std::mem::drop(src);
          (dst, c)
        },
      }
    },
  }
}

// Rocq: Ultraquicksort.ultraquicksort_implem.msort
// Variant: uncurried
pub fn msort_1(b_1: bool, lo: Int63, hi: Int63, w: Array<Int63>, s: Array<Int63>, c: Int63) -> ((Array<Int63>, Array<Int63>), Int63) {
  msort(b_1, lo, hi, w, s, c, ())
}

// Rocq: Ultraquicksort.ultraquicksort_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(b_1: bool, lo: Int63, hi: Int63, w: Array<Int63>, s: Array<Int63>, c: Int63, _H: ()) -> ((Array<Int63>, Array<Int63>), Int63) {
  let tmp = int63!(1) < hi - lo;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = hi - lo;
      let mid = lo + tmp_1 / int63!(2);
      let tmp_2 = msort(negb(b_1), lo, mid, w, s, c, ());
      match tmp_2 {
        (v69, v71) => {
          match v69 {
            (v74, v76) => {
              let tmp_3 = msort(negb(b_1), mid, hi, v74, v76, v71, ());
              match tmp_3 {
                (v101, v103) => {
                  match v101 {
                    (v106, v108) => {
                      let s2 = &v106;
                      let w2 = &v108;
                      if b_1 {
                        let w2_clone = Clone::clone(w2);
                        let tmp_4 = merge_1(w2_clone, v106, mid, hi, lo, mid, lo, v103);
                        match tmp_4 {
                          (v132, v134) => {
                            ((v132, v108), v134)
                          },
                        }
                      } else {
                        let s2_clone = Clone::clone(s2);
                        let tmp_5 = merge_1(s2_clone, v108, mid, hi, lo, mid, lo, v103);
                        match tmp_5 {
                          (v172, v174) => {
                            ((v106, v172), v174)
                          },
                        }
                      }
                    },
                  }
                },
              }
            },
          }
        },
      }
    },
    sumbool::right => {
      if b_1 {
        ((w, s), c)
      } else {
        let tmp_6 = w.get_cloned(lo);
        ((w, s.set(lo, tmp_6)), c)
      }
    },
  }
}

// Rocq: Ultraquicksort.ultraquicksort_implem.inversions_impl
pub fn inversions_impl(a_1: Array<Int63>) -> Int63 {
  let n = a_1.length();
  let tmp = int63!(0);
  let a_ref = &a_1;
  let tmp_1 = a_ref.copy();
  std::mem::drop(a_1);
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  snd::<(Array<Int63>, Array<Int63>), Int63>(msort_1(true, tmp, n, tmp_1, tmp_2, int63!(0)))
}
