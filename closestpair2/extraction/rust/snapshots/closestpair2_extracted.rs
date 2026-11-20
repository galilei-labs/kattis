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

pub type sint = Int63;

pub type uint = Int63;

pub type res = ((Int63, Int63), Int63);

// Rocq: Closestpair2.closestpair2_implem.INF
pub fn INF() -> Int63 {
  int63!(4611686018427387904)
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

// Rocq: Closestpair2.closestpair2_implem.splits
// Variant: uncurried
pub fn splits(lo: Int63, hi: Int63) -> bool {
  andb(lo < hi, int63!(1) < hi - lo)
}

// Rocq: Closestpair2.closestpair2_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Closestpair2.closestpair2_implem.midp
// Variant: uncurried
pub fn midp(lo: Int63, hi: Int63) -> Int63 {
  let tmp = hi - lo;
  lo + tmp / int63!(2)
}

// Rocq: Closestpair2.closestpair2_implem.merge_loop
// Variant: uncurried
pub fn merge_loop_1(key: Array<Int63>, src: Array<Int63>, mid: Int63, hi: Int63, i: Int63, j: Int63, k: Int63, dst: Array<Int63>) -> Array<Int63> {
  merge_loop(key, src, mid, hi, i, j, k, dst, ())
}

// Rocq: Closestpair2.closestpair2_implem.merge_loop (local: merge_loop)
// Variant: uncurried, lifted
pub fn merge_loop(key: Array<Int63>, src: Array<Int63>, mid: Int63, hi: Int63, i: Int63, j: Int63, k: Int63, dst: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = k < hi;
  match bdec(tmp) {
    sumbool::left => {
      if i < mid {
        if hi <= j {
          let tmp_1 = i + int63!(1);
          let tmp_2 = k + int63!(1);
          let tmp_3 = src.get_cloned(i);
          merge_loop(key, src, mid, hi, tmp_1, j, tmp_2, dst.set(k, tmp_3), ())
        } else {
          let tmp_4 = src.get_cloned(i);
          let tmp_5 = key.get_cloned(tmp_4);
          let tmp_6 = src.get_cloned(j);
          let tmp_7 = key.get_cloned(tmp_6);
          if tmp_5.lesb(tmp_7) {
            let tmp_8 = i + int63!(1);
            let tmp_9 = k + int63!(1);
            let tmp_10 = src.get_cloned(i);
            merge_loop(key, src, mid, hi, tmp_8, j, tmp_9, dst.set(k, tmp_10), ())
          } else {
            let tmp_11 = j + int63!(1);
            let tmp_12 = k + int63!(1);
            let tmp_13 = src.get_cloned(j);
            merge_loop(key, src, mid, hi, i, tmp_11, tmp_12, dst.set(k, tmp_13), ())
          }
        }
      } else {
        let tmp_14 = j + int63!(1);
        let tmp_15 = k + int63!(1);
        let tmp_16 = src.get_cloned(j);
        merge_loop(key, src, mid, hi, i, tmp_14, tmp_15, dst.set(k, tmp_16), ())
      }
    },
    sumbool::right => {
      std::mem::drop(key);
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Closestpair2.closestpair2_implem.merge
// Variant: uncurried
pub fn merge(key: Array<Int63>, src: Array<Int63>, lo: Int63, mid: Int63, hi: Int63, dst: Array<Int63>) -> Array<Int63> {
  merge_loop_1(key, src, mid, hi, lo, mid, lo, dst)
}

// Rocq: Closestpair2.closestpair2_implem.msort
// Variant: uncurried
pub fn msort_1(xs: Array<Int63>, lo: Int63, hi: Int63, tgt: Array<Int63>, oth: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  msort(xs, lo, hi, tgt, oth, ())
}

// Rocq: Closestpair2.closestpair2_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(xs: Array<Int63>, lo: Int63, hi: Int63, tgt: Array<Int63>, oth: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = splits(lo, hi);
  match bdec(tmp) {
    sumbool::left => {
      let mid = midp(lo, hi);
      let xs_clone = Clone::clone(&xs);
      let tmp_1 = msort(xs_clone, lo, mid, oth, tgt, ());
      match &tmp_1 {
        (t1, o1) => {
          let tmp_2 = ();
          let xs_clone_1 = Clone::clone(&xs);
          let t1_clone = Clone::clone(t1);
          let o1_clone = Clone::clone(o1);
          std::mem::drop(tmp_1);
          let tmp_3 = msort(xs_clone_1, mid, hi, t1_clone, o1_clone, tmp_2);
          match tmp_3 {
            (v64, v66) => {
              let t2 = &v64;
              let t2_clone = Clone::clone(t2);
              (merge(xs, t2_clone, lo, mid, hi, v66), v64)
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(xs);
      (tgt.set(lo, lo), oth)
    },
  }
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Closestpair2.closestpair2_implem.bd
pub fn bd(r: ((Int63, Int63), Int63)) -> Int63 {
  snd::<(Int63, Int63), Int63>(r)
}

// Rocq: Closestpair2.closestpair2_implem.near
// Variant: uncurried
pub fn near(xs: Array<Int63>, xm: Int63, b_1: Int63, v: Int63) -> bool {
  let tmp = xs.get_cloned(v);
  std::mem::drop(xs);
  let dx = tmp - xm;
  dx * dx < b_1
}

// Rocq: Closestpair2.closestpair2_implem.strip_loop
// Variant: uncurried
pub fn strip_loop_1(xs: Array<Int63>, xm: Int63, b_1: Int63, t: Array<Int63>, hi: Int63, k: Int63, c: Int63, o: Array<Int63>) -> (Array<Int63>, Int63) {
  strip_loop(xs, xm, b_1, t, hi, k, c, o, ())
}

// Rocq: Closestpair2.closestpair2_implem.strip_loop (local: strip_loop)
// Variant: uncurried, lifted
pub fn strip_loop(xs: Array<Int63>, xm: Int63, b_1: Int63, t: Array<Int63>, hi: Int63, k: Int63, c: Int63, o: Array<Int63>, _H: ()) -> (Array<Int63>, Int63) {
  let tmp = k < hi;
  match bdec(tmp) {
    sumbool::left => {
      let v = t.get_cloned(k);
      let xs_clone = Clone::clone(&xs);
      if near(xs_clone, xm, b_1, v) {
        strip_loop(xs, xm, b_1, t, hi, k + int63!(1), c + int63!(1), o.set(c, v), ())
      } else {
        strip_loop(xs, xm, b_1, t, hi, k + int63!(1), c, o, ())
      }
    },
    sumbool::right => {
      std::mem::drop(xs);
      std::mem::drop(t);
      (o, c)
    },
  }
}

// Rocq: Closestpair2.closestpair2_implem.d2
// Variant: uncurried
pub fn d2(xs: Array<Int63>, ys: Array<Int63>, a_1: Int63, b_1: Int63) -> Int63 {
  let tmp = xs.get_cloned(a_1);
  let tmp_1 = xs.get_cloned(b_1);
  std::mem::drop(xs);
  let dx = tmp - tmp_1;
  let tmp_2 = ys.get_cloned(a_1);
  let tmp_3 = ys.get_cloned(b_1);
  std::mem::drop(ys);
  let dy = tmp_2 - tmp_3;
  dx * dx + dy * dy
}

// Rocq: Closestpair2.closestpair2_implem.inner_loop
// Variant: uncurried
pub fn inner_loop_1(xs: Array<Int63>, ys: Array<Int63>, T: Array<Int63>, e: Int63, s: Int63, t: Int63, r: ((Int63, Int63), Int63)) -> ((Int63, Int63), Int63) {
  inner_loop(xs, ys, T, e, s, t, r, ())
}

// Rocq: Closestpair2.closestpair2_implem.inner_loop (local: inner_loop)
// Variant: uncurried, lifted
pub fn inner_loop(xs: Array<Int63>, ys: Array<Int63>, T: Array<Int63>, e: Int63, s: Int63, t: Int63, r: ((Int63, Int63), Int63), _H: ()) -> ((Int63, Int63), Int63) {
  let tmp = t < e;
  match bdec(tmp) {
    sumbool::left => {
      let a_1 = T.get_cloned(s);
      let b_1 = T.get_cloned(t);
      let tmp_1 = ys.get_cloned(b_1);
      let tmp_2 = ys.get_cloned(a_1);
      let dy = tmp_1 - tmp_2;
      let tmp_3 = dy * dy;
      let r_clone = Clone::clone(&r);
      let tmp_4 = bd(r_clone);
      if tmp_3 < tmp_4 {
        let xs_clone = Clone::clone(&xs);
        let ys_clone = Clone::clone(&ys);
        let d = d2(xs_clone, ys_clone, a_1, b_1);
        let tmp_5 = t + int63!(1);
        let r_clone_1 = Clone::clone(&r);
        let tmp_6 = bd(r_clone_1);
        let tmp_7 = if d < tmp_6 {
          std::mem::drop(r);
          ((a_1, b_1), d)
        } else {
          r
        };
        inner_loop(xs, ys, T, e, s, tmp_5, tmp_7, ())
      } else {
        std::mem::drop(xs);
        std::mem::drop(T);
        std::mem::drop(ys);
        r
      }
    },
    sumbool::right => {
      std::mem::drop(xs);
      std::mem::drop(ys);
      std::mem::drop(T);
      r
    },
  }
}

// Rocq: Closestpair2.closestpair2_implem.outer_loop
// Variant: uncurried
pub fn outer_loop_1(xs: Array<Int63>, ys: Array<Int63>, T: Array<Int63>, e: Int63, s: Int63, r: ((Int63, Int63), Int63)) -> ((Int63, Int63), Int63) {
  outer_loop(xs, ys, T, e, s, r, ())
}

// Rocq: Closestpair2.closestpair2_implem.outer_loop (local: outer_loop)
// Variant: uncurried, lifted
pub fn outer_loop(xs: Array<Int63>, ys: Array<Int63>, T: Array<Int63>, e: Int63, s: Int63, r: ((Int63, Int63), Int63), _H: ()) -> ((Int63, Int63), Int63) {
  let tmp = s < e;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = s + int63!(1);
      let tmp_2 = s + int63!(1);
      let xs_clone = Clone::clone(&xs);
      let ys_clone = Clone::clone(&ys);
      let T_clone = Clone::clone(&T);
      let tmp_3 = inner_loop_1(xs_clone, ys_clone, T_clone, e, s, tmp_2, r);
      outer_loop(xs, ys, T, e, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(xs);
      std::mem::drop(ys);
      std::mem::drop(T);
      r
    },
  }
}

// Rocq: Closestpair2.closestpair2_implem.solve
// Variant: uncurried
pub fn solve_1(xs: Array<Int63>, ys: Array<Int63>, P: Array<Int63>, lo: Int63, hi: Int63, tgt: Array<Int63>, oth: Array<Int63>) -> ((Array<Int63>, Array<Int63>), ((Int63, Int63), Int63)) {
  solve(xs, ys, P, lo, hi, tgt, oth, ())
}

// Rocq: Closestpair2.closestpair2_implem.solve (local: solve)
// Variant: uncurried, lifted
pub fn solve(xs: Array<Int63>, ys: Array<Int63>, P: Array<Int63>, lo: Int63, hi: Int63, tgt: Array<Int63>, oth: Array<Int63>, _H: ()) -> ((Array<Int63>, Array<Int63>), ((Int63, Int63), Int63)) {
  let tmp = splits(lo, hi);
  match bdec(tmp) {
    sumbool::left => {
      let mid = midp(lo, hi);
      let xs_clone = Clone::clone(&xs);
      let ys_clone = Clone::clone(&ys);
      let P_clone = Clone::clone(&P);
      let tmp_1 = solve(xs_clone, ys_clone, P_clone, lo, mid, oth, tgt, ());
      match tmp_1 {
        (v49, v51) => {
          let p = &v51;
          match v49 {
            (v55, v57) => {
              let xs_clone_1 = Clone::clone(&xs);
              let ys_clone_1 = Clone::clone(&ys);
              let P_clone_1 = Clone::clone(&P);
              let tmp_2 = solve(xs_clone_1, ys_clone_1, P_clone_1, mid, hi, v55, v57, ());
              match tmp_2 {
                (v83, v85) => {
                  let p_1 = &v85;
                  match v83 {
                    (v89, v91) => {
                      let t2 = &v89;
                      let ys_clone_2 = Clone::clone(&ys);
                      let t3 = merge(ys_clone_2, Clone::clone(t2), lo, mid, hi, v91);
                      let p_clone = Clone::clone(p_1);
                      let tmp_3 = bd(p_clone);
                      let p_clone_1 = Clone::clone(p);
                      let tmp_4 = bd(p_clone_1);
                      let r0 = if tmp_3 < tmp_4 {
                        std::mem::drop(v51);
                        v85
                      } else {
                        std::mem::drop(v85);
                        v51
                      };
                      let tmp_5 = P.get_cloned(mid);
                      std::mem::drop(P);
                      let tmp_6 = xs.get_cloned(tmp_5);
                      let r0_clone = Clone::clone(&r0);
                      let tmp_7 = bd(r0_clone);
                      let xs_clone_2 = Clone::clone(&xs);
                      let t3_clone = Clone::clone(&t3);
                      let t2_clone = Clone::clone(t2);
                      std::mem::drop(v89);
                      let tmp_8 = strip_loop_1(xs_clone_2, tmp_6, tmp_7, t3_clone, hi, lo, lo, t2_clone);
                      match tmp_8 {
                        (v163, v165) => {
                          let e = &v163;
                          let e_clone = Clone::clone(e);
                          ((t3, e_clone), outer_loop_1(xs, ys, v163, v165, lo, r0))
                        },
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
      std::mem::drop(xs);
      std::mem::drop(ys);
      let tmp_9 = P.get_cloned(lo);
      std::mem::drop(P);
      ((tgt.set(lo, tmp_9), oth), ((int63!(0), int63!(0)), __rocq_global_643))
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Closestpair2.closestpair2_implem.closestpair_impl
// Variant: uncurried
pub fn closestpair_impl(xs: Array<Int63>, ys: Array<Int63>) -> (Int63, Int63) {
  let n = xs.length();
  let tmp = Array::<Int63>::make(n, int63!(0));
  let tmp_1 = Array::<Int63>::make(n, int63!(0));
  let xs_clone = Clone::clone(&xs);
  let tmp_2 = msort_1(xs_clone, int63!(0), n, tmp, tmp_1);
  match &tmp_2 {
    (A, P) => {
      let tmp_3 = int63!(0);
      let tmp_4 = Array::<Int63>::make(n, int63!(0));
      let A_clone = Clone::clone(A);
      let P_clone = Clone::clone(P);
      std::mem::drop(tmp_2);
      let tmp_5 = solve_1(xs, ys, A_clone, tmp_3, n, P_clone, tmp_4);
      match tmp_5 {
        (v65, v67) => {
          std::mem::drop(v65);
          fst::<(Int63, Int63), Int63>(v67)
        },
      }
    },
  }
}
const __rocq_global_643: Int63 = int63!(4611686018427387904);