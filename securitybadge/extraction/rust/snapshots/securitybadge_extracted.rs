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

// Rocq: Securitybadge.securitybadge_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Securitybadge.securitybadge_implem.mid_of
// Variant: uncurried
pub fn mid_of(m: Int63, w: Int63, lo: Int63) -> Int63 {
  let tmp = m - lo;
  if w < tmp {
    lo + w
  } else {
    m
  }
}

// Rocq: Securitybadge.securitybadge_implem.merge
// Variant: uncurried
pub fn merge_1(src: Array<Int63>, mid: Int63, hi: Int63, i: Int63, j: Int63, k: Int63, dst: Array<Int63>) -> Array<Int63> {
  merge(src, mid, hi, i, j, k, dst, ())
}

// Rocq: Securitybadge.securitybadge_implem.merge (local: merge)
// Variant: uncurried, lifted
pub fn merge(src: Array<Int63>, mid: Int63, hi: Int63, i: Int63, j: Int63, k: Int63, dst: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < mid;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = j < hi;
      match bdec(tmp_1) {
        sumbool::left => {
          let tmp_2 = src.get_cloned(i);
          let tmp_3 = src.get_cloned(j);
          if tmp_2 <= tmp_3 {
            let tmp_4 = i + int63!(1);
            let tmp_5 = k + int63!(1);
            let tmp_6 = src.get_cloned(i);
            merge(src, mid, hi, tmp_4, j, tmp_5, dst.set(k, tmp_6), ())
          } else {
            let tmp_7 = j + int63!(1);
            let tmp_8 = k + int63!(1);
            let tmp_9 = src.get_cloned(j);
            merge(src, mid, hi, i, tmp_7, tmp_8, dst.set(k, tmp_9), ())
          }
        },
        sumbool::right => {
          let tmp_10 = i + int63!(1);
          let tmp_11 = k + int63!(1);
          let tmp_12 = src.get_cloned(i);
          merge(src, mid, hi, tmp_10, j, tmp_11, dst.set(k, tmp_12), ())
        },
      }
    },
    sumbool::right => {
      let tmp_13 = j < hi;
      match bdec(tmp_13) {
        sumbool::left => {
          let tmp_14 = j + int63!(1);
          let tmp_15 = k + int63!(1);
          let tmp_16 = src.get_cloned(j);
          merge(src, mid, hi, i, tmp_14, tmp_15, dst.set(k, tmp_16), ())
        },
        sumbool::right => {
          std::mem::drop(src);
          dst
        },
      }
    },
  }
}

// Rocq: Securitybadge.securitybadge_implem.pass
// Variant: uncurried
pub fn pass_1(src: Array<Int63>, m: Int63, w: Int63, lo: Int63, dst: Array<Int63>) -> Array<Int63> {
  pass(src, m, w, lo, dst, (), ())
}

// Rocq: Securitybadge.securitybadge_implem.pass (local: pass)
// Variant: uncurried, lifted
pub fn pass(src: Array<Int63>, m: Int63, w: Int63, lo: Int63, dst: Array<Int63>, _Hw: (), _H: ()) -> Array<Int63> {
  let tmp = lo < m;
  match bdec(tmp) {
    sumbool::left => {
      let mid = mid_of(m, w, lo);
      let hi = mid_of(m, w, mid);
      let src_clone = Clone::clone(&src);
      let tmp_1 = merge_1(src_clone, mid, hi, lo, mid, lo, dst);
      pass(src, m, w, hi, tmp_1, (), ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Securitybadge.securitybadge_implem.sort_loop
// Variant: uncurried
pub fn sort_loop_1(m: Int63, w: Int63, src: Array<Int63>, dst: Array<Int63>) -> Array<Int63> {
  sort_loop(m, w, src, dst, (), (), ())
}

// Rocq: Securitybadge.securitybadge_implem.sort_loop (local: sort_loop)
// Variant: uncurried, lifted
pub fn sort_loop(m: Int63, w: Int63, src: Array<Int63>, dst: Array<Int63>, _Hm: (), _Hw: (), _H: ()) -> Array<Int63> {
  let tmp = w < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = w + w;
      let src_clone = Clone::clone(&src);
      let tmp_2 = pass_1(src_clone, m, w, int63!(0), dst);
      sort_loop(m, tmp_1, tmp_2, src, (), (), ())
    },
    sumbool::right => {
      std::mem::drop(dst);
      src
    },
  }
}

// Rocq: Securitybadge.securitybadge_implem.msort
pub fn msort(a_1: Array<Int63>) -> Array<Int63> {
  let tmp = a_1.length();
  let tmp_1 = a_1.length();
  sort_loop_1(tmp, int63!(1), a_1, Array::<Int63>::make(tmp_1, int63!(0)))
}

// Rocq: Securitybadge.securitybadge_implem.keys_loop
// Variant: uncurried
pub fn keys_loop_1(xla: Array<Int63>, L: Int63, i: Int63, K: Array<Int63>) -> Array<Int63> {
  keys_loop(xla, L, i, K, ())
}

// Rocq: Securitybadge.securitybadge_implem.keys_loop (local: keys_loop)
// Variant: uncurried, lifted
pub fn keys_loop(xla: Array<Int63>, L: Int63, i: Int63, K: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < L;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = xla.get_cloned(i);
      let tmp_3 = (tmp_2 << int63!(13)) + i;
      keys_loop(xla, L, tmp_1, K.set(i, tmp_3), ())
    },
    sumbool::right => {
      std::mem::drop(xla);
      K
    },
  }
}

// Rocq: Securitybadge.securitybadge_implem.src_of
pub fn src_of(key: Int63) -> Int63 {
  key >> int63!(13)
}

// Rocq: Securitybadge.securitybadge_implem.st_loop
// Variant: uncurried
pub fn st_loop_1(K: Array<Int63>, p: Int63, st: Array<Int63>) -> Array<Int63> {
  st_loop(K, p, st, ())
}

// Rocq: Securitybadge.securitybadge_implem.st_loop (local: st_loop)
// Variant: uncurried, lifted
pub fn st_loop(K: Array<Int63>, p: Int63, st: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = int63!(0) < p;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = p - int63!(1);
      let tmp_2 = K.get_cloned(p - int63!(1));
      st_loop(K, tmp_1, st.set(src_of(tmp_2), p - int63!(1)), ())
    },
    sumbool::right => {
      std::mem::drop(K);
      st
    },
  }
}

// Rocq: Securitybadge.securitybadge_implem.bnd_loop
// Variant: uncurried
pub fn bnd_loop_1(xlx: Array<Int63>, xly: Array<Int63>, L: Int63, i: Int63, B: Array<Int63>) -> Array<Int63> {
  bnd_loop(xlx, xly, L, i, B, ())
}

// Rocq: Securitybadge.securitybadge_implem.bnd_loop (local: bnd_loop)
// Variant: uncurried, lifted
pub fn bnd_loop(xlx: Array<Int63>, xly: Array<Int63>, L: Int63, i: Int63, B: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < L;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = i + i + int63!(2);
      let tmp_3 = xlx.get_cloned(i);
      let tmp_4 = B.set(tmp_2, tmp_3);
      let tmp_5 = i + i + int63!(3);
      let tmp_6 = xly.get_cloned(i);
      bnd_loop(xlx, xly, L, tmp_1, tmp_4.set(tmp_5, tmp_6 + int63!(1)), ())
    },
    sumbool::right => {
      std::mem::drop(xlx);
      std::mem::drop(xly);
      B
    },
  }
}

// Rocq: Securitybadge.securitybadge_implem.idx_of
pub fn idx_of(key: Int63) -> Int63 {
  let tmp = key >> int63!(13);
  key - (tmp << int63!(13))
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

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b_1: bool) -> bool {
  if b_1 {
    false
  } else {
    true
  }
}

// Rocq: Securitybadge.securitybadge_implem.scan
// Variant: uncurried
pub fn scan_1(K: Array<Int63>, xlb: Array<Int63>, xlx: Array<Int63>, xly: Array<Int63>, L: Int63, u: Int63, k: Int63, stamp: Int63, p: Int63, vis: Array<Int63>, stk: Array<Int63>, sp: Int63) -> ((Array<Int63>, Array<Int63>), Int63) {
  scan(K, xlb, xlx, xly, L, u, k, stamp, p, vis, stk, sp, ())
}

// Rocq: Securitybadge.securitybadge_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(K: Array<Int63>, xlb: Array<Int63>, xlx: Array<Int63>, xly: Array<Int63>, L: Int63, u: Int63, k: Int63, stamp: Int63, p: Int63, vis: Array<Int63>, stk: Array<Int63>, sp: Int63, _H: ()) -> ((Array<Int63>, Array<Int63>), Int63) {
  let tmp = p < L;
  match bdec(tmp) {
    sumbool::left => {
      let key = K.get_cloned(p);
      let tmp_1 = src_of(key);
      if tmp_1 == u {
        let i = idx_of(key);
        let v = xlb.get_cloned(i);
        let tmp_2 = xlx.get_cloned(i);
        let tmp_3 = tmp_2 <= k;
        let tmp_4 = xly.get_cloned(i);
        let tmp_5 = andb(tmp_3, k <= tmp_4);
        let tmp_6 = vis.get_cloned(v);
        let tmp_7 = andb(tmp_5, negb(tmp_6 == stamp));
        let tmp_8 = vis.length();
        let tmp_9 = v < tmp_8;
        if andb(tmp_7, tmp_9) {
          let tmp_10 = p + int63!(1);
          let tmp_11 = vis.set(v, stamp);
          scan(K, xlb, xlx, xly, L, u, k, stamp, tmp_10, tmp_11, stk.set(sp, v), sp + int63!(1), ())
        } else {
          scan(K, xlb, xlx, xly, L, u, k, stamp, p + int63!(1), vis, stk, sp, ())
        }
      } else {
        std::mem::drop(K);
        std::mem::drop(xlb);
        std::mem::drop(xlx);
        std::mem::drop(xly);
        ((vis, stk), sp)
      }
    },
    sumbool::right => {
      std::mem::drop(K);
      std::mem::drop(xlb);
      std::mem::drop(xlx);
      std::mem::drop(xly);
      ((vis, stk), sp)
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Securitybadge.securitybadge_implem.dfs
// Variant: uncurried
pub fn dfs_1(K: Array<Int63>, st: Array<Int63>, xlb: Array<Int63>, xlx: Array<Int63>, xly: Array<Int63>, L: Int63, k: Int63, stamp: Int63, vis: Array<Int63>, stk: Array<Int63>, sp: Int63) -> (Array<Int63>, Array<Int63>) {
  dfs(K, st, xlb, xlx, xly, L, k, stamp, vis, stk, sp, ())
}

// Rocq: Securitybadge.securitybadge_implem.dfs (local: dfs)
// Variant: uncurried, lifted
pub fn dfs(K: Array<Int63>, st: Array<Int63>, xlb: Array<Int63>, xlx: Array<Int63>, xly: Array<Int63>, L: Int63, k: Int63, stamp: Int63, vis: Array<Int63>, stk: Array<Int63>, sp: Int63, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = int63!(0) < sp;
  match bdec(tmp) {
    sumbool::left => {
      let u = stk.get_cloned(sp - int63!(1));
      let tmp_1 = st.get_cloned(u);
      let tmp_2 = sp - int63!(1);
      let K_clone = Clone::clone(&K);
      let xlb_clone = Clone::clone(&xlb);
      let xlx_clone = Clone::clone(&xlx);
      let xly_clone = Clone::clone(&xly);
      let r = scan_1(K_clone, xlb_clone, xlx_clone, xly_clone, L, u, k, stamp, tmp_1, vis, stk, tmp_2);
      let r_clone = Clone::clone(&r);
      let tmp_3 = fst::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), Int63>(r_clone));
      let r_clone_1 = Clone::clone(&r);
      dfs(K, st, xlb, xlx, xly, L, k, stamp, tmp_3, snd::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), Int63>(r_clone_1)), snd::<(Array<Int63>, Array<Int63>), Int63>(r), ())
    },
    sumbool::right => {
      std::mem::drop(K);
      std::mem::drop(st);
      std::mem::drop(xlb);
      std::mem::drop(xlx);
      std::mem::drop(xly);
      (vis, stk)
    },
  }
}

// Rocq: Securitybadge.securitybadge_implem.count_loop
// Variant: uncurried
pub fn count_loop_1(K: Array<Int63>, st: Array<Int63>, xlb: Array<Int63>, xlx: Array<Int63>, xly: Array<Int63>, S: Array<Int63>, L: Int63, m: Int63, s: Int63, d: Int63, j: Int63, vis: Array<Int63>, stk: Array<Int63>, acc: Int63) -> Int63 {
  count_loop(K, st, xlb, xlx, xly, S, L, m, s, d, j, vis, stk, acc, ())
}

// Rocq: Securitybadge.securitybadge_implem.count_loop (local: count_loop)
// Variant: uncurried, lifted
pub fn count_loop(K: Array<Int63>, st: Array<Int63>, xlb: Array<Int63>, xlx: Array<Int63>, xly: Array<Int63>, S: Array<Int63>, L: Int63, m: Int63, s: Int63, d: Int63, j: Int63, vis: Array<Int63>, stk: Array<Int63>, acc: Int63, _H: ()) -> Int63 {
  let tmp = j < m;
  match bdec(tmp) {
    sumbool::left => {
      let p = S.get_cloned(j - int63!(1));
      let q = S.get_cloned(j);
      if p < q {
        let tmp_1 = vis.set(s, j);
        let tmp_2 = stk.set(int63!(0), s);
        let K_clone = Clone::clone(&K);
        let st_clone = Clone::clone(&st);
        let xlb_clone = Clone::clone(&xlb);
        let xlx_clone = Clone::clone(&xlx);
        let xly_clone = Clone::clone(&xly);
        let r = dfs_1(K_clone, st_clone, xlb_clone, xlx_clone, xly_clone, L, p, j, tmp_1, tmp_2, int63!(1));
        let tmp_3 = j + int63!(1);
        let r_clone = Clone::clone(&r);
        let tmp_4 = fst::<Array<Int63>, Array<Int63>>(r_clone);
        let r_clone_1 = Clone::clone(&r);
        let tmp_5 = snd::<Array<Int63>, Array<Int63>>(r_clone_1);
        let tmp_6 = fst::<Array<Int63>, Array<Int63>>(r);
        let tmp_7 = tmp_6.get_cloned(d);
        let tmp_8 = if tmp_7 == j {
          std::mem::drop(tmp_6);
          acc + (q - p)
        } else {
          std::mem::drop(tmp_6);
          acc
        };
        count_loop(K, st, xlb, xlx, xly, S, L, m, s, d, tmp_3, tmp_4, tmp_5, tmp_8, ())
      } else {
        count_loop(K, st, xlb, xlx, xly, S, L, m, s, d, j + int63!(1), vis, stk, acc, ())
      }
    },
    sumbool::right => {
      std::mem::drop(K);
      std::mem::drop(st);
      std::mem::drop(xlb);
      std::mem::drop(xlx);
      std::mem::drop(xly);
      std::mem::drop(S);
      std::mem::drop(vis);
      std::mem::drop(stk);
      acc
    },
  }
}

// Rocq: Securitybadge.securitybadge_implem.securitybadge_core
// Variant: uncurried
pub fn securitybadge_core(n: Int63, b_1: Int63, s: Int63, d: Int63, xla: Array<Int63>, xlb: Array<Int63>, xlx: Array<Int63>, xly: Array<Int63>) -> Int63 {
  let L = xla.length();
  let tmp = Array::<Int63>::make(L, int63!(0));
  let K = msort(keys_loop_1(xla, L, int63!(0), tmp));
  let tmp_1 = Array::<Int63>::make(n + int63!(2), L);
  let K_clone = Clone::clone(&K);
  let st = st_loop_1(K_clone, L, tmp_1);
  let m = L + L + int63!(2);
  let tmp_2 = Array::<Int63>::make(m, int63!(0)).set(int63!(0), int63!(1)).set(int63!(1), b_1 + int63!(1));
  let xlx_clone = Clone::clone(&xlx);
  let xly_clone = Clone::clone(&xly);
  let S = msort(bnd_loop_1(xlx_clone, xly_clone, L, int63!(0), tmp_2));
  count_loop_1(K, st, xlb, xlx, xly, S, L, m, s, d, int63!(1), Array::<Int63>::make(n + int63!(1), int63!(0)), Array::<Int63>::make(n + int63!(1), int63!(0)), int63!(0))
}

// Rocq: Securitybadge.securitybadge_implem.securitybadge_impl
// Variant: uncurried
pub fn securitybadge_impl(n: Int63, b_1: Int63, s: Int63, d: Int63, xla: Array<Int63>, xlb: Array<Int63>, xlx: Array<Int63>, xly: Array<Int63>) -> Int63 {
  securitybadge_core(n, b_1, s, d, xla, xlb, xlx, xly)
}
