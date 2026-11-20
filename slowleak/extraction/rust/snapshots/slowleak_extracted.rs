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

// Rocq: Slowleak.slowleak_implem.INF
pub fn INF() -> Int63 {
  int63!(2305843009213693952)
}

// Rocq: Slowleak.slowleak_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Slowleak.slowleak_implem.diag_loop
// Variant: uncurried
pub fn diag_loop_1(n: Int63, i: Int63, T: Array<Int63>) -> Array<Int63> {
  diag_loop(n, i, T, ())
}

// Rocq: Slowleak.slowleak_implem.diag_loop (local: diag_loop)
// Variant: uncurried, lifted
pub fn diag_loop(n: Int63, i: Int63, T: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = i * n;
      diag_loop(n, tmp_1, T.set(tmp_2 + i, int63!(0)), ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Slowleak.slowleak_implem.setmin
// Variant: uncurried
pub fn setmin(T: Array<Int63>, p: Int63, s: Int63) -> Array<Int63> {
  let tmp = T.get_cloned(p);
  if s < tmp {
    T.set(p, s)
  } else {
    T
  }
}

// Rocq: Slowleak.slowleak_implem.edge_loop
// Variant: uncurried
pub fn edge_loop_1(n: Int63, xi: Array<Int63>, xj: Array<Int63>, xk: Array<Int63>, m: Int63, e: Int63, T: Array<Int63>) -> Array<Int63> {
  edge_loop(n, xi, xj, xk, m, e, T, ())
}

// Rocq: Slowleak.slowleak_implem.edge_loop (local: edge_loop)
// Variant: uncurried, lifted
pub fn edge_loop(n: Int63, xi: Array<Int63>, xj: Array<Int63>, xk: Array<Int63>, m: Int63, e: Int63, T: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = e < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = xi.get_cloned(e);
      let u = tmp_1 - int63!(1);
      let tmp_2 = xj.get_cloned(e);
      let v = tmp_2 - int63!(1);
      let k = xk.get_cloned(e);
      let tmp_3 = e + int63!(1);
      let tmp_4 = setmin(T, u * n + v, k);
      let tmp_5 = v * n;
      edge_loop(n, xi, xj, xk, m, tmp_3, setmin(tmp_4, tmp_5 + u, k), ())
    },
    sumbool::right => {
      std::mem::drop(xi);
      std::mem::drop(xj);
      std::mem::drop(xk);
      T
    },
  }
}

// Rocq: Slowleak.slowleak_implem.fw_j
// Variant: uncurried
pub fn fw_j_1(n: Int63, rowi: Int63, rowk: Int63, aik: Int63, j: Int63, T: Array<Int63>) -> Array<Int63> {
  fw_j(n, rowi, rowk, aik, j, T, ())
}

// Rocq: Slowleak.slowleak_implem.fw_j (local: fw_j)
// Variant: uncurried, lifted
pub fn fw_j(n: Int63, rowi: Int63, rowk: Int63, aik: Int63, j: Int63, T: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = j < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = j + int63!(1);
      let tmp_2 = rowi + j;
      let tmp_3 = T.get_cloned(rowk + j);
      let tmp_4 = aik + tmp_3;
      fw_j(n, rowi, rowk, aik, tmp_1, setmin(T, tmp_2, tmp_4), ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Slowleak.slowleak_implem.fw_i
// Variant: uncurried
pub fn fw_i_1(n: Int63, k: Int63, rowk: Int63, i: Int63, T: Array<Int63>) -> Array<Int63> {
  fw_i(n, k, rowk, i, T, ())
}

// Rocq: Slowleak.slowleak_implem.fw_i (local: fw_i)
// Variant: uncurried, lifted
pub fn fw_i(n: Int63, k: Int63, rowk: Int63, i: Int63, T: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let rowi = i * n;
      let tmp_1 = i + int63!(1);
      let tmp_2 = T.get_cloned(rowi + k);
      let tmp_3 = fw_j_1(n, rowi, rowk, tmp_2, int63!(0), T);
      fw_i(n, k, rowk, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Slowleak.slowleak_implem.fw_k
// Variant: uncurried
pub fn fw_k_1(n: Int63, k: Int63, T: Array<Int63>) -> Array<Int63> {
  fw_k(n, k, T, ())
}

// Rocq: Slowleak.slowleak_implem.fw_k (local: fw_k)
// Variant: uncurried, lifted
pub fn fw_k(n: Int63, k: Int63, T: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = k < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = k + int63!(1);
      let tmp_2 = k * n;
      let tmp_3 = fw_i_1(n, k, tmp_2, int63!(0), T);
      fw_k(n, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Slowleak.slowleak_implem.vx_loop
// Variant: uncurried
pub fn vx_loop_1(xs: Array<Int63>, t: Int63, i: Int63, V: Array<Int63>) -> Array<Int63> {
  vx_loop(xs, t, i, V, ())
}

// Rocq: Slowleak.slowleak_implem.vx_loop (local: vx_loop)
// Variant: uncurried, lifted
pub fn vx_loop(xs: Array<Int63>, t: Int63, i: Int63, V: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < t;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = i + int63!(1);
      let tmp_3 = xs.get_cloned(i);
      vx_loop(xs, t, tmp_1, V.set(tmp_2, tmp_3 - int63!(1)), ())
    },
    sumbool::right => {
      std::mem::drop(xs);
      V
    },
  }
}

// Rocq: Slowleak.slowleak_implem.sel_loop
// Variant: uncurried
pub fn sel_loop_1(M: Int63, vis: Array<bool>, dist: Array<Int63>, i: Int63, b_1: Int63, bv: Int63) -> Int63 {
  sel_loop(M, vis, dist, i, b_1, bv, ())
}

// Rocq: Slowleak.slowleak_implem.sel_loop (local: sel_loop)
// Variant: uncurried, lifted
pub fn sel_loop(M: Int63, vis: Array<bool>, dist: Array<Int63>, i: Int63, b_1: Int63, bv: Int63, _H: ()) -> Int63 {
  let tmp = i < M;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = vis.get_cloned(i);
      if tmp_1 {
        sel_loop(M, vis, dist, i + int63!(1), b_1, bv, ())
      } else {
        let di = dist.get_cloned(i);
        if di < bv {
          sel_loop(M, vis, dist, i + int63!(1), i, di, ())
        } else {
          sel_loop(M, vis, dist, i + int63!(1), b_1, bv, ())
        }
      }
    },
    sumbool::right => {
      std::mem::drop(vis);
      std::mem::drop(dist);
      b_1
    },
  }
}

// Rocq: Slowleak.slowleak_implem.rel_loop
// Variant: uncurried
pub fn rel_loop_1(M: Int63, V: Array<Int63>, T: Array<Int63>, vis: Array<bool>, d: Int63, ru: Int63, du: Int63, b_1: Int63, dist: Array<Int63>) -> Array<Int63> {
  rel_loop(M, V, T, vis, d, ru, du, b_1, dist, ())
}

// Rocq: Slowleak.slowleak_implem.rel_loop (local: rel_loop)
// Variant: uncurried, lifted
pub fn rel_loop(M: Int63, V: Array<Int63>, T: Array<Int63>, vis: Array<bool>, d: Int63, ru: Int63, du: Int63, b_1: Int63, dist: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = b_1 < M;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = vis.get_cloned(b_1);
      let dist_ = if tmp_1 {
        dist
      } else {
        let tmp_2 = V.get_cloned(b_1);
        let w = T.get_cloned(ru + tmp_2);
        if w <= d {
          setmin(dist, b_1, du + w)
        } else {
          dist
        }
      };
      rel_loop(M, V, T, vis, d, ru, du, b_1 + int63!(1), dist_, ())
    },
    sumbool::right => {
      std::mem::drop(V);
      std::mem::drop(T);
      std::mem::drop(vis);
      dist
    },
  }
}

// Rocq: Slowleak.slowleak_implem.dij_loop
// Variant: uncurried
pub fn dij_loop_1(n: Int63, M: Int63, tgt: Int63, V: Array<Int63>, T: Array<Int63>, d: Int63, r: Int63, vis: Array<bool>, dist: Array<Int63>) -> Rc<option<Int63>> {
  dij_loop(n, M, tgt, V, T, d, r, vis, dist, ())
}

// Rocq: Slowleak.slowleak_implem.dij_loop (local: dij_loop)
// Variant: uncurried, lifted
pub fn dij_loop(n: Int63, M: Int63, tgt: Int63, V: Array<Int63>, T: Array<Int63>, d: Int63, r: Int63, vis: Array<bool>, dist: Array<Int63>, _H: ()) -> Rc<option<Int63>> {
  let tmp = int63!(0) < r;
  match bdec(tmp) {
    sumbool::left => {
      let vis_clone = Clone::clone(&vis);
      let dist_clone = Clone::clone(&dist);
      let u = sel_loop_1(M, vis_clone, dist_clone, int63!(0), M, __rocq_global_110);
      if u == M {
        std::mem::drop(V);
        std::mem::drop(T);
        std::mem::drop(vis);
        std::mem::drop(dist);
        Rc::new(option::<Int63>::None)
      } else {
        if u == tgt {
          std::mem::drop(V);
          std::mem::drop(T);
          std::mem::drop(vis);
          let tmp_1 = dist.get_cloned(u);
          std::mem::drop(dist);
          Rc::new(option::<Int63>::Some(tmp_1))
        } else {
          let vis_ = vis.set(u, true);
          let tmp_2 = V.get_cloned(u);
          let tmp_3 = tmp_2 * n;
          let tmp_4 = dist.get_cloned(u);
          let V_clone = Clone::clone(&V);
          let T_clone = Clone::clone(&T);
          let vis__clone = Clone::clone(&vis_);
          let dist_ = rel_loop_1(M, V_clone, T_clone, vis__clone, d, tmp_3, tmp_4, int63!(0), dist);
          dij_loop(n, M, tgt, V, T, d, r - int63!(1), vis_, dist_, ())
        }
      }
    },
    sumbool::right => {
      std::mem::drop(V);
      std::mem::drop(T);
      std::mem::drop(vis);
      std::mem::drop(dist);
      Rc::new(option::<Int63>::None)
    },
  }
}

// Rocq: Slowleak.slowleak_implem.slowleak_impl
// Variant: uncurried
pub fn slowleak_impl(x: Int63, y: Int63, xs: Array<Int63>, xi: Array<Int63>, xj: Array<Int63>, xk: Array<Int63>) -> Rc<option<Int63>> {
  let tmp = x * x;
  let T0 = diag_loop_1(x, int63!(0), Array::<Int63>::make(tmp, __rocq_global_110));
  let m = xi.length();
  let T1 = edge_loop_1(x, xi, xj, xk, m, int63!(0), T0);
  let T = fw_k_1(x, int63!(0), T1);
  let t = xs.length();
  let M = t + int63!(2);
  let tmp_1 = Array::<Int63>::make(M, int63!(0));
  let tmp_2 = t + int63!(1);
  let V = vx_loop_1(xs, t, int63!(0), tmp_1.set(tmp_2, x - int63!(1)));
  let tmp_3 = t + int63!(1);
  let tmp_4 = Array::<bool>::make(M, false);
  let tmp_5 = Array::<Int63>::make(M, __rocq_global_110);
  dij_loop_1(x, M, tmp_3, V, T, y, M, tmp_4, tmp_5.set(int63!(0), int63!(0)))
}
const __rocq_global_110: Int63 = int63!(2305843009213693952);