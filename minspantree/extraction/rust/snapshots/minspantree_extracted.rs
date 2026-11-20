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

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = Int63;

pub type sint = Int63;

// Rocq: Minspantree.minspantree_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Minspantree.minspantree_implem.find
// Variant: uncurried
pub fn find_1(par: Array<Int63>, rk: Array<Int63>, v: Int63) -> Int63 {
  find(par, rk, v, ())
}

// Rocq: Minspantree.minspantree_implem.find (local: find)
// Variant: uncurried, lifted
pub fn find(par: Array<Int63>, rk: Array<Int63>, v: Int63, _H: ()) -> Int63 {
  let u = par.get_cloned(v);
  if u == v {
    std::mem::drop(rk);
    std::mem::drop(par);
    v
  } else {
    let tmp = rk.get_cloned(v);
    let tmp_1 = rk.get_cloned(u);
    let tmp_2 = tmp < tmp_1;
    match bdec(tmp_2) {
      sumbool::left => {
        find(par, rk, u, ())
      },
      sumbool::right => {
        std::mem::drop(rk);
        std::mem::drop(par);
        v
      },
    }
  }
}

// Rocq: Minspantree.minspantree_implem.findr
// Variant: uncurried
pub fn findr(par: Array<Int63>, rk: Array<Int63>, v: Int63) -> Int63 {
  find_1(par, rk, v)
}

// Rocq: Minspantree.minspantree_implem.scan
// Variant: uncurried
pub fn scan_1(n: Int63, us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>, ord: Array<Int63>, m: Int63, q: Int63, par: Array<Int63>, rk: Array<Int63>, out: Array<Int63>, cnt: Int63, cost: Int63) -> Rc<option<(Int63, Array<Int63>)>> {
  scan(n, us, vs, ws, ord, m, q, par, rk, out, cnt, cost, ())
}

// Rocq: Minspantree.minspantree_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(n: Int63, us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>, ord: Array<Int63>, m: Int63, q: Int63, par: Array<Int63>, rk: Array<Int63>, out: Array<Int63>, cnt: Int63, cost: Int63, _H: ()) -> Rc<option<(Int63, Array<Int63>)>> {
  let tmp = q < m;
  match bdec(tmp) {
    sumbool::left => {
      let e = ord.get_cloned(q);
      let tmp_1 = us.get_cloned(e);
      let par_clone = Clone::clone(&par);
      let rk_clone = Clone::clone(&rk);
      let a_1 = findr(par_clone, rk_clone, tmp_1);
      let tmp_2 = vs.get_cloned(e);
      let par_clone_1 = Clone::clone(&par);
      let rk_clone_1 = Clone::clone(&rk);
      let b_1 = findr(par_clone_1, rk_clone_1, tmp_2);
      if a_1 == b_1 {
        scan(n, us, vs, ws, ord, m, q + int63!(1), par, rk, out, cnt, cost, ())
      } else {
        let ra = rk.get_cloned(a_1);
        let rb = rk.get_cloned(b_1);
        if ra < rb {
          let tmp_3 = q + int63!(1);
          let tmp_4 = par.set(a_1, b_1);
          let tmp_5 = out.set(cnt, e);
          let tmp_6 = cnt + int63!(1);
          let tmp_7 = ws.get_cloned(e);
          scan(n, us, vs, ws, ord, m, tmp_3, tmp_4, rk, tmp_5, tmp_6, cost + tmp_7, ())
        } else {
          if rb < ra {
            let tmp_8 = q + int63!(1);
            let tmp_9 = par.set(b_1, a_1);
            let tmp_10 = out.set(cnt, e);
            let tmp_11 = cnt + int63!(1);
            let tmp_12 = ws.get_cloned(e);
            scan(n, us, vs, ws, ord, m, tmp_8, tmp_9, rk, tmp_10, tmp_11, cost + tmp_12, ())
          } else {
            let tmp_13 = q + int63!(1);
            let tmp_14 = par.set(a_1, b_1);
            let tmp_15 = rk.set(b_1, rb + int63!(1));
            let tmp_16 = out.set(cnt, e);
            let tmp_17 = cnt + int63!(1);
            let tmp_18 = ws.get_cloned(e);
            scan(n, us, vs, ws, ord, m, tmp_13, tmp_14, tmp_15, tmp_16, tmp_17, cost + tmp_18, ())
          }
        }
      }
    },
    sumbool::right => {
      let tmp_19 = n - int63!(1);
      if cnt == tmp_19 {
        std::mem::drop(us);
        std::mem::drop(vs);
        std::mem::drop(ws);
        std::mem::drop(ord);
        std::mem::drop(par);
        std::mem::drop(rk);
        Rc::new(option::<(Int63, Array<Int63>)>::Some((cost, out)))
      } else {
        std::mem::drop(us);
        std::mem::drop(vs);
        std::mem::drop(ws);
        std::mem::drop(ord);
        std::mem::drop(par);
        std::mem::drop(rk);
        std::mem::drop(out);
        Rc::new(option::<(Int63, Array<Int63>)>::None)
      }
    },
  }
}

// Rocq: Minspantree.minspantree_implem.step_end
// Variant: uncurried
pub fn step_end(m: Int63, w: Int63, x: Int63) -> Int63 {
  let tmp = m - x;
  if w < tmp {
    x + w
  } else {
    m
  }
}

// Rocq: Minspantree.minspantree_implem.merge_loop
// Variant: uncurried
pub fn merge_loop_1(ws: Array<Int63>, src: Array<Int63>, iend: Int63, jend: Int63, kend: Int63, i: Int63, j: Int63, k: Int63, dst: Array<Int63>) -> Array<Int63> {
  merge_loop(ws, src, iend, jend, kend, i, j, k, dst, ())
}

// Rocq: Minspantree.minspantree_implem.merge_loop (local: merge_loop)
// Variant: uncurried, lifted
pub fn merge_loop(ws: Array<Int63>, src: Array<Int63>, iend: Int63, jend: Int63, kend: Int63, i: Int63, j: Int63, k: Int63, dst: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = k < kend;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = if i < iend {
        if j < jend {
          let tmp_2 = src.get_cloned(i);
          let tmp_3 = ws.get_cloned(tmp_2);
          let tmp_4 = src.get_cloned(j);
          let tmp_5 = ws.get_cloned(tmp_4);
          tmp_3.lesb(tmp_5)
        } else {
          true
        }
      } else {
        false
      };
      if tmp_1 {
        let tmp_6 = i + int63!(1);
        let tmp_7 = k + int63!(1);
        let tmp_8 = src.get_cloned(i);
        merge_loop(ws, src, iend, jend, kend, tmp_6, j, tmp_7, dst.set(k, tmp_8), ())
      } else {
        let tmp_9 = j + int63!(1);
        let tmp_10 = k + int63!(1);
        let tmp_11 = src.get_cloned(j);
        merge_loop(ws, src, iend, jend, kend, i, tmp_9, tmp_10, dst.set(k, tmp_11), ())
      }
    },
    sumbool::right => {
      std::mem::drop(ws);
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Minspantree.minspantree_implem.pass_loop
// Variant: uncurried
pub fn pass_loop_1(ws: Array<Int63>, src: Array<Int63>, m: Int63, w: Int63, lo: Int63, dst: Array<Int63>) -> Array<Int63> {
  pass_loop(ws, src, m, w, lo, dst, ())
}

// Rocq: Minspantree.minspantree_implem.pass_loop (local: pass_loop)
// Variant: uncurried, lifted
pub fn pass_loop(ws: Array<Int63>, src: Array<Int63>, m: Int63, w: Int63, lo: Int63, dst: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = lo < m;
  match bdec(tmp) {
    sumbool::left => {
      let mid = step_end(m, w, lo);
      let hi = step_end(m, w, mid);
      let tmp_1 = lo < hi;
      match bdec(tmp_1) {
        sumbool::left => {
          let ws_clone = Clone::clone(&ws);
          let src_clone = Clone::clone(&src);
          let tmp_2 = merge_loop_1(ws_clone, src_clone, mid, hi, hi, lo, mid, lo, dst);
          pass_loop(ws, src, m, w, hi, tmp_2, ())
        },
        sumbool::right => {
          std::mem::drop(ws);
          std::mem::drop(src);
          dst
        },
      }
    },
    sumbool::right => {
      std::mem::drop(ws);
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Minspantree.minspantree_implem.sort_loop
// Variant: uncurried
pub fn sort_loop_1(ws: Array<Int63>, m: Int63, w: Int63, src: Array<Int63>, dst: Array<Int63>) -> Array<Int63> {
  sort_loop(ws, m, w, src, dst, ())
}

// Rocq: Minspantree.minspantree_implem.sort_loop (local: sort_loop)
// Variant: uncurried, lifted
pub fn sort_loop(ws: Array<Int63>, m: Int63, w: Int63, src: Array<Int63>, dst: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = w < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = w + w;
      let tmp_2 = w < tmp_1;
      match bdec(tmp_2) {
        sumbool::left => {
          let tmp_3 = w + w;
          let ws_clone = Clone::clone(&ws);
          let src_clone = Clone::clone(&src);
          let tmp_4 = pass_loop_1(ws_clone, src_clone, m, w, int63!(0), dst);
          sort_loop(ws, m, tmp_3, tmp_4, src, ())
        },
        sumbool::right => {
          std::mem::drop(ws);
          std::mem::drop(dst);
          src
        },
      }
    },
    sumbool::right => {
      std::mem::drop(ws);
      std::mem::drop(dst);
      src
    },
  }
}

// Rocq: Minspantree.minspantree_implem.iota_loop
// Variant: uncurried
pub fn iota_loop_1(m: Int63, i: Int63, a_1: Array<Int63>) -> Array<Int63> {
  iota_loop(m, i, a_1, ())
}

// Rocq: Minspantree.minspantree_implem.iota_loop (local: iota_loop)
// Variant: uncurried, lifted
pub fn iota_loop(m: Int63, i: Int63, a_1: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < m;
  match bdec(tmp) {
    sumbool::left => {
      iota_loop(m, i + int63!(1), a_1.set(i, i), ())
    },
    sumbool::right => {
      a_1
    },
  }
}

// Rocq: Minspantree.minspantree_implem.iota
pub fn iota(m: Int63) -> Array<Int63> {
  let tmp = Array::<Int63>::make(m, int63!(0));
  iota_loop_1(m, int63!(0), tmp)
}

// Rocq: Minspantree.minspantree_implem.sort_edges
// Variant: uncurried
pub fn sort_edges(ws: Array<Int63>, m: Int63) -> Array<Int63> {
  let tmp = iota(m);
  let tmp_1 = Array::<Int63>::make(m, int63!(0));
  sort_loop_1(ws, m, int63!(1), tmp, tmp_1)
}

// Rocq: Minspantree.minspantree_implem.mst_impl
// Variant: uncurried
pub fn mst_impl(n: Int63, us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>) -> Rc<option<(Int63, Array<Int63>)>> {
  let m = us.length();
  let ws_clone = Clone::clone(&ws);
  let tmp = sort_edges(ws_clone, m);
  let tmp_1 = iota(n);
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  let tmp_3 = n - int63!(1);
  scan_1(n, us, vs, ws, tmp, m, int63!(0), tmp_1, tmp_2, Array::<Int63>::make(tmp_3, int63!(0)), int63!(0), int63!(0))
}
