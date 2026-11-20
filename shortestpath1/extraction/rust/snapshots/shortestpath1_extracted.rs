#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

pub struct St {
  pub st_dist: Array<Int63>,
  pub st_hk: Array<Int63>,
  pub st_hv: Array<Int63>,
  pub st_sz: Int63,
}

impl Clone for St {
  fn clone(&self) -> Self {
    match self {
      St { st_dist: __field0, st_hk: __field1, st_hv: __field2, st_sz: __field3 } => St { st_dist: Clone::clone(__field0), st_hk: Clone::clone(__field1), st_hv: Clone::clone(__field2), st_sz: Clone::clone(__field3) },
    }
  }
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

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = Int63;

// Rocq: Shortestpath1.shortestpath1_implem.INF
pub fn INF() -> Int63 {
  int63!(9223372036854775807)
}

// Rocq: Shortestpath1.shortestpath1_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.count_loop
// Variant: uncurried
pub fn count_loop_1(us: Array<Int63>, m: Int63, k: Int63, c: Array<Int63>) -> Array<Int63> {
  count_loop(us, m, k, c, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.count_loop (local: count_loop)
// Variant: uncurried, lifted
pub fn count_loop(us: Array<Int63>, m: Int63, k: Int63, c: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = k < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = us.get_cloned(k);
      let u1 = tmp_1 + int63!(1);
      let tmp_2 = k + int63!(1);
      let tmp_3 = c.get_cloned(u1);
      count_loop(us, m, tmp_2, c.set(u1, tmp_3 + int63!(1)), ())
    },
    sumbool::right => {
      std::mem::drop(us);
      c
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.prefix_loop
// Variant: uncurried
pub fn prefix_loop_1(n: Int63, i: Int63, c: Array<Int63>) -> Array<Int63> {
  prefix_loop(n, i, c, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.prefix_loop (local: prefix_loop)
// Variant: uncurried, lifted
pub fn prefix_loop(n: Int63, i: Int63, c: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let a_1 = c.get_cloned(i);
      let b_1 = c.get_cloned(i + int63!(1));
      prefix_loop(n, i + int63!(1), c.set(i + int63!(1), b_1 + a_1), ())
    },
    sumbool::right => {
      c
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>, m: Int63, k: Int63, pos: Array<Int63>, adj: Array<Int63>, wt: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  fill_loop(us, vs, ws, m, k, pos, adj, wt, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>, m: Int63, k: Int63, pos: Array<Int63>, adj: Array<Int63>, wt: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = k < m;
  match bdec(tmp) {
    sumbool::left => {
      let u = us.get_cloned(k);
      let j = pos.get_cloned(u);
      let tmp_1 = k + int63!(1);
      let tmp_2 = pos.set(u, j + int63!(1));
      let tmp_3 = vs.get_cloned(k);
      let tmp_4 = adj.set(j, tmp_3);
      let tmp_5 = ws.get_cloned(k);
      fill_loop(us, vs, ws, m, tmp_1, tmp_2, tmp_4, wt.set(j, tmp_5), ())
    },
    sumbool::right => {
      std::mem::drop(us);
      std::mem::drop(vs);
      std::mem::drop(ws);
      std::mem::drop(pos);
      (adj, wt)
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.st_sz
pub fn st_sz_owned(s: Rc<St>) -> Int63 {
  let s_st_sz_clone = Clone::clone(&s.st_sz);
  std::mem::drop(s);
  s_st_sz_clone
}

// Rocq: Shortestpath1.shortestpath1_implem.st_sz
// Variant: borrowed
pub fn st_sz(s: &Rc<St>) -> Int63 {
  let tmp = s;
  Clone::clone(&tmp.st_sz)
}

// Rocq: Shortestpath1.shortestpath1_implem.st_hv
// Variant: borrowed
pub fn st_hv(s: &Rc<St>) -> Array<Int63> {
  let tmp = s;
  Clone::clone(&tmp.st_hv)
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

// Rocq: Shortestpath1.shortestpath1_implem.child
// Variant: uncurried
pub fn child(hk: Array<Int63>, sz: Int63, l: Int63) -> Int63 {
  let tmp = l + int63!(1) < sz;
  let tmp_1 = hk.get_cloned(l + int63!(1));
  let tmp_2 = hk.get_cloned(l);
  let tmp_3 = tmp_1 < tmp_2;
  if andb(tmp, tmp_3) {
    std::mem::drop(hk);
    l + int63!(1)
  } else {
    std::mem::drop(hk);
    l
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.sift_down
// Variant: uncurried
pub fn sift_down_1(hk: Array<Int63>, hv: Array<Int63>, sz: Int63, i: Int63) -> (Array<Int63>, Array<Int63>) {
  sift_down(hk, hv, sz, i, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.sift_down (local: sift_down)
// Variant: uncurried, lifted
pub fn sift_down(hk: Array<Int63>, hv: Array<Int63>, sz: Int63, i: Int63, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let l = i + i + int63!(1);
  let tmp = andb(l < sz, i < l);
  match bdec(tmp) {
    sumbool::left => {
      let hk_clone = Clone::clone(&hk);
      let c = child(hk_clone, sz, l);
      let ki = hk.get_cloned(i);
      let kc = hk.get_cloned(c);
      let tmp_1 = kc < ki;
      match bdec(tmp_1) {
        sumbool::left => {
          let vi = hv.get_cloned(i);
          let vc = hv.get_cloned(c);
          sift_down(hk.set(i, kc).set(c, ki), hv.set(i, vc).set(c, vi), sz, c, ())
        },
        sumbool::right => {
          (hk, hv)
        },
      }
    },
    sumbool::right => {
      (hk, hv)
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.pop
// Variant: uncurried
pub fn pop(hk: Array<Int63>, hv: Array<Int63>, sz: Int63) -> (Array<Int63>, Array<Int63>) {
  let sz_ = sz - int63!(1);
  let k = hk.get_cloned(sz_);
  let v = hv.get_cloned(sz_);
  sift_down_1(hk.set(int63!(0), k), hv.set(int63!(0), v), sz_, int63!(0))
}

// Rocq: Shortestpath1.shortestpath1_implem.st_hk
// Variant: borrowed
pub fn st_hk(s: &Rc<St>) -> Array<Int63> {
  let tmp = s;
  Clone::clone(&tmp.st_hk)
}

// Rocq: Shortestpath1.shortestpath1_implem.sift_up
// Variant: uncurried
pub fn sift_up_1(hk: Array<Int63>, hv: Array<Int63>, i: Int63) -> (Array<Int63>, Array<Int63>) {
  sift_up(hk, hv, i, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.sift_up (local: sift_up)
// Variant: uncurried, lifted
pub fn sift_up(hk: Array<Int63>, hv: Array<Int63>, i: Int63, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = int63!(0) < i;
  match bdec(tmp) {
    sumbool::left => {
      let p = i - int63!(1) >> int63!(1);
      let ki = hk.get_cloned(i);
      let kp = hk.get_cloned(p);
      let tmp_1 = ki < kp;
      match bdec(tmp_1) {
        sumbool::left => {
          let vi = hv.get_cloned(i);
          let vp = hv.get_cloned(p);
          sift_up(hk.set(i, kp).set(p, ki), hv.set(i, vp).set(p, vi), p, ())
        },
        sumbool::right => {
          (hk, hv)
        },
      }
    },
    sumbool::right => {
      (hk, hv)
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.push
// Variant: uncurried
pub fn push(hk: Array<Int63>, hv: Array<Int63>, sz: Int63, k: Int63, v: Int63) -> (Array<Int63>, Array<Int63>) {
  sift_up_1(hk.set(sz, k), hv.set(sz, v), sz)
}

// Rocq: Shortestpath1.shortestpath1_implem.scan
// Variant: uncurried
pub fn scan_1(adj: Array<Int63>, wt: Array<Int63>, du: Int63, hi: Int63, j: Int63, dist: Array<Int63>, hk: Array<Int63>, hv: Array<Int63>, sz: Int63) -> Rc<St> {
  scan(adj, wt, du, hi, j, dist, hk, hv, sz, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(adj: Array<Int63>, wt: Array<Int63>, du: Int63, hi: Int63, j: Int63, dist: Array<Int63>, hk: Array<Int63>, hv: Array<Int63>, sz: Int63, _H: ()) -> Rc<St> {
  let tmp = j < hi;
  match bdec(tmp) {
    sumbool::left => {
      let v = adj.get_cloned(j);
      let tmp_1 = wt.get_cloned(j);
      let nd = du + tmp_1;
      let tmp_2 = dist.get_cloned(v);
      let tmp_3 = nd < tmp_2;
      match bdec(tmp_3) {
        sumbool::left => {
          let tmp_4 = push(hk, hv, sz, nd, v);
          match tmp_4 {
            (v63, v65) => {
              scan(adj, wt, du, hi, j + int63!(1), dist.set(v, nd), v63, v65, sz + int63!(1), ())
            },
          }
        },
        sumbool::right => {
          scan(adj, wt, du, hi, j + int63!(1), dist, hk, hv, sz, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(adj);
      std::mem::drop(wt);
      Rc::new(St { st_dist: dist, st_hk: hk, st_hv: hv, st_sz: sz })
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.st_dist
pub fn st_dist(s: Rc<St>) -> Array<Int63> {
  let s_st_dist_clone = Clone::clone(&s.st_dist);
  std::mem::drop(s);
  s_st_dist_clone
}

// Rocq: Shortestpath1.shortestpath1_implem.main
// Variant: uncurried
pub fn main_2(off: Array<Int63>, adj: Array<Int63>, wt: Array<Int63>, done: Array<Int63>, st: Rc<St>) -> Array<Int63> {
  main_1(off, adj, wt, done, st, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.main (local: main)
// Variant: uncurried, lifted
pub fn main_1(off: Array<Int63>, adj: Array<Int63>, wt: Array<Int63>, done: Array<Int63>, st: Rc<St>, _H: ()) -> Array<Int63> {
  let tmp = int63!(0) < st_sz(&st);
  match bdec(tmp) {
    sumbool::left => {
      let st_ref = &st;
      let tmp_1 = st_hv(st_ref);
      let u = tmp_1.get_cloned(int63!(0));
      let st_ref_1 = &st;
      let tmp_2 = st_hk(st_ref_1);
      let st_ref_2 = &st;
      let tmp_3 = pop(tmp_2, st_hv(st_ref_2), st_sz(&st));
      match tmp_3 {
        (v54, v56) => {
          let tmp_4 = done.length();
          let tmp_5 = u < tmp_4;
          let tmp_6 = done.get_cloned(u);
          let tmp_7 = andb(tmp_5, tmp_6 == int63!(0));
          match bdec(tmp_7) {
            sumbool::left => {
              std::mem::drop(tmp_1);
              let st_clone = Rc::clone(&st);
              let tmp_8 = st_dist(st_clone);
              let tmp_9 = tmp_8.get_cloned(u);
              std::mem::drop(tmp_8);
              let tmp_10 = off.get_cloned(u + int63!(1));
              let tmp_11 = off.get_cloned(u);
              let st_clone_1 = Rc::clone(&st);
              let tmp_12 = st_dist(st_clone_1);
              let tmp_13 = st_sz_owned(st) - int63!(1);
              let adj_clone = Clone::clone(&adj);
              let wt_clone = Clone::clone(&wt);
              let st2 = scan_1(adj_clone, wt_clone, tmp_9, tmp_10, tmp_11, tmp_12, v54, v56, tmp_13);
              main_1(off, adj, wt, done.set(u, int63!(1)), st2, ())
            },
            sumbool::right => {
              std::mem::drop(tmp_1);
              let st_clone_2 = Rc::clone(&st);
              main_1(off, adj, wt, done, Rc::new(St { st_dist: st_dist(st_clone_2), st_hk: v54, st_hv: v56, st_sz: st_sz_owned(st) - int63!(1) }), ())
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(off);
      std::mem::drop(adj);
      std::mem::drop(wt);
      std::mem::drop(done);
      st_dist(st)
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.out_loop
// Variant: uncurried
pub fn out_loop_1(dist: Array<Int63>, n: Int63, v: Int63, out: Array<Rc<option<Int63>>>) -> Array<Rc<option<Int63>>> {
  out_loop(dist, n, v, out, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.out_loop (local: out_loop)
// Variant: uncurried, lifted
pub fn out_loop(dist: Array<Int63>, n: Int63, v: Int63, out: Array<Rc<option<Int63>>>, _H: ()) -> Array<Rc<option<Int63>>> {
  let tmp = v < n;
  match bdec(tmp) {
    sumbool::left => {
      let d = dist.get_cloned(v);
      let tmp_1 = v + int63!(1);
      let tmp_2 = __rocq_global_253;
      let tmp_3 = if d == tmp_2 {
        Rc::new(option::<Int63>::None)
      } else {
        Rc::new(option::<Int63>::Some(d))
      };
      out_loop(dist, n, tmp_1, out.set(v, tmp_3), ())
    },
    sumbool::right => {
      std::mem::drop(dist);
      out
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.dijkstra_impl
// Variant: uncurried
pub fn dijkstra_impl(n: Int63, us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>, s: Int63) -> Array<Rc<option<Int63>>> {
  let m = us.length();
  let tmp = Array::<Int63>::make(n + int63!(1), int63!(0));
  let us_clone = Clone::clone(&us);
  let c = count_loop_1(us_clone, m, int63!(0), tmp);
  let off = prefix_loop_1(n, int63!(0), c);
  let off_ref = &off;
  let tmp_1 = off_ref.copy();
  let tmp_2 = Array::<Int63>::make(m, int63!(0));
  let tmp_3 = Array::<Int63>::make(m, int63!(0));
  let tmp_4 = fill_loop_1(us, vs, ws, m, int63!(0), tmp_1, tmp_2, tmp_3);
  match tmp_4 {
    (v82, v84) => {
      let dist0 = Array::<Int63>::make(n, __rocq_global_253).set(s, int63!(0));
      let hk0 = Array::<Int63>::make(m + int63!(1), int63!(0));
      let hv0 = Array::<Int63>::make(m + int63!(1), int63!(0)).set(int63!(0), s);
      let dist = main_2(off, v82, v84, Array::<Int63>::make(n, int63!(0)), Rc::new(St { st_dist: dist0, st_hk: hk0, st_hv: hv0, st_sz: int63!(1) }));
      let tmp_5 = Array::<Rc<option<Int63>>>::make(n, Rc::new(option::<Int63>::None));
      out_loop_1(dist, n, int63!(0), tmp_5)
    },
  }
}
const __rocq_global_253: Int63 = int63!(9223372036854775807);