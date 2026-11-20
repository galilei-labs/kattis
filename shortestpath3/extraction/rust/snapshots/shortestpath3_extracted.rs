#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

pub enum answer<D: 'static> {
  Dist { distance: D },
  Impossible,
  MinusInfinity,
}

impl<D: Clone + 'static> Clone for answer<D> {
  fn clone(&self) -> Self {
    match self {
      answer::Dist { distance: __field0 } => answer::Dist { distance: Clone::clone(__field0) },
      answer::Impossible => answer::Impossible,
      answer::MinusInfinity => answer::MinusInfinity,
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

pub type sint = Int63;

// Rocq: Shortestpath3.shortestpath3_implem.INF
pub fn INF() -> Int63 {
  int63!(4611686018427387903)
}

// Rocq: Shortestpath3.shortestpath3_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.relax
// Variant: uncurried
pub fn relax(us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>, j: Int63, d: Array<Int63>, ch: bool) -> (Array<Int63>, bool) {
  let tmp = us.get_cloned(j);
  let du = d.get_cloned(tmp);
  if du == __rocq_global_7 {
    std::mem::drop(vs);
    std::mem::drop(ws);
    std::mem::drop(us);
    (d, ch)
  } else {
    let v = vs.get_cloned(j);
    let tmp_1 = ws.get_cloned(j);
    let nd = du + tmp_1;
    let tmp_2 = d.get_cloned(v);
    if nd.ltsb(tmp_2) {
      std::mem::drop(vs);
      std::mem::drop(ws);
      std::mem::drop(us);
      (d.set(v, nd), true)
    } else {
      std::mem::drop(vs);
      std::mem::drop(ws);
      std::mem::drop(us);
      (d, ch)
    }
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.edges_loop
// Variant: uncurried
pub fn edges_loop_1(us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>, m: Int63, j: Int63, d: Array<Int63>, ch: bool) -> (Array<Int63>, bool) {
  edges_loop(us, vs, ws, m, j, d, ch, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.edges_loop (local: edges_loop)
// Variant: uncurried, lifted
pub fn edges_loop(us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>, m: Int63, j: Int63, d: Array<Int63>, ch: bool, _H: ()) -> (Array<Int63>, bool) {
  let tmp = j < m;
  match bdec(tmp) {
    sumbool::left => {
      let us_clone = Clone::clone(&us);
      let vs_clone = Clone::clone(&vs);
      let ws_clone = Clone::clone(&ws);
      let tmp_1 = relax(us_clone, vs_clone, ws_clone, j, d, ch);
      match tmp_1 {
        (v37, v39) => {
          edges_loop(us, vs, ws, m, j + int63!(1), v37, v39, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(us);
      std::mem::drop(vs);
      std::mem::drop(ws);
      (d, ch)
    },
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.rounds_loop
// Variant: uncurried
pub fn rounds_loop_1(us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>, m: Int63, R: Int63, k: Int63, d: Array<Int63>) -> Array<Int63> {
  rounds_loop(us, vs, ws, m, R, k, d, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.rounds_loop (local: rounds_loop)
// Variant: uncurried, lifted
pub fn rounds_loop(us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>, m: Int63, R: Int63, k: Int63, d: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = k < R;
  match bdec(tmp) {
    sumbool::left => {
      let us_clone = Clone::clone(&us);
      let vs_clone = Clone::clone(&vs);
      let ws_clone = Clone::clone(&ws);
      let tmp_1 = edges_loop_1(us_clone, vs_clone, ws_clone, m, int63!(0), d, false);
      match tmp_1 {
        (v43, v45) => {
          if v45 {
            rounds_loop(us, vs, ws, m, R, k + int63!(1), v43, ())
          } else {
            std::mem::drop(us);
            std::mem::drop(vs);
            std::mem::drop(ws);
            v43
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(us);
      std::mem::drop(vs);
      std::mem::drop(ws);
      d
    },
  }
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

// Rocq: Shortestpath3.shortestpath3_implem.seed_loop
// Variant: uncurried
pub fn seed_loop_1(us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>, d: Array<Int63>, m: Int63, j: Int63, mk: Array<Int63>, q: Array<Int63>, tl: Int63) -> ((Array<Int63>, Array<Int63>), Int63) {
  seed_loop(us, vs, ws, d, m, j, mk, q, tl, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.seed_loop (local: seed_loop)
// Variant: uncurried, lifted
pub fn seed_loop(us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>, d: Array<Int63>, m: Int63, j: Int63, mk: Array<Int63>, q: Array<Int63>, tl: Int63, _H: ()) -> ((Array<Int63>, Array<Int63>), Int63) {
  let tmp = j < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = us.get_cloned(j);
      let du = d.get_cloned(tmp_1);
      let v = vs.get_cloned(j);
      let tmp_2 = negb(du == __rocq_global_7);
      let tmp_3 = ws.get_cloned(j);
      let tmp_4 = du + tmp_3;
      let tmp_5 = d.get_cloned(v);
      let tmp_6 = andb(tmp_2, tmp_4.ltsb(tmp_5));
      let tmp_7 = mk.get_cloned(v);
      let tmp_8 = tmp_7 == int63!(0);
      if andb(tmp_6, tmp_8) {
        seed_loop(us, vs, ws, d, m, j + int63!(1), mk.set(v, int63!(1)), q.set(tl, v), tl + int63!(1), ())
      } else {
        seed_loop(us, vs, ws, d, m, j + int63!(1), mk, q, tl, ())
      }
    },
    sumbool::right => {
      std::mem::drop(us);
      std::mem::drop(vs);
      std::mem::drop(ws);
      std::mem::drop(d);
      ((mk, q), tl)
    },
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.build_loop
// Variant: uncurried
pub fn build_loop_1(us: Array<Int63>, m: Int63, j: Int63, hd: Array<Int63>, nx: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  build_loop(us, m, j, hd, nx, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.build_loop (local: build_loop)
// Variant: uncurried, lifted
pub fn build_loop(us: Array<Int63>, m: Int63, j: Int63, hd: Array<Int63>, nx: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = j < m;
  match bdec(tmp) {
    sumbool::left => {
      let u = us.get_cloned(j);
      let h = hd.get_cloned(u);
      build_loop(us, m, j + int63!(1), hd.set(u, j + int63!(1)), nx.set(j, h), ())
    },
    sumbool::right => {
      std::mem::drop(us);
      (hd, nx)
    },
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.adj_loop
// Variant: uncurried
pub fn adj_loop_1(vs: Array<Int63>, nx: Array<Int63>, e: Int63, mk: Array<Int63>, q: Array<Int63>, tl: Int63) -> ((Array<Int63>, Array<Int63>), Int63) {
  adj_loop(vs, nx, e, mk, q, tl, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.adj_loop (local: adj_loop)
// Variant: uncurried, lifted
pub fn adj_loop(vs: Array<Int63>, nx: Array<Int63>, e: Int63, mk: Array<Int63>, q: Array<Int63>, tl: Int63, _H: ()) -> ((Array<Int63>, Array<Int63>), Int63) {
  let tmp = int63!(0) < e;
  match bdec(tmp) {
    sumbool::left => {
      let j = e - int63!(1);
      let v = vs.get_cloned(j);
      let e_ = nx.get_cloned(j);
      let tmp_1 = e_ < e;
      match bdec(tmp_1) {
        sumbool::left => {
          let tmp_2 = mk.get_cloned(v);
          if tmp_2 == int63!(0) {
            adj_loop(vs, nx, e_, mk.set(v, int63!(1)), q.set(tl, v), tl + int63!(1), ())
          } else {
            adj_loop(vs, nx, e_, mk, q, tl, ())
          }
        },
        sumbool::right => {
          std::mem::drop(vs);
          std::mem::drop(nx);
          ((mk, q), tl)
        },
      }
    },
    sumbool::right => {
      std::mem::drop(vs);
      std::mem::drop(nx);
      ((mk, q), tl)
    },
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.bfs_loop
// Variant: uncurried
pub fn bfs_loop_1(vs: Array<Int63>, hd: Array<Int63>, nx: Array<Int63>, n: Int63, h: Int63, mk: Array<Int63>, q: Array<Int63>, tl: Int63) -> Array<Int63> {
  bfs_loop(vs, hd, nx, n, h, mk, q, tl, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.bfs_loop (local: bfs_loop)
// Variant: uncurried, lifted
pub fn bfs_loop(vs: Array<Int63>, hd: Array<Int63>, nx: Array<Int63>, n: Int63, h: Int63, mk: Array<Int63>, q: Array<Int63>, tl: Int63, _H: ()) -> Array<Int63> {
  let tmp = h < tl;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = h < n;
      match bdec(tmp_1) {
        sumbool::left => {
          let x = q.get_cloned(h);
          let tmp_2 = hd.get_cloned(x);
          let vs_clone = Clone::clone(&vs);
          let nx_clone = Clone::clone(&nx);
          let tmp_3 = adj_loop_1(vs_clone, nx_clone, tmp_2, mk, q, tl);
          match tmp_3 {
            (v56, v58) => {
              match v56 {
                (v61, v63) => {
                  bfs_loop(vs, hd, nx, n, h + int63!(1), v61, v63, v58, ())
                },
              }
            },
          }
        },
        sumbool::right => {
          std::mem::drop(vs);
          std::mem::drop(hd);
          std::mem::drop(nx);
          std::mem::drop(q);
          mk
        },
      }
    },
    sumbool::right => {
      std::mem::drop(vs);
      std::mem::drop(hd);
      std::mem::drop(nx);
      std::mem::drop(q);
      mk
    },
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.answer_of
// Variant: uncurried
pub fn answer_of(d: Array<Int63>, mk: Array<Int63>, t: Int63) -> Rc<answer<Int63>> {
  let x = d.get_cloned(t);
  if x == __rocq_global_7 {
    std::mem::drop(mk);
    std::mem::drop(d);
    Rc::new(answer::<Int63>::Impossible)
  } else {
    let tmp = mk.get_cloned(t);
    if tmp == int63!(0) {
      std::mem::drop(mk);
      std::mem::drop(d);
      Rc::new(answer::<Int63>::Dist { distance: x })
    } else {
      std::mem::drop(mk);
      std::mem::drop(d);
      Rc::new(answer::<Int63>::MinusInfinity)
    }
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.ans_loop
// Variant: uncurried
pub fn ans_loop_1(d: Array<Int63>, mk: Array<Int63>, qs: Array<Int63>, Q: Int63, i: Int63, out: Array<Rc<answer<Int63>>>) -> Array<Rc<answer<Int63>>> {
  ans_loop(d, mk, qs, Q, i, out, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.ans_loop (local: ans_loop)
// Variant: uncurried, lifted
pub fn ans_loop(d: Array<Int63>, mk: Array<Int63>, qs: Array<Int63>, Q: Int63, i: Int63, out: Array<Rc<answer<Int63>>>, _H: ()) -> Array<Rc<answer<Int63>>> {
  let tmp = i < Q;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = qs.get_cloned(i);
      let d_clone = Clone::clone(&d);
      let mk_clone = Clone::clone(&mk);
      let a_1 = answer_of(d_clone, mk_clone, tmp_1);
      ans_loop(d, mk, qs, Q, i + int63!(1), out.set(i, a_1), ())
    },
    sumbool::right => {
      std::mem::drop(d);
      std::mem::drop(mk);
      std::mem::drop(qs);
      out
    },
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.shortestpath3_impl
// Variant: uncurried
pub fn shortestpath3_impl(n: Int63, s: Int63, us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>, qs: Array<Int63>) -> Array<Rc<answer<Int63>>> {
  let m = us.length();
  let d0 = Array::<Int63>::make(n, __rocq_global_7).set(s, int63!(0));
  let tmp = n - int63!(1);
  let us_clone = Clone::clone(&us);
  let vs_clone = Clone::clone(&vs);
  let ws_clone = Clone::clone(&ws);
  let d = rounds_loop_1(us_clone, vs_clone, ws_clone, m, tmp, int63!(0), d0);
  let tmp_1 = Array::<Int63>::make(n, int63!(0));
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  let us_clone_1 = Clone::clone(&us);
  let vs_clone_1 = Clone::clone(&vs);
  let d_clone = Clone::clone(&d);
  let tmp_3 = seed_loop_1(us_clone_1, vs_clone_1, ws, d_clone, m, int63!(0), tmp_1, tmp_2, int63!(0));
  match tmp_3 {
    (v94, v96) => {
      match v94 {
        (v99, v101) => {
          let tmp_4 = Array::<Int63>::make(n, int63!(0));
          let tmp_5 = Array::<Int63>::make(m, int63!(0));
          let tmp_6 = build_loop_1(us, m, int63!(0), tmp_4, tmp_5);
          match tmp_6 {
            (v132, v134) => {
              let mk_ = bfs_loop_1(vs, v132, v134, n, int63!(0), v99, v101, v96);
              let Q = qs.length();
              let tmp_7 = Array::<Rc<answer<Int63>>>::make(Q, Rc::new(answer::<Int63>::Impossible));
              ans_loop_1(d, mk_, qs, Q, int63!(0), tmp_7)
            },
          }
        },
      }
    },
  }
}
const __rocq_global_7: Int63 = int63!(4611686018427387903);