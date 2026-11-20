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

pub enum answer<A: 'static> {
  Impossible,
  NegInfinity,
  Distance(A),
}

impl<A: Clone + 'static> Clone for answer<A> {
  fn clone(&self) -> Self {
    match self {
      answer::Impossible => answer::Impossible,
      answer::NegInfinity => answer::NegInfinity,
      answer::Distance(__field0) => answer::Distance(Clone::clone(__field0)),
    }
  }
}

pub type uint = Int63;

pub type sint = Int63;

// Rocq: Allpairspath.allpairspath_implem.INF
pub fn INF() -> Int63 {
  int63!(1073741824)
}

// Rocq: Allpairspath.allpairspath_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Allpairspath.allpairspath_implem.for_acc
// Variant: uncurried
pub fn for_acc_1<S: Clone + 'static>(f: Rc<dyn Fn(Int63, S) -> S>, hi: Int63, i: Int63, s: S) -> S {
  for_acc::<S>(f, hi, i, s, ())
}

// Rocq: Allpairspath.allpairspath_implem.for_acc (local: for_acc)
// Variant: uncurried, lifted
pub fn for_acc<S: Clone + 'static>(f: Rc<dyn Fn(Int63, S) -> S>, hi: Int63, i: Int63, s: S, _H: ()) -> S {
  let tmp = i < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let f_ref: &Rc<dyn Fn(Int63, S) -> S> = &f;
      let tmp_2 = f_ref(i, s);
      for_acc::<S>(f, hi, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      std::mem::drop(f);
      s
    },
  }
}

// Rocq: Allpairspath.allpairspath_implem.for_loop
// Variant: uncurried
pub fn for_loop<S: Clone + 'static>(f: Rc<dyn Fn(Int63, S) -> S>, lo: Int63, hi: Int63, s: S) -> S {
  for_acc_1::<S>(f, hi, lo, s)
}

// Rocq: Allpairspath.allpairspath_implem.adj_step
// Variant: borrowed, uncurried
pub fn adj_step(us: &Array<Int63>, k: Int63, st: (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>) {
  let k_1 = k;
  let st_1 = st;
  match st_1 {
    (v6, v8) => {
      let nx = &v6;
      let a_1 = us.get_cloned(k_1);
      let old = nx.get_cloned(a_1);
      let nx_ = v8.set(k_1, old);
      let hd_ = v6.set(a_1, k_1 + int63!(1));
      (hd_, nx_)
    },
  }
}

// Rocq: Allpairspath.allpairspath_implem.build_adj
// Variant: uncurried
pub fn build_adj(n: Int63, m: Int63, us: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  let callback: Rc<dyn Fn(Int63, (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>)> = Rc::new({
    move |v9: Int63, v10: (Array<Int63>, Array<Int63>)| -> (Array<Int63>, Array<Int63>) {
      let us = &us;
      let tmp = adj_step(us, v9, v10);
      tmp
    }
  });
  let tmp_1 = Array::<Int63>::make(n, int63!(0));
  let tmp_2 = Array::<Int63>::make(m, int63!(0));
  for_loop::<(Array<Int63>, Array<Int63>)>(callback, int63!(0), m, (tmp_1, tmp_2))
}

// Rocq: Allpairspath.allpairspath_implem.seed_step
// Variant: borrowed, uncurried
pub fn seed_step(seed: &Array<bool>, a_1: Int63, st: ((Array<bool>, Array<Int63>), Int63)) -> ((Array<bool>, Array<Int63>), Int63) {
  let a_2 = a_1;
  let st_1 = st;
  match &st_1 {
    (tl, p) => {
      match tl {
        (q, mark) => {
          if seed.get_cloned(a_2) {
            let tmp = true;
            let tmp_1 = Clone::clone(q).set(a_2, tmp);
            let mark_clone = Clone::clone(mark);
            let tmp_2 = (tmp_1, mark_clone.set(Clone::clone(p), a_2));
            let tmp_3 = int63!(1);
            let p_clone = Clone::clone(p);
            std::mem::drop(st_1);
            (tmp_2, p_clone + tmp_3)
          } else {
            st_1
          }
        },
      }
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

// Rocq: Allpairspath.allpairspath_implem.chain_acc
// Variant: uncurried
pub fn chain_acc_1<S: Clone + 'static>(nx: Array<Int63>, f: Rc<dyn Fn(Int63, S) -> S>, cur: Int63, s: S) -> S {
  chain_acc::<S>(f, nx, cur, s, ())
}

// Rocq: Allpairspath.allpairspath_implem.chain_acc (local: chain_acc)
// Variant: uncurried, lifted
pub fn chain_acc<S: Clone + 'static>(f: Rc<dyn Fn(Int63, S) -> S>, nx: Array<Int63>, cur: Int63, s: S, _H: ()) -> S {
  let tmp = int63!(0) < cur;
  match bdec(tmp) {
    sumbool::left => {
      let e = cur - int63!(1);
      let f_ref: &Rc<dyn Fn(Int63, S) -> S> = &f;
      let s_ = f_ref(e, s);
      let c_ = nx.get_cloned(e);
      let tmp_1 = c_ < cur;
      match bdec(tmp_1) {
        sumbool::left => {
          chain_acc::<S>(f, nx, c_, s_, ())
        },
        sumbool::right => {
          std::mem::drop(nx);
          std::mem::drop(f);
          s_
        },
      }
    },
    sumbool::right => {
      std::mem::drop(f);
      std::mem::drop(nx);
      s
    },
  }
}

// Rocq: Allpairspath.allpairspath_implem.chain_fold
// Variant: uncurried
pub fn chain_fold<S: Clone + 'static>(nx: Array<Int63>, f: Rc<dyn Fn(Int63, S) -> S>, cur: Int63, s: S) -> S {
  chain_acc_1::<S>(nx, f, cur, s)
}

// Rocq: Allpairspath.allpairspath_implem.bfs_visit
// Variant: borrowed, uncurried
pub fn bfs_visit(vs: &Array<Int63>, e: Int63, st: ((Array<bool>, Array<Int63>), Int63)) -> ((Array<bool>, Array<Int63>), Int63) {
  let e_1 = e;
  let st_1 = st;
  match &st_1 {
    (tl, p) => {
      match tl {
        (q, mark) => {
          let b_1 = vs.get_cloned(e_1);
          if q.get_cloned(b_1) {
            st_1
          } else {
            let tmp = true;
            let tmp_1 = Clone::clone(q).set(b_1, tmp);
            let mark_clone = Clone::clone(mark);
            let tmp_2 = (tmp_1, mark_clone.set(Clone::clone(p), b_1));
            let tmp_3 = int63!(1);
            let p_clone = Clone::clone(p);
            std::mem::drop(st_1);
            (tmp_2, p_clone + tmp_3)
          }
        },
      }
    },
  }
}

// Rocq: Allpairspath.allpairspath_implem.bfs_acc
// Variant: uncurried
pub fn bfs_acc_1(hd: Array<Int63>, nx: Array<Int63>, vs: Array<Int63>, cap: Int63, h: Int63, st: ((Array<bool>, Array<Int63>), Int63)) -> Array<bool> {
  bfs_acc(hd, nx, vs, cap, h, st, ())
}

// Rocq: Allpairspath.allpairspath_implem.bfs_acc (local: bfs_acc)
// Variant: uncurried, lifted
pub fn bfs_acc(hd: Array<Int63>, nx: Array<Int63>, vs: Array<Int63>, cap: Int63, h: Int63, st: ((Array<bool>, Array<Int63>), Int63), _H: ()) -> Array<bool> {
  match &st {
    (tl, p) => {
      match tl {
        (q, mark) => {
          let tmp = andb(h < Clone::clone(p), h < cap);
          match bdec(tmp) {
            sumbool::left => {
              let x = mark.get_cloned(h);
              let tmp_1 = h + int63!(1);
              let vs_clone = Clone::clone(&vs);
              let callback: Rc<dyn Fn(Int63, ((Array<bool>, Array<Int63>), Int63)) -> ((Array<bool>, Array<Int63>), Int63)> = Rc::new({
                move |v59: Int63, v60: ((Array<bool>, Array<Int63>), Int63)| -> ((Array<bool>, Array<Int63>), Int63) {
                  let vs = &vs_clone;
                  let tmp_2 = bfs_visit(vs, v59, v60);
                  tmp_2
                }
              });
              let tmp_3 = hd.get_cloned(x);
              let nx_clone = Clone::clone(&nx);
              bfs_acc(hd, nx, vs, cap, tmp_1, chain_fold::<((Array<bool>, Array<Int63>), Int63)>(nx_clone, callback, tmp_3, st), ())
            },
            sumbool::right => {
              std::mem::drop(hd);
              std::mem::drop(nx);
              std::mem::drop(vs);
              let q_clone = Clone::clone(q);
              std::mem::drop(st);
              q_clone
            },
          }
        },
      }
    },
  }
}

// Rocq: Allpairspath.allpairspath_implem.closure
// Variant: uncurried
pub fn closure(n: Int63, hd: Array<Int63>, nx: Array<Int63>, vs: Array<Int63>, seed: Array<bool>) -> Array<bool> {
  let callback: Rc<dyn Fn(Int63, ((Array<bool>, Array<Int63>), Int63)) -> ((Array<bool>, Array<Int63>), Int63)> = Rc::new({
    move |v11: Int63, v12: ((Array<bool>, Array<Int63>), Int63)| -> ((Array<bool>, Array<Int63>), Int63) {
      let seed = &seed;
      let tmp = seed_step(seed, v11, v12);
      tmp
    }
  });
  let tmp_1 = Array::<bool>::make(n, false);
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  let st0 = for_loop::<((Array<bool>, Array<Int63>), Int63)>(callback, int63!(0), n, ((tmp_1, tmp_2), int63!(0)));
  bfs_acc_1(hd, nx, vs, n, int63!(0), st0)
}

// Rocq: Allpairspath.allpairspath_implem.copy_step
// Variant: uncurried
pub fn copy_step(n: Int63, s: Int63, row: Array<bool>, v: Int63, r: Array<bool>) -> Array<bool> {
  let tmp = s * n + v;
  let tmp_1 = row.get_cloned(v);
  std::mem::drop(row);
  r.set(tmp, tmp_1)
}

// Rocq: Allpairspath.allpairspath_implem.reach_row
// Variant: uncurried
pub fn reach_row(n: Int63, hd: Array<Int63>, nx: Array<Int63>, vs: Array<Int63>, s: Int63, r: Array<bool>) -> Array<bool> {
  let tmp = Array::<bool>::make(n, false);
  let row = closure(n, hd, nx, vs, tmp.set(s, true));
  let callback: Rc<dyn Fn(Int63, Array<bool>) -> Array<bool>> = Rc::new({
    let __anf_capture_42 = n;
    let __anf_capture_44 = s;
    move |v48: Int63, v49: Array<bool>| -> Array<bool> {
      let tmp_1 = Clone::clone(&__anf_capture_42);
      let tmp_2 = Clone::clone(&__anf_capture_44);
      let row_clone = Clone::clone(&row);
      copy_step(tmp_1, tmp_2, row_clone, v48, v49)
    }
  });
  for_loop::<Array<bool>>(callback, int63!(0), n, r)
}

// Rocq: Allpairspath.allpairspath_implem.reach_matrix
// Variant: uncurried
pub fn reach_matrix(n: Int63, hd: Array<Int63>, nx: Array<Int63>, vs: Array<Int63>) -> Array<bool> {
  let callback: Rc<dyn Fn(Int63, Array<bool>) -> Array<bool>> = Rc::new({
    let __anf_capture_14 = n;
    move |v22: Int63, v23: Array<bool>| -> Array<bool> {
      let tmp = Clone::clone(&__anf_capture_14);
      let hd_clone = Clone::clone(&hd);
      let nx_clone = Clone::clone(&nx);
      let vs_clone = Clone::clone(&vs);
      reach_row(tmp, hd_clone, nx_clone, vs_clone, v22, v23)
    }
  });
  let tmp_1 = n * n;
  for_loop::<Array<bool>>(callback, int63!(0), n, Array::<bool>::make(tmp_1, false))
}

// Rocq: Allpairspath.allpairspath_implem.bf_edge
// Variant: uncurried
pub fn bf_edge(us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>, keep: Rc<dyn Fn(Int63) -> bool>, k: Int63, h: Array<Int63>) -> Array<Int63> {
  let keep_ref: &Rc<dyn Fn(Int63) -> bool> = &keep;
  let tmp = keep_ref(k);
  if tmp {
    let a_1 = us.get_cloned(k);
    let b_1 = vs.get_cloned(k);
    let tmp_1 = h.get_cloned(a_1);
    let tmp_2 = ws.get_cloned(k);
    let nb = tmp_1 + tmp_2;
    let tmp_3 = h.get_cloned(b_1);
    if nb.ltsb(tmp_3) {
      std::mem::drop(us);
      std::mem::drop(vs);
      std::mem::drop(ws);
      std::mem::drop(keep);
      h.set(b_1, nb)
    } else {
      std::mem::drop(us);
      std::mem::drop(vs);
      std::mem::drop(ws);
      std::mem::drop(keep);
      h
    }
  } else {
    std::mem::drop(us);
    std::mem::drop(vs);
    std::mem::drop(ws);
    std::mem::drop(keep);
    h
  }
}

// Rocq: Allpairspath.allpairspath_implem.bf_round
// Variant: uncurried
pub fn bf_round(m: Int63, us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>, keep: Rc<dyn Fn(Int63) -> bool>, _r: Int63, h: Array<Int63>) -> Array<Int63> {
  let callback: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
    move |v25: Int63, v26: Array<Int63>| -> Array<Int63> {
      let us_clone = Clone::clone(&us);
      let vs_clone = Clone::clone(&vs);
      let ws_clone = Clone::clone(&ws);
      let keep_clone: Rc<dyn Fn(Int63) -> bool> = Rc::clone(&keep);
      bf_edge(us_clone, vs_clone, ws_clone, keep_clone, v25, v26)
    }
  });
  for_loop::<Array<Int63>>(callback, int63!(0), m, h)
}

// Rocq: Allpairspath.allpairspath_implem.bf
// Variant: uncurried
pub fn bf(n: Int63, m: Int63, us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>, keep: Rc<dyn Fn(Int63) -> bool>) -> Array<Int63> {
  let callback: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
    move |v28: Int63, v29: Array<Int63>| -> Array<Int63> {
      let m_clone = Clone::clone(&m);
      let us_clone = Clone::clone(&us);
      let vs_clone = Clone::clone(&vs);
      let ws_clone = Clone::clone(&ws);
      let keep_clone: Rc<dyn Fn(Int63) -> bool> = Rc::clone(&keep);
      bf_round(m_clone, us_clone, vs_clone, ws_clone, keep_clone, v28, v29)
    }
  });
  let tmp = Array::<Int63>::make(n, int63!(0));
  for_loop::<Array<Int63>>(callback, int63!(0), n, tmp)
}

// Rocq: Allpairspath.allpairspath_implem.bad_step
// Variant: uncurried
pub fn bad_step(n: Int63, us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>, R: Array<bool>, h: Array<Int63>, k: Int63, bad: Array<bool>) -> Array<bool> {
  let a_1 = us.get_cloned(k);
  let b_1 = vs.get_cloned(k);
  let tmp = R.get_cloned(b_1 * n + a_1);
  let tmp_1 = h.get_cloned(a_1);
  let tmp_2 = ws.get_cloned(k);
  let tmp_3 = tmp_1 + tmp_2;
  let tmp_4 = h.get_cloned(b_1);
  let tmp_5 = tmp_3.ltsb(tmp_4);
  if andb(tmp, tmp_5) {
    std::mem::drop(us);
    std::mem::drop(ws);
    std::mem::drop(h);
    std::mem::drop(R);
    std::mem::drop(vs);
    bad.set(a_1, true)
  } else {
    std::mem::drop(us);
    std::mem::drop(ws);
    std::mem::drop(h);
    std::mem::drop(R);
    std::mem::drop(vs);
    bad
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

// Rocq: Allpairspath.allpairspath_implem.negseed_step
// Variant: uncurried
pub fn negseed_step(n: Int63, R: Array<bool>, bad: Array<bool>, u: Int63, a_1: Int63, s: Array<bool>) -> Array<bool> {
  let tmp = bad.get_cloned(a_1);
  let tmp_1 = R.get_cloned(u * n + a_1);
  if andb(tmp, tmp_1) {
    std::mem::drop(R);
    std::mem::drop(bad);
    s.set(a_1, true)
  } else {
    std::mem::drop(R);
    std::mem::drop(bad);
    s
  }
}

// Rocq: Allpairspath.allpairspath_implem.swap
// Variant: uncurried
pub fn swap(t: Array<Int63>, i: Int63, j: Int63) -> Array<Int63> {
  let a_1 = t.get_cloned(i);
  let b_1 = t.get_cloned(j);
  t.set(i, b_1).set(j, a_1)
}

// Rocq: Allpairspath.allpairspath_implem.sift_down
// Variant: uncurried
pub fn sift_down_1(t: Array<Int63>, s: Int63, i: Int63) -> Array<Int63> {
  sift_down(t, s, i, ())
}

// Rocq: Allpairspath.allpairspath_implem.sift_down (local: sift_down)
// Variant: uncurried, lifted
pub fn sift_down(t: Array<Int63>, s: Int63, i: Int63, _H: ()) -> Array<Int63> {
  let l = int63!(2) * i + int63!(1);
  if l < s {
    let r = l + int63!(1);
    let tmp = r < s;
    let tmp_1 = t.get_cloned(r);
    let tmp_2 = t.get_cloned(l);
    let tmp_3 = tmp_1 < tmp_2;
    let c = if andb(tmp, tmp_3) {
      r
    } else {
      l
    };
    let tmp_4 = andb(i < c, c < s);
    match bdec(tmp_4) {
      sumbool::left => {
        let tmp_5 = t.get_cloned(c);
        let tmp_6 = t.get_cloned(i);
        if tmp_5 < tmp_6 {
          sift_down(swap(t, i, c), s, c, ())
        } else {
          t
        }
      },
      sumbool::right => {
        t
      },
    }
  } else {
    t
  }
}

// Rocq: Allpairspath.allpairspath_implem.hpop
// Variant: uncurried
pub fn hpop(t: Array<Int63>, s: Int63) -> (Int63, Array<Int63>) {
  let top = t.get_cloned(int63!(0));
  let s_ = s - int63!(1);
  let last = t.get_cloned(s_);
  (top, sift_down_1(t.set(int63!(0), last), s_, int63!(0)))
}

// Rocq: Allpairspath.allpairspath_implem.sift_up
// Variant: uncurried
pub fn sift_up_1(t: Array<Int63>, i: Int63) -> Array<Int63> {
  sift_up(t, i, ())
}

// Rocq: Allpairspath.allpairspath_implem.sift_up (local: sift_up)
// Variant: uncurried, lifted
pub fn sift_up(t: Array<Int63>, i: Int63, _H: ()) -> Array<Int63> {
  let tmp = int63!(0) < i;
  match bdec(tmp) {
    sumbool::left => {
      let p = (i - int63!(1)) / int63!(2);
      let tmp_1 = t.get_cloned(i);
      let tmp_2 = t.get_cloned(p);
      if tmp_1 < tmp_2 {
        sift_up(swap(t, i, p), p, ())
      } else {
        t
      }
    },
    sumbool::right => {
      t
    },
  }
}

// Rocq: Allpairspath.allpairspath_implem.hpush
// Variant: uncurried
pub fn hpush(t: Array<Int63>, s: Int63, x: Int63) -> Array<Int63> {
  sift_up_1(t.set(s, x), s)
}

// Rocq: Allpairspath.allpairspath_implem.relax
// Variant: borrowed, uncurried
pub fn relax(vs: &Array<Int63>, ws: &Array<Int63>, bad: &Array<bool>, done: &Array<bool>, p: &Array<Int63>, v: Int63, d: Int63, e: Int63, st: ((Array<Int63>, Array<Int63>), Int63)) -> ((Array<Int63>, Array<Int63>), Int63) {
  let v_1 = v;
  let d_1 = d;
  let e_1 = e;
  let st_1 = st;
  match &st_1 {
    (sz, p0) => {
      match sz {
        (hp, D) => {
          let b_1 = vs.get_cloned(e_1);
          let tmp = negb(bad.get_cloned(b_1));
          let tmp_1 = negb(done.get_cloned(b_1));
          if andb(tmp, tmp_1) {
            let nd = d_1 + ws.get_cloned(e_1) + p.get_cloned(v_1) - p.get_cloned(b_1);
            let tmp_2 = hp.get_cloned(b_1);
            if nd < tmp_2 {
              let tmp_3 = Clone::clone(hp).set(b_1, nd);
              let tmp_4 = nd * int63!(256) + b_1;
              let D_clone = Clone::clone(D);
              let tmp_5 = (tmp_3, hpush(D_clone, Clone::clone(p0), tmp_4));
              let tmp_6 = int63!(1);
              let p0_clone = Clone::clone(p0);
              std::mem::drop(st_1);
              (tmp_5, p0_clone + tmp_6)
            } else {
              st_1
            }
          } else {
            st_1
          }
        },
      }
    },
  }
}

// Rocq: Allpairspath.allpairspath_implem.dij_body
// Variant: borrowed, uncurried
pub fn dij_body(hd: &Array<Int63>, nx: &Array<Int63>, vs: &Array<Int63>, ws: &Array<Int63>, bad: &Array<bool>, p: &Array<Int63>, st: (((Array<Int63>, Array<bool>), Array<Int63>), Int63)) -> (((Array<Int63>, Array<bool>), Array<Int63>), Int63) {
  let st_1 = st;
  match st_1 {
    (v9, v11) => {
      match v9 {
        (v14, v16) => {
          match v14 {
            (v19, v21) => {
              let D = &v21;
              let tmp = hpop(v16, v11);
              match tmp {
                (v31, v33) => {
                  let sz1 = v11 - int63!(1);
                  let v = v31 % int63!(256);
                  let d = v31 / int63!(256);
                  let tmp_1 = D.get_cloned(v);
                  if tmp_1 {
                    (((v19, v21), v33), sz1)
                  } else {
                    let done_ = v21.set(v, true);
                    let D_ = v19.set(v, d);
                    let tmp_2 = bad;
                    if tmp_2.get_cloned(v) {
                      (((D_, done_), v33), sz1)
                    } else {
                      let vs_clone = Clone::clone(vs);
                      let ws_clone = Clone::clone(ws);
                      let bad_clone = Clone::clone(bad);
                      let done__clone = Clone::clone(&done_);
                      let p_clone = Clone::clone(p);
                      let callback: Rc<dyn Fn(Int63, ((Array<Int63>, Array<Int63>), Int63)) -> ((Array<Int63>, Array<Int63>), Int63)> = Rc::new({
                        let __anf_capture_156 = v;
                        let __anf_capture_158 = d;
                        move |v160: Int63, v161: ((Array<Int63>, Array<Int63>), Int63)| -> ((Array<Int63>, Array<Int63>), Int63) {
                          let vs = &vs_clone;
                          let ws = &ws_clone;
                          let bad = &bad_clone;
                          let done_ = &done__clone;
                          let p = &p_clone;
                          let tmp_3 = relax(vs, ws, bad, done_, p, Clone::clone(&__anf_capture_156), Clone::clone(&__anf_capture_158), v160, v161);
                          tmp_3
                        }
                      });
                      let tmp_4 = hd.get_cloned(v);
                      let tmp_5 = ((D_, v33), sz1);
                      let tmp_6 = chain_fold::<((Array<Int63>, Array<Int63>), Int63)>(Clone::clone(nx), callback, tmp_4, tmp_5);
                      match tmp_6 {
                        (v208, v210) => {
                          match v208 {
                            (v213, v215) => {
                              (((v213, done_), v215), v210)
                            },
                          }
                        },
                      }
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
}

// Rocq: Allpairspath.allpairspath_implem.dij_acc
// Variant: borrowed, uncurried
pub fn dij_acc_1(hd: &Array<Int63>, nx: &Array<Int63>, vs: &Array<Int63>, ws: &Array<Int63>, bad: &Array<bool>, p: &Array<Int63>, lim: Int63, steps: Int63, st: (((Array<Int63>, Array<bool>), Array<Int63>), Int63)) -> Array<Int63> {
  let lim_1 = lim;
  let steps_1 = steps;
  let st_1 = st;
  dij_acc(hd, nx, vs, ws, bad, p, lim_1, steps_1, st_1, ())
}

// Rocq: Allpairspath.allpairspath_implem.dij_acc (local: dij_acc)
// Variant: borrowed, uncurried, lifted
pub fn dij_acc(hd: &Array<Int63>, nx: &Array<Int63>, vs: &Array<Int63>, ws: &Array<Int63>, bad: &Array<bool>, p: &Array<Int63>, lim: Int63, steps: Int63, st: (((Array<Int63>, Array<bool>), Array<Int63>), Int63), _H: ()) -> Array<Int63> {
  let lim_1 = lim;
  let steps_1 = steps;
  let st_1 = st;
  match &st_1 {
    (sz, p0) => {
      match sz {
        (hp, _p1) => {
          match hp {
            (done, _D) => {
              let tmp = andb(int63!(0) < Clone::clone(p0), steps_1 < lim_1);
              match bdec(tmp) {
                sumbool::left => {
                  let tmp_1 = steps_1 + int63!(1);
                  let tmp_2 = hd;
                  let tmp_3 = nx;
                  let tmp_4 = vs;
                  let tmp_5 = ws;
                  let tmp_6 = bad;
                  let tmp_7 = p;
                  dij_acc(hd, nx, vs, ws, bad, p, lim_1, tmp_1, dij_body(tmp_2, tmp_3, tmp_4, tmp_5, tmp_6, tmp_7, st_1), ())
                },
                sumbool::right => {
                  let done_clone = Clone::clone(done);
                  std::mem::drop(st_1);
                  done_clone
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Allpairspath.allpairspath_implem.dijkstra
// Variant: borrowed, uncurried
pub fn dijkstra(n: Int63, m: Int63, hd: &Array<Int63>, nx: &Array<Int63>, vs: &Array<Int63>, ws: &Array<Int63>, bad: &Array<bool>, p: &Array<Int63>, u: Int63) -> Array<Int63> {
  let n_1 = n;
  let m_1 = m;
  let u_1 = u;
  let D0 = Array::<Int63>::make(n_1, __rocq_global_833).set(u_1, int63!(0));
  let hp0 = Array::<Int63>::make(m_1 + int63!(1), int63!(0)).set(int63!(0), u_1);
  dij_acc_1(hd, nx, vs, ws, bad, p, m_1 + int63!(1), int63!(0), (((D0, Array::<bool>::make(n_1, false)), hp0), int63!(1)))
}

// Rocq: Allpairspath.allpairspath_implem.cell
// Variant: borrowed, uncurried
pub fn cell(n: Int63, R: &Array<bool>, neg: &Array<bool>, D: &Array<Int63>, p: &Array<Int63>, u: Int63, v: Int63) -> Rc<answer<Int63>> {
  let n_1 = n;
  let u_1 = u;
  let v_1 = v;
  if neg.get_cloned(v_1) {
    Rc::new(answer::<Int63>::NegInfinity)
  } else {
    let tmp = u_1 * n_1 + v_1;
    if R.get_cloned(tmp) {
      Rc::new(answer::<Int63>::Distance(D.get_cloned(v_1) - p.get_cloned(u_1) + p.get_cloned(v_1)))
    } else {
      Rc::new(answer::<Int63>::Impossible)
    }
  }
}

// Rocq: Allpairspath.allpairspath_implem.row_of
// Variant: borrowed, uncurried
pub fn row_of(n: Int63, m: Int63, hd: &Array<Int63>, nx: &Array<Int63>, vs: &Array<Int63>, ws: &Array<Int63>, R: &Array<bool>, bad: &Array<bool>, p: &Array<Int63>, u: Int63) -> Array<Rc<answer<Int63>>> {
  let m_1 = m;
  let R_clone = Clone::clone(R);
  let bad_clone = Clone::clone(bad);
  let callback: Rc<dyn Fn(Int63, Array<bool>) -> Array<bool>> = Rc::new({
    let __anf_capture_25 = n;
    let __anf_capture_31 = u;
    move |v33: Int63, v34: Array<bool>| -> Array<bool> {
      let tmp = Clone::clone(&__anf_capture_25);
      let tmp_1 = Clone::clone(&R_clone);
      let tmp_2 = Clone::clone(&bad_clone);
      let tmp_3 = Clone::clone(&__anf_capture_31);
      negseed_step(tmp, tmp_1, tmp_2, tmp_3, v33, v34)
    }
  });
  let tmp_4 = Array::<bool>::make(n, false);
  let seed = for_loop::<Array<bool>>(callback, int63!(0), n, tmp_4);
  let neg = closure(n, Clone::clone(hd), Clone::clone(nx), Clone::clone(vs), seed);
  let D = dijkstra(n, m_1, hd, nx, vs, ws, bad, p, u);
  let R_clone_1 = Clone::clone(R);
  let p_clone = Clone::clone(p);
  let callback_1: Rc<dyn Fn(Int63, Array<Rc<answer<Int63>>>) -> Array<Rc<answer<Int63>>>> = Rc::new({
    let __anf_capture_122 = n;
    let __anf_capture_132 = u;
    move |v: Int63, r: Array<Rc<answer<Int63>>>| -> Array<Rc<answer<Int63>>> {
      let tmp_5 = cell(Clone::clone(&__anf_capture_122), &R_clone_1, &neg, &D, &p_clone, Clone::clone(&__anf_capture_132), v);
      r.set(v, tmp_5)
    }
  });
  let tmp_6 = Array::<Rc<answer<Int63>>>::make(n, Rc::new(answer::<Int63>::Impossible));
  for_loop::<Array<Rc<answer<Int63>>>>(callback_1, int63!(0), n, tmp_6)
}

// Rocq: Allpairspath.allpairspath_implem.apsp_rows
// Variant: uncurried
pub fn apsp_rows(n: Int63, m: Int63, hd: Array<Int63>, nx: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>, R: Array<bool>, bad: Array<bool>, p: Array<Int63>) -> Array<Array<Rc<answer<Int63>>>> {
  let callback: Rc<dyn Fn(Int63, Array<Array<Rc<answer<Int63>>>>) -> Array<Array<Rc<answer<Int63>>>>> = Rc::new({
    let __anf_capture_29 = n;
    move |u: Int63, res: Array<Array<Rc<answer<Int63>>>>| -> Array<Array<Rc<answer<Int63>>>> {
      let n = &__anf_capture_29;
      let m = &m;
      let hd = &hd;
      let nx = &nx;
      let vs = &vs;
      let ws = &ws;
      let R = &R;
      let bad = &bad;
      let p = &p;
      let tmp = row_of(Clone::clone(n), Clone::clone(m), hd, nx, vs, ws, R, bad, p, u);
      res.set(u, tmp)
    }
  });
  let tmp_1 = Array::<Array<Rc<answer<Int63>>>>::make(n, Array::<Rc<answer<Int63>>>::make(int63!(0), Rc::new(answer::<Int63>::Impossible)));
  for_loop::<Array<Array<Rc<answer<Int63>>>>>(callback, int63!(0), n, tmp_1)
}

// Rocq: Allpairspath.allpairspath_implem.apsp_core
// Variant: uncurried
pub fn apsp_core(n: Int63, m: Int63, us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>, hd: Array<Int63>, nx: Array<Int63>) -> Array<Array<Rc<answer<Int63>>>> {
  let hd_clone = Clone::clone(&hd);
  let nx_clone = Clone::clone(&nx);
  let vs_clone = Clone::clone(&vs);
  let R = reach_matrix(n, hd_clone, nx_clone, vs_clone);
  let vs_clone_1 = Clone::clone(&vs);
  let us_clone = Clone::clone(&us);
  let R_clone = Clone::clone(&R);
  let callback: Rc<dyn Fn(Int63) -> bool> = Rc::new({
    let __anf_capture_35 = n;
    move |k: Int63| -> bool {
      let vs = &vs_clone_1;
      let n = &__anf_capture_35;
      let us = &us_clone;
      let R = &R_clone;
      let tmp = vs.get_cloned(k) * Clone::clone(n) + us.get_cloned(k);
      R.get_cloned(tmp)
    }
  });
  let us_clone_1 = Clone::clone(&us);
  let vs_clone_2 = Clone::clone(&vs);
  let ws_clone = Clone::clone(&ws);
  let h1 = bf(n, m, us_clone_1, vs_clone_2, ws_clone, callback);
  let us_clone_2 = Clone::clone(&us);
  let vs_clone_3 = Clone::clone(&vs);
  let ws_clone_1 = Clone::clone(&ws);
  let R_clone_1 = Clone::clone(&R);
  let callback_1: Rc<dyn Fn(Int63, Array<bool>) -> Array<bool>> = Rc::new({
    let __anf_capture_101 = n;
    move |v113: Int63, v114: Array<bool>| -> Array<bool> {
      let tmp_1 = Clone::clone(&__anf_capture_101);
      let tmp_2 = Clone::clone(&us_clone_2);
      let tmp_3 = Clone::clone(&vs_clone_3);
      let tmp_4 = Clone::clone(&ws_clone_1);
      let tmp_5 = Clone::clone(&R_clone_1);
      let h1_clone = Clone::clone(&h1);
      bad_step(tmp_1, tmp_2, tmp_3, tmp_4, tmp_5, h1_clone, v113, v114)
    }
  });
  let bad = for_loop::<Array<bool>>(callback_1, int63!(0), m, Array::<bool>::make(n, false));
  let us_clone_3 = Clone::clone(&us);
  let vs_clone_4 = Clone::clone(&vs);
  let bad_clone = Clone::clone(&bad);
  let callback_2: Rc<dyn Fn(Int63) -> bool> = Rc::new({
    move |k: Int63| -> bool {
      let us = &us_clone_3;
      let vs = &vs_clone_4;
      let tmp_6 = negb(bad_clone.get_cloned(us.get_cloned(k)));
      let tmp_7 = bad_clone.get_cloned(vs.get_cloned(k));
      andb(tmp_6, negb(tmp_7))
    }
  });
  let vs_clone_5 = Clone::clone(&vs);
  let ws_clone_2 = Clone::clone(&ws);
  let p = bf(n, m, us, vs_clone_5, ws_clone_2, callback_2);
  apsp_rows(n, m, hd, nx, vs, ws, R, bad, p)
}

// Rocq: Allpairspath.allpairspath_implem.allpairspath_impl
// Variant: uncurried
pub fn allpairspath_impl(n: Int63, us: Array<Int63>, vs: Array<Int63>, ws: Array<Int63>) -> Array<Array<Rc<answer<Int63>>>> {
  let m = us.length();
  let us_clone = Clone::clone(&us);
  let tmp = build_adj(n, m, us_clone);
  match tmp {
    (v16, v18) => {
      apsp_core(n, m, us, vs, ws, v16, v18)
    },
  }
}
const __rocq_global_833: Int63 = int63!(1073741824);