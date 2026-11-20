#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

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

pub type uint = u64;

pub type sint = u64;

// Rocq: Allpairspath.allpairspath_implem.INF
pub fn INF() -> u64 {
  1073741824u64
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Allpairspath.allpairspath_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Allpairspath.allpairspath_implem.for_acc
// Variant: uncurried
pub fn for_acc_1<S: Clone + 'static>(f: Rc<dyn Fn(u64, S) -> S>, hi: u64, i: u64, s: S) -> S {
  for_acc::<S>(f, hi, i, s, ())
}

// Rocq: Allpairspath.allpairspath_implem.for_acc (local: for_acc)
// Variant: uncurried, lifted
pub fn for_acc<S: Clone + 'static>(f: Rc<dyn Fn(u64, S) -> S>, hi: u64, i: u64, s: S, _H: ()) -> S {
  let tmp = ltb(i, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let f_ref: &Rc<dyn Fn(u64, S) -> S> = &f;
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
pub fn for_loop<S: Clone + 'static>(f: Rc<dyn Fn(u64, S) -> S>, lo: u64, hi: u64, s: S) -> S {
  for_acc_1::<S>(f, hi, lo, s)
}

// Rocq: Allpairspath.allpairspath_implem.adj_step
// Variant: borrowed, uncurried
pub fn adj_step(us: &Rc<Array<u64>>, k: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let k_1 = k;
  let st_1 = st;
  match st_1 {
    (v6, v8) => {
      let nx = &v6;
      let a = rocq_array::get::<u64>(us, k_1);
      let old = rocq_array::get::<u64>(nx, a);
      let nx_ = rocq_array::set::<u64>(v8, k_1, old);
      let hd_ = rocq_array::set::<u64>(v6, a, add(k_1, 1u64));
      (hd_, nx_)
    },
  }
}

// Rocq: Allpairspath.allpairspath_implem.build_adj
// Variant: uncurried
pub fn build_adj(n: u64, m: u64, us: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let callback: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new({
    move |v9: u64, v10: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
      let us = &us;
      let tmp = adj_step(us, v9, v10);
      tmp
    }
  });
  let tmp_1 = rocq_array::make::<u64>(n, 0u64);
  let tmp_2 = rocq_array::make::<u64>(m, 0u64);
  for_loop::<(Rc<Array<u64>>, Rc<Array<u64>>)>(callback, 0u64, m, (tmp_1, tmp_2))
}

// Rocq: Allpairspath.allpairspath_implem.seed_step
// Variant: borrowed, uncurried
pub fn seed_step(seed: &Rc<Array<bool>>, a: u64, st: ((Rc<Array<bool>>, Rc<Array<u64>>), u64)) -> ((Rc<Array<bool>>, Rc<Array<u64>>), u64) {
  let a_1 = a;
  let st_1 = st;
  match &st_1 {
    (tl, p) => {
      match tl {
        (q, mark) => {
          if rocq_array::get::<bool>(seed, a_1) {
            let q_clone = Rc::clone(q);
            let tmp = rocq_array::set::<bool>(q_clone, a_1, true);
            let mark_clone = Rc::clone(mark);
            let tmp_1 = rocq_array::set::<u64>(mark_clone, Clone::clone(p), a_1);
            let tmp_2 = (tmp, tmp_1);
            let tmp_3 = 1u64;
            let p_clone = Clone::clone(p);
            std::mem::drop(st_1);
            (tmp_2, add(p_clone, tmp_3))
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Allpairspath.allpairspath_implem.chain_acc
// Variant: uncurried
pub fn chain_acc_1<S: Clone + 'static>(nx: Rc<Array<u64>>, f: Rc<dyn Fn(u64, S) -> S>, cur: u64, s: S) -> S {
  chain_acc::<S>(f, nx, cur, s, ())
}

// Rocq: Allpairspath.allpairspath_implem.chain_acc (local: chain_acc)
// Variant: uncurried, lifted
pub fn chain_acc<S: Clone + 'static>(f: Rc<dyn Fn(u64, S) -> S>, nx: Rc<Array<u64>>, cur: u64, s: S, _H: ()) -> S {
  let tmp = ltb(0u64, cur);
  match bdec(tmp) {
    sumbool::left => {
      let e = sub(cur, 1u64);
      let f_ref: &Rc<dyn Fn(u64, S) -> S> = &f;
      let s_ = f_ref(e, s);
      let c_ = rocq_array::get::<u64>(&nx, e);
      let tmp_1 = ltb(c_, cur);
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
pub fn chain_fold<S: Clone + 'static>(nx: Rc<Array<u64>>, f: Rc<dyn Fn(u64, S) -> S>, cur: u64, s: S) -> S {
  chain_acc_1::<S>(nx, f, cur, s)
}

// Rocq: Allpairspath.allpairspath_implem.bfs_visit
// Variant: borrowed, uncurried
pub fn bfs_visit(vs: &Rc<Array<u64>>, e: u64, st: ((Rc<Array<bool>>, Rc<Array<u64>>), u64)) -> ((Rc<Array<bool>>, Rc<Array<u64>>), u64) {
  let e_1 = e;
  let st_1 = st;
  match &st_1 {
    (tl, p) => {
      match tl {
        (q, mark) => {
          let b = rocq_array::get::<u64>(vs, e_1);
          if rocq_array::get::<bool>(q, b) {
            st_1
          } else {
            let q_clone = Rc::clone(q);
            let tmp = rocq_array::set::<bool>(q_clone, b, true);
            let mark_clone = Rc::clone(mark);
            let tmp_1 = rocq_array::set::<u64>(mark_clone, Clone::clone(p), b);
            let tmp_2 = (tmp, tmp_1);
            let tmp_3 = 1u64;
            let p_clone = Clone::clone(p);
            std::mem::drop(st_1);
            (tmp_2, add(p_clone, tmp_3))
          }
        },
      }
    },
  }
}

// Rocq: Allpairspath.allpairspath_implem.bfs_acc
// Variant: uncurried
pub fn bfs_acc_1(hd: Rc<Array<u64>>, nx: Rc<Array<u64>>, vs: Rc<Array<u64>>, cap: u64, h: u64, st: ((Rc<Array<bool>>, Rc<Array<u64>>), u64)) -> Rc<Array<bool>> {
  bfs_acc(hd, nx, vs, cap, h, st, ())
}

// Rocq: Allpairspath.allpairspath_implem.bfs_acc (local: bfs_acc)
// Variant: uncurried, lifted
pub fn bfs_acc(hd: Rc<Array<u64>>, nx: Rc<Array<u64>>, vs: Rc<Array<u64>>, cap: u64, h: u64, st: ((Rc<Array<bool>>, Rc<Array<u64>>), u64), _H: ()) -> Rc<Array<bool>> {
  match &st {
    (tl, p) => {
      match tl {
        (q, mark) => {
          let tmp = andb(ltb(h, Clone::clone(p)), ltb(h, cap));
          match bdec(tmp) {
            sumbool::left => {
              let x = rocq_array::get::<u64>(mark, h);
              let tmp_1 = add(h, 1u64);
              let vs_clone = Rc::clone(&vs);
              let callback: Rc<dyn Fn(u64, ((Rc<Array<bool>>, Rc<Array<u64>>), u64)) -> ((Rc<Array<bool>>, Rc<Array<u64>>), u64)> = Rc::new({
                move |v59: u64, v60: ((Rc<Array<bool>>, Rc<Array<u64>>), u64)| -> ((Rc<Array<bool>>, Rc<Array<u64>>), u64) {
                  let vs = &vs_clone;
                  let tmp_2 = bfs_visit(vs, v59, v60);
                  tmp_2
                }
              });
              let tmp_3 = rocq_array::get::<u64>(&hd, x);
              let nx_clone = Rc::clone(&nx);
              bfs_acc(hd, nx, vs, cap, tmp_1, chain_fold::<((Rc<Array<bool>>, Rc<Array<u64>>), u64)>(nx_clone, callback, tmp_3, st), ())
            },
            sumbool::right => {
              std::mem::drop(hd);
              std::mem::drop(nx);
              std::mem::drop(vs);
              let q_clone = Rc::clone(q);
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
pub fn closure(n: u64, hd: Rc<Array<u64>>, nx: Rc<Array<u64>>, vs: Rc<Array<u64>>, seed: Rc<Array<bool>>) -> Rc<Array<bool>> {
  let callback: Rc<dyn Fn(u64, ((Rc<Array<bool>>, Rc<Array<u64>>), u64)) -> ((Rc<Array<bool>>, Rc<Array<u64>>), u64)> = Rc::new({
    move |v11: u64, v12: ((Rc<Array<bool>>, Rc<Array<u64>>), u64)| -> ((Rc<Array<bool>>, Rc<Array<u64>>), u64) {
      let seed = &seed;
      let tmp = seed_step(seed, v11, v12);
      tmp
    }
  });
  let tmp_1 = rocq_array::make::<bool>(n, false);
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  let st0 = for_loop::<((Rc<Array<bool>>, Rc<Array<u64>>), u64)>(callback, 0u64, n, ((tmp_1, tmp_2), 0u64));
  bfs_acc_1(hd, nx, vs, n, 0u64, st0)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Allpairspath.allpairspath_implem.copy_step
// Variant: uncurried
pub fn copy_step(n: u64, s: u64, row: Rc<Array<bool>>, v: u64, r: Rc<Array<bool>>) -> Rc<Array<bool>> {
  let tmp = add(mul(s, n), v);
  let tmp_1 = rocq_array::get::<bool>(&row, v);
  std::mem::drop(row);
  rocq_array::set::<bool>(r, tmp, tmp_1)
}

// Rocq: Allpairspath.allpairspath_implem.reach_row
// Variant: uncurried
pub fn reach_row(n: u64, hd: Rc<Array<u64>>, nx: Rc<Array<u64>>, vs: Rc<Array<u64>>, s: u64, r: Rc<Array<bool>>) -> Rc<Array<bool>> {
  let tmp = rocq_array::make::<bool>(n, false);
  let tmp_1 = rocq_array::set::<bool>(tmp, s, true);
  let row = closure(n, hd, nx, vs, tmp_1);
  let callback: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new({
    let __anf_capture_42 = n;
    let __anf_capture_44 = s;
    move |v48: u64, v49: Rc<Array<bool>>| -> Rc<Array<bool>> {
      let tmp_2 = Clone::clone(&__anf_capture_42);
      let tmp_3 = Clone::clone(&__anf_capture_44);
      let row_clone = Rc::clone(&row);
      copy_step(tmp_2, tmp_3, row_clone, v48, v49)
    }
  });
  for_loop::<Rc<Array<bool>>>(callback, 0u64, n, r)
}

// Rocq: Allpairspath.allpairspath_implem.reach_matrix
// Variant: uncurried
pub fn reach_matrix(n: u64, hd: Rc<Array<u64>>, nx: Rc<Array<u64>>, vs: Rc<Array<u64>>) -> Rc<Array<bool>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new({
    let __anf_capture_14 = n;
    move |v22: u64, v23: Rc<Array<bool>>| -> Rc<Array<bool>> {
      let tmp = Clone::clone(&__anf_capture_14);
      let hd_clone = Rc::clone(&hd);
      let nx_clone = Rc::clone(&nx);
      let vs_clone = Rc::clone(&vs);
      reach_row(tmp, hd_clone, nx_clone, vs_clone, v22, v23)
    }
  });
  let tmp_1 = rocq_array::make::<bool>(mul(n, n), false);
  for_loop::<Rc<Array<bool>>>(callback, 0u64, n, tmp_1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb
// Variant: uncurried
pub fn ltsb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltsb(v0, v1)
}

// Rocq: Allpairspath.allpairspath_implem.bf_edge
// Variant: uncurried
pub fn bf_edge(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, keep: Rc<dyn Fn(u64) -> bool>, k: u64, h: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let keep_ref: &Rc<dyn Fn(u64) -> bool> = &keep;
  let tmp = keep_ref(k);
  if tmp {
    let a = rocq_array::get::<u64>(&us, k);
    let b = rocq_array::get::<u64>(&vs, k);
    let tmp_1 = rocq_array::get::<u64>(&h, a);
    let tmp_2 = rocq_array::get::<u64>(&ws, k);
    let nb = add(tmp_1, tmp_2);
    let tmp_3 = rocq_array::get::<u64>(&h, b);
    if ltsb(nb, tmp_3) {
      std::mem::drop(us);
      std::mem::drop(vs);
      std::mem::drop(ws);
      std::mem::drop(keep);
      rocq_array::set::<u64>(h, b, nb)
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
pub fn bf_round(m: u64, us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, keep: Rc<dyn Fn(u64) -> bool>, _r: u64, h: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
    move |v25: u64, v26: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let us_clone = Rc::clone(&us);
      let vs_clone = Rc::clone(&vs);
      let ws_clone = Rc::clone(&ws);
      let keep_clone: Rc<dyn Fn(u64) -> bool> = Rc::clone(&keep);
      bf_edge(us_clone, vs_clone, ws_clone, keep_clone, v25, v26)
    }
  });
  for_loop::<Rc<Array<u64>>>(callback, 0u64, m, h)
}

// Rocq: Allpairspath.allpairspath_implem.bf
// Variant: uncurried
pub fn bf(n: u64, m: u64, us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, keep: Rc<dyn Fn(u64) -> bool>) -> Rc<Array<u64>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
    move |v28: u64, v29: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let m_clone = Clone::clone(&m);
      let us_clone = Rc::clone(&us);
      let vs_clone = Rc::clone(&vs);
      let ws_clone = Rc::clone(&ws);
      let keep_clone: Rc<dyn Fn(u64) -> bool> = Rc::clone(&keep);
      bf_round(m_clone, us_clone, vs_clone, ws_clone, keep_clone, v28, v29)
    }
  });
  let tmp = rocq_array::make::<u64>(n, 0u64);
  for_loop::<Rc<Array<u64>>>(callback, 0u64, n, tmp)
}

// Rocq: Allpairspath.allpairspath_implem.bad_step
// Variant: uncurried
pub fn bad_step(n: u64, us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, R: Rc<Array<bool>>, h: Rc<Array<u64>>, k: u64, bad: Rc<Array<bool>>) -> Rc<Array<bool>> {
  let a = rocq_array::get::<u64>(&us, k);
  let b = rocq_array::get::<u64>(&vs, k);
  let tmp = rocq_array::get::<bool>(&R, add(mul(b, n), a));
  let tmp_1 = rocq_array::get::<u64>(&h, a);
  let tmp_2 = rocq_array::get::<u64>(&ws, k);
  let tmp_3 = add(tmp_1, tmp_2);
  let tmp_4 = rocq_array::get::<u64>(&h, b);
  let tmp_5 = ltsb(tmp_3, tmp_4);
  if andb(tmp, tmp_5) {
    std::mem::drop(us);
    std::mem::drop(ws);
    std::mem::drop(h);
    std::mem::drop(R);
    std::mem::drop(vs);
    rocq_array::set::<bool>(bad, a, true)
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
pub fn negb(b: bool) -> bool {
  if b {
    false
  } else {
    true
  }
}

// Rocq: Allpairspath.allpairspath_implem.negseed_step
// Variant: uncurried
pub fn negseed_step(n: u64, R: Rc<Array<bool>>, bad: Rc<Array<bool>>, u: u64, a: u64, s: Rc<Array<bool>>) -> Rc<Array<bool>> {
  let tmp = rocq_array::get::<bool>(&bad, a);
  let tmp_1 = rocq_array::get::<bool>(&R, add(mul(u, n), a));
  if andb(tmp, tmp_1) {
    std::mem::drop(R);
    std::mem::drop(bad);
    rocq_array::set::<bool>(s, a, true)
  } else {
    std::mem::drop(R);
    std::mem::drop(bad);
    s
  }
}

// Rocq: Allpairspath.allpairspath_implem.swap
// Variant: uncurried
pub fn swap(t: Rc<Array<u64>>, i: u64, j: u64) -> Rc<Array<u64>> {
  let a = rocq_array::get::<u64>(&t, i);
  let b = rocq_array::get::<u64>(&t, j);
  let tmp = rocq_array::set::<u64>(t, i, b);
  rocq_array::set::<u64>(tmp, j, a)
}

// Rocq: Allpairspath.allpairspath_implem.sift_down
// Variant: uncurried
pub fn sift_down_1(t: Rc<Array<u64>>, s: u64, i: u64) -> Rc<Array<u64>> {
  sift_down(t, s, i, ())
}

// Rocq: Allpairspath.allpairspath_implem.sift_down (local: sift_down)
// Variant: uncurried, lifted
pub fn sift_down(t: Rc<Array<u64>>, s: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let l = add(mul(2u64, i), 1u64);
  if ltb(l, s) {
    let r = add(l, 1u64);
    let tmp = ltb(r, s);
    let tmp_1 = rocq_array::get::<u64>(&t, r);
    let tmp_2 = rocq_array::get::<u64>(&t, l);
    let tmp_3 = ltb(tmp_1, tmp_2);
    let c = if andb(tmp, tmp_3) {
      r
    } else {
      l
    };
    let tmp_4 = andb(ltb(i, c), ltb(c, s));
    match bdec(tmp_4) {
      sumbool::left => {
        let tmp_5 = rocq_array::get::<u64>(&t, c);
        let tmp_6 = rocq_array::get::<u64>(&t, i);
        if ltb(tmp_5, tmp_6) {
          let tmp_7 = swap(t, i, c);
          sift_down(tmp_7, s, c, ())
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
pub fn hpop(t: Rc<Array<u64>>, s: u64) -> (u64, Rc<Array<u64>>) {
  let top = rocq_array::get::<u64>(&t, 0u64);
  let s_ = sub(s, 1u64);
  let last = rocq_array::get::<u64>(&t, s_);
  let tmp = rocq_array::set::<u64>(t, 0u64, last);
  let tmp_1 = sift_down_1(tmp, s_, 0u64);
  (top, tmp_1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Allpairspath.allpairspath_implem.sift_up
// Variant: uncurried
pub fn sift_up_1(t: Rc<Array<u64>>, i: u64) -> Rc<Array<u64>> {
  sift_up(t, i, ())
}

// Rocq: Allpairspath.allpairspath_implem.sift_up (local: sift_up)
// Variant: uncurried, lifted
pub fn sift_up(t: Rc<Array<u64>>, i: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(0u64, i);
  match bdec(tmp) {
    sumbool::left => {
      let p = div(sub(i, 1u64), 2u64);
      let tmp_1 = rocq_array::get::<u64>(&t, i);
      let tmp_2 = rocq_array::get::<u64>(&t, p);
      if ltb(tmp_1, tmp_2) {
        let tmp_3 = swap(t, i, p);
        sift_up(tmp_3, p, ())
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
pub fn hpush(t: Rc<Array<u64>>, s: u64, x: u64) -> Rc<Array<u64>> {
  let tmp = rocq_array::set::<u64>(t, s, x);
  sift_up_1(tmp, s)
}

// Rocq: Allpairspath.allpairspath_implem.relax
// Variant: borrowed, uncurried
pub fn relax(vs: &Rc<Array<u64>>, ws: &Rc<Array<u64>>, bad: &Rc<Array<bool>>, done: &Rc<Array<bool>>, p: &Rc<Array<u64>>, v: u64, d: u64, e: u64, st: ((Rc<Array<u64>>, Rc<Array<u64>>), u64)) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let v_1 = v;
  let d_1 = d;
  let e_1 = e;
  let st_1 = st;
  match &st_1 {
    (sz, p0) => {
      match sz {
        (hp, D) => {
          let b = rocq_array::get::<u64>(vs, e_1);
          let tmp = negb(rocq_array::get::<bool>(bad, b));
          let tmp_1 = negb(rocq_array::get::<bool>(done, b));
          if andb(tmp, tmp_1) {
            let tmp_2 = add(d_1, rocq_array::get::<u64>(ws, e_1));
            let nd = sub(add(tmp_2, rocq_array::get::<u64>(p, v_1)), rocq_array::get::<u64>(p, b));
            let tmp_3 = rocq_array::get::<u64>(hp, b);
            if ltb(nd, tmp_3) {
              let hp_clone = Rc::clone(hp);
              let tmp_4 = rocq_array::set::<u64>(hp_clone, b, nd);
              let tmp_5 = add(mul(nd, 256u64), b);
              let D_clone = Rc::clone(D);
              let tmp_6 = hpush(D_clone, Clone::clone(p0), tmp_5);
              let tmp_7 = (tmp_4, tmp_6);
              let tmp_8 = 1u64;
              let p0_clone = Clone::clone(p0);
              std::mem::drop(st_1);
              (tmp_7, add(p0_clone, tmp_8))
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
pub fn dij_body(hd: &Rc<Array<u64>>, nx: &Rc<Array<u64>>, vs: &Rc<Array<u64>>, ws: &Rc<Array<u64>>, bad: &Rc<Array<bool>>, p: &Rc<Array<u64>>, st: (((Rc<Array<u64>>, Rc<Array<bool>>), Rc<Array<u64>>), u64)) -> (((Rc<Array<u64>>, Rc<Array<bool>>), Rc<Array<u64>>), u64) {
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
                  let sz1 = sub(v11, 1u64);
                  let v = mod_(v31, 256u64);
                  let d = div(v31, 256u64);
                  let tmp_1 = rocq_array::get::<bool>(D, v);
                  if tmp_1 {
                    (((v19, v21), v33), sz1)
                  } else {
                    let done_ = rocq_array::set::<bool>(v21, v, true);
                    let D_ = rocq_array::set::<u64>(v19, v, d);
                    let tmp_2 = bad;
                    if rocq_array::get::<bool>(tmp_2, v) {
                      (((D_, done_), v33), sz1)
                    } else {
                      let vs_clone = Rc::clone(vs);
                      let ws_clone = Rc::clone(ws);
                      let bad_clone = Rc::clone(bad);
                      let done__clone = Rc::clone(&done_);
                      let p_clone = Rc::clone(p);
                      let callback: Rc<dyn Fn(u64, ((Rc<Array<u64>>, Rc<Array<u64>>), u64)) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64)> = Rc::new({
                        let __anf_capture_156 = v;
                        let __anf_capture_158 = d;
                        move |v160: u64, v161: ((Rc<Array<u64>>, Rc<Array<u64>>), u64)| -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
                          let vs = &vs_clone;
                          let ws = &ws_clone;
                          let bad = &bad_clone;
                          let done_ = &done__clone;
                          let p = &p_clone;
                          let tmp_3 = relax(vs, ws, bad, done_, p, Clone::clone(&__anf_capture_156), Clone::clone(&__anf_capture_158), v160, v161);
                          tmp_3
                        }
                      });
                      let tmp_4 = rocq_array::get::<u64>(hd, v);
                      let tmp_5 = ((D_, v33), sz1);
                      let nx_clone = Rc::clone(nx);
                      let tmp_6 = chain_fold::<((Rc<Array<u64>>, Rc<Array<u64>>), u64)>(nx_clone, callback, tmp_4, tmp_5);
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
pub fn dij_acc_1(hd: &Rc<Array<u64>>, nx: &Rc<Array<u64>>, vs: &Rc<Array<u64>>, ws: &Rc<Array<u64>>, bad: &Rc<Array<bool>>, p: &Rc<Array<u64>>, lim: u64, steps: u64, st: (((Rc<Array<u64>>, Rc<Array<bool>>), Rc<Array<u64>>), u64)) -> Rc<Array<u64>> {
  let lim_1 = lim;
  let steps_1 = steps;
  let st_1 = st;
  dij_acc(hd, nx, vs, ws, bad, p, lim_1, steps_1, st_1, ())
}

// Rocq: Allpairspath.allpairspath_implem.dij_acc (local: dij_acc)
// Variant: borrowed, uncurried, lifted
pub fn dij_acc(hd: &Rc<Array<u64>>, nx: &Rc<Array<u64>>, vs: &Rc<Array<u64>>, ws: &Rc<Array<u64>>, bad: &Rc<Array<bool>>, p: &Rc<Array<u64>>, lim: u64, steps: u64, st: (((Rc<Array<u64>>, Rc<Array<bool>>), Rc<Array<u64>>), u64), _H: ()) -> Rc<Array<u64>> {
  let lim_1 = lim;
  let steps_1 = steps;
  let st_1 = st;
  match &st_1 {
    (sz, p0) => {
      match sz {
        (hp, _p1) => {
          match hp {
            (done, _D) => {
              let tmp = andb(ltb(0u64, Clone::clone(p0)), ltb(steps_1, lim_1));
              match bdec(tmp) {
                sumbool::left => {
                  let tmp_1 = add(steps_1, 1u64);
                  let tmp_2 = hd;
                  let tmp_3 = nx;
                  let tmp_4 = vs;
                  let tmp_5 = ws;
                  let tmp_6 = bad;
                  let tmp_7 = p;
                  dij_acc(hd, nx, vs, ws, bad, p, lim_1, tmp_1, dij_body(tmp_2, tmp_3, tmp_4, tmp_5, tmp_6, tmp_7, st_1), ())
                },
                sumbool::right => {
                  let done_clone = Rc::clone(done);
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
pub fn dijkstra(n: u64, m: u64, hd: &Rc<Array<u64>>, nx: &Rc<Array<u64>>, vs: &Rc<Array<u64>>, ws: &Rc<Array<u64>>, bad: &Rc<Array<bool>>, p: &Rc<Array<u64>>, u: u64) -> Rc<Array<u64>> {
  let n_1 = n;
  let m_1 = m;
  let u_1 = u;
  let tmp = rocq_array::make::<u64>(n_1, __rocq_global_833);
  let D0 = rocq_array::set::<u64>(tmp, u_1, 0u64);
  let tmp_1 = rocq_array::make::<u64>(add(m_1, 1u64), 0u64);
  let hp0 = rocq_array::set::<u64>(tmp_1, 0u64, u_1);
  let tmp_2 = add(m_1, 1u64);
  let tmp_3 = rocq_array::make::<bool>(n_1, false);
  dij_acc_1(hd, nx, vs, ws, bad, p, tmp_2, 0u64, (((D0, tmp_3), hp0), 1u64))
}

// Rocq: Allpairspath.allpairspath_implem.cell
// Variant: borrowed, uncurried
pub fn cell(n: u64, R: &Rc<Array<bool>>, neg: &Rc<Array<bool>>, D: &Rc<Array<u64>>, p: &Rc<Array<u64>>, u: u64, v: u64) -> Rc<answer<u64>> {
  let n_1 = n;
  let u_1 = u;
  let v_1 = v;
  if rocq_array::get::<bool>(neg, v_1) {
    Rc::new(answer::<u64>::NegInfinity)
  } else {
    let tmp = add(mul(u_1, n_1), v_1);
    if rocq_array::get::<bool>(R, tmp) {
      Rc::new(answer::<u64>::Distance(add(sub(rocq_array::get::<u64>(D, v_1), rocq_array::get::<u64>(p, u_1)), rocq_array::get::<u64>(p, v_1))))
    } else {
      Rc::new(answer::<u64>::Impossible)
    }
  }
}

// Rocq: Allpairspath.allpairspath_implem.row_of
// Variant: borrowed, uncurried
pub fn row_of(n: u64, m: u64, hd: &Rc<Array<u64>>, nx: &Rc<Array<u64>>, vs: &Rc<Array<u64>>, ws: &Rc<Array<u64>>, R: &Rc<Array<bool>>, bad: &Rc<Array<bool>>, p: &Rc<Array<u64>>, u: u64) -> Rc<Array<Rc<answer<u64>>>> {
  let m_1 = m;
  let R_clone = Rc::clone(R);
  let bad_clone = Rc::clone(bad);
  let callback: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new({
    let __anf_capture_25 = n;
    let __anf_capture_31 = u;
    move |v33: u64, v34: Rc<Array<bool>>| -> Rc<Array<bool>> {
      let tmp = Clone::clone(&__anf_capture_25);
      let tmp_1 = Rc::clone(&R_clone);
      let tmp_2 = Rc::clone(&bad_clone);
      let tmp_3 = Clone::clone(&__anf_capture_31);
      negseed_step(tmp, tmp_1, tmp_2, tmp_3, v33, v34)
    }
  });
  let tmp_4 = rocq_array::make::<bool>(n, false);
  let seed = for_loop::<Rc<Array<bool>>>(callback, 0u64, n, tmp_4);
  let hd_clone = Rc::clone(hd);
  let nx_clone = Rc::clone(nx);
  let vs_clone = Rc::clone(vs);
  let neg = closure(n, hd_clone, nx_clone, vs_clone, seed);
  let D = dijkstra(n, m_1, hd, nx, vs, ws, bad, p, u);
  let R_clone_1 = Rc::clone(R);
  let p_clone = Rc::clone(p);
  let callback_1: Rc<dyn Fn(u64, Rc<Array<Rc<answer<u64>>>>) -> Rc<Array<Rc<answer<u64>>>>> = Rc::new({
    let __anf_capture_122 = n;
    let __anf_capture_132 = u;
    move |v: u64, r: Rc<Array<Rc<answer<u64>>>>| -> Rc<Array<Rc<answer<u64>>>> {
      let tmp_5 = cell(Clone::clone(&__anf_capture_122), &R_clone_1, &neg, &D, &p_clone, Clone::clone(&__anf_capture_132), v);
      rocq_array::set::<Rc<answer<u64>>>(r, v, tmp_5)
    }
  });
  let tmp_6 = rocq_array::make::<Rc<answer<u64>>>(n, Rc::new(answer::<u64>::Impossible));
  for_loop::<Rc<Array<Rc<answer<u64>>>>>(callback_1, 0u64, n, tmp_6)
}

// Rocq: Allpairspath.allpairspath_implem.apsp_rows
// Variant: uncurried
pub fn apsp_rows(n: u64, m: u64, hd: Rc<Array<u64>>, nx: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, R: Rc<Array<bool>>, bad: Rc<Array<bool>>, p: Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<Array<Rc<answer<u64>>>>>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>>> = Rc::new({
    let __anf_capture_29 = n;
    move |u: u64, res: Rc<Array<Rc<Array<Rc<answer<u64>>>>>>| -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>> {
      let tmp = row_of(Clone::clone(&__anf_capture_29), Clone::clone(&m), &hd, &nx, &vs, &ws, &R, &bad, &p, u);
      rocq_array::set::<Rc<Array<Rc<answer<u64>>>>>(res, u, tmp)
    }
  });
  let tmp_1 = rocq_array::make::<Rc<answer<u64>>>(0u64, Rc::new(answer::<u64>::Impossible));
  let tmp_2 = rocq_array::make::<Rc<Array<Rc<answer<u64>>>>>(n, tmp_1);
  for_loop::<Rc<Array<Rc<Array<Rc<answer<u64>>>>>>>(callback, 0u64, n, tmp_2)
}

// Rocq: Allpairspath.allpairspath_implem.apsp_core
// Variant: uncurried
pub fn apsp_core(n: u64, m: u64, us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, hd: Rc<Array<u64>>, nx: Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>> {
  let hd_clone = Rc::clone(&hd);
  let nx_clone = Rc::clone(&nx);
  let vs_clone = Rc::clone(&vs);
  let R = reach_matrix(n, hd_clone, nx_clone, vs_clone);
  let vs_clone_1 = Rc::clone(&vs);
  let us_clone = Rc::clone(&us);
  let R_clone = Rc::clone(&R);
  let callback: Rc<dyn Fn(u64) -> bool> = Rc::new({
    let __anf_capture_35 = n;
    move |k: u64| -> bool {
      let vs = &vs_clone_1;
      let n = &__anf_capture_35;
      let us = &us_clone;
      let R = &R_clone;
      let tmp = add(mul(rocq_array::get::<u64>(vs, k), Clone::clone(n)), rocq_array::get::<u64>(us, k));
      rocq_array::get::<bool>(R, tmp)
    }
  });
  let us_clone_1 = Rc::clone(&us);
  let vs_clone_2 = Rc::clone(&vs);
  let ws_clone = Rc::clone(&ws);
  let h1 = bf(n, m, us_clone_1, vs_clone_2, ws_clone, callback);
  let us_clone_2 = Rc::clone(&us);
  let vs_clone_3 = Rc::clone(&vs);
  let ws_clone_1 = Rc::clone(&ws);
  let R_clone_1 = Rc::clone(&R);
  let callback_1: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new({
    let __anf_capture_101 = n;
    move |v113: u64, v114: Rc<Array<bool>>| -> Rc<Array<bool>> {
      let tmp_1 = Clone::clone(&__anf_capture_101);
      let tmp_2 = Rc::clone(&us_clone_2);
      let tmp_3 = Rc::clone(&vs_clone_3);
      let tmp_4 = Rc::clone(&ws_clone_1);
      let tmp_5 = Rc::clone(&R_clone_1);
      let h1_clone = Rc::clone(&h1);
      bad_step(tmp_1, tmp_2, tmp_3, tmp_4, tmp_5, h1_clone, v113, v114)
    }
  });
  let tmp_6 = rocq_array::make::<bool>(n, false);
  let bad = for_loop::<Rc<Array<bool>>>(callback_1, 0u64, m, tmp_6);
  let us_clone_3 = Rc::clone(&us);
  let vs_clone_4 = Rc::clone(&vs);
  let bad_clone = Rc::clone(&bad);
  let callback_2: Rc<dyn Fn(u64) -> bool> = Rc::new({
    move |k: u64| -> bool {
      let us = &us_clone_3;
      let vs = &vs_clone_4;
      let tmp_7 = negb(rocq_array::get::<bool>(&bad_clone, rocq_array::get::<u64>(us, k)));
      let tmp_8 = rocq_array::get::<bool>(&bad_clone, rocq_array::get::<u64>(vs, k));
      andb(tmp_7, negb(tmp_8))
    }
  });
  let vs_clone_5 = Rc::clone(&vs);
  let ws_clone_2 = Rc::clone(&ws);
  let p = bf(n, m, us, vs_clone_5, ws_clone_2, callback_2);
  apsp_rows(n, m, hd, nx, vs, ws, R, bad, p)
}

// Rocq: Allpairspath.allpairspath_implem.allpairspath_impl
// Variant: uncurried
pub fn allpairspath_impl(n: u64, us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>> {
  let m = rocq_array::length::<u64>(&us);
  let us_clone = Rc::clone(&us);
  let tmp = build_adj(n, m, us_clone);
  match tmp {
    (v16, v18) => {
      apsp_core(n, m, us, vs, ws, v16, v18)
    },
  }
}

mod __rocq_reuse {
//! Empty allocation ownership for OwnedANF reset and exact-type rebuilding.
use std::mem::MaybeUninit;
use std::rc::Rc;

/// Move-only and opaque: storage has no initialized `T` and cannot be inspected.
pub struct Token<T> {
    _storage: Option<Rc<MaybeUninit<T>>>,
}

/// Consume an owner. The caller supplies the IR-approved shallow field copy;
/// This may use a compiler-generated structural Clone implementation, but does
/// not authorize arbitrary host clone behavior merely because T implements Clone.
#[inline]
pub fn reset<T>(mut owner: Rc<T>, duplicate: impl FnOnce(&T) -> T) -> (T, Token<T>) {
    if let Some(payload) = Rc::get_mut(&mut owner) {
        // SAFETY: get_mut establishes exclusive access (including no Weak
        // owners). T and MaybeUninit<T> have identical size/alignment, so their
        // Rc allocation layouts agree. After read, no potentially panicking
        // user code runs before ownership becomes Rc<MaybeUninit<T>>. There is
        // exactly one from_raw for into_raw, and the original Rc<T> is consumed.
        // The token never reads or drops the moved T; dropping it only frees
        // the allocation. The payload returned here owns T's fields once.
        unsafe {
            let value = std::ptr::read(payload);
            let raw = Rc::into_raw(owner).cast::<MaybeUninit<T>>();
            let storage = Rc::from_raw(raw);
            (value, Token { _storage: Some(storage) })
        }
    } else {
        let value = duplicate(&owner);
        drop(owner);
        (value, Token { _storage: None })
    }
}

/// Consume reserved storage and a fully evaluated payload. Empty tokens allocate.
#[inline]
pub fn rebuild<T>(token: Token<T>, payload: T) -> Rc<T> {
    match token._storage {
        None => Rc::new(payload),
        Some(mut storage) => {
            // The opaque, non-Clone token owns the only strong reference and
            // has no weak references. Check before initializing, so a panic
            // cannot leave an initialized T hidden inside MaybeUninit<T>.
            Rc::get_mut(&mut storage).expect("exclusive reuse token").write(payload);
            // SAFETY: the payload is now fully initialized; no panicking code
            // lies between initialization and this ownership conversion. The
            // reset conversion established identical allocation layouts.
            unsafe { Rc::from_raw(Rc::into_raw(storage).cast::<T>()) }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    struct Probe(Rc<Cell<usize>>);
    impl Drop for Probe {
        fn drop(&mut self) { self.0.set(self.0.get() + 1); }
    }

    #[test]
    fn rebuilding_preserves_address_and_drops_only_new_payload() {
        let drops = Rc::new(Cell::new(0));
        let owner = Rc::new(Probe(drops.clone()));
        let address = Rc::as_ptr(&owner);
        let (old, token) = reset(owner, |_| panic!("unique"));
        drop(old);
        assert_eq!(drops.get(), 1);
        let new = rebuild(token, Probe(drops.clone()));
        assert_eq!(Rc::as_ptr(&new), address);
        assert_eq!(drops.get(), 1);
        drop(new);
        assert_eq!(drops.get(), 2);
    }

    #[test]
    fn empty_token_allocates_and_preserves_old_alias() {
        let old = Rc::new(7);
        let alias = old.clone();
        let (_, token) = reset(old, |x| *x);
        let new = rebuild(token, 19);
        assert_eq!(*alias, 7);
        assert_eq!(*new, 19);
        assert!(!Rc::ptr_eq(&alias, &new));
    }

    #[test]
    fn unique_token_drop_does_not_drop_payload() {
        let drops = Rc::new(Cell::new(0));
        let owner = Rc::new(Probe(drops.clone()));
        let address = Rc::as_ptr(&owner).cast::<MaybeUninit<Probe>>();
        let (payload, token) = reset(owner, |_| panic!("unique path duplicated"));
        assert_eq!(Rc::as_ptr(token._storage.as_ref().unwrap()), address);
        drop(token);
        assert_eq!(drops.get(), 0);
        drop(payload);
        assert_eq!(drops.get(), 1);
    }

    #[test]
    fn shared_fallback_preserves_aliases() {
        let field = Rc::new(7);
        let owner = Rc::new((field.clone(), 9));
        let alias = owner.clone();
        let (payload, token) = reset(owner, |x| (x.0.clone(), x.1));
        assert!(token._storage.is_none());
        assert!(Rc::ptr_eq(&payload.0, &alias.0));
        assert_eq!(Rc::strong_count(&field), 3);
        drop(token);
        drop(payload);
        assert_eq!(alias.1, 9);
        drop(alias);
        assert_eq!(Rc::strong_count(&field), 1);
    }

    #[test]
    fn weak_pointer_forces_fallback() {
        let owner = Rc::new(17);
        let weak = Rc::downgrade(&owner);
        let (payload, token) = reset(owner, |x| *x);
        assert_eq!(payload, 17);
        assert!(token._storage.is_none());
        assert!(weak.upgrade().is_none());
    }

    #[test]
    fn panicking_fallback_releases_consumed_handle() {
        let owner = Rc::new(17);
        let alias = owner.clone();
        let result = std::panic::catch_unwind(|| reset(owner, |_| panic!("copy failed")));
        assert!(result.is_err());
        assert_eq!(Rc::strong_count(&alias), 1);
        assert_eq!(*alias, 17);
    }

    #[test]
    fn zero_sized_payload() {
        let (payload, token) = reset(Rc::new(()), |_| panic!("unique"));
        drop(token);
        assert_eq!(payload, ());
    }
}

}
const __rocq_global_833: u64 = 1073741824u64;