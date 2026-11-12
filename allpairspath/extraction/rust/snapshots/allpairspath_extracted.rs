// Generated from OwnedANF. This printer is not verified.
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

// Rocq: Allpairspath.allpairspath_implem.allpairspath
// Variant: uncurried
pub fn allpairspath() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>>> {
  let v0: fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>> = allpairspath_impl;
  let v1: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>>> = Rc::new(v0);
  v1
}

// Rocq: Allpairspath.allpairspath_implem.allpairspath
pub fn allpairspath_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>>>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>>>>> = allpairspath_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>>>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Allpairspath.allpairspath_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  match b {
    true => {
      sumbool::left
    },
    false => {
      sumbool::right
    },
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
  let v12 = ltb(i, hi);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v24: &Rc<dyn Fn(u64, S) -> S> = &f;
      let v29 = v24(i, s);
      for_acc::<S>(f, hi, v23, v29, ())
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
      let v11 = us;
      let a = rocq_array::get::<u64>(&v11, k_1);
      let old = rocq_array::get::<u64>(&nx, a);
      let nx_ = rocq_array::set::<u64>(v8, k_1, old);
      let hd_ = rocq_array::set::<u64>(v6, a, add(k_1, 1u64));
      (hd_, nx_)
    },
  }
}

// Rocq: Allpairspath.allpairspath_implem.build_adj
// Variant: uncurried
pub fn build_adj(n: u64, m: u64, us: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v6 = {
    move |v9: u64, v10: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
      let us = &us;
      let v17 = adj_step(us, v9, v10);
      v17
    }
  };
  let v20: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new(v6);
  let v30 = rocq_array::make::<u64>(n, 0u64);
  let v37 = rocq_array::make::<u64>(m, 0u64);
  for_loop::<(Rc<Array<u64>>, Rc<Array<u64>>)>(v20, 0u64, m, (v30, v37))
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
          let v16 = seed;
          match rocq_array::get::<bool>(&v16, a_1) {
            true => {
              let v24 = Rc::clone(q);
              let v29 = rocq_array::set::<bool>(v24, a_1, true);
              let v31 = Rc::clone(mark);
              let v36 = rocq_array::set::<u64>(v31, Clone::clone(p), a_1);
              let v42 = (v29, v36);
              let v45 = 1u64;
              let v46 = Clone::clone(p);
              std::mem::drop(st_1);
              (v42, add(v46, v45))
            },
            false => {
              st_1
            },
          }
        },
      }
    },
  }
}

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  match b1 {
    true => {
      b2
    },
    false => {
      false
    },
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
  let v14 = ltb(0u64, cur);
  match bdec(v14) {
    sumbool::left => {
      let e = sub(cur, 1u64);
      let v26: &Rc<dyn Fn(u64, S) -> S> = &f;
      let s_ = v26(e, s);
      let v32 = &nx;
      let c_ = rocq_array::get::<u64>(&v32, e);
      let v43 = ltb(c_, cur);
      match bdec(v43) {
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
          let v16 = vs;
          let b = rocq_array::get::<u64>(&v16, e_1);
          match rocq_array::get::<bool>(&q, b) {
            true => {
              st_1
            },
            false => {
              let v29 = Rc::clone(q);
              let v34 = rocq_array::set::<bool>(v29, b, true);
              let v36 = Rc::clone(mark);
              let v41 = rocq_array::set::<u64>(v36, Clone::clone(p), b);
              let v47 = (v34, v41);
              let v50 = 1u64;
              let v51 = Clone::clone(p);
              std::mem::drop(st_1);
              (v47, add(v51, v50))
            },
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
          let v37 = andb(ltb(h, Clone::clone(p)), ltb(h, cap));
          match bdec(v37) {
            sumbool::left => {
              let x = rocq_array::get::<u64>(&mark, h);
              let v51 = add(h, 1u64);
              let v55 = Rc::clone(&vs);
              let v56 = {
                move |v59: u64, v60: ((Rc<Array<bool>>, Rc<Array<u64>>), u64)| -> ((Rc<Array<bool>>, Rc<Array<u64>>), u64) {
                  let vs = &v55;
                  let v67 = bfs_visit(vs, v59, v60);
                  v67
                }
              };
              let v70: Rc<dyn Fn(u64, ((Rc<Array<bool>>, Rc<Array<u64>>), u64)) -> ((Rc<Array<bool>>, Rc<Array<u64>>), u64)> = Rc::new(v56);
              let v72 = &hd;
              let v75 = rocq_array::get::<u64>(&v72, x);
              let v78 = Rc::clone(&nx);
              bfs_acc(hd, nx, vs, cap, v51, chain_fold::<((Rc<Array<bool>>, Rc<Array<u64>>), u64)>(v78, v70, v75, st), ())
            },
            sumbool::right => {
              std::mem::drop(hd);
              std::mem::drop(nx);
              std::mem::drop(vs);
              let v106 = Rc::clone(q);
              std::mem::drop(st);
              v106
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
  let v8 = {
    move |v11: u64, v12: ((Rc<Array<bool>>, Rc<Array<u64>>), u64)| -> ((Rc<Array<bool>>, Rc<Array<u64>>), u64) {
      let seed = &seed;
      let v19 = seed_step(seed, v11, v12);
      v19
    }
  };
  let v22: Rc<dyn Fn(u64, ((Rc<Array<bool>>, Rc<Array<u64>>), u64)) -> ((Rc<Array<bool>>, Rc<Array<u64>>), u64)> = Rc::new(v8);
  let v32 = rocq_array::make::<bool>(n, false);
  let v39 = rocq_array::make::<u64>(n, 0u64);
  let st0 = for_loop::<((Rc<Array<bool>>, Rc<Array<u64>>), u64)>(v22, 0u64, n, ((v32, v39), 0u64));
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
  let v16 = add(mul(s, n), v);
  let v17 = &row;
  let v20 = rocq_array::get::<bool>(&v17, v);
  std::mem::drop(row);
  rocq_array::set::<bool>(r, v16, v20)
}

// Rocq: Allpairspath.allpairspath_implem.reach_row
// Variant: uncurried
pub fn reach_row(n: u64, hd: Rc<Array<u64>>, nx: Rc<Array<u64>>, vs: Rc<Array<u64>>, s: u64, r: Rc<Array<bool>>) -> Rc<Array<bool>> {
  let v13 = rocq_array::make::<bool>(n, false);
  let v22 = rocq_array::set::<bool>(v13, s, true);
  let row = closure(n, hd, nx, vs, v22);
  let v41 = {
    let __anf_capture_42 = n;
    let __anf_capture_44 = s;
    move |v48: u64, v49: Rc<Array<bool>>| -> Rc<Array<bool>> {
      let v52 = Clone::clone(&__anf_capture_42);
      let v54 = Clone::clone(&__anf_capture_44);
      let v56 = Rc::clone(&row);
      copy_step(v52, v54, v56, v48, v49)
    }
  };
  let v64: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new(v41);
  for_loop::<Rc<Array<bool>>>(v64, 0u64, n, r)
}

// Rocq: Allpairspath.allpairspath_implem.reach_matrix
// Variant: uncurried
pub fn reach_matrix(n: u64, hd: Rc<Array<u64>>, nx: Rc<Array<u64>>, vs: Rc<Array<u64>>) -> Rc<Array<bool>> {
  let v13 = {
    let __anf_capture_14 = n;
    move |v22: u64, v23: Rc<Array<bool>>| -> Rc<Array<bool>> {
      let v26 = Clone::clone(&__anf_capture_14);
      let v28 = Rc::clone(&hd);
      let v30 = Rc::clone(&nx);
      let v32 = Rc::clone(&vs);
      reach_row(v26, v28, v30, v32, v22, v23)
    }
  };
  let v40: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new(v13);
  let v56 = rocq_array::make::<bool>(mul(n, n), false);
  for_loop::<Rc<Array<bool>>>(v40, 0u64, n, v56)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb
// Variant: uncurried
pub fn ltsb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltsb(v0, v1)
}

// Rocq: Allpairspath.allpairspath_implem.bf_edge
// Variant: uncurried
pub fn bf_edge(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, keep: Rc<dyn Fn(u64) -> bool>, k: u64, h: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v6: &Rc<dyn Fn(u64) -> bool> = &keep;
  let v9 = v6(k);
  match v9 {
    true => {
      let v11 = &us;
      let a = rocq_array::get::<u64>(&v11, k);
      let v15 = &vs;
      let b = rocq_array::get::<u64>(&v15, k);
      let v20 = &h;
      let v23 = rocq_array::get::<u64>(&v20, a);
      let v24 = &ws;
      let v27 = rocq_array::get::<u64>(&v24, k);
      let nb = add(v23, v27);
      let v34 = &h;
      let v37 = rocq_array::get::<u64>(&v34, b);
      match ltsb(nb, v37) {
        true => {
          std::mem::drop(us);
          std::mem::drop(vs);
          std::mem::drop(ws);
          std::mem::drop(keep);
          rocq_array::set::<u64>(h, b, nb)
        },
        false => {
          std::mem::drop(us);
          std::mem::drop(vs);
          std::mem::drop(ws);
          std::mem::drop(keep);
          h
        },
      }
    },
    false => {
      std::mem::drop(us);
      std::mem::drop(vs);
      std::mem::drop(ws);
      std::mem::drop(keep);
      h
    },
  }
}

// Rocq: Allpairspath.allpairspath_implem.bf_round
// Variant: uncurried
pub fn bf_round(m: u64, us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, keep: Rc<dyn Fn(u64) -> bool>, _r: u64, h: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v16 = {
    move |v25: u64, v26: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let v29 = Rc::clone(&us);
      let v31 = Rc::clone(&vs);
      let v33 = Rc::clone(&ws);
      let v34: Rc<dyn Fn(u64) -> bool> = Rc::clone(&keep);
      bf_edge(v29, v31, v33, v34, v25, v26)
    }
  };
  let v43: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v16);
  for_loop::<Rc<Array<u64>>>(v43, 0u64, m, h)
}

// Rocq: Allpairspath.allpairspath_implem.bf
// Variant: uncurried
pub fn bf(n: u64, m: u64, us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, keep: Rc<dyn Fn(u64) -> bool>) -> Rc<Array<u64>> {
  let v17 = {
    move |v28: u64, v29: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let v32 = Clone::clone(&m);
      let v34 = Rc::clone(&us);
      let v36 = Rc::clone(&vs);
      let v38 = Rc::clone(&ws);
      let v39: Rc<dyn Fn(u64) -> bool> = Rc::clone(&keep);
      bf_round(v32, v34, v36, v38, v39, v28, v29)
    }
  };
  let v48: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v17);
  let v58 = rocq_array::make::<u64>(n, 0u64);
  for_loop::<Rc<Array<u64>>>(v48, 0u64, n, v58)
}

// Rocq: Allpairspath.allpairspath_implem.bad_step
// Variant: uncurried
pub fn bad_step(n: u64, us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, R: Rc<Array<bool>>, h: Rc<Array<u64>>, k: u64, bad: Rc<Array<bool>>) -> Rc<Array<bool>> {
  let v8 = &us;
  let a = rocq_array::get::<u64>(&v8, k);
  let v12 = &vs;
  let b = rocq_array::get::<u64>(&v12, k);
  let v28 = add(mul(b, n), a);
  let v29 = &R;
  let v32 = rocq_array::get::<bool>(&v29, v28);
  let v35 = &h;
  let v38 = rocq_array::get::<u64>(&v35, a);
  let v39 = &ws;
  let v42 = rocq_array::get::<u64>(&v39, k);
  let v47 = add(v38, v42);
  let v48 = &h;
  let v51 = rocq_array::get::<u64>(&v48, b);
  let v56 = ltsb(v47, v51);
  match andb(v32, v56) {
    true => {
      std::mem::drop(us);
      std::mem::drop(ws);
      std::mem::drop(h);
      std::mem::drop(R);
      std::mem::drop(vs);
      rocq_array::set::<bool>(bad, a, true)
    },
    false => {
      std::mem::drop(us);
      std::mem::drop(ws);
      std::mem::drop(h);
      std::mem::drop(R);
      std::mem::drop(vs);
      bad
    },
  }
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  match b {
    true => {
      false
    },
    false => {
      true
    },
  }
}

// Rocq: Allpairspath.allpairspath_implem.negseed_step
// Variant: uncurried
pub fn negseed_step(n: u64, R: Rc<Array<bool>>, bad: Rc<Array<bool>>, u: u64, a: u64, s: Rc<Array<bool>>) -> Rc<Array<bool>> {
  let v7 = &bad;
  let v10 = rocq_array::get::<bool>(&v7, a);
  let v22 = add(mul(u, n), a);
  let v23 = &R;
  let v26 = rocq_array::get::<bool>(&v23, v22);
  match andb(v10, v26) {
    true => {
      std::mem::drop(R);
      std::mem::drop(bad);
      rocq_array::set::<bool>(s, a, true)
    },
    false => {
      std::mem::drop(R);
      std::mem::drop(bad);
      s
    },
  }
}

// Rocq: Allpairspath.allpairspath_implem.swap
// Variant: uncurried
pub fn swap(t: Rc<Array<u64>>, i: u64, j: u64) -> Rc<Array<u64>> {
  let v3 = &t;
  let a = rocq_array::get::<u64>(&v3, i);
  let v7 = &t;
  let b = rocq_array::get::<u64>(&v7, j);
  let v18 = rocq_array::set::<u64>(t, i, b);
  rocq_array::set::<u64>(v18, j, a)
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
  match ltb(l, s) {
    true => {
      let r = add(l, 1u64);
      let v41 = ltb(r, s);
      let v43 = &t;
      let v46 = rocq_array::get::<u64>(&v43, r);
      let v47 = &t;
      let v50 = rocq_array::get::<u64>(&v47, l);
      let v55 = ltb(v46, v50);
      let c = match andb(v41, v55) {
        true => {
          r
        },
        false => {
          l
        },
      };
      let v86 = andb(ltb(i, c), ltb(c, s));
      match bdec(v86) {
        sumbool::left => {
          let v91 = &t;
          let v94 = rocq_array::get::<u64>(&v91, c);
          let v95 = &t;
          let v98 = rocq_array::get::<u64>(&v95, i);
          match ltb(v94, v98) {
            true => {
              let v112 = swap(t, i, c);
              sift_down(v112, s, c, ())
            },
            false => {
              t
            },
          }
        },
        sumbool::right => {
          t
        },
      }
    },
    false => {
      t
    },
  }
}

// Rocq: Allpairspath.allpairspath_implem.hpop
// Variant: uncurried
pub fn hpop(t: Rc<Array<u64>>, s: u64) -> (u64, Rc<Array<u64>>) {
  let v3 = 0u64;
  let v4 = &t;
  let top = rocq_array::get::<u64>(&v4, v3);
  let s_ = sub(s, 1u64);
  let v16 = &t;
  let last = rocq_array::get::<u64>(&v16, s_);
  let v29 = rocq_array::set::<u64>(t, 0u64, last);
  let v38 = sift_down_1(v29, s_, 0u64);
  (top, v38)
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
  let v12 = ltb(0u64, i);
  match bdec(v12) {
    sumbool::left => {
      let p = div(sub(i, 1u64), 2u64);
      let v33 = &t;
      let v36 = rocq_array::get::<u64>(&v33, i);
      let v37 = &t;
      let v40 = rocq_array::get::<u64>(&v37, p);
      match ltb(v36, v40) {
        true => {
          let v54 = swap(t, i, p);
          sift_up(v54, p, ())
        },
        false => {
          t
        },
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
  let v11 = rocq_array::set::<u64>(t, s, x);
  sift_up_1(v11, s)
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
          let v24 = vs;
          let b = rocq_array::get::<u64>(&v24, e_1);
          let v30 = bad;
          let v36 = negb(rocq_array::get::<bool>(&v30, b));
          let v38 = done;
          let v44 = negb(rocq_array::get::<bool>(&v38, b));
          match andb(v36, v44) {
            true => {
              let v54 = ws;
              let v62 = add(d_1, rocq_array::get::<u64>(&v54, e_1));
              let v63 = p;
              let v71 = add(v62, rocq_array::get::<u64>(&v63, v_1));
              let v72 = p;
              let nd = sub(v71, rocq_array::get::<u64>(&v72, b));
              let v84 = rocq_array::get::<u64>(&hp, b);
              match ltb(nd, v84) {
                true => {
                  let v92 = Rc::clone(hp);
                  let v97 = rocq_array::set::<u64>(v92, b, nd);
                  let v112 = add(mul(nd, 256u64), b);
                  let v114 = Rc::clone(D);
                  let v119 = hpush(v114, Clone::clone(p0), v112);
                  let v125 = (v97, v119);
                  let v128 = 1u64;
                  let v129 = Clone::clone(p0);
                  std::mem::drop(st_1);
                  (v125, add(v129, v128))
                },
                false => {
                  st_1
                },
              }
            },
            false => {
              st_1
            },
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
              let v29 = hpop(v16, v11);
              match v29 {
                (v31, v33) => {
                  let sz1 = sub(v11, 1u64);
                  let v = mod_(v31, 256u64);
                  let d = div(v31, 256u64);
                  let v61 = rocq_array::get::<bool>(&D, v);
                  match v61 {
                    true => {
                      (((v19, v21), v33), sz1)
                    },
                    false => {
                      let done_ = rocq_array::set::<bool>(v21, v, true);
                      let D_ = rocq_array::set::<u64>(v19, v, d);
                      let v99 = bad;
                      let v102 = rocq_array::get::<bool>(&v99, v);
                      match &v102 {
                        true => {
                          (((D_, done_), v33), sz1)
                        },
                        false => {
                          let v128 = Rc::clone(vs);
                          let v131 = Rc::clone(ws);
                          let v134 = Rc::clone(bad);
                          let v137 = Rc::clone(&done_);
                          let v140 = Rc::clone(p);
                          let v145 = {
                            let __anf_capture_156 = v;
                            let __anf_capture_158 = d;
                            move |v160: u64, v161: ((Rc<Array<u64>>, Rc<Array<u64>>), u64)| -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
                              let vs = &v128;
                              let ws = &v131;
                              let bad = &v134;
                              let done_ = &v137;
                              let p = &v140;
                              let v176 = relax(vs, ws, bad, done_, p, Clone::clone(&__anf_capture_156), Clone::clone(&__anf_capture_158), v160, v161);
                              v176
                            }
                          };
                          let v179: Rc<dyn Fn(u64, ((Rc<Array<u64>>, Rc<Array<u64>>), u64)) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64)> = Rc::new(v145);
                          let v181 = hd;
                          let v184 = rocq_array::get::<u64>(&v181, v);
                          let v195 = ((D_, v33), sz1);
                          let v199 = Rc::clone(nx);
                          let v206 = chain_fold::<((Rc<Array<u64>>, Rc<Array<u64>>), u64)>(v199, v179, v184, v195);
                          match v206 {
                            (v208, v210) => {
                              match v208 {
                                (v213, v215) => {
                                  (((v213, done_), v215), v210)
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
              let v50 = andb(ltb(0u64, Clone::clone(p0)), ltb(steps_1, lim_1));
              match bdec(v50) {
                sumbool::left => {
                  let v61 = add(steps_1, 1u64);
                  let v62 = hd;
                  let v63 = nx;
                  let v64 = vs;
                  let v65 = ws;
                  let v66 = bad;
                  let v67 = p;
                  dij_acc(hd, nx, vs, ws, bad, p, lim_1, v61, dij_body(v62, v63, v64, v65, v66, v67, st_1), ())
                },
                sumbool::right => {
                  let v104 = Rc::clone(done);
                  std::mem::drop(st_1);
                  v104
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
  let v17 = rocq_array::make::<u64>(n_1, __rocq_global_833);
  let D0 = rocq_array::set::<u64>(v17, u_1, 0u64);
  let v41 = rocq_array::make::<u64>(add(m_1, 1u64), 0u64);
  let hp0 = rocq_array::set::<u64>(v41, 0u64, u_1);
  let v58 = add(m_1, 1u64);
  let v67 = rocq_array::make::<bool>(n_1, false);
  dij_acc_1(hd, nx, vs, ws, bad, p, v58, 0u64, (((D0, v67), hp0), 1u64))
}

// Rocq: Allpairspath.allpairspath_implem.cell
// Variant: borrowed, uncurried
pub fn cell(n: u64, R: &Rc<Array<bool>>, neg: &Rc<Array<bool>>, D: &Rc<Array<u64>>, p: &Rc<Array<u64>>, u: u64, v: u64) -> Rc<answer<u64>> {
  let n_1 = n;
  let u_1 = u;
  let v_1 = v;
  let v10 = neg;
  match rocq_array::get::<bool>(&v10, v_1) {
    true => {
      Rc::new(answer::<u64>::NegInfinity)
    },
    false => {
      let v31 = add(mul(u_1, n_1), v_1);
      let v32 = R;
      match rocq_array::get::<bool>(&v32, v31) {
        true => {
          let v39 = D;
          let v42 = rocq_array::get::<u64>(&v39, v_1);
          let v43 = p;
          let v51 = sub(v42, rocq_array::get::<u64>(&v43, u_1));
          let v52 = p;
          Rc::new(answer::<u64>::Distance(add(v51, rocq_array::get::<u64>(&v52, v_1))))
        },
        false => {
          Rc::new(answer::<u64>::Impossible)
        },
      }
    },
  }
}

// Rocq: Allpairspath.allpairspath_implem.row_of
// Variant: borrowed, uncurried
pub fn row_of(n: u64, m: u64, hd: &Rc<Array<u64>>, nx: &Rc<Array<u64>>, vs: &Rc<Array<u64>>, ws: &Rc<Array<u64>>, R: &Rc<Array<bool>>, bad: &Rc<Array<bool>>, p: &Rc<Array<u64>>, u: u64) -> Rc<Array<Rc<answer<u64>>>> {
  let m_1 = m;
  let v18 = Rc::clone(R);
  let v21 = Rc::clone(bad);
  let v24 = {
    let __anf_capture_25 = n;
    let __anf_capture_31 = u;
    move |v33: u64, v34: Rc<Array<bool>>| -> Rc<Array<bool>> {
      let v37 = Clone::clone(&__anf_capture_25);
      let v39 = Rc::clone(&v18);
      let v41 = Rc::clone(&v21);
      let v43 = Clone::clone(&__anf_capture_31);
      negseed_step(v37, v39, v41, v43, v33, v34)
    }
  };
  let v51: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new(v24);
  let v61 = rocq_array::make::<bool>(n, false);
  let seed = for_loop::<Rc<Array<bool>>>(v51, 0u64, n, v61);
  let v76 = Rc::clone(hd);
  let v79 = Rc::clone(nx);
  let v82 = Rc::clone(vs);
  let neg = closure(n, v76, v79, v82, seed);
  let D = dijkstra(n, m_1, hd, nx, vs, ws, bad, p, u);
  let v111 = Rc::clone(R);
  let v118 = Rc::clone(p);
  let v121 = {
    let __anf_capture_122 = n;
    let __anf_capture_132 = u;
    move |v: u64, r: Rc<Array<Rc<answer<u64>>>>| -> Rc<Array<Rc<answer<u64>>>> {
      let v147 = cell(Clone::clone(&__anf_capture_122), &v111, &neg, &D, &v118, Clone::clone(&__anf_capture_132), v);
      rocq_array::set::<Rc<answer<u64>>>(r, v, v147)
    }
  };
  let v157: Rc<dyn Fn(u64, Rc<Array<Rc<answer<u64>>>>) -> Rc<Array<Rc<answer<u64>>>>> = Rc::new(v121);
  let v168 = rocq_array::make::<Rc<answer<u64>>>(n, Rc::new(answer::<u64>::Impossible));
  for_loop::<Rc<Array<Rc<answer<u64>>>>>(v157, 0u64, n, v168)
}

// Rocq: Allpairspath.allpairspath_implem.allpairspath_impl
// Variant: uncurried
pub fn allpairspath_impl(n: u64, us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>> {
  let v4 = &us;
  let m = rocq_array::length::<u64>(&v4);
  let v13 = Rc::clone(&us);
  let v14 = build_adj(n, m, v13);
  match v14 {
    (v16, v18) => {
      let nx = &v16;
      let hd = &v18;
      let v26 = Rc::clone(nx);
      let v28 = Rc::clone(hd);
      let v31 = Rc::clone(&vs);
      let R = reach_matrix(n, v26, v28, v31);
      let v36 = Rc::clone(&vs);
      let v41 = Rc::clone(&us);
      let v44 = Rc::clone(&R);
      let v45 = {
        let __anf_capture_48 = n;
        move |k: u64| -> bool {
          let vs = &v36;
          let n = &__anf_capture_48;
          let us = &v41;
          let R = &v44;
          let v73 = add(mul(rocq_array::get::<u64>(&vs, k), Clone::clone(n)), rocq_array::get::<u64>(&us, k));
          rocq_array::get::<bool>(&R, v73)
        }
      };
      let v78: Rc<dyn Fn(u64) -> bool> = Rc::new(v45);
      let v86 = Rc::clone(&us);
      let v89 = Rc::clone(&vs);
      let v92 = Rc::clone(&ws);
      let h1 = bf(n, m, v86, v89, v92, v78);
      let v101 = Rc::clone(&us);
      let v104 = Rc::clone(&vs);
      let v107 = Rc::clone(&ws);
      let v110 = Rc::clone(&R);
      let v113 = {
        let __anf_capture_114 = n;
        move |v126: u64, v127: Rc<Array<bool>>| -> Rc<Array<bool>> {
          let v130 = Clone::clone(&__anf_capture_114);
          let v132 = Rc::clone(&v101);
          let v134 = Rc::clone(&v104);
          let v136 = Rc::clone(&v107);
          let v138 = Rc::clone(&v110);
          let v140 = Rc::clone(&h1);
          bad_step(v130, v132, v134, v136, v138, v140, v126, v127)
        }
      };
      let v148: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new(v113);
      let v158 = rocq_array::make::<bool>(n, false);
      let bad = for_loop::<Rc<Array<bool>>>(v148, 0u64, m, v158);
      let v171 = Rc::clone(&us);
      let v174 = Rc::clone(&vs);
      let v177 = Rc::clone(&bad);
      let v178 = {
        move |k: u64| -> bool {
          let us = &v171;
          let vs = &v174;
          let bad = &v177;
          let v191 = rocq_array::get::<u64>(&us, k);
          let v196 = negb(rocq_array::get::<bool>(&bad, v191));
          let v201 = rocq_array::get::<u64>(&vs, k);
          let v204 = rocq_array::get::<bool>(&bad, v201);
          andb(v196, negb(v204))
        }
      };
      let v214: Rc<dyn Fn(u64) -> bool> = Rc::new(v178);
      let v224 = Rc::clone(&vs);
      let v227 = Rc::clone(&ws);
      let p = bf(n, m, us, v224, v227, v214);
      let v250 = {
        let __anf_capture_251 = n;
        let __anf_capture_253 = m;
        let __anf_capture_255 = v16;
        let __anf_capture_257 = v18;
        let __anf_capture_259 = vs;
        let __anf_capture_261 = ws;
        let __anf_capture_263 = R;
        let __anf_capture_265 = bad;
        move |u: u64, res: Rc<Array<Rc<Array<Rc<answer<u64>>>>>>| -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>> {
          let v285 = row_of(Clone::clone(&__anf_capture_251), Clone::clone(&__anf_capture_253), &__anf_capture_255, &__anf_capture_257, &__anf_capture_259, &__anf_capture_261, &__anf_capture_263, &__anf_capture_265, &p, u);
          rocq_array::set::<Rc<Array<Rc<answer<u64>>>>>(res, u, v285)
        }
      };
      let v295: Rc<dyn Fn(u64, Rc<Array<Rc<Array<Rc<answer<u64>>>>>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>>> = Rc::new(v250);
      let v308 = rocq_array::make::<Rc<answer<u64>>>(0u64, Rc::new(answer::<u64>::Impossible));
      let v313 = rocq_array::make::<Rc<Array<Rc<answer<u64>>>>>(n, v308);
      for_loop::<Rc<Array<Rc<Array<Rc<answer<u64>>>>>>>(v295, 0u64, n, v313)
    },
  }
}

// Rocq: Allpairspath.allpairspath_implem.allpairspath_impl
pub fn allpairspath_impl_curried(n: u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>>>>> {
  let v3 = {
    move |us: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>>>> {
      let n = &n;
      let v8 = Clone::clone(n);
      let v11 = {
        move |vs: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>>> {
          let n = &v8;
          let us = &us;
          let v18 = Clone::clone(n);
          let v20 = Rc::clone(us);
          let v23 = {
            move |ws: Rc<Array<u64>>| -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>> {
              let v33 = Clone::clone(&v18);
              let v35 = Rc::clone(&v20);
              let v37 = Rc::clone(&vs);
              allpairspath_impl(v33, v35, v37, ws)
            }
          };
          let v43: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>>> = Rc::new(v23);
          v43
        }
      };
      let v47: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>>>> = Rc::new(v11);
      v47
    }
  };
  let v51: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>>>>> = Rc::new(v3);
  v51
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>>> {
  let v0: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>>> = __rocq_global_1491.with(Clone::clone);
  v0
}
const __rocq_global_833: u64 = 1073741824u64;
std::thread_local! { static __rocq_global_1491: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>>> = allpairspath(); }
std::thread_local! { static __rocq_global_1494: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<Array<Rc<answer<u64>>>>>>>>>> = allpairspath_curried(); }