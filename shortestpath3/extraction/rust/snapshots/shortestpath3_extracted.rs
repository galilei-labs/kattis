// Generated from OwnedANF. This printer is not verified.
#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

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

pub type uint = u64;

pub type sint = u64;

// Rocq: Shortestpath3.shortestpath3_implem.INF
pub fn INF() -> u64 {
  4611686018427387903u64
}

// Rocq: Shortestpath3.shortestpath3_implem.shortestpath3
// Variant: uncurried
pub fn shortestpath3() -> Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>>> {
  let v0: fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>> = shortestpath3_impl;
  let v1: Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>>> = Rc::new(v0);
  v1
}

// Rocq: Shortestpath3.shortestpath3_implem.shortestpath3
pub fn shortestpath3_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>>>>>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>>>>>>> = shortestpath3_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>>>>>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Shortestpath3.shortestpath3_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb
// Variant: uncurried
pub fn ltsb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltsb(v0, v1)
}

// Rocq: Shortestpath3.shortestpath3_implem.relax
// Variant: uncurried
pub fn relax(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, j: u64, d: Rc<Array<u64>>, ch: bool) -> (Rc<Array<u64>>, bool) {
  let v6 = &us;
  let v9 = rocq_array::get::<u64>(&v6, j);
  let v10 = &d;
  let du = rocq_array::get::<u64>(&v10, v9);
  match eqb(du, __rocq_global_7) {
    true => {
      std::mem::drop(vs);
      std::mem::drop(ws);
      std::mem::drop(us);
      (d, ch)
    },
    false => {
      let v30 = &vs;
      let v = rocq_array::get::<u64>(&v30, j);
      let v35 = &ws;
      let v38 = rocq_array::get::<u64>(&v35, j);
      let nd = add(du, v38);
      let v45 = &d;
      let v48 = rocq_array::get::<u64>(&v45, v);
      match ltsb(nd, v48) {
        true => {
          std::mem::drop(vs);
          std::mem::drop(ws);
          std::mem::drop(us);
          let v61 = rocq_array::set::<u64>(d, v, nd);
          (v61, true)
        },
        false => {
          std::mem::drop(vs);
          std::mem::drop(ws);
          std::mem::drop(us);
          (d, ch)
        },
      }
    },
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.edges_loop
// Variant: uncurried
pub fn edges_loop_1(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, m: u64, j: u64, d: Rc<Array<u64>>, ch: bool) -> (Rc<Array<u64>>, bool) {
  edges_loop(us, vs, ws, m, j, d, ch, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.edges_loop (local: edges_loop)
// Variant: uncurried, lifted
pub fn edges_loop(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, m: u64, j: u64, d: Rc<Array<u64>>, ch: bool, _H: ()) -> (Rc<Array<u64>>, bool) {
  let v15 = ltb(j, m);
  match bdec(v15) {
    sumbool::left => {
      let v22 = Rc::clone(&us);
      let v25 = Rc::clone(&vs);
      let v28 = Rc::clone(&ws);
      let v35 = relax(v22, v25, v28, j, d, ch);
      match v35 {
        (v37, v39) => {
          edges_loop(us, vs, ws, m, add(j, 1u64), v37, v39, ())
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
pub fn rounds_loop_1(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, m: u64, R: u64, k: u64, d: Rc<Array<u64>>) -> Rc<Array<u64>> {
  rounds_loop(us, vs, ws, m, R, k, d, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.rounds_loop (local: rounds_loop)
// Variant: uncurried, lifted
pub fn rounds_loop(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, m: u64, R: u64, k: u64, d: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v15 = ltb(k, R);
  match bdec(v15) {
    sumbool::left => {
      let v26 = Rc::clone(&us);
      let v29 = Rc::clone(&vs);
      let v32 = Rc::clone(&ws);
      let v41 = edges_loop_1(v26, v29, v32, m, 0u64, d, false);
      match v41 {
        (v43, v45) => {
          match v45 {
            true => {
              rounds_loop(us, vs, ws, m, R, add(k, 1u64), v43, ())
            },
            false => {
              std::mem::drop(us);
              std::mem::drop(vs);
              std::mem::drop(ws);
              v43
            },
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
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

// Rocq: Shortestpath3.shortestpath3_implem.seed_loop
// Variant: uncurried
pub fn seed_loop_1(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, d: Rc<Array<u64>>, m: u64, j: u64, mk: Rc<Array<u64>>, q: Rc<Array<u64>>, tl: u64) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  seed_loop(us, vs, ws, d, m, j, mk, q, tl, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.seed_loop (local: seed_loop)
// Variant: uncurried, lifted
pub fn seed_loop(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, d: Rc<Array<u64>>, m: u64, j: u64, mk: Rc<Array<u64>>, q: Rc<Array<u64>>, tl: u64, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let v17 = ltb(j, m);
  match bdec(v17) {
    sumbool::left => {
      let v21 = &us;
      let v24 = rocq_array::get::<u64>(&v21, j);
      let v25 = &d;
      let du = rocq_array::get::<u64>(&v25, v24);
      let v29 = &vs;
      let v = rocq_array::get::<u64>(&v29, j);
      let v45 = negb(eqb(du, __rocq_global_7));
      let v48 = &ws;
      let v51 = rocq_array::get::<u64>(&v48, j);
      let v56 = add(du, v51);
      let v57 = &d;
      let v60 = rocq_array::get::<u64>(&v57, v);
      let v70 = andb(v45, ltsb(v56, v60));
      let v72 = &mk;
      let v75 = rocq_array::get::<u64>(&v72, v);
      let v82 = eqb(v75, 0u64);
      match andb(v70, v82) {
        true => {
          let v96 = add(j, 1u64);
          let v105 = rocq_array::set::<u64>(mk, v, 1u64);
          let v112 = rocq_array::set::<u64>(q, tl, v);
          seed_loop(us, vs, ws, d, m, v96, v105, v112, add(tl, 1u64), ())
        },
        false => {
          seed_loop(us, vs, ws, d, m, add(j, 1u64), mk, q, tl, ())
        },
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
pub fn build_loop_1(us: Rc<Array<u64>>, m: u64, j: u64, hd: Rc<Array<u64>>, nx: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  build_loop(us, m, j, hd, nx, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.build_loop (local: build_loop)
// Variant: uncurried, lifted
pub fn build_loop(us: Rc<Array<u64>>, m: u64, j: u64, hd: Rc<Array<u64>>, nx: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v13 = ltb(j, m);
  match bdec(v13) {
    sumbool::left => {
      let v17 = &us;
      let u = rocq_array::get::<u64>(&v17, j);
      let v21 = &hd;
      let h = rocq_array::get::<u64>(&v21, u);
      let v32 = add(j, 1u64);
      let v47 = rocq_array::set::<u64>(hd, u, add(j, 1u64));
      let v54 = rocq_array::set::<u64>(nx, j, h);
      build_loop(us, m, v32, v47, v54, ())
    },
    sumbool::right => {
      std::mem::drop(us);
      (hd, nx)
    },
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.adj_loop
// Variant: uncurried
pub fn adj_loop_1(vs: Rc<Array<u64>>, nx: Rc<Array<u64>>, e: u64, mk: Rc<Array<u64>>, q: Rc<Array<u64>>, tl: u64) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  adj_loop(vs, nx, e, mk, q, tl, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.adj_loop (local: adj_loop)
// Variant: uncurried, lifted
pub fn adj_loop(vs: Rc<Array<u64>>, nx: Rc<Array<u64>>, e: u64, mk: Rc<Array<u64>>, q: Rc<Array<u64>>, tl: u64, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let v16 = ltb(0u64, e);
  match bdec(v16) {
    sumbool::left => {
      let j = sub(e, 1u64);
      let v28 = &vs;
      let v = rocq_array::get::<u64>(&v28, j);
      let v32 = &nx;
      let e_ = rocq_array::get::<u64>(&v32, j);
      let v43 = ltb(e_, e);
      match bdec(v43) {
        sumbool::left => {
          let v48 = &mk;
          let v51 = rocq_array::get::<u64>(&v48, v);
          match eqb(v51, 0u64) {
            true => {
              let v68 = rocq_array::set::<u64>(mk, v, 1u64);
              let v75 = rocq_array::set::<u64>(q, tl, v);
              adj_loop(vs, nx, e_, v68, v75, add(tl, 1u64), ())
            },
            false => {
              adj_loop(vs, nx, e_, mk, q, tl, ())
            },
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
pub fn bfs_loop_1(vs: Rc<Array<u64>>, hd: Rc<Array<u64>>, nx: Rc<Array<u64>>, n: u64, h: u64, mk: Rc<Array<u64>>, q: Rc<Array<u64>>, tl: u64) -> Rc<Array<u64>> {
  bfs_loop(vs, hd, nx, n, h, mk, q, tl, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.bfs_loop (local: bfs_loop)
// Variant: uncurried, lifted
pub fn bfs_loop(vs: Rc<Array<u64>>, hd: Rc<Array<u64>>, nx: Rc<Array<u64>>, n: u64, h: u64, mk: Rc<Array<u64>>, q: Rc<Array<u64>>, tl: u64, _H: ()) -> Rc<Array<u64>> {
  let v16 = ltb(h, tl);
  match bdec(v16) {
    sumbool::left => {
      let v27 = ltb(h, n);
      match bdec(v27) {
        sumbool::left => {
          let v31 = &q;
          let x = rocq_array::get::<u64>(&v31, h);
          let v36 = &hd;
          let v39 = rocq_array::get::<u64>(&v36, x);
          let v42 = Rc::clone(&vs);
          let v45 = Rc::clone(&nx);
          let v54 = adj_loop_1(v42, v45, v39, mk, q, tl);
          match v54 {
            (v56, v58) => {
              match v56 {
                (v61, v63) => {
                  bfs_loop(vs, hd, nx, n, add(h, 1u64), v61, v63, v58, ())
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
pub fn answer_of(d: Rc<Array<u64>>, mk: Rc<Array<u64>>, t: u64) -> Rc<answer<u64>> {
  let v3 = &d;
  let x = rocq_array::get::<u64>(&v3, t);
  match eqb(x, __rocq_global_7) {
    true => {
      std::mem::drop(mk);
      std::mem::drop(d);
      Rc::new(answer::<u64>::Impossible)
    },
    false => {
      let v21 = &mk;
      let v24 = rocq_array::get::<u64>(&v21, t);
      match eqb(v24, 0u64) {
        true => {
          std::mem::drop(mk);
          std::mem::drop(d);
          Rc::new(answer::<u64>::Dist { distance: x })
        },
        false => {
          std::mem::drop(mk);
          std::mem::drop(d);
          Rc::new(answer::<u64>::MinusInfinity)
        },
      }
    },
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.ans_loop
// Variant: uncurried
pub fn ans_loop_1(d: Rc<Array<u64>>, mk: Rc<Array<u64>>, qs: Rc<Array<u64>>, Q: u64, i: u64, out: Rc<Array<Rc<answer<u64>>>>) -> Rc<Array<Rc<answer<u64>>>> {
  ans_loop(d, mk, qs, Q, i, out, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.ans_loop (local: ans_loop)
// Variant: uncurried, lifted
pub fn ans_loop(d: Rc<Array<u64>>, mk: Rc<Array<u64>>, qs: Rc<Array<u64>>, Q: u64, i: u64, out: Rc<Array<Rc<answer<u64>>>>, _H: ()) -> Rc<Array<Rc<answer<u64>>>> {
  let v14 = ltb(i, Q);
  match bdec(v14) {
    sumbool::left => {
      let v19 = &qs;
      let v22 = rocq_array::get::<u64>(&v19, i);
      let v25 = Rc::clone(&d);
      let v28 = Rc::clone(&mk);
      let a = answer_of(v25, v28, v22);
      let v39 = add(i, 1u64);
      let v46 = rocq_array::set::<Rc<answer<u64>>>(out, i, a);
      ans_loop(d, mk, qs, Q, v39, v46, ())
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
pub fn shortestpath3_impl(n: u64, s: u64, us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, qs: Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>> {
  let v6 = &us;
  let m = rocq_array::length::<u64>(&v6);
  let v13 = rocq_array::make::<u64>(n, __rocq_global_7);
  let d0 = rocq_array::set::<u64>(v13, s, 0u64);
  let v31 = sub(n, 1u64);
  let v36 = Rc::clone(&us);
  let v39 = Rc::clone(&vs);
  let v42 = Rc::clone(&ws);
  let d = rounds_loop_1(v36, v39, v42, m, v31, 0u64, d0);
  let v61 = rocq_array::make::<u64>(n, 0u64);
  let v68 = rocq_array::make::<u64>(n, 0u64);
  let v73 = Rc::clone(&us);
  let v76 = Rc::clone(&vs);
  let v81 = Rc::clone(&d);
  let v92 = seed_loop_1(v73, v76, ws, v81, m, 0u64, v61, v68, 0u64);
  match v92 {
    (v94, v96) => {
      match v94 {
        (v99, v101) => {
          let v112 = rocq_array::make::<u64>(n, 0u64);
          let v119 = rocq_array::make::<u64>(m, 0u64);
          let v130 = build_loop_1(us, m, 0u64, v112, v119);
          match v130 {
            (v132, v134) => {
              let mk_ = bfs_loop_1(vs, v132, v134, n, 0u64, v99, v101, v96);
              let v156 = &qs;
              let Q = rocq_array::length::<u64>(&v156);
              let v168 = rocq_array::make::<Rc<answer<u64>>>(Q, Rc::new(answer::<u64>::Impossible));
              ans_loop_1(d, mk_, qs, Q, 0u64, v168)
            },
          }
        },
      }
    },
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.shortestpath3_impl
pub fn shortestpath3_impl_curried(n: u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>>>>>>> {
  let v3 = {
    move |s: u64| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>>>>>> {
      let n = &n;
      let v8 = Clone::clone(n);
      let v11 = {
        move |us: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>>>>> {
          let n = &v8;
          let s = &s;
          let v18 = Clone::clone(n);
          let v20 = Clone::clone(s);
          let v23 = {
            move |vs: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>>>> {
              let n = &v18;
              let s = &v20;
              let us = &us;
              let v32 = Clone::clone(n);
              let v34 = Clone::clone(s);
              let v36 = Rc::clone(us);
              let v39 = {
                move |ws: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>>> {
                  let n = &v32;
                  let s = &v34;
                  let us = &v36;
                  let vs = &vs;
                  let v50 = Clone::clone(n);
                  let v52 = Clone::clone(s);
                  let v54 = Rc::clone(us);
                  let v56 = Rc::clone(vs);
                  let v59 = {
                    move |qs: Rc<Array<u64>>| -> Rc<Array<Rc<answer<u64>>>> {
                      let v73 = Clone::clone(&v50);
                      let v75 = Clone::clone(&v52);
                      let v77 = Rc::clone(&v54);
                      let v79 = Rc::clone(&v56);
                      let v81 = Rc::clone(&ws);
                      shortestpath3_impl(v73, v75, v77, v79, v81, qs)
                    }
                  };
                  let v87: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>>> = Rc::new(v59);
                  v87
                }
              };
              let v91: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>>>> = Rc::new(v39);
              v91
            }
          };
          let v95: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>>>>> = Rc::new(v23);
          v95
        }
      };
      let v99: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>>>>>> = Rc::new(v11);
      v99
    }
  };
  let v103: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>>>>>>> = Rc::new(v3);
  v103
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

pub fn run() -> Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>>> {
  let v0: Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>>> = __rocq_global_763.with(Clone::clone);
  v0
}
const __rocq_global_7: u64 = 4611686018427387903u64;
std::thread_local! { static __rocq_global_763: Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>>> = shortestpath3(); }
std::thread_local! { static __rocq_global_766: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>>>>>>>> = shortestpath3_curried(); }