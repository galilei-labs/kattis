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

pub type uint = u64;

// Rocq: Chesstournament.chesstournament_implem.chess_consistent
// Variant: uncurried
pub fn chess_consistent() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<bool>>, Rc<Array<u64>>) -> bool> {
  let v0: fn(u64, Rc<Array<u64>>, Rc<Array<bool>>, Rc<Array<u64>>) -> bool = chess_impl;
  let v1: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<bool>>, Rc<Array<u64>>) -> bool> = Rc::new(v0);
  v1
}

// Rocq: Chesstournament.chesstournament_implem.chess_consistent
pub fn chess_consistent_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<bool>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<bool>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>> = chess_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<bool>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>>> = Rc::new(v0);
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

// Rocq: Chesstournament.chesstournament_implem.bdec
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

// Rocq: Chesstournament.chesstournament_implem.iota_loop
// Variant: uncurried
pub fn iota_loop_1(n: u64, x: u64, p: Rc<Array<u64>>) -> Rc<Array<u64>> {
  iota_loop(n, x, p, ())
}

// Rocq: Chesstournament.chesstournament_implem.iota_loop (local: iota_loop)
// Variant: uncurried, lifted
pub fn iota_loop(n: u64, x: u64, p: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v11 = ltb(x, n);
  match bdec(v11) {
    sumbool::left => {
      let v22 = add(x, 1u64);
      let v29 = rocq_array::set::<u64>(p, x, x);
      iota_loop(n, v22, v29, ())
    },
    sumbool::right => {
      p
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.iota
pub fn iota(n: u64) -> Rc<Array<u64>> {
  let v10 = rocq_array::make::<u64>(n, 0u64);
  iota_loop_1(n, 0u64, v10)
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let v3 = Clone::clone((&(&p).1));
  std::mem::drop(p);
  v3
}

// Rocq: Chesstournament.chesstournament_implem.find
// Variant: uncurried
pub fn find_1(p: Rc<Array<u64>>, x: u64) -> (Rc<Array<u64>>, u64) {
  find(p, x, ())
}

// Rocq: Chesstournament.chesstournament_implem.find (local: find)
// Variant: uncurried, lifted
pub fn find(p: Rc<Array<u64>>, x: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let v3 = &p;
  let y = rocq_array::get::<u64>(&v3, x);
  let v14 = eqb(y, x);
  match bdec(v14) {
    sumbool::left => {
      (p, x)
    },
    sumbool::right => {
      let f = find(p, y, ());
      let v38 = Clone::clone(&f);
      let v40 = fst::<Rc<Array<u64>>, u64>(v38);
      let v43 = Clone::clone(&f);
      let v52 = rocq_array::set::<u64>(v40, x, snd::<Rc<Array<u64>>, u64>(v43));
      (v52, snd::<Rc<Array<u64>>, u64>(f))
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.union
// Variant: uncurried
pub fn union(p: Rc<Array<u64>>, rk: Rc<Array<u64>>, a: u64, b: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  match eqb(a, b) {
    true => {
      (p, rk)
    },
    false => {
      let v19 = &rk;
      let ra = rocq_array::get::<u64>(&v19, a);
      let v23 = &rk;
      let rb = rocq_array::get::<u64>(&v23, b);
      match ltb(ra, rb) {
        true => {
          let v41 = rocq_array::set::<u64>(p, a, b);
          (v41, rk)
        },
        false => {
          match ltb(rb, ra) {
            true => {
              let v63 = rocq_array::set::<u64>(p, b, a);
              (v63, rk)
            },
            false => {
              let v77 = rocq_array::set::<u64>(p, b, a);
              let v92 = rocq_array::set::<u64>(rk, a, add(ra, 1u64));
              (v77, v92)
            },
          }
        },
      }
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.unite
// Variant: uncurried
pub fn unite(p: Rc<Array<u64>>, rk: Rc<Array<u64>>, k: u64, l: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let f1 = find_1(p, k);
  let v13 = Clone::clone(&f1);
  let v16 = fst::<Rc<Array<u64>>, u64>(v13);
  let f2 = find_1(v16, l);
  let v24 = Clone::clone(&f2);
  let v26 = fst::<Rc<Array<u64>>, u64>(v24);
  union(v26, rk, snd::<Rc<Array<u64>>, u64>(f1), snd::<Rc<Array<u64>>, u64>(f2))
}

// Rocq: Chesstournament.chesstournament_implem.uf_loop
// Variant: uncurried
pub fn uf_loop_1(ks: Rc<Array<u64>>, wins: Rc<Array<bool>>, ls: Rc<Array<u64>>, m: u64, j: u64, p: Rc<Array<u64>>, rk: Rc<Array<u64>>) -> Rc<Array<u64>> {
  uf_loop(ks, wins, ls, m, j, p, rk, (), ())
}

// Rocq: Chesstournament.chesstournament_implem.uf_loop (local: uf_loop)
// Variant: uncurried, lifted
pub fn uf_loop(ks: Rc<Array<u64>>, wins: Rc<Array<bool>>, ls: Rc<Array<u64>>, m: u64, j: u64, p: Rc<Array<u64>>, rk: Rc<Array<u64>>, _Hp: (), _H: ()) -> Rc<Array<u64>> {
  let v16 = ltb(j, m);
  match bdec(v16) {
    sumbool::left => {
      let v20 = &wins;
      let v23 = rocq_array::get::<bool>(&v20, j);
      match v23 {
        true => {
          uf_loop(ks, wins, ls, m, add(j, 1u64), p, rk, (), ())
        },
        false => {
          let v60 = &ks;
          let v63 = rocq_array::get::<u64>(&v60, j);
          let v64 = &ls;
          let v67 = rocq_array::get::<u64>(&v64, j);
          let u = unite(p, rk, v63, v67);
          let v84 = add(j, 1u64);
          let v87 = Clone::clone(&u);
          let v89 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(v87);
          let v93 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(u);
          uf_loop(ks, wins, ls, m, v84, v89, v93, (), ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(ks);
      std::mem::drop(wins);
      std::mem::drop(ls);
      std::mem::drop(rk);
      p
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.rep_loop
// Variant: uncurried
pub fn rep_loop_1(n: u64, x: u64, p: Rc<Array<u64>>, rep: Rc<Array<u64>>) -> Rc<Array<u64>> {
  rep_loop(n, x, p, rep, (), ())
}

// Rocq: Chesstournament.chesstournament_implem.rep_loop (local: rep_loop)
// Variant: uncurried, lifted
pub fn rep_loop(n: u64, x: u64, p: Rc<Array<u64>>, rep: Rc<Array<u64>>, _Hp: (), _H: ()) -> Rc<Array<u64>> {
  let v13 = ltb(x, n);
  match bdec(v13) {
    sumbool::left => {
      let f = find_1(p, x);
      let v30 = add(x, 1u64);
      let v33 = Clone::clone(&f);
      let v35 = fst::<Rc<Array<u64>>, u64>(v33);
      let v46 = rocq_array::set::<u64>(rep, x, snd::<Rc<Array<u64>>, u64>(f));
      rep_loop(n, v30, v35, v46, (), ())
    },
    sumbool::right => {
      std::mem::drop(p);
      rep
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.deg_loop
// Variant: uncurried
pub fn deg_loop_1(rep: Rc<Array<u64>>, ks: Rc<Array<u64>>, wins: Rc<Array<bool>>, ls: Rc<Array<u64>>, m: u64, j: u64, od: Rc<Array<u64>>, id: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  deg_loop(rep, ks, wins, ls, m, j, od, id, ())
}

// Rocq: Chesstournament.chesstournament_implem.deg_loop (local: deg_loop)
// Variant: uncurried, lifted
pub fn deg_loop(rep: Rc<Array<u64>>, ks: Rc<Array<u64>>, wins: Rc<Array<bool>>, ls: Rc<Array<u64>>, m: u64, j: u64, od: Rc<Array<u64>>, id: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v16 = ltb(j, m);
  match bdec(v16) {
    sumbool::left => {
      let v20 = &wins;
      let v23 = rocq_array::get::<bool>(&v20, j);
      match v23 {
        true => {
          let v25 = &ks;
          let v28 = rocq_array::get::<u64>(&v25, j);
          let v29 = &rep;
          let a = rocq_array::get::<u64>(&v29, v28);
          let v33 = &ls;
          let v36 = rocq_array::get::<u64>(&v33, j);
          let v37 = &rep;
          let b = rocq_array::get::<u64>(&v37, v36);
          let v48 = add(j, 1u64);
          let v50 = &od;
          let v53 = rocq_array::get::<u64>(&v50, a);
          let v67 = rocq_array::set::<u64>(od, a, add(v53, 1u64));
          let v69 = &id;
          let v72 = rocq_array::get::<u64>(&v69, b);
          let v86 = rocq_array::set::<u64>(id, b, add(v72, 1u64));
          deg_loop(rep, ks, wins, ls, m, v48, v67, v86, ())
        },
        false => {
          deg_loop(rep, ks, wins, ls, m, add(j, 1u64), od, id, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(rep);
      std::mem::drop(ks);
      std::mem::drop(wins);
      std::mem::drop(ls);
      (od, id)
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.pre_loop
// Variant: uncurried
pub fn pre_loop_1(od: Rc<Array<u64>>, n: u64, u: u64, s: u64, st: Rc<Array<u64>>, pos: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  pre_loop(od, n, u, s, st, pos, ())
}

// Rocq: Chesstournament.chesstournament_implem.pre_loop (local: pre_loop)
// Variant: uncurried, lifted
pub fn pre_loop(od: Rc<Array<u64>>, n: u64, u: u64, s: u64, st: Rc<Array<u64>>, pos: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v14 = ltb(u, n);
  match bdec(v14) {
    sumbool::left => {
      let v19 = &od;
      let v22 = rocq_array::get::<u64>(&v19, u);
      let s_ = add(s, v22);
      let v35 = add(u, 1u64);
      let v50 = rocq_array::set::<u64>(st, add(u, 1u64), s_);
      let v57 = rocq_array::set::<u64>(pos, u, s);
      pre_loop(od, n, v35, s_, v50, v57, ())
    },
    sumbool::right => {
      std::mem::drop(od);
      (st, pos)
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(rep: Rc<Array<u64>>, ks: Rc<Array<u64>>, wins: Rc<Array<bool>>, ls: Rc<Array<u64>>, m: u64, j: u64, pos: Rc<Array<u64>>, adj: Rc<Array<u64>>) -> Rc<Array<u64>> {
  fill_loop(rep, ks, wins, ls, m, j, pos, adj, ())
}

// Rocq: Chesstournament.chesstournament_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(rep: Rc<Array<u64>>, ks: Rc<Array<u64>>, wins: Rc<Array<bool>>, ls: Rc<Array<u64>>, m: u64, j: u64, pos: Rc<Array<u64>>, adj: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v16 = ltb(j, m);
  match bdec(v16) {
    sumbool::left => {
      let v20 = &wins;
      let v23 = rocq_array::get::<bool>(&v20, j);
      match v23 {
        true => {
          let v25 = &ks;
          let v28 = rocq_array::get::<u64>(&v25, j);
          let v29 = &rep;
          let a = rocq_array::get::<u64>(&v29, v28);
          let v33 = &pos;
          let pa = rocq_array::get::<u64>(&v33, a);
          let v44 = add(j, 1u64);
          let v59 = rocq_array::set::<u64>(pos, a, add(pa, 1u64));
          let v60 = &ls;
          let v63 = rocq_array::get::<u64>(&v60, j);
          let v64 = &rep;
          let v67 = rocq_array::get::<u64>(&v64, v63);
          let v74 = rocq_array::set::<u64>(adj, pa, v67);
          fill_loop(rep, ks, wins, ls, m, v44, v59, v74, ())
        },
        false => {
          fill_loop(rep, ks, wins, ls, m, add(j, 1u64), pos, adj, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(rep);
      std::mem::drop(ks);
      std::mem::drop(wins);
      std::mem::drop(ls);
      std::mem::drop(pos);
      adj
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(id: Rc<Array<u64>>, n: u64, v: u64, q: Rc<Array<u64>>, t: u64) -> (Rc<Array<u64>>, u64) {
  init_loop(id, n, v, q, t, ())
}

// Rocq: Chesstournament.chesstournament_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(id: Rc<Array<u64>>, n: u64, v: u64, q: Rc<Array<u64>>, t: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let v13 = ltb(v, n);
  match bdec(v13) {
    sumbool::left => {
      let v18 = &id;
      let v21 = rocq_array::get::<u64>(&v18, v);
      match eqb(v21, 0u64) {
        true => {
          let v37 = add(v, 1u64);
          let v44 = rocq_array::set::<u64>(q, t, v);
          init_loop(id, n, v37, v44, add(t, 1u64), ())
        },
        false => {
          init_loop(id, n, add(v, 1u64), q, t, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(id);
      (q, t)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Chesstournament.chesstournament_implem.inner
// Variant: uncurried
pub fn inner_1(adj: Rc<Array<u64>>, hi: u64, e: u64, d: Rc<Array<u64>>, q: Rc<Array<u64>>, t: u64) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  inner(adj, hi, e, d, q, t, ())
}

// Rocq: Chesstournament.chesstournament_implem.inner (local: inner)
// Variant: uncurried, lifted
pub fn inner(adj: Rc<Array<u64>>, hi: u64, e: u64, d: Rc<Array<u64>>, q: Rc<Array<u64>>, t: u64, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let v14 = ltb(e, hi);
  match bdec(v14) {
    sumbool::left => {
      let v18 = &adj;
      let v = rocq_array::get::<u64>(&v18, e);
      let v23 = &d;
      let v26 = rocq_array::get::<u64>(&v23, v);
      let dv = sub(v26, 1u64);
      match eqb(dv, 0u64) {
        true => {
          let v50 = add(e, 1u64);
          let v57 = rocq_array::set::<u64>(d, v, dv);
          let v64 = rocq_array::set::<u64>(q, t, v);
          inner(adj, hi, v50, v57, v64, add(t, 1u64), ())
        },
        false => {
          let v100 = add(e, 1u64);
          let v107 = rocq_array::set::<u64>(d, v, dv);
          inner(adj, hi, v100, v107, q, t, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(adj);
      ((d, q), t)
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.kahn
// Variant: uncurried
pub fn kahn_1(adj: Rc<Array<u64>>, st: Rc<Array<u64>>, h: u64, d: Rc<Array<u64>>, q: Rc<Array<u64>>, t: u64) -> u64 {
  kahn(adj, st, h, d, q, t, ())
}

// Rocq: Chesstournament.chesstournament_implem.kahn (local: kahn)
// Variant: uncurried, lifted
pub fn kahn(adj: Rc<Array<u64>>, st: Rc<Array<u64>>, h: u64, d: Rc<Array<u64>>, q: Rc<Array<u64>>, t: u64, _H: ()) -> u64 {
  let v14 = ltb(h, t);
  match bdec(v14) {
    sumbool::left => {
      let v18 = &q;
      let u = rocq_array::get::<u64>(&v18, h);
      let v30 = add(u, 1u64);
      let v31 = &st;
      let v34 = rocq_array::get::<u64>(&v31, v30);
      let v35 = &st;
      let v38 = rocq_array::get::<u64>(&v35, u);
      let v41 = Rc::clone(&adj);
      let r = inner_1(v41, v34, v38, d, q, t);
      let v60 = add(h, 1u64);
      let v64 = Clone::clone(&r);
      let v69 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(v64));
      let v73 = Clone::clone(&r);
      let v78 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(v73));
      kahn(adj, st, v60, v69, v78, snd::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r), ())
    },
    sumbool::right => {
      std::mem::drop(adj);
      std::mem::drop(st);
      std::mem::drop(d);
      std::mem::drop(q);
      t
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.chess_impl
// Variant: uncurried
pub fn chess_impl(n: u64, ks: Rc<Array<u64>>, wins: Rc<Array<bool>>, ls: Rc<Array<u64>>) -> bool {
  let v4 = &ks;
  let m = rocq_array::length::<u64>(&v4);
  let p0 = iota(n);
  let v19 = rocq_array::make::<u64>(n, 0u64);
  let v22 = Rc::clone(&ks);
  let v25 = Rc::clone(&wins);
  let v28 = Rc::clone(&ls);
  let p1 = uf_loop_1(v22, v25, v28, m, 0u64, p0, v19);
  let v47 = rocq_array::make::<u64>(n, 0u64);
  let rep = rep_loop_1(n, 0u64, p1, v47);
  let v66 = rocq_array::make::<u64>(n, 0u64);
  let v73 = rocq_array::make::<u64>(n, 0u64);
  let v76 = Rc::clone(&rep);
  let v79 = Rc::clone(&ks);
  let v82 = Rc::clone(&wins);
  let v85 = Rc::clone(&ls);
  let dg = deg_loop_1(v76, v79, v82, v85, m, 0u64, v66, v73);
  let v98 = Clone::clone(&dg);
  let v100 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(v98);
  let v119 = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  let v126 = rocq_array::make::<u64>(n, 0u64);
  let sp = pre_loop_1(v100, n, 0u64, 0u64, v119, v126);
  let v145 = Clone::clone(&sp);
  let v147 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(v145);
  let v154 = rocq_array::make::<u64>(m, 0u64);
  let adj = fill_loop_1(rep, ks, wins, ls, m, 0u64, v147, v154);
  let v175 = Clone::clone(&dg);
  let v177 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(v175);
  let v186 = rocq_array::make::<u64>(n, 0u64);
  let qi = init_loop_1(v177, n, 0u64, v186, 0u64);
  let v204 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(sp);
  let v210 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(dg);
  let v213 = Clone::clone(&qi);
  let v215 = fst::<Rc<Array<u64>>, u64>(v213);
  let t = kahn_1(adj, v204, 0u64, v210, v215, snd::<Rc<Array<u64>>, u64>(qi));
  eqb(t, n)
}

// Rocq: Chesstournament.chesstournament_implem.chess_impl
pub fn chess_impl_curried(n: u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<bool>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>> {
  let v3 = {
    move |ks: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<bool>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>> {
      let n = &n;
      let v8 = Clone::clone(n);
      let v11 = {
        move |wins: Rc<Array<bool>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> bool> {
          let n = &v8;
          let ks = &ks;
          let v18 = Clone::clone(n);
          let v20 = Rc::clone(ks);
          let v23 = {
            move |ls: Rc<Array<u64>>| -> bool {
              let v33 = Clone::clone(&v18);
              let v35 = Rc::clone(&v20);
              let v37 = Rc::clone(&wins);
              chess_impl(v33, v35, v37, ls)
            }
          };
          let v43: Rc<dyn Fn(Rc<Array<u64>>) -> bool> = Rc::new(v23);
          v43
        }
      };
      let v47: Rc<dyn Fn(Rc<Array<bool>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>> = Rc::new(v11);
      v47
    }
  };
  let v51: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<bool>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<bool>>, Rc<Array<u64>>) -> bool> {
  let v0: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<bool>>, Rc<Array<u64>>) -> bool> = __rocq_global_900.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_900: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<bool>>, Rc<Array<u64>>) -> bool> = chess_consistent(); }
std::thread_local! { static __rocq_global_903: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<bool>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>>> = chess_consistent_curried(); }