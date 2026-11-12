// Generated from OwnedANF. This printer is not verified.
#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub struct St {
  pub st_dist: Rc<Array<u64>>,
  pub st_hk: Rc<Array<u64>>,
  pub st_hv: Rc<Array<u64>>,
  pub st_sz: u64,
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

pub type uint = u64;

// Rocq: Shortestpath1.shortestpath1_implem.INF
pub fn INF() -> u64 {
  9223372036854775807u64
}

// Rocq: Shortestpath1.shortestpath1_implem.dijkstra
// Variant: uncurried
pub fn dijkstra() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, u64) -> Rc<Array<Rc<option<u64>>>>> {
  let v0: fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, u64) -> Rc<Array<Rc<option<u64>>>> = dijkstra_impl_owned;
  let v1: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, u64) -> Rc<Array<Rc<option<u64>>>>> = Rc::new(v0);
  v1
}

// Rocq: Shortestpath1.shortestpath1_implem.dijkstra
pub fn dijkstra_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(u64) -> Rc<Array<Rc<option<u64>>>>>>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(u64) -> Rc<Array<Rc<option<u64>>>>>>>> = dijkstra_impl_curried_owned;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(u64) -> Rc<Array<Rc<option<u64>>>>>>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsr
// Variant: uncurried
pub fn lsr(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsr(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Shortestpath1.shortestpath1_implem.bdec
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

// Rocq: Shortestpath1.shortestpath1_implem.count_loop
// Variant: uncurried
pub fn count_loop_1(us: Rc<Array<u64>>, m: u64, k: u64, c: Rc<Array<u64>>) -> Rc<Array<u64>> {
  count_loop(us, m, k, c, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.count_loop (local: count_loop)
// Variant: uncurried, lifted
pub fn count_loop(us: Rc<Array<u64>>, m: u64, k: u64, c: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(k, m);
  match bdec(v12) {
    sumbool::left => {
      let v17 = &us;
      let v20 = rocq_array::get::<u64>(&v17, k);
      let u1 = add(v20, 1u64);
      let v35 = add(k, 1u64);
      let v37 = &c;
      let v40 = rocq_array::get::<u64>(&v37, u1);
      let v54 = rocq_array::set::<u64>(c, u1, add(v40, 1u64));
      count_loop(us, m, v35, v54, ())
    },
    sumbool::right => {
      std::mem::drop(us);
      c
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.prefix_loop
// Variant: uncurried
pub fn prefix_loop_1(n: u64, i: u64, c: Rc<Array<u64>>) -> Rc<Array<u64>> {
  prefix_loop(n, i, c, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.prefix_loop (local: prefix_loop)
// Variant: uncurried, lifted
pub fn prefix_loop(n: u64, i: u64, c: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v11 = ltb(i, n);
  match bdec(v11) {
    sumbool::left => {
      let v15 = &c;
      let a = rocq_array::get::<u64>(&v15, i);
      let v26 = add(i, 1u64);
      let v27 = &c;
      let b = rocq_array::get::<u64>(&v27, v26);
      let v38 = add(i, 1u64);
      let v59 = rocq_array::set::<u64>(c, add(i, 1u64), add(b, a));
      prefix_loop(n, v38, v59, ())
    },
    sumbool::right => {
      c
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, m: u64, k: u64, pos: Rc<Array<u64>>, adj: Rc<Array<u64>>, wt: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  fill_loop(us, vs, ws, m, k, pos, adj, wt, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, m: u64, k: u64, pos: Rc<Array<u64>>, adj: Rc<Array<u64>>, wt: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v16 = ltb(k, m);
  match bdec(v16) {
    sumbool::left => {
      let v20 = &us;
      let u = rocq_array::get::<u64>(&v20, k);
      let v24 = &pos;
      let j = rocq_array::get::<u64>(&v24, u);
      let v35 = add(k, 1u64);
      let v50 = rocq_array::set::<u64>(pos, u, add(j, 1u64));
      let v51 = &vs;
      let v54 = rocq_array::get::<u64>(&v51, k);
      let v61 = rocq_array::set::<u64>(adj, j, v54);
      let v62 = &ws;
      let v65 = rocq_array::get::<u64>(&v62, k);
      let v72 = rocq_array::set::<u64>(wt, j, v65);
      fill_loop(us, vs, ws, m, v35, v50, v61, v72, ())
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Shortestpath1.shortestpath1_implem.st_sz
pub fn st_sz_owned(s: Rc<St>) -> u64 {
  let v3 = Clone::clone((&(&**&s).st_sz));
  std::mem::drop(s);
  v3
}

// Rocq: Shortestpath1.shortestpath1_implem.st_sz
// Variant: borrowed
pub fn st_sz(s: &Rc<St>) -> u64 {
  let v1 = s;
  Clone::clone((&(&**v1).st_sz))
}

// Rocq: Shortestpath1.shortestpath1_implem.st_hv
// Variant: borrowed
pub fn st_hv(s: &Rc<St>) -> Rc<Array<u64>> {
  let v1 = s;
  Rc::clone((&(&**v1).st_hv))
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

// Rocq: Shortestpath1.shortestpath1_implem.child
// Variant: uncurried
pub fn child(hk: Rc<Array<u64>>, sz: u64, l: u64) -> u64 {
  let v17 = ltb(add(l, 1u64), sz);
  let v26 = add(l, 1u64);
  let v27 = &hk;
  let v30 = rocq_array::get::<u64>(&v27, v26);
  let v31 = &hk;
  let v34 = rocq_array::get::<u64>(&v31, l);
  let v39 = ltb(v30, v34);
  match andb(v17, v39) {
    true => {
      std::mem::drop(hk);
      add(l, 1u64)
    },
    false => {
      std::mem::drop(hk);
      l
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.sift_down
// Variant: uncurried
pub fn sift_down_1(hk: Rc<Array<u64>>, hv: Rc<Array<u64>>, sz: u64, i: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  sift_down(hk, hv, sz, i, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.sift_down (local: sift_down)
// Variant: uncurried, lifted
pub fn sift_down(hk: Rc<Array<u64>>, hv: Rc<Array<u64>>, sz: u64, i: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v11 = add(i, i);
  let l = add(v11, 1u64);
  let v38 = andb(ltb(l, sz), ltb(i, l));
  match bdec(v38) {
    sumbool::left => {
      let v45 = Rc::clone(&hk);
      let c = child(v45, sz, l);
      let v51 = &hk;
      let ki = rocq_array::get::<u64>(&v51, i);
      let v55 = &hk;
      let kc = rocq_array::get::<u64>(&v55, c);
      let v66 = ltb(kc, ki);
      match bdec(v66) {
        sumbool::left => {
          let v70 = &hv;
          let vi = rocq_array::get::<u64>(&v70, i);
          let v74 = &hv;
          let vc = rocq_array::get::<u64>(&v74, c);
          let v85 = rocq_array::set::<u64>(hk, i, kc);
          let v91 = rocq_array::set::<u64>(v85, c, ki);
          let v99 = rocq_array::set::<u64>(hv, i, vc);
          let v105 = rocq_array::set::<u64>(v99, c, vi);
          sift_down(v91, v105, sz, c, ())
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
pub fn pop(hk: Rc<Array<u64>>, hv: Rc<Array<u64>>, sz: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let sz_ = sub(sz, 1u64);
  let v11 = &hk;
  let k = rocq_array::get::<u64>(&v11, sz_);
  let v15 = &hv;
  let v = rocq_array::get::<u64>(&v15, sz_);
  let v28 = rocq_array::set::<u64>(hk, 0u64, k);
  let v37 = rocq_array::set::<u64>(hv, 0u64, v);
  sift_down_1(v28, v37, sz_, 0u64)
}

// Rocq: Shortestpath1.shortestpath1_implem.st_hk
// Variant: borrowed
pub fn st_hk(s: &Rc<St>) -> Rc<Array<u64>> {
  let v1 = s;
  Rc::clone((&(&**v1).st_hk))
}

// Rocq: Shortestpath1.shortestpath1_implem.sift_up
// Variant: uncurried
pub fn sift_up_1(hk: Rc<Array<u64>>, hv: Rc<Array<u64>>, i: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  sift_up(hk, hv, i, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.sift_up (local: sift_up)
// Variant: uncurried, lifted
pub fn sift_up(hk: Rc<Array<u64>>, hv: Rc<Array<u64>>, i: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v13 = ltb(0u64, i);
  match bdec(v13) {
    sumbool::left => {
      let p = lsr(sub(i, 1u64), 1u64);
      let v33 = &hk;
      let ki = rocq_array::get::<u64>(&v33, i);
      let v37 = &hk;
      let kp = rocq_array::get::<u64>(&v37, p);
      let v48 = ltb(ki, kp);
      match bdec(v48) {
        sumbool::left => {
          let v52 = &hv;
          let vi = rocq_array::get::<u64>(&v52, i);
          let v56 = &hv;
          let vp = rocq_array::get::<u64>(&v56, p);
          let v67 = rocq_array::set::<u64>(hk, i, kp);
          let v73 = rocq_array::set::<u64>(v67, p, ki);
          let v81 = rocq_array::set::<u64>(hv, i, vp);
          let v87 = rocq_array::set::<u64>(v81, p, vi);
          sift_up(v73, v87, p, ())
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
pub fn push(hk: Rc<Array<u64>>, hv: Rc<Array<u64>>, sz: u64, k: u64, v: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v12 = rocq_array::set::<u64>(hk, sz, k);
  let v19 = rocq_array::set::<u64>(hv, sz, v);
  sift_up_1(v12, v19, sz)
}

// Rocq: Shortestpath1.shortestpath1_implem.scan
// Variant: uncurried
pub fn scan_1(adj: Rc<Array<u64>>, wt: Rc<Array<u64>>, du: u64, hi: u64, j: u64, dist: Rc<Array<u64>>, hk: Rc<Array<u64>>, hv: Rc<Array<u64>>, sz: u64) -> Rc<St> {
  scan(adj, wt, du, hi, j, dist, hk, hv, sz, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(adj: Rc<Array<u64>>, wt: Rc<Array<u64>>, du: u64, hi: u64, j: u64, dist: Rc<Array<u64>>, hk: Rc<Array<u64>>, hv: Rc<Array<u64>>, sz: u64, _H: ()) -> Rc<St> {
  let v17 = ltb(j, hi);
  match bdec(v17) {
    sumbool::left => {
      let v21 = &adj;
      let v = rocq_array::get::<u64>(&v21, j);
      let v26 = &wt;
      let v29 = rocq_array::get::<u64>(&v26, j);
      let nd = add(du, v29);
      let v37 = &dist;
      let v40 = rocq_array::get::<u64>(&v37, v);
      let v46 = ltb(nd, v40);
      match bdec(v46) {
        sumbool::left => {
          let v61 = push(hk, hv, sz, nd, v);
          match v61 {
            (v63, v65) => {
              let v74 = add(j, 1u64);
              let v81 = rocq_array::set::<u64>(dist, v, nd);
              scan(adj, wt, du, hi, v74, v81, v63, v65, add(sz, 1u64), ())
            },
          }
        },
        sumbool::right => {
          scan(adj, wt, du, hi, add(j, 1u64), dist, hk, hv, sz, ())
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
pub fn st_dist(s: Rc<St>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&s).st_dist));
  std::mem::drop(s);
  v3
}

// Rocq: Shortestpath1.shortestpath1_implem.main
// Variant: uncurried
pub fn main_2(off: Rc<Array<u64>>, adj: Rc<Array<u64>>, wt: Rc<Array<u64>>, done: Rc<Array<u64>>, st: Rc<St>) -> Rc<Array<u64>> {
  main_1(off, adj, wt, done, st, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.main (local: main)
// Variant: uncurried, lifted
pub fn main_1(off: Rc<Array<u64>>, adj: Rc<Array<u64>>, wt: Rc<Array<u64>>, done: Rc<Array<u64>>, st: Rc<St>, _H: ()) -> Rc<Array<u64>> {
  let v19 = ltb(0u64, st_sz(&st));
  match bdec(v19) {
    sumbool::left => {
      let v26 = st_hv(&st);
      let v28 = 0u64;
      let v29 = &v26;
      let u = rocq_array::get::<u64>(&v29, v28);
      let v37 = st_hk(&st);
      let v41 = st_hv(&st);
      let v52 = pop(v37, v41, st_sz(&st));
      match v52 {
        (v54, v56) => {
          let v61 = &done;
          let v62 = rocq_array::length::<u64>(&v61);
          let v67 = ltb(u, v62);
          let v69 = &done;
          let v72 = rocq_array::get::<u64>(&v69, u);
          let v85 = andb(v67, eqb(v72, 0u64));
          match bdec(v85) {
            sumbool::left => {
              std::mem::drop(v26);
              let v93 = Rc::clone(&st);
              let v94 = st_dist(v93);
              let v95 = &v94;
              let v98 = rocq_array::get::<u64>(&v95, u);
              std::mem::drop(v94);
              let v106 = add(u, 1u64);
              let v107 = &off;
              let v110 = rocq_array::get::<u64>(&v107, v106);
              let v111 = &off;
              let v114 = rocq_array::get::<u64>(&v111, u);
              let v118 = Rc::clone(&st);
              let v119 = st_dist(v118);
              let v131 = sub(st_sz_owned(st), 1u64);
              let v134 = Rc::clone(&adj);
              let v137 = Rc::clone(&wt);
              let st2 = scan_1(v134, v137, v98, v110, v114, v119, v54, v56, v131);
              let v161 = rocq_array::set::<u64>(done, u, 1u64);
              main_1(off, adj, wt, v161, st2, ())
            },
            sumbool::right => {
              std::mem::drop(v26);
              let v183 = Rc::clone(&st);
              let v184 = st_dist(v183);
              main_1(off, adj, wt, done, Rc::new(St { st_dist: v184, st_hk: v54, st_hv: v56, st_sz: sub(st_sz_owned(st), 1u64) }), ())
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
pub fn out_loop_1(dist: Rc<Array<u64>>, n: u64, v: u64, out: Rc<Array<Rc<option<u64>>>>) -> Rc<Array<Rc<option<u64>>>> {
  out_loop(dist, n, v, out, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.out_loop (local: out_loop)
// Variant: uncurried, lifted
pub fn out_loop(dist: Rc<Array<u64>>, n: u64, v: u64, out: Rc<Array<Rc<option<u64>>>>, _H: ()) -> Rc<Array<Rc<option<u64>>>> {
  let v12 = ltb(v, n);
  match bdec(v12) {
    sumbool::left => {
      let v16 = &dist;
      let d = rocq_array::get::<u64>(&v16, v);
      let v27 = add(v, 1u64);
      let v29 = __rocq_global_253;
      let v35 = match eqb(d, v29) {
        true => {
          Rc::new(option::<u64>::None)
        },
        false => {
          Rc::new(option::<u64>::Some(d))
        },
      };
      let v55 = rocq_array::set::<Rc<option<u64>>>(out, v, v35);
      out_loop(dist, n, v27, v55, ())
    },
    sumbool::right => {
      std::mem::drop(dist);
      out
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.dijkstra_impl
// Variant: uncurried
pub fn dijkstra_impl_owned(n: u64, us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, s: u64) -> Rc<Array<Rc<option<u64>>>> {
  let v5 = &us;
  let m = rocq_array::length::<u64>(&v5);
  let v24 = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  let v27 = Rc::clone(&us);
  let c = count_loop_1(v27, m, 0u64, v24);
  let off = prefix_loop_1(n, 0u64, c);
  let v48 = &off;
  let v49 = rocq_array::copy::<u64>(&v48);
  let v56 = rocq_array::make::<u64>(m, 0u64);
  let v63 = rocq_array::make::<u64>(m, 0u64);
  let v80 = fill_loop_1(us, vs, ws, m, 0u64, v49, v56, v63);
  match v80 {
    (v82, v84) => {
      let v91 = rocq_array::make::<u64>(n, __rocq_global_253);
      let dist0 = rocq_array::set::<u64>(v91, s, 0u64);
      let hk0 = rocq_array::make::<u64>(add(m, 1u64), 0u64);
      let v130 = rocq_array::make::<u64>(add(m, 1u64), 0u64);
      let hv0 = rocq_array::set::<u64>(v130, 0u64, s);
      let v147 = rocq_array::make::<u64>(n, 0u64);
      let dist = main_2(off, v82, v84, v147, Rc::new(St { st_dist: dist0, st_hk: hk0, st_hv: hv0, st_sz: 1u64 }));
      let v182 = rocq_array::make::<Rc<option<u64>>>(n, Rc::new(option::<u64>::None));
      out_loop_1(dist, n, 0u64, v182)
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.dijkstra_impl
// Variant: borrowed, uncurried
pub fn dijkstra_impl(n: u64, us: &Rc<Array<u64>>, vs: &Rc<Array<u64>>, ws: &Rc<Array<u64>>, s: u64) -> Rc<Array<Rc<option<u64>>>> {
  let n_1 = n;
  let s_1 = s;
  let v7 = us;
  let m = rocq_array::length::<u64>(&v7);
  let v26 = rocq_array::make::<u64>(add(n_1, 1u64), 0u64);
  let v29 = Rc::clone(us);
  let c = count_loop_1(v29, m, 0u64, v26);
  let off = prefix_loop_1(n_1, 0u64, c);
  let v50 = &off;
  let v51 = rocq_array::copy::<u64>(&v50);
  let v58 = rocq_array::make::<u64>(m, 0u64);
  let v65 = rocq_array::make::<u64>(m, 0u64);
  let v68 = Rc::clone(us);
  let v71 = Rc::clone(vs);
  let v74 = Rc::clone(ws);
  let v85 = fill_loop_1(v68, v71, v74, m, 0u64, v51, v58, v65);
  match v85 {
    (v87, v89) => {
      let v96 = rocq_array::make::<u64>(n_1, __rocq_global_253);
      let dist0 = rocq_array::set::<u64>(v96, s_1, 0u64);
      let hk0 = rocq_array::make::<u64>(add(m, 1u64), 0u64);
      let v135 = rocq_array::make::<u64>(add(m, 1u64), 0u64);
      let hv0 = rocq_array::set::<u64>(v135, 0u64, s_1);
      let v152 = rocq_array::make::<u64>(n_1, 0u64);
      let dist = main_2(off, v87, v89, v152, Rc::new(St { st_dist: dist0, st_hk: hk0, st_hv: hv0, st_sz: 1u64 }));
      let v187 = rocq_array::make::<Rc<option<u64>>>(n_1, Rc::new(option::<u64>::None));
      out_loop_1(dist, n_1, 0u64, v187)
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.dijkstra_impl
pub fn dijkstra_impl_curried_owned(n: u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(u64) -> Rc<Array<Rc<option<u64>>>>>>>> {
  let v3 = {
    move |us: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(u64) -> Rc<Array<Rc<option<u64>>>>>>> {
      let n = &n;
      let v8 = Clone::clone(n);
      let v11 = {
        move |vs: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(u64) -> Rc<Array<Rc<option<u64>>>>>> {
          let n = &v8;
          let us = &us;
          let v18 = Clone::clone(n);
          let v20 = Rc::clone(us);
          let v23 = {
            move |ws: Rc<Array<u64>>| -> Rc<dyn Fn(u64) -> Rc<Array<Rc<option<u64>>>>> {
              let n = &v18;
              let us = &v20;
              let vs = &vs;
              let v32 = Clone::clone(n);
              let v34 = Rc::clone(us);
              let v36 = Rc::clone(vs);
              let v39 = {
                move |s: u64| -> Rc<Array<Rc<option<u64>>>> {
                  let v50 = Clone::clone(&v32);
                  dijkstra_impl(v50, &v34, &v36, &ws, s)
                }
              };
              let v60: Rc<dyn Fn(u64) -> Rc<Array<Rc<option<u64>>>>> = Rc::new(v39);
              v60
            }
          };
          let v64: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(u64) -> Rc<Array<Rc<option<u64>>>>>> = Rc::new(v23);
          v64
        }
      };
      let v68: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(u64) -> Rc<Array<Rc<option<u64>>>>>>> = Rc::new(v11);
      v68
    }
  };
  let v72: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(u64) -> Rc<Array<Rc<option<u64>>>>>>>> = Rc::new(v3);
  v72
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, u64) -> Rc<Array<Rc<option<u64>>>>> {
  let v0: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, u64) -> Rc<Array<Rc<option<u64>>>>> = __rocq_global_820.with(Clone::clone);
  v0
}
const __rocq_global_253: u64 = 9223372036854775807u64;
std::thread_local! { static __rocq_global_820: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, u64) -> Rc<Array<Rc<option<u64>>>>> = dijkstra(); }
std::thread_local! { static __rocq_global_823: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(u64) -> Rc<Array<Rc<option<u64>>>>>>>>> = dijkstra_curried(); }