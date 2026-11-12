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

// Rocq: Securitybadge.securitybadge_implem.securitybadge
// Variant: uncurried
pub fn securitybadge() -> Rc<dyn Fn(u64, u64, u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> {
  let v0: fn(u64, u64, u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64 = securitybadge_impl;
  let v1: Rc<dyn Fn(u64, u64, u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> = Rc::new(v0);
  v1
}

// Rocq: Securitybadge.securitybadge_implem.securitybadge
pub fn securitybadge_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>>>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>>>>> = securitybadge_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>>>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
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

// Rocq: Securitybadge.securitybadge_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Securitybadge.securitybadge_implem.mid_of
// Variant: uncurried
pub fn mid_of(m: u64, w: u64, lo: u64) -> u64 {
  let v9 = sub(m, lo);
  match ltb(w, v9) {
    true => {
      add(lo, w)
    },
    false => {
      m
    },
  }
}

// Rocq: Securitybadge.securitybadge_implem.merge
// Variant: uncurried
pub fn merge_1(src: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  merge(src, mid, hi, i, j, k, dst, ())
}

// Rocq: Securitybadge.securitybadge_implem.merge (local: merge)
// Variant: uncurried, lifted
pub fn merge(src: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v15 = ltb(i, mid);
  match bdec(v15) {
    sumbool::left => {
      let v26 = ltb(j, hi);
      match bdec(v26) {
        sumbool::left => {
          let v31 = &src;
          let v34 = rocq_array::get::<u64>(&v31, i);
          let v35 = &src;
          let v38 = rocq_array::get::<u64>(&v35, j);
          match leb(v34, v38) {
            true => {
              let v52 = add(i, 1u64);
              let v60 = add(k, 1u64);
              let v61 = &src;
              let v64 = rocq_array::get::<u64>(&v61, i);
              let v71 = rocq_array::set::<u64>(dst, k, v64);
              merge(src, mid, hi, v52, j, v60, v71, ())
            },
            false => {
              let v101 = add(j, 1u64);
              let v109 = add(k, 1u64);
              let v110 = &src;
              let v113 = rocq_array::get::<u64>(&v110, j);
              let v120 = rocq_array::set::<u64>(dst, k, v113);
              merge(src, mid, hi, i, v101, v109, v120, ())
            },
          }
        },
        sumbool::right => {
          let v153 = add(i, 1u64);
          let v161 = add(k, 1u64);
          let v162 = &src;
          let v165 = rocq_array::get::<u64>(&v162, i);
          let v172 = rocq_array::set::<u64>(dst, k, v165);
          merge(src, mid, hi, v153, j, v161, v172, ())
        },
      }
    },
    sumbool::right => {
      let v205 = ltb(j, hi);
      match bdec(v205) {
        sumbool::left => {
          let v216 = add(j, 1u64);
          let v224 = add(k, 1u64);
          let v225 = &src;
          let v228 = rocq_array::get::<u64>(&v225, j);
          let v235 = rocq_array::set::<u64>(dst, k, v228);
          merge(src, mid, hi, i, v216, v224, v235, ())
        },
        sumbool::right => {
          std::mem::drop(src);
          dst
        },
      }
    },
  }
}

// Rocq: Securitybadge.securitybadge_implem.pass
// Variant: uncurried
pub fn pass_1(src: Rc<Array<u64>>, m: u64, w: u64, lo: u64, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  pass(src, m, w, lo, dst, (), ())
}

// Rocq: Securitybadge.securitybadge_implem.pass (local: pass)
// Variant: uncurried, lifted
pub fn pass(src: Rc<Array<u64>>, m: u64, w: u64, lo: u64, dst: Rc<Array<u64>>, _Hw: (), _H: ()) -> Rc<Array<u64>> {
  let v14 = ltb(lo, m);
  match bdec(v14) {
    sumbool::left => {
      let mid = mid_of(m, w, lo);
      let hi = mid_of(m, w, mid);
      let v37 = Rc::clone(&src);
      let v50 = merge_1(v37, mid, hi, lo, mid, lo, dst);
      pass(src, m, w, hi, v50, (), ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Securitybadge.securitybadge_implem.sort_loop
// Variant: uncurried
pub fn sort_loop_1(m: u64, w: u64, src: Rc<Array<u64>>, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  sort_loop(m, w, src, dst, (), (), ())
}

// Rocq: Securitybadge.securitybadge_implem.sort_loop (local: sort_loop)
// Variant: uncurried, lifted
pub fn sort_loop(m: u64, w: u64, src: Rc<Array<u64>>, dst: Rc<Array<u64>>, _Hm: (), _Hw: (), _H: ()) -> Rc<Array<u64>> {
  let v14 = ltb(w, m);
  match bdec(v14) {
    sumbool::left => {
      let v23 = add(w, w);
      let v29 = Rc::clone(&src);
      let v38 = pass_1(v29, m, w, 0u64, dst);
      sort_loop(m, v23, v38, src, (), (), ())
    },
    sumbool::right => {
      std::mem::drop(dst);
      src
    },
  }
}

// Rocq: Securitybadge.securitybadge_implem.msort
pub fn msort(a: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v2 = &a;
  let v3 = rocq_array::length::<u64>(&v2);
  let v6 = &a;
  let v7 = rocq_array::length::<u64>(&v6);
  let v14 = rocq_array::make::<u64>(v7, 0u64);
  sort_loop_1(v3, 1u64, a, v14)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsl
// Variant: uncurried
pub fn lsl(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsl(v0, v1)
}

// Rocq: Securitybadge.securitybadge_implem.keys_loop
// Variant: uncurried
pub fn keys_loop_1(xla: Rc<Array<u64>>, L: u64, i: u64, K: Rc<Array<u64>>) -> Rc<Array<u64>> {
  keys_loop(xla, L, i, K, ())
}

// Rocq: Securitybadge.securitybadge_implem.keys_loop (local: keys_loop)
// Variant: uncurried, lifted
pub fn keys_loop(xla: Rc<Array<u64>>, L: u64, i: u64, K: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(i, L);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v26 = &xla;
      let v29 = rocq_array::get::<u64>(&v26, i);
      let v41 = add(lsl(v29, 13u64), i);
      let v48 = rocq_array::set::<u64>(K, i, v41);
      keys_loop(xla, L, v23, v48, ())
    },
    sumbool::right => {
      std::mem::drop(xla);
      K
    },
  }
}

// Rocq: Securitybadge.securitybadge_implem.src_of
pub fn src_of(key: u64) -> u64 {
  lsr(key, 13u64)
}

// Rocq: Securitybadge.securitybadge_implem.st_loop
// Variant: uncurried
pub fn st_loop_1(K: Rc<Array<u64>>, p: u64, st: Rc<Array<u64>>) -> Rc<Array<u64>> {
  st_loop(K, p, st, ())
}

// Rocq: Securitybadge.securitybadge_implem.st_loop (local: st_loop)
// Variant: uncurried, lifted
pub fn st_loop(K: Rc<Array<u64>>, p: u64, st: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v13 = ltb(0u64, p);
  match bdec(v13) {
    sumbool::left => {
      let v24 = sub(p, 1u64);
      let v33 = sub(p, 1u64);
      let v34 = &K;
      let v38 = rocq_array::get::<u64>(&v34, v33);
      let v55 = rocq_array::set::<u64>(st, src_of(v38), sub(p, 1u64));
      st_loop(K, v24, v55, ())
    },
    sumbool::right => {
      std::mem::drop(K);
      st
    },
  }
}

// Rocq: Securitybadge.securitybadge_implem.bnd_loop
// Variant: uncurried
pub fn bnd_loop_1(xlx: Rc<Array<u64>>, xly: Rc<Array<u64>>, L: u64, i: u64, B: Rc<Array<u64>>) -> Rc<Array<u64>> {
  bnd_loop(xlx, xly, L, i, B, ())
}

// Rocq: Securitybadge.securitybadge_implem.bnd_loop (local: bnd_loop)
// Variant: uncurried, lifted
pub fn bnd_loop(xlx: Rc<Array<u64>>, xly: Rc<Array<u64>>, L: u64, i: u64, B: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v13 = ltb(i, L);
  match bdec(v13) {
    sumbool::left => {
      let v24 = add(i, 1u64);
      let v31 = add(i, i);
      let v38 = add(v31, 2u64);
      let v39 = &xlx;
      let v42 = rocq_array::get::<u64>(&v39, i);
      let v49 = rocq_array::set::<u64>(B, v38, v42);
      let v56 = add(i, i);
      let v63 = add(v56, 3u64);
      let v65 = &xly;
      let v68 = rocq_array::get::<u64>(&v65, i);
      let v82 = rocq_array::set::<u64>(v49, v63, add(v68, 1u64));
      bnd_loop(xlx, xly, L, v24, v82, ())
    },
    sumbool::right => {
      std::mem::drop(xlx);
      std::mem::drop(xly);
      B
    },
  }
}

// Rocq: Securitybadge.securitybadge_implem.idx_of
pub fn idx_of(key: u64) -> u64 {
  let v10 = lsr(key, 13u64);
  sub(key, lsl(v10, 13u64))
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

// Rocq: Securitybadge.securitybadge_implem.scan
// Variant: uncurried
pub fn scan_1(K: Rc<Array<u64>>, xlb: Rc<Array<u64>>, xlx: Rc<Array<u64>>, xly: Rc<Array<u64>>, L: u64, u: u64, k: u64, stamp: u64, p: u64, vis: Rc<Array<u64>>, stk: Rc<Array<u64>>, sp: u64) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  scan(K, xlb, xlx, xly, L, u, k, stamp, p, vis, stk, sp, ())
}

// Rocq: Securitybadge.securitybadge_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(K: Rc<Array<u64>>, xlb: Rc<Array<u64>>, xlx: Rc<Array<u64>>, xly: Rc<Array<u64>>, L: u64, u: u64, k: u64, stamp: u64, p: u64, vis: Rc<Array<u64>>, stk: Rc<Array<u64>>, sp: u64, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let v20 = ltb(p, L);
  match bdec(v20) {
    sumbool::left => {
      let v24 = &K;
      let key = rocq_array::get::<u64>(&v24, p);
      let v33 = src_of(key);
      match eqb(v33, u) {
        true => {
          let i = idx_of(key);
          let v43 = &xlb;
          let v = rocq_array::get::<u64>(&v43, i);
          let v51 = &xlx;
          let v55 = rocq_array::get::<u64>(&v51, i);
          let v59 = leb(v55, k);
          let v61 = &xly;
          let v64 = rocq_array::get::<u64>(&v61, i);
          let v74 = andb(v59, leb(k, v64));
          let v77 = &vis;
          let v81 = rocq_array::get::<u64>(&v77, v);
          let v93 = andb(v74, negb(eqb(v81, stamp)));
          let v95 = &vis;
          let v96 = rocq_array::length::<u64>(&v95);
          let v101 = ltb(v, v96);
          match andb(v93, v101) {
            true => {
              let v115 = add(p, 1u64);
              let v122 = rocq_array::set::<u64>(vis, v, stamp);
              let v129 = rocq_array::set::<u64>(stk, sp, v);
              scan(K, xlb, xlx, xly, L, u, k, stamp, v115, v122, v129, add(sp, 1u64), ())
            },
            false => {
              scan(K, xlb, xlx, xly, L, u, k, stamp, add(p, 1u64), vis, stk, sp, ())
            },
          }
        },
        false => {
          std::mem::drop(K);
          std::mem::drop(xlb);
          std::mem::drop(xlx);
          std::mem::drop(xly);
          ((vis, stk), sp)
        },
      }
    },
    sumbool::right => {
      std::mem::drop(K);
      std::mem::drop(xlb);
      std::mem::drop(xlx);
      std::mem::drop(xly);
      ((vis, stk), sp)
    },
  }
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

// Rocq: Securitybadge.securitybadge_implem.dfs
// Variant: uncurried
pub fn dfs_1(K: Rc<Array<u64>>, st: Rc<Array<u64>>, xlb: Rc<Array<u64>>, xlx: Rc<Array<u64>>, xly: Rc<Array<u64>>, L: u64, k: u64, stamp: u64, vis: Rc<Array<u64>>, stk: Rc<Array<u64>>, sp: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  dfs(K, st, xlb, xlx, xly, L, k, stamp, vis, stk, sp, ())
}

// Rocq: Securitybadge.securitybadge_implem.dfs (local: dfs)
// Variant: uncurried, lifted
pub fn dfs(K: Rc<Array<u64>>, st: Rc<Array<u64>>, xlb: Rc<Array<u64>>, xlx: Rc<Array<u64>>, xly: Rc<Array<u64>>, L: u64, k: u64, stamp: u64, vis: Rc<Array<u64>>, stk: Rc<Array<u64>>, sp: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v21 = ltb(0u64, sp);
  match bdec(v21) {
    sumbool::left => {
      let v32 = sub(sp, 1u64);
      let v33 = &stk;
      let u = rocq_array::get::<u64>(&v33, v32);
      let v38 = &st;
      let v41 = rocq_array::get::<u64>(&v38, u);
      let v49 = sub(sp, 1u64);
      let v52 = Rc::clone(&K);
      let v55 = Rc::clone(&xlb);
      let v58 = Rc::clone(&xlx);
      let v61 = Rc::clone(&xly);
      let r = scan_1(v52, v55, v58, v61, L, u, k, stamp, v41, vis, stk, v49);
      let v82 = Clone::clone(&r);
      let v87 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(v82));
      let v91 = Clone::clone(&r);
      let v96 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(v91));
      dfs(K, st, xlb, xlx, xly, L, k, stamp, v87, v96, snd::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r), ())
    },
    sumbool::right => {
      std::mem::drop(K);
      std::mem::drop(st);
      std::mem::drop(xlb);
      std::mem::drop(xlx);
      std::mem::drop(xly);
      (vis, stk)
    },
  }
}

// Rocq: Securitybadge.securitybadge_implem.count_loop
// Variant: uncurried
pub fn count_loop_1(K: Rc<Array<u64>>, st: Rc<Array<u64>>, xlb: Rc<Array<u64>>, xlx: Rc<Array<u64>>, xly: Rc<Array<u64>>, S: Rc<Array<u64>>, L: u64, m: u64, s: u64, d: u64, j: u64, vis: Rc<Array<u64>>, stk: Rc<Array<u64>>, acc: u64) -> u64 {
  count_loop(K, st, xlb, xlx, xly, S, L, m, s, d, j, vis, stk, acc, ())
}

// Rocq: Securitybadge.securitybadge_implem.count_loop (local: count_loop)
// Variant: uncurried, lifted
pub fn count_loop(K: Rc<Array<u64>>, st: Rc<Array<u64>>, xlb: Rc<Array<u64>>, xlx: Rc<Array<u64>>, xly: Rc<Array<u64>>, S: Rc<Array<u64>>, L: u64, m: u64, s: u64, d: u64, j: u64, vis: Rc<Array<u64>>, stk: Rc<Array<u64>>, acc: u64, _H: ()) -> u64 {
  let v22 = ltb(j, m);
  match bdec(v22) {
    sumbool::left => {
      let v33 = sub(j, 1u64);
      let v34 = &S;
      let p = rocq_array::get::<u64>(&v34, v33);
      let v38 = &S;
      let q = rocq_array::get::<u64>(&v38, j);
      match ltb(p, q) {
        true => {
          let v56 = rocq_array::set::<u64>(vis, s, j);
          let v65 = rocq_array::set::<u64>(stk, 0u64, s);
          let v70 = Rc::clone(&K);
          let v73 = Rc::clone(&st);
          let v76 = Rc::clone(&xlb);
          let v79 = Rc::clone(&xlx);
          let v82 = Rc::clone(&xly);
          let r = dfs_1(v70, v73, v76, v79, v82, L, p, j, v56, v65, 1u64);
          let v103 = add(j, 1u64);
          let v106 = Clone::clone(&r);
          let v108 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(v106);
          let v111 = Clone::clone(&r);
          let v113 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(v111);
          let v118 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(r);
          let v119 = &v118;
          let v123 = rocq_array::get::<u64>(&v119, d);
          let v128 = match eqb(v123, j) {
            true => {
              std::mem::drop(v118);
              add(acc, sub(q, p))
            },
            false => {
              std::mem::drop(v118);
              acc
            },
          };
          count_loop(K, st, xlb, xlx, xly, S, L, m, s, d, v103, v108, v113, v128, ())
        },
        false => {
          count_loop(K, st, xlb, xlx, xly, S, L, m, s, d, add(j, 1u64), vis, stk, acc, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(K);
      std::mem::drop(st);
      std::mem::drop(xlb);
      std::mem::drop(xlx);
      std::mem::drop(xly);
      std::mem::drop(S);
      std::mem::drop(vis);
      std::mem::drop(stk);
      acc
    },
  }
}

// Rocq: Securitybadge.securitybadge_implem.securitybadge_core
// Variant: uncurried
pub fn securitybadge_core(n: u64, b: u64, s: u64, d: u64, xla: Rc<Array<u64>>, xlb: Rc<Array<u64>>, xlx: Rc<Array<u64>>, xly: Rc<Array<u64>>) -> u64 {
  let v8 = &xla;
  let L = rocq_array::length::<u64>(&v8);
  let v20 = rocq_array::make::<u64>(L, 0u64);
  let v30 = keys_loop_1(xla, L, 0u64, v20);
  let K = msort(v30);
  let v46 = rocq_array::make::<u64>(add(n, 2u64), L);
  let v49 = Rc::clone(&K);
  let st = st_loop_1(v49, L, v46);
  let v61 = add(L, L);
  let m = add(v61, 2u64);
  let v79 = rocq_array::make::<u64>(m, 0u64);
  let v90 = rocq_array::set::<u64>(v79, 0u64, 1u64);
  let v107 = rocq_array::set::<u64>(v90, 1u64, add(b, 1u64));
  let v110 = Rc::clone(&xlx);
  let v113 = Rc::clone(&xly);
  let v121 = bnd_loop_1(v110, v113, L, 0u64, v107);
  let S = msort(v121);
  let v141 = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  let v156 = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  count_loop_1(K, st, xlb, xlx, xly, S, L, m, s, d, 1u64, v141, v156, 0u64)
}

// Rocq: Securitybadge.securitybadge_implem.securitybadge_impl
// Variant: uncurried
pub fn securitybadge_impl(n: u64, b: u64, s: u64, d: u64, xla: Rc<Array<u64>>, xlb: Rc<Array<u64>>, xlx: Rc<Array<u64>>, xly: Rc<Array<u64>>) -> u64 {
  securitybadge_core(n, b, s, d, xla, xlb, xlx, xly)
}

// Rocq: Securitybadge.securitybadge_implem.securitybadge_impl
pub fn securitybadge_impl_curried(n: u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>>>>> {
  let v3 = {
    move |b: u64| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>>>> {
      let n = &n;
      let v8 = Clone::clone(n);
      let v11 = {
        move |s: u64| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>>> {
          let n = &v8;
          let b = &b;
          let v18 = Clone::clone(n);
          let v20 = Clone::clone(b);
          let v23 = {
            move |d: u64| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>> {
              let n = &v18;
              let b = &v20;
              let s = &s;
              let v32 = Clone::clone(n);
              let v34 = Clone::clone(b);
              let v36 = Clone::clone(s);
              let v39 = {
                move |xla: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>> {
                  let n = &v32;
                  let b = &v34;
                  let s = &v36;
                  let d = &d;
                  let v50 = Clone::clone(n);
                  let v52 = Clone::clone(b);
                  let v54 = Clone::clone(s);
                  let v56 = Clone::clone(d);
                  let v59 = {
                    move |xlb: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> {
                      let n = &v50;
                      let b = &v52;
                      let s = &v54;
                      let d = &v56;
                      let xla = &xla;
                      let v72 = Clone::clone(n);
                      let v74 = Clone::clone(b);
                      let v76 = Clone::clone(s);
                      let v78 = Clone::clone(d);
                      let v80 = Rc::clone(xla);
                      let v83 = {
                        move |xlx: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> u64> {
                          let n = &v72;
                          let b = &v74;
                          let s = &v76;
                          let d = &v78;
                          let xla = &v80;
                          let xlb = &xlb;
                          let v98 = Clone::clone(n);
                          let v100 = Clone::clone(b);
                          let v102 = Clone::clone(s);
                          let v104 = Clone::clone(d);
                          let v106 = Rc::clone(xla);
                          let v108 = Rc::clone(xlb);
                          let v111 = {
                            move |xly: Rc<Array<u64>>| -> u64 {
                              let v129 = Clone::clone(&v98);
                              let v131 = Clone::clone(&v100);
                              let v133 = Clone::clone(&v102);
                              let v135 = Clone::clone(&v104);
                              let v137 = Rc::clone(&v106);
                              let v139 = Rc::clone(&v108);
                              let v141 = Rc::clone(&xlx);
                              securitybadge_impl(v129, v131, v133, v135, v137, v139, v141, xly)
                            }
                          };
                          let v147: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = Rc::new(v111);
                          v147
                        }
                      };
                      let v151: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> = Rc::new(v83);
                      v151
                    }
                  };
                  let v155: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>> = Rc::new(v59);
                  v155
                }
              };
              let v159: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>> = Rc::new(v39);
              v159
            }
          };
          let v163: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>>> = Rc::new(v23);
          v163
        }
      };
      let v167: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>>>> = Rc::new(v11);
      v167
    }
  };
  let v171: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>>>>> = Rc::new(v3);
  v171
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

pub fn run() -> Rc<dyn Fn(u64, u64, u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> {
  let v0: Rc<dyn Fn(u64, u64, u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> = __rocq_global_1052.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_1052: Rc<dyn Fn(u64, u64, u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> = securitybadge(); }
std::thread_local! { static __rocq_global_1055: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>>>>>> = securitybadge_curried(); }