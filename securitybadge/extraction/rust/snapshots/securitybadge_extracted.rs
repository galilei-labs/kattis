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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Securitybadge.securitybadge_implem.mid_of
// Variant: uncurried
pub fn mid_of(m: u64, w: u64, lo: u64) -> u64 {
  let tmp = sub(m, lo);
  if ltb(w, tmp) {
    add(lo, w)
  } else {
    m
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
  let tmp = ltb(i, mid);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = ltb(j, hi);
      match bdec(tmp_1) {
        sumbool::left => {
          let tmp_2 = rocq_array::get::<u64>(&src, i);
          let tmp_3 = rocq_array::get::<u64>(&src, j);
          if leb(tmp_2, tmp_3) {
            let tmp_4 = add(i, 1u64);
            let tmp_5 = add(k, 1u64);
            let tmp_6 = rocq_array::get::<u64>(&src, i);
            let tmp_7 = rocq_array::set::<u64>(dst, k, tmp_6);
            merge(src, mid, hi, tmp_4, j, tmp_5, tmp_7, ())
          } else {
            let tmp_8 = add(j, 1u64);
            let tmp_9 = add(k, 1u64);
            let tmp_10 = rocq_array::get::<u64>(&src, j);
            let tmp_11 = rocq_array::set::<u64>(dst, k, tmp_10);
            merge(src, mid, hi, i, tmp_8, tmp_9, tmp_11, ())
          }
        },
        sumbool::right => {
          let tmp_12 = add(i, 1u64);
          let tmp_13 = add(k, 1u64);
          let tmp_14 = rocq_array::get::<u64>(&src, i);
          let tmp_15 = rocq_array::set::<u64>(dst, k, tmp_14);
          merge(src, mid, hi, tmp_12, j, tmp_13, tmp_15, ())
        },
      }
    },
    sumbool::right => {
      let tmp_16 = ltb(j, hi);
      match bdec(tmp_16) {
        sumbool::left => {
          let tmp_17 = add(j, 1u64);
          let tmp_18 = add(k, 1u64);
          let tmp_19 = rocq_array::get::<u64>(&src, j);
          let tmp_20 = rocq_array::set::<u64>(dst, k, tmp_19);
          merge(src, mid, hi, i, tmp_17, tmp_18, tmp_20, ())
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
  let tmp = ltb(lo, m);
  match bdec(tmp) {
    sumbool::left => {
      let mid = mid_of(m, w, lo);
      let hi = mid_of(m, w, mid);
      let src_clone = Rc::clone(&src);
      let tmp_1 = merge_1(src_clone, mid, hi, lo, mid, lo, dst);
      pass(src, m, w, hi, tmp_1, (), ())
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
  let tmp = ltb(w, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(w, w);
      let src_clone = Rc::clone(&src);
      let tmp_2 = pass_1(src_clone, m, w, 0u64, dst);
      sort_loop(m, tmp_1, tmp_2, src, (), (), ())
    },
    sumbool::right => {
      std::mem::drop(dst);
      src
    },
  }
}

// Rocq: Securitybadge.securitybadge_implem.msort
pub fn msort(a: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let tmp = rocq_array::length::<u64>(&a);
  let tmp_1 = rocq_array::length::<u64>(&a);
  let tmp_2 = rocq_array::make::<u64>(tmp_1, 0u64);
  sort_loop_1(tmp, 1u64, a, tmp_2)
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
  let tmp = ltb(i, L);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&xla, i);
      let tmp_3 = add(lsl(tmp_2, 13u64), i);
      let tmp_4 = rocq_array::set::<u64>(K, i, tmp_3);
      keys_loop(xla, L, tmp_1, tmp_4, ())
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
  let tmp = ltb(0u64, p);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = sub(p, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&K, sub(p, 1u64));
      let tmp_3 = rocq_array::set::<u64>(st, src_of(tmp_2), sub(p, 1u64));
      st_loop(K, tmp_1, tmp_3, ())
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
  let tmp = ltb(i, L);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = add(i, i);
      let tmp_3 = add(tmp_2, 2u64);
      let tmp_4 = rocq_array::get::<u64>(&xlx, i);
      let tmp_5 = rocq_array::set::<u64>(B, tmp_3, tmp_4);
      let tmp_6 = add(i, i);
      let tmp_7 = add(tmp_6, 3u64);
      let tmp_8 = rocq_array::get::<u64>(&xly, i);
      let tmp_9 = rocq_array::set::<u64>(tmp_5, tmp_7, add(tmp_8, 1u64));
      bnd_loop(xlx, xly, L, tmp_1, tmp_9, ())
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
  let tmp = lsr(key, 13u64);
  sub(key, lsl(tmp, 13u64))
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
pub fn negb(b: bool) -> bool {
  if b {
    false
  } else {
    true
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
  let tmp = ltb(p, L);
  match bdec(tmp) {
    sumbool::left => {
      let key = rocq_array::get::<u64>(&K, p);
      let tmp_1 = src_of(key);
      if eqb(tmp_1, u) {
        let i = idx_of(key);
        let v = rocq_array::get::<u64>(&xlb, i);
        let tmp_2 = rocq_array::get::<u64>(&xlx, i);
        let tmp_3 = leb(tmp_2, k);
        let tmp_4 = rocq_array::get::<u64>(&xly, i);
        let tmp_5 = andb(tmp_3, leb(k, tmp_4));
        let tmp_6 = rocq_array::get::<u64>(&vis, v);
        let tmp_7 = andb(tmp_5, negb(eqb(tmp_6, stamp)));
        let tmp_8 = rocq_array::length::<u64>(&vis);
        let tmp_9 = ltb(v, tmp_8);
        if andb(tmp_7, tmp_9) {
          let tmp_10 = add(p, 1u64);
          let tmp_11 = rocq_array::set::<u64>(vis, v, stamp);
          let tmp_12 = rocq_array::set::<u64>(stk, sp, v);
          scan(K, xlb, xlx, xly, L, u, k, stamp, tmp_10, tmp_11, tmp_12, add(sp, 1u64), ())
        } else {
          scan(K, xlb, xlx, xly, L, u, k, stamp, add(p, 1u64), vis, stk, sp, ())
        }
      } else {
        std::mem::drop(K);
        std::mem::drop(xlb);
        std::mem::drop(xlx);
        std::mem::drop(xly);
        ((vis, stk), sp)
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
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Securitybadge.securitybadge_implem.dfs
// Variant: uncurried
pub fn dfs_1(K: Rc<Array<u64>>, st: Rc<Array<u64>>, xlb: Rc<Array<u64>>, xlx: Rc<Array<u64>>, xly: Rc<Array<u64>>, L: u64, k: u64, stamp: u64, vis: Rc<Array<u64>>, stk: Rc<Array<u64>>, sp: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  dfs(K, st, xlb, xlx, xly, L, k, stamp, vis, stk, sp, ())
}

// Rocq: Securitybadge.securitybadge_implem.dfs (local: dfs)
// Variant: uncurried, lifted
pub fn dfs(K: Rc<Array<u64>>, st: Rc<Array<u64>>, xlb: Rc<Array<u64>>, xlx: Rc<Array<u64>>, xly: Rc<Array<u64>>, L: u64, k: u64, stamp: u64, vis: Rc<Array<u64>>, stk: Rc<Array<u64>>, sp: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(0u64, sp);
  match bdec(tmp) {
    sumbool::left => {
      let u = rocq_array::get::<u64>(&stk, sub(sp, 1u64));
      let tmp_1 = rocq_array::get::<u64>(&st, u);
      let tmp_2 = sub(sp, 1u64);
      let K_clone = Rc::clone(&K);
      let xlb_clone = Rc::clone(&xlb);
      let xlx_clone = Rc::clone(&xlx);
      let xly_clone = Rc::clone(&xly);
      let r = scan_1(K_clone, xlb_clone, xlx_clone, xly_clone, L, u, k, stamp, tmp_1, vis, stk, tmp_2);
      let r_clone = Clone::clone(&r);
      let tmp_3 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r_clone));
      let r_clone_1 = Clone::clone(&r);
      let tmp_4 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r_clone_1));
      dfs(K, st, xlb, xlx, xly, L, k, stamp, tmp_3, tmp_4, snd::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r), ())
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
  let tmp = ltb(j, m);
  match bdec(tmp) {
    sumbool::left => {
      let p = rocq_array::get::<u64>(&S, sub(j, 1u64));
      let q = rocq_array::get::<u64>(&S, j);
      if ltb(p, q) {
        let tmp_1 = rocq_array::set::<u64>(vis, s, j);
        let tmp_2 = rocq_array::set::<u64>(stk, 0u64, s);
        let K_clone = Rc::clone(&K);
        let st_clone = Rc::clone(&st);
        let xlb_clone = Rc::clone(&xlb);
        let xlx_clone = Rc::clone(&xlx);
        let xly_clone = Rc::clone(&xly);
        let r = dfs_1(K_clone, st_clone, xlb_clone, xlx_clone, xly_clone, L, p, j, tmp_1, tmp_2, 1u64);
        let tmp_3 = add(j, 1u64);
        let r_clone = Clone::clone(&r);
        let tmp_4 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(r_clone);
        let r_clone_1 = Clone::clone(&r);
        let tmp_5 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(r_clone_1);
        let tmp_6 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(r);
        let tmp_7 = rocq_array::get::<u64>(&tmp_6, d);
        let tmp_8 = if eqb(tmp_7, j) {
          std::mem::drop(tmp_6);
          add(acc, sub(q, p))
        } else {
          std::mem::drop(tmp_6);
          acc
        };
        count_loop(K, st, xlb, xlx, xly, S, L, m, s, d, tmp_3, tmp_4, tmp_5, tmp_8, ())
      } else {
        count_loop(K, st, xlb, xlx, xly, S, L, m, s, d, add(j, 1u64), vis, stk, acc, ())
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
  let L = rocq_array::length::<u64>(&xla);
  let tmp = rocq_array::make::<u64>(L, 0u64);
  let tmp_1 = keys_loop_1(xla, L, 0u64, tmp);
  let K = msort(tmp_1);
  let tmp_2 = rocq_array::make::<u64>(add(n, 2u64), L);
  let K_clone = Rc::clone(&K);
  let st = st_loop_1(K_clone, L, tmp_2);
  let tmp_3 = add(L, L);
  let m = add(tmp_3, 2u64);
  let tmp_4 = rocq_array::make::<u64>(m, 0u64);
  let tmp_5 = rocq_array::set::<u64>(tmp_4, 0u64, 1u64);
  let tmp_6 = rocq_array::set::<u64>(tmp_5, 1u64, add(b, 1u64));
  let xlx_clone = Rc::clone(&xlx);
  let xly_clone = Rc::clone(&xly);
  let tmp_7 = bnd_loop_1(xlx_clone, xly_clone, L, 0u64, tmp_6);
  let S = msort(tmp_7);
  let tmp_8 = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  let tmp_9 = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  count_loop_1(K, st, xlb, xlx, xly, S, L, m, s, d, 1u64, tmp_8, tmp_9, 0u64)
}

// Rocq: Securitybadge.securitybadge_implem.securitybadge_impl
// Variant: uncurried
pub fn securitybadge_impl(n: u64, b: u64, s: u64, d: u64, xla: Rc<Array<u64>>, xlb: Rc<Array<u64>>, xlx: Rc<Array<u64>>, xly: Rc<Array<u64>>) -> u64 {
  securitybadge_core(n, b, s, d, xla, xlb, xlx, xly)
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
