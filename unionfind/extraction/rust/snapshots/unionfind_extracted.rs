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

pub type uint = Int63;

// Rocq: Unionfind.unionfind_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Unionfind.unionfind_implem.count_queries
// Variant: uncurried
pub fn count_queries_1(xu: Array<bool>, q: Int63, k: Int63, c: Int63) -> Int63 {
  count_queries(xu, q, k, c, ())
}

// Rocq: Unionfind.unionfind_implem.count_queries (local: count_queries)
// Variant: uncurried, lifted
pub fn count_queries(xu: Array<bool>, q: Int63, k: Int63, c: Int63, _H: ()) -> Int63 {
  let tmp = k < q;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = k + int63!(1);
      let tmp_2 = xu.get_cloned(k);
      let tmp_3 = if tmp_2 {
        c
      } else {
        c + int63!(1)
      };
      count_queries(xu, q, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(xu);
      c
    },
  }
}

// Rocq: Unionfind.unionfind_implem.pack_queries
// Variant: uncurried
pub fn pack_queries_1(xu: Array<bool>, raw: Array<bool>, q: Int63, k: Int63, c: Int63, out: Array<bool>) -> Array<bool> {
  pack_queries(xu, raw, q, k, c, out, ())
}

// Rocq: Unionfind.unionfind_implem.pack_queries (local: pack_queries)
// Variant: uncurried, lifted
pub fn pack_queries(xu: Array<bool>, raw: Array<bool>, q: Int63, k: Int63, c: Int63, out: Array<bool>, _H: ()) -> Array<bool> {
  let tmp = k < q;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = xu.get_cloned(k);
      if tmp_1 {
        pack_queries(xu, raw, q, k + int63!(1), c, out, ())
      } else {
        let tmp_2 = k + int63!(1);
        let tmp_3 = c + int63!(1);
        let tmp_4 = raw.get_cloned(k);
        pack_queries(xu, raw, q, tmp_2, tmp_3, out.set(c, tmp_4), ())
      }
    },
    sumbool::right => {
      std::mem::drop(xu);
      std::mem::drop(raw);
      out
    },
  }
}

// Rocq: Unionfind.unionfind_implem.compact_queries
// Variant: uncurried
pub fn compact_queries(xu: Array<bool>, raw: Array<bool>) -> Array<bool> {
  let q = xu.length();
  let xu_clone = Clone::clone(&xu);
  let count = count_queries_1(xu_clone, q, int63!(0), int63!(0));
  pack_queries_1(xu, raw, q, int63!(0), int63!(0), Array::<bool>::make(count, false))
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

// Rocq: Unionfind.unionfind_implem.find
// Variant: uncurried
pub fn find_1(par: Array<Int63>, x: Int63) -> (Int63, Array<Int63>) {
  find(par, x, ())
}

// Rocq: Unionfind.unionfind_implem.find (local: find)
// Variant: uncurried, lifted
pub fn find(par: Array<Int63>, x: Int63, _H: ()) -> (Int63, Array<Int63>) {
  let p = par.get_cloned(x);
  let tmp = p == x;
  match bdec(tmp) {
    sumbool::left => {
      (x, par)
    },
    sumbool::right => {
      let rp = find(par, p, ());
      let rp_clone = Clone::clone(&rp);
      let tmp_1 = fst::<Int63, Array<Int63>>(rp_clone);
      let rp_clone_1 = Clone::clone(&rp);
      (tmp_1, snd::<Int63, Array<Int63>>(rp_clone_1).set(x, fst::<Int63, Array<Int63>>(rp)))
    },
  }
}

// Rocq: Unionfind.unionfind_implem.link
// Variant: uncurried
pub fn link(par: Array<Int63>, rk: Array<Int63>, ra: Int63, rb: Int63) -> (Array<Int63>, Array<Int63>) {
  if ra == rb {
    (par, rk)
  } else {
    let ka = rk.get_cloned(ra);
    let kb = rk.get_cloned(rb);
    if ka < kb {
      (par.set(ra, rb), rk)
    } else {
      if kb < ka {
        (par.set(rb, ra), rk)
      } else {
        (par.set(ra, rb), rk.set(rb, kb + int63!(1)))
      }
    }
  }
}

// Rocq: Unionfind.unionfind_implem.scan
// Variant: uncurried
pub fn scan_1(xu: Array<bool>, xa: Array<Int63>, xb: Array<Int63>, q: Int63, k: Int63, par: Array<Int63>, rk: Array<Int63>, out: Array<bool>) -> Array<bool> {
  scan(xu, xa, xb, q, k, par, rk, out, (), ())
}

// Rocq: Unionfind.unionfind_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(xu: Array<bool>, xa: Array<Int63>, xb: Array<Int63>, q: Int63, k: Int63, par: Array<Int63>, rk: Array<Int63>, out: Array<bool>, _W: (), _H: ()) -> Array<bool> {
  let tmp = k < q;
  match bdec(tmp) {
    sumbool::left => {
      let a_1 = xa.get_cloned(k);
      let b_1 = xb.get_cloned(k);
      let fa = find_1(par, a_1);
      let fa_clone = Clone::clone(&fa);
      let fb = find_1(snd::<Int63, Array<Int63>>(fa_clone), b_1);
      let tmp_1 = xu.get_cloned(k);
      if tmp_1 {
        let fb_clone = Clone::clone(&fb);
        let l = link(snd::<Int63, Array<Int63>>(fb_clone), rk, fst::<Int63, Array<Int63>>(fa), fst::<Int63, Array<Int63>>(fb));
        let tmp_2 = k + int63!(1);
        let l_clone = Clone::clone(&l);
        scan(xu, xa, xb, q, tmp_2, fst::<Array<Int63>, Array<Int63>>(l_clone), snd::<Array<Int63>, Array<Int63>>(l), out, (), ())
      } else {
        let tmp_3 = k + int63!(1);
        let fb_clone_1 = Clone::clone(&fb);
        scan(xu, xa, xb, q, tmp_3, snd::<Int63, Array<Int63>>(fb_clone_1), rk, out.set(k, fst::<Int63, Array<Int63>>(fa) == fst::<Int63, Array<Int63>>(fb)), (), ())
      }
    },
    sumbool::right => {
      std::mem::drop(xu);
      std::mem::drop(xa);
      std::mem::drop(xb);
      std::mem::drop(par);
      std::mem::drop(rk);
      out
    },
  }
}

// Rocq: Unionfind.unionfind_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(n: Int63, i: Int63, p: Array<Int63>) -> Array<Int63> {
  init_loop(n, i, p, ())
}

// Rocq: Unionfind.unionfind_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(n: Int63, i: Int63, p: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      init_loop(n, i + int63!(1), p.set(i, i), ())
    },
    sumbool::right => {
      p
    },
  }
}

// Rocq: Unionfind.unionfind_implem.init_par
pub fn init_par(n: Int63) -> Array<Int63> {
  let tmp = Array::<Int63>::make(n, int63!(0));
  init_loop_1(n, int63!(0), tmp)
}

// Rocq: Unionfind.unionfind_implem.run_ops_raw
// Variant: uncurried
pub fn run_ops_raw(xn: Int63, xu: Array<bool>, xa: Array<Int63>, xb: Array<Int63>) -> Array<bool> {
  let q = xu.length();
  let tmp = init_par(xn);
  let tmp_1 = Array::<Int63>::make(xn, int63!(0));
  let tmp_2 = Array::<bool>::make(q, false);
  scan_1(xu, xa, xb, q, int63!(0), tmp, tmp_1, tmp_2)
}

// Rocq: Unionfind.unionfind_implem.run_ops_impl
// Variant: uncurried
pub fn run_ops_impl(xn: Int63, xu: Array<bool>, xa: Array<Int63>, xb: Array<Int63>) -> Array<bool> {
  let xu_clone = Clone::clone(&xu);
  compact_queries(xu, run_ops_raw(xn, xu_clone, xa, xb))
}
