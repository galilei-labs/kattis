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

// Rocq: Joinstrings.joinstrings_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Joinstrings.joinstrings_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(n: Int63, k: Int63, tl: Array<Int63>) -> Array<Int63> {
  init_loop(n, k, tl, ())
}

// Rocq: Joinstrings.joinstrings_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(n: Int63, k: Int63, tl: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = k < n;
  match bdec(tmp) {
    sumbool::left => {
      init_loop(n, k + int63!(1), tl.set(k, k), ())
    },
    sumbool::right => {
      tl
    },
  }
}

// Rocq: Joinstrings.joinstrings_implem.ops_loop
// Variant: uncurried
pub fn ops_loop_1(xa: Array<Int63>, xb: Array<Int63>, m: Int63, k: Int63, nx: Array<Int63>, tl: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  ops_loop(xa, xb, m, k, nx, tl, ())
}

// Rocq: Joinstrings.joinstrings_implem.ops_loop (local: ops_loop)
// Variant: uncurried, lifted
pub fn ops_loop(xa: Array<Int63>, xb: Array<Int63>, m: Int63, k: Int63, nx: Array<Int63>, tl: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = k < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = xa.get_cloned(k);
      let x = tmp_1 - int63!(1);
      let tmp_2 = xb.get_cloned(k);
      let y = tmp_2 - int63!(1);
      let ty = tl.get_cloned(y);
      let tx = tl.get_cloned(x);
      ops_loop(xa, xb, m, k + int63!(1), nx.set(tx, y), tl.set(x, ty), ())
    },
    sumbool::right => {
      std::mem::drop(xa);
      std::mem::drop(xb);
      (nx, tl)
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

// Rocq: Joinstrings.joinstrings_implem.root_of
// Variant: uncurried
pub fn root_of(xa: Array<Int63>, m: Int63) -> Int63 {
  if m == int63!(0) {
    std::mem::drop(xa);
    int63!(0)
  } else {
    let tmp = xa.get_cloned(m - int63!(1));
    std::mem::drop(xa);
    tmp - int63!(1)
  }
}

// Rocq: Joinstrings.joinstrings_implem.walk
// Variant: uncurried
pub fn walk_1(nx: Array<Int63>, t: Int63, n: Int63, cur: Int63, i: Int63, ord: Array<Int63>) -> (Array<Int63>, Int63) {
  walk(nx, t, n, cur, i, ord, ())
}

// Rocq: Joinstrings.joinstrings_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(nx: Array<Int63>, t: Int63, n: Int63, cur: Int63, i: Int63, ord: Array<Int63>, _H: ()) -> (Array<Int63>, Int63) {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      if cur == t {
        std::mem::drop(nx);
        (ord.set(i, cur), i + int63!(1))
      } else {
        let tmp_1 = nx.get_cloned(cur);
        walk(nx, t, n, tmp_1, i + int63!(1), ord.set(i, cur), ())
      }
    },
    sumbool::right => {
      std::mem::drop(nx);
      (ord, i)
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

// Rocq: Joinstrings.joinstrings_implem.split_ok
// Variant: uncurried
pub fn split_ok(lo: Int63, hi: Int63) -> bool {
  andb(lo < hi, int63!(1) < hi - lo)
}

// Rocq: Corelib.Strings.PrimString.cat
// Variant: uncurried
pub fn cat(v0: rocq_string::RocqString, v1: rocq_string::RocqString) -> rocq_string::RocqString {
  let tmp = &v0;
  let tmp_1 = &v1;
  let tmp_2 = tmp.cat(tmp_1);
  std::mem::drop(v1);
  std::mem::drop(v0);
  tmp_2
}

// Rocq: Joinstrings.joinstrings_implem.mid_of
// Variant: uncurried
pub fn mid_of(lo: Int63, hi: Int63) -> Int63 {
  let tmp = hi - lo;
  lo + tmp / int63!(2)
}

// Rocq: Joinstrings.joinstrings_implem.build
// Variant: uncurried
pub fn build_1(xs: Array<rocq_string::RocqString>, ord: Array<Int63>, lo: Int63, hi: Int63) -> rocq_string::RocqString {
  build(xs, ord, lo, hi, ())
}

// Rocq: Joinstrings.joinstrings_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(xs: Array<rocq_string::RocqString>, ord: Array<Int63>, lo: Int63, hi: Int63, _H: ()) -> rocq_string::RocqString {
  let tmp = split_ok(lo, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = mid_of(lo, hi);
      let xs_clone = Clone::clone(&xs);
      let ord_clone = Clone::clone(&ord);
      cat(build(xs_clone, ord_clone, lo, tmp_1, ()), build(xs, ord, mid_of(lo, hi), hi, ()))
    },
    sumbool::right => {
      let tmp_2 = ord.get_cloned(lo);
      std::mem::drop(ord);
      let xs_ref = &xs;
      let tmp_3 = xs_ref.get_cloned(tmp_2);
      std::mem::drop(xs);
      tmp_3
    },
  }
}

// Rocq: Joinstrings.joinstrings_implem.joinstrings_impl
// Variant: uncurried
pub fn joinstrings_impl(xs: Array<rocq_string::RocqString>, xa: Array<Int63>, xb: Array<Int63>) -> rocq_string::RocqString {
  let n = xs.length();
  let m = xa.length();
  let tmp = Array::<Int63>::make(n, int63!(0));
  let tl0 = init_loop_1(n, int63!(0), tmp);
  let tmp_1 = Array::<Int63>::make(n, int63!(0));
  let xa_clone = Clone::clone(&xa);
  let nt = ops_loop_1(xa_clone, xb, m, int63!(0), tmp_1, tl0);
  let nt_clone = Clone::clone(&nt);
  let nx = fst::<Array<Int63>, Array<Int63>>(nt_clone);
  let tl = snd::<Array<Int63>, Array<Int63>>(nt);
  let r = root_of(xa, m);
  let tmp_2 = tl.get_cloned(r);
  std::mem::drop(tl);
  let tmp_3 = Array::<Int63>::make(n, int63!(0));
  let oc = walk_1(nx, tmp_2, n, r, int63!(0), tmp_3);
  let oc_clone = Clone::clone(&oc);
  build_1(xs, fst::<Array<Int63>, Int63>(oc_clone), int63!(0), snd::<Array<Int63>, Int63>(oc))
}
