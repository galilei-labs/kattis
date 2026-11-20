#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

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

pub struct tbl {
  pub th: Rc<big>,
  pub tn: Rc<big>,
  pub tc: Rc<big>,
  pub tk: Int63,
}

impl Clone for tbl {
  fn clone(&self) -> Self {
    match self {
      tbl { th: __field0, tn: __field1, tc: __field2, tk: __field3 } => tbl { th: Clone::clone(__field0), tn: Clone::clone(__field1), tc: Clone::clone(__field2), tk: Clone::clone(__field3) },
    }
  }
}

pub struct big {
  pub b0: Array<Int63>,
  pub b1: Array<Int63>,
  pub b2: Array<Int63>,
  pub b3: Array<Int63>,
}

impl Clone for big {
  fn clone(&self) -> Self {
    match self {
      big { b0: __field0, b1: __field1, b2: __field2, b3: __field3 } => big { b0: Clone::clone(__field0), b1: Clone::clone(__field1), b2: Clone::clone(__field2), b3: Clone::clone(__field3) },
    }
  }
}

pub type sint = Int63;

// Rocq: Sumsets.sumsets_implem.HA
pub fn HA() -> Int63 {
  int63!(2177342782468422677)
}

// Rocq: Sumsets.sumsets_implem.clen
// Variant: uncurried
pub fn clen(cap: Int63, q: Int63) -> Int63 {
  let lo = q << int63!(21);
  if cap <= lo {
    int63!(0)
  } else {
    let tmp = cap - lo;
    if tmp <= int63!(2097152) {
      cap - lo
    } else {
      int63!(2097152)
    }
  }
}

// Rocq: Sumsets.sumsets_implem.bmake
// Variant: uncurried
pub fn bmake(cap: Int63, v: Int63) -> Rc<big> {
  Rc::new(big { b0: Array::<Int63>::make(clen(cap, int63!(0)), v), b1: Array::<Int63>::make(clen(cap, int63!(1)), v), b2: Array::<Int63>::make(clen(cap, int63!(2)), v), b3: Array::<Int63>::make(clen(cap, int63!(3)), v) })
}

// Rocq: Sumsets.sumsets_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Sumsets.sumsets_implem.tk
// Variant: borrowed
pub fn tk(t: &Rc<tbl>) -> Int63 {
  let tmp = t;
  Clone::clone(&tmp.tk)
}

// Rocq: Sumsets.sumsets_implem.hash
// Variant: uncurried
pub fn hash(cap: Int63, s: Int63) -> Int63 {
  (s * __rocq_global_176 >> int63!(40)) * cap >> int63!(23)
}

// Rocq: Sumsets.sumsets_implem.b0
pub fn b0_owned(b_1: Rc<big>) -> Array<Int63> {
  let b_b0_clone = Clone::clone(&b_1.b0);
  std::mem::drop(b_1);
  b_b0_clone
}

// Rocq: Sumsets.sumsets_implem.b0
// Variant: borrowed
pub fn b0(b_1: &Rc<big>) -> Array<Int63> {
  let tmp = b_1;
  Clone::clone(&tmp.b0)
}

// Rocq: Sumsets.sumsets_implem.b1
pub fn b1_owned(b_1: Rc<big>) -> Array<Int63> {
  let b_b1_clone = Clone::clone(&b_1.b1);
  std::mem::drop(b_1);
  b_b1_clone
}

// Rocq: Sumsets.sumsets_implem.b1
// Variant: borrowed
pub fn b1(b_1: &Rc<big>) -> Array<Int63> {
  let tmp = b_1;
  Clone::clone(&tmp.b1)
}

// Rocq: Sumsets.sumsets_implem.b2
pub fn b2_owned(b_1: Rc<big>) -> Array<Int63> {
  let b_b2_clone = Clone::clone(&b_1.b2);
  std::mem::drop(b_1);
  b_b2_clone
}

// Rocq: Sumsets.sumsets_implem.b2
// Variant: borrowed
pub fn b2(b_1: &Rc<big>) -> Array<Int63> {
  let tmp = b_1;
  Clone::clone(&tmp.b2)
}

// Rocq: Sumsets.sumsets_implem.b3
pub fn b3_owned(b_1: Rc<big>) -> Array<Int63> {
  let b_b3_clone = Clone::clone(&b_1.b3);
  std::mem::drop(b_1);
  b_b3_clone
}

// Rocq: Sumsets.sumsets_implem.b3
// Variant: borrowed
pub fn b3(b_1: &Rc<big>) -> Array<Int63> {
  let tmp = b_1;
  Clone::clone(&tmp.b3)
}

// Rocq: Sumsets.sumsets_implem.chunk
// Variant: uncurried
pub fn chunk_owned(b_1: Rc<big>, q: Int63) -> Array<Int63> {
  if q == int63!(0) {
    b0_owned(b_1)
  } else {
    if q == int63!(1) {
      b1_owned(b_1)
    } else {
      if q == int63!(2) {
        b2_owned(b_1)
      } else {
        b3_owned(b_1)
      }
    }
  }
}

// Rocq: Sumsets.sumsets_implem.chunk
// Variant: borrowed, uncurried
pub fn chunk(b_1: &Rc<big>, q: Int63) -> Array<Int63> {
  let q_1 = q;
  if q_1 == int63!(0) {
    b0(b_1)
  } else {
    if q_1 == int63!(1) {
      b1(b_1)
    } else {
      if q_1 == int63!(2) {
        b2(b_1)
      } else {
        b3(b_1)
      }
    }
  }
}

// Rocq: Sumsets.sumsets_implem.bget
// Variant: uncurried
pub fn bget_owned(b_1: Rc<big>, k: Int63) -> Int63 {
  let q = k >> int63!(21);
  let tmp = chunk_owned(b_1, q);
  let tmp_1 = tmp.get_cloned(k - (q << int63!(21)));
  std::mem::drop(tmp);
  tmp_1
}

// Rocq: Sumsets.sumsets_implem.bget
// Variant: borrowed, uncurried
pub fn bget(b_1: &Rc<big>, k: Int63) -> Int63 {
  let k_1 = k;
  let q = k_1 >> int63!(21);
  let tmp = chunk(b_1, q);
  let tmp_1 = tmp.get_cloned(k_1 - (q << int63!(21)));
  std::mem::drop(tmp);
  tmp_1
}

// Rocq: Sumsets.sumsets_implem.th
pub fn th(t: Rc<tbl>) -> Rc<big> {
  let t_th_clone = Rc::clone(&t.th);
  std::mem::drop(t);
  t_th_clone
}

// Rocq: Sumsets.sumsets_implem.upd
// Variant: uncurried
pub fn upd(b_1: Rc<big>, q: Int63, a_1: Array<Int63>) -> Rc<big> {
  if q == int63!(0) {
    let b_clone = Rc::clone(&b_1);
    let tmp = b1_owned(b_clone);
    let b_clone_1 = Rc::clone(&b_1);
    Rc::new(big { b0: a_1, b1: tmp, b2: b2_owned(b_clone_1), b3: b3_owned(b_1) })
  } else {
    if q == int63!(1) {
      let b_clone_2 = Rc::clone(&b_1);
      let tmp_1 = b0_owned(b_clone_2);
      let b_clone_3 = Rc::clone(&b_1);
      Rc::new(big { b0: tmp_1, b1: a_1, b2: b2_owned(b_clone_3), b3: b3_owned(b_1) })
    } else {
      if q == int63!(2) {
        let b_clone_4 = Rc::clone(&b_1);
        let tmp_2 = b0_owned(b_clone_4);
        let b_clone_5 = Rc::clone(&b_1);
        Rc::new(big { b0: tmp_2, b1: b1_owned(b_clone_5), b2: a_1, b3: b3_owned(b_1) })
      } else {
        let b_clone_6 = Rc::clone(&b_1);
        let tmp_3 = b0_owned(b_clone_6);
        let b_clone_7 = Rc::clone(&b_1);
        Rc::new(big { b0: tmp_3, b1: b1_owned(b_clone_7), b2: b2_owned(b_1), b3: a_1 })
      }
    }
  }
}

// Rocq: Sumsets.sumsets_implem.bset
// Variant: uncurried
pub fn bset(b_1: Rc<big>, k: Int63, v: Int63) -> Rc<big> {
  let q = k >> int63!(21);
  let b_clone = Rc::clone(&b_1);
  let tmp = chunk_owned(b_clone, q);
  let tmp_1 = q << int63!(21);
  upd(b_1, q, tmp.set(k - tmp_1, v))
}

// Rocq: Sumsets.sumsets_implem.tn
pub fn tn(t: Rc<tbl>) -> Rc<big> {
  let t_tn_clone = Rc::clone(&t.tn);
  std::mem::drop(t);
  t_tn_clone
}

// Rocq: Sumsets.sumsets_implem.tc
pub fn tc(t: Rc<tbl>) -> Rc<big> {
  let t_tc_clone = Rc::clone(&t.tc);
  std::mem::drop(t);
  t_tc_clone
}

// Rocq: Sumsets.sumsets_implem.code
// Variant: uncurried
pub fn code(i: Int63, j: Int63) -> Int63 {
  (i << int63!(12)) + j
}

// Rocq: Sumsets.sumsets_implem.ins
// Variant: uncurried
pub fn ins(x: Array<Int63>, cap: Int63, i: Int63, j: Int63, T: Rc<tbl>) -> Rc<tbl> {
  let tmp = tk(&T);
  let e = tmp + int63!(1);
  let tmp_1 = x.get_cloned(i);
  let tmp_2 = x.get_cloned(j);
  std::mem::drop(x);
  let h = hash(cap, tmp_1 + tmp_2);
  let T_clone = Rc::clone(&T);
  let old = bget_owned(th(T_clone), h);
  let T_clone_1 = Rc::clone(&T);
  let nx = bset(tn(T_clone_1), e, old);
  let T_clone_2 = Rc::clone(&T);
  let cd = bset(tc(T_clone_2), e, code(i, j));
  let hd = bset(th(T), h, e);
  Rc::new(tbl { th: hd, tn: nx, tc: cd, tk: e })
}

// Rocq: Sumsets.sumsets_implem.build_in
// Variant: uncurried
pub fn build_in_1(x: Array<Int63>, cap: Int63, n: Int63, i: Int63, j: Int63, T: Rc<tbl>) -> Rc<tbl> {
  build_in(x, cap, n, i, j, T, ())
}

// Rocq: Sumsets.sumsets_implem.build_in (local: build_in)
// Variant: uncurried, lifted
pub fn build_in(x: Array<Int63>, cap: Int63, n: Int63, i: Int63, j: Int63, T: Rc<tbl>, _H: ()) -> Rc<tbl> {
  let tmp = j < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = j + int63!(1);
      let x_clone = Clone::clone(&x);
      let tmp_2 = ins(x_clone, cap, i, j, T);
      build_in(x, cap, n, i, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      T
    },
  }
}

// Rocq: Sumsets.sumsets_implem.build_out
// Variant: uncurried
pub fn build_out_1(x: Array<Int63>, cap: Int63, n: Int63, i: Int63, T: Rc<tbl>) -> Rc<tbl> {
  build_out(x, cap, n, i, T, ())
}

// Rocq: Sumsets.sumsets_implem.build_out (local: build_out)
// Variant: uncurried, lifted
pub fn build_out(x: Array<Int63>, cap: Int63, n: Int63, i: Int63, T: Rc<tbl>, _H: ()) -> Rc<tbl> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = i + int63!(1);
      let x_clone = Clone::clone(&x);
      let tmp_3 = build_in_1(x_clone, cap, n, i, tmp_2, T);
      build_out(x, cap, n, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      T
    },
  }
}

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1_1: bool, b2_1: bool) -> bool {
  if b1_1 {
    b2_1
  } else {
    false
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

// Rocq: Sumsets.sumsets_implem.chk
// Variant: uncurried
pub fn chk(x: Array<Int63>, n: Int63, k: Int63, l: Int63, t: Int63, c: Int63) -> bool {
  let i = c >> int63!(12);
  let j = c - (i << int63!(12));
  let tmp = andb(i < n, j < n);
  let tmp_1 = andb(tmp, negb(i == j));
  let tmp_2 = andb(tmp_1, negb(i == k));
  let tmp_3 = andb(tmp_2, negb(i == l));
  let tmp_4 = andb(tmp_3, negb(j == k));
  let tmp_5 = andb(tmp_4, negb(j == l));
  let tmp_6 = x.get_cloned(i);
  let tmp_7 = x.get_cloned(j);
  std::mem::drop(x);
  andb(tmp_5, tmp_6 + tmp_7 == t)
}

// Rocq: Sumsets.sumsets_implem.walk
// Variant: uncurried
pub fn walk_1(x: Array<Int63>, nx: Rc<big>, cd: Rc<big>, n: Int63, k: Int63, l: Int63, t: Int63, e: Int63) -> bool {
  walk(x, nx, cd, n, k, l, t, e, ())
}

// Rocq: Sumsets.sumsets_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(x: Array<Int63>, nx: Rc<big>, cd: Rc<big>, n: Int63, k: Int63, l: Int63, t: Int63, e: Int63, _H: ()) -> bool {
  let tmp = e == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      std::mem::drop(x);
      std::mem::drop(nx);
      std::mem::drop(cd);
      false
    },
    sumbool::right => {
      let tmp_1 = bget(&cd, e);
      let x_clone = Clone::clone(&x);
      if chk(x_clone, n, k, l, t, tmp_1) {
        std::mem::drop(x);
        std::mem::drop(nx);
        std::mem::drop(cd);
        true
      } else {
        let e_ = bget(&nx, e);
        let tmp_2 = e_ < e;
        match bdec(tmp_2) {
          sumbool::left => {
            walk(x, nx, cd, n, k, l, t, e_, ())
          },
          sumbool::right => {
            std::mem::drop(x);
            std::mem::drop(nx);
            std::mem::drop(cd);
            false
          },
        }
      }
    },
  }
}

// Rocq: Sumsets.sumsets_implem.query
// Variant: uncurried
pub fn query(x: Array<Int63>, T: Rc<tbl>, cap: Int63, n: Int63, k: Int63, l: Int63) -> bool {
  let tmp = x.get_cloned(k);
  let tmp_1 = x.get_cloned(l);
  let t = tmp - tmp_1;
  let T_clone = Rc::clone(&T);
  let e = bget_owned(th(T_clone), hash(cap, t));
  let T_clone_1 = Rc::clone(&T);
  walk_1(x, tn(T_clone_1), tc(T), n, k, l, t, e)
}

// Rocq: Sumsets.sumsets_implem.any_l
// Variant: uncurried
pub fn any_l_1(x: Array<Int63>, T: Rc<tbl>, cap: Int63, n: Int63, k: Int63, l: Int63) -> bool {
  any_l(x, T, cap, n, k, l, ())
}

// Rocq: Sumsets.sumsets_implem.any_l (local: any_l)
// Variant: uncurried, lifted
pub fn any_l(x: Array<Int63>, T: Rc<tbl>, cap: Int63, n: Int63, k: Int63, l: Int63, _H: ()) -> bool {
  let tmp = l < n;
  match bdec(tmp) {
    sumbool::left => {
      if l == k {
        any_l(x, T, cap, n, k, l + int63!(1), ())
      } else {
        let x_clone = Clone::clone(&x);
        let T_clone = Rc::clone(&T);
        if query(x_clone, T_clone, cap, n, k, l) {
          std::mem::drop(x);
          std::mem::drop(T);
          true
        } else {
          any_l(x, T, cap, n, k, l + int63!(1), ())
        }
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(T);
      false
    },
  }
}

// Rocq: Sumsets.sumsets_implem.best_k
// Variant: uncurried
pub fn best_k_1(x: Array<Int63>, T: Rc<tbl>, cap: Int63, n: Int63, k: Int63, found: bool, best: Int63) -> Rc<option<Int63>> {
  best_k(x, T, cap, n, k, found, best, ())
}

// Rocq: Sumsets.sumsets_implem.best_k (local: best_k)
// Variant: uncurried, lifted
pub fn best_k(x: Array<Int63>, T: Rc<tbl>, cap: Int63, n: Int63, k: Int63, found: bool, best: Int63, _H: ()) -> Rc<option<Int63>> {
  let tmp = k < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = x.get_cloned(k);
      let tmp_2 = tmp_1.lesb(best);
      if andb(found, tmp_2) {
        best_k(x, T, cap, n, k + int63!(1), found, best, ())
      } else {
        let x_clone = Clone::clone(&x);
        let T_clone = Rc::clone(&T);
        if any_l_1(x_clone, T_clone, cap, n, k, int63!(0)) {
          let tmp_3 = k + int63!(1);
          let tmp_4 = x.get_cloned(k);
          best_k(x, T, cap, n, tmp_3, true, tmp_4, ())
        } else {
          best_k(x, T, cap, n, k + int63!(1), found, best, ())
        }
      }
    },
    sumbool::right => {
      if found {
        std::mem::drop(x);
        std::mem::drop(T);
        Rc::new(option::<Int63>::Some(best))
      } else {
        std::mem::drop(x);
        std::mem::drop(T);
        Rc::new(option::<Int63>::None)
      }
    },
  }
}

// Rocq: Sumsets.sumsets_implem.sumsets_impl
pub fn sumsets_impl(x: Array<Int63>) -> Rc<option<Int63>> {
  let n = x.length();
  let tmp = n - int63!(1);
  let cap = (n * tmp >> int63!(1)) + int63!(1);
  let T0 = Rc::new(tbl { th: bmake(cap, int63!(0)), tn: bmake(cap, int63!(0)), tc: bmake(cap, int63!(0)), tk: int63!(0) });
  let x_clone = Clone::clone(&x);
  let T = build_out_1(x_clone, cap, n, int63!(0), T0);
  best_k_1(x, T, cap, n, int63!(0), false, int63!(0))
}
const __rocq_global_176: Int63 = int63!(2177342782468422677);