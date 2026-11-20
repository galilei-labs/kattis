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

pub enum literal<A: 'static> {
  X(A),
  NotX(A),
}

impl<A: Clone + 'static> Clone for literal<A> {
  fn clone(&self) -> Self {
    match self {
      literal::X(__field0) => literal::X(Clone::clone(__field0)),
      literal::NotX(__field0) => literal::NotX(Clone::clone(__field0)),
    }
  }
}

pub type uint = Int63;

// Rocq: Satisfiability.satisfiability_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
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

// Rocq: Satisfiability.satisfiability_implem.clause_ok
// Variant: uncurried
pub fn clause_ok(t: Int63, p: Int63, q: Int63) -> bool {
  let tmp = p & t;
  if tmp == int63!(0) {
    negb(q & t == q)
  } else {
    true
  }
}

// Rocq: Satisfiability.satisfiability_implem.check_loop
// Variant: uncurried
pub fn check_loop_1(pos: Array<Int63>, neg: Array<Int63>, m: Int63, k: Int63, t: Int63) -> bool {
  check_loop(pos, neg, m, k, t, ())
}

// Rocq: Satisfiability.satisfiability_implem.check_loop (local: check_loop)
// Variant: uncurried, lifted
pub fn check_loop(pos: Array<Int63>, neg: Array<Int63>, m: Int63, k: Int63, t: Int63, _H: ()) -> bool {
  let tmp = k < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = pos.get_cloned(k);
      let tmp_2 = neg.get_cloned(k);
      if clause_ok(t, tmp_1, tmp_2) {
        check_loop(pos, neg, m, k + int63!(1), t, ())
      } else {
        std::mem::drop(pos);
        std::mem::drop(neg);
        false
      }
    },
    sumbool::right => {
      std::mem::drop(pos);
      std::mem::drop(neg);
      true
    },
  }
}

// Rocq: Satisfiability.satisfiability_implem.check_all
// Variant: uncurried
pub fn check_all(pos: Array<Int63>, neg: Array<Int63>, m: Int63, t: Int63) -> bool {
  check_loop_1(pos, neg, m, int63!(0), t)
}

// Rocq: Satisfiability.satisfiability_implem.search_loop
// Variant: uncurried
pub fn search_loop_1(pos: Array<Int63>, neg: Array<Int63>, m: Int63, lim: Int63, t: Int63) -> bool {
  search_loop(pos, neg, m, lim, t, ())
}

// Rocq: Satisfiability.satisfiability_implem.search_loop (local: search_loop)
// Variant: uncurried, lifted
pub fn search_loop(pos: Array<Int63>, neg: Array<Int63>, m: Int63, lim: Int63, t: Int63, _H: ()) -> bool {
  let tmp = t < lim;
  match bdec(tmp) {
    sumbool::left => {
      let pos_clone = Clone::clone(&pos);
      let neg_clone = Clone::clone(&neg);
      if check_all(pos_clone, neg_clone, m, t) {
        std::mem::drop(pos);
        std::mem::drop(neg);
        true
      } else {
        search_loop(pos, neg, m, lim, t + int63!(1), ())
      }
    },
    sumbool::right => {
      std::mem::drop(pos);
      std::mem::drop(neg);
      false
    },
  }
}

// Rocq: Satisfiability.satisfiability_implem.bitof
pub fn bitof(v: Int63) -> Int63 {
  int63!(1) << v - int63!(1)
}

// Rocq: Satisfiability.satisfiability_implem.lit_bits
// Variant: uncurried
pub fn lit_bits(s: bool, l: Rc<literal<Int63>>) -> Int63 {
  let (v2, v3) = __rocq_reuse::reset(l, |__payload| Clone::clone(__payload));
  std::mem::drop(v3);
  match v2 {
    literal::X(v9) => {
      if s {
        bitof(v9)
      } else {
        int63!(0)
      }
    },
    literal::NotX(v25) => {
      if s {
        int63!(0)
      } else {
        bitof(v25)
      }
    },
  }
}

// Rocq: Satisfiability.satisfiability_implem.mask_loop
// Variant: uncurried
pub fn mask_loop_1(s: bool, c: Array<Rc<literal<Int63>>>, len: Int63, i: Int63, acc: Int63) -> Int63 {
  mask_loop(s, c, len, i, acc, ())
}

// Rocq: Satisfiability.satisfiability_implem.mask_loop (local: mask_loop)
// Variant: uncurried, lifted
pub fn mask_loop(s: bool, c: Array<Rc<literal<Int63>>>, len: Int63, i: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = i < len;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = c.get_cloned(i);
      let tmp_3 = lit_bits(s, tmp_2);
      mask_loop(s, c, len, tmp_1, acc | tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(c);
      acc
    },
  }
}

// Rocq: Satisfiability.satisfiability_implem.clause_mask
// Variant: uncurried
pub fn clause_mask(s: bool, c: Array<Rc<literal<Int63>>>) -> Int63 {
  let tmp = c.length();
  mask_loop_1(s, c, tmp, int63!(0), int63!(0))
}

// Rocq: Satisfiability.satisfiability_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(s: bool, y: Array<Array<Rc<literal<Int63>>>>, m: Int63, k: Int63, r: Array<Int63>) -> Array<Int63> {
  fill_loop(s, y, m, k, r, ())
}

// Rocq: Satisfiability.satisfiability_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(s: bool, y: Array<Array<Rc<literal<Int63>>>>, m: Int63, k: Int63, r: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = k < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = k + int63!(1);
      let y_clone = Clone::clone(&y);
      let tmp_2 = &y_clone;
      let tmp_3 = tmp_2.get_cloned(k);
      std::mem::drop(y_clone);
      let tmp_4 = clause_mask(s, tmp_3);
      fill_loop(s, y, m, tmp_1, r.set(k, tmp_4), ())
    },
    sumbool::right => {
      std::mem::drop(y);
      r
    },
  }
}

// Rocq: Satisfiability.satisfiability_implem.masks
// Variant: uncurried
pub fn masks(s: bool, y: Array<Array<Rc<literal<Int63>>>>) -> Array<Int63> {
  let tmp = y.length();
  let tmp_1 = y.length();
  fill_loop_1(s, y, tmp, int63!(0), Array::<Int63>::make(tmp_1, int63!(0)))
}

// Rocq: Satisfiability.satisfiability_implem.satisfiable_impl
// Variant: uncurried
pub fn satisfiable_impl(n: Int63, y: Array<Array<Rc<literal<Int63>>>>) -> bool {
  let m = y.length();
  let lim = int63!(1) << n;
  let y_clone = Clone::clone(&y);
  search_loop_1(masks(true, y_clone), masks(false, y), m, lim, int63!(0))
}
