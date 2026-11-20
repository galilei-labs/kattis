#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};

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

pub type uint = Int63;

// Rocq: Candydistribution.candydistribution_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Candydistribution.candydistribution_implem.egcd_loop
// Variant: uncurried
pub fn egcd_loop_1(k: Int63, a_1: Int63, b_1: Int63, sa: Int63, sb: Int63) -> (Int63, Int63) {
  egcd_loop(k, a_1, b_1, sa, sb, ())
}

// Rocq: Candydistribution.candydistribution_implem.egcd_loop (local: egcd_loop)
// Variant: uncurried, lifted
pub fn egcd_loop(k: Int63, a_1: Int63, b_1: Int63, sa: Int63, sb: Int63, _H: ()) -> (Int63, Int63) {
  let tmp = b_1 == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      (a_1, sa)
    },
    sumbool::right => {
      let tmp_1 = a_1 % b_1;
      let tmp_2 = a_1 / b_1 * sb % k;
      let tmp_3 = (sa + (k - tmp_2)) % k;
      egcd_loop(k, b_1, tmp_1, sb, tmp_3, ())
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

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  if b1 {
    b2
  } else {
    false
  }
}

// Rocq: Candydistribution.candydistribution_implem.candy_impl
// Variant: uncurried
pub fn candy_impl(k: Int63, c: Int63) -> Rc<option<Int63>> {
  let tmp = c % k;
  let tmp_1 = int63!(1) % k;
  let p = egcd_loop_1(k, k, tmp, int63!(0), tmp_1);
  let p_clone = Clone::clone(&p);
  let g = fst::<Int63, Int63>(p_clone);
  let s = snd::<Int63, Int63>(p);
  if g == int63!(1) {
    let tmp_2 = int63!(0);
    let b1 = if s == tmp_2 {
      k
    } else {
      s
    };
    let tmp_3 = b1 == int63!(1);
    let tmp_4 = c == int63!(1);
    let b2 = if andb(tmp_3, tmp_4) {
      b1 + k
    } else {
      b1
    };
    if b2 <= int63!(1000000000) {
      Rc::new(option::<Int63>::Some(b2))
    } else {
      Rc::new(option::<Int63>::None)
    }
  } else {
    Rc::new(option::<Int63>::None)
  }
}
