#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

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

pub type uint = Int63;

// Rocq: Generalchineseremainder.generalchineseremainder_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Generalchineseremainder.generalchineseremainder_implem.egcd_loop
// Variant: uncurried
pub fn egcd_loop_1(m: Int63, r0: Int63, r1: Int63, s0: Int63, s1: Int63) -> (Int63, Int63) {
  egcd_loop(m, r0, r1, s0, s1, ())
}

// Rocq: Generalchineseremainder.generalchineseremainder_implem.egcd_loop (local: egcd_loop)
// Variant: uncurried, lifted
pub fn egcd_loop(m: Int63, r0: Int63, r1: Int63, s0: Int63, s1: Int63, _H: ()) -> (Int63, Int63) {
  let tmp = r1 == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      (r0, s0)
    },
    sumbool::right => {
      let tmp_1 = r0 % r1;
      let tmp_2 = (s0 + m - r0 / r1 * s1 % m) % m;
      egcd_loop(m, r1, tmp_1, s1, tmp_2, ())
    },
  }
}

// Rocq: Generalchineseremainder.generalchineseremainder_implem.crt_impl
// Variant: uncurried
pub fn crt_impl(a_1: Int63, n: Int63, b_1: Int63, m: Int63) -> Rc<option<(Int63, Int63)>> {
  let tmp = int63!(1) % m;
  let tmp_1 = egcd_loop_1(m, n, m, tmp, int63!(0));
  match tmp_1 {
    (v27, v29) => {
      let mg = m / v27;
      let d = (b_1 + m - a_1 % m) % m;
      let tmp_2 = d % v27;
      if tmp_2 == int63!(0) {
        let t = d / v27 * v29 % mg;
        Rc::new(option::<(Int63, Int63)>::Some((a_1 + n * t, n * mg)))
      } else {
        Rc::new(option::<(Int63, Int63)>::None)
      }
    },
  }
}
