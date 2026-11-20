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

pub enum token<A: 'static> {
  Open,
  Close,
  Num(A),
}

impl<A: Clone + 'static> Clone for token<A> {
  fn clone(&self) -> Self {
    match self {
      token::Open => token::Open,
      token::Close => token::Close,
      token::Num(__field0) => token::Num(Clone::clone(__field0)),
    }
  }
}

pub type uint = Int63;

// Rocq: Bracketsequence.bracketsequence_implem.Mi
pub fn Mi() -> Int63 {
  int63!(1000000007)
}

// Rocq: Bracketsequence.bracketsequence_implem.bdec
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

// Rocq: Bracketsequence.bracketsequence_implem.idm
pub fn idm(add: bool) -> Int63 {
  if add {
    int63!(0)
  } else {
    int63!(1)
  }
}

// Rocq: Bracketsequence.bracketsequence_implem.opm
// Variant: uncurried
pub fn opm(add: bool, a_1: Int63, v: Int63) -> Int63 {
  if add {
    (a_1 + v) % __rocq_global_92
  } else {
    a_1 * v % __rocq_global_92
  }
}

// Rocq: Bracketsequence.bracketsequence_implem.loop
// Variant: uncurried
pub fn loop__1(x: Array<Rc<token<Int63>>>, n: Int63, i: Int63, d: Int63, add: bool, stk: Array<Int63>) -> Int63 {
  loop_(x, n, i, d, add, stk, ())
}

// Rocq: Bracketsequence.bracketsequence_implem.loop (local: loop)
// Variant: uncurried, lifted
pub fn loop_(x: Array<Rc<token<Int63>>>, n: Int63, i: Int63, d: Int63, add: bool, stk: Array<Int63>, _H: ()) -> Int63 {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = x.get_cloned(i);
      let (v22, v23) = __rocq_reuse::reset(tmp_1, |__payload| Clone::clone(__payload));
      std::mem::drop(v23);
      match v22 {
        token::Open => {
          loop_(x, n, i + int63!(1), d + int63!(1), negb(add), stk.set(d + int63!(1), idm(negb(add))), ())
        },
        token::Close => {
          if d == int63!(0) {
            loop_(x, n, i + int63!(1), d, add, stk, ())
          } else {
            let tmp_2 = i + int63!(1);
            let tmp_3 = d - int63!(1);
            let tmp_4 = negb(add);
            let tmp_5 = d - int63!(1);
            let tmp_6 = negb(add);
            let tmp_7 = stk.get_cloned(d - int63!(1));
            let tmp_8 = stk.get_cloned(d);
            loop_(x, n, tmp_2, tmp_3, tmp_4, stk.set(tmp_5, opm(tmp_6, tmp_7, tmp_8)), ())
          }
        },
        token::Num(v214) => {
          let tmp_9 = i + int63!(1);
          let tmp_10 = stk.get_cloned(d);
          let tmp_11 = stk.set(d, opm(add, tmp_10, v214));
          loop_(x, n, tmp_9, d, add, tmp_11, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      let tmp_12 = stk.get_cloned(d);
      std::mem::drop(stk);
      tmp_12
    },
  }
}

// Rocq: Bracketsequence.bracketsequence_implem.bracketsequence_impl
pub fn bracketsequence_impl(x: Array<Rc<token<Int63>>>) -> Int63 {
  let n = x.length();
  let tmp = n + int63!(1);
  loop__1(x, n, int63!(0), int63!(0), true, Array::<Int63>::make(tmp, int63!(0)))
}
const __rocq_global_92: Int63 = int63!(1000000007);