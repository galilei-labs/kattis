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

// Rocq: Bitwise.bitwise_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Bitwise.bitwise_implem.init_ptr
// Variant: uncurried
pub fn init_ptr_1(m: Int63, x: Int63, P: Array<Int63>) -> Array<Int63> {
  init_ptr(m, x, P, ())
}

// Rocq: Bitwise.bitwise_implem.init_ptr (local: init_ptr)
// Variant: uncurried, lifted
pub fn init_ptr(m: Int63, x: Int63, P: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = x < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = x + int63!(1);
      let tmp_2 = x + int63!(1);
      init_ptr(m, tmp_1, P.set(x, tmp_2), ())
    },
    sumbool::right => {
      P
    },
  }
}

// Rocq: Bitwise.bitwise_implem.hasbit
// Variant: uncurried
pub fn hasbit(v: Int63, b_1: Int63) -> bool {
  v >> b_1 & int63!(1) == int63!(1)
}

// Rocq: Bitwise.bitwise_implem.cell
// Variant: uncurried
pub fn cell(a_1: Array<Int63>, n: Int63, x: Int63) -> Int63 {
  if x < n {
    let tmp = a_1.get_cloned(x);
    std::mem::drop(a_1);
    tmp
  } else {
    let tmp_1 = a_1.get_cloned(x - n);
    std::mem::drop(a_1);
    tmp_1
  }
}

// Rocq: Bitwise.bitwise_implem.scan
// Variant: uncurried
pub fn scan_1(a_1: Array<Int63>, P: Array<Int63>, n: Int63, b_1: Int63, i: Int63, nb: Int63, Q: Array<Int63>) -> Array<Int63> {
  scan(a_1, P, n, b_1, i, nb, Q, ())
}

// Rocq: Bitwise.bitwise_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(a_1: Array<Int63>, P: Array<Int63>, n: Int63, b_1: Int63, i: Int63, nb: Int63, Q: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = int63!(0) < i;
  match bdec(tmp) {
    sumbool::left => {
      let x = i - int63!(1);
      let a_clone = Clone::clone(&a_1);
      let tmp_1 = cell(a_clone, n, x);
      let nb_ = if hasbit(tmp_1, b_1) {
        i
      } else {
        nb
      };
      let p = P.get_cloned(x);
      let tmp_2 = if p < nb_ {
        nb_
      } else {
        p
      };
      let tmp_3 = Q.set(x, tmp_2);
      scan(a_1, P, n, b_1, x, nb_, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(a_1);
      std::mem::drop(P);
      Q
    },
  }
}

// Rocq: Bitwise.bitwise_implem.newptr
// Variant: uncurried
pub fn newptr(a_1: Array<Int63>, P: Array<Int63>, Q: Array<Int63>, n: Int63, b_1: Int63) -> Array<Int63> {
  let n2 = int63!(2) * n;
  let tmp = n2 + int63!(1);
  let tmp_1 = n2 + int63!(1);
  let tmp_2 = Q.set(n2, tmp_1);
  let tmp_3 = n2 + int63!(1);
  let tmp_4 = n2 + int63!(1);
  scan_1(a_1, P, n, b_1, n2, tmp, tmp_2.set(tmp_3, tmp_4))
}

// Rocq: Bitwise.bitwise_implem.init
// Variant: uncurried
pub fn init_1(L: Int63, j: Int63, V: Array<Int63>, S: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  init(L, j, V, S, ())
}

// Rocq: Bitwise.bitwise_implem.init (local: init)
// Variant: uncurried, lifted
pub fn init(L: Int63, j: Int63, V: Array<Int63>, S: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = j < L;
  match bdec(tmp) {
    sumbool::left => {
      init(L, j + int63!(1), V.set(j, j), S.set(j, j), ())
    },
    sumbool::right => {
      (V, S)
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

// Rocq: Bitwise.bitwise_implem.dedup
// Variant: uncurried
pub fn dedup_1(Q: Array<Int63>, V: Array<Int63>, S: Array<Int63>, w: Int63, i: Int63, w_: Int63, V_: Array<Int63>, S_: Array<Int63>) -> ((Int63, Array<Int63>), Array<Int63>) {
  dedup(Q, V, S, w, i, w_, V_, S_, ())
}

// Rocq: Bitwise.bitwise_implem.dedup (local: dedup)
// Variant: uncurried, lifted
pub fn dedup(Q: Array<Int63>, V: Array<Int63>, S: Array<Int63>, w: Int63, i: Int63, w_: Int63, V_: Array<Int63>, S_: Array<Int63>, _H: ()) -> ((Int63, Array<Int63>), Array<Int63>) {
  let tmp = i < w;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = V.get_cloned(i);
      let v = Q.get_cloned(tmp_1);
      let s = S.get_cloned(i);
      let tmp_2 = int63!(0) < w_;
      let tmp_3 = V_.get_cloned(w_ - int63!(1));
      let tmp_4 = tmp_3 == v;
      if andb(tmp_2, tmp_4) {
        let tmp_5 = i + int63!(1);
        let tmp_6 = w_ - int63!(1);
        dedup(Q, V, S, w, tmp_5, w_, V_, S_.set(tmp_6, s), ())
      } else {
        dedup(Q, V, S, w, i + int63!(1), w_ + int63!(1), V_.set(w_, v), S_.set(w_, s), ())
      }
    },
    sumbool::right => {
      std::mem::drop(Q);
      std::mem::drop(V);
      std::mem::drop(S);
      ((w_, V_), S_)
    },
  }
}

// Rocq: Bitwise.bitwise_implem.levels
// Variant: uncurried
pub fn levels_1(Q: Array<Int63>, t: Int63, w: Int63, V: Array<Int63>, S: Array<Int63>, V_: Array<Int63>, S_: Array<Int63>) -> ((((Int63, Array<Int63>), Array<Int63>), Array<Int63>), Array<Int63>) {
  levels(Q, t, w, V, S, V_, S_, ())
}

// Rocq: Bitwise.bitwise_implem.levels (local: levels)
// Variant: uncurried, lifted
pub fn levels(Q: Array<Int63>, t: Int63, w: Int63, V: Array<Int63>, S: Array<Int63>, V_: Array<Int63>, S_: Array<Int63>, _H: ()) -> ((((Int63, Array<Int63>), Array<Int63>), Array<Int63>), Array<Int63>) {
  let tmp = int63!(0) < t;
  match bdec(tmp) {
    sumbool::left => {
      let Q_clone = Clone::clone(&Q);
      let V_clone = Clone::clone(&V);
      let S_clone = Clone::clone(&S);
      let tmp_1 = dedup_1(Q_clone, V_clone, S_clone, w, int63!(0), int63!(0), V_, S_);
      match tmp_1 {
        (v47, v49) => {
          match v47 {
            (v52, v54) => {
              levels(Q, t - int63!(1), v52, v54, v49, V, S, ())
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(Q);
      ((((w, V), S), V_), S_)
    },
  }
}

// Rocq: Bitwise.bitwise_implem.check
// Variant: uncurried
pub fn check_1(V: Array<Int63>, S: Array<Int63>, n: Int63, w: Int63, j: Int63) -> bool {
  check(V, S, n, w, j, ())
}

// Rocq: Bitwise.bitwise_implem.check (local: check)
// Variant: uncurried, lifted
pub fn check(V: Array<Int63>, S: Array<Int63>, n: Int63, w: Int63, j: Int63, _H: ()) -> bool {
  let tmp = j < w;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = V.get_cloned(j);
      let tmp_2 = S.get_cloned(j);
      let tmp_3 = tmp_2 + n;
      if tmp_1 <= tmp_3 {
        std::mem::drop(V);
        std::mem::drop(S);
        true
      } else {
        check(V, S, n, w, j + int63!(1), ())
      }
    },
    sumbool::right => {
      std::mem::drop(V);
      std::mem::drop(S);
      false
    },
  }
}

// Rocq: Bitwise.bitwise_implem.test
// Variant: uncurried
pub fn test(Q: Array<Int63>, n: Int63, k: Int63, V: Array<Int63>, S: Array<Int63>, V_: Array<Int63>, S_: Array<Int63>) -> ((((bool, Array<Int63>), Array<Int63>), Array<Int63>), Array<Int63>) {
  let f0 = Q.get_cloned(int63!(0));
  let tmp = n - int63!(1);
  let tmp_1 = if f0 < tmp {
    f0
  } else {
    n - int63!(1)
  };
  let L1 = tmp_1 + int63!(1);
  let tmp_2 = init_1(L1, int63!(0), V, S);
  match &tmp_2 {
    (S1, V1) => {
      let S1_clone = Clone::clone(S1);
      let V1_clone = Clone::clone(V1);
      std::mem::drop(tmp_2);
      let tmp_3 = levels_1(Q, k, L1, S1_clone, V1_clone, V_, S_);
      match tmp_3 {
        (v84, v86) => {
          match v84 {
            (v89, v91) => {
              match v89 {
                (v94, v96) => {
                  let p1 = &v96;
                  match v94 {
                    (v100, v102) => {
                      let w = &v102;
                      let w_clone = Clone::clone(w);
                      let p1_clone = Clone::clone(p1);
                      ((((check_1(w_clone, p1_clone, n, v100, int63!(0)), v102), v96), v91), v86)
                    },
                  }
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Bitwise.bitwise_implem.bits
// Variant: uncurried
pub fn bits_1(a_1: Array<Int63>, n: Int63, k: Int63, b_1: Int63, ans: Int63, P: Array<Int63>, Q: Array<Int63>, V: Array<Int63>, S: Array<Int63>, V_: Array<Int63>, S_: Array<Int63>) -> Int63 {
  bits(a_1, n, k, b_1, ans, P, Q, V, S, V_, S_, ())
}

// Rocq: Bitwise.bitwise_implem.bits (local: bits)
// Variant: uncurried, lifted
pub fn bits(a_1: Array<Int63>, n: Int63, k: Int63, b_1: Int63, ans: Int63, P: Array<Int63>, Q: Array<Int63>, V: Array<Int63>, S: Array<Int63>, V_: Array<Int63>, S_: Array<Int63>, _H: ()) -> Int63 {
  let tmp = int63!(0) < b_1;
  match bdec(tmp) {
    sumbool::left => {
      let j = b_1 - int63!(1);
      let a_clone = Clone::clone(&a_1);
      let P_clone = Clone::clone(&P);
      let Q1 = newptr(a_clone, P_clone, Q, n, j);
      let Q1_clone = Clone::clone(&Q1);
      let tmp_1 = test(Q1_clone, n, k, V, S, V_, S_);
      match tmp_1 {
        (v65, v67) => {
          match v65 {
            (v70, v72) => {
              match v70 {
                (v75, v77) => {
                  match v75 {
                    (v80, v82) => {
                      if v80 {
                        let tmp_2 = int63!(1) << j;
                        bits(a_1, n, k, j, ans | tmp_2, Q1, P, v82, v77, v72, v67, ())
                      } else {
                        bits(a_1, n, k, j, ans, P, Q1, v82, v77, v72, v67, ())
                      }
                    },
                  }
                },
              }
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(a_1);
      std::mem::drop(P);
      std::mem::drop(Q);
      std::mem::drop(V);
      std::mem::drop(S);
      std::mem::drop(V_);
      std::mem::drop(S_);
      ans
    },
  }
}

// Rocq: Bitwise.bitwise_implem.best_and_impl
// Variant: uncurried
pub fn best_and_impl(k: Int63, a_1: Array<Int63>) -> Int63 {
  let n = a_1.length();
  let n2 = int63!(2) * n;
  let P0 = init_ptr_1(n2 + int63!(1), int63!(0), Array::<Int63>::make(n2 + int63!(2), int63!(0)));
  let P = P0.set(n2 + int63!(1), n2 + int63!(1));
  let tmp = Array::<Int63>::make(n2 + int63!(2), int63!(0));
  let tmp_1 = Array::<Int63>::make(n, int63!(0));
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  let tmp_3 = Array::<Int63>::make(n, int63!(0));
  let tmp_4 = Array::<Int63>::make(n, int63!(0));
  bits_1(a_1, n, k, int63!(30), int63!(0), P, tmp, tmp_1, tmp_2, tmp_3, tmp_4)
}
