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

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  if b1 {
    b2
  } else {
    false
  }
}

// Rocq: Cudak.cudak_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Cudak.cudak_implem.digits
// Variant: uncurried
pub fn digits_1(b_1: Int63, d: Int63, q: Int63) -> (Int63, Int63) {
  digits(b_1, d, q, ())
}

// Rocq: Cudak.cudak_implem.digits (local: digits)
// Variant: uncurried, lifted
pub fn digits(b_1: Int63, d: Int63, q: Int63, _H: ()) -> (Int63, Int63) {
  let tmp = andb(d < int63!(15), q * int63!(10) <= b_1);
  match bdec(tmp) {
    sumbool::left => {
      digits(b_1, d + int63!(1), q * int63!(10), ())
    },
    sumbool::right => {
      (d, q)
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

// Rocq: Cudak.cudak_implem.vcell
// Variant: uncurried
pub fn vcell(T: Array<Int63>, base: Int63, t: Int63, c: Int63) -> Int63 {
  if c <= t {
    let tmp = T.get_cloned(base + (t - c));
    std::mem::drop(T);
    tmp
  } else {
    std::mem::drop(T);
    int63!(0)
  }
}

// Rocq: Cudak.cudak_implem.rowsum
// Variant: uncurried
pub fn rowsum_1(T: Array<Int63>, base: Int63, t: Int63, c: Int63, d: Int63, acc: Int63) -> Int63 {
  rowsum(T, base, t, c, d, acc, ())
}

// Rocq: Cudak.cudak_implem.rowsum (local: rowsum)
// Variant: uncurried, lifted
pub fn rowsum(T: Array<Int63>, base: Int63, t: Int63, c: Int63, d: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = d < c;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = d + int63!(1);
      let T_clone = Clone::clone(&T);
      let tmp_2 = vcell(T_clone, base, t, d);
      rowsum(T, base, t, c, tmp_1, acc + tmp_2, ())
    },
    sumbool::right => {
      std::mem::drop(T);
      acc
    },
  }
}

// Rocq: Cudak.cudak_implem.fill
// Variant: uncurried
pub fn fill_1(T: Array<Int63>, s: Int63, S1: Int63, n: Int63, idx: Int63, k: Int63, u: Int63) -> Array<Int63> {
  fill(T, s, S1, n, idx, k, u, ())
}

// Rocq: Cudak.cudak_implem.fill (local: fill)
// Variant: uncurried, lifted
pub fn fill(T: Array<Int63>, s: Int63, S1: Int63, n: Int63, idx: Int63, k: Int63, u: Int63, _H: ()) -> Array<Int63> {
  let tmp = idx < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = (k - int63!(1)) * S1;
      let T_clone = Clone::clone(&T);
      let tmp_2 = T.set(idx, rowsum_1(T_clone, tmp_1, u, int63!(10), int63!(0), int63!(0)));
      let tmp_3 = idx + int63!(1);
      let tmp_4 = if u == s {
        k + int63!(1)
      } else {
        k
      };
      let tmp_5 = if u == s {
        int63!(0)
      } else {
        u + int63!(1)
      };
      fill(tmp_2, s, S1, n, tmp_3, tmp_4, tmp_5, ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Cudak.cudak_implem.walk
// Variant: uncurried
pub fn walk_1(T: Array<Int63>, S1: Int63, j: Int63, p: Int63, R: Int63, t: Int63, acc: Int63) -> Int63 {
  walk(T, S1, j, p, R, t, acc, ())
}

// Rocq: Cudak.cudak_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(T: Array<Int63>, S1: Int63, j: Int63, p: Int63, R: Int63, t: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = int63!(0) < j;
  match bdec(tmp) {
    sumbool::left => {
      let c = R / p;
      let tmp_1 = (j - int63!(1)) * S1;
      let T_clone = Clone::clone(&T);
      let acc_ = rowsum_1(T_clone, tmp_1, t, c, int63!(0), acc);
      if t < c {
        std::mem::drop(T);
        acc_
      } else {
        walk(T, S1, j - int63!(1), p / int63!(10), R % p, t - c, acc_, ())
      }
    },
    sumbool::right => {
      if t == int63!(0) {
        std::mem::drop(T);
        acc + int63!(1)
      } else {
        std::mem::drop(T);
        acc
      }
    },
  }
}

// Rocq: Cudak.cudak_implem.pick
// Variant: uncurried
pub fn pick_1(T: Array<Int63>, base: Int63, t: Int63, c: Int63, r: Int63) -> (Int63, Int63) {
  pick(T, base, t, c, r, ())
}

// Rocq: Cudak.cudak_implem.pick (local: pick)
// Variant: uncurried, lifted
pub fn pick(T: Array<Int63>, base: Int63, t: Int63, c: Int63, r: Int63, _H: ()) -> (Int63, Int63) {
  let tmp = c < int63!(9);
  let T_clone = Clone::clone(&T);
  let tmp_1 = andb(tmp, vcell(T_clone, base, t, c) < r);
  match bdec(tmp_1) {
    sumbool::left => {
      let tmp_2 = c + int63!(1);
      let T_clone_1 = Clone::clone(&T);
      let tmp_3 = vcell(T_clone_1, base, t, c);
      pick(T, base, t, tmp_2, r - tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(T);
      (c, r)
    },
  }
}

// Rocq: Cudak.cudak_implem.minwalk
// Variant: uncurried
pub fn minwalk_1(T: Array<Int63>, S1: Int63, j: Int63, t: Int63, r: Int63, x: Int63) -> Int63 {
  minwalk(T, S1, j, t, r, x, ())
}

// Rocq: Cudak.cudak_implem.minwalk (local: minwalk)
// Variant: uncurried, lifted
pub fn minwalk(T: Array<Int63>, S1: Int63, j: Int63, t: Int63, r: Int63, x: Int63, _H: ()) -> Int63 {
  let tmp = int63!(0) < j;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = (j - int63!(1)) * S1;
      let T_clone = Clone::clone(&T);
      let cr = pick_1(T_clone, tmp_1, t, int63!(0), r);
      let tmp_2 = j - int63!(1);
      let cr_clone = Clone::clone(&cr);
      let tmp_3 = t - fst::<Int63, Int63>(cr_clone);
      let cr_clone_1 = Clone::clone(&cr);
      minwalk(T, S1, tmp_2, tmp_3, snd::<Int63, Int63>(cr_clone_1), x * int63!(10) + fst::<Int63, Int63>(cr), ())
    },
    sumbool::right => {
      std::mem::drop(T);
      x
    },
  }
}

// Rocq: Cudak.cudak_implem.cudak_impl
// Variant: uncurried
pub fn cudak_impl(a_1: Int63, b_1: Int63, s: Int63) -> (Int63, Int63) {
  let S1 = s + int63!(1);
  let dq = digits_1(b_1, int63!(1), int63!(1));
  let dq_clone = Clone::clone(&dq);
  let D = fst::<Int63, Int63>(dq_clone);
  let q = snd::<Int63, Int63>(dq);
  let n = D * S1;
  let T = fill_1(Array::<Int63>::make(n, int63!(0)).set(int63!(0), int63!(1)), s, S1, n, S1, int63!(1), int63!(0));
  let T_clone = Clone::clone(&T);
  let cb = walk_1(T_clone, S1, D, q, b_1, s, int63!(0));
  let tmp = a_1 - int63!(1);
  let T_clone_1 = Clone::clone(&T);
  let ca = walk_1(T_clone_1, S1, D, q, tmp, s, int63!(0));
  (cb - ca, minwalk_1(T, S1, D, s, ca + int63!(1), int63!(0)))
}
