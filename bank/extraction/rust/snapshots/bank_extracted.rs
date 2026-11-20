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

// Rocq: Bank.bank_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Bank.bank_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(m: Int63, k: Int63, a_1: Array<Int63>) -> Array<Int63> {
  init_loop(m, k, a_1, ())
}

// Rocq: Bank.bank_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(m: Int63, k: Int63, a_1: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = k < m;
  match bdec(tmp) {
    sumbool::left => {
      init_loop(m, k + int63!(1), a_1.set(k, k), ())
    },
    sumbool::right => {
      a_1
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Bank.bank_implem.take_left
// Variant: uncurried
pub fn take_left(cash: Array<Int63>, src: Array<Int63>, mid: Int63, hi: Int63, i: Int63, j: Int63) -> bool {
  if i < mid {
    if j < hi {
      let tmp = src.get_cloned(j);
      let tmp_1 = cash.get_cloned(tmp);
      let tmp_2 = src.get_cloned(i);
      std::mem::drop(src);
      let tmp_3 = cash.get_cloned(tmp_2);
      std::mem::drop(cash);
      tmp_1 <= tmp_3
    } else {
      std::mem::drop(cash);
      std::mem::drop(src);
      true
    }
  } else {
    std::mem::drop(cash);
    std::mem::drop(src);
    false
  }
}

// Rocq: Bank.bank_implem.merge_loop
// Variant: uncurried
pub fn merge_loop_1(cash: Array<Int63>, src: Array<Int63>, mid: Int63, hi: Int63, i: Int63, j: Int63, k: Int63, dst: Array<Int63>) -> Array<Int63> {
  merge_loop(cash, src, mid, hi, i, j, k, dst, ())
}

// Rocq: Bank.bank_implem.merge_loop (local: merge_loop)
// Variant: uncurried, lifted
pub fn merge_loop(cash: Array<Int63>, src: Array<Int63>, mid: Int63, hi: Int63, i: Int63, j: Int63, k: Int63, dst: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = k < hi;
  match bdec(tmp) {
    sumbool::left => {
      let cash_clone = Clone::clone(&cash);
      let src_clone = Clone::clone(&src);
      if take_left(cash_clone, src_clone, mid, hi, i, j) {
        let tmp_1 = i + int63!(1);
        let tmp_2 = k + int63!(1);
        let tmp_3 = src.get_cloned(i);
        merge_loop(cash, src, mid, hi, tmp_1, j, tmp_2, dst.set(k, tmp_3), ())
      } else {
        let tmp_4 = j + int63!(1);
        let tmp_5 = k + int63!(1);
        let tmp_6 = src.get_cloned(j);
        merge_loop(cash, src, mid, hi, i, tmp_4, tmp_5, dst.set(k, tmp_6), ())
      }
    },
    sumbool::right => {
      std::mem::drop(cash);
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Bank.bank_implem.copy_loop
// Variant: uncurried
pub fn copy_loop_1(src: Array<Int63>, hi: Int63, k: Int63, dst: Array<Int63>) -> Array<Int63> {
  copy_loop(src, hi, k, dst, ())
}

// Rocq: Bank.bank_implem.copy_loop (local: copy_loop)
// Variant: uncurried, lifted
pub fn copy_loop(src: Array<Int63>, hi: Int63, k: Int63, dst: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = k < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = k + int63!(1);
      let tmp_2 = src.get_cloned(k);
      copy_loop(src, hi, tmp_1, dst.set(k, tmp_2), ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Bank.bank_implem.msort
// Variant: uncurried
pub fn msort_1(cash: Array<Int63>, a_1: Array<Int63>, b_1: Array<Int63>, lo: Int63, len: Int63) -> (Array<Int63>, Array<Int63>) {
  msort(cash, a_1, b_1, lo, len, ())
}

// Rocq: Bank.bank_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(cash: Array<Int63>, a_1: Array<Int63>, b_1: Array<Int63>, lo: Int63, len: Int63, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = int63!(1) < len;
  match bdec(tmp) {
    sumbool::left => {
      let len1 = len / int63!(2);
      let mid = lo + len1;
      let hi = lo + len;
      let cash_clone = Clone::clone(&cash);
      let tmp_1 = msort(cash_clone, a_1, b_1, lo, len1, ());
      match &tmp_1 {
        (b1, a1) => {
          let tmp_2 = len - len1;
          let tmp_3 = ();
          let cash_clone_1 = Clone::clone(&cash);
          let b1_clone = Clone::clone(b1);
          let a1_clone = Clone::clone(a1);
          std::mem::drop(tmp_1);
          let tmp_4 = msort(cash_clone_1, b1_clone, a1_clone, mid, tmp_2, tmp_3);
          match tmp_4 {
            (v86, v88) => {
              let b2 = &v86;
              let b2_clone = Clone::clone(b2);
              let b3 = merge_loop_1(cash, b2_clone, mid, hi, lo, mid, lo, v88);
              let b3_clone = Clone::clone(&b3);
              let a3 = copy_loop_1(b3_clone, hi, lo, v86);
              (a3, b3)
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(cash);
      (a_1, b_1)
    },
  }
}

// Rocq: Bank.bank_implem.find
// Variant: uncurried
pub fn find_1(a_1: Array<Int63>, x: Int63) -> (Array<Int63>, Int63) {
  find(a_1, x, ())
}

// Rocq: Bank.bank_implem.find (local: find)
// Variant: uncurried, lifted
pub fn find(a_1: Array<Int63>, x: Int63, _H: ()) -> (Array<Int63>, Int63) {
  let p = a_1.get_cloned(x);
  let tmp = p < x;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = find(a_1, p, ());
      match tmp_1 {
        (v29, v31) => {
          (v29.set(x, v31), v31)
        },
      }
    },
    sumbool::right => {
      (a_1, x)
    },
  }
}

// Rocq: Bank.bank_implem.greedy_loop
// Variant: uncurried
pub fn greedy_loop_1(cash: Array<Int63>, dl: Array<Int63>, perm: Array<Int63>, n: Int63, L: Int63, j: Int63, uf: Array<Int63>, tot: Int63) -> Int63 {
  greedy_loop(cash, dl, perm, n, L, j, uf, tot, ())
}

// Rocq: Bank.bank_implem.greedy_loop (local: greedy_loop)
// Variant: uncurried, lifted
pub fn greedy_loop(cash: Array<Int63>, dl: Array<Int63>, perm: Array<Int63>, n: Int63, L: Int63, j: Int63, uf: Array<Int63>, tot: Int63, _H: ()) -> Int63 {
  let tmp = j < n;
  match bdec(tmp) {
    sumbool::left => {
      let i = perm.get_cloned(j);
      let d = dl.get_cloned(i);
      let c = if d < L {
        d + int63!(1)
      } else {
        L
      };
      let tmp_1 = find_1(uf, c);
      match tmp_1 {
        (v55, v57) => {
          if v57 == int63!(0) {
            greedy_loop(cash, dl, perm, n, L, j + int63!(1), v55, tot, ())
          } else {
            let tmp_2 = j + int63!(1);
            let tmp_3 = v57 - int63!(1);
            let tmp_4 = v55.set(v57, tmp_3);
            let tmp_5 = cash.get_cloned(i);
            greedy_loop(cash, dl, perm, n, L, tmp_2, tmp_4, tot + tmp_5, ())
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(cash);
      std::mem::drop(dl);
      std::mem::drop(perm);
      std::mem::drop(uf);
      tot
    },
  }
}

// Rocq: Bank.bank_implem.bank_impl
// Variant: uncurried
pub fn bank_impl(t: Int63, cash: Array<Int63>, dl: Array<Int63>) -> Int63 {
  let n = cash.length();
  let tmp = Array::<Int63>::make(n, int63!(0));
  let p0 = init_loop_1(n, int63!(0), tmp);
  let tmp_1 = Array::<Int63>::make(n, int63!(0));
  let cash_clone = Clone::clone(&cash);
  let p = fst::<Array<Int63>, Array<Int63>>(msort_1(cash_clone, p0, tmp_1, int63!(0), n));
  let L = if t < n {
    t
  } else {
    n
  };
  let uf = init_loop_1(L + int63!(1), int63!(0), Array::<Int63>::make(L + int63!(1), int63!(0)));
  greedy_loop_1(cash, dl, p, n, L, int63!(0), uf, int63!(0))
}
