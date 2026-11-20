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

pub type sint = Int63;

pub type uint = Int63;

// Rocq: Longincsubseq.longincsubseq_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Longincsubseq.longincsubseq_implem.bsearch
// Variant: uncurried
pub fn bsearch_1(x: Array<Int63>, tails: Array<Int63>, v: Int63, lo: Int63, hi: Int63) -> Int63 {
  bsearch(x, tails, v, lo, hi, ())
}

// Rocq: Longincsubseq.longincsubseq_implem.bsearch (local: bsearch)
// Variant: uncurried, lifted
pub fn bsearch(x: Array<Int63>, tails: Array<Int63>, v: Int63, lo: Int63, hi: Int63, _H: ()) -> Int63 {
  let tmp = lo < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = hi - lo;
      let mid = lo + tmp_1 / int63!(2);
      let tmp_2 = tails.get_cloned(mid);
      let tmp_3 = x.get_cloned(tmp_2);
      let tmp_4 = tmp_3.ltsb(v);
      match bdec(tmp_4) {
        sumbool::left => {
          bsearch(x, tails, v, mid + int63!(1), hi, ())
        },
        sumbool::right => {
          bsearch(x, tails, v, lo, mid, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(tails);
      lo
    },
  }
}

// Rocq: Longincsubseq.longincsubseq_implem.main_loop
// Variant: uncurried
pub fn main_loop_1(x: Array<Int63>, n: Int63, i: Int63, L: Int63, tails: Array<Int63>, pred: Array<Int63>) -> (Int63, (Array<Int63>, Array<Int63>)) {
  main_loop(x, n, i, L, tails, pred, ())
}

// Rocq: Longincsubseq.longincsubseq_implem.main_loop (local: main_loop)
// Variant: uncurried, lifted
pub fn main_loop(x: Array<Int63>, n: Int63, i: Int63, L: Int63, tails: Array<Int63>, pred: Array<Int63>, _H: ()) -> (Int63, (Array<Int63>, Array<Int63>)) {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let v = x.get_cloned(i);
      let x_clone = Clone::clone(&x);
      let tails_clone = Clone::clone(&tails);
      let k = bsearch_1(x_clone, tails_clone, v, int63!(0), L);
      let tmp_1 = int63!(0);
      let p = if k == tmp_1 {
        int63!(0)
      } else {
        let tmp_2 = k - int63!(1);
        tails.get_cloned(tmp_2)
      };
      let pred_ = pred.set(i, p);
      let tails_ = tails.set(k, i);
      let tmp_3 = i + int63!(1);
      let tmp_4 = if k == L {
        L + int63!(1)
      } else {
        L
      };
      main_loop(x, n, tmp_3, tmp_4, tails_, pred_, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      (L, (tails, pred))
    },
  }
}

// Rocq: Longincsubseq.longincsubseq_implem.build
// Variant: uncurried
pub fn build_1(pred: Array<Int63>, c: Int63, j: Int63, res: Array<Int63>) -> Array<Int63> {
  build(pred, c, j, res, ())
}

// Rocq: Longincsubseq.longincsubseq_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(pred: Array<Int63>, c: Int63, j: Int63, res: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = int63!(0) < c;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = c - int63!(1);
      let tmp_2 = pred.get_cloned(j);
      build(pred, tmp_1, tmp_2, res.set(c - int63!(1), j), ())
    },
    sumbool::right => {
      std::mem::drop(pred);
      res
    },
  }
}

// Rocq: Longincsubseq.longincsubseq_implem.lis_impl
pub fn lis_impl(x: Array<Int63>) -> Array<Int63> {
  let n = x.length();
  let tmp = Array::<Int63>::make(n, int63!(0));
  let tmp_1 = Array::<Int63>::make(n, int63!(0));
  let tmp_2 = main_loop_1(x, n, int63!(0), int63!(0), tmp, tmp_1);
  match tmp_2 {
    (v36, v38) => {
      match v38 {
        (v41, v43) => {
          let pred = &v41;
          let tmp_3 = pred.get_cloned(v36 - int63!(1));
          std::mem::drop(v41);
          let tmp_4 = Array::<Int63>::make(v36, int63!(0));
          build_1(v43, v36, tmp_3, tmp_4)
        },
      }
    },
  }
}
