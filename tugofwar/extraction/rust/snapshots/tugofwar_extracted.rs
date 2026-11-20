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

// Rocq: Tugofwar.tugofwar_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Tugofwar.tugofwar_implem.sum_loop
// Variant: uncurried
pub fn sum_loop_1(a_1: Array<Int63>, i: Int63, acc: Int63) -> Int63 {
  sum_loop(a_1, i, acc, ())
}

// Rocq: Tugofwar.tugofwar_implem.sum_loop (local: sum_loop)
// Variant: uncurried, lifted
pub fn sum_loop(a_1: Array<Int63>, i: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = int63!(0) < i;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i - int63!(1);
      let tmp_2 = a_1.get_cloned(i - int63!(1));
      sum_loop(a_1, tmp_1, acc + tmp_2, ())
    },
    sumbool::right => {
      std::mem::drop(a_1);
      acc
    },
  }
}

// Rocq: Tugofwar.tugofwar_implem.cell_loop
// Variant: uncurried
pub fn cell_loop_1(t: Array<bool>, W: Int63, x: Int63, c: Int63, s: Int63) -> Array<bool> {
  cell_loop(t, W, x, c, s, ())
}

// Rocq: Tugofwar.tugofwar_implem.cell_loop (local: cell_loop)
// Variant: uncurried, lifted
pub fn cell_loop(t: Array<bool>, W: Int63, x: Int63, c: Int63, s: Int63, _H: ()) -> Array<bool> {
  let tmp = s < W;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = t.get_cloned((c - int63!(1)) * W + (s - x));
      let tmp_2 = if tmp_1 {
        t.set(c * W + s, true)
      } else {
        t
      };
      cell_loop(tmp_2, W, x, c, s + int63!(1), ())
    },
    sumbool::right => {
      t
    },
  }
}

// Rocq: Tugofwar.tugofwar_implem.row_loop
// Variant: uncurried
pub fn row_loop_1(t: Array<bool>, W: Int63, x: Int63, c: Int63) -> Array<bool> {
  row_loop(t, W, x, c, ())
}

// Rocq: Tugofwar.tugofwar_implem.row_loop (local: row_loop)
// Variant: uncurried, lifted
pub fn row_loop(t: Array<bool>, W: Int63, x: Int63, c: Int63, _H: ()) -> Array<bool> {
  let tmp = int63!(0) < c;
  match bdec(tmp) {
    sumbool::left => {
      row_loop(cell_loop_1(t, W, x, c, x), W, x, c - int63!(1), ())
    },
    sumbool::right => {
      t
    },
  }
}

// Rocq: Tugofwar.tugofwar_implem.item_loop
// Variant: uncurried
pub fn item_loop_1(a_1: Array<Int63>, t: Array<bool>, W: Int63, K: Int63, i: Int63) -> Array<bool> {
  item_loop(a_1, t, W, K, i, ())
}

// Rocq: Tugofwar.tugofwar_implem.item_loop (local: item_loop)
// Variant: uncurried, lifted
pub fn item_loop(a_1: Array<Int63>, t: Array<bool>, W: Int63, K: Int63, i: Int63, _H: ()) -> Array<bool> {
  let tmp = int63!(0) < i;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = a_1.get_cloned(i - int63!(1));
      item_loop(a_1, row_loop_1(t, W, tmp_1, K), W, K, i - int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(a_1);
      t
    },
  }
}

// Rocq: Corelib.Init.Datatypes.orb
// Variant: uncurried
pub fn orb(b1: bool, b2: bool) -> bool {
  if b1 {
    true
  } else {
    b2
  }
}

// Rocq: Tugofwar.tugofwar_implem.best_loop
// Variant: uncurried
pub fn best_loop_1(t: Array<bool>, W: Int63, h: Int63, K: Int63, s: Int63) -> Int63 {
  best_loop(t, W, h, K, s, ())
}

// Rocq: Tugofwar.tugofwar_implem.best_loop (local: best_loop)
// Variant: uncurried, lifted
pub fn best_loop(t: Array<bool>, W: Int63, h: Int63, K: Int63, s: Int63, _H: ()) -> Int63 {
  let tmp = t.get_cloned(h * W + s);
  let tmp_1 = t.get_cloned(K * W + s);
  if orb(tmp, tmp_1) {
    std::mem::drop(t);
    s
  } else {
    let tmp_2 = int63!(0) < s;
    match bdec(tmp_2) {
      sumbool::left => {
        best_loop(t, W, h, K, s - int63!(1), ())
      },
      sumbool::right => {
        std::mem::drop(t);
        int63!(0)
      },
    }
  }
}

// Rocq: Tugofwar.tugofwar_implem.tugofwar_impl
pub fn tugofwar_impl(a_1: Array<Int63>) -> (Int63, Int63) {
  let n = a_1.length();
  let a_clone = Clone::clone(&a_1);
  let S = sum_loop_1(a_clone, n, int63!(0));
  let half = S / int63!(2);
  let W = half + int63!(1);
  let h = n / int63!(2);
  let K = n - h;
  let t0 = Array::<bool>::make((K + int63!(1)) * W, false).set(int63!(0), true);
  let t = item_loop_1(a_1, t0, W, K, n);
  let b_1 = best_loop_1(t, W, h, K, half);
  let tmp = S - b_1;
  (b_1, tmp)
}
