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

// Rocq: Knapsack2.knapsack2_implem.inf
pub fn inf() -> Int63 {
  int63!(9223372036854775807)
}

// Rocq: Knapsack2.knapsack2_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Knapsack2.knapsack2_implem.min_loop
// Variant: uncurried
pub fn min_loop_1(g: Array<Int63>, n: Int63, i: Int63, best: Int63) -> Int63 {
  min_loop(g, n, i, best, ())
}

// Rocq: Knapsack2.knapsack2_implem.min_loop (local: min_loop)
// Variant: uncurried, lifted
pub fn min_loop(g: Array<Int63>, n: Int63, i: Int63, best: Int63, _H: ()) -> Int63 {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = g.get_cloned(i);
      let tmp_3 = if tmp_2 < best {
        g.get_cloned(i)
      } else {
        best
      };
      min_loop(g, n, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(g);
      best
    },
  }
}

// Rocq: Knapsack2.knapsack2_implem.gcd_loop
// Variant: uncurried
pub fn gcd_loop_1(u: Int63, v: Int63) -> Int63 {
  gcd_loop(u, v, ())
}

// Rocq: Knapsack2.knapsack2_implem.gcd_loop (local: gcd_loop)
// Variant: uncurried, lifted
pub fn gcd_loop(u: Int63, v: Int63, _H: ()) -> Int63 {
  let tmp = v == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      u
    },
    sumbool::right => {
      let tmp_1 = u % v;
      gcd_loop(v, tmp_1, ())
    },
  }
}

// Rocq: Knapsack2.knapsack2_implem.nxt
// Variant: uncurried
pub fn nxt(m: Int63, a_: Int63, x: Int63) -> Int63 {
  let y = x + a_;
  if y < m {
    y
  } else {
    y - m
  }
}

// Rocq: Knapsack2.knapsack2_implem.scan
// Variant: uncurried
pub fn scan_1(A: Array<Int63>, m: Int63, a_: Int63, L: Int63, j: Int63, x: Int63, p: Int63) -> Int63 {
  scan(A, m, a_, L, j, x, p, ())
}

// Rocq: Knapsack2.knapsack2_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(A: Array<Int63>, m: Int63, a_: Int63, L: Int63, j: Int63, x: Int63, p: Int63, _H: ()) -> Int63 {
  let tmp = j < L;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = j + int63!(1);
      let tmp_2 = nxt(m, a_, x);
      let tmp_3 = A.get_cloned(x);
      let tmp_4 = A.get_cloned(p);
      let tmp_5 = if tmp_3 < tmp_4 {
        x
      } else {
        p
      };
      scan(A, m, a_, L, tmp_1, tmp_2, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(A);
      p
    },
  }
}

// Rocq: Knapsack2.knapsack2_implem.relax
// Variant: uncurried
pub fn relax_1(m: Int63, a_1: Int63, a_: Int63, L1: Int63, j: Int63, x: Int63, cur: Int63, A: Array<Int63>) -> Array<Int63> {
  relax(m, a_1, a_, L1, j, x, cur, A, ())
}

// Rocq: Knapsack2.knapsack2_implem.relax (local: relax)
// Variant: uncurried, lifted
pub fn relax(m: Int63, a_1: Int63, a_: Int63, L1: Int63, j: Int63, x: Int63, cur: Int63, A: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = j < L1;
  match bdec(tmp) {
    sumbool::left => {
      let y = nxt(m, a_, x);
      let c = cur + a_1;
      let v = A.get_cloned(y);
      if c < v {
        let tmp_1 = j + int63!(1);
        let tmp_2 = A.set(y, c);
        relax(m, a_1, a_, L1, tmp_1, y, c, tmp_2, ())
      } else {
        relax(m, a_1, a_, L1, j + int63!(1), y, v, A, ())
      }
    },
    sumbool::right => {
      A
    },
  }
}

// Rocq: Knapsack2.knapsack2_implem.classes
// Variant: uncurried
pub fn classes_1(m: Int63, a_1: Int63, a_: Int63, d: Int63, L: Int63, c: Int63, A: Array<Int63>) -> Array<Int63> {
  classes(m, a_1, a_, d, L, c, A, ())
}

// Rocq: Knapsack2.knapsack2_implem.classes (local: classes)
// Variant: uncurried, lifted
pub fn classes(m: Int63, a_1: Int63, a_: Int63, d: Int63, L: Int63, c: Int63, A: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = c < d;
  match bdec(tmp) {
    sumbool::left => {
      let A_clone = Clone::clone(&A);
      let p = scan_1(A_clone, m, a_, L, int63!(0), c, c);
      let v = A.get_cloned(p);
      let tmp_1 = c + int63!(1);
      let tmp_2 = __rocq_global_249;
      let tmp_3 = if v == tmp_2 {
        A
      } else {
        relax_1(m, a_1, a_, L - int63!(1), int63!(0), p, v, A)
      };
      classes(m, a_1, a_, d, L, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      A
    },
  }
}

// Rocq: Knapsack2.knapsack2_implem.item
// Variant: uncurried
pub fn item(m: Int63, a_1: Int63, A: Array<Int63>) -> Array<Int63> {
  let a_ = a_1 % m;
  let d = gcd_loop_1(m, a_);
  let tmp = m / d;
  classes_1(m, a_1, a_, d, tmp, int63!(0), A)
}

// Rocq: Knapsack2.knapsack2_implem.items
// Variant: uncurried
pub fn items_1(g: Array<Int63>, n: Int63, m: Int63, i: Int63, A: Array<Int63>) -> Array<Int63> {
  items(g, n, m, i, A, ())
}

// Rocq: Knapsack2.knapsack2_implem.items (local: items)
// Variant: uncurried, lifted
pub fn items(g: Array<Int63>, n: Int63, m: Int63, i: Int63, A: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = g.get_cloned(i);
      let tmp_3 = item(m, tmp_2, A);
      items(g, n, m, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(g);
      A
    },
  }
}

// Rocq: Knapsack2.knapsack2_implem.fillable_core
// Variant: uncurried
pub fn fillable_core(k: Int63, g: Array<Int63>) -> bool {
  let n = g.length();
  let tmp = g.get_cloned(int63!(0));
  let g_clone = Clone::clone(&g);
  let m = min_loop_1(g_clone, n, int63!(1), tmp);
  let tmp_1 = Array::<Int63>::make(m, __rocq_global_249);
  let A = items_1(g, n, m, int63!(0), tmp_1.set(int63!(0), int63!(0)));
  let tmp_2 = A.get_cloned(k % m);
  std::mem::drop(A);
  tmp_2 <= k
}

// Rocq: Knapsack2.knapsack2_implem.fillable_impl
// Variant: uncurried
pub fn fillable_impl(k: Int63, g: Array<Int63>) -> bool {
  fillable_core(k, g)
}
const __rocq_global_249: Int63 = int63!(9223372036854775807);