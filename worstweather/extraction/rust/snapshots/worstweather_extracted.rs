#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

#[derive(Clone, Copy)]
pub enum answer {
  Ans_true,
  Ans_maybe,
  Ans_false,
}

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type sint = Int63;

pub type uint = Int63;

// Rocq: Worstweather.worstweather_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Worstweather.worstweather_implem.lg_loop
// Variant: uncurried
pub fn lg_loop_1(x: Int63, k: Int63) -> Int63 {
  lg_loop(x, k, ())
}

// Rocq: Worstweather.worstweather_implem.lg_loop (local: lg_loop)
// Variant: uncurried, lifted
pub fn lg_loop(x: Int63, k: Int63, _H: ()) -> Int63 {
  let tmp = int63!(1) < x;
  match bdec(tmp) {
    sumbool::left => {
      lg_loop(x / int63!(2), k + int63!(1), ())
    },
    sumbool::right => {
      k
    },
  }
}

// Rocq: Worstweather.worstweather_implem.lg
pub fn lg(x: Int63) -> Int63 {
  lg_loop_1(x, int63!(0))
}

// Rocq: Worstweather.worstweather_implem.imax
// Variant: uncurried
pub fn imax(a_1: Int63, b_1: Int63) -> Int63 {
  if a_1 < b_1 {
    b_1
  } else {
    a_1
  }
}

// Rocq: Worstweather.worstweather_implem.row_loop
// Variant: uncurried
pub fn row_loop_1(base: Int63, prev: Int63, half: Int63, lim: Int63, i: Int63, T: Array<Int63>) -> Array<Int63> {
  row_loop(base, prev, half, lim, i, T, ())
}

// Rocq: Worstweather.worstweather_implem.row_loop (local: row_loop)
// Variant: uncurried, lifted
pub fn row_loop(base: Int63, prev: Int63, half: Int63, lim: Int63, i: Int63, T: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < lim;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = base + i;
      let tmp_3 = T.get_cloned(prev + i);
      let tmp_4 = T.get_cloned(prev + i + half);
      row_loop(base, prev, half, lim, tmp_1, T.set(tmp_2, imax(tmp_3, tmp_4)), ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Worstweather.worstweather_implem.rows_loop
// Variant: uncurried
pub fn rows_loop_1(n: Int63, L: Int63, k: Int63, T: Array<Int63>) -> Array<Int63> {
  rows_loop(n, L, k, T, ())
}

// Rocq: Worstweather.worstweather_implem.rows_loop (local: rows_loop)
// Variant: uncurried, lifted
pub fn rows_loop(n: Int63, L: Int63, k: Int63, T: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = k < L;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = k + int63!(1);
      let tmp_2 = k * n;
      let tmp_3 = (k - int63!(1)) * n;
      let tmp_4 = int63!(1) << k - int63!(1);
      let tmp_5 = n - (int63!(1) << k);
      rows_loop(n, L, tmp_1, row_loop_1(tmp_2, tmp_3, tmp_4, tmp_5 + int63!(1), int63!(0), T), ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Worstweather.worstweather_implem.copy_loop
// Variant: uncurried
pub fn copy_loop_1(rs: Array<Int63>, n: Int63, i: Int63, T: Array<Int63>) -> Array<Int63> {
  copy_loop(rs, n, i, T, ())
}

// Rocq: Worstweather.worstweather_implem.copy_loop (local: copy_loop)
// Variant: uncurried, lifted
pub fn copy_loop(rs: Array<Int63>, n: Int63, i: Int63, T: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = rs.get_cloned(i);
      copy_loop(rs, n, tmp_1, T.set(i, tmp_2), ())
    },
    sumbool::right => {
      std::mem::drop(rs);
      T
    },
  }
}

// Rocq: Worstweather.worstweather_implem.build
// Variant: uncurried
pub fn build(rs: Array<Int63>, n: Int63, L: Int63) -> Array<Int63> {
  let tmp = L * n;
  let tmp_1 = copy_loop_1(rs, n, int63!(0), Array::<Int63>::make(tmp, int63!(0)));
  rows_loop_1(n, L, int63!(1), tmp_1)
}

// Rocq: Worstweather.worstweather_implem.lb_loop
// Variant: uncurried
pub fn lb_loop_1(ys: Array<Int63>, key: Int63, lo: Int63, hi: Int63) -> Int63 {
  lb_loop(ys, key, lo, hi, ())
}

// Rocq: Worstweather.worstweather_implem.lb_loop (local: lb_loop)
// Variant: uncurried, lifted
pub fn lb_loop(ys: Array<Int63>, key: Int63, lo: Int63, hi: Int63, _H: ()) -> Int63 {
  let tmp = lo < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = hi - lo;
      let mid = lo + tmp_1 / int63!(2);
      let tmp_2 = ys.get_cloned(mid);
      if tmp_2.ltsb(key) {
        lb_loop(ys, key, mid + int63!(1), hi, ())
      } else {
        lb_loop(ys, key, lo, mid, ())
      }
    },
    sumbool::right => {
      std::mem::drop(ys);
      lo
    },
  }
}

// Rocq: Worstweather.worstweather_implem.lower_bound
// Variant: uncurried
pub fn lower_bound(ys: Array<Int63>, n: Int63, key: Int63) -> Int63 {
  lb_loop_1(ys, key, int63!(0), n)
}

// Rocq: Worstweather.worstweather_implem.rmq
// Variant: uncurried
pub fn rmq(T: Array<Int63>, n: Int63, l: Int63, r: Int63) -> Int63 {
  let k = lg(r - l);
  let tmp = T.get_cloned(k * n + l);
  let tmp_1 = T.get_cloned(k * n + (r - (int63!(1) << k)));
  std::mem::drop(T);
  imax(tmp, tmp_1)
}

// Rocq: Worstweather.worstweather_implem.below
// Variant: uncurried
pub fn below(T: Array<Int63>, n: Int63, lo: Int63, j: Int63, v: Int63) -> bool {
  if lo < j {
    rmq(T, n, lo, j) < v
  } else {
    std::mem::drop(T);
    true
  }
}

// Rocq: Worstweather.worstweather_implem.answer_query
// Variant: uncurried
pub fn answer_query(ys: Array<Int63>, rs: Array<Int63>, T: Array<Int63>, n: Int63, Y: Int63, X: Int63) -> answer {
  let ys_clone = Clone::clone(&ys);
  let i = lower_bound(ys_clone, n, Y);
  let ys_clone_1 = Clone::clone(&ys);
  let j = lower_bound(ys_clone_1, n, X);
  let yk = if i < n {
    let tmp = ys.get_cloned(i);
    tmp == Y
  } else {
    false
  };
  let xk = if j < n {
    let tmp_1 = ys.get_cloned(j);
    tmp_1 == X
  } else {
    false
  };
  let lo = if yk {
    i + int63!(1)
  } else {
    i
  };
  if yk {
    if xk {
      let tmp_2 = rs.get_cloned(j);
      let tmp_3 = rs.get_cloned(i);
      if tmp_2 <= tmp_3 {
        let tmp_4 = rs.get_cloned(j);
        if below(T, n, lo, j, tmp_4) {
          let tmp_5 = j - i;
          let tmp_6 = X - Y;
          if tmp_5 == tmp_6 {
            std::mem::drop(ys);
            std::mem::drop(rs);
            answer::Ans_true
          } else {
            std::mem::drop(ys);
            std::mem::drop(rs);
            answer::Ans_maybe
          }
        } else {
          std::mem::drop(ys);
          std::mem::drop(rs);
          answer::Ans_false
        }
      } else {
        std::mem::drop(ys);
        std::mem::drop(rs);
        std::mem::drop(T);
        answer::Ans_false
      }
    } else {
      let tmp_7 = rs.get_cloned(i);
      if below(T, n, lo, j, tmp_7) {
        std::mem::drop(ys);
        std::mem::drop(rs);
        answer::Ans_maybe
      } else {
        std::mem::drop(ys);
        std::mem::drop(rs);
        answer::Ans_false
      }
    }
  } else {
    if xk {
      let tmp_8 = rs.get_cloned(j);
      if below(T, n, lo, j, tmp_8) {
        std::mem::drop(ys);
        std::mem::drop(rs);
        answer::Ans_maybe
      } else {
        std::mem::drop(ys);
        std::mem::drop(rs);
        answer::Ans_false
      }
    } else {
      std::mem::drop(ys);
      std::mem::drop(rs);
      std::mem::drop(T);
      answer::Ans_maybe
    }
  }
}

// Rocq: Worstweather.worstweather_implem.q_loop
// Variant: uncurried
pub fn q_loop_1(ys: Array<Int63>, rs: Array<Int63>, T: Array<Int63>, qy: Array<Int63>, qx: Array<Int63>, n: Int63, m: Int63, k: Int63, out: Array<answer>) -> Array<answer> {
  q_loop(ys, rs, T, qy, qx, n, m, k, out, ())
}

// Rocq: Worstweather.worstweather_implem.q_loop (local: q_loop)
// Variant: uncurried, lifted
pub fn q_loop(ys: Array<Int63>, rs: Array<Int63>, T: Array<Int63>, qy: Array<Int63>, qx: Array<Int63>, n: Int63, m: Int63, k: Int63, out: Array<answer>, _H: ()) -> Array<answer> {
  let tmp = k < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = k + int63!(1);
      let tmp_2 = qy.get_cloned(k);
      let tmp_3 = qx.get_cloned(k);
      let ys_clone = Clone::clone(&ys);
      let rs_clone = Clone::clone(&rs);
      let T_clone = Clone::clone(&T);
      let tmp_4 = answer_query(ys_clone, rs_clone, T_clone, n, tmp_2, tmp_3);
      q_loop(ys, rs, T, qy, qx, n, m, tmp_1, out.set(k, tmp_4), ())
    },
    sumbool::right => {
      std::mem::drop(ys);
      std::mem::drop(rs);
      std::mem::drop(T);
      std::mem::drop(qy);
      std::mem::drop(qx);
      out
    },
  }
}

// Rocq: Worstweather.worstweather_implem.worstweather_impl
// Variant: uncurried
pub fn worstweather_impl(ys: Array<Int63>, rs: Array<Int63>, qy: Array<Int63>, qx: Array<Int63>) -> Array<answer> {
  let n = ys.length();
  let m = qy.length();
  let L = lg(n) + int63!(1);
  let rs_clone = Clone::clone(&rs);
  let T = build(rs_clone, n, L);
  let tmp = Array::<answer>::make(m, answer::Ans_false);
  q_loop_1(ys, rs, T, qy, qx, n, m, int63!(0), tmp)
}
