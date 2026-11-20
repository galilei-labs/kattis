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

// Rocq: Nonnegpartsums.nonnegpartsums_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.prefix_loop
// Variant: uncurried
pub fn prefix_loop_1(x: Array<Int63>, n: Int63, i: Int63, P: Array<Int63>) -> Array<Int63> {
  prefix_loop(x, n, i, P, ())
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.prefix_loop (local: prefix_loop)
// Variant: uncurried, lifted
pub fn prefix_loop(x: Array<Int63>, n: Int63, i: Int63, P: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = i + int63!(1);
      let tmp_3 = P.get_cloned(i);
      let tmp_4 = x.get_cloned(i);
      prefix_loop(x, n, tmp_1, P.set(tmp_2, tmp_3 + tmp_4), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      P
    },
  }
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.pop_front
// Variant: uncurried
pub fn pop_front_1(dq: Array<Int63>, n: Int63, j: Int63, h: Int63, t: Int63) -> Int63 {
  pop_front(dq, n, j, h, t, ())
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.pop_front (local: pop_front)
// Variant: uncurried, lifted
pub fn pop_front(dq: Array<Int63>, n: Int63, j: Int63, h: Int63, t: Int63, _H: ()) -> Int63 {
  let tmp = h < t;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = dq.get_cloned(h % n);
      let tmp_2 = tmp_1 + n;
      if tmp_2 <= j {
        pop_front(dq, n, j, h + int63!(1), t, ())
      } else {
        std::mem::drop(dq);
        h
      }
    },
    sumbool::right => {
      std::mem::drop(dq);
      h
    },
  }
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.qv
// Variant: uncurried
pub fn qv(P: Array<Int63>, n: Int63, tot: Int63, j: Int63) -> Int63 {
  if j <= n {
    let tmp = P.get_cloned(j);
    std::mem::drop(P);
    tmp
  } else {
    let tmp_1 = P.get_cloned(j - n);
    std::mem::drop(P);
    tot + tmp_1
  }
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.pop_back
// Variant: uncurried
pub fn pop_back_1(dq: Array<Int63>, P: Array<Int63>, n: Int63, tot: Int63, qj: Int63, h: Int63, t: Int63) -> Int63 {
  pop_back(dq, P, n, tot, qj, h, t, ())
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.pop_back (local: pop_back)
// Variant: uncurried, lifted
pub fn pop_back(dq: Array<Int63>, P: Array<Int63>, n: Int63, tot: Int63, qj: Int63, h: Int63, t: Int63, _H: ()) -> Int63 {
  let tmp = h < t;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = dq.get_cloned((t - int63!(1)) % n);
      let P_clone = Clone::clone(&P);
      let tmp_2 = qv(P_clone, n, tot, tmp_1);
      if qj.lesb(tmp_2) {
        pop_back(dq, P, n, tot, qj, h, t - int63!(1), ())
      } else {
        std::mem::drop(P);
        std::mem::drop(dq);
        t
      }
    },
    sumbool::right => {
      std::mem::drop(dq);
      std::mem::drop(P);
      t
    },
  }
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.sweep
// Variant: uncurried
pub fn sweep_1(P: Array<Int63>, n: Int63, tot: Int63, m: Int63, j: Int63, h: Int63, t: Int63, cnt: Int63, dq: Array<Int63>) -> Int63 {
  sweep(P, n, tot, m, j, h, t, cnt, dq, ())
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.sweep (local: sweep)
// Variant: uncurried, lifted
pub fn sweep(P: Array<Int63>, n: Int63, tot: Int63, m: Int63, j: Int63, h: Int63, t: Int63, cnt: Int63, dq: Array<Int63>, _H: ()) -> Int63 {
  let tmp = j < m;
  match bdec(tmp) {
    sumbool::left => {
      let dq_clone = Clone::clone(&dq);
      let h1 = pop_front_1(dq_clone, n, j, h, t);
      let P_clone = Clone::clone(&P);
      let qj = qv(P_clone, n, tot, j);
      let dq_clone_1 = Clone::clone(&dq);
      let P_clone_1 = Clone::clone(&P);
      let t1 = pop_back_1(dq_clone_1, P_clone_1, n, tot, qj, h1, t);
      let dq1 = dq.set(t1 % n, j);
      let cnt1 = if n <= j {
        let tmp_1 = j - n;
        let P_clone_2 = Clone::clone(&P);
        let tmp_2 = qv(P_clone_2, n, tot, tmp_1);
        let tmp_3 = dq1.get_cloned(h1 % n);
        let P_clone_3 = Clone::clone(&P);
        let tmp_4 = qv(P_clone_3, n, tot, tmp_3);
        if tmp_2.lesb(tmp_4) {
          cnt + int63!(1)
        } else {
          cnt
        }
      } else {
        cnt
      };
      sweep(P, n, tot, m, j + int63!(1), h1, t1 + int63!(1), cnt1, dq1, ())
    },
    sumbool::right => {
      std::mem::drop(P);
      std::mem::drop(dq);
      cnt
    },
  }
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.count_impl
pub fn count_impl(x: Array<Int63>) -> Int63 {
  let n = x.length();
  let tmp = n + int63!(1);
  let P = prefix_loop_1(x, n, int63!(0), Array::<Int63>::make(tmp, int63!(0)));
  let tot = P.get_cloned(n);
  let tmp_1 = n + n;
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  sweep_1(P, n, tot, tmp_1, int63!(1), int63!(0), int63!(0), int63!(0), tmp_2)
}
