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

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  if b1 {
    b2
  } else {
    false
  }
}

// Rocq: Convexhull.convexhull_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Convexhull.convexhull_implem.min_i
// Variant: uncurried
pub fn min_i(a_1: Int63, b_1: Int63) -> Int63 {
  if a_1 < b_1 {
    a_1
  } else {
    b_1
  }
}

// Rocq: Convexhull.convexhull_implem.le_pt
// Variant: uncurried
pub fn le_pt(x: Array<Int63>, y: Array<Int63>, a_1: Int63, b_1: Int63) -> bool {
  let xa = x.get_cloned(a_1);
  let xb = x.get_cloned(b_1);
  if xa.ltsb(xb) {
    std::mem::drop(y);
    std::mem::drop(x);
    true
  } else {
    if xa == xb {
      std::mem::drop(x);
      let tmp = y.get_cloned(a_1);
      let tmp_1 = y.get_cloned(b_1);
      std::mem::drop(y);
      tmp.lesb(tmp_1)
    } else {
      std::mem::drop(y);
      std::mem::drop(x);
      false
    }
  }
}

// Rocq: Convexhull.convexhull_implem.take_left
// Variant: uncurried
pub fn take_left(x: Array<Int63>, y: Array<Int63>, src: Array<Int63>, mid: Int63, hi: Int63, i: Int63, j: Int63) -> bool {
  if i < mid {
    if j < hi {
      let tmp = src.get_cloned(i);
      let tmp_1 = src.get_cloned(j);
      std::mem::drop(src);
      le_pt(x, y, tmp, tmp_1)
    } else {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(src);
      true
    }
  } else {
    std::mem::drop(x);
    std::mem::drop(y);
    std::mem::drop(src);
    false
  }
}

// Rocq: Convexhull.convexhull_implem.merge
// Variant: uncurried
pub fn merge_1(x: Array<Int63>, y: Array<Int63>, src: Array<Int63>, mid: Int63, hi: Int63, i: Int63, j: Int63, k: Int63, dst: Array<Int63>) -> Array<Int63> {
  merge(x, y, src, mid, hi, i, j, k, dst, ())
}

// Rocq: Convexhull.convexhull_implem.merge (local: merge)
// Variant: uncurried, lifted
pub fn merge(x: Array<Int63>, y: Array<Int63>, src: Array<Int63>, mid: Int63, hi: Int63, i: Int63, j: Int63, k: Int63, dst: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = k < hi;
  match bdec(tmp) {
    sumbool::left => {
      let x_clone = Clone::clone(&x);
      let y_clone = Clone::clone(&y);
      let src_clone = Clone::clone(&src);
      if take_left(x_clone, y_clone, src_clone, mid, hi, i, j) {
        let tmp_1 = i + int63!(1);
        let tmp_2 = k + int63!(1);
        let tmp_3 = src.get_cloned(i);
        merge(x, y, src, mid, hi, tmp_1, j, tmp_2, dst.set(k, tmp_3), ())
      } else {
        let tmp_4 = j + int63!(1);
        let tmp_5 = k + int63!(1);
        let tmp_6 = src.get_cloned(j);
        merge(x, y, src, mid, hi, i, tmp_4, tmp_5, dst.set(k, tmp_6), ())
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Convexhull.convexhull_implem.pass
// Variant: uncurried
pub fn pass_1(x: Array<Int63>, y: Array<Int63>, src: Array<Int63>, w: Int63, n: Int63, lo: Int63, dst: Array<Int63>) -> Array<Int63> {
  pass(x, y, src, w, n, lo, dst, ())
}

// Rocq: Convexhull.convexhull_implem.pass (local: pass)
// Variant: uncurried, lifted
pub fn pass(x: Array<Int63>, y: Array<Int63>, src: Array<Int63>, w: Int63, n: Int63, lo: Int63, dst: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = lo + w;
  let tmp_1 = lo < min_i(tmp + w, n);
  match bdec(tmp_1) {
    sumbool::left => {
      let tmp_2 = min_i(lo + w + w, n);
      let tmp_3 = min_i(lo + w, n);
      let tmp_4 = min_i(lo + w + w, n);
      let tmp_5 = min_i(lo + w, n);
      let x_clone = Clone::clone(&x);
      let y_clone = Clone::clone(&y);
      let src_clone = Clone::clone(&src);
      pass(x, y, src, w, n, tmp_2, merge_1(x_clone, y_clone, src_clone, tmp_3, tmp_4, lo, tmp_5, lo, dst), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Convexhull.convexhull_implem.sortl
// Variant: uncurried
pub fn sortl_1(x: Array<Int63>, y: Array<Int63>, n: Int63, w: Int63, src: Array<Int63>, dst: Array<Int63>) -> Array<Int63> {
  sortl(x, y, n, w, src, dst, ())
}

// Rocq: Convexhull.convexhull_implem.sortl (local: sortl)
// Variant: uncurried, lifted
pub fn sortl(x: Array<Int63>, y: Array<Int63>, n: Int63, w: Int63, src: Array<Int63>, dst: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = w < n;
  let tmp_1 = w + w;
  let tmp_2 = andb(tmp, w < tmp_1);
  match bdec(tmp_2) {
    sumbool::left => {
      let tmp_3 = w + w;
      let x_clone = Clone::clone(&x);
      let y_clone = Clone::clone(&y);
      let src_clone = Clone::clone(&src);
      let tmp_4 = pass_1(x_clone, y_clone, src_clone, w, n, int63!(0), dst);
      sortl(x, y, n, tmp_3, tmp_4, src, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(dst);
      src
    },
  }
}

// Rocq: Convexhull.convexhull_implem.initl
// Variant: uncurried
pub fn initl_1(n: Int63, i: Int63, a_1: Array<Int63>) -> Array<Int63> {
  initl(n, i, a_1, ())
}

// Rocq: Convexhull.convexhull_implem.initl (local: initl)
// Variant: uncurried, lifted
pub fn initl(n: Int63, i: Int63, a_1: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      initl(n, i + int63!(1), a_1.set(i, i), ())
    },
    sumbool::right => {
      a_1
    },
  }
}

// Rocq: Convexhull.convexhull_implem.msort
// Variant: uncurried
pub fn msort(x: Array<Int63>, y: Array<Int63>, n: Int63) -> Array<Int63> {
  let tmp = Array::<Int63>::make(n, int63!(0));
  let tmp_1 = initl_1(n, int63!(0), tmp);
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  sortl_1(x, y, n, int63!(1), tmp_1, tmp_2)
}

// Rocq: Convexhull.convexhull_implem.cross_m
// Variant: uncurried
pub fn cross_m(x: Array<Int63>, y: Array<Int63>, a_1: Int63, b_1: Int63, c: Int63) -> Int63 {
  let xa = x.get_cloned(a_1);
  let ya = y.get_cloned(a_1);
  let tmp = x.get_cloned(b_1);
  let tmp_1 = tmp - xa;
  let tmp_2 = y.get_cloned(c);
  let tmp_3 = tmp_1 * (tmp_2 - ya);
  let tmp_4 = y.get_cloned(b_1);
  std::mem::drop(y);
  let tmp_5 = tmp_4 - ya;
  let tmp_6 = x.get_cloned(c);
  std::mem::drop(x);
  tmp_3 - tmp_5 * (tmp_6 - xa)
}

// Rocq: Convexhull.convexhull_implem.pop
// Variant: uncurried
pub fn pop_1(x: Array<Int63>, y: Array<Int63>, st: Array<Int63>, lim: Int63, k: Int63, q: Int63) -> Int63 {
  pop(x, y, st, lim, k, q, ())
}

// Rocq: Convexhull.convexhull_implem.pop (local: pop)
// Variant: uncurried, lifted
pub fn pop(x: Array<Int63>, y: Array<Int63>, st: Array<Int63>, lim: Int63, k: Int63, q: Int63, _H: ()) -> Int63 {
  let tmp = lim < k;
  let tmp_1 = st.get_cloned(k - int63!(2));
  let tmp_2 = st.get_cloned(k - int63!(1));
  let x_clone = Clone::clone(&x);
  let y_clone = Clone::clone(&y);
  let tmp_3 = andb(tmp, cross_m(x_clone, y_clone, tmp_1, tmp_2, q).lesb(int63!(0)));
  match bdec(tmp_3) {
    sumbool::left => {
      pop(x, y, st, lim, k - int63!(1), q, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(st);
      k
    },
  }
}

// Rocq: Convexhull.convexhull_implem.lower
// Variant: uncurried
pub fn lower_1(x: Array<Int63>, y: Array<Int63>, ord: Array<Int63>, st: Array<Int63>, n: Int63, k: Int63, i: Int63) -> (Array<Int63>, Int63) {
  lower(x, y, ord, st, n, k, i, ())
}

// Rocq: Convexhull.convexhull_implem.lower (local: lower)
// Variant: uncurried, lifted
pub fn lower(x: Array<Int63>, y: Array<Int63>, ord: Array<Int63>, st: Array<Int63>, n: Int63, k: Int63, i: Int63, _H: ()) -> (Array<Int63>, Int63) {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let q = ord.get_cloned(i);
      let x_clone = Clone::clone(&x);
      let y_clone = Clone::clone(&y);
      let st_clone = Clone::clone(&st);
      let k_ = pop_1(x_clone, y_clone, st_clone, int63!(1), k, q);
      lower(x, y, ord, st.set(k_, q), n, k_ + int63!(1), i + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(ord);
      (st, k)
    },
  }
}

// Rocq: Convexhull.convexhull_implem.upper
// Variant: uncurried
pub fn upper_1(x: Array<Int63>, y: Array<Int63>, ord: Array<Int63>, st: Array<Int63>, lim: Int63, k: Int63, j: Int63) -> (Array<Int63>, Int63) {
  upper(x, y, ord, st, lim, k, j, ())
}

// Rocq: Convexhull.convexhull_implem.upper (local: upper)
// Variant: uncurried, lifted
pub fn upper(x: Array<Int63>, y: Array<Int63>, ord: Array<Int63>, st: Array<Int63>, lim: Int63, k: Int63, j: Int63, _H: ()) -> (Array<Int63>, Int63) {
  let tmp = int63!(0) < j;
  match bdec(tmp) {
    sumbool::left => {
      let q = ord.get_cloned(j - int63!(1));
      let x_clone = Clone::clone(&x);
      let y_clone = Clone::clone(&y);
      let st_clone = Clone::clone(&st);
      let k_ = pop_1(x_clone, y_clone, st_clone, lim, k, q);
      upper(x, y, ord, st.set(k_, q), lim, k_ + int63!(1), j - int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(ord);
      (st, k)
    },
  }
}

// Rocq: Convexhull.convexhull_implem.copyl
// Variant: uncurried
pub fn copyl_1(src: Array<Int63>, dst: Array<Int63>, h: Int63, i: Int63) -> Array<Int63> {
  copyl(src, dst, h, i, ())
}

// Rocq: Convexhull.convexhull_implem.copyl (local: copyl)
// Variant: uncurried, lifted
pub fn copyl(src: Array<Int63>, dst: Array<Int63>, h: Int63, i: Int63, _H: ()) -> Array<Int63> {
  let tmp = i < h;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = src.get_cloned(i);
      copyl(src, dst.set(i, tmp_1), h, i + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Convexhull.convexhull_implem.hull
// Variant: uncurried
pub fn hull(x: Array<Int63>, y: Array<Int63>) -> Array<Int63> {
  let n = x.length();
  let x_clone = Clone::clone(&x);
  let y_clone = Clone::clone(&y);
  let ord = msort(x_clone, y_clone, n);
  let a_1 = ord.get_cloned(int63!(0));
  let b_1 = ord.get_cloned(n - int63!(1));
  let tmp = x.get_cloned(a_1);
  let tmp_1 = x.get_cloned(b_1);
  let tmp_2 = tmp == tmp_1;
  let tmp_3 = y.get_cloned(a_1);
  let tmp_4 = y.get_cloned(b_1);
  let tmp_5 = tmp_3 == tmp_4;
  if andb(tmp_2, tmp_5) {
    std::mem::drop(y);
    std::mem::drop(x);
    std::mem::drop(ord);
    Array::<Int63>::make(int63!(1), a_1)
  } else {
    let tmp_6 = Array::<Int63>::make(n + n, int63!(0)).set(int63!(0), a_1);
    let x_clone_1 = Clone::clone(&x);
    let y_clone_1 = Clone::clone(&y);
    let ord_clone = Clone::clone(&ord);
    let tmp_7 = lower_1(x_clone_1, y_clone_1, ord_clone, tmp_6, n, int63!(1), int63!(1));
    match &tmp_7 {
      (l, st1) => {
        let tmp_8 = n - int63!(1);
        let l_clone = Clone::clone(l);
        let st1_clone = Clone::clone(st1);
        let st1_clone_1 = Clone::clone(st1);
        std::mem::drop(tmp_7);
        let tmp_9 = upper_1(x, y, ord, l_clone, st1_clone, st1_clone_1, tmp_8);
        match tmp_9 {
          (v152, v154) => {
            copyl_1(v152, Array::<Int63>::make(v154 - int63!(1), int63!(0)), v154 - int63!(1), int63!(0))
          },
        }
      },
    }
  }
}
