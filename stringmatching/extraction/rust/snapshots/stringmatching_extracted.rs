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

pub type buffer = (Array<Int63>, Array<Int63>);

pub type char63 = Int63;

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: rocq_string::RocqString) -> Int63 {
  let tmp = v0.length();
  std::mem::drop(v0);
  tmp
}

// Rocq: Stringmatching.stringmatching_implem.bmake
pub fn bmake(n: Int63) -> (Array<Int63>, Array<Int63>) {
  let tmp = Array::<Int63>::make(n, int63!(0));
  let tmp_1 = int63!(4194303);
  let tmp_2 = if tmp_1 < n {
    n - int63!(4194303)
  } else {
    int63!(0)
  };
  (tmp, Array::<Int63>::make(tmp_2, int63!(0)))
}

// Rocq: Stringmatching.stringmatching_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: rocq_string::RocqString, v1: Int63) -> Int63 {
  let tmp = v0.get(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Stringmatching.stringmatching_implem.fall
// Variant: uncurried
pub fn fall_1(xp: rocq_string::RocqString, tbl: Array<Int63>, c: Int63, q: Int63) -> Int63 {
  fall(xp, tbl, c, q, ())
}

// Rocq: Stringmatching.stringmatching_implem.fall (local: fall)
// Variant: uncurried, lifted
pub fn fall(xp: rocq_string::RocqString, tbl: Array<Int63>, c: Int63, q: Int63, _H: ()) -> Int63 {
  let xp_clone = Clone::clone(&xp);
  let tmp = get(xp_clone, q);
  if tmp == c {
    std::mem::drop(xp);
    std::mem::drop(tbl);
    q + int63!(1)
  } else {
    let tmp_1 = int63!(0) < q;
    match bdec(tmp_1) {
      sumbool::left => {
        let q_ = tbl.get_cloned(q - int63!(1));
        let tmp_2 = q_ < q;
        match bdec(tmp_2) {
          sumbool::left => {
            fall(xp, tbl, c, q_, ())
          },
          sumbool::right => {
            std::mem::drop(xp);
            std::mem::drop(tbl);
            int63!(0)
          },
        }
      },
      sumbool::right => {
        std::mem::drop(xp);
        std::mem::drop(tbl);
        int63!(0)
      },
    }
  }
}

// Rocq: Stringmatching.stringmatching_implem.build
// Variant: uncurried
pub fn build_1(xp: rocq_string::RocqString, m: Int63, tbl: Array<Int63>, i: Int63, q: Int63) -> Array<Int63> {
  build(xp, m, tbl, i, q, ())
}

// Rocq: Stringmatching.stringmatching_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(xp: rocq_string::RocqString, m: Int63, tbl: Array<Int63>, i: Int63, q: Int63, _H: ()) -> Array<Int63> {
  let tmp = i < m;
  match bdec(tmp) {
    sumbool::left => {
      let xp_clone = Clone::clone(&xp);
      let tmp_1 = get(xp_clone, i);
      let xp_clone_1 = Clone::clone(&xp);
      let tbl_clone = Clone::clone(&tbl);
      let r = fall_1(xp_clone_1, tbl_clone, tmp_1, q);
      build(xp, m, tbl.set(i, r), i + int63!(1), r, ())
    },
    sumbool::right => {
      std::mem::drop(xp);
      tbl
    },
  }
}

// Rocq: Stringmatching.stringmatching_implem.alen
pub fn alen_owned(a_1: Array<Int63>) -> Int63 {
  let tmp = a_1.length();
  std::mem::drop(a_1);
  tmp
}

// Rocq: Stringmatching.stringmatching_implem.alen
// Variant: borrowed
pub fn alen(a_1: &Array<Int63>) -> Int63 {
  a_1.length()
}

// Rocq: Stringmatching.stringmatching_implem.bset
// Variant: uncurried
pub fn bset(t: (Array<Int63>, Array<Int63>), i: Int63, v: Int63) -> (Array<Int63>, Array<Int63>) {
  match t {
    (v4, v6) => {
      let b_1 = &v4;
      let tmp = alen(b_1);
      if i < tmp {
        (v4.set(i, v), v6)
      } else {
        let tmp_1 = alen(b_1);
        (v4, v6.set(i - tmp_1, v))
      }
    },
  }
}

// Rocq: Stringmatching.stringmatching_implem.bget
// Variant: uncurried
pub fn bget(t: (Array<Int63>, Array<Int63>), i: Int63) -> Int63 {
  match t {
    (v3, v5) => {
      let b_1 = &v3;
      let a_1 = &v5;
      let tmp = alen(b_1);
      if i < tmp {
        std::mem::drop(v5);
        let tmp_1 = b_1.get_cloned(i);
        std::mem::drop(v3);
        tmp_1
      } else {
        let tmp_2 = a_1.get_cloned(i - alen_owned(v3));
        std::mem::drop(v5);
        tmp_2
      }
    },
  }
}

// Rocq: Stringmatching.stringmatching_implem.copy
// Variant: uncurried
pub fn copy_1(buf: (Array<Int63>, Array<Int63>), res: (Array<Int63>, Array<Int63>), c: Int63, k: Int63) -> (Array<Int63>, Array<Int63>) {
  copy(buf, res, c, k, ())
}

// Rocq: Stringmatching.stringmatching_implem.copy (local: copy)
// Variant: uncurried, lifted
pub fn copy(buf: (Array<Int63>, Array<Int63>), res: (Array<Int63>, Array<Int63>), c: Int63, k: Int63, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = k < c;
  match bdec(tmp) {
    sumbool::left => {
      let buf_clone = Clone::clone(&buf);
      let tmp_1 = bget(buf_clone, k);
      copy(buf, bset(res, k, tmp_1), c, k + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(buf);
      res
    },
  }
}

// Rocq: Stringmatching.stringmatching_implem.scan
// Variant: uncurried
pub fn scan_1(xp: rocq_string::RocqString, xt: rocq_string::RocqString, tbl: Array<Int63>, m: Int63, n: Int63, buf: (Array<Int63>, Array<Int63>), i: Int63, q: Int63, cnt: Int63) -> (Array<Int63>, Array<Int63>) {
  scan(xp, xt, tbl, m, n, buf, i, q, cnt, ())
}

// Rocq: Stringmatching.stringmatching_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(xp: rocq_string::RocqString, xt: rocq_string::RocqString, tbl: Array<Int63>, m: Int63, n: Int63, buf: (Array<Int63>, Array<Int63>), i: Int63, q: Int63, cnt: Int63, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let xt_clone = Clone::clone(&xt);
      let tmp_1 = get(xt_clone, i);
      let xp_clone = Clone::clone(&xp);
      let tbl_clone = Clone::clone(&tbl);
      let r = fall_1(xp_clone, tbl_clone, tmp_1, q);
      if r == m {
        let tmp_2 = bset(buf, cnt, i + int63!(1) - m);
        let tmp_3 = i + int63!(1);
        let tmp_4 = tbl.get_cloned(m - int63!(1));
        scan(xp, xt, tbl, m, n, tmp_2, tmp_3, tmp_4, cnt + int63!(1), ())
      } else {
        scan(xp, xt, tbl, m, n, buf, i + int63!(1), r, cnt, ())
      }
    },
    sumbool::right => {
      std::mem::drop(xp);
      std::mem::drop(xt);
      std::mem::drop(tbl);
      copy_1(buf, bmake(cnt), cnt, int63!(0))
    },
  }
}

// Rocq: Stringmatching.stringmatching_implem.find_all_impl
// Variant: uncurried
pub fn find_all_impl(xp: rocq_string::RocqString, xt: rocq_string::RocqString) -> (Array<Int63>, Array<Int63>) {
  let xp_clone = Clone::clone(&xp);
  let m = length(xp_clone);
  let xt_clone = Clone::clone(&xt);
  let n = length(xt_clone);
  if n < m {
    std::mem::drop(xp);
    std::mem::drop(xt);
    bmake(int63!(0))
  } else {
    let tmp = Array::<Int63>::make(m, int63!(0));
    let xp_clone_1 = Clone::clone(&xp);
    let tbl = build_1(xp_clone_1, m, tmp, int63!(1), int63!(0));
    let tmp_1 = n - m;
    scan_1(xp, xt, tbl, m, n, bmake(tmp_1 + int63!(1)), int63!(0), int63!(0), int63!(0))
  }
}
