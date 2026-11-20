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

// Rocq: Chatter.chatter_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Chatter.chatter_implem.init
// Variant: uncurried
pub fn init_1(n: Int63, i: Int63, rep: Array<Int63>, tl: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  init(n, i, rep, tl, ())
}

// Rocq: Chatter.chatter_implem.init (local: init)
// Variant: uncurried, lifted
pub fn init(n: Int63, i: Int63, rep: Array<Int63>, tl: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      init(n, i + int63!(1), rep.set(i, i), tl.set(i, i), ())
    },
    sumbool::right => {
      (rep, tl)
    },
  }
}

// Rocq: Chatter.chatter_implem.nx
// Variant: uncurried
pub fn nx(a_1: Int63, b_1: Int63, c: Int63, r: Int63) -> Int63 {
  (r * a_1 + b_1) % c
}

// Rocq: Chatter.chatter_implem.redraw
// Variant: uncurried
pub fn redraw_1(n: Int63, a_1: Int63, b_1: Int63, c: Int63, r: Int63, bud: Int63) -> ((Int63, Int63), Int63) {
  redraw(n, a_1, b_1, c, r, bud, ())
}

// Rocq: Chatter.chatter_implem.redraw (local: redraw)
// Variant: uncurried, lifted
pub fn redraw(n: Int63, a_1: Int63, b_1: Int63, c: Int63, r: Int63, bud: Int63, _H: ()) -> ((Int63, Int63), Int63) {
  let tmp = int63!(0) < bud;
  match bdec(tmp) {
    sumbool::left => {
      let r1 = nx(a_1, b_1, c, r);
      let r2 = nx(a_1, b_1, c, r1);
      let x = r1 % n;
      let y = r2 % n;
      if x == y {
        redraw(n, a_1, b_1, c, r2, bud - int63!(1), ())
      } else {
        ((r2, x), y)
      }
    },
    sumbool::right => {
      ((r, int63!(0)), int63!(0))
    },
  }
}

// Rocq: Chatter.chatter_implem.relabel
// Variant: uncurried
pub fn relabel_1(nxt: Array<Int63>, big: Int63, q: Int63, cnt: Int63, rep: Array<Int63>) -> Array<Int63> {
  relabel(nxt, big, q, cnt, rep, ())
}

// Rocq: Chatter.chatter_implem.relabel (local: relabel)
// Variant: uncurried, lifted
pub fn relabel(nxt: Array<Int63>, big: Int63, q: Int63, cnt: Int63, rep: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = int63!(0) < cnt;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = nxt.get_cloned(q);
      let tmp_2 = cnt - int63!(1);
      let tmp_3 = rep.set(q, big);
      relabel(nxt, big, tmp_1, tmp_2, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(nxt);
      rep
    },
  }
}

// Rocq: Chatter.chatter_implem.merge
// Variant: uncurried
pub fn merge(big: Int63, small: Int63, rep: Array<Int63>, nxt: Array<Int63>, tl: Array<Int63>, sz: Array<Int63>) -> (((Array<Int63>, Array<Int63>), Array<Int63>), Array<Int63>) {
  let tmp = sz.get_cloned(small);
  let nxt_clone = Clone::clone(&nxt);
  let rep_ = relabel_1(nxt_clone, big, small, tmp, rep);
  let tmp_1 = tl.get_cloned(big);
  let nxt_ = nxt.set(tmp_1, small);
  let tmp_2 = tl.get_cloned(small);
  let tl_ = tl.set(big, tmp_2);
  let tmp_3 = sz.get_cloned(big);
  let tmp_4 = sz.get_cloned(small);
  let sz_ = sz.set(big, tmp_3 + tmp_4);
  (((rep_, nxt_), tl_), sz_)
}

// Rocq: Chatter.chatter_implem.union
// Variant: uncurried
pub fn union(x: Int63, y: Int63, rep: Array<Int63>, nxt: Array<Int63>, tl: Array<Int63>, sz: Array<Int63>) -> (((Array<Int63>, Array<Int63>), Array<Int63>), Array<Int63>) {
  let px = rep.get_cloned(x);
  let py = rep.get_cloned(y);
  if px == py {
    (((rep, nxt), tl), sz)
  } else {
    let tmp = sz.get_cloned(py);
    let tmp_1 = sz.get_cloned(px);
    if tmp < tmp_1 {
      merge(px, py, rep, nxt, tl, sz)
    } else {
      merge(py, px, rep, nxt, tl, sz)
    }
  }
}

// Rocq: Chatter.chatter_implem.sim
// Variant: uncurried
pub fn sim_1(n: Int63, a_1: Int63, b_1: Int63, c: Int63, r: Int63, k: Int63, rep: Array<Int63>, nxt: Array<Int63>, tl: Array<Int63>, sz: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  sim(n, a_1, b_1, c, r, k, rep, nxt, tl, sz, ())
}

// Rocq: Chatter.chatter_implem.sim (local: sim)
// Variant: uncurried, lifted
pub fn sim(n: Int63, a_1: Int63, b_1: Int63, c: Int63, r: Int63, k: Int63, rep: Array<Int63>, nxt: Array<Int63>, tl: Array<Int63>, sz: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = int63!(0) < k;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = c + int63!(1);
      let tmp_2 = redraw_1(n, a_1, b_1, c, r, tmp_1);
      match tmp_2 {
        (v47, v49) => {
          match v47 {
            (v52, v54) => {
              let tmp_3 = union(v54, v49, rep, nxt, tl, sz);
              match tmp_3 {
                (v71, v73) => {
                  match v71 {
                    (v76, v78) => {
                      match v76 {
                        (v81, v83) => {
                          sim(n, a_1, b_1, c, v52, k - int63!(1), v81, v83, v78, v73, ())
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
    },
    sumbool::right => {
      std::mem::drop(nxt);
      std::mem::drop(tl);
      (rep, sz)
    },
  }
}

// Rocq: Chatter.chatter_implem.tally
// Variant: uncurried
pub fn tally_1(n: Int63, i: Int63, rep: Array<Int63>, sz: Array<Int63>, seen: Array<Int63>, cnt: Array<Int63>, g: Int63) -> (Int63, Array<Int63>) {
  tally(n, i, rep, sz, seen, cnt, g, ())
}

// Rocq: Chatter.chatter_implem.tally (local: tally)
// Variant: uncurried, lifted
pub fn tally(n: Int63, i: Int63, rep: Array<Int63>, sz: Array<Int63>, seen: Array<Int63>, cnt: Array<Int63>, g: Int63, _H: ()) -> (Int63, Array<Int63>) {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let ro = rep.get_cloned(i);
      let tmp_1 = seen.get_cloned(ro);
      if tmp_1 == int63!(0) {
        let s = sz.get_cloned(ro);
        let tmp_2 = i + int63!(1);
        let tmp_3 = seen.set(ro, int63!(1));
        let tmp_4 = cnt.get_cloned(s);
        tally(n, tmp_2, rep, sz, tmp_3, cnt.set(s, tmp_4 + int63!(1)), g + int63!(1), ())
      } else {
        tally(n, i + int63!(1), rep, sz, seen, cnt, g, ())
      }
    },
    sumbool::right => {
      std::mem::drop(rep);
      std::mem::drop(sz);
      std::mem::drop(seen);
      (g, cnt)
    },
  }
}

// Rocq: Chatter.chatter_implem.countd
// Variant: uncurried
pub fn countd_1(n: Int63, i: Int63, cnt: Array<Int63>, d: Int63) -> Int63 {
  countd(n, i, cnt, d, ())
}

// Rocq: Chatter.chatter_implem.countd (local: countd)
// Variant: uncurried, lifted
pub fn countd(n: Int63, i: Int63, cnt: Array<Int63>, d: Int63, _H: ()) -> Int63 {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = int63!(0);
      let tmp_3 = cnt.get_cloned(n - i);
      let tmp_4 = if tmp_2 < tmp_3 {
        d + int63!(1)
      } else {
        d
      };
      countd(n, tmp_1, cnt, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(cnt);
      d
    },
  }
}

// Rocq: Chatter.chatter_implem.fill
// Variant: uncurried
pub fn fill_1(n: Int63, i: Int63, j: Int63, cnt: Array<Int63>, out: Array<(Int63, Int63)>) -> Array<(Int63, Int63)> {
  fill(n, i, j, cnt, out, ())
}

// Rocq: Chatter.chatter_implem.fill (local: fill)
// Variant: uncurried, lifted
pub fn fill(n: Int63, i: Int63, j: Int63, cnt: Array<Int63>, out: Array<(Int63, Int63)>, _H: ()) -> Array<(Int63, Int63)> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let s = n - i;
      let v = cnt.get_cloned(s);
      if int63!(0) < v {
        fill(n, i + int63!(1), j + int63!(1), cnt, out.set(j, (s, v)), ())
      } else {
        fill(n, i + int63!(1), j, cnt, out, ())
      }
    },
    sumbool::right => {
      std::mem::drop(cnt);
      out
    },
  }
}

// Rocq: Chatter.chatter_implem.chatter_impl
// Variant: uncurried
pub fn chatter_impl(n: Int63, r: Int63, a_1: Int63, b_1: Int63, c: Int63) -> (Int63, Array<(Int63, Int63)>) {
  let tmp = Array::<Int63>::make(n, int63!(0));
  let tmp_1 = Array::<Int63>::make(n, int63!(0));
  let tmp_2 = init_1(n, int63!(0), tmp, tmp_1);
  match tmp_2 {
    (v32, v34) => {
      let tmp_3 = Array::<Int63>::make(n, int63!(0));
      let tmp_4 = Array::<Int63>::make(n, int63!(1));
      let tmp_5 = sim_1(n, a_1, b_1, c, r, n, v32, tmp_3, v34, tmp_4);
      match &tmp_5 {
        (sz, rep) => {
          let tmp_6 = int63!(0);
          let tmp_7 = Array::<Int63>::make(n, int63!(0));
          let tmp_8 = Array::<Int63>::make(n + int63!(1), int63!(0));
          let tmp_9 = int63!(0);
          let sz_clone = Clone::clone(sz);
          let rep_clone = Clone::clone(rep);
          std::mem::drop(tmp_5);
          let tmp_10 = tally_1(n, tmp_6, sz_clone, rep_clone, tmp_7, tmp_8, tmp_9);
          match tmp_10 {
            (v121, v123) => {
              let g = &v123;
              let g_clone = Clone::clone(g);
              let d = countd_1(n, int63!(0), g_clone, int63!(0));
              (v121, fill_1(n, int63!(0), int63!(0), v123, Array::<(Int63, Int63)>::make(d, (int63!(0), int63!(0)))))
            },
          }
        },
      }
    },
  }
}
