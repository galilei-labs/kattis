#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

pub enum sres {
  SFound { v: Int63, qp: Array<Int63>, pr: Array<Int63> },
  SCont { Q: Array<Int63>, qp: Array<Int63>, pr: Array<Int63>, t: Int63 },
}

impl Clone for sres {
  fn clone(&self) -> Self {
    match self {
      sres::SFound { v: __field0, qp: __field1, pr: __field2 } => sres::SFound { v: Clone::clone(__field0), qp: Clone::clone(__field1), pr: Clone::clone(__field2) },
      sres::SCont { Q: __field0, qp: __field1, pr: __field2, t: __field3 } => sres::SCont { Q: Clone::clone(__field0), qp: Clone::clone(__field1), pr: Clone::clone(__field2), t: Clone::clone(__field3) },
    }
  }
}

pub enum bres {
  BFound { v: Int63, qp: Array<Int63>, pr: Array<Int63> },
  BFail { qp: Array<Int63>, pr: Array<Int63> },
}

impl Clone for bres {
  fn clone(&self) -> Self {
    match self {
      bres::BFound { v: __field0, qp: __field1, pr: __field2 } => bres::BFound { v: Clone::clone(__field0), qp: Clone::clone(__field1), pr: Clone::clone(__field2) },
      bres::BFail { qp: __field0, pr: __field1 } => bres::BFail { qp: Clone::clone(__field0), pr: Clone::clone(__field1) },
    }
  }
}

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = Int63;

// Rocq: Bilateral.bilateral_implem.NV
pub fn NV() -> Int63 {
  int63!(1000)
}

// Rocq: Bilateral.bilateral_implem.NP
pub fn NP() -> Int63 {
  int63!(1001)
}

// Rocq: Bilateral.bilateral_implem.NM
pub fn NM() -> Int63 {
  int63!(2000)
}

// Rocq: Bilateral.bilateral_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Bilateral.bilateral_implem.deg_loop
// Variant: uncurried
pub fn deg_loop_1(x: Array<Int63>, ex: Int63, m: Int63, k: Int63, d: Array<Int63>) -> Array<Int63> {
  deg_loop(x, ex, m, k, d, ())
}

// Rocq: Bilateral.bilateral_implem.deg_loop (local: deg_loop)
// Variant: uncurried, lifted
pub fn deg_loop(x: Array<Int63>, ex: Int63, m: Int63, k: Int63, d: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = k < m;
  match bdec(tmp) {
    sumbool::left => {
      let a_1 = x.get_cloned(k);
      let tmp_1 = k + int63!(1);
      let tmp_2 = if a_1 == ex {
        d
      } else {
        let u = a_1 - int63!(1000);
        let tmp_3 = d.get_cloned(u);
        d.set(u, tmp_3 + int63!(1))
      };
      deg_loop(x, ex, m, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      d
    },
  }
}

// Rocq: Bilateral.bilateral_implem.off_loop
// Variant: uncurried
pub fn off_loop_1(d: Array<Int63>, u: Int63, o: Array<Int63>) -> Array<Int63> {
  off_loop(d, u, o, ())
}

// Rocq: Bilateral.bilateral_implem.off_loop (local: off_loop)
// Variant: uncurried, lifted
pub fn off_loop(d: Array<Int63>, u: Int63, o: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = u < __rocq_global_132;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = u + int63!(1);
      let tmp_2 = u + int63!(1);
      let tmp_3 = o.get_cloned(u);
      let tmp_4 = d.get_cloned(u);
      off_loop(d, tmp_1, o.set(tmp_2, tmp_3 + tmp_4), ())
    },
    sumbool::right => {
      std::mem::drop(d);
      o
    },
  }
}

// Rocq: Bilateral.bilateral_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(x: Array<Int63>, y: Array<Int63>, ex: Int63, m: Int63, k: Int63, pos: Array<Int63>, tg: Array<Int63>) -> Array<Int63> {
  fill_loop(x, y, ex, m, k, pos, tg, ())
}

// Rocq: Bilateral.bilateral_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(x: Array<Int63>, y: Array<Int63>, ex: Int63, m: Int63, k: Int63, pos: Array<Int63>, tg: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = k < m;
  match bdec(tmp) {
    sumbool::left => {
      let a_1 = x.get_cloned(k);
      if a_1 == ex {
        fill_loop(x, y, ex, m, k + int63!(1), pos, tg, ())
      } else {
        let u = a_1 - int63!(1000);
        let p = pos.get_cloned(u);
        let tmp_1 = k + int63!(1);
        let tmp_2 = pos.set(u, p + int63!(1));
        let tmp_3 = y.get_cloned(k);
        fill_loop(x, y, ex, m, tmp_1, tmp_2, tg.set(p, tmp_3 - int63!(2000)), ())
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(pos);
      tg
    },
  }
}

// Rocq: Bilateral.bilateral_implem.root_loop
// Variant: uncurried
pub fn root_loop_1(mL: Array<Int63>, u: Int63, Q: Array<Int63>, qp: Array<Int63>, t: Int63) -> ((Array<Int63>, Array<Int63>), Int63) {
  root_loop(mL, u, Q, qp, t, ())
}

// Rocq: Bilateral.bilateral_implem.root_loop (local: root_loop)
// Variant: uncurried, lifted
pub fn root_loop(mL: Array<Int63>, u: Int63, Q: Array<Int63>, qp: Array<Int63>, t: Int63, _H: ()) -> ((Array<Int63>, Array<Int63>), Int63) {
  let tmp = u < __rocq_global_132;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = mL.get_cloned(u);
      if tmp_1 < __rocq_global_132 {
        root_loop(mL, u + int63!(1), Q, qp, t, ())
      } else {
        root_loop(mL, u + int63!(1), Q.set(t, u), qp.set(u, t + int63!(1)), t + int63!(1), ())
      }
    },
    sumbool::right => {
      std::mem::drop(mL);
      ((Q, qp), t)
    },
  }
}

// Rocq: Bilateral.bilateral_implem.scan
// Variant: uncurried
pub fn scan_1(tg: Array<Int63>, mR: Array<Int63>, u: Int63, pe: Int63, p: Int63, Q: Array<Int63>, qp: Array<Int63>, pr: Array<Int63>, t: Int63) -> Rc<sres> {
  scan(tg, mR, u, pe, p, Q, qp, pr, t, ())
}

// Rocq: Bilateral.bilateral_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(tg: Array<Int63>, mR: Array<Int63>, u: Int63, pe: Int63, p: Int63, Q: Array<Int63>, qp: Array<Int63>, pr: Array<Int63>, t: Int63, _H: ()) -> Rc<sres> {
  let tmp = p < pe;
  match bdec(tmp) {
    sumbool::left => {
      let v = tg.get_cloned(p);
      let tmp_1 = pr.get_cloned(v);
      if tmp_1 == int63!(0) {
        let pr_1 = pr.set(v, u + int63!(1));
        let w = mR.get_cloned(v);
        if w < __rocq_global_132 {
          let tmp_2 = qp.get_cloned(w);
          if tmp_2 == int63!(0) {
            scan(tg, mR, u, pe, p + int63!(1), Q.set(t, w), qp.set(w, t + int63!(1)), pr_1, t + int63!(1), ())
          } else {
            scan(tg, mR, u, pe, p + int63!(1), Q, qp, pr_1, t, ())
          }
        } else {
          std::mem::drop(tg);
          std::mem::drop(mR);
          std::mem::drop(Q);
          Rc::new(sres::SFound { v, qp, pr: pr_1 })
        }
      } else {
        scan(tg, mR, u, pe, p + int63!(1), Q, qp, pr, t, ())
      }
    },
    sumbool::right => {
      std::mem::drop(tg);
      std::mem::drop(mR);
      Rc::new(sres::SCont { Q, qp, pr, t })
    },
  }
}

// Rocq: Bilateral.bilateral_implem.bfs
// Variant: uncurried
pub fn bfs_1(off: Array<Int63>, tg: Array<Int63>, mR: Array<Int63>, h: Int63, t: Int63, Q: Array<Int63>, qp: Array<Int63>, pr: Array<Int63>) -> Rc<bres> {
  bfs(off, tg, mR, h, t, Q, qp, pr, ())
}

// Rocq: Bilateral.bilateral_implem.bfs (local: bfs)
// Variant: uncurried, lifted
pub fn bfs(off: Array<Int63>, tg: Array<Int63>, mR: Array<Int63>, h: Int63, t: Int63, Q: Array<Int63>, qp: Array<Int63>, pr: Array<Int63>, _H: ()) -> Rc<bres> {
  let tmp = h < __rocq_global_132;
  match bdec(tmp) {
    sumbool::left => {
      if h < t {
        let u = Q.get_cloned(h);
        let tmp_1 = off.get_cloned(u + int63!(1));
        let tmp_2 = off.get_cloned(u);
        let tg_clone = Clone::clone(&tg);
        let mR_clone = Clone::clone(&mR);
        let tmp_3 = scan_1(tg_clone, mR_clone, u, tmp_1, tmp_2, Q, qp, pr, t);
        let (v70, v71) = __rocq_reuse::reset(tmp_3, |__payload| Clone::clone(__payload));
        std::mem::drop(v71);
        match v70 {
          sres::SFound { v: v82, qp: v84, pr: v86 } => {
            std::mem::drop(tg);
            std::mem::drop(mR);
            std::mem::drop(off);
            Rc::new(bres::BFound { v: v82, qp: v84, pr: v86 })
          },
          sres::SCont { Q: v99, qp: v101, pr: v103, t: v105 } => {
            bfs(off, tg, mR, h + int63!(1), v105, v99, v101, v103, ())
          },
        }
      } else {
        std::mem::drop(off);
        std::mem::drop(tg);
        std::mem::drop(mR);
        std::mem::drop(Q);
        Rc::new(bres::BFail { qp, pr })
      }
    },
    sumbool::right => {
      std::mem::drop(off);
      std::mem::drop(tg);
      std::mem::drop(mR);
      std::mem::drop(Q);
      Rc::new(bres::BFail { qp, pr })
    },
  }
}

// Rocq: Bilateral.bilateral_implem.walk
// Variant: uncurried
pub fn walk_1(qp: Array<Int63>, pr: Array<Int63>, v: Int63, mL: Array<Int63>, mR: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  walk(qp, pr, v, mL, mR, ())
}

// Rocq: Bilateral.bilateral_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(qp: Array<Int63>, pr: Array<Int63>, v: Int63, mL: Array<Int63>, mR: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = pr.get_cloned(v);
  let u = tmp - int63!(1);
  let old = mL.get_cloned(u);
  let mL_ = mL.set(u, v);
  let mR_ = mR.set(v, u);
  if old < __rocq_global_132 {
    let tmp_1 = pr.get_cloned(old);
    let tmp_2 = qp.get_cloned(tmp_1 - int63!(1));
    let tmp_3 = pr.get_cloned(v);
    let tmp_4 = qp.get_cloned(tmp_3 - int63!(1));
    let tmp_5 = tmp_2 < tmp_4;
    match bdec(tmp_5) {
      sumbool::left => {
        walk(qp, pr, old, mL_, mR_, ())
      },
      sumbool::right => {
        std::mem::drop(qp);
        std::mem::drop(pr);
        (mL_, mR_)
      },
    }
  } else {
    std::mem::drop(qp);
    std::mem::drop(pr);
    (mL_, mR_)
  }
}

// Rocq: Bilateral.bilateral_implem.phases
// Variant: uncurried
pub fn phases_1(off: Array<Int63>, tg: Array<Int63>, it: Int63, mL: Array<Int63>, mR: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  phases(off, tg, it, mL, mR, ())
}

// Rocq: Bilateral.bilateral_implem.phases (local: phases)
// Variant: uncurried, lifted
pub fn phases(off: Array<Int63>, tg: Array<Int63>, it: Int63, mL: Array<Int63>, mR: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = it < __rocq_global_182;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = Array::<Int63>::make(__rocq_global_132, int63!(0));
      let tmp_2 = Array::<Int63>::make(__rocq_global_132, int63!(0));
      let mL_clone = Clone::clone(&mL);
      let tmp_3 = root_loop_1(mL_clone, int63!(0), tmp_1, tmp_2, int63!(0));
      match &tmp_3 {
        (t, p) => {
          match t {
            (qp, Q) => {
              let tmp_4 = Array::<Int63>::make(__rocq_global_132, int63!(0));
              let off_clone = Clone::clone(&off);
              let tg_clone = Clone::clone(&tg);
              let mR_clone = Clone::clone(&mR);
              let p_clone = Clone::clone(p);
              let qp_clone = Clone::clone(qp);
              let Q_clone = Clone::clone(Q);
              let tmp_5 = bfs_1(off_clone, tg_clone, mR_clone, int63!(0), p_clone, qp_clone, Q_clone, tmp_4);
              let (v93, v94) = __rocq_reuse::reset(tmp_5, |__payload| Clone::clone(__payload));
              std::mem::drop(v94);
              match v93 {
                bres::BFound { v: v103, qp: v105, pr: v107 } => {
                  std::mem::drop(tmp_3);
                  let tmp_6 = walk_1(v105, v107, v103, mL, mR);
                  match tmp_6 {
                    (v122, v124) => {
                      phases(off, tg, it + int63!(1), v122, v124, ())
                    },
                  }
                },
                bres::BFail { qp: v155, pr: v157 } => {
                  std::mem::drop(off);
                  std::mem::drop(tg);
                  std::mem::drop(mL);
                  std::mem::drop(mR);
                  std::mem::drop(tmp_3);
                  (v155, v157)
                },
              }
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(off);
      std::mem::drop(tg);
      std::mem::drop(mL);
      std::mem::drop(mR);
      (Array::<Int63>::make(__rocq_global_132, int63!(0)), Array::<Int63>::make(__rocq_global_132, int63!(0)))
    },
  }
}

// Rocq: Bilateral.bilateral_implem.mark_loop
// Variant: uncurried
pub fn mark_loop_1(qp: Array<Int63>, pr: Array<Int63>, i: Int63, mk: Array<Int63>) -> Array<Int63> {
  mark_loop(qp, pr, i, mk, ())
}

// Rocq: Bilateral.bilateral_implem.mark_loop (local: mark_loop)
// Variant: uncurried, lifted
pub fn mark_loop(qp: Array<Int63>, pr: Array<Int63>, i: Int63, mk: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < __rocq_global_707;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = __rocq_global_132;
      let tmp_3 = if i < tmp_2 {
        let tmp_4 = qp.get_cloned(i);
        if tmp_4 == int63!(0) {
          mk.set(i, int63!(1))
        } else {
          mk
        }
      } else {
        let tmp_5 = pr.get_cloned(i - __rocq_global_132);
        if tmp_5 == int63!(0) {
          mk
        } else {
          mk.set(i, int63!(1))
        }
      };
      mark_loop(qp, pr, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(qp);
      std::mem::drop(pr);
      mk
    },
  }
}

// Rocq: Bilateral.bilateral_implem.engine
// Variant: uncurried
pub fn engine(x: Array<Int63>, y: Array<Int63>, ex: Int63) -> Array<Int63> {
  let m = x.length();
  let tmp = Array::<Int63>::make(__rocq_global_132, int63!(0));
  let x_clone = Clone::clone(&x);
  let d = deg_loop_1(x_clone, ex, m, int63!(0), tmp);
  let tmp_1 = Array::<Int63>::make(__rocq_global_182, int63!(0));
  let d_clone = Clone::clone(&d);
  let off = off_loop_1(d_clone, int63!(0), tmp_1);
  let pos = off_loop_1(d, int63!(0), Array::<Int63>::make(__rocq_global_182, int63!(0)));
  let tmp_2 = Array::<Int63>::make(m, int63!(0));
  let tg = fill_loop_1(x, y, ex, m, int63!(0), pos, tmp_2);
  let tmp_3 = phases_1(off, tg, int63!(0), Array::<Int63>::make(__rocq_global_132, __rocq_global_132), Array::<Int63>::make(__rocq_global_132, __rocq_global_132));
  match tmp_3 {
    (v119, v121) => {
      mark_loop_1(v119, v121, int63!(0), Array::<Int63>::make(__rocq_global_707, int63!(0)))
    },
  }
}

// Rocq: Bilateral.bilateral_implem.out_loop
// Variant: uncurried
pub fn out_loop_1(mk: Array<Int63>, i: Int63, p: Int63, out: Array<Int63>) -> Array<Int63> {
  out_loop(mk, i, p, out, ())
}

// Rocq: Bilateral.bilateral_implem.out_loop (local: out_loop)
// Variant: uncurried, lifted
pub fn out_loop(mk: Array<Int63>, i: Int63, p: Int63, out: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < __rocq_global_707;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = mk.get_cloned(i);
      if tmp_1 == int63!(0) {
        out_loop(mk, i + int63!(1), p, out, ())
      } else {
        out_loop(mk, i + int63!(1), p + int63!(1), out.set(p, int63!(1000) + i), ())
      }
    },
    sumbool::right => {
      std::mem::drop(mk);
      out
    },
  }
}

// Rocq: Bilateral.bilateral_implem.cnt_loop
// Variant: uncurried
pub fn cnt_loop_1(mk: Array<Int63>, i: Int63, c: Int63) -> Int63 {
  cnt_loop(mk, i, c, ())
}

// Rocq: Bilateral.bilateral_implem.cnt_loop (local: cnt_loop)
// Variant: uncurried, lifted
pub fn cnt_loop(mk: Array<Int63>, i: Int63, c: Int63, _H: ()) -> Int63 {
  let tmp = i < __rocq_global_707;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = mk.get_cloned(i);
      let tmp_3 = int63!(0);
      let tmp_4 = if tmp_2 == tmp_3 {
        c
      } else {
        c + int63!(1)
      };
      cnt_loop(mk, tmp_1, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(mk);
      c
    },
  }
}

// Rocq: Bilateral.bilateral_implem.count_marks
pub fn count_marks(mk: Array<Int63>) -> Int63 {
  cnt_loop_1(mk, int63!(0), int63!(0))
}

// Rocq: Bilateral.bilateral_implem.build
pub fn build(mk: Array<Int63>) -> Array<Int63> {
  let mk_clone = Clone::clone(&mk);
  out_loop_1(mk, int63!(0), int63!(0), Array::<Int63>::make(count_marks(mk_clone), int63!(0)))
}

// Rocq: Bilateral.bilateral_implem.bilateral_impl
// Variant: uncurried
pub fn bilateral_impl(x: Array<Int63>, y: Array<Int63>) -> Array<Int63> {
  let x_clone = Clone::clone(&x);
  let y_clone = Clone::clone(&y);
  let mk1 = engine(x_clone, y_clone, int63!(1009));
  let mk0 = engine(x, y, int63!(0));
  let mk1_clone = Clone::clone(&mk1);
  let tmp = count_marks(mk1_clone) + int63!(1);
  let mk0_clone = Clone::clone(&mk0);
  let tmp_1 = count_marks(mk0_clone);
  let tmp_2 = if tmp <= tmp_1 {
    std::mem::drop(mk0);
    mk1.set(int63!(9), int63!(1))
  } else {
    std::mem::drop(mk1);
    mk0
  };
  build(tmp_2)
}
const __rocq_global_132: Int63 = int63!(1000);
const __rocq_global_182: Int63 = int63!(1001);
const __rocq_global_707: Int63 = int63!(2000);