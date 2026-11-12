// Generated from OwnedANF. This printer is not verified.
#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub enum sres {
  SFound { v: u64, qp: Rc<Array<u64>>, pr: Rc<Array<u64>> },
  SCont { Q: Rc<Array<u64>>, qp: Rc<Array<u64>>, pr: Rc<Array<u64>>, t: u64 },
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
  BFound { v: u64, qp: Rc<Array<u64>>, pr: Rc<Array<u64>> },
  BFail { qp: Rc<Array<u64>>, pr: Rc<Array<u64>> },
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

pub type uint = u64;

// Rocq: Bilateral.bilateral_implem.NV
pub fn NV() -> u64 {
  1000u64
}

// Rocq: Bilateral.bilateral_implem.NP
pub fn NP() -> u64 {
  1001u64
}

// Rocq: Bilateral.bilateral_implem.NM
pub fn NM() -> u64 {
  2000u64
}

// Rocq: Bilateral.bilateral_implem.bilateral
// Variant: uncurried
pub fn bilateral() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>> = bilateral_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v0);
  v1
}

// Rocq: Bilateral.bilateral_implem.bilateral
pub fn bilateral_curried() -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> {
  let v0: fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = bilateral_impl_curried;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Bilateral.bilateral_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  match b {
    true => {
      sumbool::left
    },
    false => {
      sumbool::right
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Bilateral.bilateral_implem.deg_loop
// Variant: uncurried
pub fn deg_loop_1(x: Rc<Array<u64>>, ex: u64, m: u64, k: u64, d: Rc<Array<u64>>) -> Rc<Array<u64>> {
  deg_loop(x, ex, m, k, d, ())
}

// Rocq: Bilateral.bilateral_implem.deg_loop (local: deg_loop)
// Variant: uncurried, lifted
pub fn deg_loop(x: Rc<Array<u64>>, ex: u64, m: u64, k: u64, d: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v13 = ltb(k, m);
  match bdec(v13) {
    sumbool::left => {
      let v17 = &x;
      let a = rocq_array::get::<u64>(&v17, k);
      let v28 = add(k, 1u64);
      let v35 = match eqb(a, ex) {
        true => {
          d
        },
        false => {
          let u = sub(a, 1000u64);
          let v47 = &d;
          let v50 = rocq_array::get::<u64>(&v47, u);
          rocq_array::set::<u64>(d, u, add(v50, 1u64))
        },
      };
      deg_loop(x, ex, m, v28, v35, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      d
    },
  }
}

// Rocq: Bilateral.bilateral_implem.off_loop
// Variant: uncurried
pub fn off_loop_1(d: Rc<Array<u64>>, u: u64, o: Rc<Array<u64>>) -> Rc<Array<u64>> {
  off_loop(d, u, o, ())
}

// Rocq: Bilateral.bilateral_implem.off_loop (local: off_loop)
// Variant: uncurried, lifted
pub fn off_loop(d: Rc<Array<u64>>, u: u64, o: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(u, __rocq_global_132);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(u, 1u64);
      let v31 = add(u, 1u64);
      let v33 = &o;
      let v36 = rocq_array::get::<u64>(&v33, u);
      let v37 = &d;
      let v40 = rocq_array::get::<u64>(&v37, u);
      let v52 = rocq_array::set::<u64>(o, v31, add(v36, v40));
      off_loop(d, v23, v52, ())
    },
    sumbool::right => {
      std::mem::drop(d);
      o
    },
  }
}

// Rocq: Bilateral.bilateral_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(x: Rc<Array<u64>>, y: Rc<Array<u64>>, ex: u64, m: u64, k: u64, pos: Rc<Array<u64>>, tg: Rc<Array<u64>>) -> Rc<Array<u64>> {
  fill_loop(x, y, ex, m, k, pos, tg, ())
}

// Rocq: Bilateral.bilateral_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(x: Rc<Array<u64>>, y: Rc<Array<u64>>, ex: u64, m: u64, k: u64, pos: Rc<Array<u64>>, tg: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v15 = ltb(k, m);
  match bdec(v15) {
    sumbool::left => {
      let v19 = &x;
      let a = rocq_array::get::<u64>(&v19, k);
      match eqb(a, ex) {
        true => {
          fill_loop(x, y, ex, m, add(k, 1u64), pos, tg, ())
        },
        false => {
          let u = sub(a, 1000u64);
          let v68 = &pos;
          let p = rocq_array::get::<u64>(&v68, u);
          let v79 = add(k, 1u64);
          let v94 = rocq_array::set::<u64>(pos, u, add(p, 1u64));
          let v96 = &y;
          let v99 = rocq_array::get::<u64>(&v96, k);
          let v113 = rocq_array::set::<u64>(tg, p, sub(v99, 2000u64));
          fill_loop(x, y, ex, m, v79, v94, v113, ())
        },
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
pub fn root_loop_1(mL: Rc<Array<u64>>, u: u64, Q: Rc<Array<u64>>, qp: Rc<Array<u64>>, t: u64) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  root_loop(mL, u, Q, qp, t, ())
}

// Rocq: Bilateral.bilateral_implem.root_loop (local: root_loop)
// Variant: uncurried, lifted
pub fn root_loop(mL: Rc<Array<u64>>, u: u64, Q: Rc<Array<u64>>, qp: Rc<Array<u64>>, t: u64, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let v14 = ltb(u, __rocq_global_132);
  match bdec(v14) {
    sumbool::left => {
      let v19 = &mL;
      let v22 = rocq_array::get::<u64>(&v19, u);
      match ltb(v22, __rocq_global_132) {
        true => {
          root_loop(mL, add(u, 1u64), Q, qp, t, ())
        },
        false => {
          let v63 = add(u, 1u64);
          let v70 = rocq_array::set::<u64>(Q, t, u);
          let v85 = rocq_array::set::<u64>(qp, u, add(t, 1u64));
          root_loop(mL, v63, v70, v85, add(t, 1u64), ())
        },
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
pub fn scan_1(tg: Rc<Array<u64>>, mR: Rc<Array<u64>>, u: u64, pe: u64, p: u64, Q: Rc<Array<u64>>, qp: Rc<Array<u64>>, pr: Rc<Array<u64>>, t: u64) -> Rc<sres> {
  scan(tg, mR, u, pe, p, Q, qp, pr, t, ())
}

// Rocq: Bilateral.bilateral_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(tg: Rc<Array<u64>>, mR: Rc<Array<u64>>, u: u64, pe: u64, p: u64, Q: Rc<Array<u64>>, qp: Rc<Array<u64>>, pr: Rc<Array<u64>>, t: u64, _H: ()) -> Rc<sres> {
  let v17 = ltb(p, pe);
  match bdec(v17) {
    sumbool::left => {
      let v21 = &tg;
      let v = rocq_array::get::<u64>(&v21, p);
      let v26 = &pr;
      let v29 = rocq_array::get::<u64>(&v26, v);
      match eqb(v29, 0u64) {
        true => {
          let pr_1 = rocq_array::set::<u64>(pr, v, add(u, 1u64));
          let v53 = &mR;
          let w = rocq_array::get::<u64>(&v53, v);
          match ltb(w, __rocq_global_132) {
            true => {
              let v66 = &qp;
              let v69 = rocq_array::get::<u64>(&v66, w);
              match eqb(v69, 0u64) {
                true => {
                  let v85 = add(p, 1u64);
                  let v92 = rocq_array::set::<u64>(Q, t, w);
                  let v107 = rocq_array::set::<u64>(qp, w, add(t, 1u64));
                  scan(tg, mR, u, pe, v85, v92, v107, pr_1, add(t, 1u64), ())
                },
                false => {
                  scan(tg, mR, u, pe, add(p, 1u64), Q, qp, pr_1, t, ())
                },
              }
            },
            false => {
              std::mem::drop(tg);
              std::mem::drop(mR);
              std::mem::drop(Q);
              Rc::new(sres::SFound { v, qp, pr: pr_1 })
            },
          }
        },
        false => {
          scan(tg, mR, u, pe, add(p, 1u64), Q, qp, pr, t, ())
        },
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
pub fn bfs_1(off: Rc<Array<u64>>, tg: Rc<Array<u64>>, mR: Rc<Array<u64>>, h: u64, t: u64, Q: Rc<Array<u64>>, qp: Rc<Array<u64>>, pr: Rc<Array<u64>>) -> Rc<bres> {
  bfs(off, tg, mR, h, t, Q, qp, pr, ())
}

// Rocq: Bilateral.bilateral_implem.bfs (local: bfs)
// Variant: uncurried, lifted
pub fn bfs(off: Rc<Array<u64>>, tg: Rc<Array<u64>>, mR: Rc<Array<u64>>, h: u64, t: u64, Q: Rc<Array<u64>>, qp: Rc<Array<u64>>, pr: Rc<Array<u64>>, _H: ()) -> Rc<bres> {
  let v17 = ltb(h, __rocq_global_132);
  match bdec(v17) {
    sumbool::left => {
      match ltb(h, t) {
        true => {
          let v28 = &Q;
          let u = rocq_array::get::<u64>(&v28, h);
          let v40 = add(u, 1u64);
          let v41 = &off;
          let v44 = rocq_array::get::<u64>(&v41, v40);
          let v45 = &off;
          let v48 = rocq_array::get::<u64>(&v45, u);
          let v51 = Rc::clone(&tg);
          let v54 = Rc::clone(&mR);
          let v69 = scan_1(v51, v54, u, v44, v48, Q, qp, pr, t);
          let (v70, v71) = __rocq_reuse::reset(v69, |__payload| Clone::clone(__payload));
          std::mem::drop(v71);
          match v70 {
            sres::SFound { v: v82, qp: v84, pr: v86 } => {
              std::mem::drop(tg);
              std::mem::drop(mR);
              std::mem::drop(off);
              Rc::new(bres::BFound { v: v82, qp: v84, pr: v86 })
            },
            sres::SCont { Q: v99, qp: v101, pr: v103, t: v105 } => {
              bfs(off, tg, mR, add(h, 1u64), v105, v99, v101, v103, ())
            },
          }
        },
        false => {
          std::mem::drop(off);
          std::mem::drop(tg);
          std::mem::drop(mR);
          std::mem::drop(Q);
          Rc::new(bres::BFail { qp, pr })
        },
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
pub fn walk_1(qp: Rc<Array<u64>>, pr: Rc<Array<u64>>, v: u64, mL: Rc<Array<u64>>, mR: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  walk(qp, pr, v, mL, mR, ())
}

// Rocq: Bilateral.bilateral_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(qp: Rc<Array<u64>>, pr: Rc<Array<u64>>, v: u64, mL: Rc<Array<u64>>, mR: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v7 = &pr;
  let v10 = rocq_array::get::<u64>(&v7, v);
  let u = sub(v10, 1u64);
  let v18 = &mL;
  let old = rocq_array::get::<u64>(&v18, u);
  let mL_ = rocq_array::set::<u64>(mL, u, v);
  let mR_ = rocq_array::set::<u64>(mR, v, u);
  match ltb(old, __rocq_global_132) {
    true => {
      let v47 = &pr;
      let v50 = rocq_array::get::<u64>(&v47, old);
      let v57 = sub(v50, 1u64);
      let v58 = &qp;
      let v61 = rocq_array::get::<u64>(&v58, v57);
      let v63 = &pr;
      let v66 = rocq_array::get::<u64>(&v63, v);
      let v73 = sub(v66, 1u64);
      let v74 = &qp;
      let v77 = rocq_array::get::<u64>(&v74, v73);
      let v83 = ltb(v61, v77);
      match bdec(v83) {
        sumbool::left => {
          walk(qp, pr, old, mL_, mR_, ())
        },
        sumbool::right => {
          std::mem::drop(qp);
          std::mem::drop(pr);
          (mL_, mR_)
        },
      }
    },
    false => {
      std::mem::drop(qp);
      std::mem::drop(pr);
      (mL_, mR_)
    },
  }
}

// Rocq: Bilateral.bilateral_implem.phases
// Variant: uncurried
pub fn phases_1(off: Rc<Array<u64>>, tg: Rc<Array<u64>>, it: u64, mL: Rc<Array<u64>>, mR: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  phases(off, tg, it, mL, mR, ())
}

// Rocq: Bilateral.bilateral_implem.phases (local: phases)
// Variant: uncurried, lifted
pub fn phases(off: Rc<Array<u64>>, tg: Rc<Array<u64>>, it: u64, mL: Rc<Array<u64>>, mR: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v14 = ltb(it, __rocq_global_182);
  match bdec(v14) {
    sumbool::left => {
      let v28 = rocq_array::make::<u64>(__rocq_global_132, 0u64);
      let v36 = rocq_array::make::<u64>(__rocq_global_132, 0u64);
      let v41 = Rc::clone(&mL);
      let v50 = root_loop_1(v41, 0u64, v28, v36, 0u64);
      match &v50 {
        (t, p) => {
          match t {
            (qp, Q) => {
              let v72 = rocq_array::make::<u64>(__rocq_global_132, 0u64);
              let v75 = Rc::clone(&off);
              let v78 = Rc::clone(&tg);
              let v81 = Rc::clone(&mR);
              let v85 = Clone::clone(p);
              let v87 = Rc::clone(qp);
              let v89 = Rc::clone(Q);
              let v92 = bfs_1(v75, v78, v81, 0u64, v85, v87, v89, v72);
              let (v93, v94) = __rocq_reuse::reset(v92, |__payload| Clone::clone(__payload));
              std::mem::drop(v94);
              match v93 {
                bres::BFound { v: v103, qp: v105, pr: v107 } => {
                  std::mem::drop(v50);
                  let v120 = walk_1(v105, v107, v103, mL, mR);
                  match v120 {
                    (v122, v124) => {
                      phases(off, tg, add(it, 1u64), v122, v124, ())
                    },
                  }
                },
                bres::BFail { qp: v155, pr: v157 } => {
                  std::mem::drop(off);
                  std::mem::drop(tg);
                  std::mem::drop(mL);
                  std::mem::drop(mR);
                  std::mem::drop(v50);
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
      let v183 = rocq_array::make::<u64>(__rocq_global_132, 0u64);
      let v191 = rocq_array::make::<u64>(__rocq_global_132, 0u64);
      (v183, v191)
    },
  }
}

// Rocq: Bilateral.bilateral_implem.mark_loop
// Variant: uncurried
pub fn mark_loop_1(qp: Rc<Array<u64>>, pr: Rc<Array<u64>>, i: u64, mk: Rc<Array<u64>>) -> Rc<Array<u64>> {
  mark_loop(qp, pr, i, mk, ())
}

// Rocq: Bilateral.bilateral_implem.mark_loop (local: mark_loop)
// Variant: uncurried, lifted
pub fn mark_loop(qp: Rc<Array<u64>>, pr: Rc<Array<u64>>, i: u64, mk: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v13 = ltb(i, __rocq_global_707);
  match bdec(v13) {
    sumbool::left => {
      let v24 = add(i, 1u64);
      let v26 = __rocq_global_132;
      let v32 = match ltb(i, v26) {
        true => {
          let v34 = &qp;
          let v37 = rocq_array::get::<u64>(&v34, i);
          match eqb(v37, 0u64) {
            true => {
              rocq_array::set::<u64>(mk, i, 1u64)
            },
            false => {
              mk
            },
          }
        },
        false => {
          let v69 = sub(i, __rocq_global_132);
          let v70 = &pr;
          let v73 = rocq_array::get::<u64>(&v70, v69);
          match eqb(v73, 0u64) {
            true => {
              mk
            },
            false => {
              rocq_array::set::<u64>(mk, i, 1u64)
            },
          }
        },
      };
      mark_loop(qp, pr, v24, v32, ())
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
pub fn engine(x: Rc<Array<u64>>, y: Rc<Array<u64>>, ex: u64) -> Rc<Array<u64>> {
  let v3 = &x;
  let m = rocq_array::length::<u64>(&v3);
  let v15 = rocq_array::make::<u64>(__rocq_global_132, 0u64);
  let v18 = Rc::clone(&x);
  let d = deg_loop_1(v18, ex, m, 0u64, v15);
  let v38 = rocq_array::make::<u64>(__rocq_global_182, 0u64);
  let v41 = Rc::clone(&d);
  let off = off_loop_1(v41, 0u64, v38);
  let v57 = rocq_array::make::<u64>(__rocq_global_182, 0u64);
  let pos = off_loop_1(d, 0u64, v57);
  let v74 = rocq_array::make::<u64>(m, 0u64);
  let tg = fill_loop_1(x, y, ex, m, 0u64, pos, v74);
  let v99 = rocq_array::make::<u64>(__rocq_global_132, __rocq_global_132);
  let v106 = rocq_array::make::<u64>(__rocq_global_132, __rocq_global_132);
  let v117 = phases_1(off, tg, 0u64, v99, v106);
  match v117 {
    (v119, v121) => {
      let v133 = rocq_array::make::<u64>(__rocq_global_707, 0u64);
      mark_loop_1(v119, v121, 0u64, v133)
    },
  }
}

// Rocq: Bilateral.bilateral_implem.out_loop
// Variant: uncurried
pub fn out_loop_1(mk: Rc<Array<u64>>, i: u64, p: u64, out: Rc<Array<u64>>) -> Rc<Array<u64>> {
  out_loop(mk, i, p, out, ())
}

// Rocq: Bilateral.bilateral_implem.out_loop (local: out_loop)
// Variant: uncurried, lifted
pub fn out_loop(mk: Rc<Array<u64>>, i: u64, p: u64, out: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v13 = ltb(i, __rocq_global_707);
  match bdec(v13) {
    sumbool::left => {
      let v18 = &mk;
      let v21 = rocq_array::get::<u64>(&v18, i);
      match eqb(v21, 0u64) {
        true => {
          out_loop(mk, add(i, 1u64), p, out, ())
        },
        false => {
          let v61 = add(i, 1u64);
          let v69 = add(p, 1u64);
          let v84 = rocq_array::set::<u64>(out, p, add(1000u64, i));
          out_loop(mk, v61, v69, v84, ())
        },
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
pub fn cnt_loop_1(mk: Rc<Array<u64>>, i: u64, c: u64) -> u64 {
  cnt_loop(mk, i, c, ())
}

// Rocq: Bilateral.bilateral_implem.cnt_loop (local: cnt_loop)
// Variant: uncurried, lifted
pub fn cnt_loop(mk: Rc<Array<u64>>, i: u64, c: u64, _H: ()) -> u64 {
  let v12 = ltb(i, __rocq_global_707);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v25 = &mk;
      let v28 = rocq_array::get::<u64>(&v25, i);
      let v30 = 0u64;
      let v36 = match eqb(v28, v30) {
        true => {
          c
        },
        false => {
          add(c, 1u64)
        },
      };
      cnt_loop(mk, v23, v36, ())
    },
    sumbool::right => {
      std::mem::drop(mk);
      c
    },
  }
}

// Rocq: Bilateral.bilateral_implem.count_marks
pub fn count_marks(mk: Rc<Array<u64>>) -> u64 {
  cnt_loop_1(mk, 0u64, 0u64)
}

// Rocq: Bilateral.bilateral_implem.build
pub fn build(mk: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v9 = Rc::clone(&mk);
  let v17 = rocq_array::make::<u64>(count_marks(v9), 0u64);
  out_loop_1(mk, 0u64, 0u64, v17)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Bilateral.bilateral_implem.bilateral_impl
// Variant: uncurried
pub fn bilateral_impl(x: Rc<Array<u64>>, y: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v7 = Rc::clone(&x);
  let v10 = Rc::clone(&y);
  let mk1 = engine(v7, v10, 1009u64);
  let mk0 = engine(x, y, 0u64);
  let v30 = Rc::clone(&mk1);
  let v38 = add(count_marks(v30), 1u64);
  let v42 = Rc::clone(&mk0);
  let v43 = count_marks(v42);
  let v66 = match leb(v38, v43) {
    true => {
      std::mem::drop(mk0);
      rocq_array::set::<u64>(mk1, 9u64, 1u64)
    },
    false => {
      std::mem::drop(mk1);
      mk0
    },
  };
  build(v66)
}

// Rocq: Bilateral.bilateral_implem.bilateral_impl
pub fn bilateral_impl_curried(x: Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v3 = {
    move |y: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let v9 = Rc::clone(&x);
      bilateral_impl(v9, y)
    }
  };
  let v15: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v3);
  v15
}

mod __rocq_reuse {
//! Empty allocation ownership for OwnedANF reset and exact-type rebuilding.
use std::mem::MaybeUninit;
use std::rc::Rc;

/// Move-only and opaque: storage has no initialized `T` and cannot be inspected.
pub struct Token<T> {
    _storage: Option<Rc<MaybeUninit<T>>>,
}

/// Consume an owner. The caller supplies the IR-approved shallow field copy;
/// This may use a compiler-generated structural Clone implementation, but does
/// not authorize arbitrary host clone behavior merely because T implements Clone.
#[inline]
pub fn reset<T>(mut owner: Rc<T>, duplicate: impl FnOnce(&T) -> T) -> (T, Token<T>) {
    if let Some(payload) = Rc::get_mut(&mut owner) {
        // SAFETY: get_mut establishes exclusive access (including no Weak
        // owners). T and MaybeUninit<T> have identical size/alignment, so their
        // Rc allocation layouts agree. After read, no potentially panicking
        // user code runs before ownership becomes Rc<MaybeUninit<T>>. There is
        // exactly one from_raw for into_raw, and the original Rc<T> is consumed.
        // The token never reads or drops the moved T; dropping it only frees
        // the allocation. The payload returned here owns T's fields once.
        unsafe {
            let value = std::ptr::read(payload);
            let raw = Rc::into_raw(owner).cast::<MaybeUninit<T>>();
            let storage = Rc::from_raw(raw);
            (value, Token { _storage: Some(storage) })
        }
    } else {
        let value = duplicate(&owner);
        drop(owner);
        (value, Token { _storage: None })
    }
}

/// Consume reserved storage and a fully evaluated payload. Empty tokens allocate.
#[inline]
pub fn rebuild<T>(token: Token<T>, payload: T) -> Rc<T> {
    match token._storage {
        None => Rc::new(payload),
        Some(mut storage) => {
            // The opaque, non-Clone token owns the only strong reference and
            // has no weak references. Check before initializing, so a panic
            // cannot leave an initialized T hidden inside MaybeUninit<T>.
            Rc::get_mut(&mut storage).expect("exclusive reuse token").write(payload);
            // SAFETY: the payload is now fully initialized; no panicking code
            // lies between initialization and this ownership conversion. The
            // reset conversion established identical allocation layouts.
            unsafe { Rc::from_raw(Rc::into_raw(storage).cast::<T>()) }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    struct Probe(Rc<Cell<usize>>);
    impl Drop for Probe {
        fn drop(&mut self) { self.0.set(self.0.get() + 1); }
    }

    #[test]
    fn rebuilding_preserves_address_and_drops_only_new_payload() {
        let drops = Rc::new(Cell::new(0));
        let owner = Rc::new(Probe(drops.clone()));
        let address = Rc::as_ptr(&owner);
        let (old, token) = reset(owner, |_| panic!("unique"));
        drop(old);
        assert_eq!(drops.get(), 1);
        let new = rebuild(token, Probe(drops.clone()));
        assert_eq!(Rc::as_ptr(&new), address);
        assert_eq!(drops.get(), 1);
        drop(new);
        assert_eq!(drops.get(), 2);
    }

    #[test]
    fn empty_token_allocates_and_preserves_old_alias() {
        let old = Rc::new(7);
        let alias = old.clone();
        let (_, token) = reset(old, |x| *x);
        let new = rebuild(token, 19);
        assert_eq!(*alias, 7);
        assert_eq!(*new, 19);
        assert!(!Rc::ptr_eq(&alias, &new));
    }

    #[test]
    fn unique_token_drop_does_not_drop_payload() {
        let drops = Rc::new(Cell::new(0));
        let owner = Rc::new(Probe(drops.clone()));
        let address = Rc::as_ptr(&owner).cast::<MaybeUninit<Probe>>();
        let (payload, token) = reset(owner, |_| panic!("unique path duplicated"));
        assert_eq!(Rc::as_ptr(token._storage.as_ref().unwrap()), address);
        drop(token);
        assert_eq!(drops.get(), 0);
        drop(payload);
        assert_eq!(drops.get(), 1);
    }

    #[test]
    fn shared_fallback_preserves_aliases() {
        let field = Rc::new(7);
        let owner = Rc::new((field.clone(), 9));
        let alias = owner.clone();
        let (payload, token) = reset(owner, |x| (x.0.clone(), x.1));
        assert!(token._storage.is_none());
        assert!(Rc::ptr_eq(&payload.0, &alias.0));
        assert_eq!(Rc::strong_count(&field), 3);
        drop(token);
        drop(payload);
        assert_eq!(alias.1, 9);
        drop(alias);
        assert_eq!(Rc::strong_count(&field), 1);
    }

    #[test]
    fn weak_pointer_forces_fallback() {
        let owner = Rc::new(17);
        let weak = Rc::downgrade(&owner);
        let (payload, token) = reset(owner, |x| *x);
        assert_eq!(payload, 17);
        assert!(token._storage.is_none());
        assert!(weak.upgrade().is_none());
    }

    #[test]
    fn panicking_fallback_releases_consumed_handle() {
        let owner = Rc::new(17);
        let alias = owner.clone();
        let result = std::panic::catch_unwind(|| reset(owner, |_| panic!("copy failed")));
        assert!(result.is_err());
        assert_eq!(Rc::strong_count(&alias), 1);
        assert_eq!(*alias, 17);
    }

    #[test]
    fn zero_sized_payload() {
        let (payload, token) = reset(Rc::new(()), |_| panic!("unique"));
        drop(token);
        assert_eq!(payload, ());
    }
}

}

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = __rocq_global_999.with(Clone::clone);
  v0
}
const __rocq_global_132: u64 = 1000u64;
const __rocq_global_182: u64 = 1001u64;
const __rocq_global_707: u64 = 2000u64;
std::thread_local! { static __rocq_global_999: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = bilateral(); }
std::thread_local! { static __rocq_global_1002: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> = bilateral_curried(); }