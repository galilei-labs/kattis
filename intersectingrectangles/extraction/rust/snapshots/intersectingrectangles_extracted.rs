// Generated from OwnedANF. This printer is not verified.
#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub enum option<A: 'static> {
  Some(A),
  None,
}

impl<A: Clone + 'static> Clone for option<A> {
  fn clone(&self) -> Self {
    match self {
      option::Some(__field0) => option::Some(Clone::clone(__field0)),
      option::None => option::None,
    }
  }
}

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub enum tree {
  Leaf,
  Node(Rc<tree>, u64, u64, Rc<tree>, u64),
}

impl Clone for tree {
  fn clone(&self) -> Self {
    match self {
      tree::Leaf => tree::Leaf,
      tree::Node(__field0, __field1, __field2, __field3, __field4) => tree::Node(Clone::clone(__field0), Clone::clone(__field1), Clone::clone(__field2), Clone::clone(__field3), Clone::clone(__field4)),
    }
  }
}

pub type sint = u64;

// Rocq: Intersectingrectangles.intersectingrectangles_implem.sweep
pub fn sweep_curried_1() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>>>> {
  let v0 = {
    move |n: u64, y1: Rc<Array<u64>>, y2: Rc<Array<u64>>, t: Rc<tree>| -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>> {
      let v8: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>>> = sweep_curried(n);
      let v9: &Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>>> = &v8;
      let v12: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>> = v9(y1);
      std::mem::drop(v8);
      let v13: &Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>> = &v12;
      let v16: Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> = v13(y2);
      std::mem::drop(v12);
      let v17: &Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> = &v16;
      let v20: Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>> = v17(t);
      std::mem::drop(v16);
      v20
    }
  };
  let v23: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> = Rc::new(v0);
  let v27 = {
    move |n: u64| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>>> {
      let v28 = &v23;
      let v31: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> = Rc::clone(v28);
      let v35 = {
        move |y1: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>> {
          let v36 = &v31;
          let n = &n;
          let v41: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> = Rc::clone(v36);
          let v44 = Clone::clone(n);
          let v47 = {
            move |y2: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> {
              let v48 = &v41;
              let n = &v44;
              let y1 = &y1;
              let v55: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> = Rc::clone(v48);
              let v58 = Clone::clone(n);
              let v60 = Rc::clone(y1);
              let v63 = {
                move |t: Rc<tree>| -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>> {
                  let v64 = &v55;
                  let v74 = Clone::clone(&v58);
                  let v76 = Rc::clone(&v60);
                  let v78 = Rc::clone(&y2);
                  let v81: Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>> = v64(v74, v76, v78, t);
                  v81
                }
              };
              let v84: Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> = Rc::new(v63);
              v84
            }
          };
          let v88: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>> = Rc::new(v47);
          v88
        }
      };
      let v92: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>>> = Rc::new(v35);
      v92
    }
  };
  let v96: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>>>> = Rc::new(v27);
  v96
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.sweep (local: sweep)
// Variant: lifted
pub fn sweep_curried(n: u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>>> {
  let v3 = {
    move |y1: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>> {
      let n = &n;
      let v8 = Clone::clone(n);
      let v11 = {
        move |y2: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> {
          let n = &v8;
          let y1 = &y1;
          let v18 = Clone::clone(n);
          let v20 = Rc::clone(y1);
          let v23 = {
            move |t: Rc<tree>| -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>> {
              let n = &v18;
              let y1 = &v20;
              let y2 = &y2;
              let v32 = Clone::clone(n);
              let v34 = Rc::clone(y1);
              let v36 = Rc::clone(y2);
              let v39 = {
                move |s: Rc<tree>| -> Rc<option<Rc<tree>>> {
                  let v51 = Clone::clone(&v32);
                  let v53 = Rc::clone(&v34);
                  let v55 = Rc::clone(&v36);
                  let v57 = Rc::clone(&t);
                  sweep(v51, v53, v55, v57, s)
                }
              };
              let v63: Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>> = Rc::new(v39);
              v63
            }
          };
          let v67: Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> = Rc::new(v23);
          v67
        }
      };
      let v71: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>> = Rc::new(v11);
      v71
    }
  };
  let v75: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>>> = Rc::new(v3);
  v75
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.sweep (local: sweep)
// Variant: uncurried, lifted
pub fn sweep(n: u64, y1: Rc<Array<u64>>, y2: Rc<Array<u64>>, t: Rc<tree>, s: Rc<tree>) -> Rc<option<Rc<tree>>> {
  let (v5, v6) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v6);
  match v5 {
    tree::Leaf => {
      std::mem::drop(y1);
      std::mem::drop(y2);
      Rc::new(option::<Rc<tree>>::Some(s))
    },
    tree::Node(v22, _v24, v26, v28, _v30) => {
      let v37 = Rc::clone(&y1);
      let v40 = Rc::clone(&y2);
      let v45 = sweep(n, v37, v40, v22, s);
      let (v46, v47) = __rocq_reuse::reset(v45, |__payload| Clone::clone(__payload));
      match v46 {
        option::Some(v52) => {
          std::mem::drop(v47);
          let v59 = Rc::clone(&y1);
          let v62 = Rc::clone(&y2);
          let v67 = step(n, v59, v62, v26, v52);
          let (v68, v69) = __rocq_reuse::reset(v67, |__payload| Clone::clone(__payload));
          match v68 {
            option::Some(v74) => {
              std::mem::drop(v69);
              sweep(n, y1, y2, v28, v74)
            },
            option::None => {
              std::mem::drop(y2);
              std::mem::drop(y1);
              std::mem::drop(v28);
              __rocq_reuse::rebuild(v69, option::<Rc<tree>>::None)
            },
          }
        },
        option::None => {
          std::mem::drop(y1);
          std::mem::drop(y2);
          std::mem::drop(v28);
          __rocq_reuse::rebuild(v47, option::<Rc<tree>>::None)
        },
      }
    },
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.intersecting_rectangles
// Variant: uncurried
pub fn intersecting_rectangles() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> bool> {
  let v0: fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> bool = intersecting_rectangles_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> bool> = Rc::new(v0);
  v1
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.intersecting_rectangles
pub fn intersecting_rectangles_curried() -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>>> {
  let v0: fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>> = intersecting_rectangles_impl_curried;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb
// Variant: uncurried
pub fn ltsb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltsb(v0, v1)
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.height
// Variant: borrowed
pub fn height(t: &Rc<tree>) -> u64 {
  let v1 = t;
  match &**v1 {
    tree::Leaf => {
      0u64
    },
    tree::Node(_h, _t1, _i0, _i, t0) => {
      Clone::clone(t0)
    },
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.hmax
// Variant: uncurried
pub fn hmax(a: u64, b: u64) -> u64 {
  match ltb(a, b) {
    true => {
      b
    },
    false => {
      a
    },
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.node
// Variant: uncurried
pub fn node(l: Rc<tree>, k: u64, v: u64, r: Rc<tree>) -> Rc<tree> {
  let v9 = height(&l);
  let v13 = height(&r);
  Rc::new(tree::Node(l, k, v, r, add(hmax(v9, v13), 1u64)))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.bal
// Variant: uncurried
pub fn bal(l: Rc<tree>, k: u64, v: u64, r: Rc<tree>) -> Rc<tree> {
  let hl = height(&l);
  let hr = height(&r);
  let v21 = add(hr, 2u64);
  match ltb(v21, hl) {
    true => {
      match &*l {
        tree::Leaf => {
          node(l, k, v, r)
        },
        tree::Node(i, lr, lv, lk, _ll) => {
          let v54 = height(lk);
          let v57 = height(i);
          match leb(v54, v57) {
            true => {
              let v74 = node(Rc::clone(lk), k, v, r);
              let v76 = Rc::clone(i);
              let v78 = Clone::clone(lr);
              let v79 = Clone::clone(lv);
              std::mem::drop(l);
              node(v76, v78, v79, v74)
            },
            false => {
              match &**lk {
                tree::Leaf => {
                  node(l, k, v, r)
                },
                tree::Node(i_1, lrr, lrv, lrk, _lrl) => {
                  let v119 = node(Rc::clone(i), Clone::clone(lr), Clone::clone(lv), Rc::clone(i_1));
                  let v129 = node(Rc::clone(lrk), k, v, r);
                  let v133 = Clone::clone(lrr);
                  let v134 = Clone::clone(lrv);
                  std::mem::drop(l);
                  node(v119, v133, v134, v129)
                },
              }
            },
          }
        },
      }
    },
    false => {
      let v159 = add(hl, 2u64);
      match ltb(v159, hr) {
        true => {
          match &*r {
            tree::Leaf => {
              node(l, k, v, r)
            },
            tree::Node(i, rr, rv, rk, _rl) => {
              let v192 = height(i);
              let v195 = height(rk);
              match leb(v192, v195) {
                true => {
                  let v213 = node(l, k, v, Rc::clone(i));
                  let v216 = Clone::clone(rr);
                  let v218 = Clone::clone(rv);
                  let v219 = Rc::clone(rk);
                  std::mem::drop(r);
                  node(v213, v216, v218, v219)
                },
                false => {
                  match &**i {
                    tree::Leaf => {
                      node(l, k, v, r)
                    },
                    tree::Node(i_1, rlr, rlv, rlk, _rll) => {
                      let v257 = node(l, k, v, Rc::clone(i_1));
                      let v267 = node(Rc::clone(rlk), Clone::clone(rr), Clone::clone(rv), Rc::clone(rk));
                      let v271 = Clone::clone(rlr);
                      let v272 = Clone::clone(rlv);
                      std::mem::drop(r);
                      node(v257, v271, v272, v267)
                    },
                  }
                },
              }
            },
          }
        },
        false => {
          node(l, k, v, r)
        },
      }
    },
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.insert
// Variant: uncurried
pub fn insert_1(k: u64, v: u64, t: Rc<tree>) -> Rc<tree> {
  insert(k, v, t)
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.insert (local: insert)
// Variant: uncurried, lifted
pub fn insert(k: u64, v: u64, t: Rc<tree>) -> Rc<tree> {
  let (v3, v4) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  match v3 {
    tree::Leaf => {
      let v15 = __rocq_reuse::rebuild(v4, tree::Leaf);
      let v18 = Rc::new(tree::Leaf);
      Rc::new(tree::Node(v15, k, v, v18, 1u64))
    },
    tree::Node(v36, v38, v40, v42, v44) => {
      match ltsb(k, v38) {
        true => {
          std::mem::drop(v4);
          bal(insert(k, v, v36), v38, v40, v42)
        },
        false => {
          match ltsb(v38, k) {
            true => {
              std::mem::drop(v4);
              bal(v36, v38, v40, insert(k, v, v42))
            },
            false => {
              __rocq_reuse::rebuild(v4, tree::Node(v36, k, v, v42, v44))
            },
          }
        },
      }
    },
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.build
// Variant: uncurried
pub fn build_1(x1: Rc<Array<u64>>, x2: Rc<Array<u64>>, n: u64, i: u64, t: Rc<tree>) -> Rc<tree> {
  build(x1, x2, n, i, t, ())
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(x1: Rc<Array<u64>>, x2: Rc<Array<u64>>, n: u64, i: u64, t: Rc<tree>, _H: ()) -> Rc<tree> {
  let v13 = ltb(i, n);
  match bdec(v13) {
    sumbool::left => {
      let v24 = add(i, 1u64);
      let v26 = &x2;
      let v29 = rocq_array::get::<u64>(&v26, i);
      let v35 = add(n, i);
      let v37 = &x1;
      let v41 = rocq_array::get::<u64>(&v37, i);
      let v47 = insert_1(v41, i, t);
      build(x1, x2, n, v24, insert_1(v29, v35, v47), ())
    },
    sumbool::right => {
      std::mem::drop(x1);
      std::mem::drop(x2);
      t
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lesb
// Variant: uncurried
pub fn lesb(v0: u64, v1: u64) -> bool {
  rocq_int63::lesb(v0, v1)
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.between
// Variant: borrowed, uncurried
pub fn between_1(lo: u64, hi: u64, t: &Rc<tree>) -> bool {
  let lo_1 = lo;
  let hi_1 = hi;
  between(lo_1, hi_1, t)
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.between (local: between)
// Variant: borrowed, uncurried, lifted
pub fn between(lo: u64, hi: u64, t: &Rc<tree>) -> bool {
  let lo_1 = lo;
  let hi_1 = hi;
  let v5 = t;
  match &**v5 {
    tree::Leaf => {
      false
    },
    tree::Node(i0, r, _i, k, _l) => {
      let v23 = Clone::clone(r);
      match lesb(v23, lo_1) {
        true => {
          between(lo_1, hi_1, k)
        },
        false => {
          let v41 = Clone::clone(r);
          match lesb(hi_1, v41) {
            true => {
              between(lo_1, hi_1, i0)
            },
            false => {
              true
            },
          }
        },
      }
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.remove_min
// Variant: uncurried
pub fn remove_min_1(l: Rc<tree>, k: u64, v: u64, r: Rc<tree>) -> ((u64, u64), Rc<tree>) {
  remove_min(l, k, v, r)
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.remove_min (local: remove_min)
// Variant: uncurried, lifted
pub fn remove_min(l: Rc<tree>, k: u64, v: u64, r: Rc<tree>) -> ((u64, u64), Rc<tree>) {
  match &*l {
    tree::Leaf => {
      std::mem::drop(l);
      ((k, v), r)
    },
    tree::Node(i, lr, lv, lk, _ll) => {
      let v32 = Rc::clone(i);
      let v34 = Clone::clone(lr);
      let v36 = Clone::clone(lv);
      let v37 = Rc::clone(lk);
      std::mem::drop(l);
      let v39 = remove_min(v32, v34, v36, v37);
      match v39 {
        (v41, v43) => {
          match v41 {
            (v46, v48) => {
              ((v46, v48), bal(v43, k, v, r))
            },
          }
        },
      }
    },
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.merge
// Variant: uncurried
pub fn merge(l: Rc<tree>, r: Rc<tree>) -> Rc<tree> {
  match &*l {
    tree::Leaf => {
      std::mem::drop(l);
      r
    },
    tree::Node(_i1, _t0, _i0, _i, _t) => {
      match &*r {
        tree::Leaf => {
          std::mem::drop(r);
          l
        },
        tree::Node(i_1, rr, rv, rk, _rl) => {
          let v32 = Rc::clone(i_1);
          let v34 = Clone::clone(rr);
          let v36 = Clone::clone(rv);
          let v37 = Rc::clone(rk);
          std::mem::drop(r);
          let v39 = remove_min_1(v32, v34, v36, v37);
          match v39 {
            (v41, v43) => {
              match v41 {
                (v46, v48) => {
                  bal(l, v46, v48, v43)
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.remove
// Variant: uncurried
pub fn remove_1(k: u64, t: Rc<tree>) -> Rc<tree> {
  remove(k, t)
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.remove (local: remove)
// Variant: uncurried, lifted
pub fn remove(k: u64, t: Rc<tree>) -> Rc<tree> {
  let (v2, v3) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  match v2 {
    tree::Leaf => {
      __rocq_reuse::rebuild(v3, tree::Leaf)
    },
    tree::Node(v17, v19, v21, v23, _v25) => {
      std::mem::drop(v3);
      match ltsb(k, v19) {
        true => {
          bal(remove(k, v17), v19, v21, v23)
        },
        false => {
          match ltsb(v19, k) {
            true => {
              bal(v17, v19, v21, remove(k, v23))
            },
            false => {
              merge(v17, v23)
            },
          }
        },
      }
    },
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.step
// Variant: uncurried
pub fn step(n: u64, y1: Rc<Array<u64>>, y2: Rc<Array<u64>>, v: u64, s: Rc<tree>) -> Rc<option<Rc<tree>>> {
  match ltb(v, n) {
    true => {
      let v12 = &y1;
      let lo = rocq_array::get::<u64>(&v12, v);
      let v16 = &y2;
      let hi = rocq_array::get::<u64>(&v16, v);
      match between_1(lo, hi, &s) {
        true => {
          std::mem::drop(y1);
          std::mem::drop(y2);
          std::mem::drop(s);
          Rc::new(option::<Rc<tree>>::None)
        },
        false => {
          std::mem::drop(y1);
          std::mem::drop(y2);
          let v46 = insert_1(lo, 0u64, s);
          Rc::new(option::<Rc<tree>>::Some(insert_1(hi, 0u64, v46)))
        },
      }
    },
    false => {
      let i = sub(v, n);
      let v70 = &y1;
      let lo = rocq_array::get::<u64>(&v70, i);
      let v74 = &y2;
      let hi = rocq_array::get::<u64>(&v74, i);
      let v84 = remove_1(lo, s);
      let s_ = remove_1(hi, v84);
      match between_1(lo, hi, &s_) {
        true => {
          std::mem::drop(y1);
          std::mem::drop(y2);
          std::mem::drop(s_);
          Rc::new(option::<Rc<tree>>::None)
        },
        false => {
          std::mem::drop(y1);
          std::mem::drop(y2);
          Rc::new(option::<Rc<tree>>::Some(s_))
        },
      }
    },
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.sweep
// Variant: uncurried
pub fn sweep_2(n: u64, y1: Rc<Array<u64>>, y2: Rc<Array<u64>>, t: Rc<tree>, s: Rc<tree>) -> Rc<option<Rc<tree>>> {
  sweep_1(n, y1, y2, t, s)
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.sweep (local: sweep)
// Variant: uncurried, lifted
pub fn sweep_1(n: u64, y1: Rc<Array<u64>>, y2: Rc<Array<u64>>, t: Rc<tree>, s: Rc<tree>) -> Rc<option<Rc<tree>>> {
  let (v5, v6) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v6);
  match v5 {
    tree::Leaf => {
      std::mem::drop(y1);
      std::mem::drop(y2);
      Rc::new(option::<Rc<tree>>::Some(s))
    },
    tree::Node(v22, _v24, v26, v28, _v30) => {
      let v37 = Rc::clone(&y1);
      let v40 = Rc::clone(&y2);
      let v45 = sweep_1(n, v37, v40, v22, s);
      let (v46, v47) = __rocq_reuse::reset(v45, |__payload| Clone::clone(__payload));
      match v46 {
        option::Some(v52) => {
          std::mem::drop(v47);
          let v59 = Rc::clone(&y1);
          let v62 = Rc::clone(&y2);
          let v67 = step(n, v59, v62, v26, v52);
          let (v68, v69) = __rocq_reuse::reset(v67, |__payload| Clone::clone(__payload));
          match v68 {
            option::Some(v74) => {
              std::mem::drop(v69);
              sweep_1(n, y1, y2, v28, v74)
            },
            option::None => {
              std::mem::drop(y2);
              std::mem::drop(y1);
              std::mem::drop(v28);
              __rocq_reuse::rebuild(v69, option::<Rc<tree>>::None)
            },
          }
        },
        option::None => {
          std::mem::drop(y1);
          std::mem::drop(y2);
          std::mem::drop(v28);
          __rocq_reuse::rebuild(v47, option::<Rc<tree>>::None)
        },
      }
    },
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.intersecting_rectangles_impl
// Variant: uncurried
pub fn intersecting_rectangles_impl(x1: Rc<Array<u64>>, y1: Rc<Array<u64>>, x2: Rc<Array<u64>>, y2: Rc<Array<u64>>) -> bool {
  let v4 = &x1;
  let n = rocq_array::length::<u64>(&v4);
  let ev = build_1(x1, x2, n, 0u64, Rc::new(tree::Leaf));
  let v37 = sweep_2(n, y1, y2, ev, Rc::new(tree::Leaf));
  let (v38, v39) = __rocq_reuse::reset(v37, |__payload| Clone::clone(__payload));
  std::mem::drop(v39);
  match v38 {
    option::Some(v44) => {
      std::mem::drop(v44);
      false
    },
    option::None => {
      true
    },
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.intersecting_rectangles_impl
pub fn intersecting_rectangles_impl_curried(x1: Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>> {
  let v3 = {
    move |y1: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>> {
      let x1 = &x1;
      let v8 = Rc::clone(x1);
      let v11 = {
        move |x2: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> bool> {
          let x1 = &v8;
          let y1 = &y1;
          let v18 = Rc::clone(x1);
          let v20 = Rc::clone(y1);
          let v23 = {
            move |y2: Rc<Array<u64>>| -> bool {
              let v33 = Rc::clone(&v18);
              let v35 = Rc::clone(&v20);
              let v37 = Rc::clone(&x2);
              intersecting_rectangles_impl(v33, v35, v37, y2)
            }
          };
          let v43: Rc<dyn Fn(Rc<Array<u64>>) -> bool> = Rc::new(v23);
          v43
        }
      };
      let v47: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>> = Rc::new(v11);
      v47
    }
  };
  let v51: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>> = Rc::new(v3);
  v51
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

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> bool> {
  let v0: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> bool> = __rocq_global_698.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_617: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>>>> = sweep_curried_1(); }
std::thread_local! { static __rocq_global_698: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> bool> = intersecting_rectangles(); }
std::thread_local! { static __rocq_global_701: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>>> = intersecting_rectangles_curried(); }