#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

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
  Node(Rc<tree>, Int63, Int63, Rc<tree>, Int63),
}

impl Clone for tree {
  fn clone(&self) -> Self {
    match self {
      tree::Leaf => tree::Leaf,
      tree::Node(__field0, __field1, __field2, __field3, __field4) => tree::Node(Clone::clone(__field0), Clone::clone(__field1), Clone::clone(__field2), Clone::clone(__field3), Clone::clone(__field4)),
    }
  }
}

pub type sint = Int63;

// Rocq: Intersectingrectangles.intersectingrectangles_implem.sweep
pub fn sweep_curried_1() -> Rc<dyn Fn(Int63) -> Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>>>> {
  let callback: Rc<dyn Fn(Int63, Array<Int63>, Array<Int63>, Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> = Rc::new(move |n: Int63, y1: Array<Int63>, y2: Array<Int63>, t: Rc<tree>| -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>> {
    let tmp: Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>>> = sweep_curried(n);
    let tmp_1: &Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>>> = &tmp;
    let tmp_2: Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>> = tmp_1(y1);
    std::mem::drop(tmp);
    let tmp_3: &Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>> = &tmp_2;
    let tmp_4: Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> = tmp_3(y2);
    std::mem::drop(tmp_2);
    let tmp_5: &Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> = &tmp_4;
    let tmp_6: Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>> = tmp_5(t);
    std::mem::drop(tmp_4);
    tmp_6
  });
  let callback_1: Rc<dyn Fn(Int63) -> Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>>>> = Rc::new({
    move |n: Int63| -> Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>>> {
      let v28 = &callback;
      let tmp_7: Rc<dyn Fn(Int63, Array<Int63>, Array<Int63>, Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> = Rc::clone(v28);
      let callback_2: Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>>> = Rc::new({
        move |y1: Array<Int63>| -> Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>> {
          let v36 = &tmp_7;
          let n = &n;
          let tmp_8: Rc<dyn Fn(Int63, Array<Int63>, Array<Int63>, Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> = Rc::clone(v36);
          let n_clone = Clone::clone(n);
          let callback_3: Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>> = Rc::new({
            move |y2: Array<Int63>| -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> {
              let v48 = &tmp_8;
              let n = &n_clone;
              let y1 = &y1;
              let tmp_9: Rc<dyn Fn(Int63, Array<Int63>, Array<Int63>, Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> = Rc::clone(v48);
              let n_clone_1 = Clone::clone(n);
              let y1_clone = Clone::clone(y1);
              let callback_4: Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> = Rc::new({
                move |t: Rc<tree>| -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>> {
                  let v64 = &tmp_9;
                  let tmp_10: Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>> = v64(Clone::clone(&n_clone_1), Clone::clone(&y1_clone), Clone::clone(&y2), t);
                  tmp_10
                }
              });
              callback_4
            }
          });
          callback_3
        }
      });
      callback_2
    }
  });
  callback_1
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.sweep (local: sweep)
// Variant: lifted
pub fn sweep_curried(n: Int63) -> Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>>> {
  let callback: Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>>> = Rc::new({
    move |y1: Array<Int63>| -> Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>> {
      let n = &n;
      let n_clone = Clone::clone(n);
      let callback_1: Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>> = Rc::new({
        move |y2: Array<Int63>| -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> {
          let n = &n_clone;
          let y1 = &y1;
          let n_clone_1 = Clone::clone(n);
          let y1_clone = Clone::clone(y1);
          let callback_2: Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>> = Rc::new({
            move |t: Rc<tree>| -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>> {
              let n = &n_clone_1;
              let y1 = &y1_clone;
              let y2 = &y2;
              let n_clone_2 = Clone::clone(n);
              let y1_clone_1 = Clone::clone(y1);
              let y2_clone = Clone::clone(y2);
              let callback_3: Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>> = Rc::new({
                move |s: Rc<tree>| -> Rc<option<Rc<tree>>> {
                  let tmp = Clone::clone(&n_clone_2);
                  let tmp_1 = Clone::clone(&y1_clone_1);
                  let tmp_2 = Clone::clone(&y2_clone);
                  let t_clone = Rc::clone(&t);
                  sweep(tmp, tmp_1, tmp_2, t_clone, s)
                }
              });
              callback_3
            }
          });
          callback_2
        }
      });
      callback_1
    }
  });
  callback
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.sweep (local: sweep)
// Variant: uncurried, lifted
pub fn sweep(n: Int63, y1: Array<Int63>, y2: Array<Int63>, t: Rc<tree>, s: Rc<tree>) -> Rc<option<Rc<tree>>> {
  let (v5, v6) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v6);
  match v5 {
    tree::Leaf => {
      std::mem::drop(y1);
      std::mem::drop(y2);
      Rc::new(option::<Rc<tree>>::Some(s))
    },
    tree::Node(v22, _v24, v26, v28, _v30) => {
      let y1_clone = Clone::clone(&y1);
      let y2_clone = Clone::clone(&y2);
      let tmp = sweep(n, y1_clone, y2_clone, v22, s);
      let (v46, v47) = __rocq_reuse::reset(tmp, |__payload| Clone::clone(__payload));
      match v46 {
        option::Some(v52) => {
          std::mem::drop(v47);
          let y1_clone_1 = Clone::clone(&y1);
          let y2_clone_1 = Clone::clone(&y2);
          let tmp_1 = step(n, y1_clone_1, y2_clone_1, v26, v52);
          let (v68, v69) = __rocq_reuse::reset(tmp_1, |__payload| Clone::clone(__payload));
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

// Rocq: Intersectingrectangles.intersectingrectangles_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.height
// Variant: borrowed
pub fn height(t: &Rc<tree>) -> Int63 {
  let tmp = t;
  match &**tmp {
    tree::Leaf => {
      int63!(0)
    },
    tree::Node(_h, _t1, _i0, _i, t0) => {
      Clone::clone(t0)
    },
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.hmax
// Variant: uncurried
pub fn hmax(a_1: Int63, b_1: Int63) -> Int63 {
  if a_1 < b_1 {
    b_1
  } else {
    a_1
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.node
// Variant: uncurried
pub fn node(l: Rc<tree>, k: Int63, v: Int63, r: Rc<tree>) -> Rc<tree> {
  let tmp = height(&l);
  let tmp_1 = height(&r);
  Rc::new(tree::Node(l, k, v, r, hmax(tmp, tmp_1) + int63!(1)))
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.bal
// Variant: uncurried
pub fn bal(l: Rc<tree>, k: Int63, v: Int63, r: Rc<tree>) -> Rc<tree> {
  let hl = height(&l);
  let hr = height(&r);
  let tmp = hr + int63!(2);
  if tmp < hl {
    match &*l {
      tree::Leaf => {
        node(l, k, v, r)
      },
      tree::Node(i, lr, lv, lk, _ll) => {
        let tmp_1 = height(lk);
        let tmp_2 = height(i);
        if tmp_1 <= tmp_2 {
          let tmp_3 = node(Rc::clone(lk), k, v, r);
          let i_clone = Rc::clone(i);
          let lr_clone = Clone::clone(lr);
          let lv_clone = Clone::clone(lv);
          std::mem::drop(l);
          node(i_clone, lr_clone, lv_clone, tmp_3)
        } else {
          match &**lk {
            tree::Leaf => {
              node(l, k, v, r)
            },
            tree::Node(i_1, lrr, lrv, lrk, _lrl) => {
              let tmp_4 = node(Rc::clone(i), Clone::clone(lr), Clone::clone(lv), Rc::clone(i_1));
              let tmp_5 = node(Rc::clone(lrk), k, v, r);
              let lrr_clone = Clone::clone(lrr);
              let lrv_clone = Clone::clone(lrv);
              std::mem::drop(l);
              node(tmp_4, lrr_clone, lrv_clone, tmp_5)
            },
          }
        }
      },
    }
  } else {
    let tmp_6 = hl + int63!(2);
    if tmp_6 < hr {
      match &*r {
        tree::Leaf => {
          node(l, k, v, r)
        },
        tree::Node(i, rr, rv, rk, _rl) => {
          let tmp_7 = height(i);
          let tmp_8 = height(rk);
          if tmp_7 <= tmp_8 {
            let tmp_9 = node(l, k, v, Rc::clone(i));
            let rr_clone = Clone::clone(rr);
            let rv_clone = Clone::clone(rv);
            let rk_clone = Rc::clone(rk);
            std::mem::drop(r);
            node(tmp_9, rr_clone, rv_clone, rk_clone)
          } else {
            match &**i {
              tree::Leaf => {
                node(l, k, v, r)
              },
              tree::Node(i_1, rlr, rlv, rlk, _rll) => {
                let tmp_10 = node(l, k, v, Rc::clone(i_1));
                let tmp_11 = node(Rc::clone(rlk), Clone::clone(rr), Clone::clone(rv), Rc::clone(rk));
                let rlr_clone = Clone::clone(rlr);
                let rlv_clone = Clone::clone(rlv);
                std::mem::drop(r);
                node(tmp_10, rlr_clone, rlv_clone, tmp_11)
              },
            }
          }
        },
      }
    } else {
      node(l, k, v, r)
    }
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.insert
// Variant: uncurried
pub fn insert_1(k: Int63, v: Int63, t: Rc<tree>) -> Rc<tree> {
  insert(k, v, t)
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.insert (local: insert)
// Variant: uncurried, lifted
pub fn insert(k: Int63, v: Int63, t: Rc<tree>) -> Rc<tree> {
  let (v3, v4) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  match v3 {
    tree::Leaf => {
      let tmp = __rocq_reuse::rebuild(v4, tree::Leaf);
      let tmp_1 = Rc::new(tree::Leaf);
      Rc::new(tree::Node(tmp, k, v, tmp_1, int63!(1)))
    },
    tree::Node(v36, v38, v40, v42, v44) => {
      if k.ltsb(v38) {
        std::mem::drop(v4);
        bal(insert(k, v, v36), v38, v40, v42)
      } else {
        if v38.ltsb(k) {
          std::mem::drop(v4);
          bal(v36, v38, v40, insert(k, v, v42))
        } else {
          __rocq_reuse::rebuild(v4, tree::Node(v36, k, v, v42, v44))
        }
      }
    },
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.build
// Variant: uncurried
pub fn build_1(x1: Array<Int63>, x2: Array<Int63>, n: Int63, i: Int63, t: Rc<tree>) -> Rc<tree> {
  build(x1, x2, n, i, t, ())
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(x1: Array<Int63>, x2: Array<Int63>, n: Int63, i: Int63, t: Rc<tree>, _H: ()) -> Rc<tree> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = x2.get_cloned(i);
      let tmp_3 = n + i;
      let tmp_4 = x1.get_cloned(i);
      let tmp_5 = insert_1(tmp_4, i, t);
      build(x1, x2, n, tmp_1, insert_1(tmp_2, tmp_3, tmp_5), ())
    },
    sumbool::right => {
      std::mem::drop(x1);
      std::mem::drop(x2);
      t
    },
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.between
// Variant: borrowed, uncurried
pub fn between_1(lo: Int63, hi: Int63, t: &Rc<tree>) -> bool {
  let lo_1 = lo;
  let hi_1 = hi;
  between(lo_1, hi_1, t)
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.between (local: between)
// Variant: borrowed, uncurried, lifted
pub fn between(lo: Int63, hi: Int63, t: &Rc<tree>) -> bool {
  let lo_1 = lo;
  let hi_1 = hi;
  let tmp = t;
  match &**tmp {
    tree::Leaf => {
      false
    },
    tree::Node(i0, r, _i, k, _l) => {
      let r_clone = Clone::clone(r);
      if r_clone.lesb(lo_1) {
        between(lo_1, hi_1, k)
      } else {
        let r_clone_1 = Clone::clone(r);
        if hi_1.lesb(r_clone_1) {
          between(lo_1, hi_1, i0)
        } else {
          true
        }
      }
    },
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.remove_min
// Variant: uncurried
pub fn remove_min_1(l: Rc<tree>, k: Int63, v: Int63, r: Rc<tree>) -> ((Int63, Int63), Rc<tree>) {
  remove_min(l, k, v, r)
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.remove_min (local: remove_min)
// Variant: uncurried, lifted
pub fn remove_min(l: Rc<tree>, k: Int63, v: Int63, r: Rc<tree>) -> ((Int63, Int63), Rc<tree>) {
  match &*l {
    tree::Leaf => {
      std::mem::drop(l);
      ((k, v), r)
    },
    tree::Node(i, lr, lv, lk, _ll) => {
      let i_clone = Rc::clone(i);
      let lr_clone = Clone::clone(lr);
      let lv_clone = Clone::clone(lv);
      let lk_clone = Rc::clone(lk);
      std::mem::drop(l);
      let tmp = remove_min(i_clone, lr_clone, lv_clone, lk_clone);
      match tmp {
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
          let i_clone = Rc::clone(i_1);
          let rr_clone = Clone::clone(rr);
          let rv_clone = Clone::clone(rv);
          let rk_clone = Rc::clone(rk);
          std::mem::drop(r);
          let tmp = remove_min_1(i_clone, rr_clone, rv_clone, rk_clone);
          match tmp {
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
pub fn remove_1(k: Int63, t: Rc<tree>) -> Rc<tree> {
  remove(k, t)
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.remove (local: remove)
// Variant: uncurried, lifted
pub fn remove(k: Int63, t: Rc<tree>) -> Rc<tree> {
  let (v2, v3) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  match v2 {
    tree::Leaf => {
      __rocq_reuse::rebuild(v3, tree::Leaf)
    },
    tree::Node(v17, v19, v21, v23, _v25) => {
      std::mem::drop(v3);
      if k.ltsb(v19) {
        bal(remove(k, v17), v19, v21, v23)
      } else {
        if v19.ltsb(k) {
          bal(v17, v19, v21, remove(k, v23))
        } else {
          merge(v17, v23)
        }
      }
    },
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.step
// Variant: uncurried
pub fn step(n: Int63, y1: Array<Int63>, y2: Array<Int63>, v: Int63, s: Rc<tree>) -> Rc<option<Rc<tree>>> {
  if v < n {
    let lo = y1.get_cloned(v);
    let hi = y2.get_cloned(v);
    if between_1(lo, hi, &s) {
      std::mem::drop(y1);
      std::mem::drop(y2);
      std::mem::drop(s);
      Rc::new(option::<Rc<tree>>::None)
    } else {
      std::mem::drop(y1);
      std::mem::drop(y2);
      let tmp = insert_1(lo, int63!(0), s);
      Rc::new(option::<Rc<tree>>::Some(insert_1(hi, int63!(0), tmp)))
    }
  } else {
    let i = v - n;
    let lo = y1.get_cloned(i);
    let hi = y2.get_cloned(i);
    let tmp_1 = remove_1(lo, s);
    let s_ = remove_1(hi, tmp_1);
    if between_1(lo, hi, &s_) {
      std::mem::drop(y1);
      std::mem::drop(y2);
      std::mem::drop(s_);
      Rc::new(option::<Rc<tree>>::None)
    } else {
      std::mem::drop(y1);
      std::mem::drop(y2);
      Rc::new(option::<Rc<tree>>::Some(s_))
    }
  }
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.sweep
// Variant: uncurried
pub fn sweep_2(n: Int63, y1: Array<Int63>, y2: Array<Int63>, t: Rc<tree>, s: Rc<tree>) -> Rc<option<Rc<tree>>> {
  sweep_1(n, y1, y2, t, s)
}

// Rocq: Intersectingrectangles.intersectingrectangles_implem.sweep (local: sweep)
// Variant: uncurried, lifted
pub fn sweep_1(n: Int63, y1: Array<Int63>, y2: Array<Int63>, t: Rc<tree>, s: Rc<tree>) -> Rc<option<Rc<tree>>> {
  let (v5, v6) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v6);
  match v5 {
    tree::Leaf => {
      std::mem::drop(y1);
      std::mem::drop(y2);
      Rc::new(option::<Rc<tree>>::Some(s))
    },
    tree::Node(v22, _v24, v26, v28, _v30) => {
      let y1_clone = Clone::clone(&y1);
      let y2_clone = Clone::clone(&y2);
      let tmp = sweep_1(n, y1_clone, y2_clone, v22, s);
      let (v46, v47) = __rocq_reuse::reset(tmp, |__payload| Clone::clone(__payload));
      match v46 {
        option::Some(v52) => {
          std::mem::drop(v47);
          let y1_clone_1 = Clone::clone(&y1);
          let y2_clone_1 = Clone::clone(&y2);
          let tmp_1 = step(n, y1_clone_1, y2_clone_1, v26, v52);
          let (v68, v69) = __rocq_reuse::reset(tmp_1, |__payload| Clone::clone(__payload));
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
pub fn intersecting_rectangles_impl(x1: Array<Int63>, y1: Array<Int63>, x2: Array<Int63>, y2: Array<Int63>) -> bool {
  let n = x1.length();
  let ev = build_1(x1, x2, n, int63!(0), Rc::new(tree::Leaf));
  let tmp = sweep_2(n, y1, y2, ev, Rc::new(tree::Leaf));
  let (v38, v39) = __rocq_reuse::reset(tmp, |__payload| Clone::clone(__payload));
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
std::thread_local! { static __rocq_global_617: Rc<dyn Fn(Int63) -> Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Array<Int63>) -> Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<option<Rc<tree>>>>>>>> = sweep_curried_1(); }