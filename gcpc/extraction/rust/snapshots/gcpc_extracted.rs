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

pub enum tree {
  Leaf,
  Node(Rc<tree>, Int63, Rc<tree>, Int63, Int63),
}

impl Clone for tree {
  fn clone(&self) -> Self {
    match self {
      tree::Leaf => tree::Leaf,
      tree::Node(__field0, __field1, __field2, __field3, __field4) => tree::Node(Clone::clone(__field0), Clone::clone(__field1), Clone::clone(__field2), Clone::clone(__field3), Clone::clone(__field4)),
    }
  }
}

pub type uint = Int63;

// Rocq: Gcpc.gcpc_implem.K0
pub fn K0() -> Int63 {
  int63!(2305825417027649536)
}

// Rocq: Gcpc.gcpc_implem.KD
pub fn KD() -> Int63 {
  int63!(17592186044416)
}

// Rocq: Gcpc.gcpc_implem.KE
pub fn KE() -> Int63 {
  int63!(131072)
}

// Rocq: Gcpc.gcpc_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Gcpc.gcpc_implem.size
// Variant: borrowed
pub fn size(t: &Rc<tree>) -> Int63 {
  let tmp = t;
  match &**tmp {
    tree::Leaf => {
      int63!(0)
    },
    tree::Node(_i0, _s, _t1, i, _t0) => {
      Clone::clone(i)
    },
  }
}

// Rocq: Gcpc.gcpc_implem.height
pub fn height_owned(t: Rc<tree>) -> Int63 {
  let (v1, v2) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v2);
  match v1 {
    tree::Leaf => {
      int63!(0)
    },
    tree::Node(v15, _v17, v19, _v21, v23) => {
      std::mem::drop(v15);
      std::mem::drop(v19);
      v23
    },
  }
}

// Rocq: Gcpc.gcpc_implem.height
// Variant: borrowed
pub fn height(t: &Rc<tree>) -> Int63 {
  let tmp = t;
  match &**tmp {
    tree::Leaf => {
      int63!(0)
    },
    tree::Node(_h, _i0, _t1, _i, t0) => {
      Clone::clone(t0)
    },
  }
}

// Rocq: Gcpc.gcpc_implem.mk
// Variant: uncurried
pub fn mk(l: Rc<tree>, k: Int63, r: Rc<tree>) -> Rc<tree> {
  let tmp = size(&l) + size(&r) + int63!(1);
  let tmp_1 = height(&l);
  let tmp_2 = height(&r);
  let tmp_3 = if tmp_1 < tmp_2 {
    let r_clone = Rc::clone(&r);
    height_owned(r_clone) + int63!(1)
  } else {
    let l_clone = Rc::clone(&l);
    height_owned(l_clone) + int63!(1)
  };
  Rc::new(tree::Node(l, k, r, tmp, tmp_3))
}

// Rocq: Gcpc.gcpc_implem.bal
// Variant: uncurried
pub fn bal(l: Rc<tree>, k: Int63, r: Rc<tree>) -> Rc<tree> {
  let hl = height(&l);
  let hr = height(&r);
  let tmp = hr + int63!(2);
  if tmp < hl {
    match &*l {
      tree::Leaf => {
        mk(l, k, r)
      },
      tree::Node(i0, i, lr, _lk, _ll) => {
        let tmp_1 = height(lr);
        let tmp_2 = height(i0);
        if tmp_1 <= tmp_2 {
          let tmp_3 = mk(Rc::clone(lr), k, r);
          let i0_clone = Rc::clone(i0);
          let i_clone = Clone::clone(i);
          std::mem::drop(l);
          mk(i0_clone, i_clone, tmp_3)
        } else {
          match &**lr {
            tree::Leaf => {
              mk(l, k, r)
            },
            tree::Node(i0_1, i_1, lrr, _lrk, _lrl) => {
              let tmp_4 = mk(Rc::clone(i0), Clone::clone(i), Rc::clone(i0_1));
              let tmp_5 = mk(Rc::clone(lrr), k, r);
              let i_clone_1 = Clone::clone(i_1);
              std::mem::drop(l);
              mk(tmp_4, i_clone_1, tmp_5)
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
          mk(l, k, r)
        },
        tree::Node(i0, i, rr, _rk, _rl) => {
          let tmp_7 = height(i0);
          let tmp_8 = height(rr);
          if tmp_7 <= tmp_8 {
            let tmp_9 = mk(l, k, Rc::clone(i0));
            let i_clone_2 = Clone::clone(i);
            let rr_clone = Rc::clone(rr);
            std::mem::drop(r);
            mk(tmp_9, i_clone_2, rr_clone)
          } else {
            match &**i0 {
              tree::Leaf => {
                mk(l, k, r)
              },
              tree::Node(i0_1, i_1, rlr, _rlk, _rll) => {
                let tmp_10 = mk(l, k, Rc::clone(i0_1));
                let tmp_11 = mk(Rc::clone(rlr), Clone::clone(i), Rc::clone(rr));
                let i_clone_3 = Clone::clone(i_1);
                std::mem::drop(r);
                mk(tmp_10, i_clone_3, tmp_11)
              },
            }
          }
        },
      }
    } else {
      mk(l, k, r)
    }
  }
}

// Rocq: Gcpc.gcpc_implem.insert
// Variant: uncurried
pub fn insert_1(x: Int63, t: Rc<tree>) -> Rc<tree> {
  insert(x, t)
}

// Rocq: Gcpc.gcpc_implem.insert (local: insert)
// Variant: uncurried, lifted
pub fn insert(x: Int63, t: Rc<tree>) -> Rc<tree> {
  match &*t {
    tree::Leaf => {
      std::mem::drop(t);
      mk(Rc::new(tree::Leaf), x, Rc::new(tree::Leaf))
    },
    tree::Node(i0, i, r, _k, _l) => {
      let i_clone = Clone::clone(i);
      if x < i_clone {
        let tmp = insert(x, Rc::clone(i0));
        let i_clone_1 = Clone::clone(i);
        let r_clone = Rc::clone(r);
        std::mem::drop(t);
        bal(tmp, i_clone_1, r_clone)
      } else {
        let i_clone_2 = Clone::clone(i);
        if i_clone_2 < x {
          let tmp_1 = insert(x, Rc::clone(r));
          let i0_clone = Rc::clone(i0);
          let i_clone_3 = Clone::clone(i);
          std::mem::drop(t);
          bal(i0_clone, i_clone_3, tmp_1)
        } else {
          t
        }
      }
    },
  }
}

// Rocq: Gcpc.gcpc_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(n1: Int63, k: Int63, keys: Array<Int63>, T: Rc<tree>) -> (Array<Int63>, Rc<tree>) {
  init_loop(n1, k, keys, T, ())
}

// Rocq: Gcpc.gcpc_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(n1: Int63, k: Int63, keys: Array<Int63>, T: Rc<tree>, _H: ()) -> (Array<Int63>, Rc<tree>) {
  let tmp = k < n1;
  match bdec(tmp) {
    sumbool::left => {
      let key = __rocq_global_36 + k;
      init_loop(n1, k + int63!(1), keys.set(k, key), insert_1(key, T), ())
    },
    sumbool::right => {
      (keys, T)
    },
  }
}

// Rocq: Gcpc.gcpc_implem.remove_min
// Variant: uncurried
pub fn remove_min_1(l: Rc<tree>, k: Int63, r: Rc<tree>) -> (Int63, Rc<tree>) {
  remove_min(l, k, r)
}

// Rocq: Gcpc.gcpc_implem.remove_min (local: remove_min)
// Variant: uncurried, lifted
pub fn remove_min(l: Rc<tree>, k: Int63, r: Rc<tree>) -> (Int63, Rc<tree>) {
  match &*l {
    tree::Leaf => {
      std::mem::drop(l);
      (k, r)
    },
    tree::Node(i0, i, lr, _lk, _ll) => {
      let i0_clone = Rc::clone(i0);
      let i_clone = Clone::clone(i);
      let lr_clone = Rc::clone(lr);
      std::mem::drop(l);
      let tmp = remove_min(i0_clone, i_clone, lr_clone);
      match tmp {
        (v32, v34) => {
          (v32, bal(v34, k, r))
        },
      }
    },
  }
}

// Rocq: Gcpc.gcpc_implem.merge
// Variant: uncurried
pub fn merge(l: Rc<tree>, r: Rc<tree>) -> Rc<tree> {
  match &*l {
    tree::Leaf => {
      std::mem::drop(l);
      r
    },
    tree::Node(_i1, _i0, _t0, _i, _t) => {
      match &*r {
        tree::Leaf => {
          std::mem::drop(r);
          l
        },
        tree::Node(i3, i2, rr, _rk, _rl) => {
          let i3_clone = Rc::clone(i3);
          let i2_clone = Clone::clone(i2);
          let rr_clone = Rc::clone(rr);
          std::mem::drop(r);
          let tmp = remove_min_1(i3_clone, i2_clone, rr_clone);
          match tmp {
            (v39, v41) => {
              bal(l, v39, v41)
            },
          }
        },
      }
    },
  }
}

// Rocq: Gcpc.gcpc_implem.delete
// Variant: uncurried
pub fn delete_1(x: Int63, t: Rc<tree>) -> Rc<tree> {
  delete(x, t)
}

// Rocq: Gcpc.gcpc_implem.delete (local: delete)
// Variant: uncurried, lifted
pub fn delete(x: Int63, t: Rc<tree>) -> Rc<tree> {
  let (v2, v3) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  match v2 {
    tree::Leaf => {
      __rocq_reuse::rebuild(v3, tree::Leaf)
    },
    tree::Node(v17, v19, v21, _v23, _v25) => {
      std::mem::drop(v3);
      if x < v19 {
        bal(delete(x, v17), v19, v21)
      } else {
        if v19 < x {
          bal(v17, v19, delete(x, v21))
        } else {
          merge(v17, v21)
        }
      }
    },
  }
}

// Rocq: Gcpc.gcpc_implem.count_lt
// Variant: borrowed, uncurried
pub fn count_lt_1(q: Int63, t: &Rc<tree>) -> Int63 {
  let q_1 = q;
  count_lt(q_1, t)
}

// Rocq: Gcpc.gcpc_implem.count_lt (local: count_lt)
// Variant: borrowed, uncurried, lifted
pub fn count_lt(q: Int63, t: &Rc<tree>) -> Int63 {
  let q_1 = q;
  let tmp = t;
  match &**tmp {
    tree::Leaf => {
      int63!(0)
    },
    tree::Node(i0, i, r, _k, _l) => {
      let i_clone = Clone::clone(i);
      if i_clone < q_1 {
        let tmp_1 = size(i0) + int63!(1);
        let tmp_2 = count_lt(q_1, r);
        tmp_1 + tmp_2
      } else {
        count_lt(q_1, i0)
      }
    },
  }
}

// Rocq: Gcpc.gcpc_implem.ev_loop
// Variant: uncurried
pub fn ev_loop_1(xt: Array<Int63>, xp: Array<Int63>, m: Int63, j: Int63, keys: Array<Int63>, T: Rc<tree>, out: Array<Int63>) -> Array<Int63> {
  ev_loop(xt, xp, m, j, keys, T, out, ())
}

// Rocq: Gcpc.gcpc_implem.ev_loop (local: ev_loop)
// Variant: uncurried, lifted
pub fn ev_loop(xt: Array<Int63>, xp: Array<Int63>, m: Int63, j: Int63, keys: Array<Int63>, T: Rc<tree>, out: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = j < m;
  match bdec(tmp) {
    sumbool::left => {
      let a_1 = xt.get_cloned(j);
      let old = keys.get_cloned(a_1);
      let tmp_1 = old - __rocq_global_317;
      let tmp_2 = xp.get_cloned(j);
      let new = tmp_1 + tmp_2 * __rocq_global_334;
      let keys_ = keys.set(a_1, new);
      let T_ = insert_1(new, delete_1(old, T));
      let tmp_3 = keys_.get_cloned(int63!(1));
      let tmp_4 = count_lt_1(tmp_3 - int63!(1), &T_);
      let ans = tmp_4 + int63!(1);
      ev_loop(xt, xp, m, j + int63!(1), keys_, T_, out.set(j, ans), ())
    },
    sumbool::right => {
      std::mem::drop(xt);
      std::mem::drop(xp);
      std::mem::drop(keys);
      std::mem::drop(T);
      out
    },
  }
}

// Rocq: Gcpc.gcpc_implem.gcpc_impl
// Variant: uncurried
pub fn gcpc_impl(n: Int63, xt: Array<Int63>, xp: Array<Int63>) -> Array<Int63> {
  let m = xt.length();
  let n1 = n + int63!(1);
  let tmp = Array::<Int63>::make(n1, int63!(0));
  let tmp_1 = init_loop_1(n1, int63!(1), tmp, Rc::new(tree::Leaf));
  match tmp_1 {
    (v36, v38) => {
      let tmp_2 = Array::<Int63>::make(m, int63!(0));
      ev_loop_1(xt, xp, m, int63!(0), v36, v38, tmp_2)
    },
  }
}
const __rocq_global_36: Int63 = int63!(2305825417027649536);
const __rocq_global_317: Int63 = int63!(17592186044416);
const __rocq_global_334: Int63 = int63!(131072);