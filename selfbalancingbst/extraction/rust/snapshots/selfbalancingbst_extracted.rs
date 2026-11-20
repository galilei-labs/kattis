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

pub enum tree {
  Leaf,
  Node { c: color, l: Rc<tree>, k: Int63, v: Int63, s: Int63, r: Rc<tree> },
}

impl Clone for tree {
  fn clone(&self) -> Self {
    match self {
      tree::Leaf => tree::Leaf,
      tree::Node { c: __field0, l: __field1, k: __field2, v: __field3, s: __field4, r: __field5 } => tree::Node { c: Clone::clone(__field0), l: Clone::clone(__field1), k: Clone::clone(__field2), v: Clone::clone(__field3), s: Clone::clone(__field4), r: Clone::clone(__field5) },
    }
  }
}

#[derive(Clone, Copy)]
pub enum color {
  Red,
  Black,
}

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub enum operation<U: 'static, S: 'static> {
  CopyFrom { source: U },
  FindKey { key: S },
  LowerBound { key: S },
  UpperBound { key: S },
  Insert { key: S, value: S },
  Erase,
  First,
  Last,
  NextKey,
  PreviousKey,
  SelectRank { index: S },
  GetRank,
  GetValue,
  SetValue { value: S },
  GetSize,
}

impl<U: Clone + 'static, S: Clone + 'static> Clone for operation<U, S> {
  fn clone(&self) -> Self {
    match self {
      operation::CopyFrom { source: __field0 } => operation::CopyFrom { source: Clone::clone(__field0) },
      operation::FindKey { key: __field0 } => operation::FindKey { key: Clone::clone(__field0) },
      operation::LowerBound { key: __field0 } => operation::LowerBound { key: Clone::clone(__field0) },
      operation::UpperBound { key: __field0 } => operation::UpperBound { key: Clone::clone(__field0) },
      operation::Insert { key: __field0, value: __field1 } => operation::Insert { key: Clone::clone(__field0), value: Clone::clone(__field1) },
      operation::Erase => operation::Erase,
      operation::First => operation::First,
      operation::Last => operation::Last,
      operation::NextKey => operation::NextKey,
      operation::PreviousKey => operation::PreviousKey,
      operation::SelectRank { index: __field0 } => operation::SelectRank { index: Clone::clone(__field0) },
      operation::GetRank => operation::GetRank,
      operation::GetValue => operation::GetValue,
      operation::SetValue { value: __field0 } => operation::SetValue { value: Clone::clone(__field0) },
      operation::GetSize => operation::GetSize,
    }
  }
}

pub type uint = Int63;

pub type sint = Int63;

pub type machine_command = (Int63, Rc<operation<Int63, Int63>>);

// Rocq: Selfbalancingbst.selfbalancingbst_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.output_command
pub fn output_command(line: (Int63, Rc<operation<Int63, Int63>>)) -> bool {
  match line {
    (_v2, v4) => {
      let (v6, v7) = __rocq_reuse::reset(v4, |__payload| Clone::clone(__payload));
      std::mem::drop(v7);
      match v6 {
        operation::CopyFrom { source: _v19 } => {
          false
        },
        operation::FindKey { key: _v25 } => {
          false
        },
        operation::LowerBound { key: _v31 } => {
          false
        },
        operation::UpperBound { key: _v37 } => {
          false
        },
        operation::Insert { key: _v43, value: _v45 } => {
          false
        },
        operation::Erase => {
          false
        },
        operation::First => {
          false
        },
        operation::Last => {
          false
        },
        operation::NextKey => {
          false
        },
        operation::PreviousKey => {
          false
        },
        operation::SelectRank { index: _v71 } => {
          false
        },
        operation::GetRank => {
          true
        },
        operation::GetValue => {
          true
        },
        operation::SetValue { value: _v85 } => {
          false
        },
        operation::GetSize => {
          true
        },
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.count_loop
// Variant: uncurried
pub fn count_loop_1(ops: Array<(Int63, Rc<operation<Int63, Int63>>)>, q: Int63, j: Int63, acc: Int63) -> Int63 {
  count_loop(ops, q, j, acc, ())
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.count_loop (local: count_loop)
// Variant: uncurried, lifted
pub fn count_loop(ops: Array<(Int63, Rc<operation<Int63, Int63>>)>, q: Int63, j: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = j < q;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = j + int63!(1);
      let ops_ref = &ops;
      let tmp_2 = ops_ref.get_cloned(j);
      let tmp_3 = if output_command(tmp_2) {
        acc + int63!(1)
      } else {
        acc
      };
      count_loop(ops, q, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(ops);
      acc
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.encode_operation
// Variant: uncurried
pub fn encode_operation<U: Clone + 'static, S: Clone + 'static>(zero: S, source: Rc<dyn Fn(U) -> S>, op: Rc<operation<U, S>>) -> ((Int63, S), S) {
  let (v3, v4) = __rocq_reuse::reset(op, |__payload| match __payload {
    operation::CopyFrom { source: __field0 } => operation::CopyFrom { source: Clone::clone(__field0) },
    operation::FindKey { key: __field0 } => operation::FindKey { key: Clone::clone(__field0) },
    operation::LowerBound { key: __field0 } => operation::LowerBound { key: Clone::clone(__field0) },
    operation::UpperBound { key: __field0 } => operation::UpperBound { key: Clone::clone(__field0) },
    operation::Insert { key: __field0, value: __field1 } => operation::Insert { key: Clone::clone(__field0), value: Clone::clone(__field1) },
    operation::Erase => operation::Erase,
    operation::First => operation::First,
    operation::Last => operation::Last,
    operation::NextKey => operation::NextKey,
    operation::PreviousKey => operation::PreviousKey,
    operation::SelectRank { index: __field0 } => operation::SelectRank { index: Clone::clone(__field0) },
    operation::GetRank => operation::GetRank,
    operation::GetValue => operation::GetValue,
    operation::SetValue { value: __field0 } => operation::SetValue { value: Clone::clone(__field0) },
    operation::GetSize => operation::GetSize,
  });
  std::mem::drop(v4);
  match v3 {
    operation::CopyFrom { source: v16 } => {
      let tmp = int63!(97);
      let source_ref: &Rc<dyn Fn(U) -> S> = &source;
      let tmp_1 = source_ref(v16);
      std::mem::drop(source);
      ((tmp, tmp_1), zero)
    },
    operation::FindKey { key: v38 } => {
      std::mem::drop(source);
      ((int63!(63), v38), zero)
    },
    operation::LowerBound { key: v56 } => {
      std::mem::drop(source);
      ((int63!(108), v56), zero)
    },
    operation::UpperBound { key: v74 } => {
      std::mem::drop(source);
      ((int63!(117), v74), zero)
    },
    operation::Insert { key: v92, value: v94 } => {
      std::mem::drop(zero);
      std::mem::drop(source);
      ((int63!(105), v92), v94)
    },
    operation::Erase => {
      std::mem::drop(source);
      let zero_clone = Clone::clone(&zero);
      ((int63!(101), zero_clone), zero)
    },
    operation::First => {
      std::mem::drop(source);
      let zero_clone_1 = Clone::clone(&zero);
      ((int63!(102), zero_clone_1), zero)
    },
    operation::Last => {
      std::mem::drop(source);
      let zero_clone_2 = Clone::clone(&zero);
      ((int63!(98), zero_clone_2), zero)
    },
    operation::NextKey => {
      std::mem::drop(source);
      let zero_clone_3 = Clone::clone(&zero);
      ((int63!(62), zero_clone_3), zero)
    },
    operation::PreviousKey => {
      std::mem::drop(source);
      let zero_clone_4 = Clone::clone(&zero);
      ((int63!(60), zero_clone_4), zero)
    },
    operation::SelectRank { index: v197 } => {
      std::mem::drop(source);
      ((int63!(107), v197), zero)
    },
    operation::GetRank => {
      std::mem::drop(source);
      let zero_clone_5 = Clone::clone(&zero);
      ((int63!(114), zero_clone_5), zero)
    },
    operation::GetValue => {
      std::mem::drop(source);
      let zero_clone_6 = Clone::clone(&zero);
      ((int63!(103), zero_clone_6), zero)
    },
    operation::SetValue { value: v249 } => {
      std::mem::drop(source);
      ((int63!(115), v249), zero)
    },
    operation::GetSize => {
      std::mem::drop(source);
      let zero_clone_7 = Clone::clone(&zero);
      ((int63!(122), zero_clone_7), zero)
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.encode_machine
#[inline(never)]
pub fn encode_machine(line: (Int63, Rc<operation<Int63, Int63>>)) -> (((Int63, Int63), Int63), Int63) {
  match line {
    (v2, v4) => {
      let tmp = int63!(0);
      let callback: Rc<dyn Fn(Int63) -> Int63> = Rc::new(move |id: Int63| -> Int63 {
        id
      });
      let tmp_1 = encode_operation::<Int63, Int63>(tmp, callback, v4);
      match tmp_1 {
        (v23, v25) => {
          match v23 {
            (v28, v30) => {
              (((v2, v28), v30), v25)
            },
          }
        },
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.key_lt
// Variant: uncurried
pub fn key_lt(a_1: Int63, b_1: Int63) -> bool {
  a_1.ltsb(b_1)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.find_t
// Variant: uncurried
pub fn find_t_1(x: Int63, t: Rc<tree>) -> Rc<option<Int63>> {
  find_t(x, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.find_t (local: find_t)
// Variant: uncurried, lifted
pub fn find_t(x: Int63, t: Rc<tree>) -> Rc<option<Int63>> {
  let (v2, v3) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v3);
  match v2 {
    tree::Leaf => {
      Rc::new(option::<Int63>::None)
    },
    tree::Node { c: _v18, l: v20, k: v22, v: _v24, s: _v26, r: v28 } => {
      if key_lt(x, v22) {
        std::mem::drop(v28);
        find_t(x, v20)
      } else {
        if x == v22 {
          std::mem::drop(v20);
          std::mem::drop(v28);
          Rc::new(option::<Int63>::Some(v22))
        } else {
          std::mem::drop(v20);
          find_t(x, v28)
        }
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.lower_t
// Variant: uncurried
pub fn lower_t_1(x: Int63, t: Rc<tree>) -> Rc<option<Int63>> {
  lower_t(x, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.lower_t (local: lower_t)
// Variant: uncurried, lifted
pub fn lower_t(x: Int63, t: Rc<tree>) -> Rc<option<Int63>> {
  let (v2, v3) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v3);
  match v2 {
    tree::Leaf => {
      Rc::new(option::<Int63>::None)
    },
    tree::Node { c: _v18, l: v20, k: v22, v: _v24, s: _v26, r: v28 } => {
      if key_lt(v22, x) {
        std::mem::drop(v20);
        lower_t(x, v28)
      } else {
        let tmp = lower_t(x, v20);
        let (v51, v52) = __rocq_reuse::reset(tmp, |__payload| Clone::clone(__payload));
        match v51 {
          option::Some(v57) => {
            std::mem::drop(v28);
            __rocq_reuse::rebuild(v52, option::<Int63>::Some(v57))
          },
          option::None => {
            std::mem::drop(v28);
            __rocq_reuse::rebuild(v52, option::<Int63>::Some(v22))
          },
        }
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.upper_t
// Variant: uncurried
pub fn upper_t_owned_1(x: Int63, t: Rc<tree>) -> Rc<option<Int63>> {
  upper_t_owned(x, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.upper_t (local: upper_t)
// Variant: uncurried, lifted
pub fn upper_t_owned(x: Int63, t: Rc<tree>) -> Rc<option<Int63>> {
  let (v2, v3) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v3);
  match v2 {
    tree::Leaf => {
      Rc::new(option::<Int63>::None)
    },
    tree::Node { c: _v18, l: v20, k: v22, v: _v24, s: _v26, r: v28 } => {
      if key_lt(x, v22) {
        let tmp = upper_t_owned(x, v20);
        let (v43, v44) = __rocq_reuse::reset(tmp, |__payload| Clone::clone(__payload));
        match v43 {
          option::Some(v49) => {
            std::mem::drop(v28);
            __rocq_reuse::rebuild(v44, option::<Int63>::Some(v49))
          },
          option::None => {
            std::mem::drop(v28);
            __rocq_reuse::rebuild(v44, option::<Int63>::Some(v22))
          },
        }
      } else {
        std::mem::drop(v20);
        upper_t_owned(x, v28)
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.upper_t
// Variant: borrowed, uncurried
pub fn upper_t_1(x: Int63, t: &Rc<tree>) -> Rc<option<Int63>> {
  let x_1 = x;
  upper_t(x_1, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.upper_t (local: upper_t)
// Variant: borrowed, uncurried, lifted
pub fn upper_t(x: Int63, t: &Rc<tree>) -> Rc<option<Int63>> {
  let x_1 = x;
  let tmp = t;
  match &**tmp {
    tree::Leaf => {
      Rc::new(option::<Int63>::None)
    },
    tree::Node { c: _r, l: s, k: v, v: _k, s: _l, r: c } => {
      let v_clone = Clone::clone(v);
      if key_lt(x_1, v_clone) {
        let tmp_1 = upper_t(x_1, s);
        let (v34, v35) = __rocq_reuse::reset(tmp_1, |__payload| Clone::clone(__payload));
        match v34 {
          option::Some(v40) => {
            __rocq_reuse::rebuild(v35, option::<Int63>::Some(v40))
          },
          option::None => {
            let v_clone_1 = Clone::clone(v);
            __rocq_reuse::rebuild(v35, option::<Int63>::Some(v_clone_1))
          },
        }
      } else {
        let c_clone = Rc::clone(c);
        upper_t_owned(x_1, c_clone)
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.makeBlack
pub fn makeBlack(t: Rc<tree>) -> Rc<tree> {
  let (v1, v2) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  match v1 {
    tree::Leaf => {
      __rocq_reuse::rebuild(v2, tree::Leaf)
    },
    tree::Node { c: _v17, l: v19, k: v21, v: v23, s: v25, r: v27 } => {
      __rocq_reuse::rebuild(v2, tree::Node { c: color::Black, l: v19, k: v21, v: v23, s: v25, r: v27 })
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.size
pub fn size_owned(t: Rc<tree>) -> Int63 {
  let (v1, v2) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v2);
  match v1 {
    tree::Leaf => {
      int63!(0)
    },
    tree::Node { c: _v16, l: v18, k: _v20, v: _v22, s: v24, r: v26 } => {
      std::mem::drop(v18);
      std::mem::drop(v26);
      v24
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.size
// Variant: borrowed
pub fn size(t: &Rc<tree>) -> Int63 {
  let tmp = t;
  match &**tmp {
    tree::Leaf => {
      int63!(0)
    },
    tree::Node { c: _r, l: _s, k: _v, v: _k, s: l, r: _c } => {
      Clone::clone(l)
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.node
// Variant: uncurried
pub fn node(c: color, l: Rc<tree>, k: Int63, v: Int63, r: Rc<tree>) -> Rc<tree> {
  let tmp = size(&l);
  let tmp_1 = size(&r);
  Rc::new(tree::Node { c, l, k, v, s: tmp + tmp_1 + int63!(1), r })
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.lbal
// Variant: uncurried
pub fn lbal(l: Rc<tree>, k: Int63, v: Int63, r: Rc<tree>) -> Rc<tree> {
  match &*l {
    tree::Leaf => {
      node(color::Black, l, k, v, r)
    },
    tree::Node { c, l: s, k: vx, v: x, s: _a_1, r: c0 } => {
      match c {
        color::Red => {
          match &**s {
            tree::Leaf => {
              match &**c0 {
                tree::Leaf => {
                  node(color::Black, l, k, v, r)
                },
                tree::Node { c: c_1, l: s0, k: vy, v: y, s: _b_1, r: c1 } => {
                  match c_1 {
                    color::Red => {
                      let tmp = node(color::Black, Rc::clone(s), Clone::clone(vx), Clone::clone(x), Rc::clone(s0));
                      let tmp_1 = node(color::Black, Rc::clone(c1), k, v, r);
                      let vy_clone = Clone::clone(vy);
                      let y_clone = Clone::clone(y);
                      std::mem::drop(l);
                      node(color::Red, tmp, vy_clone, y_clone, tmp_1)
                    },
                    color::Black => {
                      node(color::Black, l, k, v, r)
                    },
                  }
                },
              }
            },
            tree::Node { c: b_1, l: s0, k: vx_1, v: x_1, s: _a_2, r: c1 } => {
              match b_1 {
                color::Red => {
                  let s0_clone = Rc::clone(s0);
                  let vx_clone = Clone::clone(vx_1);
                  let x_clone = Clone::clone(x_1);
                  let c1_clone = Rc::clone(c1);
                  let tmp_2 = node(color::Black, s0_clone, vx_clone, x_clone, c1_clone);
                  let tmp_3 = node(color::Black, Rc::clone(c0), k, v, r);
                  let vx_clone_1 = Clone::clone(vx);
                  let x_clone_1 = Clone::clone(x);
                  std::mem::drop(l);
                  node(color::Red, tmp_2, vx_clone_1, x_clone_1, tmp_3)
                },
                color::Black => {
                  match &**c0 {
                    tree::Leaf => {
                      node(color::Black, l, k, v, r)
                    },
                    tree::Node { c: c_1, l: s1, k: vy, v: y, s: _b_2, r: c2 } => {
                      match c_1 {
                        color::Red => {
                          let tmp_4 = node(color::Black, Rc::clone(s), Clone::clone(vx), Clone::clone(x), Rc::clone(s1));
                          let tmp_5 = node(color::Black, Rc::clone(c2), k, v, r);
                          let vy_clone_1 = Clone::clone(vy);
                          let y_clone_1 = Clone::clone(y);
                          std::mem::drop(l);
                          node(color::Red, tmp_4, vy_clone_1, y_clone_1, tmp_5)
                        },
                        color::Black => {
                          node(color::Black, l, k, v, r)
                        },
                      }
                    },
                  }
                },
              }
            },
          }
        },
        color::Black => {
          node(color::Black, l, k, v, r)
        },
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.rbal
// Variant: uncurried
pub fn rbal(l: Rc<tree>, k: Int63, v: Int63, r: Rc<tree>) -> Rc<tree> {
  match &*r {
    tree::Leaf => {
      node(color::Black, l, k, v, r)
    },
    tree::Node { c: d, l: s, k: vy, v: y, s: _b_1, r: c0 } => {
      match d {
        color::Red => {
          match &**s {
            tree::Leaf => {
              match &**c0 {
                tree::Leaf => {
                  node(color::Black, l, k, v, r)
                },
                tree::Node { c: d_1, l: s0, k: vz, v: z, s: _c, r: c1 } => {
                  match d_1 {
                    color::Red => {
                      let tmp = node(color::Black, l, k, v, Rc::clone(s));
                      let s0_clone = Rc::clone(s0);
                      let vz_clone = Clone::clone(vz);
                      let z_clone = Clone::clone(z);
                      let c1_clone = Rc::clone(c1);
                      let tmp_1 = node(color::Black, s0_clone, vz_clone, z_clone, c1_clone);
                      let vy_clone = Clone::clone(vy);
                      let y_clone = Clone::clone(y);
                      std::mem::drop(r);
                      node(color::Red, tmp, vy_clone, y_clone, tmp_1)
                    },
                    color::Black => {
                      node(color::Black, l, k, v, r)
                    },
                  }
                },
              }
            },
            tree::Node { c, l: s0, k: vy_1, v: y_1, s: _b_2, r: c1 } => {
              match c {
                color::Red => {
                  let tmp_2 = node(color::Black, l, k, v, Rc::clone(s0));
                  let tmp_3 = node(color::Black, Rc::clone(c1), Clone::clone(vy), Clone::clone(y), Rc::clone(c0));
                  let vy_clone_1 = Clone::clone(vy_1);
                  let y_clone_1 = Clone::clone(y_1);
                  std::mem::drop(r);
                  node(color::Red, tmp_2, vy_clone_1, y_clone_1, tmp_3)
                },
                color::Black => {
                  match &**c0 {
                    tree::Leaf => {
                      node(color::Black, l, k, v, r)
                    },
                    tree::Node { c: d_1, l: s1, k: vz, v: z, s: _c_1, r: c2 } => {
                      match d_1 {
                        color::Red => {
                          let tmp_4 = node(color::Black, l, k, v, Rc::clone(s));
                          let s1_clone = Rc::clone(s1);
                          let vz_clone_1 = Clone::clone(vz);
                          let z_clone_1 = Clone::clone(z);
                          let c2_clone = Rc::clone(c2);
                          let tmp_5 = node(color::Black, s1_clone, vz_clone_1, z_clone_1, c2_clone);
                          let vy_clone_2 = Clone::clone(vy);
                          let y_clone_2 = Clone::clone(y);
                          std::mem::drop(r);
                          node(color::Red, tmp_4, vy_clone_2, y_clone_2, tmp_5)
                        },
                        color::Black => {
                          node(color::Black, l, k, v, r)
                        },
                      }
                    },
                  }
                },
              }
            },
          }
        },
        color::Black => {
          node(color::Black, l, k, v, r)
        },
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.ins
// Variant: uncurried
pub fn ins_1(x: Int63, vx: Int63, t: Rc<tree>) -> Rc<tree> {
  ins(x, vx, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.ins (local: ins)
// Variant: uncurried, lifted
pub fn ins(x: Int63, vx: Int63, t: Rc<tree>) -> Rc<tree> {
  match &*t {
    tree::Leaf => {
      std::mem::drop(t);
      node(color::Red, Rc::new(tree::Leaf), x, vx, Rc::new(tree::Leaf))
    },
    tree::Node { c: r, l: s, k: vy, v: y, s: _l, r: c } => {
      let vy_clone = Clone::clone(vy);
      if key_lt(x, vy_clone) {
        match r {
          color::Red => {
            let tmp = ins(x, vx, Rc::clone(s));
            let vy_clone_1 = Clone::clone(vy);
            let y_clone = Clone::clone(y);
            let c_clone = Rc::clone(c);
            std::mem::drop(t);
            node(color::Red, tmp, vy_clone_1, y_clone, c_clone)
          },
          color::Black => {
            let tmp_1 = ins(x, vx, Rc::clone(s));
            let vy_clone_2 = Clone::clone(vy);
            let y_clone_1 = Clone::clone(y);
            let c_clone_1 = Rc::clone(c);
            std::mem::drop(t);
            lbal(tmp_1, vy_clone_2, y_clone_1, c_clone_1)
          },
        }
      } else {
        let vy_clone_3 = Clone::clone(vy);
        if x == vy_clone_3 {
          t
        } else {
          match r {
            color::Red => {
              let tmp_2 = ins(x, vx, Rc::clone(c));
              let s_clone = Rc::clone(s);
              let vy_clone_4 = Clone::clone(vy);
              let y_clone_2 = Clone::clone(y);
              std::mem::drop(t);
              node(color::Red, s_clone, vy_clone_4, y_clone_2, tmp_2)
            },
            color::Black => {
              let tmp_3 = ins(x, vx, Rc::clone(c));
              let s_clone_1 = Rc::clone(s);
              let vy_clone_5 = Clone::clone(vy);
              let y_clone_3 = Clone::clone(y);
              std::mem::drop(t);
              rbal(s_clone_1, vy_clone_5, y_clone_3, tmp_3)
            },
          }
        }
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.insert_t
// Variant: uncurried
pub fn insert_t(x: Int63, vx: Int63, t: Rc<tree>) -> Rc<tree> {
  makeBlack(ins_1(x, vx, t))
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.rbal'
// Variant: uncurried
pub fn rbal_(l: Rc<tree>, k: Int63, v: Int63, r: Rc<tree>) -> Rc<tree> {
  match &*r {
    tree::Leaf => {
      node(color::Black, l, k, v, r)
    },
    tree::Node { c: d, l: s, k: vz, v: z, s: _b_1, r: c0 } => {
      match d {
        color::Red => {
          match &**s {
            tree::Leaf => {
              match &**c0 {
                tree::Leaf => {
                  node(color::Black, l, k, v, r)
                },
                tree::Node { c: d_1, l: s0, k: vz_1, v: z_1, s: _c, r: c1 } => {
                  match d_1 {
                    color::Red => {
                      let tmp = node(color::Black, l, k, v, Rc::clone(s));
                      let s0_clone = Rc::clone(s0);
                      let vz_clone = Clone::clone(vz_1);
                      let z_clone = Clone::clone(z_1);
                      let c1_clone = Rc::clone(c1);
                      let tmp_1 = node(color::Black, s0_clone, vz_clone, z_clone, c1_clone);
                      let vz_clone_1 = Clone::clone(vz);
                      let z_clone_1 = Clone::clone(z);
                      std::mem::drop(r);
                      node(color::Red, tmp, vz_clone_1, z_clone_1, tmp_1)
                    },
                    color::Black => {
                      node(color::Black, l, k, v, r)
                    },
                  }
                },
              }
            },
            tree::Node { c, l: s0, k: vy, v: y, s: _b_2, r: c1 } => {
              match c {
                color::Red => {
                  match &**c0 {
                    tree::Leaf => {
                      let tmp_2 = node(color::Black, l, k, v, Rc::clone(s0));
                      let tmp_3 = node(color::Black, Rc::clone(c1), Clone::clone(vz), Clone::clone(z), Rc::clone(c0));
                      let vy_clone = Clone::clone(vy);
                      let y_clone = Clone::clone(y);
                      std::mem::drop(r);
                      node(color::Red, tmp_2, vy_clone, y_clone, tmp_3)
                    },
                    tree::Node { c: d_1, l: s1, k: vz_1, v: z_1, s: _c_1, r: c2 } => {
                      match d_1 {
                        color::Red => {
                          let tmp_4 = node(color::Black, l, k, v, Rc::clone(s));
                          let s1_clone = Rc::clone(s1);
                          let vz_clone_2 = Clone::clone(vz_1);
                          let z_clone_2 = Clone::clone(z_1);
                          let c2_clone = Rc::clone(c2);
                          let tmp_5 = node(color::Black, s1_clone, vz_clone_2, z_clone_2, c2_clone);
                          let vz_clone_3 = Clone::clone(vz);
                          let z_clone_3 = Clone::clone(z);
                          std::mem::drop(r);
                          node(color::Red, tmp_4, vz_clone_3, z_clone_3, tmp_5)
                        },
                        color::Black => {
                          let tmp_6 = node(color::Black, l, k, v, Rc::clone(s0));
                          let tmp_7 = node(color::Black, Rc::clone(c1), Clone::clone(vz), Clone::clone(z), Rc::clone(c0));
                          let vy_clone_1 = Clone::clone(vy);
                          let y_clone_1 = Clone::clone(y);
                          std::mem::drop(r);
                          node(color::Red, tmp_6, vy_clone_1, y_clone_1, tmp_7)
                        },
                      }
                    },
                  }
                },
                color::Black => {
                  match &**c0 {
                    tree::Leaf => {
                      node(color::Black, l, k, v, r)
                    },
                    tree::Node { c: d_1, l: s1, k: vz_1, v: z_1, s: _c_1_1, r: c2 } => {
                      match d_1 {
                        color::Red => {
                          let tmp_8 = node(color::Black, l, k, v, Rc::clone(s));
                          let s1_clone_1 = Rc::clone(s1);
                          let vz_clone_4 = Clone::clone(vz_1);
                          let z_clone_4 = Clone::clone(z_1);
                          let c2_clone_1 = Rc::clone(c2);
                          let tmp_9 = node(color::Black, s1_clone_1, vz_clone_4, z_clone_4, c2_clone_1);
                          let vz_clone_5 = Clone::clone(vz);
                          let z_clone_5 = Clone::clone(z);
                          std::mem::drop(r);
                          node(color::Red, tmp_8, vz_clone_5, z_clone_5, tmp_9)
                        },
                        color::Black => {
                          node(color::Black, l, k, v, r)
                        },
                      }
                    },
                  }
                },
              }
            },
          }
        },
        color::Black => {
          node(color::Black, l, k, v, r)
        },
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.makeRed
pub fn makeRed(t: Rc<tree>) -> Rc<tree> {
  let (v1, v2) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  match v1 {
    tree::Leaf => {
      __rocq_reuse::rebuild(v2, tree::Leaf)
    },
    tree::Node { c: _v17, l: v19, k: v21, v: v23, s: v25, r: v27 } => {
      __rocq_reuse::rebuild(v2, tree::Node { c: color::Red, l: v19, k: v21, v: v23, s: v25, r: v27 })
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.lbalS
// Variant: uncurried
pub fn lbalS(l: Rc<tree>, k: Int63, v: Int63, r: Rc<tree>) -> Rc<tree> {
  match &*l {
    tree::Leaf => {
      match &*r {
        tree::Leaf => {
          node(color::Red, l, k, v, r)
        },
        tree::Node { c, l: s, k: vz, v: z, s: _a_1, r: c0 } => {
          match c {
            color::Red => {
              match &**s {
                tree::Leaf => {
                  node(color::Red, l, k, v, r)
                },
                tree::Node { c: b_1, l: s0, k: vy, v: y, s: _a_2, r: c1 } => {
                  match b_1 {
                    color::Red => {
                      node(color::Red, l, k, v, r)
                    },
                    color::Black => {
                      let tmp = node(color::Black, l, k, v, Rc::clone(s0));
                      let tmp_1 = makeRed(Rc::clone(c0));
                      let tmp_2 = rbal_(Rc::clone(c1), Clone::clone(vz), Clone::clone(z), tmp_1);
                      let vy_clone = Clone::clone(vy);
                      let y_clone = Clone::clone(y);
                      std::mem::drop(r);
                      node(color::Red, tmp, vy_clone, y_clone, tmp_2)
                    },
                  }
                },
              }
            },
            color::Black => {
              let s_clone = Rc::clone(s);
              let vz_clone = Clone::clone(vz);
              let z_clone = Clone::clone(z);
              let c0_clone = Rc::clone(c0);
              std::mem::drop(r);
              rbal_(l, k, v, node(color::Red, s_clone, vz_clone, z_clone, c0_clone))
            },
          }
        },
      }
    },
    tree::Node { c: b_1, l: s, k: vx, v: x, s: _a_1_1, r: c } => {
      match b_1 {
        color::Red => {
          let s_clone_1 = Rc::clone(s);
          let vx_clone = Clone::clone(vx);
          let x_clone = Clone::clone(x);
          let c_clone = Rc::clone(c);
          std::mem::drop(l);
          let tmp_3 = node(color::Black, s_clone_1, vx_clone, x_clone, c_clone);
          node(color::Red, tmp_3, k, v, r)
        },
        color::Black => {
          match &*r {
            tree::Leaf => {
              node(color::Red, l, k, v, r)
            },
            tree::Node { c: c_1, l: s_1, k: vz, v: z, s: _a_2_1, r: c0 } => {
              match c_1 {
                color::Red => {
                  match &**s_1 {
                    tree::Leaf => {
                      node(color::Red, l, k, v, r)
                    },
                    tree::Node { c: b_2, l: s0, k: vy, v: y, s: _a_3, r: c1 } => {
                      match b_2 {
                        color::Red => {
                          node(color::Red, l, k, v, r)
                        },
                        color::Black => {
                          let tmp_4 = node(color::Black, l, k, v, Rc::clone(s0));
                          let tmp_5 = makeRed(Rc::clone(c0));
                          let tmp_6 = rbal_(Rc::clone(c1), Clone::clone(vz), Clone::clone(z), tmp_5);
                          let vy_clone_1 = Clone::clone(vy);
                          let y_clone_1 = Clone::clone(y);
                          std::mem::drop(r);
                          node(color::Red, tmp_4, vy_clone_1, y_clone_1, tmp_6)
                        },
                      }
                    },
                  }
                },
                color::Black => {
                  let s_clone_2 = Rc::clone(s_1);
                  let vz_clone_1 = Clone::clone(vz);
                  let z_clone_1 = Clone::clone(z);
                  let c0_clone_1 = Rc::clone(c0);
                  std::mem::drop(r);
                  rbal_(l, k, v, node(color::Red, s_clone_2, vz_clone_1, z_clone_1, c0_clone_1))
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.append
pub fn append_1(l: Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<tree>> {
  let tmp: Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = append(l);
  tmp
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.append (local: append_l)
// Variant: lifted
pub fn append_l(l: Rc<tree>, lr: color, append_2: Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<tree>>>, lc: Rc<tree>, s: Rc<tree>, lv: Int63, lx: Int63, r: Rc<tree>) -> Rc<tree> {
  match &*r {
    tree::Leaf => {
      std::mem::drop(append_2);
      std::mem::drop(lc);
      std::mem::drop(s);
      std::mem::drop(r);
      l
    },
    tree::Node { c: rr, l: s_1, k: rv, v: rx, s: _rl, r: rc } => {
      match &lr {
        color::Red => {
          match rr {
            color::Red => {
              let append_ref: &Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<tree>>> = &append_2;
              let tmp: Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = append_ref(lc);
              let tmp_1: &Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = &tmp;
              let lrl = tmp_1(Rc::clone(s_1));
              match &*lrl {
                tree::Leaf => {
                  std::mem::drop(tmp);
                  std::mem::drop(l);
                  std::mem::drop(append_2);
                  let rv_clone = Clone::clone(rv);
                  let rx_clone = Clone::clone(rx);
                  let rc_clone = Rc::clone(rc);
                  std::mem::drop(r);
                  let tmp_2 = node(color::Red, lrl, rv_clone, rx_clone, rc_clone);
                  node(color::Red, s, lv, lx, tmp_2)
                },
                tree::Node { c: rl_, l: s_2, k: vx, v: x, s: _lr_, r: c } => {
                  match rl_ {
                    color::Red => {
                      std::mem::drop(tmp);
                      std::mem::drop(l);
                      std::mem::drop(append_2);
                      let tmp_3 = node(color::Red, s, lv, lx, Rc::clone(s_2));
                      let c_clone = Rc::clone(c);
                      let rv_clone_1 = Clone::clone(rv);
                      let rx_clone_1 = Clone::clone(rx);
                      let rc_clone_1 = Rc::clone(rc);
                      std::mem::drop(r);
                      let tmp_4 = node(color::Red, c_clone, rv_clone_1, rx_clone_1, rc_clone_1);
                      let vx_clone = Clone::clone(vx);
                      let x_clone = Clone::clone(x);
                      std::mem::drop(lrl);
                      node(color::Red, tmp_3, vx_clone, x_clone, tmp_4)
                    },
                    color::Black => {
                      std::mem::drop(tmp);
                      std::mem::drop(l);
                      std::mem::drop(append_2);
                      let rv_clone_2 = Clone::clone(rv);
                      let rx_clone_2 = Clone::clone(rx);
                      let rc_clone_2 = Rc::clone(rc);
                      std::mem::drop(r);
                      let tmp_5 = node(color::Red, lrl, rv_clone_2, rx_clone_2, rc_clone_2);
                      node(color::Red, s, lv, lx, tmp_5)
                    },
                  }
                },
              }
            },
            color::Black => {
              std::mem::drop(l);
              let append_ref_1: &Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<tree>>> = &append_2;
              let tmp_6: Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = append_ref_1(lc);
              std::mem::drop(append_2);
              let tmp_7: &Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = &tmp_6;
              let tmp_8 = tmp_7(r);
              std::mem::drop(tmp_6);
              node(color::Red, s, lv, lx, tmp_8)
            },
          }
        },
        color::Black => {
          match rr {
            color::Red => {
              let tmp_9 = append_l(l, lr, append_2, lc, s, lv, lx, Rc::clone(s_1));
              let rv_clone_3 = Clone::clone(rv);
              let rx_clone_3 = Clone::clone(rx);
              let rc_clone_3 = Rc::clone(rc);
              std::mem::drop(r);
              node(color::Red, tmp_9, rv_clone_3, rx_clone_3, rc_clone_3)
            },
            color::Black => {
              let append_ref_2: &Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<tree>>> = &append_2;
              let tmp_10: Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = append_ref_2(lc);
              let tmp_11: &Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = &tmp_10;
              let lrl = tmp_11(Rc::clone(s_1));
              match &*lrl {
                tree::Leaf => {
                  std::mem::drop(tmp_10);
                  std::mem::drop(l);
                  std::mem::drop(append_2);
                  let rv_clone_4 = Clone::clone(rv);
                  let rx_clone_4 = Clone::clone(rx);
                  let rc_clone_4 = Rc::clone(rc);
                  std::mem::drop(r);
                  lbalS(s, lv, lx, node(color::Black, lrl, rv_clone_4, rx_clone_4, rc_clone_4))
                },
                tree::Node { c: rl_, l: s_2, k: vx, v: x, s: _lr__1, r: c } => {
                  match rl_ {
                    color::Red => {
                      std::mem::drop(tmp_10);
                      std::mem::drop(l);
                      std::mem::drop(append_2);
                      let tmp_12 = node(color::Black, s, lv, lx, Rc::clone(s_2));
                      let c_clone_1 = Rc::clone(c);
                      let rv_clone_5 = Clone::clone(rv);
                      let rx_clone_5 = Clone::clone(rx);
                      let rc_clone_5 = Rc::clone(rc);
                      std::mem::drop(r);
                      let tmp_13 = node(color::Black, c_clone_1, rv_clone_5, rx_clone_5, rc_clone_5);
                      let vx_clone_1 = Clone::clone(vx);
                      let x_clone_1 = Clone::clone(x);
                      std::mem::drop(lrl);
                      node(color::Red, tmp_12, vx_clone_1, x_clone_1, tmp_13)
                    },
                    color::Black => {
                      std::mem::drop(tmp_10);
                      std::mem::drop(l);
                      std::mem::drop(append_2);
                      let rv_clone_6 = Clone::clone(rv);
                      let rx_clone_6 = Clone::clone(rx);
                      let rc_clone_6 = Rc::clone(rc);
                      std::mem::drop(r);
                      lbalS(s, lv, lx, node(color::Black, lrl, rv_clone_6, rx_clone_6, rc_clone_6))
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
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.append (local: append)
// Variant: lifted
pub fn append(l: Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<tree>> {
  let append_2: Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<tree>>> = Rc::new(move |l: Rc<tree>| -> Rc<dyn Fn(Rc<tree>) -> Rc<tree>> {
    let tmp: Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = append(l);
    tmp
  });
  let tmp_1: Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = match &*l {
    tree::Leaf => {
      std::mem::drop(append_2);
      std::mem::drop(l);
      let callback: Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = Rc::new(move |r: Rc<tree>| -> Rc<tree> {
        r
      });
      callback
    },
    tree::Node { c: lr, l: s, k: lv, v: lx, s: _ll, r: lc } => {
      let l_clone = Rc::clone(&l);
      let lr_clone = Clone::clone(lr);
      let lc_clone = Rc::clone(lc);
      let s_clone = Rc::clone(s);
      let lv_clone = Clone::clone(lv);
      let lx_clone = Clone::clone(lx);
      std::mem::drop(l);
      let callback_1: Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = Rc::new({
        let __anf_capture_53 = append_2;
        move |r: Rc<tree>| -> Rc<tree> {
          let tmp_2 = Rc::clone(&l_clone);
          let tmp_3 = Clone::clone(&lr_clone);
          let tmp_4: Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<tree>>> = Rc::clone(&__anf_capture_53);
          let tmp_5 = Rc::clone(&lc_clone);
          let tmp_6 = Rc::clone(&s_clone);
          let tmp_7 = Clone::clone(&lv_clone);
          let tmp_8 = Clone::clone(&lx_clone);
          append_l(tmp_2, tmp_3, tmp_4, tmp_5, tmp_6, tmp_7, tmp_8, r)
        }
      });
      callback_1
    },
  };
  tmp_1
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.rbalS
// Variant: uncurried
pub fn rbalS(l: Rc<tree>, k: Int63, v: Int63, r: Rc<tree>) -> Rc<tree> {
  match &*r {
    tree::Leaf => {
      match &*l {
        tree::Leaf => {
          node(color::Red, l, k, v, r)
        },
        tree::Node { c: b_1, l: s, k: vx, v: x, s: _a_1, r: c0 } => {
          match b_1 {
            color::Red => {
              match &**c0 {
                tree::Leaf => {
                  node(color::Red, l, k, v, r)
                },
                tree::Node { c, l: s0, k: vy, v: y, s: _b_2, r: c1 } => {
                  match c {
                    color::Red => {
                      node(color::Red, l, k, v, r)
                    },
                    color::Black => {
                      let tmp = lbal(makeRed(Rc::clone(s)), Clone::clone(vx), Clone::clone(x), Rc::clone(s0));
                      let tmp_1 = node(color::Black, Rc::clone(c1), k, v, r);
                      let vy_clone = Clone::clone(vy);
                      let y_clone = Clone::clone(y);
                      std::mem::drop(l);
                      node(color::Red, tmp, vy_clone, y_clone, tmp_1)
                    },
                  }
                },
              }
            },
            color::Black => {
              let s_clone = Rc::clone(s);
              let vx_clone = Clone::clone(vx);
              let x_clone = Clone::clone(x);
              let c0_clone = Rc::clone(c0);
              std::mem::drop(l);
              lbal(node(color::Red, s_clone, vx_clone, x_clone, c0_clone), k, v, r)
            },
          }
        },
      }
    },
    tree::Node { c, l: s, k: vy, v: y, s: _b_1, r: c0 } => {
      match c {
        color::Red => {
          let s_clone_1 = Rc::clone(s);
          let vy_clone_1 = Clone::clone(vy);
          let y_clone_1 = Clone::clone(y);
          let c0_clone_1 = Rc::clone(c0);
          std::mem::drop(r);
          let tmp_2 = node(color::Black, s_clone_1, vy_clone_1, y_clone_1, c0_clone_1);
          node(color::Red, l, k, v, tmp_2)
        },
        color::Black => {
          match &*l {
            tree::Leaf => {
              node(color::Red, l, k, v, r)
            },
            tree::Node { c: b_2, l: s_1, k: vx, v: x, s: _a_1_1, r: c0_1 } => {
              match b_2 {
                color::Red => {
                  match &**c0_1 {
                    tree::Leaf => {
                      node(color::Red, l, k, v, r)
                    },
                    tree::Node { c: c_1, l: s0, k: vy_1, v: y_1, s: _b_3, r: c1 } => {
                      match c_1 {
                        color::Red => {
                          node(color::Red, l, k, v, r)
                        },
                        color::Black => {
                          let tmp_3 = lbal(makeRed(Rc::clone(s_1)), Clone::clone(vx), Clone::clone(x), Rc::clone(s0));
                          let tmp_4 = node(color::Black, Rc::clone(c1), k, v, r);
                          let vy_clone_2 = Clone::clone(vy_1);
                          let y_clone_2 = Clone::clone(y_1);
                          std::mem::drop(l);
                          node(color::Red, tmp_3, vy_clone_2, y_clone_2, tmp_4)
                        },
                      }
                    },
                  }
                },
                color::Black => {
                  let s_clone_2 = Rc::clone(s_1);
                  let vx_clone_1 = Clone::clone(vx);
                  let x_clone_1 = Clone::clone(x);
                  let c0_clone_2 = Rc::clone(c0_1);
                  std::mem::drop(l);
                  lbal(node(color::Red, s_clone_2, vx_clone_1, x_clone_1, c0_clone_2), k, v, r)
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.del
// Variant: uncurried
pub fn del_1(x: Int63, t: Rc<tree>) -> Rc<tree> {
  del(x, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.del (local: del)
// Variant: uncurried, lifted
pub fn del(x: Int63, t: Rc<tree>) -> Rc<tree> {
  let (v2, v3) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  match v2 {
    tree::Leaf => {
      __rocq_reuse::rebuild(v3, tree::Leaf)
    },
    tree::Node { c: _v18, l: v20, k: v22, v: v24, s: _v26, r: v28 } => {
      std::mem::drop(v3);
      let s = &v20;
      let c = &v28;
      if key_lt(x, v22) {
        match &**s {
          tree::Leaf => {
            node(color::Red, del(x, v20), v22, v24, v28)
          },
          tree::Node { c: r, l: _s_1, k: _v, v: _k, s: _l, r: _c_1 } => {
            match r {
              color::Red => {
                node(color::Red, del(x, v20), v22, v24, v28)
              },
              color::Black => {
                lbalS(del(x, v20), v22, v24, v28)
              },
            }
          },
        }
      } else {
        if x == v22 {
          let tmp: Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = append_1(v20);
          let tmp_1: &Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = &tmp;
          let tmp_2 = tmp_1(v28);
          std::mem::drop(tmp);
          tmp_2
        } else {
          match &**c {
            tree::Leaf => {
              node(color::Red, v20, v22, v24, del(x, v28))
            },
            tree::Node { c: r, l: _s_1_1, k: _v_1, v: _k_1, s: _l_1, r: _c_1_1 } => {
              match r {
                color::Red => {
                  node(color::Red, v20, v22, v24, del(x, v28))
                },
                color::Black => {
                  rbalS(v20, v22, v24, del(x, v28))
                },
              }
            },
          }
        }
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.delete_t
// Variant: uncurried
pub fn delete_t(x: Int63, t: Rc<tree>) -> Rc<tree> {
  makeBlack(del_1(x, t))
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.front_t
pub fn front_t_1(t: Rc<tree>) -> Rc<option<Int63>> {
  front_t(t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.front_t (local: front_t)
// Variant: lifted
pub fn front_t(t: Rc<tree>) -> Rc<option<Int63>> {
  let (v1, v2) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v2);
  match v1 {
    tree::Leaf => {
      Rc::new(option::<Int63>::None)
    },
    tree::Node { c: _v17, l: v19, k: v21, v: _v23, s: _v25, r: v27 } => {
      let tmp = front_t(v19);
      let (v33, v34) = __rocq_reuse::reset(tmp, |__payload| Clone::clone(__payload));
      match v33 {
        option::Some(v39) => {
          std::mem::drop(v27);
          __rocq_reuse::rebuild(v34, option::<Int63>::Some(v39))
        },
        option::None => {
          std::mem::drop(v27);
          __rocq_reuse::rebuild(v34, option::<Int63>::Some(v21))
        },
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.back_t
pub fn back_t_1(t: Rc<tree>) -> Rc<option<Int63>> {
  back_t(t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.back_t (local: back_t)
// Variant: lifted
pub fn back_t(t: Rc<tree>) -> Rc<option<Int63>> {
  let (v1, v2) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v2);
  match v1 {
    tree::Leaf => {
      Rc::new(option::<Int63>::None)
    },
    tree::Node { c: _v17, l: v19, k: v21, v: _v23, s: _v25, r: v27 } => {
      let tmp = back_t(v27);
      let (v33, v34) = __rocq_reuse::reset(tmp, |__payload| Clone::clone(__payload));
      match v33 {
        option::Some(v39) => {
          std::mem::drop(v19);
          __rocq_reuse::rebuild(v34, option::<Int63>::Some(v39))
        },
        option::None => {
          std::mem::drop(v19);
          __rocq_reuse::rebuild(v34, option::<Int63>::Some(v21))
        },
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.on_cur
// Variant: uncurried
pub fn on_cur(cur: Rc<option<Int63>>, f: Rc<dyn Fn(Int63) -> Rc<option<Int63>>>) -> Rc<option<Int63>> {
  let (v2, v3) = __rocq_reuse::reset(cur, |__payload| Clone::clone(__payload));
  match v2 {
    option::Some(v8) => {
      std::mem::drop(v3);
      let f_ref: &Rc<dyn Fn(Int63) -> Rc<option<Int63>>> = &f;
      let tmp = f_ref(v8);
      std::mem::drop(f);
      tmp
    },
    option::None => {
      std::mem::drop(f);
      __rocq_reuse::rebuild(v3, option::<Int63>::None)
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.pred_t (local: pred_t)
// Variant: uncurried, lifted
pub fn pred_t_owned(x: Int63, t: Rc<tree>) -> Rc<option<Int63>> {
  let (v2, v3) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v3);
  match v2 {
    tree::Leaf => {
      Rc::new(option::<Int63>::None)
    },
    tree::Node { c: _v18, l: v20, k: v22, v: _v24, s: _v26, r: v28 } => {
      if key_lt(v22, x) {
        let tmp = pred_t_owned(x, v28);
        let (v43, v44) = __rocq_reuse::reset(tmp, |__payload| Clone::clone(__payload));
        match v43 {
          option::Some(v49) => {
            std::mem::drop(v20);
            __rocq_reuse::rebuild(v44, option::<Int63>::Some(v49))
          },
          option::None => {
            std::mem::drop(v20);
            __rocq_reuse::rebuild(v44, option::<Int63>::Some(v22))
          },
        }
      } else {
        std::mem::drop(v28);
        pred_t_owned(x, v20)
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.pred_t
// Variant: borrowed, uncurried
pub fn pred_t_1(x: Int63, t: &Rc<tree>) -> Rc<option<Int63>> {
  let x_1 = x;
  pred_t(x_1, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.pred_t (local: pred_t)
// Variant: borrowed, uncurried, lifted
pub fn pred_t(x: Int63, t: &Rc<tree>) -> Rc<option<Int63>> {
  let x_1 = x;
  let tmp = t;
  match &**tmp {
    tree::Leaf => {
      Rc::new(option::<Int63>::None)
    },
    tree::Node { c: _r, l: s, k: v, v: _k, s: _l, r: c } => {
      let v_clone = Clone::clone(v);
      if key_lt(v_clone, x_1) {
        let tmp_1 = pred_t(x_1, c);
        let (v34, v35) = __rocq_reuse::reset(tmp_1, |__payload| Clone::clone(__payload));
        match v34 {
          option::Some(v40) => {
            __rocq_reuse::rebuild(v35, option::<Int63>::Some(v40))
          },
          option::None => {
            let v_clone_1 = Clone::clone(v);
            __rocq_reuse::rebuild(v35, option::<Int63>::Some(v_clone_1))
          },
        }
      } else {
        let s_clone = Rc::clone(s);
        pred_t_owned(x_1, s_clone)
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.kth_t
// Variant: uncurried
pub fn kth_t_1(n: Int63, t: Rc<tree>) -> Rc<option<Int63>> {
  kth_t(n, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.kth_t (local: kth_t)
// Variant: uncurried, lifted
pub fn kth_t(n: Int63, t: Rc<tree>) -> Rc<option<Int63>> {
  let (v2, v3) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v3);
  match v2 {
    tree::Leaf => {
      Rc::new(option::<Int63>::None)
    },
    tree::Node { c: _v18, l: v20, k: v22, v: _v24, s: _v26, r: v28 } => {
      let s = &v20;
      let sl = size(s);
      if n < sl {
        std::mem::drop(v28);
        kth_t(n, v20)
      } else {
        if n == sl {
          std::mem::drop(v28);
          std::mem::drop(v20);
          Rc::new(option::<Int63>::Some(v22))
        } else {
          std::mem::drop(v20);
          kth_t(n - sl - int63!(1), v28)
        }
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.rank_t
// Variant: borrowed, uncurried
pub fn rank_t_1(x: Int63, t: &Rc<tree>) -> Int63 {
  let x_1 = x;
  rank_t(x_1, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.rank_t (local: rank_t)
// Variant: borrowed, uncurried, lifted
pub fn rank_t(x: Int63, t: &Rc<tree>) -> Int63 {
  let x_1 = x;
  let tmp = t;
  match &**tmp {
    tree::Leaf => {
      int63!(0)
    },
    tree::Node { c: _r, l: s, k: v, v: _k, s: _l, r: c } => {
      let v_clone = Clone::clone(v);
      if key_lt(x_1, v_clone) {
        rank_t(x_1, s)
      } else {
        let v_clone_1 = Clone::clone(v);
        if x_1 == v_clone_1 {
          size(s)
        } else {
          let tmp_1 = size(s) + int63!(1);
          let tmp_2 = rank_t(x_1, c);
          tmp_1 + tmp_2
        }
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.lookup_t (local: lookup_t)
// Variant: uncurried, lifted
pub fn lookup_t_owned(x: Int63, t: Rc<tree>) -> Rc<option<Int63>> {
  let (v2, v3) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v3);
  match v2 {
    tree::Leaf => {
      Rc::new(option::<Int63>::None)
    },
    tree::Node { c: _v18, l: v20, k: v22, v: v24, s: _v26, r: v28 } => {
      if key_lt(x, v22) {
        std::mem::drop(v28);
        lookup_t_owned(x, v20)
      } else {
        if x == v22 {
          std::mem::drop(v20);
          std::mem::drop(v28);
          Rc::new(option::<Int63>::Some(v24))
        } else {
          std::mem::drop(v20);
          lookup_t_owned(x, v28)
        }
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.lookup_t
// Variant: borrowed, uncurried
pub fn lookup_t_1(x: Int63, t: &Rc<tree>) -> Rc<option<Int63>> {
  let x_1 = x;
  lookup_t(x_1, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.lookup_t (local: lookup_t)
// Variant: borrowed, uncurried, lifted
pub fn lookup_t(x: Int63, t: &Rc<tree>) -> Rc<option<Int63>> {
  let x_1 = x;
  let tmp = t;
  match &**tmp {
    tree::Leaf => {
      Rc::new(option::<Int63>::None)
    },
    tree::Node { c: _r, l: s, k: v, v: k, s: _l, r: c } => {
      let v_clone = Clone::clone(v);
      if key_lt(x_1, v_clone) {
        let s_clone = Rc::clone(s);
        lookup_t_owned(x_1, s_clone)
      } else {
        let v_clone_1 = Clone::clone(v);
        if x_1 == v_clone_1 {
          let k_clone = Clone::clone(k);
          Rc::new(option::<Int63>::Some(k_clone))
        } else {
          let c_clone = Rc::clone(c);
          lookup_t_owned(x_1, c_clone)
        }
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.setv_t
// Variant: uncurried
pub fn setv_t_1(x: Int63, w: Int63, t: Rc<tree>) -> Rc<tree> {
  setv_t(x, w, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.setv_t (local: setv_t)
// Variant: uncurried, lifted
pub fn setv_t(x: Int63, w: Int63, t: Rc<tree>) -> Rc<tree> {
  let (v3, v4) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  match v3 {
    tree::Leaf => {
      __rocq_reuse::rebuild(v4, tree::Leaf)
    },
    tree::Node { c: v19, l: v21, k: v23, v: v25, s: v27, r: v29 } => {
      if key_lt(x, v23) {
        __rocq_reuse::rebuild(v4, tree::Node { c: v19, l: setv_t(x, w, v21), k: v23, v: v25, s: v27, r: v29 })
      } else {
        if x == v23 {
          __rocq_reuse::rebuild(v4, tree::Node { c: v19, l: v21, k: v23, v: w, s: v27, r: v29 })
        } else {
          __rocq_reuse::rebuild(v4, tree::Node { c: v19, l: v21, k: v23, v: v25, s: v27, r: setv_t(x, w, v29) })
        }
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.exec
// Variant: uncurried
#[inline(never)]
pub fn exec(T: Array<Rc<tree>>, C: Array<Rc<option<Int63>>>, O: Array<Rc<option<Int63>>>, p: Int63, id: Int63, op: Int63, x: Int63, y: Int63) -> (((Array<Rc<tree>>, Array<Rc<option<Int63>>>), Array<Rc<option<Int63>>>), Int63) {
  let t = T.get_cloned(id);
  let cur = C.get_cloned(id);
  if op == int63!(97) {
    std::mem::drop(cur);
    std::mem::drop(t);
    let tmp = T.get_cloned(x);
    (((T.set(id, tmp), C.set(id, Rc::new(option::<Int63>::None))), O), p)
  } else {
    if op == int63!(63) {
      std::mem::drop(cur);
      (((T, C.set(id, find_t_1(x, t))), O), p)
    } else {
      if op == int63!(108) {
        std::mem::drop(cur);
        (((T, C.set(id, lower_t_1(x, t))), O), p)
      } else {
        if op == int63!(117) {
          std::mem::drop(cur);
          (((T, C.set(id, upper_t_owned_1(x, t))), O), p)
        } else {
          if op == int63!(105) {
            std::mem::drop(cur);
            (((T.set(id, insert_t(x, y, t)), C.set(id, Rc::new(option::<Int63>::Some(x)))), O), p)
          } else {
            if op == int63!(101) {
              let (v257, v258) = __rocq_reuse::reset(cur, |__payload| Clone::clone(__payload));
              let tmp_1 = match v257 {
                option::Some(v263) => {
                  delete_t(v263, t)
                },
                option::None => {
                  t
                },
              };
              (((T.set(id, tmp_1), C.set(id, __rocq_reuse::rebuild(v258, option::<Int63>::None))), O), p)
            } else {
              if op == int63!(102) {
                std::mem::drop(cur);
                (((T, C.set(id, front_t_1(t))), O), p)
              } else {
                if op == int63!(98) {
                  std::mem::drop(cur);
                  (((T, C.set(id, back_t_1(t))), O), p)
                } else {
                  if op == int63!(62) {
                    let callback: Rc<dyn Fn(Int63) -> Rc<option<Int63>>> = Rc::new({
                      let __anf_capture_406 = t;
                      move |c: Int63| -> Rc<option<Int63>> {
                        let t = &__anf_capture_406;
                        upper_t_1(c, t)
                      }
                    });
                    (((T, C.set(id, on_cur(cur, callback))), O), p)
                  } else {
                    if op == int63!(60) {
                      let callback_1: Rc<dyn Fn(Int63) -> Rc<option<Int63>>> = Rc::new({
                        let __anf_capture_463 = t;
                        move |c: Int63| -> Rc<option<Int63>> {
                          let t = &__anf_capture_463;
                          pred_t_1(c, t)
                        }
                      });
                      (((T, C.set(id, on_cur(cur, callback_1))), O), p)
                    } else {
                      if op == int63!(107) {
                        let tmp_2 = int63!(0);
                        let tmp_3 = if x.ltsb(tmp_2) {
                          std::mem::drop(cur);
                          std::mem::drop(t);
                          Rc::new(option::<Int63>::None)
                        } else {
                          std::mem::drop(cur);
                          kth_t_1(x, t)
                        };
                        (((T, C.set(id, tmp_3)), O), p)
                      } else {
                        if op == int63!(114) {
                          let tmp_4 = (T, C);
                          let callback_2: Rc<dyn Fn(Int63) -> Rc<option<Int63>>> = Rc::new({
                            let __anf_capture_585 = t;
                            move |c: Int63| -> Rc<option<Int63>> {
                              let t = &__anf_capture_585;
                              let tmp_5 = rank_t_1(c, t);
                              Rc::new(option::<Int63>::Some(tmp_5))
                            }
                          });
                          ((tmp_4, O.set(p, on_cur(cur, callback_2))), p + int63!(1))
                        } else {
                          if op == int63!(103) {
                            let tmp_6 = (T, C);
                            let callback_3: Rc<dyn Fn(Int63) -> Rc<option<Int63>>> = Rc::new({
                              let __anf_capture_655 = t;
                              move |c: Int63| -> Rc<option<Int63>> {
                                let t = &__anf_capture_655;
                                lookup_t_1(c, t)
                              }
                            });
                            ((tmp_6, O.set(p, on_cur(cur, callback_3))), p + int63!(1))
                          } else {
                            if op == int63!(115) {
                              let (v710, v711) = __rocq_reuse::reset(cur, |__payload| Clone::clone(__payload));
                              std::mem::drop(v711);
                              let tmp_7 = match v710 {
                                option::Some(v716) => {
                                  setv_t_1(v716, x, t)
                                },
                                option::None => {
                                  t
                                },
                              };
                              (((T.set(id, tmp_7), C), O), p)
                            } else {
                              if op == int63!(122) {
                                std::mem::drop(cur);
                                (((T, C), O.set(p, Rc::new(option::<Int63>::Some(size_owned(t))))), p + int63!(1))
                              } else {
                                std::mem::drop(cur);
                                std::mem::drop(t);
                                (((T, C), O), p)
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.run_loop
// Variant: uncurried
pub fn run_loop_1(commands: Array<(Int63, Rc<operation<Int63, Int63>>)>, q: Int63, j: Int63, T: Array<Rc<tree>>, C: Array<Rc<option<Int63>>>, O: Array<Rc<option<Int63>>>, p: Int63) -> Array<Rc<option<Int63>>> {
  run_loop(commands, q, j, T, C, O, p, ())
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.run_loop (local: run_loop)
// Variant: uncurried, lifted
pub fn run_loop(commands: Array<(Int63, Rc<operation<Int63, Int63>>)>, q: Int63, j: Int63, T: Array<Rc<tree>>, C: Array<Rc<option<Int63>>>, O: Array<Rc<option<Int63>>>, p: Int63, _H: ()) -> Array<Rc<option<Int63>>> {
  let tmp = j < q;
  match bdec(tmp) {
    sumbool::left => {
      let commands_ref = &commands;
      let tmp_1 = commands_ref.get_cloned(j);
      let tmp_2 = encode_machine(tmp_1);
      match tmp_2 {
        (v28, v30) => {
          match v28 {
            (v33, v35) => {
              match v33 {
                (v38, v40) => {
                  let tmp_3 = exec(T, C, O, p, v38, v40, v35, v30);
                  match tmp_3 {
                    (v61, v63) => {
                      match v61 {
                        (v66, v68) => {
                          match v66 {
                            (v71, v73) => {
                              run_loop(commands, q, j + int63!(1), v71, v73, v68, v63, ())
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
      }
    },
    sumbool::right => {
      std::mem::drop(commands);
      std::mem::drop(T);
      std::mem::drop(C);
      O
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.run_impl
pub fn run_impl(commands: Array<(Int63, Rc<operation<Int63, Int63>>)>) -> Array<Rc<option<Int63>>> {
  let q = commands.length();
  let commands_clone = Clone::clone(&commands);
  let n = count_loop_1(commands_clone, q, int63!(0), int63!(0));
  run_loop_1(commands, q, int63!(0), Array::<Rc<tree>>::make(int63!(1001), Rc::new(tree::Leaf)), Array::<Rc<option<Int63>>>::make(int63!(1001), Rc::new(option::<Int63>::None)), Array::<Rc<option<Int63>>>::make(n, Rc::new(option::<Int63>::None)), int63!(0))
}
