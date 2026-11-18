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

pub enum tree {
  Leaf,
  Node { c: color, l: Rc<tree>, k: u64, v: u64, s: u64, r: Rc<tree> },
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

pub type uint = u64;

pub type sint = u64;

pub type machine_command = (u64, Rc<operation<u64, u64>>);

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

// Rocq: Selfbalancingbst.selfbalancingbst_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.output_command
pub fn output_command(line: (u64, Rc<operation<u64, u64>>)) -> bool {
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
pub fn count_loop_1(ops: Rc<Array<(u64, Rc<operation<u64, u64>>)>>, q: u64, j: u64, acc: u64) -> u64 {
  count_loop(ops, q, j, acc, ())
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.count_loop (local: count_loop)
// Variant: uncurried, lifted
pub fn count_loop(ops: Rc<Array<(u64, Rc<operation<u64, u64>>)>>, q: u64, j: u64, acc: u64, _H: ()) -> u64 {
  let tmp = ltb(j, q);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(j, 1u64);
      let ops_ref = &ops;
      let tmp_2 = j;
      let tmp_3 = Clone::clone(&(ops_ref)[tmp_2]);
      let tmp_4 = if output_command(tmp_3) {
        add(acc, 1u64)
      } else {
        acc
      };
      count_loop(ops, q, tmp_1, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(ops);
      acc
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.encode_operation
// Variant: uncurried
pub fn encode_operation<U: Clone + 'static, S: Clone + 'static>(zero: S, source: Rc<dyn Fn(U) -> S>, op: Rc<operation<U, S>>) -> ((u64, S), S) {
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
      let tmp = 97u64;
      let source_ref: &Rc<dyn Fn(U) -> S> = &source;
      let tmp_1 = source_ref(v16);
      std::mem::drop(source);
      ((tmp, tmp_1), zero)
    },
    operation::FindKey { key: v38 } => {
      std::mem::drop(source);
      ((63u64, v38), zero)
    },
    operation::LowerBound { key: v56 } => {
      std::mem::drop(source);
      ((108u64, v56), zero)
    },
    operation::UpperBound { key: v74 } => {
      std::mem::drop(source);
      ((117u64, v74), zero)
    },
    operation::Insert { key: v92, value: v94 } => {
      std::mem::drop(zero);
      std::mem::drop(source);
      ((105u64, v92), v94)
    },
    operation::Erase => {
      std::mem::drop(source);
      let zero_clone = Clone::clone(&zero);
      ((101u64, zero_clone), zero)
    },
    operation::First => {
      std::mem::drop(source);
      let zero_clone_1 = Clone::clone(&zero);
      ((102u64, zero_clone_1), zero)
    },
    operation::Last => {
      std::mem::drop(source);
      let zero_clone_2 = Clone::clone(&zero);
      ((98u64, zero_clone_2), zero)
    },
    operation::NextKey => {
      std::mem::drop(source);
      let zero_clone_3 = Clone::clone(&zero);
      ((62u64, zero_clone_3), zero)
    },
    operation::PreviousKey => {
      std::mem::drop(source);
      let zero_clone_4 = Clone::clone(&zero);
      ((60u64, zero_clone_4), zero)
    },
    operation::SelectRank { index: v197 } => {
      std::mem::drop(source);
      ((107u64, v197), zero)
    },
    operation::GetRank => {
      std::mem::drop(source);
      let zero_clone_5 = Clone::clone(&zero);
      ((114u64, zero_clone_5), zero)
    },
    operation::GetValue => {
      std::mem::drop(source);
      let zero_clone_6 = Clone::clone(&zero);
      ((103u64, zero_clone_6), zero)
    },
    operation::SetValue { value: v249 } => {
      std::mem::drop(source);
      ((115u64, v249), zero)
    },
    operation::GetSize => {
      std::mem::drop(source);
      let zero_clone_7 = Clone::clone(&zero);
      ((122u64, zero_clone_7), zero)
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.encode_machine
#[inline(never)]
pub fn encode_machine(line: (u64, Rc<operation<u64, u64>>)) -> (((u64, u64), u64), u64) {
  match line {
    (v2, v4) => {
      let tmp = 0u64;
      let callback: Rc<dyn Fn(u64) -> u64> = Rc::new(move |id: u64| -> u64 {
        id
      });
      let tmp_1 = encode_operation::<u64, u64>(tmp, callback, v4);
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb
// Variant: uncurried
pub fn ltsb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltsb(v0, v1)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.key_lt
// Variant: uncurried
pub fn key_lt(a: u64, b: u64) -> bool {
  ltsb(a, b)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.find_t
// Variant: uncurried
pub fn find_t_1(x: u64, t: Rc<tree>) -> Rc<option<u64>> {
  find_t(x, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.find_t (local: find_t)
// Variant: uncurried, lifted
pub fn find_t(x: u64, t: Rc<tree>) -> Rc<option<u64>> {
  let (v2, v3) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v3);
  match v2 {
    tree::Leaf => {
      Rc::new(option::<u64>::None)
    },
    tree::Node { c: _v18, l: v20, k: v22, v: _v24, s: _v26, r: v28 } => {
      if key_lt(x, v22) {
        std::mem::drop(v28);
        find_t(x, v20)
      } else {
        if eqb(x, v22) {
          std::mem::drop(v20);
          std::mem::drop(v28);
          Rc::new(option::<u64>::Some(v22))
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
pub fn lower_t_1(x: u64, t: Rc<tree>) -> Rc<option<u64>> {
  lower_t(x, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.lower_t (local: lower_t)
// Variant: uncurried, lifted
pub fn lower_t(x: u64, t: Rc<tree>) -> Rc<option<u64>> {
  let (v2, v3) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v3);
  match v2 {
    tree::Leaf => {
      Rc::new(option::<u64>::None)
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
            __rocq_reuse::rebuild(v52, option::<u64>::Some(v57))
          },
          option::None => {
            std::mem::drop(v28);
            __rocq_reuse::rebuild(v52, option::<u64>::Some(v22))
          },
        }
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.upper_t
// Variant: uncurried
pub fn upper_t_owned_1(x: u64, t: Rc<tree>) -> Rc<option<u64>> {
  upper_t_owned(x, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.upper_t (local: upper_t)
// Variant: uncurried, lifted
pub fn upper_t_owned(x: u64, t: Rc<tree>) -> Rc<option<u64>> {
  let (v2, v3) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v3);
  match v2 {
    tree::Leaf => {
      Rc::new(option::<u64>::None)
    },
    tree::Node { c: _v18, l: v20, k: v22, v: _v24, s: _v26, r: v28 } => {
      if key_lt(x, v22) {
        let tmp = upper_t_owned(x, v20);
        let (v43, v44) = __rocq_reuse::reset(tmp, |__payload| Clone::clone(__payload));
        match v43 {
          option::Some(v49) => {
            std::mem::drop(v28);
            __rocq_reuse::rebuild(v44, option::<u64>::Some(v49))
          },
          option::None => {
            std::mem::drop(v28);
            __rocq_reuse::rebuild(v44, option::<u64>::Some(v22))
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
pub fn upper_t_1(x: u64, t: &Rc<tree>) -> Rc<option<u64>> {
  let x_1 = x;
  upper_t(x_1, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.upper_t (local: upper_t)
// Variant: borrowed, uncurried, lifted
pub fn upper_t(x: u64, t: &Rc<tree>) -> Rc<option<u64>> {
  let x_1 = x;
  let tmp = t;
  match &**tmp {
    tree::Leaf => {
      Rc::new(option::<u64>::None)
    },
    tree::Node { c: _r, l: s, k: v, v: _k, s: _l, r: c } => {
      let v_clone = Clone::clone(v);
      if key_lt(x_1, v_clone) {
        let tmp_1 = upper_t(x_1, s);
        let (v34, v35) = __rocq_reuse::reset(tmp_1, |__payload| Clone::clone(__payload));
        match v34 {
          option::Some(v40) => {
            __rocq_reuse::rebuild(v35, option::<u64>::Some(v40))
          },
          option::None => {
            let v_clone_1 = Clone::clone(v);
            __rocq_reuse::rebuild(v35, option::<u64>::Some(v_clone_1))
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
pub fn size_owned(t: Rc<tree>) -> u64 {
  let (v1, v2) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v2);
  match v1 {
    tree::Leaf => {
      0u64
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
pub fn size(t: &Rc<tree>) -> u64 {
  let tmp = t;
  match &**tmp {
    tree::Leaf => {
      0u64
    },
    tree::Node { c: _r, l: _s, k: _v, v: _k, s: l, r: _c } => {
      Clone::clone(l)
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.node
// Variant: uncurried
pub fn node(c: color, l: Rc<tree>, k: u64, v: u64, r: Rc<tree>) -> Rc<tree> {
  let tmp = size(&l);
  let tmp_1 = size(&r);
  let tmp_2 = add(tmp, tmp_1);
  Rc::new(tree::Node { c, l, k, v, s: add(tmp_2, 1u64), r })
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.lbal
// Variant: uncurried
pub fn lbal(l: Rc<tree>, k: u64, v: u64, r: Rc<tree>) -> Rc<tree> {
  match &*l {
    tree::Leaf => {
      node(color::Black, l, k, v, r)
    },
    tree::Node { c, l: s, k: vx, v: x, s: _a, r: c0 } => {
      match c {
        color::Red => {
          match &**s {
            tree::Leaf => {
              match &**c0 {
                tree::Leaf => {
                  node(color::Black, l, k, v, r)
                },
                tree::Node { c: c_1, l: s0, k: vy, v: y, s: _b, r: c1 } => {
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
            tree::Node { c: b, l: s0, k: vx_1, v: x_1, s: _a_1, r: c1 } => {
              match b {
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
                    tree::Node { c: c_1, l: s1, k: vy, v: y, s: _b_1, r: c2 } => {
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
pub fn rbal(l: Rc<tree>, k: u64, v: u64, r: Rc<tree>) -> Rc<tree> {
  match &*r {
    tree::Leaf => {
      node(color::Black, l, k, v, r)
    },
    tree::Node { c: d, l: s, k: vy, v: y, s: _b, r: c0 } => {
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
            tree::Node { c, l: s0, k: vy_1, v: y_1, s: _b_1, r: c1 } => {
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
pub fn ins_1(x: u64, vx: u64, t: Rc<tree>) -> Rc<tree> {
  ins(x, vx, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.ins (local: ins)
// Variant: uncurried, lifted
pub fn ins(x: u64, vx: u64, t: Rc<tree>) -> Rc<tree> {
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
        if eqb(x, vy_clone_3) {
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
pub fn insert_t(x: u64, vx: u64, t: Rc<tree>) -> Rc<tree> {
  makeBlack(ins_1(x, vx, t))
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.rbal'
// Variant: uncurried
pub fn rbal_(l: Rc<tree>, k: u64, v: u64, r: Rc<tree>) -> Rc<tree> {
  match &*r {
    tree::Leaf => {
      node(color::Black, l, k, v, r)
    },
    tree::Node { c: d, l: s, k: vz, v: z, s: _b, r: c0 } => {
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
            tree::Node { c, l: s0, k: vy, v: y, s: _b_1, r: c1 } => {
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
pub fn lbalS(l: Rc<tree>, k: u64, v: u64, r: Rc<tree>) -> Rc<tree> {
  match &*l {
    tree::Leaf => {
      match &*r {
        tree::Leaf => {
          node(color::Red, l, k, v, r)
        },
        tree::Node { c, l: s, k: vz, v: z, s: _a, r: c0 } => {
          match c {
            color::Red => {
              match &**s {
                tree::Leaf => {
                  node(color::Red, l, k, v, r)
                },
                tree::Node { c: b, l: s0, k: vy, v: y, s: _a_1, r: c1 } => {
                  match b {
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
    tree::Node { c: b, l: s, k: vx, v: x, s: _a_2, r: c } => {
      match b {
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
            tree::Node { c: c_1, l: s_1, k: vz, v: z, s: _a_1_1, r: c0 } => {
              match c_1 {
                color::Red => {
                  match &**s_1 {
                    tree::Leaf => {
                      node(color::Red, l, k, v, r)
                    },
                    tree::Node { c: b_1, l: s0, k: vy, v: y, s: _a_2_1, r: c1 } => {
                      match b_1 {
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
pub fn append_l(l: Rc<tree>, lr: color, append_2: Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<tree>>>, lc: Rc<tree>, s: Rc<tree>, lv: u64, lx: u64, r: Rc<tree>) -> Rc<tree> {
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
pub fn rbalS(l: Rc<tree>, k: u64, v: u64, r: Rc<tree>) -> Rc<tree> {
  match &*r {
    tree::Leaf => {
      match &*l {
        tree::Leaf => {
          node(color::Red, l, k, v, r)
        },
        tree::Node { c: b, l: s, k: vx, v: x, s: _a, r: c0 } => {
          match b {
            color::Red => {
              match &**c0 {
                tree::Leaf => {
                  node(color::Red, l, k, v, r)
                },
                tree::Node { c, l: s0, k: vy, v: y, s: _b_1, r: c1 } => {
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
    tree::Node { c, l: s, k: vy, v: y, s: _b, r: c0 } => {
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
            tree::Node { c: b_1, l: s_1, k: vx, v: x, s: _a_1, r: c0_1 } => {
              match b_1 {
                color::Red => {
                  match &**c0_1 {
                    tree::Leaf => {
                      node(color::Red, l, k, v, r)
                    },
                    tree::Node { c: c_1, l: s0, k: vy_1, v: y_1, s: _b_2, r: c1 } => {
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
pub fn del_1(x: u64, t: Rc<tree>) -> Rc<tree> {
  del(x, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.del (local: del)
// Variant: uncurried, lifted
pub fn del(x: u64, t: Rc<tree>) -> Rc<tree> {
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
        if eqb(x, v22) {
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
pub fn delete_t(x: u64, t: Rc<tree>) -> Rc<tree> {
  makeBlack(del_1(x, t))
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.front_t
pub fn front_t_1(t: Rc<tree>) -> Rc<option<u64>> {
  front_t(t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.front_t (local: front_t)
// Variant: lifted
pub fn front_t(t: Rc<tree>) -> Rc<option<u64>> {
  let (v1, v2) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v2);
  match v1 {
    tree::Leaf => {
      Rc::new(option::<u64>::None)
    },
    tree::Node { c: _v17, l: v19, k: v21, v: _v23, s: _v25, r: v27 } => {
      let tmp = front_t(v19);
      let (v33, v34) = __rocq_reuse::reset(tmp, |__payload| Clone::clone(__payload));
      match v33 {
        option::Some(v39) => {
          std::mem::drop(v27);
          __rocq_reuse::rebuild(v34, option::<u64>::Some(v39))
        },
        option::None => {
          std::mem::drop(v27);
          __rocq_reuse::rebuild(v34, option::<u64>::Some(v21))
        },
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.back_t
pub fn back_t_1(t: Rc<tree>) -> Rc<option<u64>> {
  back_t(t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.back_t (local: back_t)
// Variant: lifted
pub fn back_t(t: Rc<tree>) -> Rc<option<u64>> {
  let (v1, v2) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v2);
  match v1 {
    tree::Leaf => {
      Rc::new(option::<u64>::None)
    },
    tree::Node { c: _v17, l: v19, k: v21, v: _v23, s: _v25, r: v27 } => {
      let tmp = back_t(v27);
      let (v33, v34) = __rocq_reuse::reset(tmp, |__payload| Clone::clone(__payload));
      match v33 {
        option::Some(v39) => {
          std::mem::drop(v19);
          __rocq_reuse::rebuild(v34, option::<u64>::Some(v39))
        },
        option::None => {
          std::mem::drop(v19);
          __rocq_reuse::rebuild(v34, option::<u64>::Some(v21))
        },
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.on_cur
// Variant: uncurried
pub fn on_cur(cur: Rc<option<u64>>, f: Rc<dyn Fn(u64) -> Rc<option<u64>>>) -> Rc<option<u64>> {
  let (v2, v3) = __rocq_reuse::reset(cur, |__payload| Clone::clone(__payload));
  match v2 {
    option::Some(v8) => {
      std::mem::drop(v3);
      let f_ref: &Rc<dyn Fn(u64) -> Rc<option<u64>>> = &f;
      let tmp = f_ref(v8);
      std::mem::drop(f);
      tmp
    },
    option::None => {
      std::mem::drop(f);
      __rocq_reuse::rebuild(v3, option::<u64>::None)
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.pred_t (local: pred_t)
// Variant: uncurried, lifted
pub fn pred_t_owned(x: u64, t: Rc<tree>) -> Rc<option<u64>> {
  let (v2, v3) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v3);
  match v2 {
    tree::Leaf => {
      Rc::new(option::<u64>::None)
    },
    tree::Node { c: _v18, l: v20, k: v22, v: _v24, s: _v26, r: v28 } => {
      if key_lt(v22, x) {
        let tmp = pred_t_owned(x, v28);
        let (v43, v44) = __rocq_reuse::reset(tmp, |__payload| Clone::clone(__payload));
        match v43 {
          option::Some(v49) => {
            std::mem::drop(v20);
            __rocq_reuse::rebuild(v44, option::<u64>::Some(v49))
          },
          option::None => {
            std::mem::drop(v20);
            __rocq_reuse::rebuild(v44, option::<u64>::Some(v22))
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
pub fn pred_t_1(x: u64, t: &Rc<tree>) -> Rc<option<u64>> {
  let x_1 = x;
  pred_t(x_1, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.pred_t (local: pred_t)
// Variant: borrowed, uncurried, lifted
pub fn pred_t(x: u64, t: &Rc<tree>) -> Rc<option<u64>> {
  let x_1 = x;
  let tmp = t;
  match &**tmp {
    tree::Leaf => {
      Rc::new(option::<u64>::None)
    },
    tree::Node { c: _r, l: s, k: v, v: _k, s: _l, r: c } => {
      let v_clone = Clone::clone(v);
      if key_lt(v_clone, x_1) {
        let tmp_1 = pred_t(x_1, c);
        let (v34, v35) = __rocq_reuse::reset(tmp_1, |__payload| Clone::clone(__payload));
        match v34 {
          option::Some(v40) => {
            __rocq_reuse::rebuild(v35, option::<u64>::Some(v40))
          },
          option::None => {
            let v_clone_1 = Clone::clone(v);
            __rocq_reuse::rebuild(v35, option::<u64>::Some(v_clone_1))
          },
        }
      } else {
        let s_clone = Rc::clone(s);
        pred_t_owned(x_1, s_clone)
      }
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.kth_t
// Variant: uncurried
pub fn kth_t_1(n: u64, t: Rc<tree>) -> Rc<option<u64>> {
  kth_t(n, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.kth_t (local: kth_t)
// Variant: uncurried, lifted
pub fn kth_t(n: u64, t: Rc<tree>) -> Rc<option<u64>> {
  let (v2, v3) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v3);
  match v2 {
    tree::Leaf => {
      Rc::new(option::<u64>::None)
    },
    tree::Node { c: _v18, l: v20, k: v22, v: _v24, s: _v26, r: v28 } => {
      let s = &v20;
      let sl = size(s);
      if ltb(n, sl) {
        std::mem::drop(v28);
        kth_t(n, v20)
      } else {
        if eqb(n, sl) {
          std::mem::drop(v28);
          std::mem::drop(v20);
          Rc::new(option::<u64>::Some(v22))
        } else {
          std::mem::drop(v20);
          let tmp = sub(n, sl);
          kth_t(sub(tmp, 1u64), v28)
        }
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.rank_t
// Variant: borrowed, uncurried
pub fn rank_t_1(x: u64, t: &Rc<tree>) -> u64 {
  let x_1 = x;
  rank_t(x_1, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.rank_t (local: rank_t)
// Variant: borrowed, uncurried, lifted
pub fn rank_t(x: u64, t: &Rc<tree>) -> u64 {
  let x_1 = x;
  let tmp = t;
  match &**tmp {
    tree::Leaf => {
      0u64
    },
    tree::Node { c: _r, l: s, k: v, v: _k, s: _l, r: c } => {
      let v_clone = Clone::clone(v);
      if key_lt(x_1, v_clone) {
        rank_t(x_1, s)
      } else {
        let v_clone_1 = Clone::clone(v);
        if eqb(x_1, v_clone_1) {
          size(s)
        } else {
          let tmp_1 = add(size(s), 1u64);
          let tmp_2 = rank_t(x_1, c);
          add(tmp_1, tmp_2)
        }
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.lookup_t (local: lookup_t)
// Variant: uncurried, lifted
pub fn lookup_t_owned(x: u64, t: Rc<tree>) -> Rc<option<u64>> {
  let (v2, v3) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v3);
  match v2 {
    tree::Leaf => {
      Rc::new(option::<u64>::None)
    },
    tree::Node { c: _v18, l: v20, k: v22, v: v24, s: _v26, r: v28 } => {
      if key_lt(x, v22) {
        std::mem::drop(v28);
        lookup_t_owned(x, v20)
      } else {
        if eqb(x, v22) {
          std::mem::drop(v20);
          std::mem::drop(v28);
          Rc::new(option::<u64>::Some(v24))
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
pub fn lookup_t_1(x: u64, t: &Rc<tree>) -> Rc<option<u64>> {
  let x_1 = x;
  lookup_t(x_1, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.lookup_t (local: lookup_t)
// Variant: borrowed, uncurried, lifted
pub fn lookup_t(x: u64, t: &Rc<tree>) -> Rc<option<u64>> {
  let x_1 = x;
  let tmp = t;
  match &**tmp {
    tree::Leaf => {
      Rc::new(option::<u64>::None)
    },
    tree::Node { c: _r, l: s, k: v, v: k, s: _l, r: c } => {
      let v_clone = Clone::clone(v);
      if key_lt(x_1, v_clone) {
        let s_clone = Rc::clone(s);
        lookup_t_owned(x_1, s_clone)
      } else {
        let v_clone_1 = Clone::clone(v);
        if eqb(x_1, v_clone_1) {
          let k_clone = Clone::clone(k);
          Rc::new(option::<u64>::Some(k_clone))
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
pub fn setv_t_1(x: u64, w: u64, t: Rc<tree>) -> Rc<tree> {
  setv_t(x, w, t)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.setv_t (local: setv_t)
// Variant: uncurried, lifted
pub fn setv_t(x: u64, w: u64, t: Rc<tree>) -> Rc<tree> {
  let (v3, v4) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  match v3 {
    tree::Leaf => {
      __rocq_reuse::rebuild(v4, tree::Leaf)
    },
    tree::Node { c: v19, l: v21, k: v23, v: v25, s: v27, r: v29 } => {
      if key_lt(x, v23) {
        __rocq_reuse::rebuild(v4, tree::Node { c: v19, l: setv_t(x, w, v21), k: v23, v: v25, s: v27, r: v29 })
      } else {
        if eqb(x, v23) {
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
pub fn exec(T: Rc<Array<Rc<tree>>>, C: Rc<Array<Rc<option<u64>>>>, O: Rc<Array<Rc<option<u64>>>>, p: u64, id: u64, op: u64, x: u64, y: u64) -> (((Rc<Array<Rc<tree>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<u64>>>>), u64) {
  let T_ref = &T;
  let tmp = id;
  let t = Clone::clone(&(T_ref)[tmp]);
  let C_ref = &C;
  let tmp_1 = id;
  let cur = Clone::clone(&(C_ref)[tmp_1]);
  if eqb(op, 97u64) {
    std::mem::drop(cur);
    std::mem::drop(t);
    let T_ref_1 = &T;
    let tmp_2 = x;
    let tmp_3 = Clone::clone(&(T_ref_1)[tmp_2]);
    let tmp_4 = rocq_array::set::<Rc<tree>>(T, id, tmp_3);
    let tmp_5 = rocq_array::set::<Rc<option<u64>>>(C, id, Rc::new(option::<u64>::None));
    (((tmp_4, tmp_5), O), p)
  } else {
    if eqb(op, 63u64) {
      std::mem::drop(cur);
      let tmp_6 = rocq_array::set::<Rc<option<u64>>>(C, id, find_t_1(x, t));
      (((T, tmp_6), O), p)
    } else {
      if eqb(op, 108u64) {
        std::mem::drop(cur);
        let tmp_7 = rocq_array::set::<Rc<option<u64>>>(C, id, lower_t_1(x, t));
        (((T, tmp_7), O), p)
      } else {
        if eqb(op, 117u64) {
          std::mem::drop(cur);
          let tmp_8 = rocq_array::set::<Rc<option<u64>>>(C, id, upper_t_owned_1(x, t));
          (((T, tmp_8), O), p)
        } else {
          if eqb(op, 105u64) {
            std::mem::drop(cur);
            let tmp_9 = rocq_array::set::<Rc<tree>>(T, id, insert_t(x, y, t));
            let tmp_10 = rocq_array::set::<Rc<option<u64>>>(C, id, Rc::new(option::<u64>::Some(x)));
            (((tmp_9, tmp_10), O), p)
          } else {
            if eqb(op, 101u64) {
              let (v257, v258) = __rocq_reuse::reset(cur, |__payload| Clone::clone(__payload));
              let tmp_11 = match v257 {
                option::Some(v263) => {
                  delete_t(v263, t)
                },
                option::None => {
                  t
                },
              };
              let tmp_12 = rocq_array::set::<Rc<tree>>(T, id, tmp_11);
              let tmp_13 = rocq_array::set::<Rc<option<u64>>>(C, id, __rocq_reuse::rebuild(v258, option::<u64>::None));
              (((tmp_12, tmp_13), O), p)
            } else {
              if eqb(op, 102u64) {
                std::mem::drop(cur);
                let tmp_14 = rocq_array::set::<Rc<option<u64>>>(C, id, front_t_1(t));
                (((T, tmp_14), O), p)
              } else {
                if eqb(op, 98u64) {
                  std::mem::drop(cur);
                  let tmp_15 = rocq_array::set::<Rc<option<u64>>>(C, id, back_t_1(t));
                  (((T, tmp_15), O), p)
                } else {
                  if eqb(op, 62u64) {
                    let callback: Rc<dyn Fn(u64) -> Rc<option<u64>>> = Rc::new({
                      let __anf_capture_406 = t;
                      move |c: u64| -> Rc<option<u64>> {
                        let t = &__anf_capture_406;
                        upper_t_1(c, t)
                      }
                    });
                    let tmp_16 = rocq_array::set::<Rc<option<u64>>>(C, id, on_cur(cur, callback));
                    (((T, tmp_16), O), p)
                  } else {
                    if eqb(op, 60u64) {
                      let callback_1: Rc<dyn Fn(u64) -> Rc<option<u64>>> = Rc::new({
                        let __anf_capture_463 = t;
                        move |c: u64| -> Rc<option<u64>> {
                          let t = &__anf_capture_463;
                          pred_t_1(c, t)
                        }
                      });
                      let tmp_17 = rocq_array::set::<Rc<option<u64>>>(C, id, on_cur(cur, callback_1));
                      (((T, tmp_17), O), p)
                    } else {
                      if eqb(op, 107u64) {
                        let tmp_18 = 0u64;
                        let tmp_19 = if ltsb(x, tmp_18) {
                          std::mem::drop(cur);
                          std::mem::drop(t);
                          Rc::new(option::<u64>::None)
                        } else {
                          std::mem::drop(cur);
                          kth_t_1(x, t)
                        };
                        let tmp_20 = rocq_array::set::<Rc<option<u64>>>(C, id, tmp_19);
                        (((T, tmp_20), O), p)
                      } else {
                        if eqb(op, 114u64) {
                          let tmp_21 = (T, C);
                          let callback_2: Rc<dyn Fn(u64) -> Rc<option<u64>>> = Rc::new({
                            let __anf_capture_585 = t;
                            move |c: u64| -> Rc<option<u64>> {
                              let t = &__anf_capture_585;
                              let tmp_22 = rank_t_1(c, t);
                              Rc::new(option::<u64>::Some(tmp_22))
                            }
                          });
                          let tmp_23 = rocq_array::set::<Rc<option<u64>>>(O, p, on_cur(cur, callback_2));
                          ((tmp_21, tmp_23), add(p, 1u64))
                        } else {
                          if eqb(op, 103u64) {
                            let tmp_24 = (T, C);
                            let callback_3: Rc<dyn Fn(u64) -> Rc<option<u64>>> = Rc::new({
                              let __anf_capture_655 = t;
                              move |c: u64| -> Rc<option<u64>> {
                                let t = &__anf_capture_655;
                                lookup_t_1(c, t)
                              }
                            });
                            let tmp_25 = rocq_array::set::<Rc<option<u64>>>(O, p, on_cur(cur, callback_3));
                            ((tmp_24, tmp_25), add(p, 1u64))
                          } else {
                            if eqb(op, 115u64) {
                              let (v710, v711) = __rocq_reuse::reset(cur, |__payload| Clone::clone(__payload));
                              std::mem::drop(v711);
                              let tmp_26 = match v710 {
                                option::Some(v716) => {
                                  setv_t_1(v716, x, t)
                                },
                                option::None => {
                                  t
                                },
                              };
                              let tmp_27 = rocq_array::set::<Rc<tree>>(T, id, tmp_26);
                              (((tmp_27, C), O), p)
                            } else {
                              if eqb(op, 122u64) {
                                std::mem::drop(cur);
                                let tmp_28 = (T, C);
                                let tmp_29 = rocq_array::set::<Rc<option<u64>>>(O, p, Rc::new(option::<u64>::Some(size_owned(t))));
                                ((tmp_28, tmp_29), add(p, 1u64))
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
pub fn run_loop_1(commands: Rc<Array<(u64, Rc<operation<u64, u64>>)>>, q: u64, j: u64, T: Rc<Array<Rc<tree>>>, C: Rc<Array<Rc<option<u64>>>>, O: Rc<Array<Rc<option<u64>>>>, p: u64) -> Rc<Array<Rc<option<u64>>>> {
  run_loop(commands, q, j, T, C, O, p, ())
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.run_loop (local: run_loop)
// Variant: uncurried, lifted
pub fn run_loop(commands: Rc<Array<(u64, Rc<operation<u64, u64>>)>>, q: u64, j: u64, T: Rc<Array<Rc<tree>>>, C: Rc<Array<Rc<option<u64>>>>, O: Rc<Array<Rc<option<u64>>>>, p: u64, _H: ()) -> Rc<Array<Rc<option<u64>>>> {
  let tmp = ltb(j, q);
  match bdec(tmp) {
    sumbool::left => {
      let commands_ref = &commands;
      let tmp_1 = j;
      let tmp_2 = Clone::clone(&(commands_ref)[tmp_1]);
      let tmp_3 = encode_machine(tmp_2);
      match tmp_3 {
        (v28, v30) => {
          match v28 {
            (v33, v35) => {
              match v33 {
                (v38, v40) => {
                  let tmp_4 = exec(T, C, O, p, v38, v40, v35, v30);
                  match tmp_4 {
                    (v61, v63) => {
                      match v61 {
                        (v66, v68) => {
                          match v66 {
                            (v71, v73) => {
                              run_loop(commands, q, add(j, 1u64), v71, v73, v68, v63, ())
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
pub fn run_impl(commands: Rc<Array<(u64, Rc<operation<u64, u64>>)>>) -> Rc<Array<Rc<option<u64>>>> {
  let q = rocq_array::length::<(u64, Rc<operation<u64, u64>>)>(&commands);
  let commands_clone = Rc::clone(&commands);
  let n = count_loop_1(commands_clone, q, 0u64, 0u64);
  let tmp = rocq_array::make::<Rc<tree>>(1001u64, Rc::new(tree::Leaf));
  let tmp_1 = rocq_array::make::<Rc<option<u64>>>(1001u64, Rc::new(option::<u64>::None));
  let tmp_2 = rocq_array::make::<Rc<option<u64>>>(n, Rc::new(option::<u64>::None));
  run_loop_1(commands, q, 0u64, tmp, tmp_1, tmp_2, 0u64)
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
