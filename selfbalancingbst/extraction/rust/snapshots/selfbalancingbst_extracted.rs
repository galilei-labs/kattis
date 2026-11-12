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

pub type uint = u64;

pub type sint = u64;

// Rocq: Selfbalancingbst.selfbalancingbst_implem.run_commands
// Variant: uncurried
pub fn run_commands() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>> {
  let v0: fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>> = run_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>> = Rc::new(v0);
  v1
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.run_commands
pub fn run_commands_curried() -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>>> {
  let v0: fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>> = run_impl_curried;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>>> = Rc::new(v0);
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

// Rocq: Selfbalancingbst.selfbalancingbst_implem.bdec
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

// Rocq: Corelib.Init.Datatypes.orb
// Variant: uncurried
pub fn orb(b1: bool, b2: bool) -> bool {
  match b1 {
    true => {
      true
    },
    false => {
      b2
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.is_out
pub fn is_out(op: u64) -> bool {
  let v23 = orb(eqb(op, 114u64), eqb(op, 103u64));
  orb(v23, eqb(op, 122u64))
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.count_loop
// Variant: uncurried
pub fn count_loop_1(ops: Rc<Array<u64>>, q: u64, j: u64, acc: u64) -> u64 {
  count_loop(ops, q, j, acc, ())
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.count_loop (local: count_loop)
// Variant: uncurried, lifted
pub fn count_loop(ops: Rc<Array<u64>>, q: u64, j: u64, acc: u64, _H: ()) -> u64 {
  let v12 = ltb(j, q);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(j, 1u64);
      let v25 = &ops;
      let v27 = j;
      let v29 = Clone::clone(&(v25)[v27]);
      let v32 = match is_out(v29) {
        true => {
          add(acc, 1u64)
        },
        false => {
          acc
        },
      };
      count_loop(ops, q, v23, v32, ())
    },
    sumbool::right => {
      std::mem::drop(ops);
      acc
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
      match key_lt(x, v22) {
        true => {
          std::mem::drop(v28);
          find_t(x, v20)
        },
        false => {
          match eqb(x, v22) {
            true => {
              std::mem::drop(v20);
              std::mem::drop(v28);
              Rc::new(option::<u64>::Some(v22))
            },
            false => {
              std::mem::drop(v20);
              find_t(x, v28)
            },
          }
        },
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
      match key_lt(v22, x) {
        true => {
          std::mem::drop(v20);
          lower_t(x, v28)
        },
        false => {
          let v50 = lower_t(x, v20);
          let (v51, v52) = __rocq_reuse::reset(v50, |__payload| Clone::clone(__payload));
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
        },
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
      match key_lt(x, v22) {
        true => {
          let v42 = upper_t_owned(x, v20);
          let (v43, v44) = __rocq_reuse::reset(v42, |__payload| Clone::clone(__payload));
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
        },
        false => {
          std::mem::drop(v20);
          upper_t_owned(x, v28)
        },
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
  let v3 = t;
  match &**v3 {
    tree::Leaf => {
      Rc::new(option::<u64>::None)
    },
    tree::Node { c: _r, l: s, k: v, v: _k, s: _l, r: c } => {
      let v26 = Clone::clone(v);
      match key_lt(x_1, v26) {
        true => {
          let v33 = upper_t(x_1, s);
          let (v34, v35) = __rocq_reuse::reset(v33, |__payload| Clone::clone(__payload));
          match v34 {
            option::Some(v40) => {
              __rocq_reuse::rebuild(v35, option::<u64>::Some(v40))
            },
            option::None => {
              let v50 = Clone::clone(v);
              __rocq_reuse::rebuild(v35, option::<u64>::Some(v50))
            },
          }
        },
        false => {
          let v63 = Rc::clone(c);
          upper_t_owned(x_1, v63)
        },
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
  let v1 = t;
  match &**v1 {
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
  let v10 = size(&l);
  let v14 = size(&r);
  let v19 = add(v10, v14);
  Rc::new(tree::Node { c, l, k, v, s: add(v19, 1u64), r })
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
                      let v82 = node(color::Black, Rc::clone(s), Clone::clone(vx), Clone::clone(x), Rc::clone(s0));
                      let v96 = node(color::Black, Rc::clone(c1), k, v, r);
                      let v102 = Clone::clone(vy);
                      let v103 = Clone::clone(y);
                      std::mem::drop(l);
                      node(color::Red, v82, v102, v103, v96)
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
                  let v154 = Rc::clone(s0);
                  let v156 = Clone::clone(vx_1);
                  let v158 = Clone::clone(x_1);
                  let v160 = Rc::clone(c1);
                  let v161 = node(color::Black, v154, v156, v158, v160);
                  let v175 = node(color::Black, Rc::clone(c0), k, v, r);
                  let v181 = Clone::clone(vx);
                  let v182 = Clone::clone(x);
                  std::mem::drop(l);
                  node(color::Red, v161, v181, v182, v175)
                },
                color::Black => {
                  match &**c0 {
                    tree::Leaf => {
                      node(color::Black, l, k, v, r)
                    },
                    tree::Node { c: c_1, l: s1, k: vy, v: y, s: _b_1, r: c2 } => {
                      match c_1 {
                        color::Red => {
                          let v235 = node(color::Black, Rc::clone(s), Clone::clone(vx), Clone::clone(x), Rc::clone(s1));
                          let v249 = node(color::Black, Rc::clone(c2), k, v, r);
                          let v255 = Clone::clone(vy);
                          let v256 = Clone::clone(y);
                          std::mem::drop(l);
                          node(color::Red, v235, v255, v256, v249)
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
                      let v82 = node(color::Black, l, k, v, Rc::clone(s));
                      let v89 = Rc::clone(s0);
                      let v91 = Clone::clone(vz);
                      let v93 = Clone::clone(z);
                      let v95 = Rc::clone(c1);
                      let v96 = node(color::Black, v89, v91, v93, v95);
                      let v102 = Clone::clone(vy);
                      let v103 = Clone::clone(y);
                      std::mem::drop(r);
                      node(color::Red, v82, v102, v103, v96)
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
                  let v161 = node(color::Black, l, k, v, Rc::clone(s0));
                  let v175 = node(color::Black, Rc::clone(c1), Clone::clone(vy), Clone::clone(y), Rc::clone(c0));
                  let v181 = Clone::clone(vy_1);
                  let v182 = Clone::clone(y_1);
                  std::mem::drop(r);
                  node(color::Red, v161, v181, v182, v175)
                },
                color::Black => {
                  match &**c0 {
                    tree::Leaf => {
                      node(color::Black, l, k, v, r)
                    },
                    tree::Node { c: d_1, l: s1, k: vz, v: z, s: _c_1, r: c2 } => {
                      match d_1 {
                        color::Red => {
                          let v235 = node(color::Black, l, k, v, Rc::clone(s));
                          let v242 = Rc::clone(s1);
                          let v244 = Clone::clone(vz);
                          let v246 = Clone::clone(z);
                          let v248 = Rc::clone(c2);
                          let v249 = node(color::Black, v242, v244, v246, v248);
                          let v255 = Clone::clone(vy);
                          let v256 = Clone::clone(y);
                          std::mem::drop(r);
                          node(color::Red, v235, v255, v256, v249)
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
      let v43 = Clone::clone(vy);
      match key_lt(x, v43) {
        true => {
          match r {
            color::Red => {
              let v57 = ins(x, vx, Rc::clone(s));
              let v63 = Clone::clone(vy);
              let v65 = Clone::clone(y);
              let v66 = Rc::clone(c);
              std::mem::drop(t);
              node(color::Red, v57, v63, v65, v66)
            },
            color::Black => {
              let v80 = ins(x, vx, Rc::clone(s));
              let v83 = Clone::clone(vy);
              let v85 = Clone::clone(y);
              let v86 = Rc::clone(c);
              std::mem::drop(t);
              lbal(v80, v83, v85, v86)
            },
          }
        },
        false => {
          let v98 = Clone::clone(vy);
          match eqb(x, v98) {
            true => {
              t
            },
            false => {
              match r {
                color::Red => {
                  let v114 = ins(x, vx, Rc::clone(c));
                  let v118 = Rc::clone(s);
                  let v120 = Clone::clone(vy);
                  let v121 = Clone::clone(y);
                  std::mem::drop(t);
                  node(color::Red, v118, v120, v121, v114)
                },
                color::Black => {
                  let v136 = ins(x, vx, Rc::clone(c));
                  let v138 = Rc::clone(s);
                  let v140 = Clone::clone(vy);
                  let v141 = Clone::clone(y);
                  std::mem::drop(t);
                  rbal(v138, v140, v141, v136)
                },
              }
            },
          }
        },
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
                      let v82 = node(color::Black, l, k, v, Rc::clone(s));
                      let v89 = Rc::clone(s0);
                      let v91 = Clone::clone(vz_1);
                      let v93 = Clone::clone(z_1);
                      let v95 = Rc::clone(c1);
                      let v96 = node(color::Black, v89, v91, v93, v95);
                      let v102 = Clone::clone(vz);
                      let v103 = Clone::clone(z);
                      std::mem::drop(r);
                      node(color::Red, v82, v102, v103, v96)
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
                      let v162 = node(color::Black, l, k, v, Rc::clone(s0));
                      let v176 = node(color::Black, Rc::clone(c1), Clone::clone(vz), Clone::clone(z), Rc::clone(c0));
                      let v182 = Clone::clone(vy);
                      let v183 = Clone::clone(y);
                      std::mem::drop(r);
                      node(color::Red, v162, v182, v183, v176)
                    },
                    tree::Node { c: d_1, l: s1, k: vz_1, v: z_1, s: _c_1, r: c2 } => {
                      match d_1 {
                        color::Red => {
                          let v219 = node(color::Black, l, k, v, Rc::clone(s));
                          let v226 = Rc::clone(s1);
                          let v228 = Clone::clone(vz_1);
                          let v230 = Clone::clone(z_1);
                          let v232 = Rc::clone(c2);
                          let v233 = node(color::Black, v226, v228, v230, v232);
                          let v239 = Clone::clone(vz);
                          let v240 = Clone::clone(z);
                          std::mem::drop(r);
                          node(color::Red, v219, v239, v240, v233)
                        },
                        color::Black => {
                          let v263 = node(color::Black, l, k, v, Rc::clone(s0));
                          let v277 = node(color::Black, Rc::clone(c1), Clone::clone(vz), Clone::clone(z), Rc::clone(c0));
                          let v283 = Clone::clone(vy);
                          let v284 = Clone::clone(y);
                          std::mem::drop(r);
                          node(color::Red, v263, v283, v284, v277)
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
                          let v343 = node(color::Black, l, k, v, Rc::clone(s));
                          let v350 = Rc::clone(s1);
                          let v352 = Clone::clone(vz_1);
                          let v354 = Clone::clone(z_1);
                          let v356 = Rc::clone(c2);
                          let v357 = node(color::Black, v350, v352, v354, v356);
                          let v363 = Clone::clone(vz);
                          let v364 = Clone::clone(z);
                          std::mem::drop(r);
                          node(color::Red, v343, v363, v364, v357)
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
                      let v99 = node(color::Black, l, k, v, Rc::clone(s0));
                      let v104 = makeRed(Rc::clone(c0));
                      let v113 = rbal_(Rc::clone(c1), Clone::clone(vz), Clone::clone(z), v104);
                      let v119 = Clone::clone(vy);
                      let v120 = Clone::clone(y);
                      std::mem::drop(r);
                      node(color::Red, v99, v119, v120, v113)
                    },
                  }
                },
              }
            },
            color::Black => {
              let v140 = Rc::clone(s);
              let v142 = Clone::clone(vz);
              let v144 = Clone::clone(z);
              let v145 = Rc::clone(c0);
              std::mem::drop(r);
              rbal_(l, k, v, node(color::Red, v140, v142, v144, v145))
            },
          }
        },
      }
    },
    tree::Node { c: b, l: s, k: vx, v: x, s: _a_2, r: c } => {
      match b {
        color::Red => {
          let v187 = Rc::clone(s);
          let v189 = Clone::clone(vx);
          let v191 = Clone::clone(x);
          let v192 = Rc::clone(c);
          std::mem::drop(l);
          let v194 = node(color::Black, v187, v189, v191, v192);
          node(color::Red, v194, k, v, r)
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
                          let v301 = node(color::Black, l, k, v, Rc::clone(s0));
                          let v306 = makeRed(Rc::clone(c0));
                          let v315 = rbal_(Rc::clone(c1), Clone::clone(vz), Clone::clone(z), v306);
                          let v321 = Clone::clone(vy);
                          let v322 = Clone::clone(y);
                          std::mem::drop(r);
                          node(color::Red, v301, v321, v322, v315)
                        },
                      }
                    },
                  }
                },
                color::Black => {
                  let v342 = Rc::clone(s_1);
                  let v344 = Clone::clone(vz);
                  let v346 = Clone::clone(z);
                  let v347 = Rc::clone(c0);
                  std::mem::drop(r);
                  rbal_(l, k, v, node(color::Red, v342, v344, v346, v347))
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
  let v4: Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = append(l);
  v4
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
              let v27: &Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<tree>>> = &append_2;
              let v30: Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = v27(lc);
              let v31: &Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = &v30;
              let lrl = v31(Rc::clone(s_1));
              match &*lrl {
                tree::Leaf => {
                  std::mem::drop(v30);
                  std::mem::drop(l);
                  std::mem::drop(append_2);
                  let v48 = Clone::clone(rv);
                  let v50 = Clone::clone(rx);
                  let v51 = Rc::clone(rc);
                  std::mem::drop(r);
                  let v53 = node(color::Red, lrl, v48, v50, v51);
                  node(color::Red, s, lv, lx, v53)
                },
                tree::Node { c: rl_, l: s_2, k: vx, v: x, s: _lr_, r: c } => {
                  match rl_ {
                    color::Red => {
                      std::mem::drop(v30);
                      std::mem::drop(l);
                      std::mem::drop(append_2);
                      let v96 = node(color::Red, s, lv, lx, Rc::clone(s_2));
                      let v103 = Rc::clone(c);
                      let v105 = Clone::clone(rv);
                      let v107 = Clone::clone(rx);
                      let v108 = Rc::clone(rc);
                      std::mem::drop(r);
                      let v110 = node(color::Red, v103, v105, v107, v108);
                      let v116 = Clone::clone(vx);
                      let v117 = Clone::clone(x);
                      std::mem::drop(lrl);
                      node(color::Red, v96, v116, v117, v110)
                    },
                    color::Black => {
                      std::mem::drop(v30);
                      std::mem::drop(l);
                      std::mem::drop(append_2);
                      let v135 = Clone::clone(rv);
                      let v137 = Clone::clone(rx);
                      let v138 = Rc::clone(rc);
                      std::mem::drop(r);
                      let v140 = node(color::Red, lrl, v135, v137, v138);
                      node(color::Red, s, lv, lx, v140)
                    },
                  }
                },
              }
            },
            color::Black => {
              std::mem::drop(l);
              let v163: &Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<tree>>> = &append_2;
              let v166: Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = v163(lc);
              std::mem::drop(append_2);
              let v167: &Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = &v166;
              let v170 = v167(r);
              std::mem::drop(v166);
              node(color::Red, s, lv, lx, v170)
            },
          }
        },
        color::Black => {
          match rr {
            color::Red => {
              let v208 = append_l(l, lr, append_2, lc, s, lv, lx, Rc::clone(s_1));
              let v214 = Clone::clone(rv);
              let v216 = Clone::clone(rx);
              let v217 = Rc::clone(rc);
              std::mem::drop(r);
              node(color::Red, v208, v214, v216, v217)
            },
            color::Black => {
              let v222: &Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<tree>>> = &append_2;
              let v225: Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = v222(lc);
              let v226: &Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = &v225;
              let lrl = v226(Rc::clone(s_1));
              match &*lrl {
                tree::Leaf => {
                  std::mem::drop(v225);
                  std::mem::drop(l);
                  std::mem::drop(append_2);
                  let v241 = Clone::clone(rv);
                  let v243 = Clone::clone(rx);
                  let v244 = Rc::clone(rc);
                  std::mem::drop(r);
                  lbalS(s, lv, lx, node(color::Black, lrl, v241, v243, v244))
                },
                tree::Node { c: rl_, l: s_2, k: vx, v: x, s: _lr__1, r: c } => {
                  match rl_ {
                    color::Red => {
                      std::mem::drop(v225);
                      std::mem::drop(l);
                      std::mem::drop(append_2);
                      let v287 = node(color::Black, s, lv, lx, Rc::clone(s_2));
                      let v294 = Rc::clone(c);
                      let v296 = Clone::clone(rv);
                      let v298 = Clone::clone(rx);
                      let v299 = Rc::clone(rc);
                      std::mem::drop(r);
                      let v301 = node(color::Black, v294, v296, v298, v299);
                      let v307 = Clone::clone(vx);
                      let v308 = Clone::clone(x);
                      std::mem::drop(lrl);
                      node(color::Red, v287, v307, v308, v301)
                    },
                    color::Black => {
                      std::mem::drop(v225);
                      std::mem::drop(l);
                      std::mem::drop(append_2);
                      let v324 = Clone::clone(rv);
                      let v326 = Clone::clone(rx);
                      let v327 = Rc::clone(rc);
                      std::mem::drop(r);
                      lbalS(s, lv, lx, node(color::Black, lrl, v324, v326, v327))
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
  let v1 = {
    move |l: Rc<tree>| -> Rc<dyn Fn(Rc<tree>) -> Rc<tree>> {
      let v6: Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = append(l);
      v6
    }
  };
  let v9: Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<tree>>> = Rc::new(v1);
  let append_2: Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<tree>>> = v9;
  let v12: Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = match &*l {
    tree::Leaf => {
      std::mem::drop(append_2);
      std::mem::drop(l);
      let v13 = {
        move |r: Rc<tree>| -> Rc<tree> {
          r
        }
      };
      let v17: Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = Rc::new(v13);
      v17
    },
    tree::Node { c: lr, l: s, k: lv, v: lx, s: _ll, r: lc } => {
      let v35 = Rc::clone(&l);
      let v37 = Clone::clone(lr);
      let v41 = Rc::clone(lc);
      let v43 = Rc::clone(s);
      let v45 = Clone::clone(lv);
      let v46 = Clone::clone(lx);
      std::mem::drop(l);
      let v48 = {
        let __anf_capture_53 = append_2;
        move |r: Rc<tree>| -> Rc<tree> {
          let v66 = Rc::clone(&v35);
          let v68 = Clone::clone(&v37);
          let v69: Rc<dyn Fn(Rc<tree>) -> Rc<dyn Fn(Rc<tree>) -> Rc<tree>>> = Rc::clone(&__anf_capture_53);
          let v72 = Rc::clone(&v41);
          let v74 = Rc::clone(&v43);
          let v76 = Clone::clone(&v45);
          let v78 = Clone::clone(&v46);
          append_l(v66, v68, v69, v72, v74, v76, v78, r)
        }
      };
      let v84: Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = Rc::new(v48);
      v84
    },
  };
  v12
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
                      let v99 = lbal(makeRed(Rc::clone(s)), Clone::clone(vx), Clone::clone(x), Rc::clone(s0));
                      let v113 = node(color::Black, Rc::clone(c1), k, v, r);
                      let v119 = Clone::clone(vy);
                      let v120 = Clone::clone(y);
                      std::mem::drop(l);
                      node(color::Red, v99, v119, v120, v113)
                    },
                  }
                },
              }
            },
            color::Black => {
              let v140 = Rc::clone(s);
              let v142 = Clone::clone(vx);
              let v144 = Clone::clone(x);
              let v145 = Rc::clone(c0);
              std::mem::drop(l);
              lbal(node(color::Red, v140, v142, v144, v145), k, v, r)
            },
          }
        },
      }
    },
    tree::Node { c, l: s, k: vy, v: y, s: _b, r: c0 } => {
      match c {
        color::Red => {
          let v187 = Rc::clone(s);
          let v189 = Clone::clone(vy);
          let v191 = Clone::clone(y);
          let v192 = Rc::clone(c0);
          std::mem::drop(r);
          let v194 = node(color::Black, v187, v189, v191, v192);
          node(color::Red, l, k, v, v194)
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
                          let v301 = lbal(makeRed(Rc::clone(s_1)), Clone::clone(vx), Clone::clone(x), Rc::clone(s0));
                          let v315 = node(color::Black, Rc::clone(c1), k, v, r);
                          let v321 = Clone::clone(vy_1);
                          let v322 = Clone::clone(y_1);
                          std::mem::drop(l);
                          node(color::Red, v301, v321, v322, v315)
                        },
                      }
                    },
                  }
                },
                color::Black => {
                  let v342 = Rc::clone(s_1);
                  let v344 = Clone::clone(vx);
                  let v346 = Clone::clone(x);
                  let v347 = Rc::clone(c0_1);
                  std::mem::drop(l);
                  lbal(node(color::Red, v342, v344, v346, v347), k, v, r)
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
      match key_lt(x, v22) {
        true => {
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
        },
        false => {
          match eqb(x, v22) {
            true => {
              let v131: Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = append_1(v20);
              let v132: &Rc<dyn Fn(Rc<tree>) -> Rc<tree>> = &v131;
              let v135 = v132(v28);
              std::mem::drop(v131);
              v135
            },
            false => {
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
            },
          }
        },
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
      let v32 = front_t(v19);
      let (v33, v34) = __rocq_reuse::reset(v32, |__payload| Clone::clone(__payload));
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
      let v32 = back_t(v27);
      let (v33, v34) = __rocq_reuse::reset(v32, |__payload| Clone::clone(__payload));
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
      let v10: &Rc<dyn Fn(u64) -> Rc<option<u64>>> = &f;
      let v13 = v10(v8);
      std::mem::drop(f);
      v13
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
      match key_lt(v22, x) {
        true => {
          let v42 = pred_t_owned(x, v28);
          let (v43, v44) = __rocq_reuse::reset(v42, |__payload| Clone::clone(__payload));
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
        },
        false => {
          std::mem::drop(v28);
          pred_t_owned(x, v20)
        },
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
  let v3 = t;
  match &**v3 {
    tree::Leaf => {
      Rc::new(option::<u64>::None)
    },
    tree::Node { c: _r, l: s, k: v, v: _k, s: _l, r: c } => {
      let v24 = Clone::clone(v);
      match key_lt(v24, x_1) {
        true => {
          let v33 = pred_t(x_1, c);
          let (v34, v35) = __rocq_reuse::reset(v33, |__payload| Clone::clone(__payload));
          match v34 {
            option::Some(v40) => {
              __rocq_reuse::rebuild(v35, option::<u64>::Some(v40))
            },
            option::None => {
              let v50 = Clone::clone(v);
              __rocq_reuse::rebuild(v35, option::<u64>::Some(v50))
            },
          }
        },
        false => {
          let v63 = Rc::clone(s);
          pred_t_owned(x_1, v63)
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
      match ltb(n, sl) {
        true => {
          std::mem::drop(v28);
          kth_t(n, v20)
        },
        false => {
          match eqb(n, sl) {
            true => {
              std::mem::drop(v28);
              std::mem::drop(v20);
              Rc::new(option::<u64>::Some(v22))
            },
            false => {
              std::mem::drop(v20);
              let v69 = sub(n, sl);
              kth_t(sub(v69, 1u64), v28)
            },
          }
        },
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
  let v3 = t;
  match &**v3 {
    tree::Leaf => {
      0u64
    },
    tree::Node { c: _r, l: s, k: v, v: _k, s: _l, r: c } => {
      let v25 = Clone::clone(v);
      match key_lt(x_1, v25) {
        true => {
          rank_t(x_1, s)
        },
        false => {
          let v39 = Clone::clone(v);
          match eqb(x_1, v39) {
            true => {
              size(s)
            },
            false => {
              let v58 = add(size(s), 1u64);
              let v63 = rank_t(x_1, c);
              add(v58, v63)
            },
          }
        },
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
      match key_lt(x, v22) {
        true => {
          std::mem::drop(v28);
          lookup_t_owned(x, v20)
        },
        false => {
          match eqb(x, v22) {
            true => {
              std::mem::drop(v20);
              std::mem::drop(v28);
              Rc::new(option::<u64>::Some(v24))
            },
            false => {
              std::mem::drop(v20);
              lookup_t_owned(x, v28)
            },
          }
        },
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
  let v3 = t;
  match &**v3 {
    tree::Leaf => {
      Rc::new(option::<u64>::None)
    },
    tree::Node { c: _r, l: s, k: v, v: k, s: _l, r: c } => {
      let v26 = Clone::clone(v);
      match key_lt(x_1, v26) {
        true => {
          let v33 = Rc::clone(s);
          lookup_t_owned(x_1, v33)
        },
        false => {
          let v41 = Clone::clone(v);
          match eqb(x_1, v41) {
            true => {
              let v45 = Clone::clone(k);
              Rc::new(option::<u64>::Some(v45))
            },
            false => {
              let v55 = Rc::clone(c);
              lookup_t_owned(x_1, v55)
            },
          }
        },
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
      match key_lt(x, v23) {
        true => {
          __rocq_reuse::rebuild(v4, tree::Node { c: v19, l: setv_t(x, w, v21), k: v23, v: v25, s: v27, r: v29 })
        },
        false => {
          match eqb(x, v23) {
            true => {
              __rocq_reuse::rebuild(v4, tree::Node { c: v19, l: v21, k: v23, v: w, s: v27, r: v29 })
            },
            false => {
              __rocq_reuse::rebuild(v4, tree::Node { c: v19, l: v21, k: v23, v: v25, s: v27, r: setv_t(x, w, v29) })
            },
          }
        },
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.exec
// Variant: uncurried
#[inline(never)]
pub fn exec(T: Rc<Array<Rc<tree>>>, C: Rc<Array<Rc<option<u64>>>>, O: Rc<Array<Rc<option<u64>>>>, p: u64, id: u64, op: u64, x: u64, y: u64) -> (((Rc<Array<Rc<tree>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<u64>>>>), u64) {
  let v8 = &T;
  let v10 = id;
  let t = Clone::clone(&(v8)[v10]);
  let v12 = &C;
  let v14 = id;
  let cur = Clone::clone(&(v12)[v14]);
  match eqb(op, 97u64) {
    true => {
      std::mem::drop(cur);
      std::mem::drop(t);
      let v25 = &T;
      let v27 = x;
      let v28 = Clone::clone(&(v25)[v27]);
      let v35 = rocq_array::set::<Rc<tree>>(T, id, v28);
      let v45 = rocq_array::set::<Rc<option<u64>>>(C, id, Rc::new(option::<u64>::None));
      (((v35, v45), O), p)
    },
    false => {
      match eqb(op, 63u64) {
        true => {
          std::mem::drop(cur);
          let v87 = rocq_array::set::<Rc<option<u64>>>(C, id, find_t_1(x, t));
          (((T, v87), O), p)
        },
        false => {
          match eqb(op, 108u64) {
            true => {
              std::mem::drop(cur);
              let v129 = rocq_array::set::<Rc<option<u64>>>(C, id, lower_t_1(x, t));
              (((T, v129), O), p)
            },
            false => {
              match eqb(op, 117u64) {
                true => {
                  std::mem::drop(cur);
                  let v171 = rocq_array::set::<Rc<option<u64>>>(C, id, upper_t_owned_1(x, t));
                  (((T, v171), O), p)
                },
                false => {
                  match eqb(op, 105u64) {
                    true => {
                      std::mem::drop(cur);
                      let v215 = rocq_array::set::<Rc<tree>>(T, id, insert_t(x, y, t));
                      let v227 = rocq_array::set::<Rc<option<u64>>>(C, id, Rc::new(option::<u64>::Some(x)));
                      (((v215, v227), O), p)
                    },
                    false => {
                      match eqb(op, 101u64) {
                        true => {
                          let (v257, v258) = __rocq_reuse::reset(cur, |__payload| Clone::clone(__payload));
                          let v262 = match v257 {
                            option::Some(v263) => {
                              delete_t(v263, t)
                            },
                            option::None => {
                              t
                            },
                          };
                          let v282 = rocq_array::set::<Rc<tree>>(T, id, v262);
                          let v292 = rocq_array::set::<Rc<option<u64>>>(C, id, __rocq_reuse::rebuild(v258, option::<u64>::None));
                          (((v282, v292), O), p)
                        },
                        false => {
                          match eqb(op, 102u64) {
                            true => {
                              std::mem::drop(cur);
                              let v332 = rocq_array::set::<Rc<option<u64>>>(C, id, front_t_1(t));
                              (((T, v332), O), p)
                            },
                            false => {
                              match eqb(op, 98u64) {
                                true => {
                                  std::mem::drop(cur);
                                  let v372 = rocq_array::set::<Rc<option<u64>>>(C, id, back_t_1(t));
                                  (((T, v372), O), p)
                                },
                                false => {
                                  match eqb(op, 62u64) {
                                    true => {
                                      let v405 = {
                                        let __anf_capture_406 = t;
                                        move |c: u64| -> Rc<option<u64>> {
                                          let t = &__anf_capture_406;
                                          upper_t_1(c, t)
                                        }
                                      };
                                      let v416: Rc<dyn Fn(u64) -> Rc<option<u64>>> = Rc::new(v405);
                                      let v429 = rocq_array::set::<Rc<option<u64>>>(C, id, on_cur(cur, v416));
                                      (((T, v429), O), p)
                                    },
                                    false => {
                                      match eqb(op, 60u64) {
                                        true => {
                                          let v462 = {
                                            let __anf_capture_463 = t;
                                            move |c: u64| -> Rc<option<u64>> {
                                              let t = &__anf_capture_463;
                                              pred_t_1(c, t)
                                            }
                                          };
                                          let v473: Rc<dyn Fn(u64) -> Rc<option<u64>>> = Rc::new(v462);
                                          let v486 = rocq_array::set::<Rc<option<u64>>>(C, id, on_cur(cur, v473));
                                          (((T, v486), O), p)
                                        },
                                        false => {
                                          match eqb(op, 107u64) {
                                            true => {
                                              let v518 = 0u64;
                                              let v524 = match ltsb(x, v518) {
                                                true => {
                                                  std::mem::drop(cur);
                                                  std::mem::drop(t);
                                                  Rc::new(option::<u64>::None)
                                                },
                                                false => {
                                                  std::mem::drop(cur);
                                                  kth_t_1(x, t)
                                                },
                                              };
                                              let v545 = rocq_array::set::<Rc<option<u64>>>(C, id, v524);
                                              (((T, v545), O), p)
                                            },
                                            false => {
                                              match eqb(op, 114u64) {
                                                true => {
                                                  let v580 = (T, C);
                                                  let v584 = {
                                                    let __anf_capture_585 = t;
                                                    move |c: u64| -> Rc<option<u64>> {
                                                      let t = &__anf_capture_585;
                                                      let v593 = rank_t_1(c, t);
                                                      Rc::new(option::<u64>::Some(v593))
                                                    }
                                                  };
                                                  let v600: Rc<dyn Fn(u64) -> Rc<option<u64>>> = Rc::new(v584);
                                                  let v613 = rocq_array::set::<Rc<option<u64>>>(O, p, on_cur(cur, v600));
                                                  ((v580, v613), add(p, 1u64))
                                                },
                                                false => {
                                                  match eqb(op, 103u64) {
                                                    true => {
                                                      let v650 = (T, C);
                                                      let v654 = {
                                                        let __anf_capture_655 = t;
                                                        move |c: u64| -> Rc<option<u64>> {
                                                          let t = &__anf_capture_655;
                                                          lookup_t_1(c, t)
                                                        }
                                                      };
                                                      let v665: Rc<dyn Fn(u64) -> Rc<option<u64>>> = Rc::new(v654);
                                                      let v678 = rocq_array::set::<Rc<option<u64>>>(O, p, on_cur(cur, v665));
                                                      ((v650, v678), add(p, 1u64))
                                                    },
                                                    false => {
                                                      match eqb(op, 115u64) {
                                                        true => {
                                                          let (v710, v711) = __rocq_reuse::reset(cur, |__payload| Clone::clone(__payload));
                                                          std::mem::drop(v711);
                                                          let v715 = match v710 {
                                                            option::Some(v716) => {
                                                              setv_t_1(v716, x, t)
                                                            },
                                                            option::None => {
                                                              t
                                                            },
                                                          };
                                                          let v738 = rocq_array::set::<Rc<tree>>(T, id, v715);
                                                          (((v738, C), O), p)
                                                        },
                                                        false => {
                                                          match eqb(op, 122u64) {
                                                            true => {
                                                              std::mem::drop(cur);
                                                              let v771 = (T, C);
                                                              let v788 = rocq_array::set::<Rc<option<u64>>>(O, p, Rc::new(option::<u64>::Some(size_owned(t))));
                                                              ((v771, v788), add(p, 1u64))
                                                            },
                                                            false => {
                                                              std::mem::drop(cur);
                                                              std::mem::drop(t);
                                                              (((T, C), O), p)
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
          }
        },
      }
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.run_loop
// Variant: uncurried
pub fn run_loop_1(ids: Rc<Array<u64>>, ops: Rc<Array<u64>>, xs: Rc<Array<u64>>, ys: Rc<Array<u64>>, q: u64, j: u64, T: Rc<Array<Rc<tree>>>, C: Rc<Array<Rc<option<u64>>>>, O: Rc<Array<Rc<option<u64>>>>, p: u64) -> Rc<Array<Rc<option<u64>>>> {
  run_loop(ids, ops, xs, ys, q, j, T, C, O, p, ())
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.run_loop (local: run_loop)
// Variant: uncurried, lifted
pub fn run_loop(ids: Rc<Array<u64>>, ops: Rc<Array<u64>>, xs: Rc<Array<u64>>, ys: Rc<Array<u64>>, q: u64, j: u64, T: Rc<Array<Rc<tree>>>, C: Rc<Array<Rc<option<u64>>>>, O: Rc<Array<Rc<option<u64>>>>, p: u64, _H: ()) -> Rc<Array<Rc<option<u64>>>> {
  let v18 = ltb(j, q);
  match bdec(v18) {
    sumbool::left => {
      let v23 = &ids;
      let v25 = j;
      let v26 = Clone::clone(&(v23)[v25]);
      let v27 = &ops;
      let v29 = j;
      let v30 = Clone::clone(&(v27)[v29]);
      let v31 = &xs;
      let v33 = j;
      let v34 = Clone::clone(&(v31)[v33]);
      let v35 = &ys;
      let v37 = j;
      let v38 = Clone::clone(&(v35)[v37]);
      let v55 = exec(T, C, O, p, v26, v30, v34, v38);
      match v55 {
        (v57, v59) => {
          match v57 {
            (v62, v64) => {
              match v62 {
                (v67, v69) => {
                  run_loop(ids, ops, xs, ys, q, add(j, 1u64), v67, v69, v64, v59, ())
                },
              }
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(ids);
      std::mem::drop(ops);
      std::mem::drop(xs);
      std::mem::drop(ys);
      std::mem::drop(T);
      std::mem::drop(C);
      O
    },
  }
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.run_impl
// Variant: uncurried
pub fn run_impl(ids: Rc<Array<u64>>, ops: Rc<Array<u64>>, xs: Rc<Array<u64>>, ys: Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>> {
  let v4 = &ids;
  let q = rocq_array::length::<u64>(&v4);
  let v13 = Rc::clone(&ops);
  let n = count_loop_1(v13, q, 0u64, 0u64);
  let v33 = rocq_array::make::<Rc<tree>>(1001u64, Rc::new(tree::Leaf));
  let v43 = rocq_array::make::<Rc<option<u64>>>(1001u64, Rc::new(option::<u64>::None));
  let v51 = rocq_array::make::<Rc<option<u64>>>(n, Rc::new(option::<u64>::None));
  run_loop_1(ids, ops, xs, ys, q, 0u64, v33, v43, v51, 0u64)
}

// Rocq: Selfbalancingbst.selfbalancingbst_implem.run_impl
pub fn run_impl_curried(ids: Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>> {
  let v3 = {
    move |ops: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>> {
      let ids = &ids;
      let v8 = Rc::clone(ids);
      let v11 = {
        move |xs: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>> {
          let ids = &v8;
          let ops = &ops;
          let v18 = Rc::clone(ids);
          let v20 = Rc::clone(ops);
          let v23 = {
            move |ys: Rc<Array<u64>>| -> Rc<Array<Rc<option<u64>>>> {
              let v33 = Rc::clone(&v18);
              let v35 = Rc::clone(&v20);
              let v37 = Rc::clone(&xs);
              run_impl(v33, v35, v37, ys)
            }
          };
          let v43: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>> = Rc::new(v23);
          v43
        }
      };
      let v47: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>> = Rc::new(v11);
      v47
    }
  };
  let v51: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>> {
  let v0: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>> = __rocq_global_1714.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_1714: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>> = run_commands(); }
std::thread_local! { static __rocq_global_1717: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>>> = run_commands_curried(); }