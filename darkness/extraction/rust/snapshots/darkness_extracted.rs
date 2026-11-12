// Generated from OwnedANF. This printer is not verified.
#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub struct bst {
  pub bd: Rc<Array<u64>>,
  pub bp: Rc<Array<u64>>,
  pub bq: Rc<Array<u64>>,
  pub bt: u64,
}

impl Clone for bst {
  fn clone(&self) -> Self {
    match self {
      bst { bd: __field0, bp: __field1, bq: __field2, bt: __field3 } => bst { bd: Clone::clone(__field0), bp: Clone::clone(__field1), bq: Clone::clone(__field2), bt: Clone::clone(__field3) },
    }
  }
}

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<std::cmp::Ordering>; };

pub enum Z {
  Z0,
  Zpos(Rc<positive>),
  Zneg(Rc<positive>),
}

impl Clone for Z {
  fn clone(&self) -> Self {
    match self {
      Z::Z0 => Z::Z0,
      Z::Zpos(__field0) => Z::Zpos(Clone::clone(__field0)),
      Z::Zneg(__field0) => Z::Zneg(Clone::clone(__field0)),
    }
  }
}

pub enum positive {
  xI(Rc<positive>),
  xO(Rc<positive>),
  xH,
}

impl Clone for positive {
  fn clone(&self) -> Self {
    match self {
      positive::xI(__field0) => positive::xI(Clone::clone(__field0)),
      positive::xO(__field0) => positive::xO(Clone::clone(__field0)),
      positive::xH => positive::xH,
    }
  }
}

pub type uint = u64;

// Rocq: Darkness.darkness_implem.M48
pub fn M48() -> u64 {
  281474976710656u64
}

// Rocq: Darkness.darkness_implem.darkness
// Variant: uncurried
pub fn darkness() -> Rc<dyn Fn(u64, u64, Rc<Array<Rc<Array<u64>>>>) -> u64> {
  let v0: fn(u64, u64, Rc<Array<Rc<Array<u64>>>>) -> u64 = darkness_impl;
  let v1: Rc<dyn Fn(u64, u64, Rc<Array<Rc<Array<u64>>>>) -> u64> = Rc::new(v0);
  v1
}

// Rocq: Darkness.darkness_implem.darkness
pub fn darkness_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> u64>>> {
  let v0: fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> u64>> = darkness_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> u64>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul_1(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Corelib.BinNums.PosDef.Pos.compare_cont
// Variant: uncurried
pub fn compare_cont_1(r: std::cmp::Ordering, x: Rc<positive>, y: Rc<positive>) -> std::cmp::Ordering {
  compare_cont(r, x, y)
}

// Rocq: Corelib.BinNums.PosDef.Pos.compare_cont (local: compare_cont)
// Variant: uncurried, lifted
pub fn compare_cont(r: std::cmp::Ordering, x: Rc<positive>, y: Rc<positive>) -> std::cmp::Ordering {
  match &*x {
    positive::xI(p) => {
      let (v7, v8) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      std::mem::drop(v8);
      match v7 {
        positive::xI(v14) => {
          let v19 = Rc::clone(p);
          std::mem::drop(x);
          compare_cont(r, v19, v14)
        },
        positive::xO(v26) => {
          let v33 = Rc::clone(p);
          std::mem::drop(x);
          compare_cont(std::cmp::Ordering::Greater, v33, v26)
        },
        positive::xH => {
          std::mem::drop(x);
          std::cmp::Ordering::Greater
        },
      }
    },
    positive::xO(p) => {
      let (v49, v50) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      std::mem::drop(v50);
      match v49 {
        positive::xI(v56) => {
          let v63 = Rc::clone(p);
          std::mem::drop(x);
          compare_cont(std::cmp::Ordering::Less, v63, v56)
        },
        positive::xO(v70) => {
          let v75 = Rc::clone(p);
          std::mem::drop(x);
          compare_cont(r, v75, v70)
        },
        positive::xH => {
          std::mem::drop(x);
          std::cmp::Ordering::Greater
        },
      }
    },
    positive::xH => {
      let (v89, v90) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      std::mem::drop(v90);
      match v89 {
        positive::xI(v96) => {
          std::mem::drop(x);
          std::mem::drop(v96);
          std::cmp::Ordering::Less
        },
        positive::xO(v102) => {
          std::mem::drop(x);
          std::mem::drop(v102);
          std::cmp::Ordering::Less
        },
        positive::xH => {
          std::mem::drop(x);
          r
        },
      }
    },
  }
}

// Rocq: Corelib.Init.Datatypes.CompOpp
pub fn CompOpp(r: std::cmp::Ordering) -> std::cmp::Ordering {
  match r {
    std::cmp::Ordering::Equal => {
      std::cmp::Ordering::Equal
    },
    std::cmp::Ordering::Less => {
      std::cmp::Ordering::Greater
    },
    std::cmp::Ordering::Greater => {
      std::cmp::Ordering::Less
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.compare
// Variant: uncurried
pub fn compare(x: Rc<Z>, y: Rc<Z>) -> std::cmp::Ordering {
  let (v2, v3) = __rocq_reuse::reset(x, |__payload| Clone::clone(__payload));
  std::mem::drop(v3);
  match v2 {
    Z::Z0 => {
      let (v9, v10) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      std::mem::drop(v10);
      match v9 {
        Z::Z0 => {
          std::cmp::Ordering::Equal
        },
        Z::Zpos(v20) => {
          std::mem::drop(v20);
          std::cmp::Ordering::Less
        },
        Z::Zneg(v26) => {
          std::mem::drop(v26);
          std::cmp::Ordering::Greater
        },
      }
    },
    Z::Zpos(v35) => {
      let (v37, v38) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      std::mem::drop(v38);
      match v37 {
        Z::Z0 => {
          std::mem::drop(v35);
          std::cmp::Ordering::Greater
        },
        Z::Zpos(v48) => {
          compare_cont_1(std::cmp::Ordering::Equal, v35, v48)
        },
        Z::Zneg(v62) => {
          std::mem::drop(v35);
          std::mem::drop(v62);
          std::cmp::Ordering::Greater
        },
      }
    },
    Z::Zneg(v71) => {
      let (v73, v74) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      std::mem::drop(v74);
      match v73 {
        Z::Z0 => {
          std::mem::drop(v71);
          std::cmp::Ordering::Less
        },
        Z::Zpos(v84) => {
          std::mem::drop(v71);
          std::mem::drop(v84);
          std::cmp::Ordering::Less
        },
        Z::Zneg(v90) => {
          CompOpp(compare_cont_1(std::cmp::Ordering::Equal, v71, v90))
        },
      }
    },
  }
}

// Rocq: Corelib.BinNums.PosDef.Pos.succ
pub fn succ_1(x: Rc<positive>) -> Rc<positive> {
  succ(x)
}

// Rocq: Corelib.BinNums.PosDef.Pos.succ (local: succ)
// Variant: lifted
pub fn succ(x: Rc<positive>) -> Rc<positive> {
  let (v1, v2) = __rocq_reuse::reset(x, |__payload| Clone::clone(__payload));
  match v1 {
    positive::xI(v8) => {
      __rocq_reuse::rebuild(v2, positive::xO(succ(v8)))
    },
    positive::xO(v21) => {
      __rocq_reuse::rebuild(v2, positive::xI(v21))
    },
    positive::xH => {
      Rc::new(positive::xO(__rocq_reuse::rebuild(v2, positive::xH)))
    },
  }
}

// Rocq: Corelib.BinNums.PosDef.Pos.add
// Variant: uncurried
pub fn add_1(x: Rc<positive>, y: Rc<positive>) -> Rc<positive> {
  add(x, y)
}

// Rocq: Corelib.BinNums.PosDef.Pos.add (local: add)
// Variant: uncurried, lifted
pub fn add(x: Rc<positive>, y: Rc<positive>) -> Rc<positive> {
  match &*x {
    positive::xI(p) => {
      let (v6, v7) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      match v6 {
        positive::xI(v13) => {
          let v16 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v7, positive::xO(add_carry(v16, v13)))
        },
        positive::xO(v28) => {
          let v31 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v7, positive::xI(add(v31, v28)))
        },
        positive::xH => {
          let v44 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v7, positive::xO(succ_1(v44)))
        },
      }
    },
    positive::xO(p) => {
      let (v59, v60) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      match v59 {
        positive::xI(v66) => {
          let v69 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v60, positive::xI(add(v69, v66)))
        },
        positive::xO(v81) => {
          let v84 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v60, positive::xO(add(v84, v81)))
        },
        positive::xH => {
          let v96 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v60, positive::xI(v96))
        },
      }
    },
    positive::xH => {
      let (v106, v107) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      match v106 {
        positive::xI(v113) => {
          std::mem::drop(x);
          __rocq_reuse::rebuild(v107, positive::xO(succ_1(v113)))
        },
        positive::xO(v126) => {
          std::mem::drop(x);
          __rocq_reuse::rebuild(v107, positive::xI(v126))
        },
        positive::xH => {
          std::mem::drop(x);
          Rc::new(positive::xO(__rocq_reuse::rebuild(v107, positive::xH)))
        },
      }
    },
  }
}

// Rocq: Corelib.BinNums.PosDef.Pos.add (local: add_carry)
// Variant: uncurried, lifted
pub fn add_carry(x: Rc<positive>, y: Rc<positive>) -> Rc<positive> {
  match &*x {
    positive::xI(p) => {
      let (v6, v7) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      match v6 {
        positive::xI(v13) => {
          let v16 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v7, positive::xI(add_carry(v16, v13)))
        },
        positive::xO(v28) => {
          let v31 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v7, positive::xO(add_carry(v31, v28)))
        },
        positive::xH => {
          let v44 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v7, positive::xI(succ_1(v44)))
        },
      }
    },
    positive::xO(p) => {
      let (v59, v60) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      match v59 {
        positive::xI(v66) => {
          let v69 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v60, positive::xO(add_carry(v69, v66)))
        },
        positive::xO(v81) => {
          let v84 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v60, positive::xI(add(v84, v81)))
        },
        positive::xH => {
          let v97 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v60, positive::xO(succ_1(v97)))
        },
      }
    },
    positive::xH => {
      let (v110, v111) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      match v110 {
        positive::xI(v117) => {
          std::mem::drop(x);
          __rocq_reuse::rebuild(v111, positive::xI(succ_1(v117)))
        },
        positive::xO(v130) => {
          std::mem::drop(x);
          __rocq_reuse::rebuild(v111, positive::xO(succ_1(v130)))
        },
        positive::xH => {
          std::mem::drop(x);
          Rc::new(positive::xI(__rocq_reuse::rebuild(v111, positive::xH)))
        },
      }
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.double
pub fn double(x: Rc<Z>) -> Rc<Z> {
  let (v1, v2) = __rocq_reuse::reset(x, |__payload| Clone::clone(__payload));
  match v1 {
    Z::Z0 => {
      __rocq_reuse::rebuild(v2, Z::Z0)
    },
    Z::Zpos(v13) => {
      __rocq_reuse::rebuild(v2, Z::Zpos(Rc::new(positive::xO(v13))))
    },
    Z::Zneg(v27) => {
      __rocq_reuse::rebuild(v2, Z::Zneg(Rc::new(positive::xO(v27))))
    },
  }
}

// Rocq: Corelib.BinNums.PosDef.Pos.pred_double
pub fn pred_double_1(x: Rc<positive>) -> Rc<positive> {
  pred_double(x)
}

// Rocq: Corelib.BinNums.PosDef.Pos.pred_double (local: pred_double)
// Variant: lifted
pub fn pred_double(x: Rc<positive>) -> Rc<positive> {
  let (v1, v2) = __rocq_reuse::reset(x, |__payload| Clone::clone(__payload));
  match v1 {
    positive::xI(v8) => {
      Rc::new(positive::xI(__rocq_reuse::rebuild(v2, positive::xO(v8))))
    },
    positive::xO(v22) => {
      __rocq_reuse::rebuild(v2, positive::xI(pred_double(v22)))
    },
    positive::xH => {
      __rocq_reuse::rebuild(v2, positive::xH)
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.succ_double
pub fn succ_double(x: Rc<Z>) -> Rc<Z> {
  let (v1, v2) = __rocq_reuse::reset(x, |__payload| Clone::clone(__payload));
  match v1 {
    Z::Z0 => {
      __rocq_reuse::rebuild(v2, Z::Zpos(Rc::new(positive::xH)))
    },
    Z::Zpos(v18) => {
      __rocq_reuse::rebuild(v2, Z::Zpos(Rc::new(positive::xI(v18))))
    },
    Z::Zneg(v32) => {
      __rocq_reuse::rebuild(v2, Z::Zneg(pred_double_1(v32)))
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.pred_double
pub fn pred_double_2(x: Rc<Z>) -> Rc<Z> {
  let (v1, v2) = __rocq_reuse::reset(x, |__payload| Clone::clone(__payload));
  match v1 {
    Z::Z0 => {
      __rocq_reuse::rebuild(v2, Z::Zneg(Rc::new(positive::xH)))
    },
    Z::Zpos(v18) => {
      __rocq_reuse::rebuild(v2, Z::Zpos(pred_double_1(v18)))
    },
    Z::Zneg(v31) => {
      __rocq_reuse::rebuild(v2, Z::Zneg(Rc::new(positive::xI(v31))))
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.pos_sub
// Variant: uncurried
pub fn pos_sub_1(x: Rc<positive>, y: Rc<positive>) -> Rc<Z> {
  pos_sub(x, y)
}

// Rocq: Corelib.BinNums.IntDef.Z.pos_sub (local: pos_sub)
// Variant: uncurried, lifted
pub fn pos_sub(x: Rc<positive>, y: Rc<positive>) -> Rc<Z> {
  match &*x {
    positive::xI(p) => {
      let (v6, v7) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      match v6 {
        positive::xI(v13) => {
          std::mem::drop(v7);
          let v17 = Rc::clone(p);
          std::mem::drop(x);
          double(pos_sub(v17, v13))
        },
        positive::xO(v27) => {
          std::mem::drop(v7);
          let v31 = Rc::clone(p);
          std::mem::drop(x);
          succ_double(pos_sub(v31, v27))
        },
        positive::xH => {
          let v41 = Rc::clone(p);
          std::mem::drop(x);
          Rc::new(Z::Zpos(__rocq_reuse::rebuild(v7, positive::xO(v41))))
        },
      }
    },
    positive::xO(p) => {
      let (v58, v59) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      std::mem::drop(v59);
      match v58 {
        positive::xI(v65) => {
          let v69 = Rc::clone(p);
          std::mem::drop(x);
          pred_double_2(pos_sub(v69, v65))
        },
        positive::xO(v79) => {
          let v83 = Rc::clone(p);
          std::mem::drop(x);
          double(pos_sub(v83, v79))
        },
        positive::xH => {
          let v94 = Rc::clone(p);
          std::mem::drop(x);
          Rc::new(Z::Zpos(pred_double_1(v94)))
        },
      }
    },
    positive::xH => {
      let (v107, v108) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      match v107 {
        positive::xI(v114) => {
          std::mem::drop(x);
          Rc::new(Z::Zneg(__rocq_reuse::rebuild(v108, positive::xO(v114))))
        },
        positive::xO(v128) => {
          std::mem::drop(v108);
          std::mem::drop(x);
          Rc::new(Z::Zneg(pred_double_1(v128)))
        },
        positive::xH => {
          std::mem::drop(v108);
          std::mem::drop(x);
          Rc::new(Z::Z0)
        },
      }
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.add
// Variant: uncurried
pub fn add_2(x: Rc<Z>, y: Rc<Z>) -> Rc<Z> {
  match &*x {
    Z::Z0 => {
      std::mem::drop(x);
      y
    },
    Z::Zpos(x_) => {
      let (v8, v9) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      match v8 {
        Z::Z0 => {
          std::mem::drop(v9);
          x
        },
        Z::Zpos(v17) => {
          let v20 = Rc::clone(x_);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v9, Z::Zpos(add_1(v20, v17)))
        },
        Z::Zneg(v32) => {
          std::mem::drop(v9);
          let v35 = Rc::clone(x_);
          std::mem::drop(x);
          pos_sub_1(v35, v32)
        },
      }
    },
    Z::Zneg(x_) => {
      let (v47, v48) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      match v47 {
        Z::Z0 => {
          std::mem::drop(v48);
          x
        },
        Z::Zpos(v56) => {
          std::mem::drop(v48);
          let v61 = Rc::clone(x_);
          std::mem::drop(x);
          pos_sub_1(v56, v61)
        },
        Z::Zneg(v66) => {
          let v69 = Rc::clone(x_);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v48, Z::Zneg(add_1(v69, v66)))
        },
      }
    },
  }
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

// Rocq: Darkness.darkness_implem.bdec
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
pub fn add_3(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Darkness.darkness_implem.gloop
// Variant: uncurried
pub fn gloop_1<A: Clone + 'static>(C: u64, n: u64, f: Rc<dyn Fn(u64, u64, u64, A) -> A>, u: u64, i: u64, j: u64, a: A) -> A {
  gloop::<A>((), C, n, f, u, i, j, a, ())
}

// Rocq: Darkness.darkness_implem.gloop (local: gloop)
// Variant: uncurried, lifted
pub fn gloop<A: Clone + 'static>(_A_1: (), C: u64, n: u64, f: Rc<dyn Fn(u64, u64, u64, A) -> A>, u: u64, i: u64, j: u64, a: A, _H: ()) -> A {
  let v16 = ltb(u, n);
  match bdec(v16) {
    sumbool::left => {
      let v20: &Rc<dyn Fn(u64, u64, u64, A) -> A> = &f;
      let a_ = v20(u, i, j, a);
      let j1 = add_3(j, 1u64);
      let e = eqb(j1, C);
      let v45 = ();
      let v53 = add_3(u, 1u64);
      let v55 = match &e {
        true => {
          add_3(i, 1u64)
        },
        false => {
          i
        },
      };
      let v70 = match &e {
        true => {
          0u64
        },
        false => {
          j1
        },
      };
      gloop::<A>(v45, C, n, f, v53, v55, v70, a_, ())
    },
    sumbool::right => {
      std::mem::drop(f);
      a
    },
  }
}

// Rocq: Darkness.darkness_implem.grid_fold
// Variant: uncurried
pub fn grid_fold<A: Clone + 'static>(C: u64, n: u64, f: Rc<dyn Fn(u64, u64, u64, A) -> A>, a: A) -> A {
  gloop_1::<A>(C, n, f, 0u64, 0u64, 0u64, a)
}

// Rocq: Darkness.darkness_implem.flat
// Variant: uncurried
pub fn flat(xg: Rc<Array<Rc<Array<u64>>>>, C: u64, n: u64) -> Rc<Array<u64>> {
  let v6 = {
    move |u: u64, i: u64, j: u64, a: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let xg = &xg;
      let v14 = Rc::clone(xg);
      let v18 = rocq_array::get::<Rc<Array<u64>>>(&v14, i);
      std::mem::drop(v14);
      let v19 = &v18;
      let v22 = rocq_array::get::<u64>(&v19, j);
      std::mem::drop(v18);
      rocq_array::set::<u64>(a, u, v22)
    }
  };
  let v32: Rc<dyn Fn(u64, u64, u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v6);
  let v40 = rocq_array::make::<u64>(n, 0u64);
  grid_fold::<Rc<Array<u64>>>(C, n, v32, v40)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Darkness.darkness_implem.absdiff
// Variant: uncurried
pub fn absdiff(a: u64, b: u64) -> u64 {
  match ltb(a, b) {
    true => {
      sub(b, a)
    },
    false => {
      sub(a, b)
    },
  }
}

// Rocq: Darkness.darkness_implem.denom
// Variant: uncurried
pub fn denom(hh: u64, i: u64, j: u64, i_: u64, j_: u64) -> u64 {
  let di = absdiff(i, i_);
  let dj = absdiff(j, j_);
  let v36 = add_3(mul_1(di, di), mul_1(dj, dj));
  add_3(v36, hh)
}

// Rocq: Darkness.darkness_implem.lo_sum
// Variant: borrowed, uncurried
pub fn lo_sum(s: &Rc<Array<u64>>, C: u64, n: u64, hh: u64, i: u64, j: u64) -> u64 {
  let C_1 = C;
  let n_1 = n;
  let v14 = Rc::clone(s);
  let v21 = {
    move |u: u64, i_: u64, j_: u64, acc: u64| -> u64 {
      let s = &v14;
      let hh = &hh;
      let i = &i;
      let j = &j;
      let v45 = mul_1(__rocq_global_789, rocq_array::get::<u64>(&s, u));
      let v48 = Clone::clone(hh);
      let v50 = Clone::clone(i);
      let v52 = Clone::clone(j);
      add_3(acc, div(v45, denom(v48, v50, v52, i_, j_)))
    }
  };
  let v70: Rc<dyn Fn(u64, u64, u64, u64) -> u64> = Rc::new(v21);
  grid_fold::<u64>(C_1, n_1, v70, 0u64)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Corelib.BinNums.PosDef.Pos.mul
// Variant: uncurried
pub fn mul_2(x: Rc<positive>, y: Rc<positive>) -> Rc<positive> {
  mul(x, y)
}

// Rocq: Corelib.BinNums.PosDef.Pos.mul (local: mul)
// Variant: uncurried, lifted
pub fn mul(x: Rc<positive>, y: Rc<positive>) -> Rc<positive> {
  let (v2, v3) = __rocq_reuse::reset(x, |__payload| Clone::clone(__payload));
  match v2 {
    positive::xI(v9) => {
      let v17 = Rc::clone(&y);
      add_1(y, __rocq_reuse::rebuild(v3, positive::xO(mul(v9, v17))))
    },
    positive::xO(v31) => {
      __rocq_reuse::rebuild(v3, positive::xO(mul(v31, y)))
    },
    positive::xH => {
      std::mem::drop(v3);
      y
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.mul
// Variant: uncurried
pub fn mul_3(x: Rc<Z>, y: Rc<Z>) -> Rc<Z> {
  let (v2, v3) = __rocq_reuse::reset(x, |__payload| Clone::clone(__payload));
  match v2 {
    Z::Z0 => {
      std::mem::drop(y);
      __rocq_reuse::rebuild(v3, Z::Z0)
    },
    Z::Zpos(v14) => {
      std::mem::drop(v3);
      let (v16, v17) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      match v16 {
        Z::Z0 => {
          std::mem::drop(v14);
          __rocq_reuse::rebuild(v17, Z::Z0)
        },
        Z::Zpos(v28) => {
          __rocq_reuse::rebuild(v17, Z::Zpos(mul_2(v14, v28)))
        },
        Z::Zneg(v43) => {
          __rocq_reuse::rebuild(v17, Z::Zneg(mul_2(v14, v43)))
        },
      }
    },
    Z::Zneg(v61) => {
      std::mem::drop(v3);
      let (v63, v64) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      match v63 {
        Z::Z0 => {
          std::mem::drop(v61);
          __rocq_reuse::rebuild(v64, Z::Z0)
        },
        Z::Zpos(v75) => {
          __rocq_reuse::rebuild(v64, Z::Zneg(mul_2(v61, v75)))
        },
        Z::Zneg(v90) => {
          __rocq_reuse::rebuild(v64, Z::Zpos(mul_2(v61, v90)))
        },
      }
    },
  }
}

// Rocq: Darkness.darkness_implem.zofint_aux
pub fn zofint_aux_1(x: u64) -> Rc<Z> {
  zofint_aux(x, ())
}

// Rocq: Darkness.darkness_implem.zofint_aux (local: zofint_aux)
// Variant: uncurried, lifted
pub fn zofint_aux(x: u64, _H: ()) -> Rc<Z> {
  let v11 = eqb(x, 0u64);
  match bdec(v11) {
    sumbool::left => {
      Rc::new(Z::Z0)
    },
    sumbool::right => {
      let r = zofint_aux(div(x, 2u64), ());
      let v44 = mod_(x, 2u64);
      match eqb(v44, 0u64) {
        true => {
          let v56 = Rc::new(positive::xH);
          let v61 = Rc::new(positive::xO(v56));
          mul_3(Rc::new(Z::Zpos(v61)), r)
        },
        false => {
          let v78 = Rc::new(positive::xH);
          let v83 = Rc::new(positive::xO(v78));
          let v93 = mul_3(Rc::new(Z::Zpos(v83)), r);
          let v96 = Rc::new(positive::xH);
          add_2(v93, Rc::new(Z::Zpos(v96)))
        },
      }
    },
  }
}

// Rocq: Darkness.darkness_implem.zofint
pub fn zofint(x: u64) -> Rc<Z> {
  zofint_aux_1(x)
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let v3 = Clone::clone((&(&p).1));
  std::mem::drop(p);
  v3
}

// Rocq: Darkness.darkness_implem.exact_sum
// Variant: borrowed, uncurried
pub fn exact_sum(s: &Rc<Array<u64>>, C: u64, n: u64, hh: u64, i: u64, j: u64) -> (Rc<Z>, Rc<Z>) {
  let C_1 = C;
  let n_1 = n;
  let v20 = Rc::clone(s);
  let v21 = {
    move |u: u64, i_: u64, j_: u64, pq: (Rc<Z>, Rc<Z>)| -> (Rc<Z>, Rc<Z>) {
      let hh = &hh;
      let i = &i;
      let j = &j;
      let s = &v20;
      let d = zofint(denom(Clone::clone(hh), Clone::clone(i), Clone::clone(j), i_, j_));
      let v54 = rocq_array::get::<u64>(&s, u);
      let sv = zofint(v54);
      let v61 = Clone::clone(&pq);
      let v64 = fst::<Rc<Z>, Rc<Z>>(v61);
      let v68 = Rc::clone(&d);
      let v69 = mul_3(v64, v68);
      let v73 = Clone::clone(&pq);
      (add_2(v69, mul_3(sv, snd::<Rc<Z>, Rc<Z>>(v73))), mul_3(snd::<Rc<Z>, Rc<Z>>(pq), d))
    }
  };
  let v104: Rc<dyn Fn(u64, u64, u64, (Rc<Z>, Rc<Z>)) -> (Rc<Z>, Rc<Z>)> = Rc::new(v21);
  let v108 = Rc::new(Z::Z0);
  let v111 = Rc::new(positive::xH);
  grid_fold::<(Rc<Z>, Rc<Z>)>(C_1, n_1, v104, (v108, Rc::new(Z::Zpos(v111))))
}

// Rocq: Corelib.BinNums.IntDef.Z.leb
// Variant: uncurried
pub fn leb_1(x: Rc<Z>, y: Rc<Z>) -> bool {
  match compare(x, y) {
    std::cmp::Ordering::Equal => {
      true
    },
    std::cmp::Ordering::Less => {
      true
    },
    std::cmp::Ordering::Greater => {
      false
    },
  }
}

// Rocq: Darkness.darkness_implem.lit_cell
// Variant: borrowed, uncurried
pub fn lit_cell(s: &Rc<Array<u64>>, C: u64, n: u64, b: u64, hh: u64, i: u64, j: u64) -> bool {
  let C_1 = C;
  let n_1 = n;
  let b_1 = b;
  let hh_1 = hh;
  let i_1 = i;
  let j_1 = j;
  let lo = lo_sum(s, C_1, n_1, hh_1, i_1, j_1);
  let mb = mul_1(__rocq_global_789, b_1);
  match leb(mb, lo) {
    true => {
      true
    },
    false => {
      let v52 = add_3(lo, n_1);
      match ltb(v52, mb) {
        true => {
          false
        },
        false => {
          let pq = exact_sum(s, C_1, n_1, hh_1, i_1, j_1);
          let v81 = zofint(b_1);
          let v84 = Clone::clone(&pq);
          leb_1(mul_3(v81, snd::<Rc<Z>, Rc<Z>>(v84)), fst::<Rc<Z>, Rc<Z>>(pq))
        },
      }
    },
  }
}

// Rocq: Darkness.darkness_implem.lit_arr
// Variant: uncurried
pub fn lit_arr(s: Rc<Array<u64>>, C: u64, n: u64, b: u64, hh: u64) -> Rc<Array<bool>> {
  let v16 = {
    let __anf_capture_19 = C;
    let __anf_capture_21 = n;
    move |u: u64, i: u64, j: u64, a: Rc<Array<bool>>| -> Rc<Array<bool>> {
      let v45 = lit_cell(&s, Clone::clone(&__anf_capture_19), Clone::clone(&__anf_capture_21), Clone::clone(&b), Clone::clone(&hh), i, j);
      rocq_array::set::<bool>(a, u, v45)
    }
  };
  let v55: Rc<dyn Fn(u64, u64, u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new(v16);
  let v63 = rocq_array::make::<bool>(n, false);
  grid_fold::<Rc<Array<bool>>>(C, n, v55, v63)
}

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  match b1 {
    true => {
      b2
    },
    false => {
      false
    },
  }
}

// Rocq: Darkness.darkness_implem.capf
// Variant: uncurried
pub fn capf(x: bool, y: bool) -> u64 {
  match andb(x, y) {
    true => {
      43u64
    },
    false => {
      11u64
    },
  }
}

// Rocq: Darkness.darkness_implem.init_res
// Variant: uncurried
pub fn init_res(lt: Rc<Array<bool>>, C: u64, n: u64) -> Rc<Array<u64>> {
  let v8 = {
    let __anf_capture_9 = C;
    move |u: u64, _i: u64, _j: u64, r: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let C = &__anf_capture_9;
      let lt = &lt;
      let v20 = rocq_array::get::<bool>(&lt, u);
      let v29 = add_3(u, 1u64);
      let c1 = capf(v20, rocq_array::get::<bool>(&lt, v29));
      let v40 = rocq_array::get::<bool>(&lt, u);
      let v47 = add_3(u, Clone::clone(C));
      let v49 = rocq_array::get::<bool>(&lt, v47);
      let c2 = capf(v40, v49);
      let v69 = rocq_array::set::<u64>(r, mul_1(2u64, u), c1);
      rocq_array::set::<u64>(v69, add_3(mul_1(2u64, u), 1u64), c2)
    }
  };
  let v95: Rc<dyn Fn(u64, u64, u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v8);
  let v111 = rocq_array::make::<u64>(mul_1(2u64, n), 0u64);
  grid_fold::<Rc<Array<u64>>>(C, n, v95, v111)
}

// Rocq: Darkness.darkness_implem.bt
pub fn bt_owned(b: Rc<bst>) -> u64 {
  let v3 = Clone::clone((&(&**&b).bt));
  std::mem::drop(b);
  v3
}

// Rocq: Darkness.darkness_implem.bt
// Variant: borrowed
pub fn bt(b: &Rc<bst>) -> u64 {
  let v1 = b;
  Clone::clone((&(&**v1).bt))
}

// Rocq: Darkness.darkness_implem.bq
pub fn bq(b: Rc<bst>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&b).bq));
  std::mem::drop(b);
  v3
}

// Rocq: Darkness.darkness_implem.bd
pub fn bd(b: Rc<bst>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&b).bd));
  std::mem::drop(b);
  v3
}

// Rocq: Darkness.darkness_implem.nbr
// Variant: uncurried
pub fn nbr(C: u64, p: u64, d: u64) -> u64 {
  match eqb(d, 0u64) {
    true => {
      add_3(p, 1u64)
    },
    false => {
      match eqb(d, 1u64) {
        true => {
          sub(p, 1u64)
        },
        false => {
          match eqb(d, 2u64) {
            true => {
              add_3(p, C)
            },
            false => {
              sub(p, C)
            },
          }
        },
      }
    },
  }
}

// Rocq: Darkness.darkness_implem.slot
// Variant: uncurried
pub fn slot(C: u64, p: u64, d: u64) -> u64 {
  match eqb(d, 0u64) {
    true => {
      mul_1(2u64, p)
    },
    false => {
      match eqb(d, 1u64) {
        true => {
          mul_1(2u64, sub(p, 1u64))
        },
        false => {
          match eqb(d, 2u64) {
            true => {
              add_3(mul_1(2u64, p), 1u64)
            },
            false => {
              add_3(mul_1(2u64, sub(p, C)), 1u64)
            },
          }
        },
      }
    },
  }
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

// Rocq: Darkness.darkness_implem.fwd
pub fn fwd(d: u64) -> bool {
  orb(eqb(d, 0u64), eqb(d, 2u64))
}

// Rocq: Darkness.darkness_implem.resid
// Variant: uncurried
pub fn resid(lt: Rc<Array<bool>>, res: Rc<Array<u64>>, C: u64, p: u64, d: u64) -> u64 {
  let k = slot(C, p, d);
  match fwd(d) {
    true => {
      std::mem::drop(lt);
      let v18 = &res;
      let v21 = rocq_array::get::<u64>(&v18, k);
      std::mem::drop(res);
      v21
    },
    false => {
      let v27 = 2u64;
      let v29 = &lt;
      let v32 = rocq_array::get::<bool>(&v29, p);
      let v40 = nbr(C, p, d);
      let v41 = &lt;
      let v44 = rocq_array::get::<bool>(&v41, v40);
      std::mem::drop(lt);
      let v54 = mul_1(v27, capf(v32, v44));
      let v55 = &res;
      let v58 = rocq_array::get::<u64>(&v55, k);
      std::mem::drop(res);
      sub(v54, v58)
    },
  }
}

// Rocq: Darkness.darkness_implem.bp
pub fn bp(b: Rc<bst>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&b).bp));
  std::mem::drop(b);
  v3
}

// Rocq: Darkness.darkness_implem.visit
// Variant: uncurried
pub fn visit(lt: Rc<Array<bool>>, res: Rc<Array<u64>>, C: u64, st: Rc<bst>, v: u64, dv: u64, d: u64, ok: bool) -> Rc<bst> {
  match ok {
    true => {
      let w = nbr(C, v, d);
      let v31 = resid(lt, res, C, v, d);
      match ltb(0u64, v31) {
        true => {
          let v42 = Rc::clone(&st);
          let v43 = bd(v42);
          let v44 = &v43;
          let v47 = rocq_array::get::<u64>(&v44, w);
          match eqb(v47, 0u64) {
            true => {
              std::mem::drop(v43);
              let v59 = Rc::clone(&st);
              let v60 = bd(v59);
              let v75 = rocq_array::set::<u64>(v60, w, add_3(dv, 1u64));
              let v79 = Rc::clone(&st);
              let v81 = bp(v79);
              let v87 = rocq_array::set::<u64>(v81, w, d);
              let v91 = Rc::clone(&st);
              let v92 = bq(v91);
              let v96 = bt(&st);
              let v103 = rocq_array::set::<u64>(v92, v96, w);
              Rc::new(bst { bd: v75, bp: v87, bq: v103, bt: add_3(bt_owned(st), 1u64) })
            },
            false => {
              std::mem::drop(v43);
              st
            },
          }
        },
        false => {
          st
        },
      }
    },
    false => {
      std::mem::drop(lt);
      std::mem::drop(res);
      st
    },
  }
}

// Rocq: Darkness.darkness_implem.bfs_loop
// Variant: uncurried
pub fn bfs_loop_1(lt: Rc<Array<bool>>, res: Rc<Array<u64>>, C: u64, n: u64, head: u64, st: Rc<bst>) -> Rc<bst> {
  bfs_loop(lt, res, C, n, head, st, ())
}

// Rocq: Darkness.darkness_implem.bfs_loop (local: bfs_loop)
// Variant: uncurried, lifted
pub fn bfs_loop(lt: Rc<Array<bool>>, res: Rc<Array<u64>>, C: u64, n: u64, head: u64, st: Rc<bst>, _H: ()) -> Rc<bst> {
  let v14 = ltb(head, n);
  match bdec(v14) {
    sumbool::left => {
      let v22 = bt(&st);
      match ltb(head, v22) {
        true => {
          let v32 = Rc::clone(&st);
          let v33 = bq(v32);
          let v34 = &v33;
          let v = rocq_array::get::<u64>(&v34, head);
          std::mem::drop(v33);
          let v41 = Rc::clone(&st);
          let v42 = bd(v41);
          let v43 = &v42;
          let dv = rocq_array::get::<u64>(&v43, v);
          std::mem::drop(v42);
          let j = mod_(v, C);
          let v69 = ltb(add_3(j, 1u64), C);
          let v72 = Rc::clone(&lt);
          let v75 = Rc::clone(&res);
          let st1 = visit(v72, v75, C, st, v, dv, 0u64, v69);
          let v99 = ltb(0u64, j);
          let v102 = Rc::clone(&lt);
          let v105 = Rc::clone(&res);
          let st2 = visit(v102, v105, C, st1, v, dv, 1u64, v99);
          let v133 = ltb(add_3(v, C), n);
          let v136 = Rc::clone(&lt);
          let v139 = Rc::clone(&res);
          let st3 = visit(v136, v139, C, st2, v, dv, 2u64, v133);
          let v161 = leb(C, v);
          let v164 = Rc::clone(&lt);
          let v167 = Rc::clone(&res);
          let st4 = visit(v164, v167, C, st3, v, dv, 3u64, v161);
          bfs_loop(lt, res, C, n, add_3(head, 1u64), st4, ())
        },
        false => {
          std::mem::drop(lt);
          std::mem::drop(res);
          st
        },
      }
    },
    sumbool::right => {
      std::mem::drop(lt);
      std::mem::drop(res);
      st
    },
  }
}

// Rocq: Darkness.darkness_implem.root_step
// Variant: uncurried
pub fn root_step(lt: Rc<Array<bool>>, u: u64, _i: u64, _j: u64, st: Rc<bst>) -> Rc<bst> {
  let v5 = &lt;
  let v8 = rocq_array::get::<bool>(&v5, u);
  match v8 {
    true => {
      std::mem::drop(lt);
      st
    },
    false => {
      std::mem::drop(lt);
      let v15 = Rc::clone(&st);
      let v16 = bd(v15);
      let v25 = rocq_array::set::<u64>(v16, u, 1u64);
      let v29 = Rc::clone(&st);
      let v30 = bp(v29);
      let v39 = rocq_array::set::<u64>(v30, u, 4u64);
      let v43 = Rc::clone(&st);
      let v44 = bq(v43);
      let v48 = bt(&st);
      let v55 = rocq_array::set::<u64>(v44, v48, u);
      Rc::new(bst { bd: v25, bp: v39, bq: v55, bt: add_3(bt_owned(st), 1u64) })
    },
  }
}

// Rocq: Darkness.darkness_implem.roots
// Variant: uncurried
pub fn roots(lt: Rc<Array<bool>>, C: u64, n: u64) -> Rc<bst> {
  let v6 = {
    move |v9: u64, v10: u64, v11: u64, v12: Rc<bst>| -> Rc<bst> {
      let v15 = Rc::clone(&lt);
      root_step(v15, v9, v10, v11, v12)
    }
  };
  let v27: Rc<dyn Fn(u64, u64, u64, Rc<bst>) -> Rc<bst>> = Rc::new(v6);
  let v35 = rocq_array::make::<u64>(n, 0u64);
  let v42 = rocq_array::make::<u64>(n, 0u64);
  let v49 = rocq_array::make::<u64>(n, 0u64);
  grid_fold::<Rc<bst>>(C, n, v27, Rc::new(bst { bd: v35, bp: v42, bq: v49, bt: 0u64 }))
}

// Rocq: Darkness.darkness_implem.bfs
// Variant: uncurried
pub fn bfs(lt: Rc<Array<bool>>, res: Rc<Array<u64>>, C: u64, n: u64) -> Rc<bst> {
  let v10 = Rc::clone(&lt);
  let v15 = roots(v10, C, n);
  bfs_loop_1(lt, res, C, n, 0u64, v15)
}

// Rocq: Darkness.darkness_implem.is_border
// Variant: uncurried
pub fn is_border(R: u64, C: u64, i: u64, j: u64) -> bool {
  let v33 = orb(eqb(i, 0u64), eqb(i, sub(R, 1u64)));
  let v46 = orb(v33, eqb(j, 0u64));
  orb(v46, eqb(j, sub(C, 1u64)))
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  match b {
    true => {
      false
    },
    false => {
      true
    },
  }
}

// Rocq: Darkness.darkness_implem.fb_step
// Variant: borrowed, uncurried
pub fn fb_step(dist: &Rc<Array<u64>>, R: u64, C: u64, n: u64, u: u64, i: u64, j: u64, acc: u64) -> u64 {
  let R_1 = R;
  let C_1 = C;
  let n_1 = n;
  let u_1 = u;
  let i_1 = i;
  let j_1 = j;
  let acc_1 = acc;
  let v26 = is_border(R_1, C_1, i_1, j_1);
  let v29 = dist;
  let v47 = andb(v26, negb(eqb(rocq_array::get::<u64>(&v29, u_1), 0u64)));
  let v54 = eqb(acc_1, n_1);
  let v56 = dist;
  let v59 = rocq_array::get::<u64>(&v56, u_1);
  let v60 = dist;
  let v73 = orb(v54, ltb(v59, rocq_array::get::<u64>(&v60, acc_1)));
  match andb(v47, v73) {
    true => {
      u_1
    },
    false => {
      acc_1
    },
  }
}

// Rocq: Darkness.darkness_implem.find_border
// Variant: uncurried
pub fn find_border(dist: Rc<Array<u64>>, R: u64, C: u64, n: u64) -> u64 {
  let v13 = {
    let __anf_capture_18 = C;
    let __anf_capture_20 = n;
    move |v22: u64, v23: u64, v24: u64, v25: u64| -> u64 {
      let dist = &dist;
      let v27 = Clone::clone(&R);
      let v29 = Clone::clone(&__anf_capture_18);
      let v31 = Clone::clone(&__anf_capture_20);
      fb_step(dist, v27, v29, v31, v22, v23, v24, v25)
    }
  };
  let v45: Rc<dyn Fn(u64, u64, u64, u64) -> u64> = Rc::new(v13);
  grid_fold::<u64>(C, n, v45, n)
}

// Rocq: Darkness.darkness_implem.opp
pub fn opp(d: u64) -> u64 {
  match eqb(d, 0u64) {
    true => {
      1u64
    },
    false => {
      match eqb(d, 1u64) {
        true => {
          0u64
        },
        false => {
          match eqb(d, 2u64) {
            true => {
              3u64
            },
            false => {
              2u64
            },
          }
        },
      }
    },
  }
}

// Rocq: Darkness.darkness_implem.tmin
// Variant: uncurried
pub fn tmin_1(lt: Rc<Array<bool>>, res: Rc<Array<u64>>, C: u64, par: Rc<Array<u64>>, dist: Rc<Array<u64>>, v: u64, dl: u64) -> u64 {
  tmin(lt, res, C, par, dist, v, dl, ())
}

// Rocq: Darkness.darkness_implem.tmin (local: tmin)
// Variant: uncurried, lifted
pub fn tmin(lt: Rc<Array<bool>>, res: Rc<Array<u64>>, C: u64, par: Rc<Array<u64>>, dist: Rc<Array<u64>>, v: u64, dl: u64, _H: ()) -> u64 {
  let v8 = &par;
  let d = rocq_array::get::<u64>(&v8, v);
  match ltb(d, 4u64) {
    true => {
      let p = nbr(C, v, opp(d));
      let v35 = &dist;
      let v38 = rocq_array::get::<u64>(&v35, p);
      let v39 = &dist;
      let v42 = rocq_array::get::<u64>(&v39, v);
      let v48 = ltb(v38, v42);
      match bdec(v48) {
        sumbool::left => {
          let v55 = Rc::clone(&lt);
          let v58 = Rc::clone(&res);
          let r = resid(v55, v58, C, p, d);
          let v72 = match ltb(r, dl) {
            true => {
              r
            },
            false => {
              dl
            },
          };
          tmin(lt, res, C, par, dist, p, v72, ())
        },
        sumbool::right => {
          std::mem::drop(lt);
          std::mem::drop(res);
          std::mem::drop(dist);
          std::mem::drop(par);
          dl
        },
      }
    },
    false => {
      std::mem::drop(lt);
      std::mem::drop(res);
      std::mem::drop(dist);
      std::mem::drop(par);
      dl
    },
  }
}

// Rocq: Darkness.darkness_implem.aug
// Variant: uncurried
pub fn aug(res: Rc<Array<u64>>, C: u64, p: u64, d: u64, dl: u64) -> Rc<Array<u64>> {
  let k = slot(C, p, d);
  match fwd(d) {
    true => {
      let v19 = &res;
      let v23 = rocq_array::get::<u64>(&v19, k);
      rocq_array::set::<u64>(res, k, sub(v23, dl))
    },
    false => {
      let v38 = &res;
      let v42 = rocq_array::get::<u64>(&v38, k);
      rocq_array::set::<u64>(res, k, add_3(v42, dl))
    },
  }
}

// Rocq: Darkness.darkness_implem.tapp
// Variant: uncurried
pub fn tapp_1(C: u64, par: Rc<Array<u64>>, dist: Rc<Array<u64>>, dl: u64, v: u64, res: Rc<Array<u64>>) -> Rc<Array<u64>> {
  tapp(C, par, dist, dl, v, res, ())
}

// Rocq: Darkness.darkness_implem.tapp (local: tapp)
// Variant: uncurried, lifted
pub fn tapp(C: u64, par: Rc<Array<u64>>, dist: Rc<Array<u64>>, dl: u64, v: u64, res: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v7 = &par;
  let d = rocq_array::get::<u64>(&v7, v);
  match ltb(d, 4u64) {
    true => {
      let p = nbr(C, v, opp(d));
      let v34 = &dist;
      let v37 = rocq_array::get::<u64>(&v34, p);
      let v38 = &dist;
      let v41 = rocq_array::get::<u64>(&v38, v);
      let v47 = ltb(v37, v41);
      match bdec(v47) {
        sumbool::left => {
          let v62 = aug(res, C, p, d, dl);
          tapp(C, par, dist, dl, p, v62, ())
        },
        sumbool::right => {
          std::mem::drop(dist);
          std::mem::drop(par);
          res
        },
      }
    },
    false => {
      std::mem::drop(dist);
      std::mem::drop(par);
      res
    },
  }
}

// Rocq: Darkness.darkness_implem.flow_loop
// Variant: uncurried
pub fn flow_loop_1(lt: Rc<Array<bool>>, R: u64, C: u64, n: u64, B: u64, res: Rc<Array<u64>>, F: u64) -> u64 {
  flow_loop(lt, R, C, n, B, res, F, ())
}

// Rocq: Darkness.darkness_implem.flow_loop (local: flow_loop)
// Variant: uncurried, lifted
pub fn flow_loop(lt: Rc<Array<bool>>, R: u64, C: u64, n: u64, B: u64, res: Rc<Array<u64>>, F: u64, _H: ()) -> u64 {
  let v11 = Rc::clone(&lt);
  let v14 = Rc::clone(&res);
  let st = bfs(v11, v14, C, n);
  let v24 = Rc::clone(&st);
  let v26 = bd(v24);
  let w = find_border(v26, R, C, n);
  match eqb(w, n) {
    true => {
      std::mem::drop(st);
      std::mem::drop(lt);
      std::mem::drop(res);
      F
    },
    false => {
      let v48 = Rc::clone(&st);
      let v49 = bp(v48);
      let v53 = Rc::clone(&st);
      let v54 = bd(v53);
      let v59 = Rc::clone(&lt);
      let v62 = Rc::clone(&res);
      let dl = tmin_1(v59, v62, C, v49, v54, w, 1000u64);
      let v78 = Rc::clone(&st);
      let v79 = bp(v78);
      let v83 = bd(st);
      let res_ = tapp_1(C, v79, v83, dl, w, res);
      let F_ = add_3(F, dl);
      let v122 = andb(ltb(F, F_), leb(F_, B));
      match bdec(v122) {
        sumbool::left => {
          flow_loop(lt, R, C, n, B, res_, F_, ())
        },
        sumbool::right => {
          std::mem::drop(res_);
          std::mem::drop(lt);
          F
        },
      }
    },
  }
}

// Rocq: Darkness.darkness_implem.darkness_impl
// Variant: uncurried
pub fn darkness_impl(xb: u64, xh: u64, xg: Rc<Array<Rc<Array<u64>>>>) -> u64 {
  let v3 = &xg;
  let R = rocq_array::length::<Rc<Array<u64>>>(&v3);
  let v6 = 0u64;
  let v9 = Rc::clone(&xg);
  let v13 = rocq_array::get::<Rc<Array<u64>>>(&v9, v6);
  std::mem::drop(v9);
  let v14 = &v13;
  let C = rocq_array::length::<u64>(&v14);
  std::mem::drop(v13);
  let n = mul_1(R, C);
  let s = flat(xg, C, n);
  let lt = lit_arr(s, C, n, xb, mul_1(xh, xh));
  let v51 = Rc::clone(&lt);
  let res = init_res(v51, C, n);
  let B = mul_1(86u64, n);
  flow_loop_1(lt, R, C, n, B, res, 0u64)
}

// Rocq: Darkness.darkness_implem.darkness_impl
pub fn darkness_impl_curried(xb: u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> u64>> {
  let v3 = {
    move |xh: u64| -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> u64> {
      let xb = &xb;
      let v8 = Clone::clone(xb);
      let v11 = {
        move |xg: Rc<Array<Rc<Array<u64>>>>| -> u64 {
          let v19 = Clone::clone(&v8);
          let v21 = Clone::clone(&xh);
          darkness_impl(v19, v21, xg)
        }
      };
      let v27: Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> u64> = Rc::new(v11);
      v27
    }
  };
  let v31: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> u64>> = Rc::new(v3);
  v31
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

pub fn run() -> Rc<dyn Fn(u64, u64, Rc<Array<Rc<Array<u64>>>>) -> u64> {
  let v0: Rc<dyn Fn(u64, u64, Rc<Array<Rc<Array<u64>>>>) -> u64> = __rocq_global_2090.with(Clone::clone);
  v0
}
const __rocq_global_789: u64 = 281474976710656u64;
std::thread_local! { static __rocq_global_2090: Rc<dyn Fn(u64, u64, Rc<Array<Rc<Array<u64>>>>) -> u64> = darkness(); }
std::thread_local! { static __rocq_global_2093: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> u64>>> = darkness_curried(); }