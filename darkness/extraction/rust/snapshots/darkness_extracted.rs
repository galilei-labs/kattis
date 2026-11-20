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
          let p_clone = Rc::clone(p);
          std::mem::drop(x);
          compare_cont(r, p_clone, v14)
        },
        positive::xO(v26) => {
          let p_clone_1 = Rc::clone(p);
          std::mem::drop(x);
          compare_cont(std::cmp::Ordering::Greater, p_clone_1, v26)
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
          let p_clone_2 = Rc::clone(p);
          std::mem::drop(x);
          compare_cont(std::cmp::Ordering::Less, p_clone_2, v56)
        },
        positive::xO(v70) => {
          let p_clone_3 = Rc::clone(p);
          std::mem::drop(x);
          compare_cont(r, p_clone_3, v70)
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
          let p_clone = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v7, positive::xO(add_carry(p_clone, v13)))
        },
        positive::xO(v28) => {
          let p_clone_1 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v7, positive::xI(add(p_clone_1, v28)))
        },
        positive::xH => {
          let p_clone_2 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v7, positive::xO(succ_1(p_clone_2)))
        },
      }
    },
    positive::xO(p) => {
      let (v59, v60) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      match v59 {
        positive::xI(v66) => {
          let p_clone_3 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v60, positive::xI(add(p_clone_3, v66)))
        },
        positive::xO(v81) => {
          let p_clone_4 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v60, positive::xO(add(p_clone_4, v81)))
        },
        positive::xH => {
          let p_clone_5 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v60, positive::xI(p_clone_5))
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
          let p_clone = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v7, positive::xI(add_carry(p_clone, v13)))
        },
        positive::xO(v28) => {
          let p_clone_1 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v7, positive::xO(add_carry(p_clone_1, v28)))
        },
        positive::xH => {
          let p_clone_2 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v7, positive::xI(succ_1(p_clone_2)))
        },
      }
    },
    positive::xO(p) => {
      let (v59, v60) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      match v59 {
        positive::xI(v66) => {
          let p_clone_3 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v60, positive::xO(add_carry(p_clone_3, v66)))
        },
        positive::xO(v81) => {
          let p_clone_4 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v60, positive::xI(add(p_clone_4, v81)))
        },
        positive::xH => {
          let p_clone_5 = Rc::clone(p);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v60, positive::xO(succ_1(p_clone_5)))
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
          let p_clone = Rc::clone(p);
          std::mem::drop(x);
          double(pos_sub(p_clone, v13))
        },
        positive::xO(v27) => {
          std::mem::drop(v7);
          let p_clone_1 = Rc::clone(p);
          std::mem::drop(x);
          succ_double(pos_sub(p_clone_1, v27))
        },
        positive::xH => {
          let p_clone_2 = Rc::clone(p);
          std::mem::drop(x);
          Rc::new(Z::Zpos(__rocq_reuse::rebuild(v7, positive::xO(p_clone_2))))
        },
      }
    },
    positive::xO(p) => {
      let (v58, v59) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      std::mem::drop(v59);
      match v58 {
        positive::xI(v65) => {
          let p_clone_3 = Rc::clone(p);
          std::mem::drop(x);
          pred_double_2(pos_sub(p_clone_3, v65))
        },
        positive::xO(v79) => {
          let p_clone_4 = Rc::clone(p);
          std::mem::drop(x);
          double(pos_sub(p_clone_4, v79))
        },
        positive::xH => {
          let p_clone_5 = Rc::clone(p);
          std::mem::drop(x);
          Rc::new(Z::Zpos(pred_double_1(p_clone_5)))
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
          let x__clone = Rc::clone(x_);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v9, Z::Zpos(add_1(x__clone, v17)))
        },
        Z::Zneg(v32) => {
          std::mem::drop(v9);
          let x__clone_1 = Rc::clone(x_);
          std::mem::drop(x);
          pos_sub_1(x__clone_1, v32)
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
          let x__clone_2 = Rc::clone(x_);
          std::mem::drop(x);
          pos_sub_1(v56, x__clone_2)
        },
        Z::Zneg(v66) => {
          let x__clone_3 = Rc::clone(x_);
          std::mem::drop(x);
          __rocq_reuse::rebuild(v48, Z::Zneg(add_1(x__clone_3, v66)))
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
  if b {
    sumbool::left
  } else {
    sumbool::right
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
  let tmp = ltb(u, n);
  match bdec(tmp) {
    sumbool::left => {
      let f_ref: &Rc<dyn Fn(u64, u64, u64, A) -> A> = &f;
      let a_ = f_ref(u, i, j, a);
      let j1 = add_3(j, 1u64);
      let e = eqb(j1, C);
      let tmp_1 = ();
      let tmp_2 = add_3(u, 1u64);
      let tmp_3 = if e {
        add_3(i, 1u64)
      } else {
        i
      };
      let tmp_4 = if e {
        0u64
      } else {
        j1
      };
      gloop::<A>(tmp_1, C, n, f, tmp_2, tmp_3, tmp_4, a_, ())
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
  let callback: Rc<dyn Fn(u64, u64, u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
    move |u: u64, i: u64, j: u64, a: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let xg = &xg;
      let xg_clone = Rc::clone(xg);
      let tmp = rocq_array::get::<Rc<Array<u64>>>(&xg_clone, i);
      std::mem::drop(xg_clone);
      let tmp_1 = rocq_array::get::<u64>(&tmp, j);
      std::mem::drop(tmp);
      rocq_array::set::<u64>(a, u, tmp_1)
    }
  });
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  grid_fold::<Rc<Array<u64>>>(C, n, callback, tmp_2)
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
  if ltb(a, b) {
    sub(b, a)
  } else {
    sub(a, b)
  }
}

// Rocq: Darkness.darkness_implem.denom
// Variant: uncurried
pub fn denom(hh: u64, i: u64, j: u64, i_: u64, j_: u64) -> u64 {
  let di = absdiff(i, i_);
  let dj = absdiff(j, j_);
  let tmp = add_3(mul_1(di, di), mul_1(dj, dj));
  add_3(tmp, hh)
}

// Rocq: Darkness.darkness_implem.lo_sum
// Variant: borrowed, uncurried
pub fn lo_sum(s: &Rc<Array<u64>>, C: u64, n: u64, hh: u64, i: u64, j: u64) -> u64 {
  let C_1 = C;
  let n_1 = n;
  let s_clone = Rc::clone(s);
  let callback: Rc<dyn Fn(u64, u64, u64, u64) -> u64> = Rc::new({
    move |u: u64, i_: u64, j_: u64, acc: u64| -> u64 {
      let s = &s_clone;
      let hh = &hh;
      let i = &i;
      let j = &j;
      let tmp = mul_1(__rocq_global_789, rocq_array::get::<u64>(s, u));
      let hh_clone = Clone::clone(hh);
      let i_clone = Clone::clone(i);
      let j_clone = Clone::clone(j);
      add_3(acc, div(tmp, denom(hh_clone, i_clone, j_clone, i_, j_)))
    }
  });
  grid_fold::<u64>(C_1, n_1, callback, 0u64)
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
      let y_clone = Rc::clone(&y);
      add_1(y, __rocq_reuse::rebuild(v3, positive::xO(mul(v9, y_clone))))
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
  let tmp = eqb(x, 0u64);
  match bdec(tmp) {
    sumbool::left => {
      Rc::new(Z::Z0)
    },
    sumbool::right => {
      let r = zofint_aux(div(x, 2u64), ());
      let tmp_1 = mod_(x, 2u64);
      if eqb(tmp_1, 0u64) {
        let tmp_2 = Rc::new(positive::xH);
        let tmp_3 = Rc::new(positive::xO(tmp_2));
        mul_3(Rc::new(Z::Zpos(tmp_3)), r)
      } else {
        let tmp_4 = Rc::new(positive::xH);
        let tmp_5 = Rc::new(positive::xO(tmp_4));
        let tmp_6 = mul_3(Rc::new(Z::Zpos(tmp_5)), r);
        let tmp_7 = Rc::new(positive::xH);
        add_2(tmp_6, Rc::new(Z::Zpos(tmp_7)))
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
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Darkness.darkness_implem.exact_sum
// Variant: borrowed, uncurried
pub fn exact_sum(s: &Rc<Array<u64>>, C: u64, n: u64, hh: u64, i: u64, j: u64) -> (Rc<Z>, Rc<Z>) {
  let C_1 = C;
  let n_1 = n;
  let s_clone = Rc::clone(s);
  let callback: Rc<dyn Fn(u64, u64, u64, (Rc<Z>, Rc<Z>)) -> (Rc<Z>, Rc<Z>)> = Rc::new({
    move |u: u64, i_: u64, j_: u64, pq: (Rc<Z>, Rc<Z>)| -> (Rc<Z>, Rc<Z>) {
      let hh = &hh;
      let i = &i;
      let j = &j;
      let s = &s_clone;
      let d = zofint(denom(Clone::clone(hh), Clone::clone(i), Clone::clone(j), i_, j_));
      let tmp = rocq_array::get::<u64>(s, u);
      let sv = zofint(tmp);
      let pq_clone = Clone::clone(&pq);
      let tmp_1 = fst::<Rc<Z>, Rc<Z>>(pq_clone);
      let d_clone = Rc::clone(&d);
      let tmp_2 = mul_3(tmp_1, d_clone);
      let pq_clone_1 = Clone::clone(&pq);
      (add_2(tmp_2, mul_3(sv, snd::<Rc<Z>, Rc<Z>>(pq_clone_1))), mul_3(snd::<Rc<Z>, Rc<Z>>(pq), d))
    }
  });
  let tmp_3 = Rc::new(Z::Z0);
  let tmp_4 = Rc::new(positive::xH);
  grid_fold::<(Rc<Z>, Rc<Z>)>(C_1, n_1, callback, (tmp_3, Rc::new(Z::Zpos(tmp_4))))
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
  if leb(mb, lo) {
    true
  } else {
    let tmp = add_3(lo, n_1);
    if ltb(tmp, mb) {
      false
    } else {
      let pq = exact_sum(s, C_1, n_1, hh_1, i_1, j_1);
      let tmp_1 = zofint(b_1);
      let pq_clone = Clone::clone(&pq);
      leb_1(mul_3(tmp_1, snd::<Rc<Z>, Rc<Z>>(pq_clone)), fst::<Rc<Z>, Rc<Z>>(pq))
    }
  }
}

// Rocq: Darkness.darkness_implem.lit_arr
// Variant: uncurried
pub fn lit_arr(s: Rc<Array<u64>>, C: u64, n: u64, b: u64, hh: u64) -> Rc<Array<bool>> {
  let callback: Rc<dyn Fn(u64, u64, u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new({
    let __anf_capture_19 = C;
    let __anf_capture_21 = n;
    move |u: u64, i: u64, j: u64, a: Rc<Array<bool>>| -> Rc<Array<bool>> {
      let tmp = lit_cell(&s, Clone::clone(&__anf_capture_19), Clone::clone(&__anf_capture_21), Clone::clone(&b), Clone::clone(&hh), i, j);
      rocq_array::set::<bool>(a, u, tmp)
    }
  });
  let tmp_1 = rocq_array::make::<bool>(n, false);
  grid_fold::<Rc<Array<bool>>>(C, n, callback, tmp_1)
}

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  if b1 {
    b2
  } else {
    false
  }
}

// Rocq: Darkness.darkness_implem.capf
// Variant: uncurried
pub fn capf(x: bool, y: bool) -> u64 {
  if andb(x, y) {
    43u64
  } else {
    11u64
  }
}

// Rocq: Darkness.darkness_implem.init_res
// Variant: uncurried
pub fn init_res(lt: Rc<Array<bool>>, C: u64, n: u64) -> Rc<Array<u64>> {
  let callback: Rc<dyn Fn(u64, u64, u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
    let __anf_capture_9 = C;
    move |u: u64, _i: u64, _j: u64, r: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let C = &__anf_capture_9;
      let c1 = capf(rocq_array::get::<bool>(&lt, u), rocq_array::get::<bool>(&lt, add_3(u, 1u64)));
      let tmp = rocq_array::get::<bool>(&lt, u);
      let tmp_1 = rocq_array::get::<bool>(&lt, add_3(u, Clone::clone(C)));
      let c2 = capf(tmp, tmp_1);
      let tmp_2 = rocq_array::set::<u64>(r, mul_1(2u64, u), c1);
      rocq_array::set::<u64>(tmp_2, add_3(mul_1(2u64, u), 1u64), c2)
    }
  });
  let tmp_3 = rocq_array::make::<u64>(mul_1(2u64, n), 0u64);
  grid_fold::<Rc<Array<u64>>>(C, n, callback, tmp_3)
}

// Rocq: Darkness.darkness_implem.bt
pub fn bt_owned(b: Rc<bst>) -> u64 {
  let b_bt_clone = Clone::clone(&b.bt);
  std::mem::drop(b);
  b_bt_clone
}

// Rocq: Darkness.darkness_implem.bt
// Variant: borrowed
pub fn bt(b: &Rc<bst>) -> u64 {
  let tmp = b;
  Clone::clone(&tmp.bt)
}

// Rocq: Darkness.darkness_implem.bq
pub fn bq(b: Rc<bst>) -> Rc<Array<u64>> {
  let b_bq_clone = Rc::clone(&b.bq);
  std::mem::drop(b);
  b_bq_clone
}

// Rocq: Darkness.darkness_implem.bd
pub fn bd(b: Rc<bst>) -> Rc<Array<u64>> {
  let b_bd_clone = Rc::clone(&b.bd);
  std::mem::drop(b);
  b_bd_clone
}

// Rocq: Darkness.darkness_implem.nbr
// Variant: uncurried
pub fn nbr(C: u64, p: u64, d: u64) -> u64 {
  if eqb(d, 0u64) {
    add_3(p, 1u64)
  } else {
    if eqb(d, 1u64) {
      sub(p, 1u64)
    } else {
      if eqb(d, 2u64) {
        add_3(p, C)
      } else {
        sub(p, C)
      }
    }
  }
}

// Rocq: Darkness.darkness_implem.slot
// Variant: uncurried
pub fn slot(C: u64, p: u64, d: u64) -> u64 {
  if eqb(d, 0u64) {
    mul_1(2u64, p)
  } else {
    if eqb(d, 1u64) {
      mul_1(2u64, sub(p, 1u64))
    } else {
      if eqb(d, 2u64) {
        add_3(mul_1(2u64, p), 1u64)
      } else {
        add_3(mul_1(2u64, sub(p, C)), 1u64)
      }
    }
  }
}

// Rocq: Corelib.Init.Datatypes.orb
// Variant: uncurried
pub fn orb(b1: bool, b2: bool) -> bool {
  if b1 {
    true
  } else {
    b2
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
  if fwd(d) {
    std::mem::drop(lt);
    let tmp = rocq_array::get::<u64>(&res, k);
    std::mem::drop(res);
    tmp
  } else {
    let tmp_1 = 2u64;
    let tmp_2 = rocq_array::get::<bool>(&lt, p);
    let tmp_3 = rocq_array::get::<bool>(&lt, nbr(C, p, d));
    std::mem::drop(lt);
    let tmp_4 = mul_1(tmp_1, capf(tmp_2, tmp_3));
    let tmp_5 = rocq_array::get::<u64>(&res, k);
    std::mem::drop(res);
    sub(tmp_4, tmp_5)
  }
}

// Rocq: Darkness.darkness_implem.bp
pub fn bp(b: Rc<bst>) -> Rc<Array<u64>> {
  let b_bp_clone = Rc::clone(&b.bp);
  std::mem::drop(b);
  b_bp_clone
}

// Rocq: Darkness.darkness_implem.visit
// Variant: uncurried
pub fn visit(lt: Rc<Array<bool>>, res: Rc<Array<u64>>, C: u64, st: Rc<bst>, v: u64, dv: u64, d: u64, ok: bool) -> Rc<bst> {
  if ok {
    let w = nbr(C, v, d);
    let tmp = resid(lt, res, C, v, d);
    if ltb(0u64, tmp) {
      let st_clone = Rc::clone(&st);
      let tmp_1 = bd(st_clone);
      let tmp_2 = rocq_array::get::<u64>(&tmp_1, w);
      if eqb(tmp_2, 0u64) {
        std::mem::drop(tmp_1);
        let st_clone_1 = Rc::clone(&st);
        let tmp_3 = bd(st_clone_1);
        let tmp_4 = rocq_array::set::<u64>(tmp_3, w, add_3(dv, 1u64));
        let st_clone_2 = Rc::clone(&st);
        let tmp_5 = bp(st_clone_2);
        let tmp_6 = rocq_array::set::<u64>(tmp_5, w, d);
        let st_clone_3 = Rc::clone(&st);
        let tmp_7 = bq(st_clone_3);
        let tmp_8 = bt(&st);
        let tmp_9 = rocq_array::set::<u64>(tmp_7, tmp_8, w);
        Rc::new(bst { bd: tmp_4, bp: tmp_6, bq: tmp_9, bt: add_3(bt_owned(st), 1u64) })
      } else {
        std::mem::drop(tmp_1);
        st
      }
    } else {
      st
    }
  } else {
    std::mem::drop(lt);
    std::mem::drop(res);
    st
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
  let tmp = ltb(head, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = bt(&st);
      if ltb(head, tmp_1) {
        let st_clone = Rc::clone(&st);
        let tmp_2 = bq(st_clone);
        let v = rocq_array::get::<u64>(&tmp_2, head);
        std::mem::drop(tmp_2);
        let st_clone_1 = Rc::clone(&st);
        let tmp_3 = bd(st_clone_1);
        let dv = rocq_array::get::<u64>(&tmp_3, v);
        std::mem::drop(tmp_3);
        let j = mod_(v, C);
        let tmp_4 = ltb(add_3(j, 1u64), C);
        let lt_clone = Rc::clone(&lt);
        let res_clone = Rc::clone(&res);
        let st1 = visit(lt_clone, res_clone, C, st, v, dv, 0u64, tmp_4);
        let tmp_5 = ltb(0u64, j);
        let lt_clone_1 = Rc::clone(&lt);
        let res_clone_1 = Rc::clone(&res);
        let st2 = visit(lt_clone_1, res_clone_1, C, st1, v, dv, 1u64, tmp_5);
        let tmp_6 = ltb(add_3(v, C), n);
        let lt_clone_2 = Rc::clone(&lt);
        let res_clone_2 = Rc::clone(&res);
        let st3 = visit(lt_clone_2, res_clone_2, C, st2, v, dv, 2u64, tmp_6);
        let tmp_7 = leb(C, v);
        let lt_clone_3 = Rc::clone(&lt);
        let res_clone_3 = Rc::clone(&res);
        let st4 = visit(lt_clone_3, res_clone_3, C, st3, v, dv, 3u64, tmp_7);
        bfs_loop(lt, res, C, n, add_3(head, 1u64), st4, ())
      } else {
        std::mem::drop(lt);
        std::mem::drop(res);
        st
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
  let tmp = rocq_array::get::<bool>(&lt, u);
  if tmp {
    std::mem::drop(lt);
    st
  } else {
    std::mem::drop(lt);
    let st_clone = Rc::clone(&st);
    let tmp_1 = bd(st_clone);
    let tmp_2 = rocq_array::set::<u64>(tmp_1, u, 1u64);
    let st_clone_1 = Rc::clone(&st);
    let tmp_3 = bp(st_clone_1);
    let tmp_4 = rocq_array::set::<u64>(tmp_3, u, 4u64);
    let st_clone_2 = Rc::clone(&st);
    let tmp_5 = bq(st_clone_2);
    let tmp_6 = bt(&st);
    let tmp_7 = rocq_array::set::<u64>(tmp_5, tmp_6, u);
    Rc::new(bst { bd: tmp_2, bp: tmp_4, bq: tmp_7, bt: add_3(bt_owned(st), 1u64) })
  }
}

// Rocq: Darkness.darkness_implem.roots
// Variant: uncurried
pub fn roots(lt: Rc<Array<bool>>, C: u64, n: u64) -> Rc<bst> {
  let callback: Rc<dyn Fn(u64, u64, u64, Rc<bst>) -> Rc<bst>> = Rc::new({
    move |v9: u64, v10: u64, v11: u64, v12: Rc<bst>| -> Rc<bst> {
      let lt_clone = Rc::clone(&lt);
      root_step(lt_clone, v9, v10, v11, v12)
    }
  });
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let tmp_1 = rocq_array::make::<u64>(n, 0u64);
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  grid_fold::<Rc<bst>>(C, n, callback, Rc::new(bst { bd: tmp, bp: tmp_1, bq: tmp_2, bt: 0u64 }))
}

// Rocq: Darkness.darkness_implem.bfs
// Variant: uncurried
pub fn bfs(lt: Rc<Array<bool>>, res: Rc<Array<u64>>, C: u64, n: u64) -> Rc<bst> {
  let lt_clone = Rc::clone(&lt);
  let tmp = roots(lt_clone, C, n);
  bfs_loop_1(lt, res, C, n, 0u64, tmp)
}

// Rocq: Darkness.darkness_implem.is_border
// Variant: uncurried
pub fn is_border(R: u64, C: u64, i: u64, j: u64) -> bool {
  let tmp = orb(eqb(i, 0u64), eqb(i, sub(R, 1u64)));
  let tmp_1 = orb(tmp, eqb(j, 0u64));
  orb(tmp_1, eqb(j, sub(C, 1u64)))
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  if b {
    false
  } else {
    true
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
  let tmp = andb(is_border(R_1, C_1, i_1, j_1), negb(eqb(rocq_array::get::<u64>(dist, u_1), 0u64)));
  let tmp_1 = orb(eqb(acc_1, n_1), ltb(rocq_array::get::<u64>(dist, u_1), rocq_array::get::<u64>(dist, acc_1)));
  if andb(tmp, tmp_1) {
    u_1
  } else {
    acc_1
  }
}

// Rocq: Darkness.darkness_implem.find_border
// Variant: uncurried
pub fn find_border(dist: Rc<Array<u64>>, R: u64, C: u64, n: u64) -> u64 {
  let callback: Rc<dyn Fn(u64, u64, u64, u64) -> u64> = Rc::new({
    let __anf_capture_18 = C;
    let __anf_capture_20 = n;
    move |v22: u64, v23: u64, v24: u64, v25: u64| -> u64 {
      let dist = &dist;
      let R_clone = Clone::clone(&R);
      let tmp = Clone::clone(&__anf_capture_18);
      let tmp_1 = Clone::clone(&__anf_capture_20);
      fb_step(dist, R_clone, tmp, tmp_1, v22, v23, v24, v25)
    }
  });
  grid_fold::<u64>(C, n, callback, n)
}

// Rocq: Darkness.darkness_implem.opp
pub fn opp(d: u64) -> u64 {
  if eqb(d, 0u64) {
    1u64
  } else {
    if eqb(d, 1u64) {
      0u64
    } else {
      if eqb(d, 2u64) {
        3u64
      } else {
        2u64
      }
    }
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
  let d = rocq_array::get::<u64>(&par, v);
  if ltb(d, 4u64) {
    let p = nbr(C, v, opp(d));
    let tmp = rocq_array::get::<u64>(&dist, p);
    let tmp_1 = rocq_array::get::<u64>(&dist, v);
    let tmp_2 = ltb(tmp, tmp_1);
    match bdec(tmp_2) {
      sumbool::left => {
        let lt_clone = Rc::clone(&lt);
        let res_clone = Rc::clone(&res);
        let r = resid(lt_clone, res_clone, C, p, d);
        let tmp_3 = if ltb(r, dl) {
          r
        } else {
          dl
        };
        tmin(lt, res, C, par, dist, p, tmp_3, ())
      },
      sumbool::right => {
        std::mem::drop(lt);
        std::mem::drop(res);
        std::mem::drop(dist);
        std::mem::drop(par);
        dl
      },
    }
  } else {
    std::mem::drop(lt);
    std::mem::drop(res);
    std::mem::drop(dist);
    std::mem::drop(par);
    dl
  }
}

// Rocq: Darkness.darkness_implem.aug
// Variant: uncurried
pub fn aug(res: Rc<Array<u64>>, C: u64, p: u64, d: u64, dl: u64) -> Rc<Array<u64>> {
  let k = slot(C, p, d);
  if fwd(d) {
    let tmp = rocq_array::get::<u64>(&res, k);
    rocq_array::set::<u64>(res, k, sub(tmp, dl))
  } else {
    let tmp_1 = rocq_array::get::<u64>(&res, k);
    rocq_array::set::<u64>(res, k, add_3(tmp_1, dl))
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
  let d = rocq_array::get::<u64>(&par, v);
  if ltb(d, 4u64) {
    let p = nbr(C, v, opp(d));
    let tmp = rocq_array::get::<u64>(&dist, p);
    let tmp_1 = rocq_array::get::<u64>(&dist, v);
    let tmp_2 = ltb(tmp, tmp_1);
    match bdec(tmp_2) {
      sumbool::left => {
        let tmp_3 = aug(res, C, p, d, dl);
        tapp(C, par, dist, dl, p, tmp_3, ())
      },
      sumbool::right => {
        std::mem::drop(dist);
        std::mem::drop(par);
        res
      },
    }
  } else {
    std::mem::drop(dist);
    std::mem::drop(par);
    res
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
  let lt_clone = Rc::clone(&lt);
  let res_clone = Rc::clone(&res);
  let st = bfs(lt_clone, res_clone, C, n);
  let st_clone = Rc::clone(&st);
  let tmp = bd(st_clone);
  let w = find_border(tmp, R, C, n);
  if eqb(w, n) {
    std::mem::drop(st);
    std::mem::drop(lt);
    std::mem::drop(res);
    F
  } else {
    let st_clone_1 = Rc::clone(&st);
    let tmp_1 = bp(st_clone_1);
    let st_clone_2 = Rc::clone(&st);
    let tmp_2 = bd(st_clone_2);
    let lt_clone_1 = Rc::clone(&lt);
    let res_clone_1 = Rc::clone(&res);
    let dl = tmin_1(lt_clone_1, res_clone_1, C, tmp_1, tmp_2, w, 1000u64);
    let st_clone_3 = Rc::clone(&st);
    let tmp_3 = bp(st_clone_3);
    let tmp_4 = bd(st);
    let res_ = tapp_1(C, tmp_3, tmp_4, dl, w, res);
    let F_ = add_3(F, dl);
    let tmp_5 = andb(ltb(F, F_), leb(F_, B));
    match bdec(tmp_5) {
      sumbool::left => {
        flow_loop(lt, R, C, n, B, res_, F_, ())
      },
      sumbool::right => {
        std::mem::drop(res_);
        std::mem::drop(lt);
        F
      },
    }
  }
}

// Rocq: Darkness.darkness_implem.darkness_impl
// Variant: uncurried
pub fn darkness_impl(xb: u64, xh: u64, xg: Rc<Array<Rc<Array<u64>>>>) -> u64 {
  let R = rocq_array::length::<Rc<Array<u64>>>(&xg);
  let xg_clone = Rc::clone(&xg);
  let tmp = rocq_array::get::<Rc<Array<u64>>>(&xg_clone, 0u64);
  std::mem::drop(xg_clone);
  let C = rocq_array::length::<u64>(&tmp);
  std::mem::drop(tmp);
  let n = mul_1(R, C);
  let s = flat(xg, C, n);
  let lt = lit_arr(s, C, n, xb, mul_1(xh, xh));
  let lt_clone = Rc::clone(&lt);
  let res = init_res(lt_clone, C, n);
  let B = mul_1(86u64, n);
  flow_loop_1(lt, R, C, n, B, res, 0u64)
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
const __rocq_global_789: u64 = 281474976710656u64;