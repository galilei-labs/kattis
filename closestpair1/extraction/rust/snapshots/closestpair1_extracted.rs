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

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = Int63;

// Rocq: Closestpair1.closestpair1_implem.cinit
pub fn cinit(_v0: ()) -> f64 {
  rocq_float64::of_uint63(int63!(200001))
}

// Rocq: Corelib.BinNums.PosDef.Pos.compare_cont
// Variant: uncurried
pub fn compare_cont_owned_1(r: std::cmp::Ordering, x: Rc<positive>, y: Rc<positive>) -> std::cmp::Ordering {
  compare_cont_owned(r, x, y)
}

// Rocq: Corelib.BinNums.PosDef.Pos.compare_cont (local: compare_cont)
// Variant: uncurried, lifted
pub fn compare_cont_owned(r: std::cmp::Ordering, x: Rc<positive>, y: Rc<positive>) -> std::cmp::Ordering {
  match &*x {
    positive::xI(p) => {
      let (v7, v8) = __rocq_reuse::reset(y, |__payload| Clone::clone(__payload));
      std::mem::drop(v8);
      match v7 {
        positive::xI(v14) => {
          let p_clone = Rc::clone(p);
          std::mem::drop(x);
          compare_cont_owned(r, p_clone, v14)
        },
        positive::xO(v26) => {
          let p_clone_1 = Rc::clone(p);
          std::mem::drop(x);
          compare_cont_owned(std::cmp::Ordering::Greater, p_clone_1, v26)
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
          compare_cont_owned(std::cmp::Ordering::Less, p_clone_2, v56)
        },
        positive::xO(v70) => {
          let p_clone_3 = Rc::clone(p);
          std::mem::drop(x);
          compare_cont_owned(r, p_clone_3, v70)
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

// Rocq: Corelib.BinNums.PosDef.Pos.compare_cont
// Variant: borrowed, uncurried
pub fn compare_cont_1(r: std::cmp::Ordering, x: &Rc<positive>, y: &Rc<positive>) -> std::cmp::Ordering {
  let r_1 = r;
  compare_cont(r_1, x, y)
}

// Rocq: Corelib.BinNums.PosDef.Pos.compare_cont (local: compare_cont)
// Variant: borrowed, uncurried, lifted
pub fn compare_cont(r: std::cmp::Ordering, x: &Rc<positive>, y: &Rc<positive>) -> std::cmp::Ordering {
  let r_1 = r;
  let tmp = x;
  match &**tmp {
    positive::xI(p) => {
      let tmp_1 = y;
      match &**tmp_1 {
        positive::xI(q) => {
          compare_cont(r_1, p, q)
        },
        positive::xO(q) => {
          compare_cont(std::cmp::Ordering::Greater, p, q)
        },
        positive::xH => {
          std::cmp::Ordering::Greater
        },
      }
    },
    positive::xO(p) => {
      let tmp_2 = y;
      match &**tmp_2 {
        positive::xI(q) => {
          compare_cont(std::cmp::Ordering::Less, p, q)
        },
        positive::xO(q) => {
          compare_cont(r_1, p, q)
        },
        positive::xH => {
          std::cmp::Ordering::Greater
        },
      }
    },
    positive::xH => {
      let tmp_3 = y;
      match &**tmp_3 {
        positive::xI(_q) => {
          std::cmp::Ordering::Less
        },
        positive::xO(_q_1) => {
          std::cmp::Ordering::Less
        },
        positive::xH => {
          r_1
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
pub fn compare_owned(x: Rc<Z>, y: Rc<Z>) -> std::cmp::Ordering {
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
          compare_cont_owned_1(std::cmp::Ordering::Equal, v35, v48)
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
          CompOpp(compare_cont_owned_1(std::cmp::Ordering::Equal, v71, v90))
        },
      }
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.compare
// Variant: borrowed, uncurried
pub fn compare(x: &Rc<Z>, y: &Rc<Z>) -> std::cmp::Ordering {
  let tmp = x;
  match &**tmp {
    Z::Z0 => {
      let tmp_1 = y;
      match &**tmp_1 {
        Z::Z0 => {
          std::cmp::Ordering::Equal
        },
        Z::Zpos(_y_) => {
          std::cmp::Ordering::Less
        },
        Z::Zneg(_y__1) => {
          std::cmp::Ordering::Greater
        },
      }
    },
    Z::Zpos(x_) => {
      let tmp_2 = y;
      match &**tmp_2 {
        Z::Z0 => {
          std::cmp::Ordering::Greater
        },
        Z::Zpos(y_) => {
          compare_cont_1(std::cmp::Ordering::Equal, x_, y_)
        },
        Z::Zneg(_y__2) => {
          std::cmp::Ordering::Greater
        },
      }
    },
    Z::Zneg(x_) => {
      let tmp_3 = y;
      match &**tmp_3 {
        Z::Z0 => {
          std::cmp::Ordering::Less
        },
        Z::Zpos(_y__3) => {
          std::cmp::Ordering::Less
        },
        Z::Zneg(y_) => {
          let tmp_4 = compare_cont_1(std::cmp::Ordering::Equal, x_, y_);
          CompOpp(tmp_4)
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

// Rocq: Corelib.BinNums.IntDef.Z.opp
pub fn opp(x: Rc<Z>) -> Rc<Z> {
  let (v1, v2) = __rocq_reuse::reset(x, |__payload| Clone::clone(__payload));
  match v1 {
    Z::Z0 => {
      __rocq_reuse::rebuild(v2, Z::Z0)
    },
    Z::Zpos(v13) => {
      __rocq_reuse::rebuild(v2, Z::Zneg(v13))
    },
    Z::Zneg(v22) => {
      __rocq_reuse::rebuild(v2, Z::Zpos(v22))
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.sub
// Variant: uncurried
pub fn sub(m: Rc<Z>, n: Rc<Z>) -> Rc<Z> {
  add_2(m, opp(n))
}

// Rocq: Closestpair1.closestpair1_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Closestpair1.closestpair1_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: Int63, cont: Rc<dyn Fn(Int63, St) -> bool>, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Closestpair1.closestpair1_implem.wloop (local: wloop)
// Variant: uncurried, lifted
pub fn wloop<St: Clone + 'static>(hi: Int63, cont: Rc<dyn Fn(Int63, St) -> bool>, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St, _H: ()) -> St {
  let tmp = i < hi;
  match bdec(tmp) {
    sumbool::left => {
      let cont_ref: &Rc<dyn Fn(Int63, St) -> bool> = &cont;
      let s_clone = Clone::clone(&s);
      let tmp_1 = cont_ref(i, s_clone);
      if tmp_1 {
        let tmp_2 = i + int63!(1);
        let f_ref: &Rc<dyn Fn(Int63, St) -> St> = &f;
        let tmp_3 = f_ref(i, s);
        wloop::<St>(hi, cont, f, tmp_2, tmp_3, ())
      } else {
        std::mem::drop(f);
        std::mem::drop(cont);
        s
      }
    },
    sumbool::right => {
      std::mem::drop(cont);
      std::mem::drop(f);
      s
    },
  }
}

// Rocq: Closestpair1.closestpair1_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: Int63, cont: Rc<dyn Fn(Int63, St) -> bool>, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop_1::<St>(hi, cont, f, i, s)
}

// Rocq: Closestpair1.closestpair1_implem.c1e5
pub fn c1e5(_v0: ()) -> f64 {
  rocq_float64::of_uint63(int63!(100000))
}

// Rocq: Closestpair1.closestpair1_implem.c52
pub fn c52(_v0: ()) -> f64 {
  rocq_float64::of_uint63(int63!(4503599627370496))
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Corelib.Floats.PrimFloat.frshiftexp
pub fn frshiftexp(x: f64) -> (f64, Int63) {
  (rocq_float64::frshiftexp_fraction(x), rocq_float64::frshiftexp_exponent(x))
}

// Rocq: Closestpair1.closestpair1_implem.key
// Variant: uncurried
pub fn key(s: f64, n1: Int63, f: f64) -> Int63 {
  let tmp = rocq_float64::add(f, c1e5(()));
  let u = rocq_float64::add(rocq_float64::mul(tmp, s), c52(()));
  let k = rocq_float64::normfr_mantissa(fst::<f64, Int63>(frshiftexp(u))) - int63!(4503599627370496);
  if k < n1 {
    k
  } else {
    n1
  }
}

// Rocq: Closestpair1.closestpair1_implem.key_step
// Variant: uncurried
pub fn key_step(x: Array<f64>, s: f64, n1: Int63, i: Int63, K: Array<Int63>) -> Array<Int63> {
  let tmp = x.get_cloned(i);
  std::mem::drop(x);
  K.set(i, key(s, n1, tmp))
}

// Rocq: Closestpair1.closestpair1_implem.count_step
// Variant: uncurried
pub fn count_step(K: Array<Int63>, i: Int63, C: Array<Int63>) -> Array<Int63> {
  let b_1 = K.get_cloned(i);
  std::mem::drop(K);
  let v = C.get_cloned(b_1);
  C.set(b_1, v + int63!(1))
}

// Rocq: Closestpair1.closestpair1_implem.prefix_step
// Variant: uncurried
pub fn prefix_step(b_1: Int63, st: (Array<Int63>, Int63)) -> (Array<Int63>, Int63) {
  match st {
    (v3, v5) => {
      let acc = &v3;
      let v = acc.get_cloned(b_1);
      (v3.set(b_1, v5), v5 + v)
    },
  }
}

// Rocq: Closestpair1.closestpair1_implem.place_step
// Variant: borrowed, uncurried
pub fn place_step(K: &Array<Int63>, i: Int63, st: (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>) {
  let i_1 = i;
  let st_1 = st;
  match st_1 {
    (v6, v8) => {
      let P = &v8;
      let b_1 = K.get_cloned(i_1);
      let v = P.get_cloned(b_1);
      (v6.set(v, i_1), v8.set(b_1, v + int63!(1)))
    },
  }
}

// Rocq: Closestpair1.closestpair1_implem.min_step
// Variant: uncurried
pub fn min_step(x: Array<f64>, K: Array<Int63>, i: Int63, M: Array<f64>) -> Array<f64> {
  let b_1 = K.get_cloned(i);
  let xi = x.get_cloned(i);
  let tmp = M.get_cloned(b_1);
  if rocq_float64::ltb(xi, tmp) {
    std::mem::drop(K);
    std::mem::drop(x);
    M.set(b_1, xi)
  } else {
    std::mem::drop(K);
    std::mem::drop(x);
    M
  }
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b_1: bool) -> bool {
  if b_1 {
    false
  } else {
    true
  }
}

// Rocq: Closestpair1.closestpair1_implem.tol
pub fn tol(_v0: ()) -> f64 {
  rocq_float64::div(rocq_float64::of_uint63(int63!(1)), rocq_float64::of_uint63(int63!(1024)))
}

// Rocq: Closestpair1.closestpair1_implem.gx
// Variant: uncurried
pub fn gx(m: f64, p: f64) -> f64 {
  let d = rocq_float64::sub(m, p);
  rocq_float64::mul(d, d)
}

// Rocq: Closestpair1.closestpair1_implem.cand_cont
// Variant: borrowed, uncurried
pub fn cand_cont(x: &Array<f64>, K: &Array<Int63>, M: &Array<f64>, P: &Array<Int63>, p: Int63, kp: Int63, c: Int63, st: ((f64, Int63), Int63)) -> bool {
  let p_1 = p;
  let kp_1 = kp;
  let c_1 = c;
  let st_1 = st;
  match st_1 {
    (v13, _v15) => {
      match v13 {
        (v18, _v20) => {
          let kq = K.get_cloned(P.get_cloned(c_1));
          if kp_1 < kq {
            negb(rocq_float64::ltb(rocq_float64::add(v18, tol(())), gx(M.get_cloned(kq), x.get_cloned(p_1))))
          } else {
            true
          }
        },
      }
    },
  }
}

// Rocq: Closestpair1.closestpair1_implem.fd
// Variant: uncurried
pub fn fd_owned(x: Array<f64>, y: Array<f64>, a_1: Int63, b_1: Int63) -> f64 {
  let tmp = x.get_cloned(a_1);
  let tmp_1 = x.get_cloned(b_1);
  std::mem::drop(x);
  let dx = rocq_float64::sub(tmp, tmp_1);
  let tmp_2 = y.get_cloned(a_1);
  let tmp_3 = y.get_cloned(b_1);
  std::mem::drop(y);
  let dy = rocq_float64::sub(tmp_2, tmp_3);
  rocq_float64::add(rocq_float64::mul(dx, dx), rocq_float64::mul(dy, dy))
}

// Rocq: Closestpair1.closestpair1_implem.fd
// Variant: borrowed, uncurried
pub fn fd(x: &Array<f64>, y: &Array<f64>, a_1: Int63, b_1: Int63) -> f64 {
  let a_2 = a_1;
  let b_2 = b_1;
  let dx = rocq_float64::sub(x.get_cloned(a_2), x.get_cloned(b_2));
  let dy = rocq_float64::sub(y.get_cloned(a_2), y.get_cloned(b_2));
  rocq_float64::add(rocq_float64::mul(dx, dx), rocq_float64::mul(dy, dy))
}

// Rocq: Corelib.BinNums.IntDef.Z.min
// Variant: uncurried
pub fn min(n: Rc<Z>, m: Rc<Z>) -> Rc<Z> {
  match compare(&n, &m) {
    std::cmp::Ordering::Equal => {
      std::mem::drop(m);
      n
    },
    std::cmp::Ordering::Less => {
      std::mem::drop(m);
      n
    },
    std::cmp::Ordering::Greater => {
      std::mem::drop(n);
      m
    },
  }
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Corelib.BinNums.IntDef.Z.ltb
// Variant: uncurried
pub fn ltb(x: Rc<Z>, y: Rc<Z>) -> bool {
  match compare_owned(x, y) {
    std::cmp::Ordering::Equal => {
      false
    },
    std::cmp::Ordering::Less => {
      true
    },
    std::cmp::Ordering::Greater => {
      false
    },
  }
}

// Rocq: Corelib.BinNums.PosDef.Pos.iter
// Variant: uncurried
pub fn iter<A: Clone + 'static>(f: Rc<dyn Fn(A) -> A>, x: A, n: Rc<positive>) -> A {
  iter_fix::<A>(f, x, n)
}

// Rocq: Corelib.BinNums.PosDef.Pos.iter (local: iter_fix)
// Variant: uncurried, lifted
pub fn iter_fix<A: Clone + 'static>(f: Rc<dyn Fn(A) -> A>, x: A, n: Rc<positive>) -> A {
  let (v3, v4) = __rocq_reuse::reset(n, |__payload| Clone::clone(__payload));
  std::mem::drop(v4);
  match v3 {
    positive::xI(v10) => {
      let n_ = &v10;
      let f_clone: Rc<dyn Fn(A) -> A> = Rc::clone(&f);
      let tmp = x;
      let n__clone = Rc::clone(n_);
      let tmp_1 = iter_fix::<A>(f_clone, tmp, n__clone);
      let f_clone_1: Rc<dyn Fn(A) -> A> = Rc::clone(&f);
      let tmp_2 = iter_fix::<A>(f_clone_1, tmp_1, v10);
      let f_ref: &Rc<dyn Fn(A) -> A> = &f;
      let tmp_3 = f_ref(tmp_2);
      std::mem::drop(f);
      tmp_3
    },
    positive::xO(v37) => {
      let n_ = &v37;
      let f_clone_2: Rc<dyn Fn(A) -> A> = Rc::clone(&f);
      let tmp_4 = x;
      let n__clone_1 = Rc::clone(n_);
      let tmp_5 = iter_fix::<A>(f_clone_2, tmp_4, n__clone_1);
      iter_fix::<A>(f, tmp_5, v37)
    },
    positive::xH => {
      let f_ref_1: &Rc<dyn Fn(A) -> A> = &f;
      let tmp_6 = f_ref_1(x);
      std::mem::drop(f);
      tmp_6
    },
  }
}

// Rocq: Corelib.BinNums.PosDef.Pos.mul
// Variant: uncurried
pub fn mul_1(x: Rc<positive>, y: Rc<positive>) -> Rc<positive> {
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
pub fn mul_2(x: Rc<Z>, y: Rc<Z>) -> Rc<Z> {
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
          __rocq_reuse::rebuild(v17, Z::Zpos(mul_1(v14, v28)))
        },
        Z::Zneg(v43) => {
          __rocq_reuse::rebuild(v17, Z::Zneg(mul_1(v14, v43)))
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
          __rocq_reuse::rebuild(v64, Z::Zneg(mul_1(v61, v75)))
        },
        Z::Zneg(v90) => {
          __rocq_reuse::rebuild(v64, Z::Zpos(mul_1(v61, v90)))
        },
      }
    },
  }
}

// Rocq: Corelib.BinNums.PosDef.Pos.div2
pub fn div2(p: Rc<positive>) -> Rc<positive> {
  let (v1, v2) = __rocq_reuse::reset(p, |__payload| Clone::clone(__payload));
  match v1 {
    positive::xI(v8) => {
      std::mem::drop(v2);
      v8
    },
    positive::xO(v12) => {
      std::mem::drop(v2);
      v12
    },
    positive::xH => {
      __rocq_reuse::rebuild(v2, positive::xH)
    },
  }
}

// Rocq: Corelib.BinNums.PosDef.Pos.div2_up
pub fn div2_up(p: Rc<positive>) -> Rc<positive> {
  let (v1, v2) = __rocq_reuse::reset(p, |__payload| Clone::clone(__payload));
  match v1 {
    positive::xI(v8) => {
      std::mem::drop(v2);
      succ_1(v8)
    },
    positive::xO(v16) => {
      std::mem::drop(v2);
      v16
    },
    positive::xH => {
      __rocq_reuse::rebuild(v2, positive::xH)
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.div2
pub fn div2_1(z: Rc<Z>) -> Rc<Z> {
  let (v1, v2) = __rocq_reuse::reset(z, |__payload| Clone::clone(__payload));
  match v1 {
    Z::Z0 => {
      __rocq_reuse::rebuild(v2, Z::Z0)
    },
    Z::Zpos(v13) => {
      let p = &v13;
      match &**p {
        positive::xI(_p0) => {
          __rocq_reuse::rebuild(v2, Z::Zpos(div2(v13)))
        },
        positive::xO(_p0_1) => {
          __rocq_reuse::rebuild(v2, Z::Zpos(div2(v13)))
        },
        positive::xH => {
          std::mem::drop(v13);
          __rocq_reuse::rebuild(v2, Z::Z0)
        },
      }
    },
    Z::Zneg(v51) => {
      __rocq_reuse::rebuild(v2, Z::Zneg(div2_up(v51)))
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.shiftl
// Variant: uncurried
pub fn shiftl(a_1: Rc<Z>, n: Rc<Z>) -> Rc<Z> {
  let (v2, v3) = __rocq_reuse::reset(n, |__payload| Clone::clone(__payload));
  match v2 {
    Z::Z0 => {
      std::mem::drop(v3);
      a_1
    },
    Z::Zpos(v11) => {
      let tmp = Rc::new(positive::xH);
      let tmp_1 = __rocq_reuse::rebuild(v3, Z::Zpos(Rc::new(positive::xO(tmp))));
      let callback: Rc<dyn Fn(Rc<Z>) -> Rc<Z>> = Rc::new({
        move |v32: Rc<Z>| -> Rc<Z> {
          let tmp_2 = Rc::clone(&tmp_1);
          mul_2(tmp_2, v32)
        }
      });
      iter::<Rc<Z>>(callback, a_1, v11)
    },
    Z::Zneg(v52) => {
      std::mem::drop(v3);
      let tmp_3: fn(Rc<Z>) -> Rc<Z> = div2_1;
      let tmp_4: Rc<dyn Fn(Rc<Z>) -> Rc<Z>> = Rc::new(tmp_3);
      iter::<Rc<Z>>(tmp_4, a_1, v52)
    },
  }
}

// Rocq: Closestpair1.closestpair1_implem.dal
// Variant: uncurried
pub fn dal(d: (Rc<Z>, Rc<Z>), e: Rc<Z>) -> Rc<Z> {
  let d_clone = Clone::clone(&d);
  shiftl(fst::<Rc<Z>, Rc<Z>>(d_clone), sub(snd::<Rc<Z>, Rc<Z>>(d), e))
}

// Rocq: Closestpair1.closestpair1_implem.dlt
// Variant: uncurried
pub fn dlt(a_1: (Rc<Z>, Rc<Z>), b_1: (Rc<Z>, Rc<Z>)) -> bool {
  let a_clone = Clone::clone(&a_1);
  let tmp = snd::<Rc<Z>, Rc<Z>>(a_clone);
  let b_clone = Clone::clone(&b_1);
  let e = min(tmp, snd::<Rc<Z>, Rc<Z>>(b_clone));
  let tmp_1 = a_1;
  let e_clone = Rc::clone(&e);
  ltb(dal(tmp_1, e_clone), dal(b_1, e))
}

// Rocq: Closestpair1.closestpair1_implem.dsub
// Variant: uncurried
pub fn dsub(a_1: (Rc<Z>, Rc<Z>), b_1: (Rc<Z>, Rc<Z>)) -> (Rc<Z>, Rc<Z>) {
  let a_clone = Clone::clone(&a_1);
  let tmp = snd::<Rc<Z>, Rc<Z>>(a_clone);
  let b_clone = Clone::clone(&b_1);
  let e = min(tmp, snd::<Rc<Z>, Rc<Z>>(b_clone));
  let tmp_1 = a_1;
  let e_clone = Rc::clone(&e);
  let tmp_2 = dal(tmp_1, e_clone);
  let tmp_3 = b_1;
  let e_clone_1 = Rc::clone(&e);
  (sub(tmp_2, dal(tmp_3, e_clone_1)), e)
}

// Rocq: Closestpair1.closestpair1_implem.zofi_rec
pub fn zofi_rec_1(i: Int63) -> Rc<Z> {
  zofi_rec(i, ())
}

// Rocq: Closestpair1.closestpair1_implem.zofi_rec (local: zofi_rec)
// Variant: uncurried, lifted
pub fn zofi_rec(i: Int63, _H: ()) -> Rc<Z> {
  let tmp = i == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      Rc::new(Z::Z0)
    },
    sumbool::right => {
      let r = zofi_rec(i / int63!(2), ());
      let tmp_1 = i % int63!(2);
      let tmp_2 = int63!(0);
      let bit = if tmp_1 == tmp_2 {
        Rc::new(Z::Z0)
      } else {
        let tmp_3 = Rc::new(positive::xH);
        Rc::new(Z::Zpos(tmp_3))
      };
      let tmp_4 = Rc::new(positive::xH);
      let tmp_5 = Rc::new(positive::xO(tmp_4));
      add_2(mul_2(Rc::new(Z::Zpos(tmp_5)), r), bit)
    },
  }
}

// Rocq: Closestpair1.closestpair1_implem.zofi
pub fn zofi(i: Int63) -> Rc<Z> {
  zofi_rec_1(i)
}

// Rocq: Closestpair1.closestpair1_implem.fex
pub fn fex(f: f64) -> (Rc<Z>, Rc<Z>) {
  let tmp = frshiftexp(f);
  match tmp {
    (v6, v8) => {
      let z = &v8;
      let m = zofi(rocq_float64::normfr_mantissa(v6));
      let tmp_1 = f64::from_bits(0u64);
      let tmp_2 = if rocq_float64::ltb(f, tmp_1) {
        opp(m)
      } else {
        m
      };
      let z_clone = Clone::clone(z);
      let tmp_3 = zofi(z_clone);
      let tmp_4 = Rc::new(positive::xH);
      let tmp_5 = Rc::new(positive::xO(tmp_4));
      let tmp_6 = Rc::new(positive::xO(tmp_5));
      let tmp_7 = Rc::new(positive::xO(tmp_6));
      let tmp_8 = Rc::new(positive::xO(tmp_7));
      let tmp_9 = Rc::new(positive::xI(tmp_8));
      let tmp_10 = Rc::new(positive::xI(tmp_9));
      let tmp_11 = Rc::new(positive::xO(tmp_10));
      let tmp_12 = Rc::new(positive::xI(tmp_11));
      let tmp_13 = Rc::new(positive::xO(tmp_12));
      let tmp_14 = Rc::new(positive::xI(tmp_13));
      let tmp_15 = Rc::new(positive::xO(tmp_14));
      (tmp_2, sub(tmp_3, Rc::new(Z::Zpos(tmp_15))))
    },
  }
}

// Rocq: Closestpair1.closestpair1_implem.dadd
// Variant: uncurried
pub fn dadd(a_1: (Rc<Z>, Rc<Z>), b_1: (Rc<Z>, Rc<Z>)) -> (Rc<Z>, Rc<Z>) {
  let a_clone = Clone::clone(&a_1);
  let tmp = snd::<Rc<Z>, Rc<Z>>(a_clone);
  let b_clone = Clone::clone(&b_1);
  let e = min(tmp, snd::<Rc<Z>, Rc<Z>>(b_clone));
  let tmp_1 = a_1;
  let e_clone = Rc::clone(&e);
  let tmp_2 = dal(tmp_1, e_clone);
  let tmp_3 = b_1;
  let e_clone_1 = Rc::clone(&e);
  (add_2(tmp_2, dal(tmp_3, e_clone_1)), e)
}

// Rocq: Closestpair1.closestpair1_implem.dmul
// Variant: uncurried
pub fn dmul(a_1: (Rc<Z>, Rc<Z>), b_1: (Rc<Z>, Rc<Z>)) -> (Rc<Z>, Rc<Z>) {
  let a_clone = Clone::clone(&a_1);
  let tmp = fst::<Rc<Z>, Rc<Z>>(a_clone);
  let b_clone = Clone::clone(&b_1);
  (mul_2(tmp, fst::<Rc<Z>, Rc<Z>>(b_clone)), add_2(snd::<Rc<Z>, Rc<Z>>(a_1), snd::<Rc<Z>, Rc<Z>>(b_1)))
}

// Rocq: Closestpair1.closestpair1_implem.dex
// Variant: borrowed, uncurried
pub fn dex(x: &Array<f64>, y: &Array<f64>, a_1: Int63, b_1: Int63) -> (Rc<Z>, Rc<Z>) {
  let a_2 = a_1;
  let b_2 = b_1;
  let dx = dsub(fex(x.get_cloned(a_2)), fex(x.get_cloned(b_2)));
  let dy = dsub(fex(y.get_cloned(a_2)), fex(y.get_cloned(b_2)));
  let dx_clone = Clone::clone(&dx);
  let tmp = dmul(dx_clone, dx);
  let dy_clone = Clone::clone(&dy);
  dadd(tmp, dmul(dy_clone, dy))
}

// Rocq: Closestpair1.closestpair1_implem.cand_step
// Variant: borrowed, uncurried
pub fn cand_step(x: &Array<f64>, y: &Array<f64>, P: &Array<Int63>, p: Int63, c: Int63, st: ((f64, Int63), Int63)) -> ((f64, Int63), Int63) {
  let p_1 = p;
  let c_1 = c;
  let st_1 = st;
  match &st_1 {
    (bj, p0) => {
      match bj {
        (bi, bf) => {
          let q = P.get_cloned(c_1);
          let f = fd(x, y, p_1, q);
          let tmp = tol(());
          let tmp_1 = rocq_float64::add(Clone::clone(bi), tmp);
          if rocq_float64::ltb(tmp_1, f) {
            st_1
          } else {
            let tmp_2 = dex(x, y, p_1, q);
            let tmp_3 = x;
            let tmp_4 = y;
            let bf_clone = Clone::clone(bf);
            let p0_clone = Clone::clone(p0);
            let tmp_5 = dex(tmp_3, tmp_4, bf_clone, p0_clone);
            if dlt(tmp_2, tmp_5) {
              std::mem::drop(st_1);
              ((f, p_1), q)
            } else {
              st_1
            }
          }
        },
      }
    },
  }
}

// Rocq: Closestpair1.closestpair1_implem.sweep_step
// Variant: borrowed, uncurried
pub fn sweep_step(x: &Array<f64>, y: &Array<f64>, K: &Array<Int63>, M: &Array<f64>, P: &Array<Int63>, n: Int63, a_1: Int63, st: ((f64, Int63), Int63)) -> ((f64, Int63), Int63) {
  let n_1 = n;
  let a_2 = a_1;
  let st_1 = st;
  let p = P.get_cloned(a_2);
  let tmp = K.get_cloned(p);
  let x_clone = Clone::clone(x);
  let K_clone = Clone::clone(K);
  let M_clone = Clone::clone(M);
  let P_clone = Clone::clone(P);
  let callback: Rc<dyn Fn(Int63, ((f64, Int63), Int63)) -> bool> = Rc::new({
    let __anf_capture_45 = p;
    move |v49: Int63, v50: ((f64, Int63), Int63)| -> bool {
      let x = &x_clone;
      let K = &K_clone;
      let M = &M_clone;
      let P = &P_clone;
      let tmp_1 = Clone::clone(&__anf_capture_45);
      let tmp_2 = Clone::clone(&tmp);
      cand_cont(x, K, M, P, tmp_1, tmp_2, v49, v50)
    }
  });
  let x_clone_1 = Clone::clone(x);
  let y_clone = Clone::clone(y);
  let P_clone_1 = Clone::clone(P);
  let callback_1: Rc<dyn Fn(Int63, ((f64, Int63), Int63)) -> ((f64, Int63), Int63)> = Rc::new({
    let __anf_capture_87 = p;
    move |v89: Int63, v90: ((f64, Int63), Int63)| -> ((f64, Int63), Int63) {
      let x = &x_clone_1;
      let y = &y_clone;
      let P = &P_clone_1;
      let tmp_3 = cand_step(x, y, P, Clone::clone(&__anf_capture_87), v89, v90);
      tmp_3
    }
  });
  loop_::<((f64, Int63), Int63)>(n_1, callback, callback_1, a_2 + int63!(1), st_1)
}

// Rocq: Closestpair1.closestpair1_implem.closestpair
// Variant: uncurried
pub fn closestpair(x: Array<f64>, y: Array<f64>) -> (Int63, Int63) {
  let n = x.length();
  if int63!(2) <= n {
    let s = rocq_float64::div(rocq_float64::of_uint63(n), cinit(()));
    let n1 = n - int63!(1);
    let callback: Rc<dyn Fn(Int63, Array<Int63>) -> bool> = Rc::new(move |_v39: Int63, v40: Array<Int63>| -> bool {
      std::mem::drop(v40);
      true
    });
    let x_clone = Clone::clone(&x);
    let callback_1: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
      move |v61: Int63, v62: Array<Int63>| -> Array<Int63> {
        let tmp = Clone::clone(&x_clone);
        let s_clone = Clone::clone(&s);
        let n1_clone = Clone::clone(&n1);
        key_step(tmp, s_clone, n1_clone, v61, v62)
      }
    });
    let tmp_1 = Array::<Int63>::make(n, int63!(0));
    let K = loop_::<Array<Int63>>(n, callback, callback_1, int63!(0), tmp_1);
    let callback_2: Rc<dyn Fn(Int63, Array<Int63>) -> bool> = Rc::new(move |_v101: Int63, v102: Array<Int63>| -> bool {
      std::mem::drop(v102);
      true
    });
    let K_clone = Clone::clone(&K);
    let callback_3: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
      move |v115: Int63, v116: Array<Int63>| -> Array<Int63> {
        let tmp_2 = Clone::clone(&K_clone);
        count_step(tmp_2, v115, v116)
      }
    });
    let tmp_3 = Array::<Int63>::make(n, int63!(0));
    let C = loop_::<Array<Int63>>(n, callback_2, callback_3, int63!(0), tmp_3);
    let callback_4: Rc<dyn Fn(Int63, (Array<Int63>, Int63)) -> bool> = Rc::new(move |_v151: Int63, v152: (Array<Int63>, Int63)| -> bool {
      std::mem::drop(v152);
      true
    });
    let tmp_4: fn(Int63, (Array<Int63>, Int63)) -> (Array<Int63>, Int63) = prefix_step;
    let tmp_5: Rc<dyn Fn(Int63, (Array<Int63>, Int63)) -> (Array<Int63>, Int63)> = Rc::new(tmp_4);
    let tmp_6 = loop_::<(Array<Int63>, Int63)>(n, callback_4, tmp_5, int63!(0), (C, int63!(0)));
    match tmp_6 {
      (v184, _v186) => {
        let callback_5: Rc<dyn Fn(Int63, (Array<Int63>, Array<Int63>)) -> bool> = Rc::new(move |_v190: Int63, v191: (Array<Int63>, Array<Int63>)| -> bool {
          std::mem::drop(v191);
          true
        });
        let K_clone_1 = Clone::clone(&K);
        let callback_6: Rc<dyn Fn(Int63, (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>)> = Rc::new({
          move |v204: Int63, v205: (Array<Int63>, Array<Int63>)| -> (Array<Int63>, Array<Int63>) {
            let K = &K_clone_1;
            let tmp_7 = place_step(K, v204, v205);
            tmp_7
          }
        });
        let tmp_8 = Array::<Int63>::make(n, int63!(0));
        let tmp_9 = loop_::<(Array<Int63>, Array<Int63>)>(n, callback_5, callback_6, int63!(0), (tmp_8, v184));
        match &tmp_9 {
          (a_1, _P) => {
            let callback_7: Rc<dyn Fn(Int63, Array<f64>) -> bool> = Rc::new(move |_v251: Int63, v252: Array<f64>| -> bool {
              std::mem::drop(v252);
              true
            });
            let x_clone_1 = Clone::clone(&x);
            let K_clone_2 = Clone::clone(&K);
            let callback_8: Rc<dyn Fn(Int63, Array<f64>) -> Array<f64>> = Rc::new({
              move |v270: Int63, v271: Array<f64>| -> Array<f64> {
                let tmp_10 = Clone::clone(&x_clone_1);
                let tmp_11 = Clone::clone(&K_clone_2);
                min_step(tmp_10, tmp_11, v270, v271)
              }
            });
            let tmp_12 = Array::<f64>::make(n, cinit(()));
            let M = loop_::<Array<f64>>(n, callback_7, callback_8, int63!(0), tmp_12);
            let callback_9: Rc<dyn Fn(Int63, ((f64, Int63), Int63)) -> bool> = Rc::new(move |_v312: Int63, v313: ((f64, Int63), Int63)| -> bool {
              std::mem::drop(v313);
              true
            });
            let x_clone_2 = Clone::clone(&x);
            let y_clone = Clone::clone(&y);
            let a_clone = Clone::clone(a_1);
            std::mem::drop(tmp_9);
            let callback_10: Rc<dyn Fn(Int63, ((f64, Int63), Int63)) -> ((f64, Int63), Int63)> = Rc::new({
              let __anf_capture_339 = K;
              let __anf_capture_345 = n;
              move |v347: Int63, v348: ((f64, Int63), Int63)| -> ((f64, Int63), Int63) {
                let x = &x_clone_2;
                let y = &y_clone;
                let K = &__anf_capture_339;
                let M = &M;
                let a_1 = &a_clone;
                let tmp_13 = sweep_step(x, y, K, M, a_1, Clone::clone(&__anf_capture_345), v347, v348);
                tmp_13
              }
            });
            let tmp_14 = loop_::<((f64, Int63), Int63)>(n, callback_9, callback_10, int63!(0), ((fd_owned(x, y, int63!(0), int63!(1)), int63!(0)), int63!(1)));
            match tmp_14 {
              (v410, v412) => {
                match v410 {
                  (_v415, v417) => {
                    (v417, v412)
                  },
                }
              },
            }
          },
        }
      },
    }
  } else {
    std::mem::drop(x);
    std::mem::drop(y);
    (int63!(0), int63!(1))
  }
}
