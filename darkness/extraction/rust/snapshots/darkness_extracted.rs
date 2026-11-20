#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

pub struct bst {
  pub bd: Array<Int63>,
  pub bp: Array<Int63>,
  pub bq: Array<Int63>,
  pub bt: Int63,
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

pub type uint = Int63;

// Rocq: Darkness.darkness_implem.M48
pub fn M48() -> Int63 {
  int63!(281474976710656)
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

// Rocq: Darkness.darkness_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Darkness.darkness_implem.gloop
// Variant: uncurried
pub fn gloop_1<A: Clone + 'static>(C: Int63, n: Int63, f: Rc<dyn Fn(Int63, Int63, Int63, A) -> A>, u: Int63, i: Int63, j: Int63, a_1: A) -> A {
  gloop::<A>((), C, n, f, u, i, j, a_1, ())
}

// Rocq: Darkness.darkness_implem.gloop (local: gloop)
// Variant: uncurried, lifted
pub fn gloop<A: Clone + 'static>(_A_1: (), C: Int63, n: Int63, f: Rc<dyn Fn(Int63, Int63, Int63, A) -> A>, u: Int63, i: Int63, j: Int63, a_1: A, _H: ()) -> A {
  let tmp = u < n;
  match bdec(tmp) {
    sumbool::left => {
      let f_ref: &Rc<dyn Fn(Int63, Int63, Int63, A) -> A> = &f;
      let a_ = f_ref(u, i, j, a_1);
      let j1 = j + int63!(1);
      let e = j1 == C;
      let tmp_1 = ();
      let tmp_2 = u + int63!(1);
      let tmp_3 = if e {
        i + int63!(1)
      } else {
        i
      };
      let tmp_4 = if e {
        int63!(0)
      } else {
        j1
      };
      gloop::<A>(tmp_1, C, n, f, tmp_2, tmp_3, tmp_4, a_, ())
    },
    sumbool::right => {
      std::mem::drop(f);
      a_1
    },
  }
}

// Rocq: Darkness.darkness_implem.grid_fold
// Variant: uncurried
pub fn grid_fold<A: Clone + 'static>(C: Int63, n: Int63, f: Rc<dyn Fn(Int63, Int63, Int63, A) -> A>, a_1: A) -> A {
  gloop_1::<A>(C, n, f, int63!(0), int63!(0), int63!(0), a_1)
}

// Rocq: Darkness.darkness_implem.flat
// Variant: uncurried
pub fn flat(xg: Array<Array<Int63>>, C: Int63, n: Int63) -> Array<Int63> {
  let callback: Rc<dyn Fn(Int63, Int63, Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
    move |u: Int63, i: Int63, j: Int63, a_1: Array<Int63>| -> Array<Int63> {
      let xg = &xg;
      let xg_clone = Clone::clone(xg);
      let tmp = &xg_clone;
      let tmp_1 = tmp.get_cloned(i);
      std::mem::drop(xg_clone);
      let tmp_2 = tmp_1.get_cloned(j);
      std::mem::drop(tmp_1);
      a_1.set(u, tmp_2)
    }
  });
  let tmp_3 = Array::<Int63>::make(n, int63!(0));
  grid_fold::<Array<Int63>>(C, n, callback, tmp_3)
}

// Rocq: Darkness.darkness_implem.absdiff
// Variant: uncurried
pub fn absdiff(a_1: Int63, b_1: Int63) -> Int63 {
  if a_1 < b_1 {
    b_1 - a_1
  } else {
    a_1 - b_1
  }
}

// Rocq: Darkness.darkness_implem.denom
// Variant: uncurried
pub fn denom(hh: Int63, i: Int63, j: Int63, i_: Int63, j_: Int63) -> Int63 {
  let di = absdiff(i, i_);
  let dj = absdiff(j, j_);
  di * di + dj * dj + hh
}

// Rocq: Darkness.darkness_implem.lo_sum
// Variant: borrowed, uncurried
pub fn lo_sum(s: &Array<Int63>, C: Int63, n: Int63, hh: Int63, i: Int63, j: Int63) -> Int63 {
  let C_1 = C;
  let n_1 = n;
  let s_clone = Clone::clone(s);
  let callback: Rc<dyn Fn(Int63, Int63, Int63, Int63) -> Int63> = Rc::new({
    move |u: Int63, i_: Int63, j_: Int63, acc: Int63| -> Int63 {
      let s = &s_clone;
      let hh = &hh;
      let i = &i;
      let j = &j;
      let tmp = __rocq_global_789 * s.get_cloned(u);
      let hh_clone = Clone::clone(hh);
      let i_clone = Clone::clone(i);
      let j_clone = Clone::clone(j);
      acc + tmp / denom(hh_clone, i_clone, j_clone, i_, j_)
    }
  });
  grid_fold::<Int63>(C_1, n_1, callback, int63!(0))
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

// Rocq: Darkness.darkness_implem.zofint_aux
pub fn zofint_aux_1(x: Int63) -> Rc<Z> {
  zofint_aux(x, ())
}

// Rocq: Darkness.darkness_implem.zofint_aux (local: zofint_aux)
// Variant: uncurried, lifted
pub fn zofint_aux(x: Int63, _H: ()) -> Rc<Z> {
  let tmp = x == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      Rc::new(Z::Z0)
    },
    sumbool::right => {
      let r = zofint_aux(x / int63!(2), ());
      let tmp_1 = x % int63!(2);
      if tmp_1 == int63!(0) {
        let tmp_2 = Rc::new(positive::xH);
        let tmp_3 = Rc::new(positive::xO(tmp_2));
        mul_2(Rc::new(Z::Zpos(tmp_3)), r)
      } else {
        let tmp_4 = Rc::new(positive::xH);
        let tmp_5 = Rc::new(positive::xO(tmp_4));
        let tmp_6 = mul_2(Rc::new(Z::Zpos(tmp_5)), r);
        let tmp_7 = Rc::new(positive::xH);
        add_2(tmp_6, Rc::new(Z::Zpos(tmp_7)))
      }
    },
  }
}

// Rocq: Darkness.darkness_implem.zofint
pub fn zofint(x: Int63) -> Rc<Z> {
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
pub fn exact_sum(s: &Array<Int63>, C: Int63, n: Int63, hh: Int63, i: Int63, j: Int63) -> (Rc<Z>, Rc<Z>) {
  let C_1 = C;
  let n_1 = n;
  let s_clone = Clone::clone(s);
  let callback: Rc<dyn Fn(Int63, Int63, Int63, (Rc<Z>, Rc<Z>)) -> (Rc<Z>, Rc<Z>)> = Rc::new({
    move |u: Int63, i_: Int63, j_: Int63, pq: (Rc<Z>, Rc<Z>)| -> (Rc<Z>, Rc<Z>) {
      let hh = &hh;
      let i = &i;
      let j = &j;
      let s = &s_clone;
      let d = zofint(denom(Clone::clone(hh), Clone::clone(i), Clone::clone(j), i_, j_));
      let tmp = s.get_cloned(u);
      let sv = zofint(tmp);
      let pq_clone = Clone::clone(&pq);
      let tmp_1 = fst::<Rc<Z>, Rc<Z>>(pq_clone);
      let d_clone = Rc::clone(&d);
      let tmp_2 = mul_2(tmp_1, d_clone);
      let pq_clone_1 = Clone::clone(&pq);
      (add_2(tmp_2, mul_2(sv, snd::<Rc<Z>, Rc<Z>>(pq_clone_1))), mul_2(snd::<Rc<Z>, Rc<Z>>(pq), d))
    }
  });
  let tmp_3 = Rc::new(Z::Z0);
  let tmp_4 = Rc::new(positive::xH);
  grid_fold::<(Rc<Z>, Rc<Z>)>(C_1, n_1, callback, (tmp_3, Rc::new(Z::Zpos(tmp_4))))
}

// Rocq: Corelib.BinNums.IntDef.Z.leb
// Variant: uncurried
pub fn leb(x: Rc<Z>, y: Rc<Z>) -> bool {
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
pub fn lit_cell(s: &Array<Int63>, C: Int63, n: Int63, b_1: Int63, hh: Int63, i: Int63, j: Int63) -> bool {
  let C_1 = C;
  let n_1 = n;
  let b_2 = b_1;
  let hh_1 = hh;
  let i_1 = i;
  let j_1 = j;
  let lo = lo_sum(s, C_1, n_1, hh_1, i_1, j_1);
  let mb = __rocq_global_789 * b_2;
  if mb <= lo {
    true
  } else {
    let tmp = lo + n_1;
    if tmp < mb {
      false
    } else {
      let pq = exact_sum(s, C_1, n_1, hh_1, i_1, j_1);
      let tmp_1 = zofint(b_2);
      let pq_clone = Clone::clone(&pq);
      leb(mul_2(tmp_1, snd::<Rc<Z>, Rc<Z>>(pq_clone)), fst::<Rc<Z>, Rc<Z>>(pq))
    }
  }
}

// Rocq: Darkness.darkness_implem.lit_arr
// Variant: uncurried
pub fn lit_arr(s: Array<Int63>, C: Int63, n: Int63, b_1: Int63, hh: Int63) -> Array<bool> {
  let callback: Rc<dyn Fn(Int63, Int63, Int63, Array<bool>) -> Array<bool>> = Rc::new({
    let __anf_capture_19 = C;
    let __anf_capture_21 = n;
    move |u: Int63, i: Int63, j: Int63, a_1: Array<bool>| -> Array<bool> {
      let tmp = lit_cell(&s, Clone::clone(&__anf_capture_19), Clone::clone(&__anf_capture_21), Clone::clone(&b_1), Clone::clone(&hh), i, j);
      a_1.set(u, tmp)
    }
  });
  let tmp_1 = Array::<bool>::make(n, false);
  grid_fold::<Array<bool>>(C, n, callback, tmp_1)
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
pub fn capf(x: bool, y: bool) -> Int63 {
  if andb(x, y) {
    int63!(43)
  } else {
    int63!(11)
  }
}

// Rocq: Darkness.darkness_implem.init_res
// Variant: uncurried
pub fn init_res(lt: Array<bool>, C: Int63, n: Int63) -> Array<Int63> {
  let callback: Rc<dyn Fn(Int63, Int63, Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
    let __anf_capture_9 = C;
    move |u: Int63, _i: Int63, _j: Int63, r: Array<Int63>| -> Array<Int63> {
      let C = &__anf_capture_9;
      let c1 = capf(lt.get_cloned(u), lt.get_cloned(u + int63!(1)));
      let tmp = lt.get_cloned(u);
      let tmp_1 = lt.get_cloned(u + Clone::clone(C));
      let c2 = capf(tmp, tmp_1);
      r.set(int63!(2) * u, c1).set(int63!(2) * u + int63!(1), c2)
    }
  });
  let tmp_2 = int63!(2) * n;
  grid_fold::<Array<Int63>>(C, n, callback, Array::<Int63>::make(tmp_2, int63!(0)))
}

// Rocq: Darkness.darkness_implem.bt
pub fn bt_owned(b_1: Rc<bst>) -> Int63 {
  let b_bt_clone = Clone::clone(&b_1.bt);
  std::mem::drop(b_1);
  b_bt_clone
}

// Rocq: Darkness.darkness_implem.bt
// Variant: borrowed
pub fn bt(b_1: &Rc<bst>) -> Int63 {
  let tmp = b_1;
  Clone::clone(&tmp.bt)
}

// Rocq: Darkness.darkness_implem.bq
pub fn bq(b_1: Rc<bst>) -> Array<Int63> {
  let b_bq_clone = Clone::clone(&b_1.bq);
  std::mem::drop(b_1);
  b_bq_clone
}

// Rocq: Darkness.darkness_implem.bd
pub fn bd(b_1: Rc<bst>) -> Array<Int63> {
  let b_bd_clone = Clone::clone(&b_1.bd);
  std::mem::drop(b_1);
  b_bd_clone
}

// Rocq: Darkness.darkness_implem.nbr
// Variant: uncurried
pub fn nbr(C: Int63, p: Int63, d: Int63) -> Int63 {
  if d == int63!(0) {
    p + int63!(1)
  } else {
    if d == int63!(1) {
      p - int63!(1)
    } else {
      if d == int63!(2) {
        p + C
      } else {
        p - C
      }
    }
  }
}

// Rocq: Darkness.darkness_implem.slot
// Variant: uncurried
pub fn slot(C: Int63, p: Int63, d: Int63) -> Int63 {
  if d == int63!(0) {
    int63!(2) * p
  } else {
    if d == int63!(1) {
      int63!(2) * (p - int63!(1))
    } else {
      if d == int63!(2) {
        int63!(2) * p + int63!(1)
      } else {
        int63!(2) * (p - C) + int63!(1)
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
pub fn fwd(d: Int63) -> bool {
  orb(d == int63!(0), d == int63!(2))
}

// Rocq: Darkness.darkness_implem.resid
// Variant: uncurried
pub fn resid(lt: Array<bool>, res: Array<Int63>, C: Int63, p: Int63, d: Int63) -> Int63 {
  let k = slot(C, p, d);
  if fwd(d) {
    std::mem::drop(lt);
    let tmp = res.get_cloned(k);
    std::mem::drop(res);
    tmp
  } else {
    let tmp_1 = int63!(2);
    let tmp_2 = lt.get_cloned(p);
    let tmp_3 = lt.get_cloned(nbr(C, p, d));
    std::mem::drop(lt);
    let tmp_4 = tmp_1 * capf(tmp_2, tmp_3);
    let tmp_5 = res.get_cloned(k);
    std::mem::drop(res);
    tmp_4 - tmp_5
  }
}

// Rocq: Darkness.darkness_implem.bp
pub fn bp(b_1: Rc<bst>) -> Array<Int63> {
  let b_bp_clone = Clone::clone(&b_1.bp);
  std::mem::drop(b_1);
  b_bp_clone
}

// Rocq: Darkness.darkness_implem.visit
// Variant: uncurried
pub fn visit(lt: Array<bool>, res: Array<Int63>, C: Int63, st: Rc<bst>, v: Int63, dv: Int63, d: Int63, ok: bool) -> Rc<bst> {
  if ok {
    let w = nbr(C, v, d);
    let tmp = resid(lt, res, C, v, d);
    if int63!(0) < tmp {
      let st_clone = Rc::clone(&st);
      let tmp_1 = bd(st_clone);
      let tmp_2 = tmp_1.get_cloned(w);
      if tmp_2 == int63!(0) {
        std::mem::drop(tmp_1);
        let st_clone_1 = Rc::clone(&st);
        let tmp_3 = bd(st_clone_1).set(w, dv + int63!(1));
        let st_clone_2 = Rc::clone(&st);
        let tmp_4 = bp(st_clone_2).set(w, d);
        let st_clone_3 = Rc::clone(&st);
        let tmp_5 = bq(st_clone_3);
        let tmp_6 = bt(&st);
        Rc::new(bst { bd: tmp_3, bp: tmp_4, bq: tmp_5.set(tmp_6, w), bt: bt_owned(st) + int63!(1) })
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
pub fn bfs_loop_1(lt: Array<bool>, res: Array<Int63>, C: Int63, n: Int63, head: Int63, st: Rc<bst>) -> Rc<bst> {
  bfs_loop(lt, res, C, n, head, st, ())
}

// Rocq: Darkness.darkness_implem.bfs_loop (local: bfs_loop)
// Variant: uncurried, lifted
pub fn bfs_loop(lt: Array<bool>, res: Array<Int63>, C: Int63, n: Int63, head: Int63, st: Rc<bst>, _H: ()) -> Rc<bst> {
  let tmp = head < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = bt(&st);
      if head < tmp_1 {
        let st_clone = Rc::clone(&st);
        let tmp_2 = bq(st_clone);
        let v = tmp_2.get_cloned(head);
        std::mem::drop(tmp_2);
        let st_clone_1 = Rc::clone(&st);
        let tmp_3 = bd(st_clone_1);
        let dv = tmp_3.get_cloned(v);
        std::mem::drop(tmp_3);
        let j = v % C;
        let tmp_4 = j + int63!(1) < C;
        let lt_clone = Clone::clone(&lt);
        let res_clone = Clone::clone(&res);
        let st1 = visit(lt_clone, res_clone, C, st, v, dv, int63!(0), tmp_4);
        let tmp_5 = int63!(0) < j;
        let lt_clone_1 = Clone::clone(&lt);
        let res_clone_1 = Clone::clone(&res);
        let st2 = visit(lt_clone_1, res_clone_1, C, st1, v, dv, int63!(1), tmp_5);
        let tmp_6 = v + C < n;
        let lt_clone_2 = Clone::clone(&lt);
        let res_clone_2 = Clone::clone(&res);
        let st3 = visit(lt_clone_2, res_clone_2, C, st2, v, dv, int63!(2), tmp_6);
        let tmp_7 = C <= v;
        let lt_clone_3 = Clone::clone(&lt);
        let res_clone_3 = Clone::clone(&res);
        let st4 = visit(lt_clone_3, res_clone_3, C, st3, v, dv, int63!(3), tmp_7);
        bfs_loop(lt, res, C, n, head + int63!(1), st4, ())
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
pub fn root_step(lt: Array<bool>, u: Int63, _i: Int63, _j: Int63, st: Rc<bst>) -> Rc<bst> {
  let tmp = lt.get_cloned(u);
  if tmp {
    std::mem::drop(lt);
    st
  } else {
    std::mem::drop(lt);
    let st_clone = Rc::clone(&st);
    let tmp_1 = bd(st_clone).set(u, int63!(1));
    let st_clone_1 = Rc::clone(&st);
    let tmp_2 = bp(st_clone_1).set(u, int63!(4));
    let st_clone_2 = Rc::clone(&st);
    let tmp_3 = bq(st_clone_2);
    let tmp_4 = bt(&st);
    Rc::new(bst { bd: tmp_1, bp: tmp_2, bq: tmp_3.set(tmp_4, u), bt: bt_owned(st) + int63!(1) })
  }
}

// Rocq: Darkness.darkness_implem.roots
// Variant: uncurried
pub fn roots(lt: Array<bool>, C: Int63, n: Int63) -> Rc<bst> {
  let callback: Rc<dyn Fn(Int63, Int63, Int63, Rc<bst>) -> Rc<bst>> = Rc::new({
    move |v9: Int63, v10: Int63, v11: Int63, v12: Rc<bst>| -> Rc<bst> {
      let lt_clone = Clone::clone(&lt);
      root_step(lt_clone, v9, v10, v11, v12)
    }
  });
  let tmp = Array::<Int63>::make(n, int63!(0));
  let tmp_1 = Array::<Int63>::make(n, int63!(0));
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  grid_fold::<Rc<bst>>(C, n, callback, Rc::new(bst { bd: tmp, bp: tmp_1, bq: tmp_2, bt: int63!(0) }))
}

// Rocq: Darkness.darkness_implem.bfs
// Variant: uncurried
pub fn bfs(lt: Array<bool>, res: Array<Int63>, C: Int63, n: Int63) -> Rc<bst> {
  let lt_clone = Clone::clone(&lt);
  let tmp = roots(lt_clone, C, n);
  bfs_loop_1(lt, res, C, n, int63!(0), tmp)
}

// Rocq: Darkness.darkness_implem.is_border
// Variant: uncurried
pub fn is_border(R: Int63, C: Int63, i: Int63, j: Int63) -> bool {
  let tmp = orb(i == int63!(0), i == R - int63!(1));
  let tmp_1 = orb(tmp, j == int63!(0));
  orb(tmp_1, j == C - int63!(1))
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b_1: bool) -> bool {
  if b_1 {
    false
  } else {
    true
  }
}

// Rocq: Darkness.darkness_implem.fb_step
// Variant: borrowed, uncurried
pub fn fb_step(dist: &Array<Int63>, R: Int63, C: Int63, n: Int63, u: Int63, i: Int63, j: Int63, acc: Int63) -> Int63 {
  let R_1 = R;
  let C_1 = C;
  let n_1 = n;
  let u_1 = u;
  let i_1 = i;
  let j_1 = j;
  let acc_1 = acc;
  let tmp = andb(is_border(R_1, C_1, i_1, j_1), negb(dist.get_cloned(u_1) == int63!(0)));
  let tmp_1 = orb(acc_1 == n_1, dist.get_cloned(u_1) < dist.get_cloned(acc_1));
  if andb(tmp, tmp_1) {
    u_1
  } else {
    acc_1
  }
}

// Rocq: Darkness.darkness_implem.find_border
// Variant: uncurried
pub fn find_border(dist: Array<Int63>, R: Int63, C: Int63, n: Int63) -> Int63 {
  let callback: Rc<dyn Fn(Int63, Int63, Int63, Int63) -> Int63> = Rc::new({
    let __anf_capture_18 = C;
    let __anf_capture_20 = n;
    move |v22: Int63, v23: Int63, v24: Int63, v25: Int63| -> Int63 {
      let dist = &dist;
      let R_clone = Clone::clone(&R);
      let tmp = Clone::clone(&__anf_capture_18);
      let tmp_1 = Clone::clone(&__anf_capture_20);
      fb_step(dist, R_clone, tmp, tmp_1, v22, v23, v24, v25)
    }
  });
  grid_fold::<Int63>(C, n, callback, n)
}

// Rocq: Darkness.darkness_implem.opp
pub fn opp(d: Int63) -> Int63 {
  if d == int63!(0) {
    int63!(1)
  } else {
    if d == int63!(1) {
      int63!(0)
    } else {
      if d == int63!(2) {
        int63!(3)
      } else {
        int63!(2)
      }
    }
  }
}

// Rocq: Darkness.darkness_implem.tmin
// Variant: uncurried
pub fn tmin_1(lt: Array<bool>, res: Array<Int63>, C: Int63, par: Array<Int63>, dist: Array<Int63>, v: Int63, dl: Int63) -> Int63 {
  tmin(lt, res, C, par, dist, v, dl, ())
}

// Rocq: Darkness.darkness_implem.tmin (local: tmin)
// Variant: uncurried, lifted
pub fn tmin(lt: Array<bool>, res: Array<Int63>, C: Int63, par: Array<Int63>, dist: Array<Int63>, v: Int63, dl: Int63, _H: ()) -> Int63 {
  let d = par.get_cloned(v);
  if d < int63!(4) {
    let p = nbr(C, v, opp(d));
    let tmp = dist.get_cloned(p);
    let tmp_1 = dist.get_cloned(v);
    let tmp_2 = tmp < tmp_1;
    match bdec(tmp_2) {
      sumbool::left => {
        let lt_clone = Clone::clone(&lt);
        let res_clone = Clone::clone(&res);
        let r = resid(lt_clone, res_clone, C, p, d);
        let tmp_3 = if r < dl {
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
pub fn aug(res: Array<Int63>, C: Int63, p: Int63, d: Int63, dl: Int63) -> Array<Int63> {
  let k = slot(C, p, d);
  if fwd(d) {
    let tmp = res.get_cloned(k);
    res.set(k, tmp - dl)
  } else {
    let tmp_1 = res.get_cloned(k);
    res.set(k, tmp_1 + dl)
  }
}

// Rocq: Darkness.darkness_implem.tapp
// Variant: uncurried
pub fn tapp_1(C: Int63, par: Array<Int63>, dist: Array<Int63>, dl: Int63, v: Int63, res: Array<Int63>) -> Array<Int63> {
  tapp(C, par, dist, dl, v, res, ())
}

// Rocq: Darkness.darkness_implem.tapp (local: tapp)
// Variant: uncurried, lifted
pub fn tapp(C: Int63, par: Array<Int63>, dist: Array<Int63>, dl: Int63, v: Int63, res: Array<Int63>, _H: ()) -> Array<Int63> {
  let d = par.get_cloned(v);
  if d < int63!(4) {
    let p = nbr(C, v, opp(d));
    let tmp = dist.get_cloned(p);
    let tmp_1 = dist.get_cloned(v);
    let tmp_2 = tmp < tmp_1;
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
pub fn flow_loop_1(lt: Array<bool>, R: Int63, C: Int63, n: Int63, B: Int63, res: Array<Int63>, F: Int63) -> Int63 {
  flow_loop(lt, R, C, n, B, res, F, ())
}

// Rocq: Darkness.darkness_implem.flow_loop (local: flow_loop)
// Variant: uncurried, lifted
pub fn flow_loop(lt: Array<bool>, R: Int63, C: Int63, n: Int63, B: Int63, res: Array<Int63>, F: Int63, _H: ()) -> Int63 {
  let lt_clone = Clone::clone(&lt);
  let res_clone = Clone::clone(&res);
  let st = bfs(lt_clone, res_clone, C, n);
  let st_clone = Rc::clone(&st);
  let w = find_border(bd(st_clone), R, C, n);
  if w == n {
    std::mem::drop(st);
    std::mem::drop(lt);
    std::mem::drop(res);
    F
  } else {
    let st_clone_1 = Rc::clone(&st);
    let tmp = bp(st_clone_1);
    let st_clone_2 = Rc::clone(&st);
    let tmp_1 = bd(st_clone_2);
    let lt_clone_1 = Clone::clone(&lt);
    let res_clone_1 = Clone::clone(&res);
    let dl = tmin_1(lt_clone_1, res_clone_1, C, tmp, tmp_1, w, int63!(1000));
    let st_clone_3 = Rc::clone(&st);
    let res_ = tapp_1(C, bp(st_clone_3), bd(st), dl, w, res);
    let F_ = F + dl;
    let tmp_2 = andb(F < F_, F_ <= B);
    match bdec(tmp_2) {
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
pub fn darkness_impl(xb: Int63, xh: Int63, xg: Array<Array<Int63>>) -> Int63 {
  let R = xg.length();
  let xg_clone = Clone::clone(&xg);
  let tmp = &xg_clone;
  let tmp_1 = tmp.get_cloned(int63!(0));
  std::mem::drop(xg_clone);
  let C = tmp_1.length();
  std::mem::drop(tmp_1);
  let n = R * C;
  let s = flat(xg, C, n);
  let lt = lit_arr(s, C, n, xb, xh * xh);
  let lt_clone = Clone::clone(&lt);
  let res = init_res(lt_clone, C, n);
  let B = int63!(86) * n;
  flow_loop_1(lt, R, C, n, B, res, int63!(0))
}
const __rocq_global_789: Int63 = int63!(281474976710656);