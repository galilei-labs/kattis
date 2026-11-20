#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;
#[allow(unused_imports)] use rocq_bigint::BigInt;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::PositiveTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::NaturalTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::IntegerTag>; };

// Rocq: Bigfactoring.bigfactoring_implem.CAP
pub fn CAP() -> u64 {
  128u64
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_rmax
pub fn rho_rmax() -> u64 {
  33554432u64
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_m
pub fn rho_m() -> u64 {
  128u64
}

// Rocq: Corelib.BinNums.IntDef.Z.add
// Variant: uncurried
pub fn add(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::add(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.sub
// Variant: uncurried
pub fn sub(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::sub(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.ltb
// Variant: uncurried
pub fn ltb(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::lt(v0, v1)
}

// Rocq: Bigfactoring.bigfactoring_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.mul
// Variant: uncurried
pub fn mul_owned(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::mul(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.mul
// Variant: borrowed, uncurried
pub fn mul(v0: &Rc<BigInt>, v1: &Rc<BigInt>) -> Rc<BigInt> {
  let tmp = Rc::clone(v0);
  let tmp_1 = Rc::clone(v1);
  rocq_bigint::mul(tmp, tmp_1)
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

// Rocq: Corelib.BinNums.IntDef.Z.eqb
// Variant: uncurried
pub fn eqb(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::equal(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.leb
// Variant: uncurried
pub fn leb(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::le(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.modulo
// Variant: uncurried
pub fn modulo(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::modulo(v0, v1)
}

// Rocq: Bigfactoring.bigfactoring_implem.dguard
// Variant: uncurried
pub fn dguard(m: Rc<BigInt>, d: Rc<BigInt>) -> bool {
  let tmp = rocq_bigint::one();
  let tmp_1 = rocq_bigint::identity(tmp);
  let d_clone = Rc::clone(&d);
  let tmp_2 = ltb(tmp_1, d_clone);
  let tmp_3 = rocq_bigint::zero();
  let m_clone = Rc::clone(&m);
  let tmp_4 = andb(tmp_2, ltb(tmp_3, m_clone));
  let tmp_5 = modulo(m, d);
  let tmp_6 = rocq_bigint::zero();
  andb(tmp_4, eqb(tmp_5, tmp_6))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add_1(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Bigfactoring.bigfactoring_implem.push
// Variant: uncurried
pub fn push(acc: Rc<Array<Rc<BigInt>>>, cnt: u64, p: Rc<BigInt>) -> (Rc<Array<Rc<BigInt>>>, u64) {
  let tmp = rocq_array::set::<Rc<BigInt>>(acc, cnt, p);
  (tmp, add_1(cnt, 1u64))
}

// Rocq: Corelib.BinNums.IntDef.Z.div
// Variant: uncurried
pub fn div(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::div(v0, v1)
}

// Rocq: Bigfactoring.bigfactoring_implem.divout
// Variant: uncurried
pub fn divout_1(m: Rc<BigInt>, d: Rc<BigInt>, acc: Rc<Array<Rc<BigInt>>>, cnt: u64) -> ((Rc<BigInt>, Rc<Array<Rc<BigInt>>>), u64) {
  divout(m, d, acc, cnt, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.divout (local: divout)
// Variant: uncurried, lifted
pub fn divout(m: Rc<BigInt>, d: Rc<BigInt>, acc: Rc<Array<Rc<BigInt>>>, cnt: u64, _H: ()) -> ((Rc<BigInt>, Rc<Array<Rc<BigInt>>>), u64) {
  let m_clone = Rc::clone(&m);
  let d_clone = Rc::clone(&d);
  let tmp = dguard(m_clone, d_clone);
  match bdec(tmp) {
    sumbool::left => {
      let d_clone_1 = Rc::clone(&d);
      let tmp_1 = push(acc, cnt, d_clone_1);
      match tmp_1 {
        (v28, v30) => {
          let d_clone_2 = Rc::clone(&d);
          let tmp_2 = div(m, d_clone_2);
          divout(tmp_2, d, v28, v30, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(d);
      ((m, acc), cnt)
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.trial
// Variant: uncurried
pub fn trial_1(B: Rc<BigInt>, m: Rc<BigInt>, d: Rc<BigInt>, acc: Rc<Array<Rc<BigInt>>>, cnt: u64) -> (((Rc<BigInt>, Rc<BigInt>), Rc<Array<Rc<BigInt>>>), u64) {
  trial(B, m, d, acc, cnt, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.trial (local: trial)
// Variant: uncurried, lifted
pub fn trial(B: Rc<BigInt>, m: Rc<BigInt>, d: Rc<BigInt>, acc: Rc<Array<Rc<BigInt>>>, cnt: u64, _H: ()) -> (((Rc<BigInt>, Rc<BigInt>), Rc<Array<Rc<BigInt>>>), u64) {
  let d_clone = Rc::clone(&d);
  let B_clone = Rc::clone(&B);
  let tmp = ltb(d_clone, B_clone);
  match bdec(tmp) {
    sumbool::left => {
      let d_clone_1 = Rc::clone(&d);
      let d_clone_2 = Rc::clone(&d);
      let tmp_1 = mul_owned(d_clone_1, d_clone_2);
      let m_clone = Rc::clone(&m);
      if ltb(m_clone, tmp_1) {
        std::mem::drop(B);
        (((m, d), acc), cnt)
      } else {
        let d_clone_3 = Rc::clone(&d);
        let tmp_2 = divout_1(m, d_clone_3, acc, cnt);
        match tmp_2 {
          (v68, v70) => {
            match v68 {
              (v73, v75) => {
                let tmp_3 = rocq_bigint::one();
                let tmp_4 = rocq_bigint::identity(tmp_3);
                let tmp_5 = add(d, tmp_4);
                trial(B, v73, tmp_5, v75, v70, ())
              },
            }
          },
        }
      }
    },
    sumbool::right => {
      std::mem::drop(B);
      (((m, d), acc), cnt)
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.B0
pub fn B0(_v0: ()) -> Rc<BigInt> {
  let tmp = rocq_bigint::one();
  let tmp_1 = rocq_bigint::twice_plus_one(tmp);
  let tmp_2 = rocq_bigint::twice_plus_one(tmp_1);
  let tmp_3 = rocq_bigint::twice_plus_one(tmp_2);
  let tmp_4 = rocq_bigint::twice_plus_one(tmp_3);
  let tmp_5 = rocq_bigint::twice(tmp_4);
  let tmp_6 = rocq_bigint::twice_plus_one(tmp_5);
  let tmp_7 = rocq_bigint::twice(tmp_6);
  let tmp_8 = rocq_bigint::twice(tmp_7);
  let tmp_9 = rocq_bigint::twice(tmp_8);
  rocq_bigint::identity(tmp_9)
}

// Rocq: Corelib.BinNums.IntDef.Z.even
pub fn even(v0: Rc<BigInt>) -> bool {
  rocq_bigint::even(v0)
}

// Rocq: Bigfactoring.bigfactoring_implem.strip
// Variant: uncurried
pub fn strip_1(d: Rc<BigInt>, s: u64) -> (Rc<BigInt>, u64) {
  strip(d, s, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.strip (local: strip)
// Variant: uncurried, lifted
pub fn strip(d: Rc<BigInt>, s: u64, _H: ()) -> (Rc<BigInt>, u64) {
  let tmp = rocq_bigint::zero();
  let d_clone = Rc::clone(&d);
  let tmp_1 = ltb(tmp, d_clone);
  match bdec(tmp_1) {
    sumbool::left => {
      let d_clone_1 = Rc::clone(&d);
      if even(d_clone_1) {
        let tmp_2 = rocq_bigint::one();
        let tmp_3 = rocq_bigint::twice(tmp_2);
        let tmp_4 = rocq_bigint::identity(tmp_3);
        let tmp_5 = div(d, tmp_4);
        strip(tmp_5, add_1(s, 1u64), ())
      } else {
        (d, s)
      }
    },
    sumbool::right => {
      (d, s)
    },
  }
}

// Rocq: Stdlib.ZArith.BinIntDef.Z.odd
pub fn odd(v0: Rc<BigInt>) -> bool {
  rocq_bigint::odd(v0)
}

// Rocq: Bigfactoring.bigfactoring_implem.pm_loop
// Variant: uncurried
pub fn pm_loop_1(b: Rc<BigInt>, e: Rc<BigInt>, m: Rc<BigInt>, acc: Rc<BigInt>) -> Rc<BigInt> {
  pm_loop(b, e, m, acc, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.pm_loop (local: pm_loop)
// Variant: uncurried, lifted
pub fn pm_loop(b: Rc<BigInt>, e: Rc<BigInt>, m: Rc<BigInt>, acc: Rc<BigInt>, _H: ()) -> Rc<BigInt> {
  let tmp = rocq_bigint::zero();
  let e_clone = Rc::clone(&e);
  let tmp_1 = ltb(tmp, e_clone);
  match bdec(tmp_1) {
    sumbool::left => {
      let b_clone = Rc::clone(&b);
      let b_clone_1 = Rc::clone(&b);
      let tmp_2 = mul_owned(b_clone, b_clone_1);
      let m_clone = Rc::clone(&m);
      let tmp_3 = modulo(tmp_2, m_clone);
      let tmp_4 = rocq_bigint::one();
      let tmp_5 = rocq_bigint::twice(tmp_4);
      let tmp_6 = rocq_bigint::identity(tmp_5);
      let e_clone_1 = Rc::clone(&e);
      let tmp_7 = div(e_clone_1, tmp_6);
      let tmp_8 = if odd(e) {
        let tmp_9 = mul_owned(acc, b);
        let m_clone_1 = Rc::clone(&m);
        modulo(tmp_9, m_clone_1)
      } else {
        std::mem::drop(b);
        acc
      };
      pm_loop(tmp_3, tmp_7, m, tmp_8, ())
    },
    sumbool::right => {
      std::mem::drop(b);
      std::mem::drop(e);
      modulo(acc, m)
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.powmod
// Variant: uncurried
pub fn powmod(b: Rc<BigInt>, e: Rc<BigInt>, m: Rc<BigInt>) -> Rc<BigInt> {
  let m_clone = Rc::clone(&m);
  let tmp = modulo(b, m_clone);
  let tmp_1 = rocq_bigint::one();
  let tmp_2 = rocq_bigint::identity(tmp_1);
  pm_loop_1(tmp, e, m, tmp_2)
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb_1(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub_1(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Bigfactoring.bigfactoring_implem.sq_loop
// Variant: uncurried
pub fn sq_loop_1(n: Rc<BigInt>, x: Rc<BigInt>, k: u64) -> bool {
  sq_loop(n, x, k, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.sq_loop (local: sq_loop)
// Variant: uncurried, lifted
pub fn sq_loop(n: Rc<BigInt>, x: Rc<BigInt>, k: u64, _H: ()) -> bool {
  let tmp = ltb_1(0u64, k);
  match bdec(tmp) {
    sumbool::left => {
      let x_clone = Rc::clone(&x);
      let tmp_1 = mul_owned(x_clone, x);
      let n_clone = Rc::clone(&n);
      let x_1 = modulo(tmp_1, n_clone);
      let tmp_2 = rocq_bigint::one();
      let tmp_3 = rocq_bigint::identity(tmp_2);
      let n_clone_1 = Rc::clone(&n);
      let tmp_4 = sub(n_clone_1, tmp_3);
      let x_clone_1 = Rc::clone(&x_1);
      if eqb(x_clone_1, tmp_4) {
        std::mem::drop(x_1);
        std::mem::drop(n);
        true
      } else {
        sq_loop(n, x_1, sub_1(k, 1u64), ())
      }
    },
    sumbool::right => {
      std::mem::drop(n);
      std::mem::drop(x);
      false
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.mr_base
// Variant: uncurried
pub fn mr_base(n: Rc<BigInt>, d: Rc<BigInt>, s: u64, a: Rc<BigInt>) -> bool {
  let n_clone = Rc::clone(&n);
  let x = powmod(a, d, n_clone);
  let tmp = rocq_bigint::one();
  let tmp_1 = rocq_bigint::identity(tmp);
  let x_clone = Rc::clone(&x);
  let tmp_2 = eqb(x_clone, tmp_1);
  let tmp_3 = rocq_bigint::one();
  let tmp_4 = rocq_bigint::identity(tmp_3);
  let n_clone_1 = Rc::clone(&n);
  let tmp_5 = sub(n_clone_1, tmp_4);
  let x_clone_1 = Rc::clone(&x);
  let tmp_6 = eqb(x_clone_1, tmp_5);
  if orb(tmp_2, tmp_6) {
    std::mem::drop(x);
    std::mem::drop(n);
    true
  } else {
    sq_loop_1(n, x, sub_1(s, 1u64))
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.miller_rabin
// Variant: borrowed
pub fn miller_rabin(n: &Rc<BigInt>) -> bool {
  let tmp = rocq_bigint::one();
  let tmp_1 = rocq_bigint::identity(tmp);
  let n_clone = Rc::clone(n);
  let tmp_2 = sub(n_clone, tmp_1);
  let tmp_3 = strip_1(tmp_2, 0u64);
  match tmp_3 {
    (v21, v23) => {
      let s = &v21;
      let tmp_4 = rocq_bigint::one();
      let tmp_5 = rocq_bigint::twice(tmp_4);
      let tmp_6 = rocq_bigint::identity(tmp_5);
      let n_clone_1 = Rc::clone(n);
      let s_clone = Rc::clone(s);
      let tmp_7 = mr_base(n_clone_1, s_clone, v23, tmp_6);
      let tmp_8 = rocq_bigint::one();
      let tmp_9 = rocq_bigint::twice_plus_one(tmp_8);
      let tmp_10 = rocq_bigint::identity(tmp_9);
      let n_clone_2 = Rc::clone(n);
      let s_clone_1 = Rc::clone(s);
      let tmp_11 = andb(tmp_7, mr_base(n_clone_2, s_clone_1, v23, tmp_10));
      let tmp_12 = rocq_bigint::one();
      let tmp_13 = rocq_bigint::twice(tmp_12);
      let tmp_14 = rocq_bigint::twice_plus_one(tmp_13);
      let tmp_15 = rocq_bigint::identity(tmp_14);
      let n_clone_3 = Rc::clone(n);
      let s_clone_2 = Rc::clone(s);
      let tmp_16 = andb(tmp_11, mr_base(n_clone_3, s_clone_2, v23, tmp_15));
      let tmp_17 = rocq_bigint::one();
      let tmp_18 = rocq_bigint::twice_plus_one(tmp_17);
      let tmp_19 = rocq_bigint::twice_plus_one(tmp_18);
      let tmp_20 = rocq_bigint::identity(tmp_19);
      let n_clone_4 = Rc::clone(n);
      let s_clone_3 = Rc::clone(s);
      let tmp_21 = andb(tmp_16, mr_base(n_clone_4, s_clone_3, v23, tmp_20));
      let tmp_22 = rocq_bigint::one();
      let tmp_23 = rocq_bigint::twice(tmp_22);
      let tmp_24 = rocq_bigint::twice_plus_one(tmp_23);
      let tmp_25 = rocq_bigint::twice_plus_one(tmp_24);
      let tmp_26 = rocq_bigint::identity(tmp_25);
      let n_clone_5 = Rc::clone(n);
      let s_clone_4 = Rc::clone(s);
      let tmp_27 = andb(tmp_21, mr_base(n_clone_5, s_clone_4, v23, tmp_26));
      let tmp_28 = rocq_bigint::one();
      let tmp_29 = rocq_bigint::twice_plus_one(tmp_28);
      let tmp_30 = rocq_bigint::twice(tmp_29);
      let tmp_31 = rocq_bigint::twice_plus_one(tmp_30);
      let tmp_32 = rocq_bigint::identity(tmp_31);
      let n_clone_6 = Rc::clone(n);
      let s_clone_5 = Rc::clone(s);
      let tmp_33 = andb(tmp_27, mr_base(n_clone_6, s_clone_5, v23, tmp_32));
      let tmp_34 = rocq_bigint::one();
      let tmp_35 = rocq_bigint::twice(tmp_34);
      let tmp_36 = rocq_bigint::twice(tmp_35);
      let tmp_37 = rocq_bigint::twice(tmp_36);
      let tmp_38 = rocq_bigint::twice_plus_one(tmp_37);
      let tmp_39 = rocq_bigint::identity(tmp_38);
      let n_clone_7 = Rc::clone(n);
      let s_clone_6 = Rc::clone(s);
      let tmp_40 = andb(tmp_33, mr_base(n_clone_7, s_clone_6, v23, tmp_39));
      let tmp_41 = rocq_bigint::one();
      let tmp_42 = rocq_bigint::twice(tmp_41);
      let tmp_43 = rocq_bigint::twice(tmp_42);
      let tmp_44 = rocq_bigint::twice_plus_one(tmp_43);
      let tmp_45 = rocq_bigint::twice_plus_one(tmp_44);
      let tmp_46 = rocq_bigint::identity(tmp_45);
      let n_clone_8 = Rc::clone(n);
      let s_clone_7 = Rc::clone(s);
      let tmp_47 = andb(tmp_40, mr_base(n_clone_8, s_clone_7, v23, tmp_46));
      let tmp_48 = rocq_bigint::one();
      let tmp_49 = rocq_bigint::twice(tmp_48);
      let tmp_50 = rocq_bigint::twice_plus_one(tmp_49);
      let tmp_51 = rocq_bigint::twice_plus_one(tmp_50);
      let tmp_52 = rocq_bigint::twice_plus_one(tmp_51);
      let tmp_53 = rocq_bigint::identity(tmp_52);
      let n_clone_9 = Rc::clone(n);
      let s_clone_8 = Rc::clone(s);
      let tmp_54 = andb(tmp_47, mr_base(n_clone_9, s_clone_8, v23, tmp_53));
      let tmp_55 = rocq_bigint::one();
      let tmp_56 = rocq_bigint::twice_plus_one(tmp_55);
      let tmp_57 = rocq_bigint::twice_plus_one(tmp_56);
      let tmp_58 = rocq_bigint::twice(tmp_57);
      let tmp_59 = rocq_bigint::twice_plus_one(tmp_58);
      let tmp_60 = rocq_bigint::identity(tmp_59);
      let n_clone_10 = Rc::clone(n);
      let s_clone_9 = Rc::clone(s);
      let tmp_61 = andb(tmp_54, mr_base(n_clone_10, s_clone_9, v23, tmp_60));
      let tmp_62 = rocq_bigint::one();
      let tmp_63 = rocq_bigint::twice_plus_one(tmp_62);
      let tmp_64 = rocq_bigint::twice_plus_one(tmp_63);
      let tmp_65 = rocq_bigint::twice_plus_one(tmp_64);
      let tmp_66 = rocq_bigint::twice_plus_one(tmp_65);
      let tmp_67 = rocq_bigint::identity(tmp_66);
      let n_clone_11 = Rc::clone(n);
      let s_clone_10 = Rc::clone(s);
      let tmp_68 = andb(tmp_61, mr_base(n_clone_11, s_clone_10, v23, tmp_67));
      let tmp_69 = rocq_bigint::one();
      let tmp_70 = rocq_bigint::twice(tmp_69);
      let tmp_71 = rocq_bigint::twice(tmp_70);
      let tmp_72 = rocq_bigint::twice_plus_one(tmp_71);
      let tmp_73 = rocq_bigint::twice(tmp_72);
      let tmp_74 = rocq_bigint::twice_plus_one(tmp_73);
      let tmp_75 = rocq_bigint::identity(tmp_74);
      let n_clone_12 = Rc::clone(n);
      andb(tmp_68, mr_base(n_clone_12, v21, v23, tmp_75))
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.guard
// Variant: uncurried
pub fn guard(x: Rc<BigInt>, m: Rc<BigInt>) -> bool {
  let tmp = rocq_bigint::zero();
  let x_clone = Rc::clone(&x);
  andb(leb(tmp, x_clone), ltb(x, m))
}

// Rocq: StdGalilei.bigint.zgcd_loop
// Variant: uncurried
pub fn zgcd_loop_1(a: Rc<BigInt>, b: Rc<BigInt>) -> Rc<BigInt> {
  zgcd_loop(a, b, ())
}

// Rocq: StdGalilei.bigint.zgcd_loop (local: zgcd_loop)
// Variant: uncurried, lifted
pub fn zgcd_loop(a: Rc<BigInt>, b: Rc<BigInt>, _H: ()) -> Rc<BigInt> {
  let tmp = rocq_bigint::zero();
  let b_clone = Rc::clone(&b);
  if ltb(tmp, b_clone) {
    let b_clone_1 = Rc::clone(&b);
    let tmp_1 = modulo(a, b_clone_1);
    zgcd_loop(b, tmp_1, ())
  } else {
    std::mem::drop(b);
    a
  }
}

// Rocq: Stdlib.ZArith.BinIntDef.Z.abs
pub fn abs(v0: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::abs(v0)
}

// Rocq: StdGalilei.bigint.zgcd
// Variant: uncurried
pub fn zgcd(a: Rc<BigInt>, b: Rc<BigInt>) -> Rc<BigInt> {
  let tmp = abs(a);
  let tmp_1 = abs(b);
  zgcd_loop_1(tmp, tmp_1)
}

// Rocq: Bigfactoring.bigfactoring_implem.all_q
// Variant: uncurried
pub fn all_q_1(r: Rc<BigInt>, a: Rc<BigInt>, qs: Rc<Array<Rc<BigInt>>>, qc: u64, i: u64) -> bool {
  all_q(r, a, qs, qc, i, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.all_q (local: all_q)
// Variant: uncurried, lifted
pub fn all_q(r: Rc<BigInt>, a: Rc<BigInt>, qs: Rc<Array<Rc<BigInt>>>, qc: u64, i: u64, _H: ()) -> bool {
  let tmp = ltb_1(i, qc);
  match bdec(tmp) {
    sumbool::left => {
      let q = rocq_array::get::<Rc<BigInt>>(&qs, i);
      let tmp_1 = ltb_1(0u64, i);
      let tmp_2 = rocq_array::get::<Rc<BigInt>>(&qs, sub_1(i, 1u64));
      let q_clone = Rc::clone(&q);
      let tmp_3 = eqb(q_clone, tmp_2);
      if andb(tmp_1, tmp_3) {
        std::mem::drop(q);
        all_q(r, a, qs, qc, add_1(i, 1u64), ())
      } else {
        let tmp_4 = rocq_bigint::one();
        let tmp_5 = rocq_bigint::identity(tmp_4);
        let r_clone = Rc::clone(&r);
        let tmp_6 = sub(r_clone, tmp_5);
        let tmp_7 = div(tmp_6, q);
        let a_clone = Rc::clone(&a);
        let r_clone_1 = Rc::clone(&r);
        let tmp_8 = powmod(a_clone, tmp_7, r_clone_1);
        let tmp_9 = rocq_bigint::one();
        let tmp_10 = rocq_bigint::identity(tmp_9);
        let tmp_11 = sub(tmp_8, tmp_10);
        let r_clone_2 = Rc::clone(&r);
        let tmp_12 = zgcd(tmp_11, r_clone_2);
        let tmp_13 = rocq_bigint::one();
        let tmp_14 = rocq_bigint::identity(tmp_13);
        if eqb(tmp_12, tmp_14) {
          all_q(r, a, qs, qc, add_1(i, 1u64), ())
        } else {
          std::mem::drop(r);
          std::mem::drop(a);
          std::mem::drop(qs);
          false
        }
      }
    },
    sumbool::right => {
      std::mem::drop(r);
      std::mem::drop(a);
      std::mem::drop(qs);
      true
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.lucas_ok
// Variant: uncurried
pub fn lucas_ok(r: Rc<BigInt>, a: Rc<BigInt>, qs: Rc<Array<Rc<BigInt>>>, qc: u64) -> bool {
  let tmp = rocq_bigint::one();
  let tmp_1 = rocq_bigint::identity(tmp);
  let r_clone = Rc::clone(&r);
  let tmp_2 = sub(r_clone, tmp_1);
  let a_clone = Rc::clone(&a);
  let r_clone_1 = Rc::clone(&r);
  let tmp_3 = powmod(a_clone, tmp_2, r_clone_1);
  let tmp_4 = rocq_bigint::one();
  let tmp_5 = rocq_bigint::identity(tmp_4);
  andb(eqb(tmp_3, tmp_5), all_q_1(r, a, qs, qc, 0u64))
}

// Rocq: Bigfactoring.bigfactoring_implem.cert_try
// Variant: uncurried
pub fn cert_try_1(r: Rc<BigInt>, qs: Rc<Array<Rc<BigInt>>>, qc: u64, a: Rc<BigInt>, k: u64) -> bool {
  cert_try(r, qs, qc, a, k, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.cert_try (local: cert_try)
// Variant: uncurried, lifted
pub fn cert_try(r: Rc<BigInt>, qs: Rc<Array<Rc<BigInt>>>, qc: u64, a: Rc<BigInt>, k: u64, _H: ()) -> bool {
  let tmp = ltb_1(0u64, k);
  match bdec(tmp) {
    sumbool::left => {
      let r_clone = Rc::clone(&r);
      let a_clone = Rc::clone(&a);
      let qs_clone = Rc::clone(&qs);
      if lucas_ok(r_clone, a_clone, qs_clone, qc) {
        std::mem::drop(r);
        std::mem::drop(qs);
        std::mem::drop(a);
        true
      } else {
        let tmp_1 = rocq_bigint::one();
        let tmp_2 = rocq_bigint::identity(tmp_1);
        let tmp_3 = add(a, tmp_2);
        cert_try(r, qs, qc, tmp_3, sub_1(k, 1u64), ())
      }
    },
    sumbool::right => {
      std::mem::drop(r);
      std::mem::drop(qs);
      std::mem::drop(a);
      false
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.certify
// Variant: uncurried
pub fn certify(r: Rc<BigInt>, qs: Rc<Array<Rc<BigInt>>>, qc: u64) -> bool {
  let tmp = rocq_bigint::one();
  let tmp_1 = rocq_bigint::twice(tmp);
  let tmp_2 = rocq_bigint::identity(tmp_1);
  cert_try_1(r, qs, qc, tmp_2, 1000u64)
}

// Rocq: Bigfactoring.bigfactoring_implem.fallback
// Variant: uncurried
pub fn fallback(m: Rc<BigInt>, lo: Rc<BigInt>, acc: Rc<Array<Rc<BigInt>>>, cnt: u64) -> (Rc<Array<Rc<BigInt>>>, u64) {
  let tmp = rocq_bigint::one();
  let tmp_1 = rocq_bigint::twice(tmp);
  let tmp_2 = rocq_bigint::identity(tmp_1);
  let m_clone = Rc::clone(&m);
  let tmp_3 = add(m_clone, tmp_2);
  let tmp_4 = trial_1(tmp_3, m, lo, acc, cnt);
  match tmp_4 {
    (v31, v33) => {
      match v31 {
        (v36, v38) => {
          match v36 {
            (v41, v43) => {
              let z = &v41;
              let tmp_5 = rocq_bigint::one();
              let tmp_6 = rocq_bigint::identity(tmp_5);
              let z_clone = Rc::clone(z);
              if ltb(tmp_6, z_clone) {
                std::mem::drop(v43);
                push(v38, v33, v41)
              } else {
                std::mem::drop(v43);
                std::mem::drop(v41);
                (v38, v33)
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_f
// Variant: uncurried
pub fn rho_f(n: Rc<BigInt>, c: Rc<BigInt>, y: Rc<BigInt>) -> Rc<BigInt> {
  let y_clone = Rc::clone(&y);
  let tmp = mul_owned(y_clone, y);
  let tmp_1 = add(tmp, c);
  modulo(tmp_1, n)
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_iter
// Variant: uncurried
pub fn rho_iter_1(n: Rc<BigInt>, c: Rc<BigInt>, y: Rc<BigInt>, k: u64) -> Rc<BigInt> {
  rho_iter(n, c, y, k, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_iter (local: rho_iter)
// Variant: uncurried, lifted
pub fn rho_iter(n: Rc<BigInt>, c: Rc<BigInt>, y: Rc<BigInt>, k: u64, _H: ()) -> Rc<BigInt> {
  let tmp = ltb_1(0u64, k);
  match bdec(tmp) {
    sumbool::left => {
      let n_clone = Rc::clone(&n);
      let c_clone = Rc::clone(&c);
      let tmp_1 = rho_f(n_clone, c_clone, y);
      rho_iter(n, c, tmp_1, sub_1(k, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(n);
      std::mem::drop(c);
      y
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_batch
// Variant: uncurried
pub fn rho_batch_1(n: Rc<BigInt>, c: Rc<BigInt>, x: Rc<BigInt>, y: Rc<BigInt>, q: Rc<BigInt>, k: u64) -> (Rc<BigInt>, Rc<BigInt>) {
  rho_batch(n, c, x, y, q, k, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_batch (local: rho_batch)
// Variant: uncurried, lifted
pub fn rho_batch(n: Rc<BigInt>, c: Rc<BigInt>, x: Rc<BigInt>, y: Rc<BigInt>, q: Rc<BigInt>, k: u64, _H: ()) -> (Rc<BigInt>, Rc<BigInt>) {
  let tmp = ltb_1(0u64, k);
  match bdec(tmp) {
    sumbool::left => {
      let n_clone = Rc::clone(&n);
      let c_clone = Rc::clone(&c);
      let y_1 = rho_f(n_clone, c_clone, y);
      let x_clone = Rc::clone(&x);
      let y_clone = Rc::clone(&y_1);
      let tmp_1 = sub(x_clone, y_clone);
      let tmp_2 = abs(tmp_1);
      let tmp_3 = mul_owned(q, tmp_2);
      let n_clone_1 = Rc::clone(&n);
      let tmp_4 = modulo(tmp_3, n_clone_1);
      rho_batch(n, c, x, y_1, tmp_4, sub_1(k, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(n);
      std::mem::drop(c);
      std::mem::drop(x);
      (y, q)
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_inner
// Variant: uncurried
pub fn rho_inner_1(n: Rc<BigInt>, c: Rc<BigInt>, x: Rc<BigInt>, y: Rc<BigInt>, q: Rc<BigInt>, r: u64, k: u64) -> (((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>) {
  rho_inner(n, c, x, y, q, r, k, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_inner (local: rho_inner)
// Variant: uncurried, lifted
pub fn rho_inner(n: Rc<BigInt>, c: Rc<BigInt>, x: Rc<BigInt>, y: Rc<BigInt>, q: Rc<BigInt>, r: u64, k: u64, _H: ()) -> (((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>) {
  let tmp = ltb_1(k, r);
  let tmp_1 = add_1(k, __rocq_global_1089);
  let tmp_2 = andb(tmp, ltb_1(k, tmp_1));
  match bdec(tmp_2) {
    sumbool::left => {
      let tmp_3 = sub_1(r, k);
      let tmp_4 = __rocq_global_1089;
      let t = if ltb_1(tmp_3, tmp_4) {
        sub_1(r, k)
      } else {
        __rocq_global_1089
      };
      let n_clone = Rc::clone(&n);
      let c_clone = Rc::clone(&c);
      let x_clone = Rc::clone(&x);
      let y_clone = Rc::clone(&y);
      let tmp_5 = rho_batch_1(n_clone, c_clone, x_clone, y_clone, q, t);
      match tmp_5 {
        (v83, v85) => {
          let y_ = &v85;
          let y__clone = Rc::clone(y_);
          let n_clone_1 = Rc::clone(&n);
          let g = zgcd(y__clone, n_clone_1);
          let tmp_6 = rocq_bigint::one();
          let tmp_7 = rocq_bigint::identity(tmp_6);
          let g_clone = Rc::clone(&g);
          if eqb(g_clone, tmp_7) {
            std::mem::drop(g);
            std::mem::drop(y);
            rho_inner(n, c, x, v83, v85, r, add_1(k, __rocq_global_1089), ())
          } else {
            std::mem::drop(c);
            std::mem::drop(x);
            std::mem::drop(n);
            (((g, y), v83), v85)
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(n);
      std::mem::drop(c);
      std::mem::drop(x);
      let tmp_8 = rocq_bigint::one();
      let tmp_9 = rocq_bigint::identity(tmp_8);
      let y_clone_1 = Rc::clone(&y);
      (((tmp_9, y_clone_1), y), q)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul_1(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_back
// Variant: uncurried
pub fn rho_back_1(n: Rc<BigInt>, c: Rc<BigInt>, x: Rc<BigInt>, ys: Rc<BigInt>, k: u64) -> Rc<BigInt> {
  rho_back(n, c, x, ys, k, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_back (local: rho_back)
// Variant: uncurried, lifted
pub fn rho_back(n: Rc<BigInt>, c: Rc<BigInt>, x: Rc<BigInt>, ys: Rc<BigInt>, k: u64, _H: ()) -> Rc<BigInt> {
  let tmp = ltb_1(0u64, k);
  match bdec(tmp) {
    sumbool::left => {
      let n_clone = Rc::clone(&n);
      let c_clone = Rc::clone(&c);
      let ys_1 = rho_f(n_clone, c_clone, ys);
      let x_clone = Rc::clone(&x);
      let ys_clone = Rc::clone(&ys_1);
      let tmp_1 = sub(x_clone, ys_clone);
      let tmp_2 = abs(tmp_1);
      let n_clone_1 = Rc::clone(&n);
      let g = zgcd(tmp_2, n_clone_1);
      let tmp_3 = rocq_bigint::one();
      let tmp_4 = rocq_bigint::identity(tmp_3);
      let g_clone = Rc::clone(&g);
      if eqb(g_clone, tmp_4) {
        std::mem::drop(g);
        rho_back(n, c, x, ys_1, sub_1(k, 1u64), ())
      } else {
        std::mem::drop(ys_1);
        std::mem::drop(n);
        std::mem::drop(c);
        std::mem::drop(x);
        g
      }
    },
    sumbool::right => {
      std::mem::drop(c);
      std::mem::drop(x);
      std::mem::drop(ys);
      n
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_outer
// Variant: uncurried
pub fn rho_outer_1(n: Rc<BigInt>, c: Rc<BigInt>, y: Rc<BigInt>, q: Rc<BigInt>, r: u64) -> Rc<BigInt> {
  rho_outer(n, c, y, q, r, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_outer (local: rho_outer)
// Variant: uncurried, lifted
pub fn rho_outer(n: Rc<BigInt>, c: Rc<BigInt>, y: Rc<BigInt>, q: Rc<BigInt>, r: u64, _H: ()) -> Rc<BigInt> {
  let n_clone = Rc::clone(&n);
  let c_clone = Rc::clone(&c);
  let y_clone = Rc::clone(&y);
  let y_1 = rho_iter_1(n_clone, c_clone, y_clone, r);
  let n_clone_1 = Rc::clone(&n);
  let c_clone_1 = Rc::clone(&c);
  let y_clone_1 = Rc::clone(&y);
  let tmp = rho_inner_1(n_clone_1, c_clone_1, y_clone_1, y_1, q, r, 0u64);
  match tmp {
    (v41, v43) => {
      match v41 {
        (v46, v48) => {
          match v46 {
            (v51, v53) => {
              let ys = &v51;
              let tmp_1 = rocq_bigint::one();
              let tmp_2 = rocq_bigint::identity(tmp_1);
              let ys_clone = Rc::clone(ys);
              if eqb(ys_clone, tmp_2) {
                let tmp_3 = ltb_1(r, __rocq_global_1021);
                let tmp_4 = mul_1(r, 2u64);
                let tmp_5 = andb(tmp_3, ltb_1(r, tmp_4));
                match bdec(tmp_5) {
                  sumbool::left => {
                    std::mem::drop(y);
                    std::mem::drop(v53);
                    std::mem::drop(v51);
                    rho_outer(n, c, v48, v43, mul_1(r, 2u64), ())
                  },
                  sumbool::right => {
                    std::mem::drop(n);
                    std::mem::drop(c);
                    std::mem::drop(y);
                    std::mem::drop(v53);
                    std::mem::drop(v51);
                    std::mem::drop(v48);
                    std::mem::drop(v43);
                    rocq_bigint::zero()
                  },
                }
              } else {
                let ys_clone_1 = Rc::clone(ys);
                let n_clone_2 = Rc::clone(&n);
                if eqb(ys_clone_1, n_clone_2) {
                  std::mem::drop(v48);
                  std::mem::drop(v43);
                  std::mem::drop(v51);
                  rho_back_1(n, c, y, v53, add_1(__rocq_global_1089, 1u64))
                } else {
                  std::mem::drop(c);
                  std::mem::drop(y);
                  std::mem::drop(n);
                  std::mem::drop(v48);
                  std::mem::drop(v43);
                  std::mem::drop(v53);
                  v51
                }
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_try
// Variant: uncurried
pub fn rho_try_1(n: Rc<BigInt>, c: Rc<BigInt>, k: u64) -> Rc<BigInt> {
  rho_try(n, c, k, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_try (local: rho_try)
// Variant: uncurried, lifted
pub fn rho_try(n: Rc<BigInt>, c: Rc<BigInt>, k: u64, _H: ()) -> Rc<BigInt> {
  let tmp = ltb_1(0u64, k);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_bigint::one();
      let tmp_2 = rocq_bigint::twice(tmp_1);
      let tmp_3 = rocq_bigint::identity(tmp_2);
      let tmp_4 = rocq_bigint::one();
      let tmp_5 = rocq_bigint::identity(tmp_4);
      let n_clone = Rc::clone(&n);
      let c_clone = Rc::clone(&c);
      let g = rho_outer_1(n_clone, c_clone, tmp_3, tmp_5, 1u64);
      let tmp_6 = rocq_bigint::one();
      let tmp_7 = rocq_bigint::identity(tmp_6);
      let g_clone = Rc::clone(&g);
      let tmp_8 = ltb(tmp_7, g_clone);
      let g_clone_1 = Rc::clone(&g);
      let n_clone_1 = Rc::clone(&n);
      let tmp_9 = ltb(g_clone_1, n_clone_1);
      if andb(tmp_8, tmp_9) {
        std::mem::drop(n);
        std::mem::drop(c);
        g
      } else {
        std::mem::drop(g);
        let tmp_10 = rocq_bigint::one();
        let tmp_11 = rocq_bigint::identity(tmp_10);
        let tmp_12 = add(c, tmp_11);
        rho_try(n, tmp_12, sub_1(k, 1u64), ())
      }
    },
    sumbool::right => {
      std::mem::drop(n);
      std::mem::drop(c);
      rocq_bigint::zero()
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.rho
// Variant: borrowed
pub fn rho(n: &Rc<BigInt>) -> Rc<BigInt> {
  let tmp = rocq_bigint::one();
  let tmp_1 = rocq_bigint::identity(tmp);
  let n_clone = Rc::clone(n);
  rho_try_1(n_clone, tmp_1, 20u64)
}

// Rocq: Bigfactoring.bigfactoring_implem.fac
// Variant: uncurried
pub fn fac_1(m: Rc<BigInt>, lo: Rc<BigInt>, acc: Rc<Array<Rc<BigInt>>>, cnt: u64) -> (Rc<Array<Rc<BigInt>>>, u64) {
  fac(m, lo, acc, cnt, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.fac (local: fac)
// Variant: uncurried, lifted
pub fn fac(m: Rc<BigInt>, lo: Rc<BigInt>, acc: Rc<Array<Rc<BigInt>>>, cnt: u64, _H: ()) -> (Rc<Array<Rc<BigInt>>>, u64) {
  let tmp = B0(());
  let m_clone = Rc::clone(&m);
  let tmp_1 = trial_1(tmp, m_clone, lo, acc, cnt);
  match tmp_1 {
    (v25, v27) => {
      match v25 {
        (v30, v32) => {
          match v30 {
            (v35, v37) => {
              let d = &v35;
              let r = &v37;
              let tmp_2 = mul(r, r);
              let d_clone = Rc::clone(d);
              if ltb(d_clone, tmp_2) {
                let tmp_3 = rocq_bigint::one();
                let tmp_4 = rocq_bigint::identity(tmp_3);
                let d_clone_1 = Rc::clone(d);
                if ltb(tmp_4, d_clone_1) {
                  std::mem::drop(m);
                  std::mem::drop(v37);
                  push(v32, v27, v35)
                } else {
                  std::mem::drop(m);
                  std::mem::drop(v37);
                  std::mem::drop(v35);
                  (v32, v27)
                }
              } else {
                let tmp_5 = d;
                if miller_rabin(tmp_5) {
                  let tmp_6 = rocq_bigint::one();
                  let tmp_7 = rocq_bigint::identity(tmp_6);
                  let d_clone_2 = Rc::clone(d);
                  let tmp_8 = sub(d_clone_2, tmp_7);
                  let tmp_9 = guard(tmp_8, m);
                  match bdec(tmp_9) {
                    sumbool::left => {
                      let tmp_10 = rocq_bigint::one();
                      let tmp_11 = rocq_bigint::identity(tmp_10);
                      let d_clone_3 = Rc::clone(d);
                      let tmp_12 = sub(d_clone_3, tmp_11);
                      let tmp_13 = rocq_bigint::one();
                      let tmp_14 = rocq_bigint::twice(tmp_13);
                      let tmp_15 = rocq_bigint::identity(tmp_14);
                      let tmp_16 = rocq_bigint::zero();
                      let tmp_17 = rocq_array::make::<Rc<BigInt>>(__rocq_global_729, tmp_16);
                      let tmp_18 = fac(tmp_12, tmp_15, tmp_17, 0u64, ());
                      match tmp_18 {
                        (v150, v152) => {
                          let d_clone_4 = Rc::clone(d);
                          if certify(d_clone_4, v150, v152) {
                            std::mem::drop(v37);
                            push(v32, v27, v35)
                          } else {
                            fallback(v35, v37, v32, v27)
                          }
                        },
                      }
                    },
                    sumbool::right => {
                      fallback(v35, v37, v32, v27)
                    },
                  }
                } else {
                  let g = rho(d);
                  let tmp_19 = rocq_bigint::one();
                  let tmp_20 = rocq_bigint::identity(tmp_19);
                  let g_clone = Rc::clone(&g);
                  let tmp_21 = ltb(tmp_20, g_clone);
                  let g_clone_1 = Rc::clone(&g);
                  let d_clone_5 = Rc::clone(d);
                  let tmp_22 = andb(tmp_21, ltb(g_clone_1, d_clone_5));
                  let d_clone_6 = Rc::clone(d);
                  let g_clone_2 = Rc::clone(&g);
                  let tmp_23 = modulo(d_clone_6, g_clone_2);
                  let tmp_24 = rocq_bigint::zero();
                  let tmp_25 = eqb(tmp_23, tmp_24);
                  if andb(tmp_22, tmp_25) {
                    let g_clone_3 = Rc::clone(&g);
                    let m_clone_1 = Rc::clone(&m);
                    let tmp_26 = guard(g_clone_3, m_clone_1);
                    match bdec(tmp_26) {
                      sumbool::left => {
                        let d_clone_7 = Rc::clone(d);
                        let g_clone_4 = Rc::clone(&g);
                        let tmp_27 = div(d_clone_7, g_clone_4);
                        let tmp_28 = guard(tmp_27, m);
                        match bdec(tmp_28) {
                          sumbool::left => {
                            let tmp_29 = B0(());
                            let g_clone_5 = Rc::clone(&g);
                            let tmp_30 = fac(g_clone_5, tmp_29, v32, v27, ());
                            match tmp_30 {
                              (v307, v309) => {
                                std::mem::drop(v37);
                                let tmp_31 = div(v35, g);
                                let tmp_32 = B0(());
                                fac(tmp_31, tmp_32, v307, v309, ())
                              },
                            }
                          },
                          sumbool::right => {
                            std::mem::drop(g);
                            fallback(v35, v37, v32, v27)
                          },
                        }
                      },
                      sumbool::right => {
                        std::mem::drop(m);
                        std::mem::drop(g);
                        fallback(v35, v37, v32, v27)
                      },
                    }
                  } else {
                    std::mem::drop(g);
                    std::mem::drop(m);
                    fallback(v35, v37, v32, v27)
                  }
                }
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.copy
// Variant: uncurried
pub fn copy_1(src: Rc<Array<Rc<BigInt>>>, dst: Rc<Array<Rc<BigInt>>>, n: u64, i: u64) -> Rc<Array<Rc<BigInt>>> {
  copy(src, dst, n, i, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.copy (local: copy)
// Variant: uncurried, lifted
pub fn copy(src: Rc<Array<Rc<BigInt>>>, dst: Rc<Array<Rc<BigInt>>>, n: u64, i: u64, _H: ()) -> Rc<Array<Rc<BigInt>>> {
  let tmp = ltb_1(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<Rc<BigInt>>(&src, i);
      let tmp_2 = rocq_array::set::<Rc<BigInt>>(dst, i, tmp_1);
      copy(src, tmp_2, n, add_1(i, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.sink
// Variant: uncurried
pub fn sink_1(a: Rc<Array<Rc<BigInt>>>, j: u64) -> Rc<Array<Rc<BigInt>>> {
  sink(a, j, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.sink (local: sink)
// Variant: uncurried, lifted
pub fn sink(a: Rc<Array<Rc<BigInt>>>, j: u64, _H: ()) -> Rc<Array<Rc<BigInt>>> {
  let tmp = ltb_1(0u64, j);
  match bdec(tmp) {
    sumbool::left => {
      let x = rocq_array::get::<Rc<BigInt>>(&a, sub_1(j, 1u64));
      let y = rocq_array::get::<Rc<BigInt>>(&a, j);
      let y_clone = Rc::clone(&y);
      let x_clone = Rc::clone(&x);
      if ltb(y_clone, x_clone) {
        let tmp_1 = rocq_array::set::<Rc<BigInt>>(a, sub_1(j, 1u64), y);
        let tmp_2 = rocq_array::set::<Rc<BigInt>>(tmp_1, j, x);
        sink(tmp_2, sub_1(j, 1u64), ())
      } else {
        std::mem::drop(y);
        std::mem::drop(x);
        a
      }
    },
    sumbool::right => {
      a
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.isort
// Variant: uncurried
pub fn isort_1(a: Rc<Array<Rc<BigInt>>>, n: u64, i: u64) -> Rc<Array<Rc<BigInt>>> {
  isort(a, n, i, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.isort (local: isort)
// Variant: uncurried, lifted
pub fn isort(a: Rc<Array<Rc<BigInt>>>, n: u64, i: u64, _H: ()) -> Rc<Array<Rc<BigInt>>> {
  let tmp = ltb_1(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = sink_1(a, i);
      isort(tmp_1, n, add_1(i, 1u64), ())
    },
    sumbool::right => {
      a
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.bigfactoring_impl
pub fn bigfactoring_impl(n: Rc<BigInt>) -> Rc<Array<Rc<BigInt>>> {
  let tmp = rocq_bigint::one();
  let tmp_1 = rocq_bigint::twice(tmp);
  let tmp_2 = rocq_bigint::identity(tmp_1);
  let tmp_3 = rocq_bigint::zero();
  let tmp_4 = rocq_array::make::<Rc<BigInt>>(__rocq_global_729, tmp_3);
  let tmp_5 = fac_1(n, tmp_2, tmp_4, 0u64);
  match tmp_5 {
    (v28, v30) => {
      let tmp_6 = rocq_bigint::zero();
      let tmp_7 = rocq_array::make::<Rc<BigInt>>(v30, tmp_6);
      let out = copy_1(v28, tmp_7, v30, 0u64);
      isort_1(out, v30, 1u64)
    },
  }
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
const __rocq_global_729: u64 = 128u64;
const __rocq_global_1021: u64 = 33554432u64;
const __rocq_global_1089: u64 = 128u64;