#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};
#[allow(unused_imports)] use rocq_bigint::{self as b, BigInt};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::PositiveTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::NaturalTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::IntegerTag>; };

// Rocq: Bigfactoring.bigfactoring_implem.CAP
pub fn CAP() -> Int63 {
  int63!(128)
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_rmax
pub fn rho_rmax() -> Int63 {
  int63!(33554432)
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_m
pub fn rho_m() -> Int63 {
  int63!(128)
}

// Rocq: Bigfactoring.bigfactoring_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
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

// Rocq: Bigfactoring.bigfactoring_implem.dguard
// Variant: uncurried
pub fn dguard(m: Rc<BigInt>, d: Rc<BigInt>) -> bool {
  let tmp = b::one();
  let tmp_1 = b::identity(tmp);
  let d_clone = Rc::clone(&d);
  let tmp_2 = b::lt(tmp_1, d_clone);
  let tmp_3 = b::zero();
  let m_clone = Rc::clone(&m);
  let tmp_4 = andb(tmp_2, b::lt(tmp_3, m_clone));
  let tmp_5 = b::modulo(m, d);
  let tmp_6 = b::zero();
  andb(tmp_4, b::equal(tmp_5, tmp_6))
}

// Rocq: Bigfactoring.bigfactoring_implem.push
// Variant: uncurried
pub fn push(acc: Array<Rc<BigInt>>, cnt: Int63, p: Rc<BigInt>) -> (Array<Rc<BigInt>>, Int63) {
  (acc.set(cnt, p), cnt + int63!(1))
}

// Rocq: Bigfactoring.bigfactoring_implem.divout
// Variant: uncurried
pub fn divout_1(m: Rc<BigInt>, d: Rc<BigInt>, acc: Array<Rc<BigInt>>, cnt: Int63) -> ((Rc<BigInt>, Array<Rc<BigInt>>), Int63) {
  divout(m, d, acc, cnt, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.divout (local: divout)
// Variant: uncurried, lifted
pub fn divout(m: Rc<BigInt>, d: Rc<BigInt>, acc: Array<Rc<BigInt>>, cnt: Int63, _H: ()) -> ((Rc<BigInt>, Array<Rc<BigInt>>), Int63) {
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
          let tmp_2 = b::div(m, d_clone_2);
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
pub fn trial_1(B: Rc<BigInt>, m: Rc<BigInt>, d: Rc<BigInt>, acc: Array<Rc<BigInt>>, cnt: Int63) -> (((Rc<BigInt>, Rc<BigInt>), Array<Rc<BigInt>>), Int63) {
  trial(B, m, d, acc, cnt, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.trial (local: trial)
// Variant: uncurried, lifted
pub fn trial(B: Rc<BigInt>, m: Rc<BigInt>, d: Rc<BigInt>, acc: Array<Rc<BigInt>>, cnt: Int63, _H: ()) -> (((Rc<BigInt>, Rc<BigInt>), Array<Rc<BigInt>>), Int63) {
  let d_clone = Rc::clone(&d);
  let B_clone = Rc::clone(&B);
  let tmp = b::lt(d_clone, B_clone);
  match bdec(tmp) {
    sumbool::left => {
      let d_clone_1 = Rc::clone(&d);
      let d_clone_2 = Rc::clone(&d);
      let tmp_1 = b::mul(d_clone_1, d_clone_2);
      let m_clone = Rc::clone(&m);
      if b::lt(m_clone, tmp_1) {
        std::mem::drop(B);
        (((m, d), acc), cnt)
      } else {
        let d_clone_3 = Rc::clone(&d);
        let tmp_2 = divout_1(m, d_clone_3, acc, cnt);
        match tmp_2 {
          (v68, v70) => {
            match v68 {
              (v73, v75) => {
                let tmp_3 = b::one();
                let tmp_4 = b::identity(tmp_3);
                let tmp_5 = b::add(d, tmp_4);
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
  let tmp = b::one();
  let tmp_1 = b::twice_plus_one(tmp);
  let tmp_2 = b::twice_plus_one(tmp_1);
  let tmp_3 = b::twice_plus_one(tmp_2);
  let tmp_4 = b::twice_plus_one(tmp_3);
  let tmp_5 = b::twice(tmp_4);
  let tmp_6 = b::twice_plus_one(tmp_5);
  let tmp_7 = b::twice(tmp_6);
  let tmp_8 = b::twice(tmp_7);
  let tmp_9 = b::twice(tmp_8);
  b::identity(tmp_9)
}

// Rocq: Bigfactoring.bigfactoring_implem.strip
// Variant: uncurried
pub fn strip_1(d: Rc<BigInt>, s: Int63) -> (Rc<BigInt>, Int63) {
  strip(d, s, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.strip (local: strip)
// Variant: uncurried, lifted
pub fn strip(d: Rc<BigInt>, s: Int63, _H: ()) -> (Rc<BigInt>, Int63) {
  let tmp = b::zero();
  let d_clone = Rc::clone(&d);
  let tmp_1 = b::lt(tmp, d_clone);
  match bdec(tmp_1) {
    sumbool::left => {
      let d_clone_1 = Rc::clone(&d);
      if b::even(d_clone_1) {
        let tmp_2 = b::one();
        let tmp_3 = b::twice(tmp_2);
        let tmp_4 = b::identity(tmp_3);
        let tmp_5 = b::div(d, tmp_4);
        strip(tmp_5, s + int63!(1), ())
      } else {
        (d, s)
      }
    },
    sumbool::right => {
      (d, s)
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.pm_loop
// Variant: uncurried
pub fn pm_loop_1(b_1: Rc<BigInt>, e: Rc<BigInt>, m: Rc<BigInt>, acc: Rc<BigInt>) -> Rc<BigInt> {
  pm_loop(b_1, e, m, acc, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.pm_loop (local: pm_loop)
// Variant: uncurried, lifted
pub fn pm_loop(b_1: Rc<BigInt>, e: Rc<BigInt>, m: Rc<BigInt>, acc: Rc<BigInt>, _H: ()) -> Rc<BigInt> {
  let tmp = b::zero();
  let e_clone = Rc::clone(&e);
  let tmp_1 = b::lt(tmp, e_clone);
  match bdec(tmp_1) {
    sumbool::left => {
      let b_clone = Rc::clone(&b_1);
      let b_clone_1 = Rc::clone(&b_1);
      let tmp_2 = b::mul(b_clone, b_clone_1);
      let m_clone = Rc::clone(&m);
      let tmp_3 = b::modulo(tmp_2, m_clone);
      let tmp_4 = b::one();
      let tmp_5 = b::twice(tmp_4);
      let tmp_6 = b::identity(tmp_5);
      let e_clone_1 = Rc::clone(&e);
      let tmp_7 = b::div(e_clone_1, tmp_6);
      let tmp_8 = if b::odd(e) {
        let tmp_9 = b::mul(acc, b_1);
        let m_clone_1 = Rc::clone(&m);
        b::modulo(tmp_9, m_clone_1)
      } else {
        std::mem::drop(b_1);
        acc
      };
      pm_loop(tmp_3, tmp_7, m, tmp_8, ())
    },
    sumbool::right => {
      std::mem::drop(b_1);
      std::mem::drop(e);
      b::modulo(acc, m)
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.powmod
// Variant: uncurried
pub fn powmod(b_1: Rc<BigInt>, e: Rc<BigInt>, m: Rc<BigInt>) -> Rc<BigInt> {
  let m_clone = Rc::clone(&m);
  let tmp = b::modulo(b_1, m_clone);
  let tmp_1 = b::one();
  let tmp_2 = b::identity(tmp_1);
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

// Rocq: Bigfactoring.bigfactoring_implem.sq_loop
// Variant: uncurried
pub fn sq_loop_1(n: Rc<BigInt>, x: Rc<BigInt>, k: Int63) -> bool {
  sq_loop(n, x, k, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.sq_loop (local: sq_loop)
// Variant: uncurried, lifted
pub fn sq_loop(n: Rc<BigInt>, x: Rc<BigInt>, k: Int63, _H: ()) -> bool {
  let tmp = int63!(0) < k;
  match bdec(tmp) {
    sumbool::left => {
      let x_clone = Rc::clone(&x);
      let tmp_1 = b::mul(x_clone, x);
      let n_clone = Rc::clone(&n);
      let x_1 = b::modulo(tmp_1, n_clone);
      let tmp_2 = b::one();
      let tmp_3 = b::identity(tmp_2);
      let n_clone_1 = Rc::clone(&n);
      let tmp_4 = b::sub(n_clone_1, tmp_3);
      let x_clone_1 = Rc::clone(&x_1);
      if b::equal(x_clone_1, tmp_4) {
        std::mem::drop(x_1);
        std::mem::drop(n);
        true
      } else {
        sq_loop(n, x_1, k - int63!(1), ())
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
pub fn mr_base(n: Rc<BigInt>, d: Rc<BigInt>, s: Int63, a_1: Rc<BigInt>) -> bool {
  let n_clone = Rc::clone(&n);
  let x = powmod(a_1, d, n_clone);
  let tmp = b::one();
  let tmp_1 = b::identity(tmp);
  let x_clone = Rc::clone(&x);
  let tmp_2 = b::equal(x_clone, tmp_1);
  let tmp_3 = b::one();
  let tmp_4 = b::identity(tmp_3);
  let n_clone_1 = Rc::clone(&n);
  let tmp_5 = b::sub(n_clone_1, tmp_4);
  let x_clone_1 = Rc::clone(&x);
  let tmp_6 = b::equal(x_clone_1, tmp_5);
  if orb(tmp_2, tmp_6) {
    std::mem::drop(x);
    std::mem::drop(n);
    true
  } else {
    sq_loop_1(n, x, s - int63!(1))
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.miller_rabin
// Variant: borrowed
pub fn miller_rabin(n: &Rc<BigInt>) -> bool {
  let tmp = b::one();
  let tmp_1 = b::identity(tmp);
  let n_clone = Rc::clone(n);
  let tmp_2 = b::sub(n_clone, tmp_1);
  let tmp_3 = strip_1(tmp_2, int63!(0));
  match tmp_3 {
    (v21, v23) => {
      let s = &v21;
      let tmp_4 = b::one();
      let tmp_5 = b::twice(tmp_4);
      let tmp_6 = b::identity(tmp_5);
      let n_clone_1 = Rc::clone(n);
      let s_clone = Rc::clone(s);
      let tmp_7 = mr_base(n_clone_1, s_clone, v23, tmp_6);
      let tmp_8 = b::one();
      let tmp_9 = b::twice_plus_one(tmp_8);
      let tmp_10 = b::identity(tmp_9);
      let n_clone_2 = Rc::clone(n);
      let s_clone_1 = Rc::clone(s);
      let tmp_11 = andb(tmp_7, mr_base(n_clone_2, s_clone_1, v23, tmp_10));
      let tmp_12 = b::one();
      let tmp_13 = b::twice(tmp_12);
      let tmp_14 = b::twice_plus_one(tmp_13);
      let tmp_15 = b::identity(tmp_14);
      let n_clone_3 = Rc::clone(n);
      let s_clone_2 = Rc::clone(s);
      let tmp_16 = andb(tmp_11, mr_base(n_clone_3, s_clone_2, v23, tmp_15));
      let tmp_17 = b::one();
      let tmp_18 = b::twice_plus_one(tmp_17);
      let tmp_19 = b::twice_plus_one(tmp_18);
      let tmp_20 = b::identity(tmp_19);
      let n_clone_4 = Rc::clone(n);
      let s_clone_3 = Rc::clone(s);
      let tmp_21 = andb(tmp_16, mr_base(n_clone_4, s_clone_3, v23, tmp_20));
      let tmp_22 = b::one();
      let tmp_23 = b::twice(tmp_22);
      let tmp_24 = b::twice_plus_one(tmp_23);
      let tmp_25 = b::twice_plus_one(tmp_24);
      let tmp_26 = b::identity(tmp_25);
      let n_clone_5 = Rc::clone(n);
      let s_clone_4 = Rc::clone(s);
      let tmp_27 = andb(tmp_21, mr_base(n_clone_5, s_clone_4, v23, tmp_26));
      let tmp_28 = b::one();
      let tmp_29 = b::twice_plus_one(tmp_28);
      let tmp_30 = b::twice(tmp_29);
      let tmp_31 = b::twice_plus_one(tmp_30);
      let tmp_32 = b::identity(tmp_31);
      let n_clone_6 = Rc::clone(n);
      let s_clone_5 = Rc::clone(s);
      let tmp_33 = andb(tmp_27, mr_base(n_clone_6, s_clone_5, v23, tmp_32));
      let tmp_34 = b::one();
      let tmp_35 = b::twice(tmp_34);
      let tmp_36 = b::twice(tmp_35);
      let tmp_37 = b::twice(tmp_36);
      let tmp_38 = b::twice_plus_one(tmp_37);
      let tmp_39 = b::identity(tmp_38);
      let n_clone_7 = Rc::clone(n);
      let s_clone_6 = Rc::clone(s);
      let tmp_40 = andb(tmp_33, mr_base(n_clone_7, s_clone_6, v23, tmp_39));
      let tmp_41 = b::one();
      let tmp_42 = b::twice(tmp_41);
      let tmp_43 = b::twice(tmp_42);
      let tmp_44 = b::twice_plus_one(tmp_43);
      let tmp_45 = b::twice_plus_one(tmp_44);
      let tmp_46 = b::identity(tmp_45);
      let n_clone_8 = Rc::clone(n);
      let s_clone_7 = Rc::clone(s);
      let tmp_47 = andb(tmp_40, mr_base(n_clone_8, s_clone_7, v23, tmp_46));
      let tmp_48 = b::one();
      let tmp_49 = b::twice(tmp_48);
      let tmp_50 = b::twice_plus_one(tmp_49);
      let tmp_51 = b::twice_plus_one(tmp_50);
      let tmp_52 = b::twice_plus_one(tmp_51);
      let tmp_53 = b::identity(tmp_52);
      let n_clone_9 = Rc::clone(n);
      let s_clone_8 = Rc::clone(s);
      let tmp_54 = andb(tmp_47, mr_base(n_clone_9, s_clone_8, v23, tmp_53));
      let tmp_55 = b::one();
      let tmp_56 = b::twice_plus_one(tmp_55);
      let tmp_57 = b::twice_plus_one(tmp_56);
      let tmp_58 = b::twice(tmp_57);
      let tmp_59 = b::twice_plus_one(tmp_58);
      let tmp_60 = b::identity(tmp_59);
      let n_clone_10 = Rc::clone(n);
      let s_clone_9 = Rc::clone(s);
      let tmp_61 = andb(tmp_54, mr_base(n_clone_10, s_clone_9, v23, tmp_60));
      let tmp_62 = b::one();
      let tmp_63 = b::twice_plus_one(tmp_62);
      let tmp_64 = b::twice_plus_one(tmp_63);
      let tmp_65 = b::twice_plus_one(tmp_64);
      let tmp_66 = b::twice_plus_one(tmp_65);
      let tmp_67 = b::identity(tmp_66);
      let n_clone_11 = Rc::clone(n);
      let s_clone_10 = Rc::clone(s);
      let tmp_68 = andb(tmp_61, mr_base(n_clone_11, s_clone_10, v23, tmp_67));
      let tmp_69 = b::one();
      let tmp_70 = b::twice(tmp_69);
      let tmp_71 = b::twice(tmp_70);
      let tmp_72 = b::twice_plus_one(tmp_71);
      let tmp_73 = b::twice(tmp_72);
      let tmp_74 = b::twice_plus_one(tmp_73);
      let tmp_75 = b::identity(tmp_74);
      let n_clone_12 = Rc::clone(n);
      andb(tmp_68, mr_base(n_clone_12, v21, v23, tmp_75))
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.guard
// Variant: uncurried
pub fn guard(x: Rc<BigInt>, m: Rc<BigInt>) -> bool {
  let tmp = b::zero();
  let x_clone = Rc::clone(&x);
  andb(b::le(tmp, x_clone), b::lt(x, m))
}

// Rocq: StdGalilei.bigint.zgcd_loop
// Variant: uncurried
pub fn zgcd_loop_1(a_1: Rc<BigInt>, b_1: Rc<BigInt>) -> Rc<BigInt> {
  zgcd_loop(a_1, b_1, ())
}

// Rocq: StdGalilei.bigint.zgcd_loop (local: zgcd_loop)
// Variant: uncurried, lifted
pub fn zgcd_loop(a_1: Rc<BigInt>, b_1: Rc<BigInt>, _H: ()) -> Rc<BigInt> {
  let tmp = b::zero();
  let b_clone = Rc::clone(&b_1);
  if b::lt(tmp, b_clone) {
    let b_clone_1 = Rc::clone(&b_1);
    let tmp_1 = b::modulo(a_1, b_clone_1);
    zgcd_loop(b_1, tmp_1, ())
  } else {
    std::mem::drop(b_1);
    a_1
  }
}

// Rocq: StdGalilei.bigint.zgcd
// Variant: uncurried
pub fn zgcd(a_1: Rc<BigInt>, b_1: Rc<BigInt>) -> Rc<BigInt> {
  let tmp = b::abs(a_1);
  let tmp_1 = b::abs(b_1);
  zgcd_loop_1(tmp, tmp_1)
}

// Rocq: Bigfactoring.bigfactoring_implem.all_q
// Variant: uncurried
pub fn all_q_1(r: Rc<BigInt>, a_1: Rc<BigInt>, qs: Array<Rc<BigInt>>, qc: Int63, i: Int63) -> bool {
  all_q(r, a_1, qs, qc, i, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.all_q (local: all_q)
// Variant: uncurried, lifted
pub fn all_q(r: Rc<BigInt>, a_1: Rc<BigInt>, qs: Array<Rc<BigInt>>, qc: Int63, i: Int63, _H: ()) -> bool {
  let tmp = i < qc;
  match bdec(tmp) {
    sumbool::left => {
      let q = qs.get_cloned(i);
      let tmp_1 = int63!(0) < i;
      let tmp_2 = qs.get_cloned(i - int63!(1));
      let q_clone = Rc::clone(&q);
      let tmp_3 = b::equal(q_clone, tmp_2);
      if andb(tmp_1, tmp_3) {
        std::mem::drop(q);
        all_q(r, a_1, qs, qc, i + int63!(1), ())
      } else {
        let tmp_4 = b::one();
        let tmp_5 = b::identity(tmp_4);
        let r_clone = Rc::clone(&r);
        let tmp_6 = b::sub(r_clone, tmp_5);
        let tmp_7 = b::div(tmp_6, q);
        let a_clone = Rc::clone(&a_1);
        let r_clone_1 = Rc::clone(&r);
        let tmp_8 = powmod(a_clone, tmp_7, r_clone_1);
        let tmp_9 = b::one();
        let tmp_10 = b::identity(tmp_9);
        let tmp_11 = b::sub(tmp_8, tmp_10);
        let r_clone_2 = Rc::clone(&r);
        let tmp_12 = zgcd(tmp_11, r_clone_2);
        let tmp_13 = b::one();
        let tmp_14 = b::identity(tmp_13);
        if b::equal(tmp_12, tmp_14) {
          all_q(r, a_1, qs, qc, i + int63!(1), ())
        } else {
          std::mem::drop(r);
          std::mem::drop(a_1);
          std::mem::drop(qs);
          false
        }
      }
    },
    sumbool::right => {
      std::mem::drop(r);
      std::mem::drop(a_1);
      std::mem::drop(qs);
      true
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.lucas_ok
// Variant: uncurried
pub fn lucas_ok(r: Rc<BigInt>, a_1: Rc<BigInt>, qs: Array<Rc<BigInt>>, qc: Int63) -> bool {
  let tmp = b::one();
  let tmp_1 = b::identity(tmp);
  let r_clone = Rc::clone(&r);
  let tmp_2 = b::sub(r_clone, tmp_1);
  let a_clone = Rc::clone(&a_1);
  let r_clone_1 = Rc::clone(&r);
  let tmp_3 = powmod(a_clone, tmp_2, r_clone_1);
  let tmp_4 = b::one();
  let tmp_5 = b::identity(tmp_4);
  andb(b::equal(tmp_3, tmp_5), all_q_1(r, a_1, qs, qc, int63!(0)))
}

// Rocq: Bigfactoring.bigfactoring_implem.cert_try
// Variant: uncurried
pub fn cert_try_1(r: Rc<BigInt>, qs: Array<Rc<BigInt>>, qc: Int63, a_1: Rc<BigInt>, k: Int63) -> bool {
  cert_try(r, qs, qc, a_1, k, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.cert_try (local: cert_try)
// Variant: uncurried, lifted
pub fn cert_try(r: Rc<BigInt>, qs: Array<Rc<BigInt>>, qc: Int63, a_1: Rc<BigInt>, k: Int63, _H: ()) -> bool {
  let tmp = int63!(0) < k;
  match bdec(tmp) {
    sumbool::left => {
      let r_clone = Rc::clone(&r);
      let a_clone = Rc::clone(&a_1);
      let qs_clone = Clone::clone(&qs);
      if lucas_ok(r_clone, a_clone, qs_clone, qc) {
        std::mem::drop(r);
        std::mem::drop(qs);
        std::mem::drop(a_1);
        true
      } else {
        let tmp_1 = b::one();
        let tmp_2 = b::identity(tmp_1);
        let tmp_3 = b::add(a_1, tmp_2);
        cert_try(r, qs, qc, tmp_3, k - int63!(1), ())
      }
    },
    sumbool::right => {
      std::mem::drop(r);
      std::mem::drop(qs);
      std::mem::drop(a_1);
      false
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.certify
// Variant: uncurried
pub fn certify(r: Rc<BigInt>, qs: Array<Rc<BigInt>>, qc: Int63) -> bool {
  let tmp = b::one();
  let tmp_1 = b::twice(tmp);
  let tmp_2 = b::identity(tmp_1);
  cert_try_1(r, qs, qc, tmp_2, int63!(1000))
}

// Rocq: Bigfactoring.bigfactoring_implem.fallback
// Variant: uncurried
pub fn fallback(m: Rc<BigInt>, lo: Rc<BigInt>, acc: Array<Rc<BigInt>>, cnt: Int63) -> (Array<Rc<BigInt>>, Int63) {
  let tmp = b::one();
  let tmp_1 = b::twice(tmp);
  let tmp_2 = b::identity(tmp_1);
  let m_clone = Rc::clone(&m);
  let tmp_3 = b::add(m_clone, tmp_2);
  let tmp_4 = trial_1(tmp_3, m, lo, acc, cnt);
  match tmp_4 {
    (v31, v33) => {
      match v31 {
        (v36, v38) => {
          match v36 {
            (v41, v43) => {
              let z = &v41;
              let tmp_5 = b::one();
              let tmp_6 = b::identity(tmp_5);
              let z_clone = Rc::clone(z);
              if b::lt(tmp_6, z_clone) {
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
  let tmp = b::mul(y_clone, y);
  let tmp_1 = b::add(tmp, c);
  b::modulo(tmp_1, n)
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_iter
// Variant: uncurried
pub fn rho_iter_1(n: Rc<BigInt>, c: Rc<BigInt>, y: Rc<BigInt>, k: Int63) -> Rc<BigInt> {
  rho_iter(n, c, y, k, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_iter (local: rho_iter)
// Variant: uncurried, lifted
pub fn rho_iter(n: Rc<BigInt>, c: Rc<BigInt>, y: Rc<BigInt>, k: Int63, _H: ()) -> Rc<BigInt> {
  let tmp = int63!(0) < k;
  match bdec(tmp) {
    sumbool::left => {
      let n_clone = Rc::clone(&n);
      let c_clone = Rc::clone(&c);
      let tmp_1 = rho_f(n_clone, c_clone, y);
      rho_iter(n, c, tmp_1, k - int63!(1), ())
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
pub fn rho_batch_1(n: Rc<BigInt>, c: Rc<BigInt>, x: Rc<BigInt>, y: Rc<BigInt>, q: Rc<BigInt>, k: Int63) -> (Rc<BigInt>, Rc<BigInt>) {
  rho_batch(n, c, x, y, q, k, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_batch (local: rho_batch)
// Variant: uncurried, lifted
pub fn rho_batch(n: Rc<BigInt>, c: Rc<BigInt>, x: Rc<BigInt>, y: Rc<BigInt>, q: Rc<BigInt>, k: Int63, _H: ()) -> (Rc<BigInt>, Rc<BigInt>) {
  let tmp = int63!(0) < k;
  match bdec(tmp) {
    sumbool::left => {
      let n_clone = Rc::clone(&n);
      let c_clone = Rc::clone(&c);
      let y_1 = rho_f(n_clone, c_clone, y);
      let x_clone = Rc::clone(&x);
      let y_clone = Rc::clone(&y_1);
      let tmp_1 = b::sub(x_clone, y_clone);
      let tmp_2 = b::abs(tmp_1);
      let tmp_3 = b::mul(q, tmp_2);
      let n_clone_1 = Rc::clone(&n);
      let tmp_4 = b::modulo(tmp_3, n_clone_1);
      rho_batch(n, c, x, y_1, tmp_4, k - int63!(1), ())
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
pub fn rho_inner_1(n: Rc<BigInt>, c: Rc<BigInt>, x: Rc<BigInt>, y: Rc<BigInt>, q: Rc<BigInt>, r: Int63, k: Int63) -> (((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>) {
  rho_inner(n, c, x, y, q, r, k, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_inner (local: rho_inner)
// Variant: uncurried, lifted
pub fn rho_inner(n: Rc<BigInt>, c: Rc<BigInt>, x: Rc<BigInt>, y: Rc<BigInt>, q: Rc<BigInt>, r: Int63, k: Int63, _H: ()) -> (((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>) {
  let tmp = k < r;
  let tmp_1 = k + __rocq_global_1089;
  let tmp_2 = andb(tmp, k < tmp_1);
  match bdec(tmp_2) {
    sumbool::left => {
      let tmp_3 = r - k;
      let tmp_4 = __rocq_global_1089;
      let t = if tmp_3 < tmp_4 {
        r - k
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
          let tmp_6 = b::one();
          let tmp_7 = b::identity(tmp_6);
          let g_clone = Rc::clone(&g);
          if b::equal(g_clone, tmp_7) {
            std::mem::drop(g);
            std::mem::drop(y);
            rho_inner(n, c, x, v83, v85, r, k + __rocq_global_1089, ())
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
      let tmp_8 = b::one();
      let tmp_9 = b::identity(tmp_8);
      let y_clone_1 = Rc::clone(&y);
      (((tmp_9, y_clone_1), y), q)
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_back
// Variant: uncurried
pub fn rho_back_1(n: Rc<BigInt>, c: Rc<BigInt>, x: Rc<BigInt>, ys: Rc<BigInt>, k: Int63) -> Rc<BigInt> {
  rho_back(n, c, x, ys, k, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_back (local: rho_back)
// Variant: uncurried, lifted
pub fn rho_back(n: Rc<BigInt>, c: Rc<BigInt>, x: Rc<BigInt>, ys: Rc<BigInt>, k: Int63, _H: ()) -> Rc<BigInt> {
  let tmp = int63!(0) < k;
  match bdec(tmp) {
    sumbool::left => {
      let n_clone = Rc::clone(&n);
      let c_clone = Rc::clone(&c);
      let ys_1 = rho_f(n_clone, c_clone, ys);
      let x_clone = Rc::clone(&x);
      let ys_clone = Rc::clone(&ys_1);
      let tmp_1 = b::sub(x_clone, ys_clone);
      let tmp_2 = b::abs(tmp_1);
      let n_clone_1 = Rc::clone(&n);
      let g = zgcd(tmp_2, n_clone_1);
      let tmp_3 = b::one();
      let tmp_4 = b::identity(tmp_3);
      let g_clone = Rc::clone(&g);
      if b::equal(g_clone, tmp_4) {
        std::mem::drop(g);
        rho_back(n, c, x, ys_1, k - int63!(1), ())
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
pub fn rho_outer_1(n: Rc<BigInt>, c: Rc<BigInt>, y: Rc<BigInt>, q: Rc<BigInt>, r: Int63) -> Rc<BigInt> {
  rho_outer(n, c, y, q, r, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_outer (local: rho_outer)
// Variant: uncurried, lifted
pub fn rho_outer(n: Rc<BigInt>, c: Rc<BigInt>, y: Rc<BigInt>, q: Rc<BigInt>, r: Int63, _H: ()) -> Rc<BigInt> {
  let n_clone = Rc::clone(&n);
  let c_clone = Rc::clone(&c);
  let y_clone = Rc::clone(&y);
  let y_1 = rho_iter_1(n_clone, c_clone, y_clone, r);
  let n_clone_1 = Rc::clone(&n);
  let c_clone_1 = Rc::clone(&c);
  let y_clone_1 = Rc::clone(&y);
  let tmp = rho_inner_1(n_clone_1, c_clone_1, y_clone_1, y_1, q, r, int63!(0));
  match tmp {
    (v41, v43) => {
      match v41 {
        (v46, v48) => {
          match v46 {
            (v51, v53) => {
              let ys = &v51;
              let tmp_1 = b::one();
              let tmp_2 = b::identity(tmp_1);
              let ys_clone = Rc::clone(ys);
              if b::equal(ys_clone, tmp_2) {
                let tmp_3 = r < __rocq_global_1021;
                let tmp_4 = r * int63!(2);
                let tmp_5 = andb(tmp_3, r < tmp_4);
                match bdec(tmp_5) {
                  sumbool::left => {
                    std::mem::drop(y);
                    std::mem::drop(v53);
                    std::mem::drop(v51);
                    rho_outer(n, c, v48, v43, r * int63!(2), ())
                  },
                  sumbool::right => {
                    std::mem::drop(n);
                    std::mem::drop(c);
                    std::mem::drop(y);
                    std::mem::drop(v53);
                    std::mem::drop(v51);
                    std::mem::drop(v48);
                    std::mem::drop(v43);
                    b::zero()
                  },
                }
              } else {
                let ys_clone_1 = Rc::clone(ys);
                let n_clone_2 = Rc::clone(&n);
                if b::equal(ys_clone_1, n_clone_2) {
                  std::mem::drop(v48);
                  std::mem::drop(v43);
                  std::mem::drop(v51);
                  rho_back_1(n, c, y, v53, __rocq_global_1089 + int63!(1))
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
pub fn rho_try_1(n: Rc<BigInt>, c: Rc<BigInt>, k: Int63) -> Rc<BigInt> {
  rho_try(n, c, k, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_try (local: rho_try)
// Variant: uncurried, lifted
pub fn rho_try(n: Rc<BigInt>, c: Rc<BigInt>, k: Int63, _H: ()) -> Rc<BigInt> {
  let tmp = int63!(0) < k;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = b::one();
      let tmp_2 = b::twice(tmp_1);
      let tmp_3 = b::identity(tmp_2);
      let tmp_4 = b::one();
      let tmp_5 = b::identity(tmp_4);
      let n_clone = Rc::clone(&n);
      let c_clone = Rc::clone(&c);
      let g = rho_outer_1(n_clone, c_clone, tmp_3, tmp_5, int63!(1));
      let tmp_6 = b::one();
      let tmp_7 = b::identity(tmp_6);
      let g_clone = Rc::clone(&g);
      let tmp_8 = b::lt(tmp_7, g_clone);
      let g_clone_1 = Rc::clone(&g);
      let n_clone_1 = Rc::clone(&n);
      let tmp_9 = b::lt(g_clone_1, n_clone_1);
      if andb(tmp_8, tmp_9) {
        std::mem::drop(n);
        std::mem::drop(c);
        g
      } else {
        std::mem::drop(g);
        let tmp_10 = b::one();
        let tmp_11 = b::identity(tmp_10);
        let tmp_12 = b::add(c, tmp_11);
        rho_try(n, tmp_12, k - int63!(1), ())
      }
    },
    sumbool::right => {
      std::mem::drop(n);
      std::mem::drop(c);
      b::zero()
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.rho
// Variant: borrowed
pub fn rho(n: &Rc<BigInt>) -> Rc<BigInt> {
  let tmp = b::one();
  let tmp_1 = b::identity(tmp);
  let n_clone = Rc::clone(n);
  rho_try_1(n_clone, tmp_1, int63!(20))
}

// Rocq: Bigfactoring.bigfactoring_implem.fac
// Variant: uncurried
pub fn fac_1(m: Rc<BigInt>, lo: Rc<BigInt>, acc: Array<Rc<BigInt>>, cnt: Int63) -> (Array<Rc<BigInt>>, Int63) {
  fac(m, lo, acc, cnt, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.fac (local: fac)
// Variant: uncurried, lifted
pub fn fac(m: Rc<BigInt>, lo: Rc<BigInt>, acc: Array<Rc<BigInt>>, cnt: Int63, _H: ()) -> (Array<Rc<BigInt>>, Int63) {
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
              let r_clone = Rc::clone(r);
              let r_clone_1 = Rc::clone(r);
              let tmp_2 = b::mul(r_clone, r_clone_1);
              let d_clone = Rc::clone(d);
              if b::lt(d_clone, tmp_2) {
                let tmp_3 = b::one();
                let tmp_4 = b::identity(tmp_3);
                let d_clone_1 = Rc::clone(d);
                if b::lt(tmp_4, d_clone_1) {
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
                  let tmp_6 = b::one();
                  let tmp_7 = b::identity(tmp_6);
                  let d_clone_2 = Rc::clone(d);
                  let tmp_8 = b::sub(d_clone_2, tmp_7);
                  let tmp_9 = guard(tmp_8, m);
                  match bdec(tmp_9) {
                    sumbool::left => {
                      let tmp_10 = b::one();
                      let tmp_11 = b::identity(tmp_10);
                      let d_clone_3 = Rc::clone(d);
                      let tmp_12 = b::sub(d_clone_3, tmp_11);
                      let tmp_13 = b::one();
                      let tmp_14 = b::twice(tmp_13);
                      let tmp_15 = b::identity(tmp_14);
                      let tmp_16 = b::zero();
                      let tmp_17 = fac(tmp_12, tmp_15, Array::<Rc<BigInt>>::make(__rocq_global_729, tmp_16), int63!(0), ());
                      match tmp_17 {
                        (v152, v154) => {
                          let d_clone_4 = Rc::clone(d);
                          if certify(d_clone_4, v152, v154) {
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
                  let tmp_18 = b::one();
                  let tmp_19 = b::identity(tmp_18);
                  let g_clone = Rc::clone(&g);
                  let tmp_20 = b::lt(tmp_19, g_clone);
                  let g_clone_1 = Rc::clone(&g);
                  let d_clone_5 = Rc::clone(d);
                  let tmp_21 = andb(tmp_20, b::lt(g_clone_1, d_clone_5));
                  let d_clone_6 = Rc::clone(d);
                  let g_clone_2 = Rc::clone(&g);
                  let tmp_22 = b::modulo(d_clone_6, g_clone_2);
                  let tmp_23 = b::zero();
                  let tmp_24 = b::equal(tmp_22, tmp_23);
                  if andb(tmp_21, tmp_24) {
                    let g_clone_3 = Rc::clone(&g);
                    let m_clone_1 = Rc::clone(&m);
                    let tmp_25 = guard(g_clone_3, m_clone_1);
                    match bdec(tmp_25) {
                      sumbool::left => {
                        let d_clone_7 = Rc::clone(d);
                        let g_clone_4 = Rc::clone(&g);
                        let tmp_26 = b::div(d_clone_7, g_clone_4);
                        let tmp_27 = guard(tmp_26, m);
                        match bdec(tmp_27) {
                          sumbool::left => {
                            let tmp_28 = B0(());
                            let g_clone_5 = Rc::clone(&g);
                            let tmp_29 = fac(g_clone_5, tmp_28, v32, v27, ());
                            match tmp_29 {
                              (v309, v311) => {
                                std::mem::drop(v37);
                                let tmp_30 = b::div(v35, g);
                                let tmp_31 = B0(());
                                fac(tmp_30, tmp_31, v309, v311, ())
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
pub fn copy_1(src: Array<Rc<BigInt>>, dst: Array<Rc<BigInt>>, n: Int63, i: Int63) -> Array<Rc<BigInt>> {
  copy(src, dst, n, i, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.copy (local: copy)
// Variant: uncurried, lifted
pub fn copy(src: Array<Rc<BigInt>>, dst: Array<Rc<BigInt>>, n: Int63, i: Int63, _H: ()) -> Array<Rc<BigInt>> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = src.get_cloned(i);
      copy(src, dst.set(i, tmp_1), n, i + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.sink
// Variant: uncurried
pub fn sink_1(a_1: Array<Rc<BigInt>>, j: Int63) -> Array<Rc<BigInt>> {
  sink(a_1, j, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.sink (local: sink)
// Variant: uncurried, lifted
pub fn sink(a_1: Array<Rc<BigInt>>, j: Int63, _H: ()) -> Array<Rc<BigInt>> {
  let tmp = int63!(0) < j;
  match bdec(tmp) {
    sumbool::left => {
      let x = a_1.get_cloned(j - int63!(1));
      let y = a_1.get_cloned(j);
      let y_clone = Rc::clone(&y);
      let x_clone = Rc::clone(&x);
      if b::lt(y_clone, x_clone) {
        sink(a_1.set(j - int63!(1), y).set(j, x), j - int63!(1), ())
      } else {
        std::mem::drop(y);
        std::mem::drop(x);
        a_1
      }
    },
    sumbool::right => {
      a_1
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.isort
// Variant: uncurried
pub fn isort_1(a_1: Array<Rc<BigInt>>, n: Int63, i: Int63) -> Array<Rc<BigInt>> {
  isort(a_1, n, i, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.isort (local: isort)
// Variant: uncurried, lifted
pub fn isort(a_1: Array<Rc<BigInt>>, n: Int63, i: Int63, _H: ()) -> Array<Rc<BigInt>> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      isort(sink_1(a_1, i), n, i + int63!(1), ())
    },
    sumbool::right => {
      a_1
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.bigfactoring_impl
pub fn bigfactoring_impl(n: Rc<BigInt>) -> Array<Rc<BigInt>> {
  let tmp = b::one();
  let tmp_1 = b::twice(tmp);
  let tmp_2 = b::identity(tmp_1);
  let tmp_3 = b::zero();
  let tmp_4 = fac_1(n, tmp_2, Array::<Rc<BigInt>>::make(__rocq_global_729, tmp_3), int63!(0));
  match tmp_4 {
    (v28, v30) => {
      let tmp_5 = b::zero();
      let out = copy_1(v28, Array::<Rc<BigInt>>::make(v30, tmp_5), v30, int63!(0));
      isort_1(out, v30, int63!(1))
    },
  }
}
const __rocq_global_729: Int63 = int63!(128);
const __rocq_global_1021: Int63 = int63!(33554432);
const __rocq_global_1089: Int63 = int63!(128);