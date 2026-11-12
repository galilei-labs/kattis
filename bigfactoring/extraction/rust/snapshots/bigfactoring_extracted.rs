// Generated from OwnedANF. This printer is not verified.
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

// Rocq: Bigfactoring.bigfactoring_implem.bigfactoring
pub fn bigfactoring() -> Rc<dyn Fn(Rc<BigInt>) -> Rc<Array<Rc<BigInt>>>> {
  let v0: fn(Rc<BigInt>) -> Rc<Array<Rc<BigInt>>> = bigfactoring_impl;
  let v1: Rc<dyn Fn(Rc<BigInt>) -> Rc<Array<Rc<BigInt>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.BinNums.IntDef.Z.add
// Variant: uncurried
pub fn add(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::add(v0, v1);
  v8
}

// Rocq: Corelib.BinNums.IntDef.Z.sub
// Variant: uncurried
pub fn sub(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::sub(v0, v1);
  v8
}

// Rocq: Corelib.BinNums.IntDef.Z.ltb
// Variant: uncurried
pub fn ltb(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::lt(v0, v1)
}

// Rocq: Bigfactoring.bigfactoring_implem.bdec
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

// Rocq: Corelib.BinNums.IntDef.Z.mul
// Variant: uncurried
pub fn mul_owned(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::mul(v0, v1);
  v8
}

// Rocq: Corelib.BinNums.IntDef.Z.mul
// Variant: borrowed, uncurried
pub fn mul(v0: &Rc<BigInt>, v1: &Rc<BigInt>) -> Rc<BigInt> {
  let v5 = Rc::clone(v0);
  let v8 = Rc::clone(v1);
  let v10 = rocq_bigint::mul(v5, v8);
  v10
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
  let v8 = rocq_bigint::modulo(v0, v1);
  v8
}

// Rocq: Bigfactoring.bigfactoring_implem.dguard
// Variant: uncurried
pub fn dguard(m: Rc<BigInt>, d: Rc<BigInt>) -> bool {
  let v6 = rocq_bigint::one();
  let v9 = rocq_bigint::identity(v6);
  let v13 = Rc::clone(&d);
  let v14 = ltb(v9, v13);
  let v17 = rocq_bigint::zero();
  let v21 = Rc::clone(&m);
  let v27 = andb(v14, ltb(v17, v21));
  let v34 = modulo(m, d);
  let v35 = rocq_bigint::zero();
  andb(v27, eqb(v34, v35))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add_1(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Bigfactoring.bigfactoring_implem.push
// Variant: uncurried
pub fn push(acc: Rc<Array<Rc<BigInt>>>, cnt: u64, p: Rc<BigInt>) -> (Rc<Array<Rc<BigInt>>>, u64) {
  let v9 = rocq_array::set::<Rc<BigInt>>(acc, cnt, p);
  (v9, add_1(cnt, 1u64))
}

// Rocq: Corelib.BinNums.IntDef.Z.div
// Variant: uncurried
pub fn div(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::div(v0, v1);
  v8
}

// Rocq: Bigfactoring.bigfactoring_implem.divout
// Variant: uncurried
pub fn divout_1(m: Rc<BigInt>, d: Rc<BigInt>, acc: Rc<Array<Rc<BigInt>>>, cnt: u64) -> ((Rc<BigInt>, Rc<Array<Rc<BigInt>>>), u64) {
  divout(m, d, acc, cnt, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.divout (local: divout)
// Variant: uncurried, lifted
pub fn divout(m: Rc<BigInt>, d: Rc<BigInt>, acc: Rc<Array<Rc<BigInt>>>, cnt: u64, _H: ()) -> ((Rc<BigInt>, Rc<Array<Rc<BigInt>>>), u64) {
  let v9 = Rc::clone(&m);
  let v12 = Rc::clone(&d);
  let v14 = dguard(v9, v12);
  match bdec(v14) {
    sumbool::left => {
      let v25 = Rc::clone(&d);
      let v26 = push(acc, cnt, v25);
      match v26 {
        (v28, v30) => {
          let v37 = Rc::clone(&d);
          let v38 = div(m, v37);
          divout(v38, d, v28, v30, ())
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
  let v10 = Rc::clone(&d);
  let v13 = Rc::clone(&B);
  let v15 = ltb(v10, v13);
  match bdec(v15) {
    sumbool::left => {
      let v23 = Rc::clone(&d);
      let v26 = Rc::clone(&d);
      let v27 = mul_owned(v23, v26);
      let v30 = Rc::clone(&m);
      let v33 = ltb(v30, v27);
      match &v33 {
        true => {
          std::mem::drop(B);
          (((m, d), acc), cnt)
        },
        false => {
          let v61 = Rc::clone(&d);
          let v66 = divout_1(m, v61, acc, cnt);
          match v66 {
            (v68, v70) => {
              match v68 {
                (v73, v75) => {
                  let v79 = rocq_bigint::one();
                  let v81 = rocq_bigint::identity(v79);
                  let v86 = add(d, v81);
                  trial(B, v73, v86, v75, v70, ())
                },
              }
            },
          }
        },
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
  let v2 = rocq_bigint::one();
  let v5 = rocq_bigint::twice_plus_one(v2);
  let v8 = rocq_bigint::twice_plus_one(v5);
  let v11 = rocq_bigint::twice_plus_one(v8);
  let v14 = rocq_bigint::twice_plus_one(v11);
  let v17 = rocq_bigint::twice(v14);
  let v20 = rocq_bigint::twice_plus_one(v17);
  let v23 = rocq_bigint::twice(v20);
  let v26 = rocq_bigint::twice(v23);
  let v29 = rocq_bigint::twice(v26);
  let v32 = rocq_bigint::identity(v29);
  v32
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
  let v6 = rocq_bigint::zero();
  let v10 = Rc::clone(&d);
  let v12 = ltb(v6, v10);
  match bdec(v12) {
    sumbool::left => {
      let v19 = Rc::clone(&d);
      match even(v19) {
        true => {
          let v24 = rocq_bigint::one();
          let v27 = rocq_bigint::twice(v24);
          let v29 = rocq_bigint::identity(v27);
          let v34 = div(d, v29);
          strip(v34, add_1(s, 1u64), ())
        },
        false => {
          (d, s)
        },
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
  let v18 = pm_loop(b, e, m, acc, ());
  v18
}

// Rocq: Bigfactoring.bigfactoring_implem.pm_loop (local: pm_loop)
// Variant: uncurried, lifted
pub fn pm_loop(b: Rc<BigInt>, e: Rc<BigInt>, m: Rc<BigInt>, acc: Rc<BigInt>, _H: ()) -> Rc<BigInt> {
  let v8 = rocq_bigint::zero();
  let v12 = Rc::clone(&e);
  let v14 = ltb(v8, v12);
  let v95 = match bdec(v14) {
    sumbool::left => {
      let v22 = Rc::clone(&b);
      let v25 = Rc::clone(&b);
      let v27 = mul_owned(v22, v25);
      let v31 = Rc::clone(&m);
      let v32 = modulo(v27, v31);
      let v35 = rocq_bigint::one();
      let v38 = rocq_bigint::twice(v35);
      let v40 = rocq_bigint::identity(v38);
      let v43 = Rc::clone(&e);
      let v46 = div(v43, v40);
      let v51 = match odd(e) {
        true => {
          let v59 = mul_owned(acc, b);
          let v63 = Rc::clone(&m);
          let v65 = modulo(v59, v63);
          v65
        },
        false => {
          std::mem::drop(b);
          acc
        },
      };
      let v84 = pm_loop(v32, v46, m, v51, ());
      v84
    },
    sumbool::right => {
      std::mem::drop(b);
      std::mem::drop(e);
      let v92 = modulo(acc, m);
      v92
    },
  };
  v95
}

// Rocq: Bigfactoring.bigfactoring_implem.powmod
// Variant: uncurried
pub fn powmod(b: Rc<BigInt>, e: Rc<BigInt>, m: Rc<BigInt>) -> Rc<BigInt> {
  let v9 = Rc::clone(&m);
  let v10 = modulo(b, v9);
  let v12 = rocq_bigint::one();
  let v14 = rocq_bigint::identity(v12);
  let v24 = pm_loop_1(v10, e, m, v14);
  v24
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
  let v13 = ltb_1(0u64, k);
  match bdec(v13) {
    sumbool::left => {
      let v21 = Rc::clone(&x);
      let v25 = mul_owned(v21, x);
      let v29 = Rc::clone(&n);
      let x_1 = modulo(v25, v29);
      let v34 = rocq_bigint::one();
      let v36 = rocq_bigint::identity(v34);
      let v39 = Rc::clone(&n);
      let v42 = sub(v39, v36);
      let v45 = Rc::clone(&x_1);
      match eqb(v45, v42) {
        true => {
          std::mem::drop(x_1);
          std::mem::drop(n);
          true
        },
        false => {
          sq_loop(n, x_1, sub_1(k, 1u64), ())
        },
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
  let v11 = Rc::clone(&n);
  let x = powmod(a, d, v11);
  let v16 = rocq_bigint::one();
  let v18 = rocq_bigint::identity(v16);
  let v21 = Rc::clone(&x);
  let v24 = eqb(v21, v18);
  let v28 = rocq_bigint::one();
  let v30 = rocq_bigint::identity(v28);
  let v33 = Rc::clone(&n);
  let v36 = sub(v33, v30);
  let v39 = Rc::clone(&x);
  let v42 = eqb(v39, v36);
  match orb(v24, v42) {
    true => {
      std::mem::drop(x);
      std::mem::drop(n);
      true
    },
    false => {
      sq_loop_1(n, x, sub_1(s, 1u64))
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.miller_rabin
// Variant: borrowed
pub fn miller_rabin(n: &Rc<BigInt>) -> bool {
  let v4 = rocq_bigint::one();
  let v6 = rocq_bigint::identity(v4);
  let v9 = Rc::clone(n);
  let v12 = sub(v9, v6);
  let v19 = strip_1(v12, 0u64);
  match v19 {
    (v21, v23) => {
      let s = &v21;
      let v39 = rocq_bigint::one();
      let v42 = rocq_bigint::twice(v39);
      let v44 = rocq_bigint::identity(v42);
      let v47 = Rc::clone(n);
      let v49 = Rc::clone(s);
      let v54 = mr_base(v47, v49, v23, v44);
      let v57 = rocq_bigint::one();
      let v60 = rocq_bigint::twice_plus_one(v57);
      let v62 = rocq_bigint::identity(v60);
      let v65 = Rc::clone(n);
      let v67 = Rc::clone(s);
      let v77 = andb(v54, mr_base(v65, v67, v23, v62));
      let v80 = rocq_bigint::one();
      let v83 = rocq_bigint::twice(v80);
      let v86 = rocq_bigint::twice_plus_one(v83);
      let v88 = rocq_bigint::identity(v86);
      let v91 = Rc::clone(n);
      let v93 = Rc::clone(s);
      let v103 = andb(v77, mr_base(v91, v93, v23, v88));
      let v106 = rocq_bigint::one();
      let v109 = rocq_bigint::twice_plus_one(v106);
      let v112 = rocq_bigint::twice_plus_one(v109);
      let v114 = rocq_bigint::identity(v112);
      let v117 = Rc::clone(n);
      let v119 = Rc::clone(s);
      let v129 = andb(v103, mr_base(v117, v119, v23, v114));
      let v132 = rocq_bigint::one();
      let v135 = rocq_bigint::twice(v132);
      let v138 = rocq_bigint::twice_plus_one(v135);
      let v141 = rocq_bigint::twice_plus_one(v138);
      let v143 = rocq_bigint::identity(v141);
      let v146 = Rc::clone(n);
      let v148 = Rc::clone(s);
      let v158 = andb(v129, mr_base(v146, v148, v23, v143));
      let v161 = rocq_bigint::one();
      let v164 = rocq_bigint::twice_plus_one(v161);
      let v167 = rocq_bigint::twice(v164);
      let v170 = rocq_bigint::twice_plus_one(v167);
      let v172 = rocq_bigint::identity(v170);
      let v175 = Rc::clone(n);
      let v177 = Rc::clone(s);
      let v187 = andb(v158, mr_base(v175, v177, v23, v172));
      let v190 = rocq_bigint::one();
      let v193 = rocq_bigint::twice(v190);
      let v196 = rocq_bigint::twice(v193);
      let v199 = rocq_bigint::twice(v196);
      let v202 = rocq_bigint::twice_plus_one(v199);
      let v204 = rocq_bigint::identity(v202);
      let v207 = Rc::clone(n);
      let v209 = Rc::clone(s);
      let v219 = andb(v187, mr_base(v207, v209, v23, v204));
      let v222 = rocq_bigint::one();
      let v225 = rocq_bigint::twice(v222);
      let v228 = rocq_bigint::twice(v225);
      let v231 = rocq_bigint::twice_plus_one(v228);
      let v234 = rocq_bigint::twice_plus_one(v231);
      let v236 = rocq_bigint::identity(v234);
      let v239 = Rc::clone(n);
      let v241 = Rc::clone(s);
      let v251 = andb(v219, mr_base(v239, v241, v23, v236));
      let v254 = rocq_bigint::one();
      let v257 = rocq_bigint::twice(v254);
      let v260 = rocq_bigint::twice_plus_one(v257);
      let v263 = rocq_bigint::twice_plus_one(v260);
      let v266 = rocq_bigint::twice_plus_one(v263);
      let v268 = rocq_bigint::identity(v266);
      let v271 = Rc::clone(n);
      let v273 = Rc::clone(s);
      let v283 = andb(v251, mr_base(v271, v273, v23, v268));
      let v286 = rocq_bigint::one();
      let v289 = rocq_bigint::twice_plus_one(v286);
      let v292 = rocq_bigint::twice_plus_one(v289);
      let v295 = rocq_bigint::twice(v292);
      let v298 = rocq_bigint::twice_plus_one(v295);
      let v300 = rocq_bigint::identity(v298);
      let v303 = Rc::clone(n);
      let v305 = Rc::clone(s);
      let v315 = andb(v283, mr_base(v303, v305, v23, v300));
      let v318 = rocq_bigint::one();
      let v321 = rocq_bigint::twice_plus_one(v318);
      let v324 = rocq_bigint::twice_plus_one(v321);
      let v327 = rocq_bigint::twice_plus_one(v324);
      let v330 = rocq_bigint::twice_plus_one(v327);
      let v332 = rocq_bigint::identity(v330);
      let v335 = Rc::clone(n);
      let v337 = Rc::clone(s);
      let v347 = andb(v315, mr_base(v335, v337, v23, v332));
      let v350 = rocq_bigint::one();
      let v353 = rocq_bigint::twice(v350);
      let v356 = rocq_bigint::twice(v353);
      let v359 = rocq_bigint::twice_plus_one(v356);
      let v362 = rocq_bigint::twice(v359);
      let v365 = rocq_bigint::twice_plus_one(v362);
      let v367 = rocq_bigint::identity(v365);
      let v370 = Rc::clone(n);
      andb(v347, mr_base(v370, v21, v23, v367))
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.guard
// Variant: uncurried
pub fn guard(x: Rc<BigInt>, m: Rc<BigInt>) -> bool {
  let v5 = rocq_bigint::zero();
  let v9 = Rc::clone(&x);
  andb(leb(v5, v9), ltb(x, m))
}

// Rocq: StdGalilei.bigint.zgcd_loop
// Variant: uncurried
pub fn zgcd_loop_1(a: Rc<BigInt>, b: Rc<BigInt>) -> Rc<BigInt> {
  let v12 = zgcd_loop(a, b, ());
  v12
}

// Rocq: StdGalilei.bigint.zgcd_loop (local: zgcd_loop)
// Variant: uncurried, lifted
pub fn zgcd_loop(a: Rc<BigInt>, b: Rc<BigInt>, _H: ()) -> Rc<BigInt> {
  let v5 = rocq_bigint::zero();
  let v9 = Rc::clone(&b);
  let v34 = match ltb(v5, v9) {
    true => {
      let v17 = Rc::clone(&b);
      let v18 = modulo(a, v17);
      let v29 = zgcd_loop(b, v18, ());
      v29
    },
    false => {
      std::mem::drop(b);
      a
    },
  };
  v34
}

// Rocq: Stdlib.ZArith.BinIntDef.Z.abs
pub fn abs(v0: Rc<BigInt>) -> Rc<BigInt> {
  let v5 = rocq_bigint::abs(v0);
  v5
}

// Rocq: StdGalilei.bigint.zgcd
// Variant: uncurried
pub fn zgcd(a: Rc<BigInt>, b: Rc<BigInt>) -> Rc<BigInt> {
  let v6 = abs(a);
  let v10 = abs(b);
  let v16 = zgcd_loop_1(v6, v10);
  v16
}

// Rocq: Bigfactoring.bigfactoring_implem.all_q
// Variant: uncurried
pub fn all_q_1(r: Rc<BigInt>, a: Rc<BigInt>, qs: Rc<Array<Rc<BigInt>>>, qc: u64, i: u64) -> bool {
  all_q(r, a, qs, qc, i, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.all_q (local: all_q)
// Variant: uncurried, lifted
pub fn all_q(r: Rc<BigInt>, a: Rc<BigInt>, qs: Rc<Array<Rc<BigInt>>>, qc: u64, i: u64, _H: ()) -> bool {
  let v13 = ltb_1(i, qc);
  match bdec(v13) {
    sumbool::left => {
      let v17 = &qs;
      let q = rocq_array::get::<Rc<BigInt>>(&v17, i);
      let v29 = ltb_1(0u64, i);
      let v38 = sub_1(i, 1u64);
      let v39 = &qs;
      let v42 = rocq_array::get::<Rc<BigInt>>(&v39, v38);
      let v45 = Rc::clone(&q);
      let v48 = eqb(v45, v42);
      match andb(v29, v48) {
        true => {
          std::mem::drop(q);
          all_q(r, a, qs, qc, add_1(i, 1u64), ())
        },
        false => {
          let v88 = rocq_bigint::one();
          let v90 = rocq_bigint::identity(v88);
          let v93 = Rc::clone(&r);
          let v97 = sub(v93, v90);
          let v101 = div(v97, q);
          let v104 = Rc::clone(&a);
          let v109 = Rc::clone(&r);
          let v110 = powmod(v104, v101, v109);
          let v112 = rocq_bigint::one();
          let v114 = rocq_bigint::identity(v112);
          let v120 = sub(v110, v114);
          let v124 = Rc::clone(&r);
          let v125 = zgcd(v120, v124);
          let v127 = rocq_bigint::one();
          let v129 = rocq_bigint::identity(v127);
          match eqb(v125, v129) {
            true => {
              all_q(r, a, qs, qc, add_1(i, 1u64), ())
            },
            false => {
              std::mem::drop(r);
              std::mem::drop(a);
              std::mem::drop(qs);
              false
            },
          }
        },
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
  let v9 = rocq_bigint::one();
  let v11 = rocq_bigint::identity(v9);
  let v14 = Rc::clone(&r);
  let v17 = sub(v14, v11);
  let v20 = Rc::clone(&a);
  let v25 = Rc::clone(&r);
  let v26 = powmod(v20, v17, v25);
  let v28 = rocq_bigint::one();
  let v30 = rocq_bigint::identity(v28);
  andb(eqb(v26, v30), all_q_1(r, a, qs, qc, 0u64))
}

// Rocq: Bigfactoring.bigfactoring_implem.cert_try
// Variant: uncurried
pub fn cert_try_1(r: Rc<BigInt>, qs: Rc<Array<Rc<BigInt>>>, qc: u64, a: Rc<BigInt>, k: u64) -> bool {
  cert_try(r, qs, qc, a, k, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.cert_try (local: cert_try)
// Variant: uncurried, lifted
pub fn cert_try(r: Rc<BigInt>, qs: Rc<Array<Rc<BigInt>>>, qc: u64, a: Rc<BigInt>, k: u64, _H: ()) -> bool {
  let v15 = ltb_1(0u64, k);
  match bdec(v15) {
    sumbool::left => {
      let v22 = Rc::clone(&r);
      let v25 = Rc::clone(&a);
      let v28 = Rc::clone(&qs);
      match lucas_ok(v22, v25, v28, qc) {
        true => {
          std::mem::drop(r);
          std::mem::drop(qs);
          std::mem::drop(a);
          true
        },
        false => {
          let v39 = rocq_bigint::one();
          let v41 = rocq_bigint::identity(v39);
          let v46 = add(a, v41);
          cert_try(r, qs, qc, v46, sub_1(k, 1u64), ())
        },
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
  let v5 = rocq_bigint::one();
  let v8 = rocq_bigint::twice(v5);
  let v10 = rocq_bigint::identity(v8);
  cert_try_1(r, qs, qc, v10, 1000u64)
}

// Rocq: Bigfactoring.bigfactoring_implem.fallback
// Variant: uncurried
pub fn fallback(m: Rc<BigInt>, lo: Rc<BigInt>, acc: Rc<Array<Rc<BigInt>>>, cnt: u64) -> (Rc<Array<Rc<BigInt>>>, u64) {
  let v7 = rocq_bigint::one();
  let v10 = rocq_bigint::twice(v7);
  let v12 = rocq_bigint::identity(v10);
  let v15 = Rc::clone(&m);
  let v19 = add(v15, v12);
  let v29 = trial_1(v19, m, lo, acc, cnt);
  match v29 {
    (v31, v33) => {
      match v31 {
        (v36, v38) => {
          match v36 {
            (v41, v43) => {
              let z = &v41;
              let v48 = rocq_bigint::one();
              let v51 = rocq_bigint::identity(v48);
              let v54 = Rc::clone(z);
              match ltb(v51, v54) {
                true => {
                  std::mem::drop(v43);
                  push(v38, v33, v41)
                },
                false => {
                  std::mem::drop(v43);
                  std::mem::drop(v41);
                  (v38, v33)
                },
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
  let v8 = Rc::clone(&y);
  let v12 = mul_owned(v8, y);
  let v17 = add(v12, c);
  let v22 = modulo(v17, n);
  v22
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_iter
// Variant: uncurried
pub fn rho_iter_1(n: Rc<BigInt>, c: Rc<BigInt>, y: Rc<BigInt>, k: u64) -> Rc<BigInt> {
  let v18 = rho_iter(n, c, y, k, ());
  v18
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_iter (local: rho_iter)
// Variant: uncurried, lifted
pub fn rho_iter(n: Rc<BigInt>, c: Rc<BigInt>, y: Rc<BigInt>, k: u64, _H: ()) -> Rc<BigInt> {
  let v14 = ltb_1(0u64, k);
  let v55 = match bdec(v14) {
    sumbool::left => {
      let v21 = Rc::clone(&n);
      let v24 = Rc::clone(&c);
      let v27 = rho_f(v21, v24, y);
      let v50 = rho_iter(n, c, v27, sub_1(k, 1u64), ());
      v50
    },
    sumbool::right => {
      std::mem::drop(n);
      std::mem::drop(c);
      y
    },
  };
  v55
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_batch
// Variant: uncurried
pub fn rho_batch_1(n: Rc<BigInt>, c: Rc<BigInt>, x: Rc<BigInt>, y: Rc<BigInt>, q: Rc<BigInt>, k: u64) -> (Rc<BigInt>, Rc<BigInt>) {
  rho_batch(n, c, x, y, q, k, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_batch (local: rho_batch)
// Variant: uncurried, lifted
pub fn rho_batch(n: Rc<BigInt>, c: Rc<BigInt>, x: Rc<BigInt>, y: Rc<BigInt>, q: Rc<BigInt>, k: u64, _H: ()) -> (Rc<BigInt>, Rc<BigInt>) {
  let v16 = ltb_1(0u64, k);
  match bdec(v16) {
    sumbool::left => {
      let v23 = Rc::clone(&n);
      let v26 = Rc::clone(&c);
      let y_1 = rho_f(v23, v26, y);
      let v36 = Rc::clone(&x);
      let v39 = Rc::clone(&y_1);
      let v41 = sub(v36, v39);
      let v43 = abs(v41);
      let v49 = mul_owned(q, v43);
      let v53 = Rc::clone(&n);
      let v54 = modulo(v49, v53);
      rho_batch(n, c, x, y_1, v54, sub_1(k, 1u64), ())
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
  let v15 = ltb_1(k, r);
  let v23 = add_1(k, __rocq_global_1089);
  let v34 = andb(v15, ltb_1(k, v23));
  match bdec(v34) {
    sumbool::left => {
      let v44 = sub_1(r, k);
      let v45 = __rocq_global_1089;
      let t = match ltb_1(v44, v45) {
        true => {
          sub_1(r, k)
        },
        false => {
          __rocq_global_1089
        },
      };
      let v67 = Rc::clone(&n);
      let v70 = Rc::clone(&c);
      let v73 = Rc::clone(&x);
      let v76 = Rc::clone(&y);
      let v81 = rho_batch_1(v67, v70, v73, v76, q, t);
      match v81 {
        (v83, v85) => {
          let y_ = &v85;
          let v90 = Rc::clone(y_);
          let v93 = Rc::clone(&n);
          let g = zgcd(v90, v93);
          let v97 = rocq_bigint::one();
          let v99 = rocq_bigint::identity(v97);
          let v102 = Rc::clone(&g);
          match eqb(v102, v99) {
            true => {
              std::mem::drop(g);
              std::mem::drop(y);
              rho_inner(n, c, x, v83, v85, r, add_1(k, __rocq_global_1089), ())
            },
            false => {
              std::mem::drop(c);
              std::mem::drop(x);
              std::mem::drop(n);
              (((g, y), v83), v85)
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(n);
      std::mem::drop(c);
      std::mem::drop(x);
      let v163 = rocq_bigint::one();
      let v166 = rocq_bigint::identity(v163);
      let v170 = Rc::clone(&y);
      (((v166, v170), y), q)
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
  let v21 = rho_back(n, c, x, ys, k, ());
  v21
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_back (local: rho_back)
// Variant: uncurried, lifted
pub fn rho_back(n: Rc<BigInt>, c: Rc<BigInt>, x: Rc<BigInt>, ys: Rc<BigInt>, k: u64, _H: ()) -> Rc<BigInt> {
  let v15 = ltb_1(0u64, k);
  let v94 = match bdec(v15) {
    sumbool::left => {
      let v22 = Rc::clone(&n);
      let v25 = Rc::clone(&c);
      let ys_1 = rho_f(v22, v25, ys);
      let v34 = Rc::clone(&x);
      let v37 = Rc::clone(&ys_1);
      let v39 = sub(v34, v37);
      let v42 = abs(v39);
      let v46 = Rc::clone(&n);
      let g = zgcd(v42, v46);
      let v50 = rocq_bigint::one();
      let v52 = rocq_bigint::identity(v50);
      let v55 = Rc::clone(&g);
      let v89 = match eqb(v55, v52) {
        true => {
          std::mem::drop(g);
          let v84 = rho_back(n, c, x, ys_1, sub_1(k, 1u64), ());
          v84
        },
        false => {
          std::mem::drop(ys_1);
          std::mem::drop(n);
          std::mem::drop(c);
          std::mem::drop(x);
          g
        },
      };
      v89
    },
    sumbool::right => {
      std::mem::drop(c);
      std::mem::drop(x);
      std::mem::drop(ys);
      n
    },
  };
  v94
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_outer
// Variant: uncurried
pub fn rho_outer_1(n: Rc<BigInt>, c: Rc<BigInt>, y: Rc<BigInt>, q: Rc<BigInt>, r: u64) -> Rc<BigInt> {
  let v21 = rho_outer(n, c, y, q, r, ());
  v21
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_outer (local: rho_outer)
// Variant: uncurried, lifted
pub fn rho_outer(n: Rc<BigInt>, c: Rc<BigInt>, y: Rc<BigInt>, q: Rc<BigInt>, r: u64, _H: ()) -> Rc<BigInt> {
  let v9 = Rc::clone(&n);
  let v12 = Rc::clone(&c);
  let v15 = Rc::clone(&y);
  let y_1 = rho_iter_1(v9, v12, v15, r);
  let v24 = Rc::clone(&n);
  let v27 = Rc::clone(&c);
  let v30 = Rc::clone(&y);
  let v39 = rho_inner_1(v24, v27, v30, y_1, q, r, 0u64);
  let v177 = match v39 {
    (v41, v43) => {
      let v174 = match v41 {
        (v46, v48) => {
          let v171 = match v46 {
            (v51, v53) => {
              let ys = &v51;
              let v58 = rocq_bigint::one();
              let v60 = rocq_bigint::identity(v58);
              let v62 = Rc::clone(ys);
              let v168 = match eqb(v62, v60) {
                true => {
                  let v75 = ltb_1(r, __rocq_global_1021);
                  let v84 = mul_1(r, 2u64);
                  let v95 = andb(v75, ltb_1(r, v84));
                  let v129 = match bdec(v95) {
                    sumbool::left => {
                      std::mem::drop(y);
                      std::mem::drop(v53);
                      std::mem::drop(v51);
                      let v123 = rho_outer(n, c, v48, v43, mul_1(r, 2u64), ());
                      v123
                    },
                    sumbool::right => {
                      std::mem::drop(n);
                      std::mem::drop(c);
                      std::mem::drop(y);
                      std::mem::drop(v53);
                      std::mem::drop(v51);
                      std::mem::drop(v48);
                      std::mem::drop(v43);
                      let v126 = rocq_bigint::zero();
                      v126
                    },
                  };
                  v129
                },
                false => {
                  let v133 = Rc::clone(ys);
                  let v136 = Rc::clone(&n);
                  let v165 = match eqb(v133, v136) {
                    true => {
                      std::mem::drop(v48);
                      std::mem::drop(v43);
                      std::mem::drop(v51);
                      let v160 = rho_back_1(n, c, y, v53, add_1(__rocq_global_1089, 1u64));
                      v160
                    },
                    false => {
                      std::mem::drop(c);
                      std::mem::drop(y);
                      std::mem::drop(n);
                      std::mem::drop(v48);
                      std::mem::drop(v43);
                      std::mem::drop(v53);
                      v51
                    },
                  };
                  v165
                },
              };
              v168
            },
          };
          v171
        },
      };
      v174
    },
  };
  v177
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_try
// Variant: uncurried
pub fn rho_try_1(n: Rc<BigInt>, c: Rc<BigInt>, k: u64) -> Rc<BigInt> {
  let v15 = rho_try(n, c, k, ());
  v15
}

// Rocq: Bigfactoring.bigfactoring_implem.rho_try (local: rho_try)
// Variant: uncurried, lifted
pub fn rho_try(n: Rc<BigInt>, c: Rc<BigInt>, k: u64, _H: ()) -> Rc<BigInt> {
  let v13 = ltb_1(0u64, k);
  let v111 = match bdec(v13) {
    sumbool::left => {
      let v19 = rocq_bigint::one();
      let v22 = rocq_bigint::twice(v19);
      let v24 = rocq_bigint::identity(v22);
      let v26 = rocq_bigint::one();
      let v28 = rocq_bigint::identity(v26);
      let v33 = Rc::clone(&n);
      let v36 = Rc::clone(&c);
      let g = rho_outer_1(v33, v36, v24, v28, 1u64);
      let v47 = rocq_bigint::one();
      let v50 = rocq_bigint::identity(v47);
      let v54 = Rc::clone(&g);
      let v55 = ltb(v50, v54);
      let v59 = Rc::clone(&g);
      let v62 = Rc::clone(&n);
      let v63 = ltb(v59, v62);
      let v105 = match andb(v55, v63) {
        true => {
          std::mem::drop(n);
          std::mem::drop(c);
          g
        },
        false => {
          std::mem::drop(g);
          let v74 = rocq_bigint::one();
          let v76 = rocq_bigint::identity(v74);
          let v81 = add(c, v76);
          let v102 = rho_try(n, v81, sub_1(k, 1u64), ());
          v102
        },
      };
      v105
    },
    sumbool::right => {
      std::mem::drop(n);
      std::mem::drop(c);
      let v108 = rocq_bigint::zero();
      v108
    },
  };
  v111
}

// Rocq: Bigfactoring.bigfactoring_implem.rho
// Variant: borrowed
pub fn rho(n: &Rc<BigInt>) -> Rc<BigInt> {
  let v3 = rocq_bigint::one();
  let v5 = rocq_bigint::identity(v3);
  let v10 = Rc::clone(n);
  let v16 = rho_try_1(v10, v5, 20u64);
  v16
}

// Rocq: Bigfactoring.bigfactoring_implem.fac
// Variant: uncurried
pub fn fac_1(m: Rc<BigInt>, lo: Rc<BigInt>, acc: Rc<Array<Rc<BigInt>>>, cnt: u64) -> (Rc<Array<Rc<BigInt>>>, u64) {
  fac(m, lo, acc, cnt, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.fac (local: fac)
// Variant: uncurried, lifted
pub fn fac(m: Rc<BigInt>, lo: Rc<BigInt>, acc: Rc<Array<Rc<BigInt>>>, cnt: u64, _H: ()) -> (Rc<Array<Rc<BigInt>>>, u64) {
  let v12 = B0(());
  let v16 = Rc::clone(&m);
  let v23 = trial_1(v12, v16, lo, acc, cnt);
  match v23 {
    (v25, v27) => {
      match v25 {
        (v30, v32) => {
          match v30 {
            (v35, v37) => {
              let d = &v35;
              let r = &v37;
              let v45 = mul(r, r);
              let v47 = Rc::clone(d);
              match ltb(v47, v45) {
                true => {
                  let v54 = rocq_bigint::one();
                  let v57 = rocq_bigint::identity(v54);
                  let v60 = Rc::clone(d);
                  match ltb(v57, v60) {
                    true => {
                      std::mem::drop(m);
                      std::mem::drop(v37);
                      push(v32, v27, v35)
                    },
                    false => {
                      std::mem::drop(m);
                      std::mem::drop(v37);
                      std::mem::drop(v35);
                      (v32, v27)
                    },
                  }
                },
                false => {
                  let v85 = d;
                  match miller_rabin(v85) {
                    true => {
                      let v92 = rocq_bigint::one();
                      let v94 = rocq_bigint::identity(v92);
                      let v96 = Rc::clone(d);
                      let v100 = sub(v96, v94);
                      let v105 = guard(v100, m);
                      match bdec(v105) {
                        sumbool::left => {
                          let v111 = rocq_bigint::one();
                          let v113 = rocq_bigint::identity(v111);
                          let v115 = Rc::clone(d);
                          let v118 = sub(v115, v113);
                          let v120 = rocq_bigint::one();
                          let v123 = rocq_bigint::twice(v120);
                          let v125 = rocq_bigint::identity(v123);
                          let v127 = rocq_bigint::zero();
                          let v132 = rocq_array::make::<Rc<BigInt>>(__rocq_global_729, v127);
                          let v148 = fac(v118, v125, v132, 0u64, ());
                          match v148 {
                            (v150, v152) => {
                              let v156 = Rc::clone(d);
                              match certify(v156, v150, v152) {
                                true => {
                                  std::mem::drop(v37);
                                  push(v32, v27, v35)
                                },
                                false => {
                                  fallback(v35, v37, v32, v27)
                                },
                              }
                            },
                          }
                        },
                        sumbool::right => {
                          fallback(v35, v37, v32, v27)
                        },
                      }
                    },
                    false => {
                      let g = rho(d);
                      let v213 = rocq_bigint::one();
                      let v216 = rocq_bigint::identity(v213);
                      let v220 = Rc::clone(&g);
                      let v221 = ltb(v216, v220);
                      let v225 = Rc::clone(&g);
                      let v227 = Rc::clone(d);
                      let v233 = andb(v221, ltb(v225, v227));
                      let v237 = Rc::clone(d);
                      let v240 = Rc::clone(&g);
                      let v241 = modulo(v237, v240);
                      let v242 = rocq_bigint::zero();
                      let v247 = eqb(v241, v242);
                      match andb(v233, v247) {
                        true => {
                          let v258 = Rc::clone(&g);
                          let v261 = Rc::clone(&m);
                          let v263 = guard(v258, v261);
                          match bdec(v263) {
                            sumbool::left => {
                              let v271 = Rc::clone(d);
                              let v274 = Rc::clone(&g);
                              let v276 = div(v271, v274);
                              let v281 = guard(v276, m);
                              match bdec(v281) {
                                sumbool::left => {
                                  let v290 = B0(());
                                  let v296 = Rc::clone(&g);
                                  let v305 = fac(v296, v290, v32, v27, ());
                                  match v305 {
                                    (v307, v309) => {
                                      std::mem::drop(v37);
                                      let v316 = div(v35, g);
                                      let v322 = B0(());
                                      fac(v316, v322, v307, v309, ())
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
                        },
                        false => {
                          std::mem::drop(g);
                          std::mem::drop(m);
                          fallback(v35, v37, v32, v27)
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

// Rocq: Bigfactoring.bigfactoring_implem.copy
// Variant: uncurried
pub fn copy_1(src: Rc<Array<Rc<BigInt>>>, dst: Rc<Array<Rc<BigInt>>>, n: u64, i: u64) -> Rc<Array<Rc<BigInt>>> {
  copy(src, dst, n, i, ())
}

// Rocq: Bigfactoring.bigfactoring_implem.copy (local: copy)
// Variant: uncurried, lifted
pub fn copy(src: Rc<Array<Rc<BigInt>>>, dst: Rc<Array<Rc<BigInt>>>, n: u64, i: u64, _H: ()) -> Rc<Array<Rc<BigInt>>> {
  let v12 = ltb_1(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v16 = &src;
      let v19 = rocq_array::get::<Rc<BigInt>>(&v16, i);
      let v26 = rocq_array::set::<Rc<BigInt>>(dst, i, v19);
      copy(src, v26, n, add_1(i, 1u64), ())
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
  let v12 = ltb_1(0u64, j);
  match bdec(v12) {
    sumbool::left => {
      let v23 = sub_1(j, 1u64);
      let v24 = &a;
      let x = rocq_array::get::<Rc<BigInt>>(&v24, v23);
      let v28 = &a;
      let y = rocq_array::get::<Rc<BigInt>>(&v28, j);
      let v35 = Rc::clone(&y);
      let v38 = Rc::clone(&x);
      match ltb(v35, v38) {
        true => {
          let v56 = rocq_array::set::<Rc<BigInt>>(a, sub_1(j, 1u64), y);
          let v62 = rocq_array::set::<Rc<BigInt>>(v56, j, x);
          sink(v62, sub_1(j, 1u64), ())
        },
        false => {
          std::mem::drop(y);
          std::mem::drop(x);
          a
        },
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
  let v11 = ltb_1(i, n);
  match bdec(v11) {
    sumbool::left => {
      let v20 = sink_1(a, i);
      isort(v20, n, add_1(i, 1u64), ())
    },
    sumbool::right => {
      a
    },
  }
}

// Rocq: Bigfactoring.bigfactoring_implem.bigfactoring_impl
pub fn bigfactoring_impl(n: Rc<BigInt>) -> Rc<Array<Rc<BigInt>>> {
  let v3 = rocq_bigint::one();
  let v6 = rocq_bigint::twice(v3);
  let v8 = rocq_bigint::identity(v6);
  let v10 = rocq_bigint::zero();
  let v15 = rocq_array::make::<Rc<BigInt>>(__rocq_global_729, v10);
  let v26 = fac_1(n, v8, v15, 0u64);
  match v26 {
    (v28, v30) => {
      let v33 = rocq_bigint::zero();
      let v38 = rocq_array::make::<Rc<BigInt>>(v30, v33);
      let out = copy_1(v28, v38, v30, 0u64);
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

pub fn run() -> Rc<dyn Fn(Rc<BigInt>) -> Rc<Array<Rc<BigInt>>>> {
  let v0: Rc<dyn Fn(Rc<BigInt>) -> Rc<Array<Rc<BigInt>>>> = __rocq_global_1794.with(Clone::clone);
  v0
}
const __rocq_global_729: u64 = 128u64;
const __rocq_global_1021: u64 = 33554432u64;
const __rocq_global_1089: u64 = 128u64;
std::thread_local! { static __rocq_global_1794: Rc<dyn Fn(Rc<BigInt>) -> Rc<Array<Rc<BigInt>>>> = bigfactoring(); }