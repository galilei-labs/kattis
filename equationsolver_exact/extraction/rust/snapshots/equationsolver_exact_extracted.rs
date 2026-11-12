// Generated from OwnedANF. This printer is not verified.
#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::{self as a, Array};
#[allow(unused_imports)] use rocq_bigint::{self as b, BigInt};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub struct shr_record {
  pub shr_m: Rc<BigInt>,
  pub shr_r: bool,
  pub shr_s: bool,
}

impl Clone for shr_record {
  fn clone(&self) -> Self {
    match self {
      shr_record { shr_m: __field0, shr_r: __field1, shr_s: __field2 } => shr_record { shr_m: Clone::clone(__field0), shr_r: Clone::clone(__field1), shr_s: Clone::clone(__field2) },
    }
  }
}

pub enum spec_float {
  S754_zero { s: bool },
  S754_infinity { s: bool },
  S754_nan,
  S754_finite { s: bool, m: Rc<BigInt>, e: Rc<BigInt> },
}

impl Clone for spec_float {
  fn clone(&self) -> Self {
    match self {
      spec_float::S754_zero { s: __field0 } => spec_float::S754_zero { s: Clone::clone(__field0) },
      spec_float::S754_infinity { s: __field0 } => spec_float::S754_infinity { s: Clone::clone(__field0) },
      spec_float::S754_nan => spec_float::S754_nan,
      spec_float::S754_finite { s: __field0, m: __field1, e: __field2 } => spec_float::S754_finite { s: Clone::clone(__field0), m: Clone::clone(__field1), e: Clone::clone(__field2) },
    }
  }
}

pub enum location {
  loc_Exact,
  loc_Inexact(std::cmp::Ordering),
}

impl Clone for location {
  fn clone(&self) -> Self {
    match self {
      location::loc_Exact => location::loc_Exact,
      location::loc_Inexact(__field0) => location::loc_Inexact(Clone::clone(__field0)),
    }
  }
}

pub enum outcome<V: 'static> {
  Unique(V),
  Multiple,
  Inconsistent,
}

impl<V: Clone + 'static> Clone for outcome<V> {
  fn clone(&self) -> Self {
    match self {
      outcome::Unique(__field0) => outcome::Unique(Clone::clone(__field0)),
      outcome::Multiple => outcome::Multiple,
      outcome::Inconsistent => outcome::Inconsistent,
    }
  }
}

pub struct fstate {
  pub fs_M: Rc<Array<f64>>,
  pub fs_Q: Rc<Array<f64>>,
  pub fs_r: u64,
  pub fs_pc: Rc<Array<u64>>,
  pub fs_perm: Rc<Array<u64>>,
}

impl Clone for fstate {
  fn clone(&self) -> Self {
    match self {
      fstate { fs_M: __field0, fs_Q: __field1, fs_r: __field2, fs_pc: __field3, fs_perm: __field4 } => fstate { fs_M: Clone::clone(__field0), fs_Q: Clone::clone(__field1), fs_r: Clone::clone(__field2), fs_pc: Clone::clone(__field3), fs_perm: Clone::clone(__field4) },
    }
  }
}

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<std::cmp::Ordering>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::PositiveTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::NaturalTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::IntegerTag>; };

pub type uint = u64;

pub type dy = (Rc<BigInt>, Rc<BigInt>);

// Rocq: Corelib.Floats.PrimFloat.zero
pub fn zero() -> f64 {
  f64::from_bits(0u64)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.thr_scale
pub fn thr_scale() -> f64 {
  f64::from_bits(4427038433705197568u64)
}

// Rocq: Corelib.Floats.PrimFloat.one
pub fn one() -> f64 {
  f64::from_bits(4607182418800017408u64)
}

// Rocq: Corelib.Floats.PrimFloat.infinity
pub fn infinity() -> f64 {
  f64::from_bits(9218868437227405312u64)
}

// Rocq: Corelib.Floats.PrimFloat.neg_zero
pub fn neg_zero() -> f64 {
  f64::from_bits(9223372036854775808u64)
}

// Rocq: Corelib.Floats.PrimFloat.neg_infinity
pub fn neg_infinity() -> f64 {
  f64::from_bits(18442240474082181120u64)
}

// Rocq: Corelib.Floats.PrimFloat.nan
pub fn nan() -> f64 {
  f64::from_bits(9221120237041090560u64)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.compare
// Variant: uncurried
pub fn compare(v0: Rc<BigInt>, v1: Rc<BigInt>) -> std::cmp::Ordering {
  b::compare(v0, v1)
}

// Rocq: Corelib.BinNums.PosDef.Pos.succ
pub fn succ(v0: Rc<BigInt>) -> Rc<BigInt> {
  let v5 = b::succ(v0);
  v5
}

// Rocq: Corelib.BinNums.IntDef.Z.add
// Variant: uncurried
pub fn add_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = b::add(v0, v1);
  v8
}

// Rocq: Corelib.BinNums.IntDef.Z.opp
pub fn opp(v0: Rc<BigInt>) -> Rc<BigInt> {
  let v5 = b::neg(v0);
  v5
}

// Rocq: Corelib.BinNums.IntDef.Z.sub
// Variant: uncurried
pub fn sub(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = b::sub(v0, v1);
  v8
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z
pub fn to_Z(v0: u64) -> Rc<BigInt> {
  let v5 = b::of_uint63(v0);
  v5
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  match b_1 {
    true => {
      sumbool::left
    },
    false => {
      sumbool::right
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.wloop (local: wloop)
// Variant: uncurried, lifted
pub fn wloop<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St, _H: ()) -> St {
  let v13 = ltb(i, hi);
  match bdec(v13) {
    sumbool::left => {
      let v17: &Rc<dyn Fn(u64, St) -> bool> = &cont;
      let v21 = Clone::clone(&s);
      let v23 = v17(i, v21);
      match v23 {
        true => {
          let v32 = add(i, 1u64);
          let v33: &Rc<dyn Fn(u64, St) -> St> = &f;
          let v38 = v33(i, s);
          wloop::<St>(hi, cont, f, v32, v38, ())
        },
        false => {
          std::mem::drop(f);
          std::mem::drop(cont);
          s
        },
      }
    },
    sumbool::right => {
      std::mem::drop(cont);
      std::mem::drop(f);
      s
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop_1::<St>(hi, cont, f, i, s)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_r
pub fn fs_r_owned(f: Rc<fstate>) -> u64 {
  let v3 = Clone::clone((&(&**&f).fs_r));
  std::mem::drop(f);
  v3
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_r
// Variant: borrowed
pub fn fs_r(f: &Rc<fstate>) -> u64 {
  let v1 = f;
  Clone::clone((&(&**v1).fs_r))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_M
pub fn fs_M_owned(f: Rc<fstate>) -> Rc<Array<f64>> {
  let v3 = Rc::clone((&(&**&f).fs_M));
  std::mem::drop(f);
  v3
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_M
// Variant: borrowed
pub fn fs_M(f: &Rc<fstate>) -> Rc<Array<f64>> {
  let v1 = f;
  Rc::clone((&(&**v1).fs_M))
}

// Rocq: Corelib.Floats.PrimFloat.abs
pub fn abs_1(v0: f64) -> f64 {
  rocq_float64::abs(v0)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Corelib.Floats.PrimFloat.ltb
// Variant: uncurried
pub fn ltb_1(v0: f64, v1: f64) -> bool {
  rocq_float64::ltb(v0, v1)
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let v3 = Clone::clone((&(&p).1));
  std::mem::drop(p);
  v3
}

// Rocq: Corelib.Floats.PrimFloat.leb
// Variant: uncurried
pub fn leb_1(v0: f64, v1: f64) -> bool {
  rocq_float64::leb(v0, v1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.swap_f
// Variant: uncurried
pub fn swap_f(T: Rc<Array<f64>>, w: u64, p: u64, r: u64) -> Rc<Array<f64>> {
  let v5 = {
    move |_v6: u64, v7: Rc<Array<f64>>| -> bool {
      std::mem::drop(v7);
      true
    }
  };
  let v12: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(v5);
  let v13: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = v12;
  let v20 = {
    let __anf_capture_25 = w;
    move |j: u64, T: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let r = &r;
      let p = &p;
      let v40 = add(mul(Clone::clone(r), Clone::clone(&__anf_capture_25)), j);
      let v41 = &T;
      let x = a::get::<f64>(&v41, v40);
      let v56 = add(mul(Clone::clone(p), Clone::clone(&__anf_capture_25)), j);
      let v57 = &T;
      let y = a::get::<f64>(&v57, v56);
      let v79 = a::set::<f64>(T, add(mul(Clone::clone(r), Clone::clone(&__anf_capture_25)), j), y);
      let v83 = Clone::clone(p);
      let v85 = Clone::clone(&__anf_capture_25);
      a::set::<f64>(v79, add(mul(v83, v85), j), x)
    }
  };
  let v101: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new(v20);
  loop_::<Rc<Array<f64>>>(w, v13, v101, 0u64, T)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_Q
pub fn fs_Q(f: Rc<fstate>) -> Rc<Array<f64>> {
  let v3 = Rc::clone((&(&**&f).fs_Q));
  std::mem::drop(f);
  v3
}

// Rocq: Corelib.Floats.PrimFloat.div
// Variant: uncurried
pub fn div_1(v0: f64, v1: f64) -> f64 {
  rocq_float64::div(v0, v1)
}

// Rocq: Corelib.Floats.PrimFloat.sub
// Variant: uncurried
pub fn sub_1(v0: f64, v1: f64) -> f64 {
  rocq_float64::sub(v0, v1)
}

// Rocq: Corelib.Floats.PrimFloat.mul
// Variant: uncurried
pub fn mul_1(v0: f64, v1: f64) -> f64 {
  rocq_float64::mul(v0, v1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.axpy_row
// Variant: uncurried
pub fn axpy_row(T: Rc<Array<f64>>, w: u64, i: u64, r: u64, lo: u64, f: f64) -> Rc<Array<f64>> {
  let v7 = {
    move |_v8: u64, v9: Rc<Array<f64>>| -> bool {
      std::mem::drop(v9);
      true
    }
  };
  let v14: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(v7);
  let v15: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = v14;
  let v24 = {
    let __anf_capture_29 = w;
    move |j: u64, T: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let i = &i;
      let r = &r;
      let w = &__anf_capture_29;
      let f = &f;
      let v46 = add(mul(Clone::clone(i), Clone::clone(w)), j);
      let v59 = add(mul(Clone::clone(i), Clone::clone(w)), j);
      let v60 = &T;
      let v63 = a::get::<f64>(&v60, v59);
      let v76 = add(mul(Clone::clone(r), Clone::clone(w)), j);
      let v77 = &T;
      let v80 = a::get::<f64>(&v77, v76);
      let v82 = Clone::clone(f);
      a::set::<f64>(T, v46, sub_1(v63, mul_1(v82, v80)))
    }
  };
  let v100: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new(v24);
  loop_::<Rc<Array<f64>>>(w, v15, v100, lo, T)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_perm
pub fn fs_perm(f: Rc<fstate>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&f).fs_perm));
  std::mem::drop(f);
  v3
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_pc
pub fn fs_pc(f: Rc<fstate>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&f).fs_pc));
  std::mem::drop(f);
  v3
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fwd_col
// Variant: uncurried
pub fn fwd_col(n: u64, w: u64, thr: Rc<Array<f64>>, c: u64, st: Rc<fstate>) -> Rc<fstate> {
  let r = fs_r(&st);
  match ltb(r, n) {
    true => {
      let M = fs_M(&st);
      let v21 = {
        move |_v22: u64, v23: (u64, f64)| -> bool {
          std::mem::drop(v23);
          true
        }
      };
      let v28: Rc<dyn Fn(u64, (u64, f64)) -> bool> = Rc::new(v21);
      let v29: Rc<dyn Fn(u64, (u64, f64)) -> bool> = v28;
      let v36 = Rc::clone(&M);
      let v37 = {
        let __anf_capture_38 = w;
        let __anf_capture_40 = c;
        move |i: u64, pm: (u64, f64)| -> (u64, f64) {
          let w = &__anf_capture_38;
          let c = &__anf_capture_40;
          let M = &v36;
          let v59 = add(mul(i, Clone::clone(w)), Clone::clone(c));
          let v = abs_1(a::get::<f64>(&M, v59));
          let v68 = Clone::clone(&pm);
          let v71 = snd::<u64, f64>(v68);
          match ltb_1(v71, v) {
            true => {
              std::mem::drop(pm);
              (i, v)
            },
            false => {
              pm
            },
          }
        }
      };
      let v90: Rc<dyn Fn(u64, (u64, f64)) -> (u64, f64)> = Rc::new(v37);
      let v97 = (r, __rocq_global_371);
      let v109 = loop_::<(u64, f64)>(n, v29, v90, r, v97);
      match v109 {
        (v111, v113) => {
          let v116 = &thr;
          let v119 = a::get::<f64>(&v116, c);
          match leb_1(v113, v119) {
            true => {
              std::mem::drop(M);
              std::mem::drop(thr);
              st
            },
            false => {
              std::mem::drop(thr);
              let M_1 = swap_f(M, w, v111, r);
              let v142 = Rc::clone(&st);
              let v144 = fs_Q(v142);
              let Q = swap_f(v144, n, v111, r);
              let v164 = add(mul(r, w), c);
              let v165 = &M_1;
              let piv = a::get::<f64>(&v165, v164);
              let v170 = {
                move |_v171: u64, v172: (Rc<Array<f64>>, Rc<Array<f64>>)| -> bool {
                  std::mem::drop(v172);
                  true
                }
              };
              let v177: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> bool> = Rc::new(v170);
              let v178: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> bool> = v177;
              let v189 = {
                let __anf_capture_192 = w;
                let __anf_capture_194 = c;
                let __anf_capture_196 = n;
                let __anf_capture_198 = r;
                move |i: u64, mq: (Rc<Array<f64>>, Rc<Array<f64>>)| -> (Rc<Array<f64>>, Rc<Array<f64>>) {
                  let piv = &piv;
                  let w = &__anf_capture_192;
                  let c = &__anf_capture_194;
                  let n = &__anf_capture_196;
                  let r = &__anf_capture_198;
                  match mq {
                    (v203, v205) => {
                      let Q = &v203;
                      let v221 = add(mul(i, Clone::clone(w)), Clone::clone(c));
                      let v224 = a::get::<f64>(&Q, v221);
                      let f = div_1(v224, Clone::clone(piv));
                      let v232 = 1u64;
                      let v237 = add(Clone::clone(c), v232);
                      let M = axpy_row(v203, Clone::clone(w), i, Clone::clone(r), v237, f);
                      let v270 = a::set::<f64>(M, add(mul(i, Clone::clone(w)), Clone::clone(c)), __rocq_global_371);
                      let v277 = Clone::clone(n);
                      let v281 = Clone::clone(r);
                      let v286 = axpy_row(v205, v277, i, v281, 0u64, f);
                      (v270, v286)
                    },
                  }
                }
              };
              let v298: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>)> = Rc::new(v189);
              let v324 = loop_::<(Rc<Array<f64>>, Rc<Array<f64>>)>(n, v178, v298, add(r, 1u64), (M_1, Q));
              match v324 {
                (v326, v328) => {
                  let v333 = Rc::clone(&st);
                  let pm = fs_perm(v333);
                  let v335 = &pm;
                  let x = a::get::<u64>(&v335, v111);
                  let v339 = &pm;
                  let y = a::get::<u64>(&v339, r);
                  let v350 = add(r, 1u64);
                  let v355 = fs_pc(st);
                  let v361 = a::set::<u64>(v355, r, c);
                  let v369 = a::set::<u64>(pm, v111, y);
                  let v375 = a::set::<u64>(v369, r, x);
                  Rc::new(fstate { fs_M: v326, fs_Q: v328, fs_r: v350, fs_pc: v361, fs_perm: v375 })
                },
              }
            },
          }
        },
      }
    },
    false => {
      std::mem::drop(thr);
      st
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.tab
// Variant: uncurried
pub fn tab<T: Clone + 'static>(n: u64, d: T, f: Rc<dyn Fn(u64) -> T>) -> Rc<Array<T>> {
  let v4 = {
    move |_v5: u64, v6: Rc<Array<T>>| -> bool {
      std::mem::drop(v6);
      true
    }
  };
  let v11: Rc<dyn Fn(u64, Rc<Array<T>>) -> bool> = Rc::new(v4);
  let v12: Rc<dyn Fn(u64, Rc<Array<T>>) -> bool> = v11;
  let v15 = {
    move |i: u64, t: Rc<Array<T>>| -> Rc<Array<T>> {
      let f = &f;
      let v22 = f(i);
      a::set::<T>(t, i, v22)
    }
  };
  let v32: Rc<dyn Fn(u64, Rc<Array<T>>) -> Rc<Array<T>>> = Rc::new(v15);
  let v40 = a::make::<T>(n, d);
  loop_::<Rc<Array<T>>>(n, v12, v32, 0u64, v40)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.forward
// Variant: uncurried
pub fn forward(n: u64, w: u64, thr: Rc<Array<f64>>, M: Rc<Array<f64>>, Q: Rc<Array<f64>>) -> Rc<fstate> {
  let v6 = {
    move |_v7: u64, v8: Rc<fstate>| -> bool {
      std::mem::drop(v8);
      true
    }
  };
  let v13: Rc<dyn Fn(u64, Rc<fstate>) -> bool> = Rc::new(v6);
  let v14: Rc<dyn Fn(u64, Rc<fstate>) -> bool> = v13;
  let v21 = {
    let __anf_capture_22 = n;
    move |v28: u64, v29: Rc<fstate>| -> Rc<fstate> {
      let v32 = Clone::clone(&__anf_capture_22);
      let v34 = Clone::clone(&w);
      let v36 = Rc::clone(&thr);
      fwd_col(v32, v34, v36, v28, v29)
    }
  };
  let v44: Rc<dyn Fn(u64, Rc<fstate>) -> Rc<fstate>> = Rc::new(v21);
  let v45: Rc<dyn Fn(u64, Rc<fstate>) -> Rc<fstate>> = v44;
  let v47 = 0u64;
  let v49 = 0u64;
  let v56 = a::make::<u64>(n, 0u64);
  let v59 = 0u64;
  let v60 = {
    move |i: u64| -> u64 {
      i
    }
  };
  let v64: Rc<dyn Fn(u64) -> u64> = Rc::new(v60);
  let v72 = tab::<u64>(n, v59, v64);
  loop_::<Rc<fstate>>(n, v14, v45, v47, Rc::new(fstate { fs_M: M, fs_Q: Q, fs_r: v49, fs_pc: v56, fs_perm: v72 }))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.col_thr
// Variant: uncurried
pub fn col_thr(xa: Rc<Array<Rc<Array<f64>>>>, n: u64) -> Rc<Array<f64>> {
  let v3 = {
    move |_v4: u64, v5: Rc<Array<f64>>| -> bool {
      std::mem::drop(v5);
      true
    }
  };
  let v10: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(v3);
  let v11: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = v10;
  let v16 = {
    let __anf_capture_19 = n;
    move |j: u64, T: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let xa = &xa;
      let n = &__anf_capture_19;
      let v24 = {
        move |_v25: u64, _v26: f64| -> bool {
          true
        }
      };
      let v31: Rc<dyn Fn(u64, f64) -> bool> = Rc::new(v24);
      let v32: Rc<dyn Fn(u64, f64) -> bool> = v31;
      let v34 = Rc::clone(xa);
      let v37 = {
        let __anf_capture_40 = j;
        move |i: u64, m: f64| -> f64 {
          let xa = &v34;
          let j = &__anf_capture_40;
          let v46 = Rc::clone(xa);
          let v50 = a::get::<Rc<Array<f64>>>(&v46, i);
          let v51 = &v50;
          let v53 = Clone::clone(j);
          let v55 = a::get::<f64>(&v51, v53);
          let v = abs_1(v55);
          match ltb_1(m, v) {
            true => {
              std::mem::drop(v50);
              std::mem::drop(v46);
              v
            },
            false => {
              std::mem::drop(v50);
              std::mem::drop(v46);
              m
            },
          }
        }
      };
      let v72: Rc<dyn Fn(u64, f64) -> f64> = Rc::new(v37);
      let v78 = Clone::clone(n);
      let m = loop_::<f64>(v78, v32, v72, 0u64, __rocq_global_371);
      a::set::<f64>(T, j, mul_1(m, __rocq_global_722))
    }
  };
  let v104: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new(v16);
  let v113 = a::make::<f64>(n, __rocq_global_371);
  loop_::<Rc<Array<f64>>>(n, v11, v104, 0u64, v113)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.init_M
// Variant: uncurried
pub fn init_M(xa: Rc<Array<Rc<Array<f64>>>>, xb: Rc<Array<f64>>, n: u64, w: u64) -> Rc<Array<f64>> {
  let v5 = {
    move |_v6: u64, v7: Rc<Array<f64>>| -> bool {
      std::mem::drop(v7);
      true
    }
  };
  let v12: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(v5);
  let v13: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = v12;
  let v22 = {
    let __anf_capture_25 = w;
    let __anf_capture_27 = n;
    move |i: u64, M: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let xa = &xa;
      let w = &__anf_capture_25;
      let n = &__anf_capture_27;
      let xb = &xb;
      let v34 = Rc::clone(xa);
      let row = a::get::<Rc<Array<f64>>>(&v34, i);
      std::mem::drop(v34);
      let v40 = {
        move |_v41: u64, v42: Rc<Array<f64>>| -> bool {
          std::mem::drop(v42);
          true
        }
      };
      let v47: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(v40);
      let v48: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = v47;
      let v52 = Clone::clone(w);
      let v55 = {
        let __anf_capture_56 = i;
        move |j: u64, M: Rc<Array<f64>>| -> Rc<Array<f64>> {
          let i = &__anf_capture_56;
          let w = &v52;
          let row = &row;
          let v75 = add(mul(Clone::clone(i), Clone::clone(w)), j);
          let v78 = a::get::<f64>(&row, j);
          a::set::<f64>(M, v75, v78)
        }
      };
      let v88: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new(v55);
      let v91 = 0u64;
      let M_1 = loop_::<Rc<Array<f64>>>(Clone::clone(n), v48, v88, v91, M);
      let v114 = add(mul(i, Clone::clone(w)), Clone::clone(n));
      let v117 = a::get::<f64>(&xb, i);
      a::set::<f64>(M_1, v114, v117)
    }
  };
  let v127: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new(v22);
  let v142 = a::make::<f64>(mul(n, w), __rocq_global_371);
  loop_::<Rc<Array<f64>>>(n, v13, v127, 0u64, v142)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.init_Q
pub fn init_Q(n: u64) -> Rc<Array<f64>> {
  let v2 = {
    move |_v3: u64, v4: Rc<Array<f64>>| -> bool {
      std::mem::drop(v4);
      true
    }
  };
  let v9: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(v2);
  let v10: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = v9;
  let v13 = {
    let __anf_capture_14 = n;
    move |i: u64, Q: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let v23 = Clone::clone(&__anf_capture_14);
      a::set::<f64>(Q, add(mul(i, v23), i), __rocq_global_820)
    }
  };
  let v40: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new(v13);
  let v55 = a::make::<f64>(mul(n, n), __rocq_global_371);
  loop_::<Rc<Array<f64>>>(n, v10, v40, 0u64, v55)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.transpose
// Variant: uncurried
pub fn transpose(xa: Rc<Array<Rc<Array<f64>>>>, n: u64) -> Rc<Array<f64>> {
  let v3 = {
    move |_v4: u64, v5: Rc<Array<f64>>| -> bool {
      std::mem::drop(v5);
      true
    }
  };
  let v10: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(v3);
  let v11: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = v10;
  let v16 = {
    let __anf_capture_19 = n;
    move |i: u64, T: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let xa = &xa;
      let n = &__anf_capture_19;
      let v24 = Rc::clone(xa);
      let row = a::get::<Rc<Array<f64>>>(&v24, i);
      std::mem::drop(v24);
      let v30 = {
        move |_v31: u64, v32: Rc<Array<f64>>| -> bool {
          std::mem::drop(v32);
          true
        }
      };
      let v37: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(v30);
      let v38: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = v37;
      let v40 = Clone::clone(n);
      let v45 = {
        let __anf_capture_48 = i;
        move |j: u64, T: Rc<Array<f64>>| -> Rc<Array<f64>> {
          let n = &v40;
          let i = &__anf_capture_48;
          let row = &row;
          let v65 = add(mul(j, Clone::clone(n)), Clone::clone(i));
          let v68 = a::get::<f64>(&row, j);
          a::set::<f64>(T, v65, v68)
        }
      };
      let v78: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new(v45);
      let v83 = Clone::clone(n);
      loop_::<Rc<Array<f64>>>(v83, v38, v78, 0u64, T)
    }
  };
  let v95: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new(v16);
  let v110 = a::make::<f64>(mul(n, n), __rocq_global_371);
  loop_::<Rc<Array<f64>>>(n, v11, v95, 0u64, v110)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub_2(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.scale_row
// Variant: uncurried
pub fn scale_row(T: Rc<Array<f64>>, w: u64, i: u64, piv: f64) -> Rc<Array<f64>> {
  let v5 = {
    move |_v6: u64, v7: Rc<Array<f64>>| -> bool {
      std::mem::drop(v7);
      true
    }
  };
  let v12: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(v5);
  let v13: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = v12;
  let v20 = {
    let __anf_capture_23 = w;
    move |j: u64, T: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let i = &i;
      let w = &__anf_capture_23;
      let piv = &piv;
      let v40 = add(mul(Clone::clone(i), Clone::clone(w)), j);
      let v53 = add(mul(Clone::clone(i), Clone::clone(w)), j);
      let v54 = &T;
      let v58 = a::get::<f64>(&v54, v53);
      let v61 = Clone::clone(piv);
      a::set::<f64>(T, v40, div_1(v58, v61))
    }
  };
  let v72: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new(v20);
  loop_::<Rc<Array<f64>>>(w, v13, v72, 0u64, T)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.backsub
// Variant: uncurried
pub fn backsub(n: u64, w: u64, M: Rc<Array<f64>>, Q: Rc<Array<f64>>) -> (Rc<Array<f64>>, Rc<Array<f64>>) {
  let v5 = {
    move |_v6: u64, v7: (Rc<Array<f64>>, Rc<Array<f64>>)| -> bool {
      std::mem::drop(v7);
      true
    }
  };
  let v12: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> bool> = Rc::new(v5);
  let v13: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> bool> = v12;
  let v18 = {
    let __anf_capture_21 = n;
    move |t: u64, mq: (Rc<Array<f64>>, Rc<Array<f64>>)| -> (Rc<Array<f64>>, Rc<Array<f64>>) {
      let w = &w;
      let n = &__anf_capture_21;
      match mq {
        (v26, v28) => {
          let Q = &v26;
          let v34 = 1u64;
          let v40 = sub_2(Clone::clone(n), v34);
          let i = sub_2(v40, t);
          let v57 = add(mul(i, Clone::clone(w)), i);
          let piv = a::get::<f64>(&Q, v57);
          let v73 = add(mul(i, Clone::clone(w)), Clone::clone(n));
          let v76 = a::get::<f64>(&Q, v73);
          let xi = div_1(v76, piv);
          let M = a::set::<f64>(v26, add(mul(i, Clone::clone(w)), Clone::clone(n)), xi);
          let Q_1 = scale_row(v28, Clone::clone(n), i, piv);
          let v111 = {
            move |_v112: u64, v113: (Rc<Array<f64>>, Rc<Array<f64>>)| -> bool {
              std::mem::drop(v113);
              true
            }
          };
          let v118: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> bool> = Rc::new(v111);
          let v119: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> bool> = v118;
          let v121 = Clone::clone(w);
          let v125 = Clone::clone(n);
          let v128 = {
            let __anf_capture_131 = xi;
            let __anf_capture_135 = i;
            move |i_: u64, mq: (Rc<Array<f64>>, Rc<Array<f64>>)| -> (Rc<Array<f64>>, Rc<Array<f64>>) {
              let w = &v121;
              let xi = &__anf_capture_131;
              let n = &v125;
              let i = &__anf_capture_135;
              match mq {
                (v140, v142) => {
                  let Q = &v140;
                  let v157 = add(mul(i_, Clone::clone(w)), Clone::clone(i));
                  let f = a::get::<f64>(&Q, v157);
                  let v171 = add(mul(i_, Clone::clone(w)), Clone::clone(n));
                  let v185 = add(mul(i_, Clone::clone(w)), Clone::clone(n));
                  let v187 = a::get::<f64>(&Q, v185);
                  let v205 = a::set::<f64>(v140, v171, sub_1(v187, mul_1(f, Clone::clone(xi))));
                  let v212 = Clone::clone(n);
                  let v216 = Clone::clone(i);
                  let v221 = axpy_row(v142, v212, i_, v216, 0u64, f);
                  (v205, v221)
                },
              }
            }
          };
          let v233: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>)> = Rc::new(v128);
          loop_::<(Rc<Array<f64>>, Rc<Array<f64>>)>(i, v119, v233, 0u64, (M, Q_1))
        },
      }
    }
  };
  let v259: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>)> = Rc::new(v18);
  loop_::<(Rc<Array<f64>>, Rc<Array<f64>>)>(n, v13, v259, 0u64, (M, Q))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.get_col
// Variant: uncurried
pub fn get_col(M: Rc<Array<f64>>, n: u64, w: u64, c: u64) -> Rc<Array<f64>> {
  let v5 = {
    move |_v6: u64, v7: Rc<Array<f64>>| -> bool {
      std::mem::drop(v7);
      true
    }
  };
  let v12: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(v5);
  let v13: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = v12;
  let v20 = {
    move |i: u64, x: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let w = &w;
      let c = &c;
      let M = &M;
      let v41 = add(mul(i, Clone::clone(w)), Clone::clone(c));
      let v43 = a::get::<f64>(&M, v41);
      a::set::<f64>(x, i, v43)
    }
  };
  let v53: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new(v20);
  let v62 = a::make::<f64>(n, __rocq_global_371);
  loop_::<Rc<Array<f64>>>(n, v13, v53, 0u64, v62)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.i2z
pub fn i2z(x: u64) -> Rc<BigInt> {
  let v5 = to_Z(x);
  v5
}

// Rocq: Corelib.BinNums.IntDef.Z.mul
// Variant: uncurried
pub fn mul_2(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = b::mul(v0, v1);
  v8
}

// Rocq: Corelib.BinNums.IntDef.Z.leb
// Variant: uncurried
pub fn leb_owned(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  b::le(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.leb
// Variant: borrowed, uncurried
pub fn leb(v0: &Rc<BigInt>, v1: &Rc<BigInt>) -> bool {
  let v5 = Rc::clone(v0);
  let v8 = Rc::clone(v1);
  b::le(v5, v8)
}

// Rocq: Corelib.BinNums.IntDef.Z.shiftl
// Variant: uncurried
pub fn shiftl(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = b::shiftl(v0, v1);
  v8
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dadd
// Variant: uncurried
pub fn dadd(x: (Rc<BigInt>, Rc<BigInt>), y: (Rc<BigInt>, Rc<BigInt>)) -> (Rc<BigInt>, Rc<BigInt>) {
  match x {
    (v3, v5) => {
      let m1 = &v5;
      match y {
        (v9, v11) => {
          let m2 = &v11;
          let v15 = m1;
          let v16 = m2;
          match leb(v15, v16) {
            true => {
              let v25 = Rc::clone(m1);
              let v26 = sub(v11, v25);
              let v31 = shiftl(v9, v26);
              let v37 = add_1(v3, v31);
              (v37, v5)
            },
            false => {
              let v51 = Rc::clone(m2);
              let v52 = sub(v5, v51);
              let v58 = shiftl(v3, v52);
              let v63 = add_1(v58, v9);
              (v63, v11)
            },
          }
        },
      }
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.d0
pub fn d0(_v0: ()) -> (Rc<BigInt>, Rc<BigInt>) {
  let v1 = b::zero();
  let v2 = b::zero();
  (v1, v2)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dsumf
// Variant: uncurried
pub fn dsumf(len: u64, f: Rc<dyn Fn(u64) -> (Rc<BigInt>, Rc<BigInt>)>) -> (Rc<BigInt>, Rc<BigInt>) {
  let v3 = {
    move |_v4: u64, v5: (Rc<BigInt>, Rc<BigInt>)| -> bool {
      std::mem::drop(v5);
      true
    }
  };
  let v10: Rc<dyn Fn(u64, (Rc<BigInt>, Rc<BigInt>)) -> bool> = Rc::new(v3);
  let v11: Rc<dyn Fn(u64, (Rc<BigInt>, Rc<BigInt>)) -> bool> = v10;
  let v14 = {
    move |k: u64, acc: (Rc<BigInt>, Rc<BigInt>)| -> (Rc<BigInt>, Rc<BigInt>) {
      let f = &f;
      let v22 = f(k);
      dadd(acc, v22)
    }
  };
  let v30: Rc<dyn Fn(u64, (Rc<BigInt>, Rc<BigInt>)) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new(v14);
  loop_::<(Rc<BigInt>, Rc<BigInt>)>(len, v11, v30, 0u64, d0(()))
}

// Rocq: Stdlib.ZArith.BinIntDef.Z.abs
pub fn abs_owned(v0: Rc<BigInt>) -> Rc<BigInt> {
  let v5 = b::abs(v0);
  v5
}

// Rocq: Stdlib.ZArith.BinIntDef.Z.abs
// Variant: borrowed
pub fn abs(v0: &Rc<BigInt>) -> Rc<BigInt> {
  let v4 = Rc::clone(v0);
  let v6 = b::abs(v4);
  v6
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dabs
pub fn dabs(x: (Rc<BigInt>, Rc<BigInt>)) -> (Rc<BigInt>, Rc<BigInt>) {
  let v4 = Clone::clone(&x);
  let v7 = fst::<Rc<BigInt>, Rc<BigInt>>(v4);
  let v9 = abs_owned(v7);
  let v13 = snd::<Rc<BigInt>, Rc<BigInt>>(x);
  (v9, v13)
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b_1: bool) -> bool {
  match b_1 {
    true => {
      false
    },
    false => {
      true
    },
  }
}

// Rocq: Corelib.Floats.PrimFloat.eqb
// Variant: uncurried
pub fn eqb_1(v0: f64, v1: f64) -> bool {
  rocq_float64::eqb(v0, v1)
}

// Rocq: Corelib.Floats.PrimFloat.is_nan
pub fn is_nan(f: f64) -> bool {
  negb(eqb_1(f, f))
}

// Rocq: Corelib.Floats.PrimFloat.is_zero
pub fn is_zero(f: f64) -> bool {
  eqb_1(f, __rocq_global_371)
}

// Rocq: Corelib.Floats.PrimFloat.is_infinity
pub fn is_infinity(f: f64) -> bool {
  eqb_1(abs_1(f), __rocq_global_1215)
}

// Rocq: Corelib.Floats.PrimFloat.frshiftexp$rust_exponent$uncurry$0
pub fn frshiftexp_rust_exponent_uncurry_0(v0: f64) -> u64 {
  rocq_float64::frshiftexp_exponent(v0)
}

// Rocq: Corelib.Floats.PrimFloat.frshiftexp$rust_fraction$uncurry$0
pub fn frshiftexp_rust_fraction_uncurry_0(v0: f64) -> f64 {
  rocq_float64::frshiftexp_fraction(v0)
}

// Rocq: Corelib.Floats.PrimFloat.frshiftexp
pub fn frshiftexp(x: f64) -> (f64, u64) {
  (frshiftexp_rust_fraction_uncurry_0(x), frshiftexp_rust_exponent_uncurry_0(x))
}

// Rocq: Corelib.Floats.PrimFloat.normfr_mantissa
pub fn normfr_mantissa(v0: f64) -> u64 {
  rocq_float64::normfr_mantissa(v0)
}

// Rocq: Corelib.Floats.PrimFloat.get_sign
pub fn get_sign(f: f64) -> bool {
  let f_1 = match is_zero(f) {
    true => {
      div_1(__rocq_global_820, f)
    },
    false => {
      f
    },
  };
  ltb_1(f_1, __rocq_global_371)
}

// Rocq: Corelib.Floats.FloatOps.shift
pub fn shift(_v0: ()) -> Rc<BigInt> {
  let v2 = b::one();
  let v5 = b::twice(v2);
  let v8 = b::twice(v5);
  let v11 = b::twice(v8);
  let v14 = b::twice(v11);
  let v17 = b::twice(v14);
  let v20 = b::twice_plus_one(v17);
  let v23 = b::twice_plus_one(v20);
  let v26 = b::twice(v23);
  let v29 = b::twice_plus_one(v26);
  let v32 = b::twice(v29);
  let v35 = b::twice_plus_one(v32);
  let v38 = b::identity(v35);
  v38
}

// Rocq: Corelib.Floats.FloatOps.prec
pub fn prec(_v0: ()) -> Rc<BigInt> {
  let v2 = b::one();
  let v5 = b::twice_plus_one(v2);
  let v8 = b::twice(v5);
  let v11 = b::twice_plus_one(v8);
  let v14 = b::twice(v11);
  let v17 = b::twice_plus_one(v14);
  let v20 = b::identity(v17);
  v20
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dec
pub fn dec(f: f64) -> (Rc<BigInt>, Rc<BigInt>) {
  match is_nan(f) {
    true => {
      let v6 = b::zero();
      let v7 = b::zero();
      (v6, v7)
    },
    false => {
      match is_zero(f) {
        true => {
          let v21 = b::zero();
          let v22 = b::zero();
          (v21, v22)
        },
        false => {
          let v34 = is_infinity(f);
          match &v34 {
            true => {
              let v37 = b::zero();
              let v38 = b::zero();
              (v37, v38)
            },
            false => {
              let v50 = frshiftexp(f);
              match v50 {
                (v52, v54) => {
                  let r = &v54;
                  let m = to_Z(normfr_mantissa(v52));
                  let v69 = match get_sign(f) {
                    true => {
                      let v74 = opp(m);
                      v74
                    },
                    false => {
                      m
                    },
                  };
                  let v83 = Clone::clone(r);
                  let v84 = to_Z(v83);
                  let v90 = shift(());
                  let v95 = sub(v84, v90);
                  let v101 = prec(());
                  let v106 = sub(v95, v101);
                  (v69, v106)
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.rowabs
// Variant: uncurried
pub fn rowabs(xa: Rc<Array<Rc<Array<f64>>>>, n: u64) -> Rc<Array<(Rc<BigInt>, Rc<BigInt>)>> {
  let v3 = {
    move |_v4: u64, v5: Rc<Array<(Rc<BigInt>, Rc<BigInt>)>>| -> bool {
      std::mem::drop(v5);
      true
    }
  };
  let v10: Rc<dyn Fn(u64, Rc<Array<(Rc<BigInt>, Rc<BigInt>)>>) -> bool> = Rc::new(v3);
  let v11: Rc<dyn Fn(u64, Rc<Array<(Rc<BigInt>, Rc<BigInt>)>>) -> bool> = v10;
  let v16 = {
    let __anf_capture_19 = n;
    move |k: u64, S: Rc<Array<(Rc<BigInt>, Rc<BigInt>)>>| -> Rc<Array<(Rc<BigInt>, Rc<BigInt>)>> {
      let xa = &xa;
      let n = &__anf_capture_19;
      let v24 = Rc::clone(xa);
      let row = a::get::<Rc<Array<f64>>>(&v24, k);
      std::mem::drop(v24);
      let v32 = {
        move |j: u64| -> (Rc<BigInt>, Rc<BigInt>) {
          let row = &row;
          let v41 = a::get::<f64>(&row, j);
          dabs(dec(v41))
        }
      };
      let v49: Rc<dyn Fn(u64) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new(v32);
      let v52 = Clone::clone(n);
      a::set::<(Rc<BigInt>, Rc<BigInt>)>(S, k, dsumf(v52, v49))
    }
  };
  let v65: Rc<dyn Fn(u64, Rc<Array<(Rc<BigInt>, Rc<BigInt>)>>) -> Rc<Array<(Rc<BigInt>, Rc<BigInt>)>>> = Rc::new(v16);
  let v79 = a::make::<(Rc<BigInt>, Rc<BigInt>)>(n, d0(()));
  loop_::<Rc<Array<(Rc<BigInt>, Rc<BigInt>)>>>(n, v11, v65, 0u64, v79)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dneg
pub fn dneg(x: (Rc<BigInt>, Rc<BigInt>)) -> (Rc<BigInt>, Rc<BigInt>) {
  let v4 = Clone::clone(&x);
  let v7 = fst::<Rc<BigInt>, Rc<BigInt>>(v4);
  let v9 = opp(v7);
  let v13 = snd::<Rc<BigInt>, Rc<BigInt>>(x);
  (v9, v13)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dleb
// Variant: uncurried
pub fn dleb(x: (Rc<BigInt>, Rc<BigInt>), y: (Rc<BigInt>, Rc<BigInt>)) -> bool {
  let v3 = b::zero();
  let v17 = fst::<Rc<BigInt>, Rc<BigInt>>(dadd(y, dneg(x)));
  leb_owned(v3, v17)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dmax
// Variant: uncurried
pub fn dmax(x: (Rc<BigInt>, Rc<BigInt>), y: (Rc<BigInt>, Rc<BigInt>)) -> (Rc<BigInt>, Rc<BigInt>) {
  let v4 = Clone::clone(&x);
  let v5 = v4;
  let v7 = Clone::clone(&y);
  match dleb(v5, v7) {
    true => {
      std::mem::drop(x);
      y
    },
    false => {
      std::mem::drop(y);
      x
    },
  }
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

// Rocq: EquationsolverExact.equationsolver_exact_implem.maxb
// Variant: uncurried
pub fn maxb(len: u64, h: Rc<dyn Fn(u64) -> ((Rc<BigInt>, Rc<BigInt>), bool)>) -> ((Rc<BigInt>, Rc<BigInt>), bool) {
  let v3 = {
    move |_v4: u64, v5: ((Rc<BigInt>, Rc<BigInt>), bool)| -> bool {
      std::mem::drop(v5);
      true
    }
  };
  let v10: Rc<dyn Fn(u64, ((Rc<BigInt>, Rc<BigInt>), bool)) -> bool> = Rc::new(v3);
  let v11: Rc<dyn Fn(u64, ((Rc<BigInt>, Rc<BigInt>), bool)) -> bool> = v10;
  let v14 = {
    move |i: u64, st: ((Rc<BigInt>, Rc<BigInt>), bool)| -> ((Rc<BigInt>, Rc<BigInt>), bool) {
      let h = &h;
      let r = h(i);
      let v25 = Clone::clone(&st);
      let v27 = fst::<(Rc<BigInt>, Rc<BigInt>), bool>(v25);
      let v30 = Clone::clone(&r);
      (dmax(v27, fst::<(Rc<BigInt>, Rc<BigInt>), bool>(v30)), andb(snd::<(Rc<BigInt>, Rc<BigInt>), bool>(st), snd::<(Rc<BigInt>, Rc<BigInt>), bool>(r)))
    }
  };
  let v60: Rc<dyn Fn(u64, ((Rc<BigInt>, Rc<BigInt>), bool)) -> ((Rc<BigInt>, Rc<BigInt>), bool)> = Rc::new(v14);
  loop_::<((Rc<BigInt>, Rc<BigInt>), bool)>(len, v11, v60, 0u64, (d0(()), true))
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

// Rocq: Corelib.Floats.PrimFloat.is_finite
pub fn is_finite(x: f64) -> bool {
  negb(orb(is_nan(x), is_infinity(x)))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dsumb
// Variant: uncurried
pub fn dsumb(len: u64, g: Rc<dyn Fn(u64) -> f64>, f: Rc<dyn Fn(u64, f64) -> (Rc<BigInt>, Rc<BigInt>)>) -> ((Rc<BigInt>, Rc<BigInt>), bool) {
  let v4 = {
    move |_v5: u64, v6: ((Rc<BigInt>, Rc<BigInt>), bool)| -> bool {
      std::mem::drop(v6);
      true
    }
  };
  let v11: Rc<dyn Fn(u64, ((Rc<BigInt>, Rc<BigInt>), bool)) -> bool> = Rc::new(v4);
  let v12: Rc<dyn Fn(u64, ((Rc<BigInt>, Rc<BigInt>), bool)) -> bool> = v11;
  let v17 = {
    move |k: u64, st: ((Rc<BigInt>, Rc<BigInt>), bool)| -> ((Rc<BigInt>, Rc<BigInt>), bool) {
      let g = &g;
      let f = &f;
      let d = g(k);
      let v30 = Clone::clone(&st);
      let v32 = fst::<(Rc<BigInt>, Rc<BigInt>), bool>(v30);
      let v37 = f(k, d);
      (dadd(v32, v37), andb(snd::<(Rc<BigInt>, Rc<BigInt>), bool>(st), is_finite(d)))
    }
  };
  let v65: Rc<dyn Fn(u64, ((Rc<BigInt>, Rc<BigInt>), bool)) -> ((Rc<BigInt>, Rc<BigInt>), bool)> = Rc::new(v17);
  loop_::<((Rc<BigInt>, Rc<BigInt>), bool)>(len, v12, v65, 0u64, (d0(()), true))
}

// Rocq: Corelib.Floats.PrimFloat.add
// Variant: uncurried
pub fn add_2(v0: f64, v1: f64) -> f64 {
  rocq_float64::add(v0, v1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fdot
// Variant: uncurried
pub fn fdot_owned(X: Rc<Array<f64>>, ox: u64, Y: Rc<Array<f64>>, oy: u64, len: u64) -> f64 {
  let v6 = {
    move |_v7: u64, _v8: f64| -> bool {
      true
    }
  };
  let v13: Rc<dyn Fn(u64, f64) -> bool> = Rc::new(v6);
  let v14: Rc<dyn Fn(u64, f64) -> bool> = v13;
  let v23 = {
    move |k: u64, s: f64| -> f64 {
      let ox = &ox;
      let X = &X;
      let oy = &oy;
      let Y = &Y;
      let v42 = add(Clone::clone(ox), k);
      let v44 = a::get::<f64>(&X, v42);
      let v51 = add(Clone::clone(oy), k);
      let v53 = a::get::<f64>(&Y, v51);
      add_2(s, mul_1(v44, v53))
    }
  };
  let v66: Rc<dyn Fn(u64, f64) -> f64> = Rc::new(v23);
  loop_::<f64>(len, v14, v66, 0u64, __rocq_global_371)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fdot
// Variant: borrowed, uncurried
pub fn fdot(X: &Rc<Array<f64>>, ox: u64, Y: &Rc<Array<f64>>, oy: u64, len: u64) -> f64 {
  let len_1 = len;
  let v9 = {
    move |_v10: u64, _v11: f64| -> bool {
      true
    }
  };
  let v16: Rc<dyn Fn(u64, f64) -> bool> = Rc::new(v9);
  let v17: Rc<dyn Fn(u64, f64) -> bool> = v16;
  let v22 = Rc::clone(X);
  let v27 = Rc::clone(Y);
  let v28 = {
    move |k: u64, s: f64| -> f64 {
      let ox = &ox;
      let X = &v22;
      let oy = &oy;
      let Y = &v27;
      let v47 = add(Clone::clone(ox), k);
      let v49 = a::get::<f64>(&X, v47);
      let v56 = add(Clone::clone(oy), k);
      let v58 = a::get::<f64>(&Y, v56);
      add_2(s, mul_1(v49, v58))
    }
  };
  let v71: Rc<dyn Fn(u64, f64) -> f64> = Rc::new(v28);
  loop_::<f64>(len_1, v17, v71, 0u64, __rocq_global_371)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dsub
// Variant: uncurried
pub fn dsub(x: (Rc<BigInt>, Rc<BigInt>), y: (Rc<BigInt>, Rc<BigInt>)) -> (Rc<BigInt>, Rc<BigInt>) {
  dadd(x, dneg(y))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dint
pub fn dint_owned(z: Rc<BigInt>) -> (Rc<BigInt>, Rc<BigInt>) {
  let v1 = b::zero();
  (z, v1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dint
// Variant: borrowed
pub fn dint(z: &Rc<BigInt>) -> (Rc<BigInt>, Rc<BigInt>) {
  let v1 = b::zero();
  let v4 = Rc::clone(z);
  (v4, v1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dmul
// Variant: uncurried
pub fn dmul(x: (Rc<BigInt>, Rc<BigInt>), y: (Rc<BigInt>, Rc<BigInt>)) -> (Rc<BigInt>, Rc<BigInt>) {
  let v5 = Clone::clone(&x);
  let v7 = fst::<Rc<BigInt>, Rc<BigInt>>(v5);
  let v10 = Clone::clone(&y);
  let v12 = fst::<Rc<BigInt>, Rc<BigInt>>(v10);
  let v17 = mul_2(v7, v12);
  let v22 = snd::<Rc<BigInt>, Rc<BigInt>>(x);
  let v26 = snd::<Rc<BigInt>, Rc<BigInt>>(y);
  let v31 = add_1(v22, v26);
  (v17, v31)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.erow
// Variant: borrowed, uncurried
pub fn erow(n: u64, Q: &Rc<Array<f64>>, AT: &Rc<Array<f64>>, S: &Rc<Array<(Rc<BigInt>, Rc<BigInt>)>>, lamd: (Rc<BigInt>, Rc<BigInt>), mud2: (Rc<BigInt>, Rc<BigInt>), i: u64) -> ((Rc<BigInt>, Rc<BigInt>), bool) {
  let lamd_1 = lamd;
  let mud2_1 = mud2;
  let v16 = Rc::clone(Q);
  let v19 = Rc::clone(AT);
  let v22 = {
    let __anf_capture_23 = i;
    let __anf_capture_29 = n;
    move |j: u64| -> f64 {
      let i = &__anf_capture_23;
      let Q = &v16;
      let AT = &v19;
      let v37 = mul(Clone::clone(i), Clone::clone(&__anf_capture_29));
      let v43 = mul(j, Clone::clone(&__anf_capture_29));
      let v49 = Clone::clone(&__anf_capture_29);
      fdot(Q, v37, AT, v43, v49)
    }
  };
  let v56: Rc<dyn Fn(u64) -> f64> = Rc::new(v22);
  let v57: Rc<dyn Fn(u64) -> f64> = v56;
  let v60 = {
    let __anf_capture_61 = i;
    move |j: u64, d: f64| -> (Rc<BigInt>, Rc<BigInt>) {
      let i = &__anf_capture_61;
      let v70 = Clone::clone(i);
      let v85 = match eqb(v70, j) {
        true => {
          let v76 = b::one();
          let v79 = b::identity(v76);
          v79
        },
        false => {
          let v82 = b::zero();
          v82
        },
      };
      dabs(dsub(dint_owned(v85), dec(d)))
    }
  };
  let v102: Rc<dyn Fn(u64, f64) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new(v60);
  let e = dsumb(n, v57, v102);
  let v118 = Rc::clone(Q);
  let v121 = Rc::clone(S);
  let v122 = {
    let __anf_capture_123 = i;
    let __anf_capture_125 = n;
    move |k: u64| -> (Rc<BigInt>, Rc<BigInt>) {
      let i = &__anf_capture_123;
      let n = &__anf_capture_125;
      let Q = &v118;
      let S = &v121;
      let v147 = add(mul(Clone::clone(i), Clone::clone(n)), k);
      let v155 = dabs(dec(a::get::<f64>(&Q, v147)));
      let v158 = a::get::<(Rc<BigInt>, Rc<BigInt>)>(&S, k);
      dmul(v155, v158)
    }
  };
  let v166: Rc<dyn Fn(u64) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new(v122);
  let rr = dsumf(n, v166);
  let v177 = Clone::clone(&e);
  let v190 = dadd(fst::<(Rc<BigInt>, Rc<BigInt>), bool>(v177), dmul(lamd_1, rr));
  (dadd(v190, mud2_1), snd::<(Rc<BigInt>, Rc<BigInt>), bool>(e))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.rowR
// Variant: borrowed, uncurried
pub fn rowR(n: u64, Q: &Rc<Array<f64>>, i: u64) -> ((Rc<BigInt>, Rc<BigInt>), bool) {
  let v12 = Rc::clone(Q);
  let v13 = {
    let __anf_capture_16 = n;
    move |k: u64| -> (Rc<BigInt>, Rc<BigInt>) {
      let i = &i;
      let n = &__anf_capture_16;
      let Q = &v12;
      let v35 = add(mul(Clone::clone(i), Clone::clone(n)), k);
      let v38 = a::get::<f64>(&Q, v35);
      dabs(dec(v38))
    }
  };
  let v46: Rc<dyn Fn(u64) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new(v13);
  (dsumf(n, v46), true)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.resid
// Variant: borrowed, uncurried
pub fn resid(n: u64, xa: &Rc<Array<Rc<Array<f64>>>>, xb: &Rc<Array<f64>>, xt: &Rc<Array<f64>>, lamd: (Rc<BigInt>, Rc<BigInt>), mud1: (Rc<BigInt>, Rc<BigInt>), i: u64) -> ((Rc<BigInt>, Rc<BigInt>), bool) {
  let n_1 = n;
  let lamd_1 = lamd;
  let mud1_1 = mud1;
  let i_1 = i;
  let v13 = Rc::clone(xa);
  let row = a::get::<Rc<Array<f64>>>(&v13, i_1);
  std::mem::drop(v13);
  let v25 = Rc::clone(&row);
  let v30 = Rc::clone(xt);
  let d = fdot_owned(v25, 0u64, v30, 0u64, n_1);
  let v41 = xb;
  let v59 = dabs(dsub(dec(a::get::<f64>(&v41, i_1)), dec(d)));
  let v66 = Rc::clone(xt);
  let v67 = {
    let __anf_capture_68 = row;
    move |j: u64| -> (Rc<BigInt>, Rc<BigInt>) {
      let row = &__anf_capture_68;
      let xt = &v66;
      let v81 = dec(a::get::<f64>(&row, j));
      let v86 = a::get::<f64>(&xt, j);
      dabs(dmul(v81, dec(v86)))
    }
  };
  let v99: Rc<dyn Fn(u64) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new(v67);
  let v115 = dadd(v59, dmul(lamd_1, dsumf(n_1, v99)));
  (dadd(v115, mud1_1), is_finite(d))
}

// Rocq: Corelib.BinNums.IntDef.Z.ltb
// Variant: uncurried
pub fn ltb_2(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  b::lt(v0, v1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dltb
// Variant: uncurried
pub fn dltb(x: (Rc<BigInt>, Rc<BigInt>), y: (Rc<BigInt>, Rc<BigInt>)) -> bool {
  let v3 = b::zero();
  let v17 = fst::<Rc<BigInt>, Rc<BigInt>>(dadd(y, dneg(x)));
  ltb_2(v3, v17)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.d1
pub fn d1(_v0: ()) -> (Rc<BigInt>, Rc<BigInt>) {
  let v2 = b::one();
  let v4 = b::identity(v2);
  let v5 = b::zero();
  (v4, v5)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.certify
// Variant: uncurried
pub fn certify(n: u64, xa: Rc<Array<Rc<Array<f64>>>>, xb: Rc<Array<f64>>, AT: Rc<Array<f64>>, Q: Rc<Array<f64>>, xt: Rc<Array<f64>>) -> bool {
  let nz = i2z(n);
  let v12 = b::one();
  let v15 = b::twice_plus_one(v12);
  let v18 = b::identity(v15);
  let v22 = Rc::clone(&nz);
  let v23 = mul_2(v18, v22);
  let v25 = b::one();
  let v28 = b::twice_plus_one(v25);
  let v31 = b::twice(v28);
  let v34 = b::twice_plus_one(v31);
  let v37 = b::twice(v34);
  let v40 = b::twice_plus_one(v37);
  let v42 = b::neg(v40);
  let lamd = (v23, v42);
  let v51 = b::one();
  let v54 = b::twice_plus_one(v51);
  let v57 = b::identity(v54);
  let v61 = Rc::clone(&nz);
  let v62 = mul_2(v57, v61);
  let v64 = b::one();
  let v67 = b::twice(v64);
  let v70 = b::twice(v67);
  let v73 = b::twice(v70);
  let v76 = b::twice(v73);
  let v79 = b::twice_plus_one(v76);
  let v82 = b::twice_plus_one(v79);
  let v85 = b::twice(v82);
  let v88 = b::twice(v85);
  let v91 = b::twice_plus_one(v88);
  let v94 = b::twice_plus_one(v91);
  let v96 = b::neg(v94);
  let mud1 = (v62, v96);
  let v106 = b::one();
  let v109 = b::twice_plus_one(v106);
  let v112 = b::identity(v109);
  let v116 = Rc::clone(&nz);
  let v118 = mul_2(v112, v116);
  let v122 = mul_2(v118, nz);
  let v124 = b::one();
  let v127 = b::twice(v124);
  let v130 = b::twice(v127);
  let v133 = b::twice(v130);
  let v136 = b::twice(v133);
  let v139 = b::twice_plus_one(v136);
  let v142 = b::twice_plus_one(v139);
  let v145 = b::twice(v142);
  let v148 = b::twice(v145);
  let v151 = b::twice_plus_one(v148);
  let v154 = b::twice_plus_one(v151);
  let v156 = b::neg(v154);
  let mud2 = (v122, v156);
  let v166 = Rc::clone(&xa);
  let S = rowabs(v166, n);
  let v175 = Rc::clone(&Q);
  let v178 = Rc::clone(&AT);
  let v181 = Rc::clone(&S);
  let v183 = Clone::clone(&lamd);
  let v184 = v183;
  let v186 = Clone::clone(&mud2);
  let v188 = {
    let __anf_capture_189 = n;
    move |v201: u64| -> ((Rc<BigInt>, Rc<BigInt>), bool) {
      let n = &__anf_capture_189;
      let Q = &v175;
      let AT = &v178;
      let S = &v181;
      let v214 = erow(Clone::clone(n), Q, AT, S, Clone::clone(&v184), Clone::clone(&v186), v201);
      v214
    }
  };
  let v217: Rc<dyn Fn(u64) -> ((Rc<BigInt>, Rc<BigInt>), bool)> = Rc::new(v188);
  let v223 = maxb(n, v217);
  match v223 {
    (v225, v227) => {
      let ok1 = &v225;
      let v235 = Rc::clone(&Q);
      let v236 = {
        let __anf_capture_237 = n;
        move |v241: u64| -> ((Rc<BigInt>, Rc<BigInt>), bool) {
          let n = &__anf_capture_237;
          let Q = &v235;
          let v248 = rowR(Clone::clone(n), Q, v241);
          v248
        }
      };
      let v251: Rc<dyn Fn(u64) -> ((Rc<BigInt>, Rc<BigInt>), bool)> = Rc::new(v236);
      let v257 = maxb(n, v251);
      match v257 {
        (v259, _v261) => {
          std::mem::drop(S);
          std::mem::drop(mud2);
          std::mem::drop(AT);
          std::mem::drop(Q);
          let v272 = Rc::clone(&xt);
          let v277 = {
            let __anf_capture_278 = n;
            let __anf_capture_280 = xa;
            let __anf_capture_286 = lamd;
            move |v290: u64| -> ((Rc<BigInt>, Rc<BigInt>), bool) {
              let n = &__anf_capture_278;
              let xa = &__anf_capture_280;
              let xb = &xb;
              let xt = &v272;
              let v303 = resid(Clone::clone(n), xa, xb, xt, Clone::clone(&__anf_capture_286), Clone::clone(&mud1), v290);
              v303
            }
          };
          let v306: Rc<dyn Fn(u64) -> ((Rc<BigInt>, Rc<BigInt>), bool)> = Rc::new(v277);
          let v312 = maxb(n, v306);
          match v312 {
            (v314, v316) => {
              let v325 = andb(v227, v316);
              let v327 = &xt;
              let v328 = a::length::<f64>(&v327);
              std::mem::drop(xt);
              let v338 = andb(v325, eqb(v328, n));
              let v346 = d1(());
              let v347 = Clone::clone(ok1);
              let v351 = dltb(v347, v346);
              let v356 = b::one();
              let v359 = b::twice_plus_one(v356);
              let v362 = b::twice_plus_one(v359);
              let v365 = b::twice_plus_one(v362);
              let v368 = b::twice_plus_one(v365);
              let v371 = b::twice(v368);
              let v374 = b::twice_plus_one(v371);
              let v377 = b::twice(v374);
              let v380 = b::twice(v377);
              let v383 = b::twice(v380);
              let v385 = b::identity(v383);
              let v386 = b::zero();
              let v391 = (v385, v386);
              let v398 = dmul(v259, v314);
              let v424 = andb(v351, dleb(dadd(dmul(v391, v398), v225), d1(())));
              andb(v338, v424)
            },
          }
        },
      }
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.min
// Variant: uncurried
pub fn min(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = b::min(v0, v1);
  v8
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.row_exp
// Variant: uncurried
pub fn row_exp(n: u64, row: Rc<Array<f64>>, bi: f64) -> Rc<BigInt> {
  let v4 = {
    move |_v5: u64, v6: Rc<BigInt>| -> bool {
      std::mem::drop(v6);
      true
    }
  };
  let v11: Rc<dyn Fn(u64, Rc<BigInt>) -> bool> = Rc::new(v4);
  let v12: Rc<dyn Fn(u64, Rc<BigInt>) -> bool> = v11;
  let v15 = {
    move |j: u64, E: Rc<BigInt>| -> Rc<BigInt> {
      let row = &row;
      let v26 = a::get::<f64>(&row, j);
      let v31 = snd::<Rc<BigInt>, Rc<BigInt>>(dec(v26));
      let v37 = min(E, v31);
      v37
    }
  };
  let v39: Rc<dyn Fn(u64, Rc<BigInt>) -> Rc<BigInt>> = Rc::new(v15);
  let v44 = b::zero();
  let v52 = snd::<Rc<BigInt>, Rc<BigInt>>(dec(bi));
  let v57 = min(v44, v52);
  let v69 = loop_::<Rc<BigInt>>(n, v12, v39, 0u64, v57);
  v69
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.scale
// Variant: uncurried
pub fn scale_owned(f: f64, E: Rc<BigInt>) -> Rc<BigInt> {
  let v10 = fst::<Rc<BigInt>, Rc<BigInt>>(dec(f));
  let v20 = snd::<Rc<BigInt>, Rc<BigInt>>(dec(f));
  let v24 = sub(v20, E);
  let v30 = shiftl(v10, v24);
  v30
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.scale
// Variant: borrowed, uncurried
pub fn scale(f: f64, E: &Rc<BigInt>) -> Rc<BigInt> {
  let f_1 = f;
  let v11 = fst::<Rc<BigInt>, Rc<BigInt>>(dec(f_1));
  let v21 = snd::<Rc<BigInt>, Rc<BigInt>>(dec(f_1));
  let v25 = Rc::clone(E);
  let v26 = sub(v21, v25);
  let v32 = shiftl(v11, v26);
  v32
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fill_row
// Variant: uncurried
pub fn fill_row(n: u64, w: u64, i: u64, row: Rc<Array<f64>>, E: Rc<BigInt>, T: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let v7 = {
    move |_v8: u64, v9: Rc<Array<Rc<BigInt>>>| -> bool {
      std::mem::drop(v9);
      true
    }
  };
  let v14: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = Rc::new(v7);
  let v15: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = v14;
  let v24 = {
    move |j: u64, T: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let i = &i;
      let w = &w;
      let row = &row;
      let E = &E;
      let v46 = add(mul(Clone::clone(i), Clone::clone(w)), j);
      let v54 = scale(a::get::<f64>(&row, j), E);
      a::set::<Rc<BigInt>>(T, v46, v54)
    }
  };
  let v64: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new(v24);
  loop_::<Rc<Array<Rc<BigInt>>>>(n, v15, v64, 0u64, T)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.build_step
// Variant: uncurried
pub fn build_step(a_1: Rc<Array<Rc<Array<f64>>>>, b_1: Rc<Array<f64>>, n: u64, w: u64, i: u64, T: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let row = a::get::<Rc<Array<f64>>>(&a_1, i);
  std::mem::drop(a_1);
  let v12 = &b_1;
  let bi = a::get::<f64>(&v12, i);
  std::mem::drop(b_1);
  let v21 = Rc::clone(&row);
  let E = row_exp(n, v21, bi);
  let v36 = Rc::clone(&E);
  let T_1 = fill_row(n, w, i, row, v36, T);
  let v51 = add(mul(i, w), n);
  let v57 = scale_owned(bi, E);
  a::set::<Rc<BigInt>>(T_1, v51, v57)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.build
// Variant: uncurried
pub fn build(a_1: Rc<Array<Rc<Array<f64>>>>, b_1: Rc<Array<f64>>, n: u64, w: u64) -> Rc<Array<Rc<BigInt>>> {
  let v5 = {
    move |_v6: u64, v7: Rc<Array<Rc<BigInt>>>| -> bool {
      std::mem::drop(v7);
      true
    }
  };
  let v12: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = Rc::new(v5);
  let v13: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = v12;
  let v22 = {
    let __anf_capture_27 = n;
    let __anf_capture_29 = w;
    move |v31: u64, v32: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let v35 = Rc::clone(&a_1);
      let v37 = Rc::clone(&b_1);
      let v39 = Clone::clone(&__anf_capture_27);
      let v41 = Clone::clone(&__anf_capture_29);
      build_step(v35, v37, v39, v41, v31, v32)
    }
  };
  let v49: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new(v22);
  let v58 = mul(n, w);
  let v59 = b::zero();
  let v64 = a::make::<Rc<BigInt>>(v58, v59);
  loop_::<Rc<Array<Rc<BigInt>>>>(n, v13, v49, 0u64, v64)
}

// Rocq: Corelib.BinNums.IntDef.Z.eqb
// Variant: uncurried
pub fn eqb_2(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  b::equal(v0, v1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.find_piv
// Variant: uncurried
pub fn find_piv(T: Rc<Array<Rc<BigInt>>>, n: u64, w: u64, c: u64, r: u64) -> u64 {
  let v6 = {
    move |_v7: u64, _v8: u64| -> bool {
      true
    }
  };
  let v13: Rc<dyn Fn(u64, u64) -> bool> = Rc::new(v6);
  let v14: Rc<dyn Fn(u64, u64) -> bool> = v13;
  let v23 = {
    let __anf_capture_24 = n;
    move |i: u64, s: u64| -> u64 {
      let n = &__anf_capture_24;
      let w = &w;
      let c = &c;
      let T = &T;
      let v38 = Clone::clone(n);
      match eqb(s, v38) {
        true => {
          let v54 = add(mul(i, Clone::clone(w)), Clone::clone(c));
          let v56 = a::get::<Rc<BigInt>>(&T, v54);
          let v57 = b::zero();
          match eqb_2(v56, v57) {
            true => {
              s
            },
            false => {
              i
            },
          }
        },
        false => {
          s
        },
      }
    }
  };
  let v76: Rc<dyn Fn(u64, u64) -> u64> = Rc::new(v23);
  loop_::<u64>(n, v14, v76, r, n)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.swap_rows
// Variant: uncurried
pub fn swap_rows(T: Rc<Array<Rc<BigInt>>>, w: u64, q: u64, r: u64) -> Rc<Array<Rc<BigInt>>> {
  let v5 = {
    move |_v6: u64, v7: Rc<Array<Rc<BigInt>>>| -> bool {
      std::mem::drop(v7);
      true
    }
  };
  let v12: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = Rc::new(v5);
  let v13: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = v12;
  let v20 = {
    let __anf_capture_25 = w;
    move |j: u64, T: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let r = &r;
      let q = &q;
      let v40 = add(mul(Clone::clone(r), Clone::clone(&__anf_capture_25)), j);
      let v41 = &T;
      let x = a::get::<Rc<BigInt>>(&v41, v40);
      let v56 = add(mul(Clone::clone(q), Clone::clone(&__anf_capture_25)), j);
      let v57 = &T;
      let y = a::get::<Rc<BigInt>>(&v57, v56);
      let v79 = a::set::<Rc<BigInt>>(T, add(mul(Clone::clone(r), Clone::clone(&__anf_capture_25)), j), y);
      let v83 = Clone::clone(q);
      let v85 = Clone::clone(&__anf_capture_25);
      a::set::<Rc<BigInt>>(v79, add(mul(v83, v85), j), x)
    }
  };
  let v101: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new(v20);
  loop_::<Rc<Array<Rc<BigInt>>>>(w, v13, v101, 0u64, T)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.upd_row
// Variant: uncurried
pub fn upd_row(T: Rc<Array<Rc<BigInt>>>, w: u64, i: u64, r: u64, a_1: Rc<BigInt>, b_1: Rc<BigInt>) -> Rc<Array<Rc<BigInt>>> {
  let v7 = {
    move |_v8: u64, v9: Rc<Array<Rc<BigInt>>>| -> bool {
      std::mem::drop(v9);
      true
    }
  };
  let v14: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = Rc::new(v7);
  let v15: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = v14;
  let v26 = {
    let __anf_capture_33 = w;
    move |j: u64, T: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let i = &i;
      let a_1 = &a_1;
      let r = &r;
      let w = &__anf_capture_33;
      let b_1 = &b_1;
      let v50 = add(mul(Clone::clone(i), Clone::clone(w)), j);
      let v64 = add(mul(Clone::clone(i), Clone::clone(w)), j);
      let v65 = &T;
      let v68 = a::get::<Rc<BigInt>>(&v65, v64);
      let v70 = Rc::clone(a_1);
      let v73 = mul_2(v70, v68);
      let v86 = add(mul(Clone::clone(r), Clone::clone(w)), j);
      let v87 = &T;
      let v90 = a::get::<Rc<BigInt>>(&v87, v86);
      let v92 = Rc::clone(b_1);
      let v95 = mul_2(v92, v90);
      let v100 = sub(v73, v95);
      a::set::<Rc<BigInt>>(T, v50, v100)
    }
  };
  let v110: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new(v26);
  loop_::<Rc<Array<Rc<BigInt>>>>(w, v15, v110, 0u64, T)
}

// Rocq: Corelib.BinNums.IntDef.Z.pos_div_eucl
// Variant: uncurried
pub fn pos_div_eucl_1(a_1: Rc<BigInt>, b_1: Rc<BigInt>) -> (Rc<BigInt>, Rc<BigInt>) {
  pos_div_eucl(a_1, b_1)
}

// Rocq: Corelib.BinNums.IntDef.Z.pos_div_eucl (local: pos_div_eucl)
// Variant: uncurried, lifted
pub fn pos_div_eucl(a_1: Rc<BigInt>, b_1: Rc<BigInt>) -> (Rc<BigInt>, Rc<BigInt>) {
  let v4 = Rc::clone(&a_1);
  match b::positive_tag(v4) {
    b::PositiveTag::Odd => {
      let a_ = b::positive_tail(a_1);
      let v15 = Rc::clone(&b_1);
      let v16 = pos_div_eucl(a_, v15);
      match v16 {
        (v18, v20) => {
          let v25 = b::one();
          let v28 = b::twice(v25);
          let v31 = b::identity(v28);
          let v35 = mul_2(v31, v20);
          let v37 = b::one();
          let v39 = b::identity(v37);
          let r_ = add_1(v35, v39);
          let v48 = Rc::clone(&r_);
          let v51 = Rc::clone(&b_1);
          match ltb_2(v48, v51) {
            true => {
              std::mem::drop(b_1);
              let v56 = b::one();
              let v59 = b::twice(v56);
              let v62 = b::identity(v59);
              let v67 = mul_2(v62, v18);
              (v67, r_)
            },
            false => {
              let v78 = b::one();
              let v81 = b::twice(v78);
              let v84 = b::identity(v81);
              let v88 = mul_2(v84, v18);
              let v90 = b::one();
              let v92 = b::identity(v90);
              let v97 = add_1(v88, v92);
              let v103 = sub(r_, b_1);
              (v97, v103)
            },
          }
        },
      }
    },
    b::PositiveTag::Even => {
      let a_ = b::positive_tail(a_1);
      let v126 = Rc::clone(&b_1);
      let v127 = pos_div_eucl(a_, v126);
      match v127 {
        (v129, v131) => {
          let v135 = b::one();
          let v138 = b::twice(v135);
          let v141 = b::identity(v138);
          let r_ = mul_2(v141, v131);
          let v149 = Rc::clone(&r_);
          let v152 = Rc::clone(&b_1);
          match ltb_2(v149, v152) {
            true => {
              std::mem::drop(b_1);
              let v157 = b::one();
              let v160 = b::twice(v157);
              let v163 = b::identity(v160);
              let v168 = mul_2(v163, v129);
              (v168, r_)
            },
            false => {
              let v179 = b::one();
              let v182 = b::twice(v179);
              let v185 = b::identity(v182);
              let v189 = mul_2(v185, v129);
              let v191 = b::one();
              let v193 = b::identity(v191);
              let v198 = add_1(v189, v193);
              let v204 = sub(r_, b_1);
              (v198, v204)
            },
          }
        },
      }
    },
    b::PositiveTag::One => {
      let v221 = b::one();
      let v224 = b::twice(v221);
      let v227 = b::identity(v224);
      match leb_owned(v227, b_1) {
        true => {
          std::mem::drop(a_1);
          let v233 = b::zero();
          let v235 = b::one();
          let v237 = b::identity(v235);
          (v233, v237)
        },
        false => {
          std::mem::drop(a_1);
          let v247 = b::one();
          let v249 = b::identity(v247);
          let v250 = b::zero();
          (v249, v250)
        },
      }
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.div_eucl
// Variant: uncurried
pub fn div_eucl(a_1: Rc<BigInt>, b_1: Rc<BigInt>) -> (Rc<BigInt>, Rc<BigInt>) {
  let v4 = Rc::clone(&a_1);
  match b::integer_tag(v4) {
    b::IntegerTag::Zero => {
      std::mem::drop(a_1);
      std::mem::drop(b_1);
      let v7 = b::zero();
      let v8 = b::zero();
      (v7, v8)
    },
    b::IntegerTag::Positive => {
      let v19 = Rc::clone(&a_1);
      let a_ = b::integer_magnitude(v19);
      let v23 = Rc::clone(&b_1);
      let v24 = b::integer_tag(v23);
      match &v24 {
        b::IntegerTag::Zero => {
          std::mem::drop(a_);
          std::mem::drop(b_1);
          let v28 = b::zero();
          (v28, a_1)
        },
        b::IntegerTag::Positive => {
          std::mem::drop(a_1);
          let v38 = Rc::clone(&b_1);
          let p = b::integer_magnitude(v38);
          std::mem::drop(p);
          pos_div_eucl_1(a_, b_1)
        },
        b::IntegerTag::Negative => {
          let v50 = Rc::clone(&b_1);
          let b_ = b::integer_magnitude(v50);
          let v55 = b::identity(b_);
          let v60 = pos_div_eucl_1(a_, v55);
          match v60 {
            (v62, v64) => {
              let q = &v64;
              let v68 = Rc::clone(q);
              match b::integer_tag(v68) {
                b::IntegerTag::Zero => {
                  std::mem::drop(b_1);
                  std::mem::drop(a_1);
                  std::mem::drop(v64);
                  let v74 = opp(v62);
                  let v75 = b::zero();
                  (v74, v75)
                },
                b::IntegerTag::Positive => {
                  std::mem::drop(a_1);
                  let v85 = Rc::clone(q);
                  let p = b::integer_magnitude(v85);
                  std::mem::drop(p);
                  let v90 = b::one();
                  let v92 = b::identity(v90);
                  let v98 = add_1(v62, v92);
                  let v100 = opp(v98);
                  let v106 = add_1(b_1, v64);
                  (v100, v106)
                },
                b::IntegerTag::Negative => {
                  std::mem::drop(a_1);
                  let v116 = Rc::clone(q);
                  let p = b::integer_magnitude(v116);
                  std::mem::drop(p);
                  let v121 = b::one();
                  let v123 = b::identity(v121);
                  let v129 = add_1(v62, v123);
                  let v131 = opp(v129);
                  let v137 = add_1(b_1, v64);
                  (v131, v137)
                },
              }
            },
          }
        },
      }
    },
    b::IntegerTag::Negative => {
      let v157 = Rc::clone(&a_1);
      let a_ = b::integer_magnitude(v157);
      let v161 = Rc::clone(&b_1);
      let v162 = b::integer_tag(v161);
      match &v162 {
        b::IntegerTag::Zero => {
          std::mem::drop(a_);
          std::mem::drop(b_1);
          let v166 = b::zero();
          (v166, a_1)
        },
        b::IntegerTag::Positive => {
          let v176 = Rc::clone(&b_1);
          let p = b::integer_magnitude(v176);
          let v183 = Rc::clone(&b_1);
          let v184 = pos_div_eucl_1(a_, v183);
          match v184 {
            (v186, v188) => {
              let q = &v188;
              let v192 = Rc::clone(q);
              match b::integer_tag(v192) {
                b::IntegerTag::Zero => {
                  std::mem::drop(p);
                  std::mem::drop(b_1);
                  std::mem::drop(a_1);
                  std::mem::drop(v188);
                  let v198 = opp(v186);
                  let v199 = b::zero();
                  (v198, v199)
                },
                b::IntegerTag::Positive => {
                  std::mem::drop(p);
                  std::mem::drop(a_1);
                  let v209 = Rc::clone(q);
                  let p_1 = b::integer_magnitude(v209);
                  std::mem::drop(p_1);
                  let v214 = b::one();
                  let v216 = b::identity(v214);
                  let v222 = add_1(v186, v216);
                  let v224 = opp(v222);
                  let v230 = sub(b_1, v188);
                  (v224, v230)
                },
                b::IntegerTag::Negative => {
                  std::mem::drop(p);
                  std::mem::drop(a_1);
                  let v240 = Rc::clone(q);
                  let p_1 = b::integer_magnitude(v240);
                  std::mem::drop(p_1);
                  let v245 = b::one();
                  let v247 = b::identity(v245);
                  let v253 = add_1(v186, v247);
                  let v255 = opp(v253);
                  let v261 = sub(b_1, v188);
                  (v255, v261)
                },
              }
            },
          }
        },
        b::IntegerTag::Negative => {
          std::mem::drop(a_1);
          let b_ = b::integer_magnitude(b_1);
          let v282 = b::identity(b_);
          let v287 = pos_div_eucl_1(a_, v282);
          match v287 {
            (v289, v291) => {
              let v296 = opp(v291);
              (v289, v296)
            },
          }
        },
      }
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.modulo
// Variant: uncurried
pub fn modulo(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = b::modulo(v0, v1);
  v8
}

// Rocq: StdGalilei.bigint.zgcd_loop
// Variant: uncurried
pub fn zgcd_loop_1(a_1: Rc<BigInt>, b_1: Rc<BigInt>) -> Rc<BigInt> {
  let v12 = zgcd_loop(a_1, b_1, ());
  v12
}

// Rocq: StdGalilei.bigint.zgcd_loop (local: zgcd_loop)
// Variant: uncurried, lifted
pub fn zgcd_loop(a_1: Rc<BigInt>, b_1: Rc<BigInt>, _H: ()) -> Rc<BigInt> {
  let v5 = b::zero();
  let v9 = Rc::clone(&b_1);
  let v34 = match ltb_2(v5, v9) {
    true => {
      let v17 = Rc::clone(&b_1);
      let v18 = modulo(a_1, v17);
      let v29 = zgcd_loop(b_1, v18, ());
      v29
    },
    false => {
      std::mem::drop(b_1);
      a_1
    },
  };
  v34
}

// Rocq: StdGalilei.bigint.zgcd
// Variant: uncurried
pub fn zgcd_owned(a_1: Rc<BigInt>, b_1: Rc<BigInt>) -> Rc<BigInt> {
  let v6 = abs_owned(a_1);
  let v10 = abs_owned(b_1);
  let v16 = zgcd_loop_1(v6, v10);
  v16
}

// Rocq: StdGalilei.bigint.zgcd
// Variant: borrowed, uncurried
pub fn zgcd(a_1: &Rc<BigInt>, b_1: &Rc<BigInt>) -> Rc<BigInt> {
  let v6 = abs(a_1);
  let v10 = abs(b_1);
  let v16 = zgcd_loop_1(v6, v10);
  v16
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.row_gcd
// Variant: uncurried
pub fn row_gcd(T: Rc<Array<Rc<BigInt>>>, w: u64, i: u64) -> Rc<BigInt> {
  let v4 = {
    move |_v5: u64, v6: Rc<BigInt>| -> bool {
      std::mem::drop(v6);
      true
    }
  };
  let v11: Rc<dyn Fn(u64, Rc<BigInt>) -> bool> = Rc::new(v4);
  let v12: Rc<dyn Fn(u64, Rc<BigInt>) -> bool> = v11;
  let v19 = {
    let __anf_capture_22 = w;
    move |j: u64, g: Rc<BigInt>| -> Rc<BigInt> {
      let i = &i;
      let w = &__anf_capture_22;
      let T = &T;
      let v41 = add(mul(Clone::clone(i), Clone::clone(w)), j);
      let v43 = a::get::<Rc<BigInt>>(&T, v41);
      let v49 = zgcd_owned(g, v43);
      v49
    }
  };
  let v51: Rc<dyn Fn(u64, Rc<BigInt>) -> Rc<BigInt>> = Rc::new(v19);
  let v55 = b::zero();
  let v67 = loop_::<Rc<BigInt>>(w, v12, v51, 0u64, v55);
  v67
}

// Rocq: Corelib.BinNums.IntDef.Z.div
// Variant: uncurried
pub fn div_owned(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = b::div(v0, v1);
  v8
}

// Rocq: Corelib.BinNums.IntDef.Z.div
// Variant: borrowed, uncurried
pub fn div(v0: &Rc<BigInt>, v1: &Rc<BigInt>) -> Rc<BigInt> {
  let v5 = Rc::clone(v0);
  let v8 = Rc::clone(v1);
  let v10 = b::div(v5, v8);
  v10
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.div_row
// Variant: uncurried
pub fn div_row(T: Rc<Array<Rc<BigInt>>>, w: u64, i: u64, g: Rc<BigInt>) -> Rc<Array<Rc<BigInt>>> {
  let v5 = {
    move |_v6: u64, v7: Rc<Array<Rc<BigInt>>>| -> bool {
      std::mem::drop(v7);
      true
    }
  };
  let v12: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = Rc::new(v5);
  let v13: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = v12;
  let v20 = {
    let __anf_capture_23 = w;
    move |j: u64, T: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let i = &i;
      let w = &__anf_capture_23;
      let g = &g;
      let v40 = add(mul(Clone::clone(i), Clone::clone(w)), j);
      let v53 = add(mul(Clone::clone(i), Clone::clone(w)), j);
      let v54 = &T;
      let v58 = a::get::<Rc<BigInt>>(&v54, v53);
      let v61 = Rc::clone(g);
      let v62 = div_owned(v58, v61);
      a::set::<Rc<BigInt>>(T, v40, v62)
    }
  };
  let v72: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new(v20);
  loop_::<Rc<Array<Rc<BigInt>>>>(w, v13, v72, 0u64, T)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.elim_row
// Variant: uncurried
pub fn elim_row(w: u64, c: u64, r: u64, a_1: Rc<BigInt>, i: u64, T: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  match eqb(i, r) {
    true => {
      std::mem::drop(a_1);
      T
    },
    false => {
      let v26 = add(mul(i, w), c);
      let v27 = &T;
      let b_1 = a::get::<Rc<BigInt>>(&v27, v26);
      let v32 = b::zero();
      let v35 = Rc::clone(&b_1);
      match eqb_2(v35, v32) {
        true => {
          std::mem::drop(b_1);
          std::mem::drop(a_1);
          T
        },
        false => {
          let T_1 = upd_row(T, w, i, r, a_1, b_1);
          let v59 = Rc::clone(&T_1);
          let g = row_gcd(v59, w, i);
          let v67 = b::one();
          let v70 = b::identity(v67);
          let v74 = Rc::clone(&g);
          match ltb_2(v70, v74) {
            true => {
              div_row(T_1, w, i, g)
            },
            false => {
              std::mem::drop(g);
              T_1
            },
          }
        },
      }
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.col_step
// Variant: uncurried
pub fn col_step(n: u64, w: u64, c: u64, st: (Rc<Array<Rc<BigInt>>>, u64)) -> (Rc<Array<Rc<BigInt>>>, u64) {
  match st {
    (v5, v7) => {
      let r = &v5;
      let v12 = Rc::clone(r);
      let q = find_piv(v12, n, w, c, v7);
      match eqb(q, n) {
        true => {
          (v5, v7)
        },
        false => {
          let T = swap_rows(v5, w, q, v7);
          let v58 = add(mul(v7, w), c);
          let v59 = &T;
          let a_1 = a::get::<Rc<BigInt>>(&v59, v58);
          let v64 = {
            move |_v65: u64, v66: Rc<Array<Rc<BigInt>>>| -> bool {
              std::mem::drop(v66);
              true
            }
          };
          let v71: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = Rc::new(v64);
          let v72: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = v71;
          let v81 = {
            let __anf_capture_82 = w;
            let __anf_capture_84 = c;
            let __anf_capture_86 = v7;
            move |v90: u64, v91: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
              let v94 = Clone::clone(&__anf_capture_82);
              let v96 = Clone::clone(&__anf_capture_84);
              let v98 = Clone::clone(&__anf_capture_86);
              let v100 = Rc::clone(&a_1);
              elim_row(v94, v96, v98, v100, v90, v91)
            }
          };
          let v108: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new(v81);
          let v122 = loop_::<Rc<Array<Rc<BigInt>>>>(n, v72, v108, 0u64, T);
          (v122, add(v7, 1u64))
        },
      }
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.eliminate
// Variant: uncurried
pub fn eliminate(n: u64, w: u64, T: Rc<Array<Rc<BigInt>>>) -> (Rc<Array<Rc<BigInt>>>, u64) {
  let v4 = {
    move |_v5: u64, v6: (Rc<Array<Rc<BigInt>>>, u64)| -> bool {
      std::mem::drop(v6);
      true
    }
  };
  let v11: Rc<dyn Fn(u64, (Rc<Array<Rc<BigInt>>>, u64)) -> bool> = Rc::new(v4);
  let v12: Rc<dyn Fn(u64, (Rc<Array<Rc<BigInt>>>, u64)) -> bool> = v11;
  let v17 = {
    let __anf_capture_18 = n;
    move |v22: u64, v23: (Rc<Array<Rc<BigInt>>>, u64)| -> (Rc<Array<Rc<BigInt>>>, u64) {
      let v26 = Clone::clone(&__anf_capture_18);
      let v28 = Clone::clone(&w);
      col_step(v26, v28, v22, v23)
    }
  };
  let v36: Rc<dyn Fn(u64, (Rc<Array<Rc<BigInt>>>, u64)) -> (Rc<Array<Rc<BigInt>>>, u64)> = Rc::new(v17);
  loop_::<(Rc<Array<Rc<BigInt>>>, u64)>(n, v12, v36, 0u64, (T, 0u64))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.inconsistent
// Variant: uncurried
pub fn inconsistent(T: Rc<Array<Rc<BigInt>>>, n: u64, w: u64, r: u64) -> bool {
  let v5 = {
    move |_v6: u64, _v7: bool| -> bool {
      true
    }
  };
  let v12: Rc<dyn Fn(u64, bool) -> bool> = Rc::new(v5);
  let v13: Rc<dyn Fn(u64, bool) -> bool> = v12;
  let v20 = {
    let __anf_capture_23 = n;
    move |i: u64, fl: bool| -> bool {
      let w = &w;
      let n = &__anf_capture_23;
      let T = &T;
      let v44 = add(mul(i, Clone::clone(w)), Clone::clone(n));
      let v46 = a::get::<Rc<BigInt>>(&T, v44);
      let v47 = b::zero();
      orb(fl, negb(eqb_2(v46, v47)))
    }
  };
  let v63: Rc<dyn Fn(u64, bool) -> bool> = Rc::new(v20);
  loop_::<bool>(n, v13, v63, r, false)
}

// Rocq: Corelib.Floats.SpecFloat.digits2_pos
pub fn digits2_pos_1(n: Rc<BigInt>) -> Rc<BigInt> {
  let v5 = digits2_pos(n);
  v5
}

// Rocq: Corelib.Floats.SpecFloat.digits2_pos (local: digits2_pos)
// Variant: lifted
pub fn digits2_pos(n: Rc<BigInt>) -> Rc<BigInt> {
  let v3 = Rc::clone(&n);
  let v36 = match b::positive_tag(v3) {
    b::PositiveTag::Odd => {
      let p = b::positive_tail(n);
      let v14 = digits2_pos(p);
      let v17 = succ(v14);
      v17
    },
    b::PositiveTag::Even => {
      let p = b::positive_tail(n);
      let v27 = digits2_pos(p);
      let v30 = succ(v27);
      v30
    },
    b::PositiveTag::One => {
      std::mem::drop(n);
      let v33 = b::one();
      v33
    },
  };
  v36
}

// Rocq: Corelib.Floats.SpecFloat.Zdigits2
pub fn Zdigits2(n: Rc<BigInt>) -> Rc<BigInt> {
  let v3 = Rc::clone(&n);
  let v33 = match b::integer_tag(v3) {
    b::IntegerTag::Zero => {
      n
    },
    b::IntegerTag::Positive => {
      let p = b::integer_magnitude(n);
      let v15 = digits2_pos_1(p);
      let v18 = b::identity(v15);
      v18
    },
    b::IntegerTag::Negative => {
      let p = b::integer_magnitude(n);
      let v27 = digits2_pos_1(p);
      let v30 = b::identity(v27);
      v30
    },
  };
  v33
}

// Rocq: Corelib.BinNums.IntDef.Z.max
// Variant: uncurried
pub fn max(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = b::max(v0, v1);
  v8
}

// Rocq: Corelib.Floats.SpecFloat.emin
// Variant: uncurried
pub fn emin(prec_1: Rc<BigInt>, emax_1: Rc<BigInt>) -> Rc<BigInt> {
  let v5 = b::one();
  let v8 = b::twice_plus_one(v5);
  let v11 = b::identity(v8);
  let v16 = sub(v11, emax_1);
  let v21 = sub(v16, prec_1);
  v21
}

// Rocq: Corelib.Floats.SpecFloat.fexp
// Variant: uncurried
pub fn fexp(prec_1: Rc<BigInt>, emax_1: Rc<BigInt>, e: Rc<BigInt>) -> Rc<BigInt> {
  let v9 = Rc::clone(&prec_1);
  let v10 = sub(e, v9);
  let v16 = emin(prec_1, emax_1);
  let v22 = max(v10, v16);
  v22
}

// Rocq: Corelib.BinNums.IntDef.Z.even
pub fn even(v0: Rc<BigInt>) -> bool {
  b::even(v0)
}

// Rocq: Corelib.Floats.SpecFloat.new_location_even
// Variant: uncurried
pub fn new_location_even(nb_steps: Rc<BigInt>, k: Rc<BigInt>) -> Rc<location> {
  let v3 = b::zero();
  let v6 = Rc::clone(&k);
  match eqb_2(v6, v3) {
    true => {
      std::mem::drop(nb_steps);
      std::mem::drop(k);
      Rc::new(location::loc_Exact)
    },
    false => {
      let v19 = b::one();
      let v22 = b::twice(v19);
      let v25 = b::identity(v22);
      let v30 = mul_2(v25, k);
      Rc::new(location::loc_Inexact(compare(v30, nb_steps)))
    },
  }
}

// Rocq: Corelib.Floats.SpecFloat.new_location_odd
// Variant: uncurried
pub fn new_location_odd(nb_steps: Rc<BigInt>, k: Rc<BigInt>) -> Rc<location> {
  let v3 = b::zero();
  let v6 = Rc::clone(&k);
  match eqb_2(v6, v3) {
    true => {
      std::mem::drop(nb_steps);
      std::mem::drop(k);
      Rc::new(location::loc_Exact)
    },
    false => {
      let v20 = b::one();
      let v23 = b::twice(v20);
      let v26 = b::identity(v23);
      let v30 = mul_2(v26, k);
      let v32 = b::one();
      let v34 = b::identity(v32);
      let v40 = add_1(v30, v34);
      let v59 = match compare(v40, nb_steps) {
        std::cmp::Ordering::Equal => {
          std::cmp::Ordering::Less
        },
        std::cmp::Ordering::Less => {
          std::cmp::Ordering::Less
        },
        std::cmp::Ordering::Greater => {
          std::cmp::Ordering::Greater
        },
      };
      Rc::new(location::loc_Inexact(v59))
    },
  }
}

// Rocq: Corelib.Floats.SpecFloat.new_location
pub fn new_location(nb_steps: Rc<BigInt>) -> Rc<dyn Fn(Rc<BigInt>) -> Rc<location>> {
  let v4 = Rc::clone(&nb_steps);
  let v6: Rc<dyn Fn(Rc<BigInt>) -> Rc<location>> = match even(v4) {
    true => {
      let v9 = {
        let __anf_capture_10 = nb_steps;
        move |v12: Rc<BigInt>| -> Rc<location> {
          let v15 = Rc::clone(&__anf_capture_10);
          new_location_even(v15, v12)
        }
      };
      let v21: Rc<dyn Fn(Rc<BigInt>) -> Rc<location>> = Rc::new(v9);
      v21
    },
    false => {
      let v27 = {
        let __anf_capture_28 = nb_steps;
        move |v30: Rc<BigInt>| -> Rc<location> {
          let v33 = Rc::clone(&__anf_capture_28);
          new_location_odd(v33, v30)
        }
      };
      let v39: Rc<dyn Fn(Rc<BigInt>) -> Rc<location>> = Rc::new(v27);
      v39
    },
  };
  v6
}

// Rocq: Corelib.Floats.SpecFloat.SFdiv_core_binary
// Variant: uncurried
pub fn SFdiv_core_binary(prec_1: Rc<BigInt>, emax_1: Rc<BigInt>, m1: Rc<BigInt>, e1: Rc<BigInt>, m2: Rc<BigInt>, e2: Rc<BigInt>) -> ((Rc<BigInt>, Rc<BigInt>), Rc<location>) {
  let v9 = Rc::clone(&m1);
  let d1_1 = Zdigits2(v9);
  let v14 = Rc::clone(&m2);
  let d2 = Zdigits2(v14);
  let v24 = Rc::clone(&e1);
  let v25 = add_1(d1_1, v24);
  let v31 = Rc::clone(&e2);
  let v32 = add_1(d2, v31);
  let v37 = sub(v25, v32);
  let v44 = fexp(prec_1, emax_1, v37);
  let v48 = Rc::clone(&e1);
  let v51 = Rc::clone(&e2);
  let v52 = sub(v48, v51);
  let e_ = min(v44, v52);
  let v65 = sub(e1, e2);
  let v69 = Rc::clone(&e_);
  let s = sub(v65, v69);
  let v73 = Rc::clone(&s);
  let m_ = match b::integer_tag(v73) {
    b::IntegerTag::Zero => {
      std::mem::drop(s);
      m1
    },
    b::IntegerTag::Positive => {
      let v80 = Rc::clone(&s);
      let p = b::integer_magnitude(v80);
      std::mem::drop(p);
      let v88 = shiftl(m1, s);
      v88
    },
    b::IntegerTag::Negative => {
      std::mem::drop(m1);
      let p = b::integer_magnitude(s);
      std::mem::drop(p);
      let v94 = b::zero();
      v94
    },
  };
  let v102 = Rc::clone(&m2);
  let v103 = div_eucl(m_, v102);
  match v103 {
    (v105, v107) => {
      let v114 = (v105, e_);
      let v118: Rc<dyn Fn(Rc<BigInt>) -> Rc<location>> = new_location(m2);
      let v119: &Rc<dyn Fn(Rc<BigInt>) -> Rc<location>> = &v118;
      let v122 = v119(v107);
      std::mem::drop(v118);
      (v114, v122)
    },
  }
}

// Rocq: Corelib.Floats.FloatOps.emax
pub fn emax(_v0: ()) -> Rc<BigInt> {
  let v2 = b::one();
  let v5 = b::twice(v2);
  let v8 = b::twice(v5);
  let v11 = b::twice(v8);
  let v14 = b::twice(v11);
  let v17 = b::twice(v14);
  let v20 = b::twice(v17);
  let v23 = b::twice(v20);
  let v26 = b::twice(v23);
  let v29 = b::twice(v26);
  let v32 = b::twice(v29);
  let v35 = b::identity(v32);
  v35
}

// Rocq: Corelib.Floats.SpecFloat.iter_pos
// Variant: uncurried
pub fn iter_pos_1<A: Clone + 'static>(f: Rc<dyn Fn(A) -> A>, n: Rc<BigInt>) -> Rc<dyn Fn(A) -> A> {
  let v7: Rc<dyn Fn(A) -> A> = iter_pos_curried_owned::<A>(f, n);
  v7
}

// Rocq: Corelib.Floats.SpecFloat.iter_pos (local: iter_pos)
// Variant: lifted
pub fn iter_pos_curried_owned<A: Clone + 'static>(f: Rc<dyn Fn(A) -> A>, n: Rc<BigInt>) -> Rc<dyn Fn(A) -> A> {
  let v6 = {
    move |x: A| -> A {
      let f = &f;
      let n = &n;
      let v17 = iter_pos::<A>(f, n, x);
      v17
    }
  };
  let v20: Rc<dyn Fn(A) -> A> = Rc::new(v6);
  v20
}

// Rocq: Corelib.Floats.SpecFloat.iter_pos (local: iter_pos)
// Variant: uncurried, lifted
pub fn iter_pos_owned<A: Clone + 'static>(f: Rc<dyn Fn(A) -> A>, n: Rc<BigInt>, x: A) -> A {
  let v5 = Rc::clone(&n);
  match b::positive_tag(v5) {
    b::PositiveTag::Odd => {
      let n_ = b::positive_tail(n);
      let v11: &Rc<dyn Fn(A) -> A> = &f;
      let v14 = v11(x);
      let v17: Rc<dyn Fn(A) -> A> = Rc::clone(&f);
      let v21 = Rc::clone(&n_);
      let v24 = iter_pos_owned::<A>(v17, v21, v14);
      iter_pos_owned::<A>(f, n_, v24)
    },
    b::PositiveTag::Even => {
      let n_ = b::positive_tail(n);
      let v40: Rc<dyn Fn(A) -> A> = Rc::clone(&f);
      let v44 = Rc::clone(&n_);
      let v47 = iter_pos_owned::<A>(v40, v44, x);
      iter_pos_owned::<A>(f, n_, v47)
    },
    b::PositiveTag::One => {
      std::mem::drop(n);
      let v58: &Rc<dyn Fn(A) -> A> = &f;
      let v61 = v58(x);
      std::mem::drop(f);
      v61
    },
  }
}

// Rocq: Corelib.Floats.SpecFloat.iter_pos (local: iter_pos)
// Variant: borrowed, uncurried, lifted
pub fn iter_pos<A: Clone + 'static>(f: &Rc<dyn Fn(A) -> A>, n: &Rc<BigInt>, x: A) -> A {
  let x_1 = x;
  let v6 = Rc::clone(n);
  match b::positive_tag(v6) {
    b::PositiveTag::Odd => {
      let v11 = Rc::clone(n);
      let n_ = b::positive_tail(v11);
      let v16 = f(x_1);
      let v19: Rc<dyn Fn(A) -> A> = Rc::clone(f);
      let v23 = Rc::clone(&n_);
      let v26 = iter_pos_owned::<A>(v19, v23, v16);
      let v29: Rc<dyn Fn(A) -> A> = Rc::clone(f);
      iter_pos_owned::<A>(v29, n_, v26)
    },
    b::PositiveTag::Even => {
      let v40 = Rc::clone(n);
      let n_ = b::positive_tail(v40);
      let v44: Rc<dyn Fn(A) -> A> = Rc::clone(f);
      let v48 = Rc::clone(&n_);
      let v51 = iter_pos_owned::<A>(v44, v48, x_1);
      let v54: Rc<dyn Fn(A) -> A> = Rc::clone(f);
      iter_pos_owned::<A>(v54, n_, v51)
    },
    b::PositiveTag::One => {
      f(x_1)
    },
  }
}

// Rocq: Corelib.Floats.SpecFloat.shr_1
pub fn shr_1(mrs: Rc<shr_record>) -> Rc<shr_record> {
  let (v1, v2) = __rocq_reuse::reset(mrs, |__payload| Clone::clone(__payload));
  match v1 {
    shr_record { shr_m: v9, shr_r: v11, shr_s: v13 } => {
      let s = &v9;
      let s_1 = orb(v11, v13);
      let v23 = Rc::clone(s);
      match b::integer_tag(v23) {
        b::IntegerTag::Zero => {
          std::mem::drop(v9);
          let v26 = b::zero();
          __rocq_reuse::rebuild(v2, shr_record { shr_m: v26, shr_r: false, shr_s: s_1 })
        },
        b::IntegerTag::Positive => {
          let p0 = b::integer_magnitude(v9);
          let v45 = Rc::clone(&p0);
          match b::positive_tag(v45) {
            b::PositiveTag::Odd => {
              let p = b::positive_tail(p0);
              let v53 = b::identity(p);
              __rocq_reuse::rebuild(v2, shr_record { shr_m: v53, shr_r: true, shr_s: s_1 })
            },
            b::PositiveTag::Even => {
              let p = b::positive_tail(p0);
              let v72 = b::identity(p);
              __rocq_reuse::rebuild(v2, shr_record { shr_m: v72, shr_r: false, shr_s: s_1 })
            },
            b::PositiveTag::One => {
              std::mem::drop(p0);
              let v86 = b::zero();
              __rocq_reuse::rebuild(v2, shr_record { shr_m: v86, shr_r: true, shr_s: s_1 })
            },
          }
        },
        b::IntegerTag::Negative => {
          let p0 = b::integer_magnitude(v9);
          let v108 = Rc::clone(&p0);
          match b::positive_tag(v108) {
            b::PositiveTag::Odd => {
              let p = b::positive_tail(p0);
              let v116 = b::neg(p);
              __rocq_reuse::rebuild(v2, shr_record { shr_m: v116, shr_r: true, shr_s: s_1 })
            },
            b::PositiveTag::Even => {
              let p = b::positive_tail(p0);
              let v135 = b::neg(p);
              __rocq_reuse::rebuild(v2, shr_record { shr_m: v135, shr_r: false, shr_s: s_1 })
            },
            b::PositiveTag::One => {
              std::mem::drop(p0);
              let v149 = b::zero();
              __rocq_reuse::rebuild(v2, shr_record { shr_m: v149, shr_r: true, shr_s: s_1 })
            },
          }
        },
      }
    },
  }
}

// Rocq: Corelib.Floats.SpecFloat.shr
// Variant: uncurried
pub fn shr(mrs: Rc<shr_record>, e: Rc<BigInt>, n: Rc<BigInt>) -> (Rc<shr_record>, Rc<BigInt>) {
  let v5 = Rc::clone(&n);
  match b::integer_tag(v5) {
    b::IntegerTag::Zero => {
      std::mem::drop(n);
      (mrs, e)
    },
    b::IntegerTag::Positive => {
      let v18 = Rc::clone(&n);
      let p = b::integer_magnitude(v18);
      let v21: fn(Rc<shr_record>) -> Rc<shr_record> = shr_1;
      let v22: Rc<dyn Fn(Rc<shr_record>) -> Rc<shr_record>> = Rc::new(v21);
      let v28: Rc<dyn Fn(Rc<shr_record>) -> Rc<shr_record>> = iter_pos_1::<Rc<shr_record>>(v22, p);
      let v29: &Rc<dyn Fn(Rc<shr_record>) -> Rc<shr_record>> = &v28;
      let v32 = v29(mrs);
      std::mem::drop(v28);
      let v38 = add_1(e, n);
      (v32, v38)
    },
    b::IntegerTag::Negative => {
      let p = b::integer_magnitude(n);
      std::mem::drop(p);
      (mrs, e)
    },
  }
}

// Rocq: Corelib.Floats.SpecFloat.shr_record_of_loc
// Variant: uncurried
pub fn shr_record_of_loc(m: Rc<BigInt>, l: Rc<location>) -> Rc<shr_record> {
  let (v2, v3) = __rocq_reuse::reset(l, |__payload| Clone::clone(__payload));
  std::mem::drop(v3);
  match v2 {
    location::loc_Exact => {
      Rc::new(shr_record { shr_m: m, shr_r: false, shr_s: false })
    },
    location::loc_Inexact(v23) => {
      match v23 {
        std::cmp::Ordering::Equal => {
          Rc::new(shr_record { shr_m: m, shr_r: true, shr_s: false })
        },
        std::cmp::Ordering::Less => {
          Rc::new(shr_record { shr_m: m, shr_r: false, shr_s: true })
        },
        std::cmp::Ordering::Greater => {
          Rc::new(shr_record { shr_m: m, shr_r: true, shr_s: true })
        },
      }
    },
  }
}

// Rocq: Corelib.Floats.SpecFloat.shr_fexp
// Variant: uncurried
pub fn shr_fexp(prec_1: Rc<BigInt>, emax_1: Rc<BigInt>, m: Rc<BigInt>, e: Rc<BigInt>, l: Rc<location>) -> (Rc<shr_record>, Rc<BigInt>) {
  let v9 = Rc::clone(&m);
  let v12 = shr_record_of_loc(v9, l);
  let v20 = Zdigits2(m);
  let v24 = Rc::clone(&e);
  let v25 = add_1(v20, v24);
  let v33 = fexp(prec_1, emax_1, v25);
  let v37 = Rc::clone(&e);
  let v38 = sub(v33, v37);
  shr(v12, e, v38)
}

// Rocq: Corelib.Floats.SpecFloat.round_nearest_even
// Variant: uncurried
pub fn round_nearest_even(mx: Rc<BigInt>, lx: Rc<location>) -> Rc<BigInt> {
  let (v2, v3) = __rocq_reuse::reset(lx, |__payload| Clone::clone(__payload));
  std::mem::drop(v3);
  let v54 = match v2 {
    location::loc_Exact => {
      mx
    },
    location::loc_Inexact(v10) => {
      let v51 = match v10 {
        std::cmp::Ordering::Equal => {
          let v16 = Rc::clone(&mx);
          let v34 = match even(v16) {
            true => {
              mx
            },
            false => {
              let v23 = b::one();
              let v25 = b::identity(v23);
              let v31 = add_1(mx, v25);
              v31
            },
          };
          v34
        },
        std::cmp::Ordering::Less => {
          mx
        },
        std::cmp::Ordering::Greater => {
          let v40 = b::one();
          let v42 = b::identity(v40);
          let v48 = add_1(mx, v42);
          v48
        },
      };
      v51
    },
  };
  v54
}

// Rocq: Corelib.Floats.SpecFloat.shr_m
pub fn shr_m_owned(s: Rc<shr_record>) -> Rc<BigInt> {
  let v3 = Rc::clone((&(&**&s).shr_m));
  std::mem::drop(s);
  v3
}

// Rocq: Corelib.Floats.SpecFloat.shr_m
// Variant: borrowed
pub fn shr_m(s: &Rc<shr_record>) -> Rc<BigInt> {
  let v1 = s;
  let v4 = Rc::clone((&(&**v1).shr_m));
  v4
}

// Rocq: Corelib.Floats.SpecFloat.loc_of_shr_record
pub fn loc_of_shr_record(mrs: Rc<shr_record>) -> Rc<location> {
  let (v1, v2) = __rocq_reuse::reset(mrs, |__payload| Clone::clone(__payload));
  std::mem::drop(v2);
  match v1 {
    shr_record { shr_m: v9, shr_r: v11, shr_s: v13 } => {
      let shr_m_1 = &v13;
      match v11 {
        true => {
          match shr_m_1 {
            true => {
              std::mem::drop(v9);
              Rc::new(location::loc_Inexact(std::cmp::Ordering::Greater))
            },
            false => {
              std::mem::drop(v9);
              Rc::new(location::loc_Inexact(std::cmp::Ordering::Equal))
            },
          }
        },
        false => {
          match shr_m_1 {
            true => {
              std::mem::drop(v9);
              Rc::new(location::loc_Inexact(std::cmp::Ordering::Less))
            },
            false => {
              std::mem::drop(v9);
              Rc::new(location::loc_Exact)
            },
          }
        },
      }
    },
  }
}

// Rocq: Corelib.Floats.SpecFloat.binary_round_aux
// Variant: uncurried
pub fn binary_round_aux(prec_1: Rc<BigInt>, emax_1: Rc<BigInt>, sx: bool, mx: Rc<BigInt>, ex: Rc<BigInt>, lx: Rc<location>) -> Rc<spec_float> {
  let v9 = Rc::clone(&prec_1);
  let v12 = Rc::clone(&emax_1);
  let v19 = shr_fexp(v9, v12, mx, ex, lx);
  match v19 {
    (v21, v23) => {
      let e_ = &v21;
      let v30 = shr_m(e_);
      let v39 = round_nearest_even(v30, loc_of_shr_record(v21));
      let v42 = Rc::new(location::loc_Exact);
      let v45 = Rc::clone(&prec_1);
      let v48 = Rc::clone(&emax_1);
      let v55 = shr_fexp(v45, v48, v39, v23, v42);
      match v55 {
        (v57, v59) => {
          let mrs__ = &v59;
          let v65 = shr_m_owned(v57);
          let v68 = Rc::clone(&v65);
          match b::integer_tag(v68) {
            b::IntegerTag::Zero => {
              std::mem::drop(v65);
              std::mem::drop(emax_1);
              std::mem::drop(prec_1);
              std::mem::drop(v59);
              Rc::new(spec_float::S754_zero { s: sx })
            },
            b::IntegerTag::Positive => {
              let m = b::integer_magnitude(v65);
              let v87 = sub(emax_1, prec_1);
              let v89 = Rc::clone(mrs__);
              match leb_owned(v89, v87) {
                true => {
                  Rc::new(spec_float::S754_finite { s: sx, m, e: v59 })
                },
                false => {
                  std::mem::drop(m);
                  std::mem::drop(v59);
                  Rc::new(spec_float::S754_infinity { s: sx })
                },
              }
            },
            b::IntegerTag::Negative => {
              std::mem::drop(emax_1);
              std::mem::drop(prec_1);
              std::mem::drop(v59);
              let p = b::integer_magnitude(v65);
              std::mem::drop(p);
              Rc::new(spec_float::S754_nan)
            },
          }
        },
      }
    },
  }
}

// Rocq: Corelib.Init.Datatypes.xorb
// Variant: uncurried
pub fn xorb(b1: bool, b2: bool) -> bool {
  match b1 {
    true => {
      match b2 {
        true => {
          false
        },
        false => {
          true
        },
      }
    },
    false => {
      b2
    },
  }
}

// Rocq: Corelib.Floats.PrimFloat.of_uint63
pub fn of_uint63(v0: u64) -> f64 {
  rocq_float64::of_uint63(v0)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.Uint63Axioms.of_Z
pub fn of_Z(v0: Rc<BigInt>) -> u64 {
  b::to_uint63(v0)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.z2i
pub fn z2i(z: Rc<BigInt>) -> u64 {
  of_Z(z)
}

// Rocq: Corelib.Floats.PrimFloat.ldshiftexp
// Variant: uncurried
pub fn ldshiftexp(v0: f64, v1: u64) -> f64 {
  rocq_float64::ldshiftexp(v0, v1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.ldexp'
// Variant: borrowed, uncurried
pub fn ldexp_(f: f64, e: &Rc<BigInt>) -> f64 {
  let f_1 = f;
  let v11 = emax(());
  let v18 = prec(());
  let v24 = emax(());
  let v29 = emin(v18, v24);
  let v34 = sub(v11, v29);
  let v37 = Rc::clone(e);
  let v40 = min(v37, v34);
  let v49 = prec(());
  let v55 = emax(());
  let v60 = emin(v49, v55);
  let v66 = emax(());
  let v71 = sub(v60, v66);
  let v73 = b::one();
  let v75 = b::identity(v73);
  let v80 = sub(v71, v75);
  let e_ = max(v40, v80);
  let v94 = shift(());
  let v100 = add_1(e_, v94);
  ldshiftexp(f_1, z2i(v100))
}

// Rocq: Corelib.Floats.PrimFloat.opp
pub fn opp_1(v0: f64) -> f64 {
  rocq_float64::opp(v0)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.SF2Prim'
pub fn SF2Prim_(ef: Rc<spec_float>) -> f64 {
  let (v1, v2) = __rocq_reuse::reset(ef, |__payload| Clone::clone(__payload));
  std::mem::drop(v2);
  match v1 {
    spec_float::S754_zero { s: v11 } => {
      match v11 {
        true => {
          __rocq_global_3377
        },
        false => {
          __rocq_global_371
        },
      }
    },
    spec_float::S754_infinity { s: v23 } => {
      match v23 {
        true => {
          __rocq_global_3380
        },
        false => {
          __rocq_global_1215
        },
      }
    },
    spec_float::S754_nan => {
      __rocq_global_3383
    },
    spec_float::S754_finite { s: v38, m: v40, e: v42 } => {
      let e = &v38;
      let s = &v42;
      let v51 = b::identity(v40);
      let pm = of_uint63(z2i(v51));
      let f = ldexp_(pm, s);
      match e {
        true => {
          std::mem::drop(v42);
          opp_1(f)
        },
        false => {
          std::mem::drop(v42);
          f
        },
      }
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.qr
// Variant: uncurried
pub fn qr(sx: bool, mx: Rc<BigInt>, sy: bool, my: Rc<BigInt>) -> f64 {
  let v10 = prec(());
  let v16 = emax(());
  let v19 = b::identity(mx);
  let v20 = b::zero();
  let v23 = b::identity(my);
  let v24 = b::zero();
  let v37 = SFdiv_core_binary(v10, v16, v19, v20, v23, v24);
  match &v37 {
    (lz, p) => {
      match lz {
        (ez, mz) => {
          let v55 = prec(());
          let v61 = emax(());
          let v67 = xorb(sx, sy);
          let v75 = Rc::clone(ez);
          let v77 = Rc::clone(mz);
          let v79 = Rc::clone(p);
          let v80 = binary_round_aux(v55, v61, v67, v75, v77, v79);
          let (v81, v82) = __rocq_reuse::reset(v80, |__payload| Clone::clone(__payload));
          match v81 {
            spec_float::S754_zero { s: _v91 } => {
              std::mem::drop(v82);
              std::mem::drop(v37);
              __rocq_global_371
            },
            spec_float::S754_infinity { s: _v96 } => {
              std::mem::drop(v82);
              std::mem::drop(v37);
              __rocq_global_371
            },
            spec_float::S754_nan => {
              std::mem::drop(v82);
              std::mem::drop(v37);
              __rocq_global_371
            },
            spec_float::S754_finite { s: v104, m: v106, e: v108 } => {
              std::mem::drop(v37);
              SF2Prim_(__rocq_reuse::rebuild(v82, spec_float::S754_finite { s: v104, m: v106, e: v108 }))
            },
          }
        },
      }
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.qround
// Variant: uncurried
pub fn qround(num: Rc<BigInt>, den: Rc<BigInt>) -> f64 {
  let v4 = Rc::clone(&num);
  match b::integer_tag(v4) {
    b::IntegerTag::Zero => {
      std::mem::drop(num);
      std::mem::drop(den);
      __rocq_global_371
    },
    b::IntegerTag::Positive => {
      let mx = b::integer_magnitude(num);
      let v15 = Rc::clone(&den);
      match b::integer_tag(v15) {
        b::IntegerTag::Zero => {
          std::mem::drop(mx);
          std::mem::drop(den);
          __rocq_global_371
        },
        b::IntegerTag::Positive => {
          let my = b::integer_magnitude(den);
          qr(false, mx, false, my)
        },
        b::IntegerTag::Negative => {
          let my = b::integer_magnitude(den);
          qr(false, mx, true, my)
        },
      }
    },
    b::IntegerTag::Negative => {
      let mx = b::integer_magnitude(num);
      let v67 = Rc::clone(&den);
      match b::integer_tag(v67) {
        b::IntegerTag::Zero => {
          std::mem::drop(mx);
          std::mem::drop(den);
          __rocq_global_371
        },
        b::IntegerTag::Positive => {
          let my = b::integer_magnitude(den);
          qr(true, mx, false, my)
        },
        b::IntegerTag::Negative => {
          let my = b::integer_magnitude(den);
          qr(true, mx, true, my)
        },
      }
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.output
// Variant: uncurried
pub fn output(T: Rc<Array<Rc<BigInt>>>, n: u64, w: u64) -> Rc<Array<f64>> {
  let v4 = {
    move |_v5: u64, v6: Rc<Array<f64>>| -> bool {
      std::mem::drop(v6);
      true
    }
  };
  let v11: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(v4);
  let v12: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = v11;
  let v19 = {
    let __anf_capture_20 = n;
    move |i: u64, out: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let n = &__anf_capture_20;
      let w = &w;
      let T = &T;
      let v41 = add(mul(i, Clone::clone(w)), Clone::clone(n));
      let v43 = a::get::<Rc<BigInt>>(&T, v41);
      let v56 = add(mul(i, Clone::clone(w)), i);
      let v58 = a::get::<Rc<BigInt>>(&T, v56);
      a::set::<f64>(out, i, qround(v43, v58))
    }
  };
  let v73: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new(v19);
  let v82 = a::make::<f64>(n, __rocq_global_371);
  loop_::<Rc<Array<f64>>>(n, v12, v73, 0u64, v82)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.solve_exact
// Variant: uncurried
pub fn solve_exact(n: u64, a_1: Rc<Array<Rc<Array<f64>>>>, b_1: Rc<Array<f64>>) -> Rc<outcome<Rc<Array<f64>>>> {
  let w = add(n, 1u64);
  let T = build(a_1, b_1, n, w);
  let v28 = eliminate(n, w, T);
  match v28 {
    (v30, v32) => {
      let r = &v30;
      let v37 = Rc::clone(r);
      match inconsistent(v37, n, w, v32) {
        true => {
          std::mem::drop(v30);
          Rc::new(outcome::<Rc<Array<f64>>>::Inconsistent)
        },
        false => {
          match ltb(v32, n) {
            true => {
              std::mem::drop(v30);
              Rc::new(outcome::<Rc<Array<f64>>>::Multiple)
            },
            false => {
              let v71 = output(v30, n, w);
              Rc::new(outcome::<Rc<Array<f64>>>::Unique(v71))
            },
          }
        },
      }
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.free_cols
// Variant: uncurried
pub fn free_cols(pc: Rc<Array<u64>>, n: u64, r: u64) -> Rc<Array<u64>> {
  let v4 = {
    move |_v5: u64, v6: Rc<Array<bool>>| -> bool {
      std::mem::drop(v6);
      true
    }
  };
  let v11: Rc<dyn Fn(u64, Rc<Array<bool>>) -> bool> = Rc::new(v4);
  let v12: Rc<dyn Fn(u64, Rc<Array<bool>>) -> bool> = v11;
  let v15 = {
    move |t: u64, isp: Rc<Array<bool>>| -> Rc<Array<bool>> {
      let pc = &pc;
      let v22 = a::get::<u64>(&pc, t);
      a::set::<bool>(isp, v22, true)
    }
  };
  let v34: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new(v15);
  let v44 = a::make::<bool>(n, false);
  let isp = loop_::<Rc<Array<bool>>>(r, v12, v34, 0u64, v44);
  let v58 = {
    move |_v59: u64, v60: (Rc<Array<u64>>, u64)| -> bool {
      std::mem::drop(v60);
      true
    }
  };
  let v65: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> bool> = Rc::new(v58);
  let v66: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> bool> = v65;
  let v69 = {
    move |c: u64, st: (Rc<Array<u64>>, u64)| -> (Rc<Array<u64>>, u64) {
      let isp = &isp;
      match st {
        (v75, v77) => {
          match a::get::<bool>(&isp, c) {
            true => {
              (v75, v77)
            },
            false => {
              let v97 = a::set::<u64>(v75, v77, c);
              (v97, add(v77, 1u64))
            },
          }
        },
      }
    }
  };
  let v120: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> (Rc<Array<u64>>, u64)> = Rc::new(v69);
  let v130 = a::make::<u64>(n, 0u64);
  fst::<Rc<Array<u64>>, u64>(loop_::<(Rc<Array<u64>>, u64)>(n, v66, v120, 0u64, (v130, 0u64)))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.mark_D
// Variant: uncurried
pub fn mark_D(perm: Rc<Array<u64>>, n: u64, r: u64, k: u64) -> (Rc<Array<bool>>, Rc<Array<u64>>) {
  let v5 = {
    move |_v6: u64, v7: (Rc<Array<bool>>, Rc<Array<u64>>)| -> bool {
      std::mem::drop(v7);
      true
    }
  };
  let v12: Rc<dyn Fn(u64, (Rc<Array<bool>>, Rc<Array<u64>>)) -> bool> = Rc::new(v5);
  let v13: Rc<dyn Fn(u64, (Rc<Array<bool>>, Rc<Array<u64>>)) -> bool> = v12;
  let v18 = {
    move |t: u64, st: (Rc<Array<bool>>, Rc<Array<u64>>)| -> (Rc<Array<bool>>, Rc<Array<u64>>) {
      let r = &r;
      let perm = &perm;
      let v31 = add(Clone::clone(r), t);
      let d = a::get::<u64>(&perm, v31);
      let v36 = Clone::clone(&st);
      let v38 = fst::<Rc<Array<bool>>, Rc<Array<u64>>>(v36);
      let v47 = a::set::<bool>(v38, d, true);
      let v52 = snd::<Rc<Array<bool>>, Rc<Array<u64>>>(st);
      let v58 = a::set::<u64>(v52, d, t);
      (v47, v58)
    }
  };
  let v67: Rc<dyn Fn(u64, (Rc<Array<bool>>, Rc<Array<u64>>)) -> (Rc<Array<bool>>, Rc<Array<u64>>)> = Rc::new(v18);
  let v77 = a::make::<bool>(n, false);
  let v84 = a::make::<u64>(n, 0u64);
  loop_::<(Rc<Array<bool>>, Rc<Array<u64>>)>(k, v13, v67, 0u64, (v77, v84))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.mark_C
// Variant: uncurried
pub fn mark_C(fc: Rc<Array<u64>>, n: u64, k: u64) -> Rc<Array<bool>> {
  let v4 = {
    move |_v5: u64, v6: Rc<Array<bool>>| -> bool {
      std::mem::drop(v6);
      true
    }
  };
  let v11: Rc<dyn Fn(u64, Rc<Array<bool>>) -> bool> = Rc::new(v4);
  let v12: Rc<dyn Fn(u64, Rc<Array<bool>>) -> bool> = v11;
  let v15 = {
    move |t: u64, C: Rc<Array<bool>>| -> Rc<Array<bool>> {
      let fc = &fc;
      let v22 = a::get::<u64>(&fc, t);
      a::set::<bool>(C, v22, true)
    }
  };
  let v34: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new(v15);
  let v44 = a::make::<bool>(n, false);
  loop_::<Rc<Array<bool>>>(k, v12, v34, 0u64, v44)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.rat1
pub fn rat1(f: f64) -> (Rc<BigInt>, Rc<BigInt>) {
  let v4 = dec(f);
  match v4 {
    (v6, v8) => {
      let e = &v6;
      let m = &v8;
      let v14 = b::zero();
      let v17 = Rc::clone(m);
      match leb_owned(v14, v17) {
        true => {
          let v25 = shiftl(v6, v8);
          let v27 = b::one();
          let v29 = b::identity(v27);
          (v25, v29)
        },
        false => {
          let v40 = b::one();
          let v42 = b::identity(v40);
          let v46 = opp(v8);
          let den = shiftl(v42, v46);
          let v54 = 64u64;
          let v55 = {
            move |_v56: u64, st: ((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool)| -> bool {
              negb(snd::<(((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool>(st))
            }
          };
          let v68: Rc<dyn Fn(u64, ((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool)) -> bool> = Rc::new(v55);
          let v69: Rc<dyn Fn(u64, ((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool)) -> bool> = v68;
          let v72 = Rc::clone(&den);
          let v74 = Rc::clone(e);
          let v75 = {
            move |_v80: u64, st: ((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool)| -> ((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool) {
              let den = &v72;
              let e = &v74;
              let v84 = Clone::clone(&st);
              let v86 = fst::<(((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool>(v84);
              match v86 {
                (v88, v90) => {
                  match v88 {
                    (v93, v95) => {
                      let y0 = &v95;
                      match v93 {
                        (v99, v101) => {
                          match v99 {
                            (v104, v106) => {
                              let y2 = &v106;
                              match v104 {
                                (v110, v112) => {
                                  let ad = &v110;
                                  let an = &v112;
                                  let q = div(ad, an);
                                  let v124 = Rc::clone(&q);
                                  let v126 = Rc::clone(y2);
                                  let v128 = mul_2(v124, v126);
                                  let h = add_1(v128, v101);
                                  let v137 = Rc::clone(&q);
                                  let v139 = Rc::clone(y0);
                                  let v141 = mul_2(v137, v139);
                                  let k = add_1(v141, v90);
                                  let v148 = b::one();
                                  let v151 = b::twice(v148);
                                  let v154 = b::twice(v151);
                                  let v157 = b::twice(v154);
                                  let v160 = b::twice(v157);
                                  let v163 = b::twice(v160);
                                  let v166 = b::twice(v163);
                                  let v169 = b::twice(v166);
                                  let v172 = b::twice(v169);
                                  let v175 = b::twice(v172);
                                  let v178 = b::twice(v175);
                                  let v181 = b::twice(v178);
                                  let v184 = b::twice(v181);
                                  let v187 = b::twice(v184);
                                  let v190 = b::twice(v187);
                                  let v193 = b::twice(v190);
                                  let v196 = b::twice(v193);
                                  let v199 = b::twice(v196);
                                  let v202 = b::twice(v199);
                                  let v205 = b::twice(v202);
                                  let v208 = b::twice(v205);
                                  let v211 = b::twice(v208);
                                  let v214 = b::twice(v211);
                                  let v217 = b::twice(v214);
                                  let v220 = b::twice(v217);
                                  let v223 = b::twice(v220);
                                  let v226 = b::twice(v223);
                                  let v229 = b::twice(v226);
                                  let v232 = b::twice(v229);
                                  let v235 = b::twice(v232);
                                  let v238 = b::twice(v235);
                                  let v241 = b::identity(v238);
                                  let v245 = Rc::clone(&k);
                                  match ltb_2(v241, v245) {
                                    true => {
                                      std::mem::drop(k);
                                      std::mem::drop(h);
                                      std::mem::drop(q);
                                      std::mem::drop(v106);
                                      std::mem::drop(v95);
                                      std::mem::drop(v112);
                                      std::mem::drop(v110);
                                      (fst::<(((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool>(st), true)
                                    },
                                    false => {
                                      std::mem::drop(st);
                                      let v267 = Rc::clone(an);
                                      let v268 = mul_2(q, v267);
                                      let rem = sub(v110, v268);
                                      let v280 = Rc::clone(e);
                                      let v283 = Rc::clone(&k);
                                      let v284 = mul_2(v280, v283);
                                      let v288 = Rc::clone(&h);
                                      let v290 = Rc::clone(den);
                                      let v291 = mul_2(v288, v290);
                                      let v297 = sub(v284, v291);
                                      let v299 = abs_owned(v297);
                                      let v301 = b::one();
                                      let v304 = b::twice(v301);
                                      let v307 = b::twice_plus_one(v304);
                                      let v310 = b::twice(v307);
                                      let v313 = b::twice(v310);
                                      let v316 = b::twice(v313);
                                      let v318 = b::identity(v316);
                                      let v323 = shiftl(v299, v318);
                                      let v328 = abs(e);
                                      let v332 = Rc::clone(&k);
                                      let v333 = mul_2(v328, v332);
                                      let close = leb_owned(v323, v333);
                                      let v343 = Rc::clone(&rem);
                                      let v368 = (((((v112, v343), h), v106), k), v95);
                                      let v372 = b::zero();
                                      (v368, orb(eqb_2(rem, v372), close))
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
          };
          let v409: Rc<dyn Fn(u64, ((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool)) -> ((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool)> = Rc::new(v75);
          let v417 = (v6, den);
          let v420 = b::one();
          let v422 = b::identity(v420);
          let v427 = (v417, v422);
          let v429 = b::zero();
          let v434 = (v427, v429);
          let v436 = b::zero();
          let v441 = (v434, v436);
          let v444 = b::one();
          let v446 = b::identity(v444);
          let st = loop_::<((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool)>(v54, v69, v409, 0u64, ((v441, v446), false));
          let v475 = fst::<(((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool>(st);
          match v475 {
            (v477, v479) => {
              match v477 {
                (v482, v484) => {
                  let p0 = &v484;
                  match v482 {
                    (v488, v490) => {
                      match v488 {
                        (v493, v495) => {
                          match v493 {
                            (v498, v500) => {
                              let v504 = b::zero();
                              let v507 = Rc::clone(p0);
                              match ltb_2(v504, v507) {
                                true => {
                                  std::mem::drop(v498);
                                  std::mem::drop(v500);
                                  std::mem::drop(v490);
                                  std::mem::drop(v479);
                                  (v495, v484)
                                },
                                false => {
                                  std::mem::drop(v498);
                                  std::mem::drop(v500);
                                  std::mem::drop(v490);
                                  std::mem::drop(v479);
                                  std::mem::drop(v495);
                                  std::mem::drop(v484);
                                  let v518 = b::zero();
                                  let v520 = b::one();
                                  let v522 = b::identity(v520);
                                  (v518, v522)
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

// Rocq: EquationsolverExact.equationsolver_exact_implem.ratvec
// Variant: uncurried
pub fn ratvec(x: Rc<Array<f64>>, n: u64) -> (Rc<Array<Rc<BigInt>>>, Rc<BigInt>) {
  let v3 = {
    move |_v4: u64, v5: ((Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>), Rc<BigInt>)| -> bool {
      std::mem::drop(v5);
      true
    }
  };
  let v10: Rc<dyn Fn(u64, ((Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>), Rc<BigInt>)) -> bool> = Rc::new(v3);
  let v11: Rc<dyn Fn(u64, ((Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>), Rc<BigInt>)) -> bool> = v10;
  let v14 = {
    move |j: u64, st: ((Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>), Rc<BigInt>)| -> ((Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>), Rc<BigInt>) {
      let x = &x;
      match st {
        (v20, v22) => {
          let y = &v22;
          match v20 {
            (v26, v28) => {
              let v34 = a::get::<f64>(&x, j);
              let v36 = rat1(v34);
              match v36 {
                (v38, v40) => {
                  let h = &v40;
                  let v49 = a::set::<Rc<BigInt>>(v26, j, v38);
                  let v55 = Rc::clone(h);
                  let v56 = a::set::<Rc<BigInt>>(v28, j, v55);
                  let v62 = (v49, v56);
                  let v68 = zgcd(y, h);
                  let v74 = div_owned(v22, v68);
                  let v78 = mul_2(v74, v40);
                  (v62, v78)
                },
              }
            },
          }
        },
      }
    }
  };
  let v96: Rc<dyn Fn(u64, ((Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>), Rc<BigInt>)) -> ((Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>), Rc<BigInt>)> = Rc::new(v14);
  let v100 = b::zero();
  let v105 = a::make::<Rc<BigInt>>(n, v100);
  let v107 = b::one();
  let v109 = b::identity(v107);
  let v114 = a::make::<Rc<BigInt>>(n, v109);
  let v119 = (v105, v114);
  let v122 = b::one();
  let v124 = b::identity(v122);
  let v141 = loop_::<((Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>), Rc<BigInt>)>(n, v11, v96, 0u64, (v119, v124));
  match v141 {
    (v143, v145) => {
      let p = &v145;
      match v143 {
        (v149, v151) => {
          let v154 = {
            move |_v155: u64, v156: Rc<Array<Rc<BigInt>>>| -> bool {
              std::mem::drop(v156);
              true
            }
          };
          let v161: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = Rc::new(v154);
          let v162: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = v161;
          let v168 = Rc::clone(p);
          let v169 = {
            move |j: u64, P: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
              let K = &v149;
              let H = &v151;
              let p = &v168;
              let v181 = a::get::<Rc<BigInt>>(&K, j);
              let v185 = a::get::<Rc<BigInt>>(&H, j);
              let v187 = Rc::clone(p);
              let v190 = div_owned(v187, v185);
              let v195 = mul_2(v181, v190);
              a::set::<Rc<BigInt>>(P, j, v195)
            }
          };
          let v205: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new(v169);
          let v209 = b::zero();
          let v214 = a::make::<Rc<BigInt>>(n, v209);
          let v226 = loop_::<Rc<Array<Rc<BigInt>>>>(n, v162, v205, 0u64, v214);
          (v226, v145)
        },
      }
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.get_row
// Variant: borrowed, uncurried
pub fn get_row(Q: &Rc<Array<f64>>, n: u64, i: u64) -> Rc<Array<f64>> {
  let v6 = {
    move |_v7: u64, v8: Rc<Array<f64>>| -> bool {
      std::mem::drop(v8);
      true
    }
  };
  let v13: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(v6);
  let v14: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = v13;
  let v21 = Rc::clone(Q);
  let v22 = {
    let __anf_capture_25 = n;
    move |k: u64, x: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let i = &i;
      let n = &__anf_capture_25;
      let Q = &v21;
      let v43 = add(mul(Clone::clone(i), Clone::clone(n)), k);
      let v45 = a::get::<f64>(&Q, v43);
      a::set::<f64>(x, k, v45)
    }
  };
  let v55: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new(v22);
  let v64 = a::make::<f64>(n, __rocq_global_371);
  loop_::<Rc<Array<f64>>>(n, v14, v55, 0u64, v64)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.yv
// Variant: borrowed, uncurried
pub fn yv(Q: &Rc<Array<f64>>, n: u64, r: u64, t: u64) -> Rc<Array<Rc<BigInt>>> {
  let n_1 = n;
  let r_1 = r;
  let t_1 = t;
  let v23 = get_row(Q, n_1, add(r_1, t_1));
  fst::<Rc<Array<Rc<BigInt>>>, Rc<BigInt>>(ratvec(v23, n_1))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.allf
// Variant: uncurried
pub fn allf(len: u64, p: Rc<dyn Fn(u64) -> bool>) -> bool {
  let v3 = {
    move |_v4: u64, _v5: bool| -> bool {
      true
    }
  };
  let v10: Rc<dyn Fn(u64, bool) -> bool> = Rc::new(v3);
  let v11: Rc<dyn Fn(u64, bool) -> bool> = v10;
  let v14 = {
    move |k: u64, b_1: bool| -> bool {
      let p = &p;
      let v22 = p(k);
      andb(b_1, v22)
    }
  };
  let v30: Rc<dyn Fn(u64, bool) -> bool> = Rc::new(v14);
  loop_::<bool>(len, v11, v30, 0u64, true)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dzero
pub fn dzero(x: (Rc<BigInt>, Rc<BigInt>)) -> bool {
  let v5 = fst::<Rc<BigInt>, Rc<BigInt>>(x);
  let v6 = b::zero();
  eqb_2(v5, v6)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.zdot
// Variant: uncurried
pub fn zdot_owned(X: Rc<Array<f64>>, o: u64, Y: Rc<Array<Rc<BigInt>>>, len: u64) -> (Rc<BigInt>, Rc<BigInt>) {
  let v11 = {
    move |k: u64| -> (Rc<BigInt>, Rc<BigInt>) {
      let o = &o;
      let X = &X;
      let Y = &Y;
      let v27 = add(Clone::clone(o), k);
      let v32 = dec(a::get::<f64>(&X, v27));
      let v37 = a::get::<Rc<BigInt>>(&Y, k);
      dmul(v32, dint_owned(v37))
    }
  };
  let v47: Rc<dyn Fn(u64) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new(v11);
  dsumf(len, v47)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.zdot
// Variant: borrowed, uncurried
pub fn zdot(X: &Rc<Array<f64>>, o: u64, Y: &Rc<Array<Rc<BigInt>>>, len: u64) -> (Rc<BigInt>, Rc<BigInt>) {
  let len_1 = len;
  let v11 = Rc::clone(X);
  let v14 = Rc::clone(Y);
  let v15 = {
    move |k: u64| -> (Rc<BigInt>, Rc<BigInt>) {
      let o = &o;
      let X = &v11;
      let Y = &v14;
      let v31 = add(Clone::clone(o), k);
      let v36 = dec(a::get::<f64>(&X, v31));
      let v41 = a::get::<Rc<BigInt>>(&Y, k);
      dmul(v36, dint_owned(v41))
    }
  };
  let v51: Rc<dyn Fn(u64) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new(v15);
  dsumf(len_1, v51)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.chk_incons
// Variant: uncurried
pub fn chk_incons(AT: Rc<Array<f64>>, xb: Rc<Array<f64>>, n: u64, y: Rc<Array<Rc<BigInt>>>) -> bool {
  let v10 = Rc::clone(&y);
  let v13 = {
    let __anf_capture_18 = n;
    move |j: u64| -> bool {
      let AT = &AT;
      let y = &v10;
      let n = &__anf_capture_18;
      let v35 = zdot(AT, mul(j, Clone::clone(n)), y, Clone::clone(n));
      dzero(v35)
    }
  };
  let v41: Rc<dyn Fn(u64) -> bool> = Rc::new(v13);
  andb(allf(n, v41), negb(dzero(zdot_owned(xb, 0u64, y, n))))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.chk_red
// Variant: uncurried
pub fn chk_red(AT: Rc<Array<f64>>, xb: Rc<Array<f64>>, n: u64, y: Rc<Array<Rc<BigInt>>>, d: u64, Df: Rc<Array<bool>>) -> bool {
  let v13 = Rc::clone(&y);
  let v16 = {
    let __anf_capture_21 = n;
    move |j: u64| -> bool {
      let AT = &AT;
      let y = &v13;
      let n = &__anf_capture_21;
      let v38 = zdot(AT, mul(j, Clone::clone(n)), y, Clone::clone(n));
      dzero(v38)
    }
  };
  let v44: Rc<dyn Fn(u64) -> bool> = Rc::new(v16);
  let v50 = allf(n, v44);
  let v61 = Rc::clone(&y);
  let v72 = andb(v50, dzero(zdot_owned(xb, 0u64, v61, n)));
  let v76 = &y;
  let v79 = a::get::<Rc<BigInt>>(&v76, d);
  let v80 = b::zero();
  let v88 = negb(eqb_2(v79, v80));
  let v96 = {
    let __anf_capture_99 = d;
    let __anf_capture_101 = y;
    move |i: u64| -> bool {
      let Df = &Df;
      let d = &__anf_capture_99;
      let y = &__anf_capture_101;
      let v111 = negb(a::get::<bool>(&Df, i));
      let v118 = eqb(i, Clone::clone(d));
      let v122 = a::get::<Rc<BigInt>>(&y, i);
      let v123 = b::zero();
      let v133 = orb(v118, eqb_2(v122, v123));
      orb(v111, v133)
    }
  };
  let v141: Rc<dyn Fn(u64) -> bool> = Rc::new(v96);
  let v152 = andb(v88, allf(n, v141));
  andb(v72, v152)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.scan_null
// Variant: uncurried
pub fn scan_null(AT: Rc<Array<f64>>, xb: Rc<Array<f64>>, Q: Rc<Array<f64>>, perm: Rc<Array<u64>>, fc: Rc<Array<u64>>, Df: Rc<Array<bool>>, n: u64, r: u64, k: u64) -> (bool, bool) {
  let v10 = {
    move |_v11: u64, v12: (bool, bool)| -> bool {
      std::mem::drop(v12);
      true
    }
  };
  let v17: Rc<dyn Fn(u64, (bool, bool)) -> bool> = Rc::new(v10);
  let v18: Rc<dyn Fn(u64, (bool, bool)) -> bool> = v17;
  let v35 = {
    let __anf_capture_38 = r;
    let __anf_capture_48 = n;
    move |t: u64, s: (bool, bool)| -> (bool, bool) {
      let Q = &Q;
      let r = &__anf_capture_38;
      let perm = &perm;
      let fc = &fc;
      let AT = &AT;
      let xb = &xb;
      let n = &__anf_capture_48;
      let Df = &Df;
      let y = yv(Q, Clone::clone(n), Clone::clone(r), t);
      let v69 = add(Clone::clone(r), t);
      let d = a::get::<u64>(&perm, v69);
      let v75 = Clone::clone(&s);
      let v77 = fst::<bool, bool>(v75);
      let v80 = Rc::clone(AT);
      let v82 = Rc::clone(xb);
      let v84 = Clone::clone(n);
      let v87 = Rc::clone(&y);
      let v93 = orb(v77, chk_incons(v80, v82, v84, v87));
      let v98 = snd::<bool, bool>(s);
      let v120 = andb(ltb(d, Clone::clone(n)), ltb(a::get::<u64>(&fc, t), Clone::clone(n)));
      let v123 = Rc::clone(AT);
      let v125 = Rc::clone(xb);
      let v127 = Clone::clone(n);
      let v133 = Rc::clone(Df);
      let v139 = andb(v120, chk_red(v123, v125, v127, y, d, v133));
      (v93, andb(v98, v139))
    }
  };
  let v153: Rc<dyn Fn(u64, (bool, bool)) -> (bool, bool)> = Rc::new(v35);
  loop_::<(bool, bool)>(k, v18, v153, 0u64, (false, ltb(r, n)))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.bentry
// Variant: borrowed, uncurried
pub fn bentry(xa: &Rc<Array<Rc<Array<f64>>>>, Df: &Rc<Array<bool>>, tix: &Rc<Array<u64>>, fc: &Rc<Array<u64>>, Cf: &Rc<Array<bool>>, i: u64, j: u64) -> f64 {
  let i_1 = i;
  let j_1 = j;
  let v9 = Df;
  match a::get::<bool>(&v9, i_1) {
    true => {
      let v15 = tix;
      let v18 = a::get::<u64>(&v15, i_1);
      let v19 = fc;
      let v22 = a::get::<u64>(&v19, v18);
      match eqb(j_1, v22) {
        true => {
          __rocq_global_820
        },
        false => {
          __rocq_global_371
        },
      }
    },
    false => {
      let v38 = Cf;
      match a::get::<bool>(&v38, j_1) {
        true => {
          __rocq_global_371
        },
        false => {
          let v48 = Rc::clone(xa);
          let v52 = a::get::<Rc<Array<f64>>>(&v48, i_1);
          std::mem::drop(v48);
          let v53 = &v52;
          let v56 = a::get::<f64>(&v53, j_1);
          std::mem::drop(v52);
          v56
        },
      }
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.padB
// Variant: uncurried
pub fn padB(xa: Rc<Array<Rc<Array<f64>>>>, n: u64, Df: Rc<Array<bool>>, tix: Rc<Array<u64>>, fc: Rc<Array<u64>>, Cf: Rc<Array<bool>>) -> Rc<Array<Rc<Array<f64>>>> {
  let v14 = a::make::<f64>(0u64, __rocq_global_371);
  let v27 = {
    let __anf_capture_38 = n;
    move |i: u64| -> Rc<Array<f64>> {
      let xa = &xa;
      let Df = &Df;
      let tix = &tix;
      let fc = &fc;
      let Cf = &Cf;
      let n = &__anf_capture_38;
      let v42 = __rocq_global_371;
      let v44 = Rc::clone(xa);
      let v46 = Rc::clone(Df);
      let v48 = Rc::clone(tix);
      let v50 = Rc::clone(fc);
      let v52 = Rc::clone(Cf);
      let v55 = {
        move |j: u64| -> f64 {
          let xa = &v44;
          let Df = &v46;
          let tix = &v48;
          let fc = &v50;
          let Cf = &v52;
          let v70 = Clone::clone(&i);
          bentry(xa, Df, tix, fc, Cf, v70, j)
        }
      };
      let v82: Rc<dyn Fn(u64) -> f64> = Rc::new(v55);
      let v85 = Clone::clone(n);
      tab::<f64>(v85, v42, v82)
    }
  };
  let v93: Rc<dyn Fn(u64) -> Rc<Array<f64>>> = Rc::new(v27);
  tab::<Rc<Array<f64>>>(n, v14, v93)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.certify_inj
// Variant: uncurried
pub fn certify_inj(n: u64, xa: Rc<Array<Rc<Array<f64>>>>, AT: Rc<Array<f64>>, Q: Rc<Array<f64>>) -> bool {
  let nz = i2z(n);
  let v10 = b::one();
  let v13 = b::twice_plus_one(v10);
  let v16 = b::identity(v13);
  let v20 = Rc::clone(&nz);
  let v21 = mul_2(v16, v20);
  let v23 = b::one();
  let v26 = b::twice_plus_one(v23);
  let v29 = b::twice(v26);
  let v32 = b::twice_plus_one(v29);
  let v35 = b::twice(v32);
  let v38 = b::twice_plus_one(v35);
  let v40 = b::neg(v38);
  let lamd = (v21, v40);
  let v50 = b::one();
  let v53 = b::twice_plus_one(v50);
  let v56 = b::identity(v53);
  let v60 = Rc::clone(&nz);
  let v62 = mul_2(v56, v60);
  let v66 = mul_2(v62, nz);
  let v68 = b::one();
  let v71 = b::twice(v68);
  let v74 = b::twice(v71);
  let v77 = b::twice(v74);
  let v80 = b::twice(v77);
  let v83 = b::twice_plus_one(v80);
  let v86 = b::twice_plus_one(v83);
  let v89 = b::twice(v86);
  let v92 = b::twice(v89);
  let v95 = b::twice_plus_one(v92);
  let v98 = b::twice_plus_one(v95);
  let v100 = b::neg(v98);
  let mud2 = (v66, v100);
  let S = rowabs(xa, n);
  let v126 = {
    let __anf_capture_127 = n;
    move |v139: u64| -> ((Rc<BigInt>, Rc<BigInt>), bool) {
      let n = &__anf_capture_127;
      let Q = &Q;
      let AT = &AT;
      let S = &S;
      let v152 = erow(Clone::clone(n), Q, AT, S, Clone::clone(&lamd), Clone::clone(&mud2), v139);
      v152
    }
  };
  let v155: Rc<dyn Fn(u64) -> ((Rc<BigInt>, Rc<BigInt>), bool)> = Rc::new(v126);
  let v161 = maxb(n, v155);
  match v161 {
    (v163, v165) => {
      andb(v165, dltb(v163, d1(())))
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.padded_ok
// Variant: uncurried
pub fn padded_ok(xa: Rc<Array<Rc<Array<f64>>>>, n: u64, Df: Rc<Array<bool>>, tix: Rc<Array<u64>>, fc: Rc<Array<u64>>, Cf: Rc<Array<bool>>) -> bool {
  let B = padB(xa, n, Df, tix, fc, Cf);
  let w = add(n, 1u64);
  let v32 = Rc::clone(&B);
  let v35 = col_thr(v32, n);
  let v42 = a::make::<f64>(n, __rocq_global_371);
  let v45 = Rc::clone(&B);
  let v52 = init_M(v45, v42, n, w);
  let v56 = init_Q(n);
  let st = forward(n, w, v35, v52, v56);
  let v73 = fs_r(&st);
  match eqb(v73, n) {
    true => {
      let v83 = Rc::clone(&B);
      let v86 = transpose(v83, n);
      let v92 = Rc::clone(&st);
      let v93 = fs_M_owned(v92);
      let v97 = fs_Q(st);
      let v109 = snd::<Rc<Array<f64>>, Rc<Array<f64>>>(backsub(n, w, v93, v97));
      certify_inj(n, B, v86, v109)
    },
    false => {
      std::mem::drop(B);
      std::mem::drop(st);
      false
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.free_col
// Variant: uncurried
pub fn free_col(pc: Rc<Array<u64>>, n: u64, r: u64) -> u64 {
  let v4 = {
    move |_v5: u64, v6: Rc<Array<bool>>| -> bool {
      std::mem::drop(v6);
      true
    }
  };
  let v11: Rc<dyn Fn(u64, Rc<Array<bool>>) -> bool> = Rc::new(v4);
  let v12: Rc<dyn Fn(u64, Rc<Array<bool>>) -> bool> = v11;
  let v15 = {
    move |t: u64, isp: Rc<Array<bool>>| -> Rc<Array<bool>> {
      let pc = &pc;
      let v22 = a::get::<u64>(&pc, t);
      a::set::<bool>(isp, v22, true)
    }
  };
  let v34: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new(v15);
  let v44 = a::make::<bool>(n, false);
  let isp = loop_::<Rc<Array<bool>>>(r, v12, v34, 0u64, v44);
  let v57 = {
    move |_v58: u64, _v59: u64| -> bool {
      true
    }
  };
  let v64: Rc<dyn Fn(u64, u64) -> bool> = Rc::new(v57);
  let v65: Rc<dyn Fn(u64, u64) -> bool> = v64;
  let v70 = {
    let __anf_capture_71 = n;
    move |c: u64, f: u64| -> u64 {
      let n = &__anf_capture_71;
      let isp = &isp;
      let v83 = eqb(f, Clone::clone(n));
      let v90 = negb(a::get::<bool>(&isp, c));
      match andb(v83, v90) {
        true => {
          c
        },
        false => {
          f
        },
      }
    }
  };
  let v104: Rc<dyn Fn(u64, u64) -> u64> = Rc::new(v70);
  loop_::<u64>(n, v65, v104, 0u64, n)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.echelon_solve
// Variant: uncurried
pub fn echelon_solve(M: Rc<Array<f64>>, pc: Rc<Array<u64>>, n: u64, w: u64, r: u64, homog: bool, x: Rc<Array<f64>>) -> Rc<Array<f64>> {
  let v8 = {
    move |_v9: u64, v10: Rc<Array<f64>>| -> bool {
      std::mem::drop(v10);
      true
    }
  };
  let v15: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(v8);
  let v16: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = v15;
  let v29 = {
    let __anf_capture_30 = r;
    move |s: u64, x: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let r = &__anf_capture_30;
      let pc = &pc;
      let homog = &homog;
      let n = &n;
      let w = &w;
      let M = &M;
      let v47 = 1u64;
      let v53 = sub_2(Clone::clone(r), v47);
      let t = sub_2(v53, s);
      let c = a::get::<u64>(&pc, t);
      let s0 = match homog {
        true => {
          __rocq_global_371
        },
        false => {
          let v77 = add(mul(t, Clone::clone(w)), Clone::clone(n));
          a::get::<f64>(&M, v77)
        },
      };
      let v84 = {
        move |_v85: u64, _v86: f64| -> bool {
          true
        }
      };
      let v91: Rc<dyn Fn(u64, f64) -> bool> = Rc::new(v84);
      let v92: Rc<dyn Fn(u64, f64) -> bool> = v91;
      let v96 = Clone::clone(w);
      let v98 = Rc::clone(M);
      let v101 = Rc::clone(&x);
      let v102 = {
        let __anf_capture_103 = t;
        move |j: u64, acc: f64| -> f64 {
          let t = &__anf_capture_103;
          let w = &v96;
          let M = &v98;
          let x = &v101;
          let v127 = add(mul(Clone::clone(t), Clone::clone(w)), j);
          let v129 = a::get::<f64>(&M, v127);
          let v132 = a::get::<f64>(&x, j);
          sub_1(acc, mul_1(v129, v132))
        }
      };
      let v145: Rc<dyn Fn(u64, f64) -> f64> = Rc::new(v102);
      let v154 = add(c, 1u64);
      let acc = loop_::<f64>(Clone::clone(n), v92, v145, v154, s0);
      let v179 = add(mul(t, Clone::clone(w)), c);
      let v181 = a::get::<f64>(&M, v179);
      a::set::<f64>(x, c, div_1(acc, v181))
    }
  };
  let v196: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new(v29);
  loop_::<Rc<Array<f64>>>(r, v16, v196, 0u64, x)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.chk_mult
// Variant: uncurried
pub fn chk_mult(xa: Rc<Array<Rc<Array<f64>>>>, xb: Rc<Array<f64>>, n: u64, p: Rc<Array<Rc<BigInt>>>, q: Rc<BigInt>, v: Rc<Array<Rc<BigInt>>>) -> bool {
  let v10 = b::zero();
  let v13 = Rc::clone(&q);
  let v19 = negb(eqb_2(v13, v10));
  let v24 = Rc::clone(&v);
  let v25 = {
    move |j: u64| -> bool {
      let v = &v24;
      let v32 = a::get::<Rc<BigInt>>(&v, j);
      let v33 = b::zero();
      eqb_2(v32, v33)
    }
  };
  let v41: Rc<dyn Fn(u64) -> bool> = Rc::new(v25);
  let v55 = andb(v19, negb(allf(n, v41)));
  let v69 = {
    let __anf_capture_74 = q;
    let __anf_capture_78 = v;
    let __anf_capture_80 = n;
    move |i: u64| -> bool {
      let xa = &xa;
      let p = &p;
      let q = &__anf_capture_74;
      let xb = &xb;
      let v = &__anf_capture_78;
      let n = &__anf_capture_80;
      let v84 = Rc::clone(xa);
      let row = a::get::<Rc<Array<f64>>>(&v84, i);
      std::mem::drop(v84);
      let v97 = Rc::clone(&row);
      let v101 = Rc::clone(p);
      let v128 = dzero(dsub(zdot_owned(v97, 0u64, v101, Clone::clone(n)), dmul(dint(q), dec(a::get::<f64>(&xb, i)))));
      let v138 = Rc::clone(v);
      let v140 = Clone::clone(n);
      andb(v128, dzero(zdot_owned(row, 0u64, v138, v140)))
    }
  };
  let v152: Rc<dyn Fn(u64) -> bool> = Rc::new(v69);
  andb(v55, allf(n, v152))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.solve
// Variant: uncurried
pub fn solve(n: u64, xa: Rc<Array<Rc<Array<f64>>>>, xb: Rc<Array<f64>>) -> Rc<outcome<Rc<Array<f64>>>> {
  let w = add(n, 1u64);
  let v15 = Rc::clone(&xa);
  let v18 = col_thr(v15, n);
  let v22 = Rc::clone(&xa);
  let v25 = Rc::clone(&xb);
  let v30 = init_M(v22, v25, n, w);
  let v34 = init_Q(n);
  let st = forward(n, w, v18, v30, v34);
  let v49 = Rc::clone(&xa);
  let AT = transpose(v49, n);
  let v57 = Rc::clone(&st);
  let v59 = fs_r_owned(v57);
  match eqb(v59, n) {
    true => {
      let v69 = Rc::clone(&st);
      let v70 = fs_M_owned(v69);
      let v74 = fs_Q(st);
      let v83 = backsub(n, w, v70, v74);
      match v83 {
        (v85, v87) => {
          let xt = get_col(v85, n, w, n);
          let v104 = Rc::clone(&xa);
          let v107 = Rc::clone(&xb);
          let v114 = Rc::clone(&xt);
          match certify(n, v104, v107, AT, v87, v114) {
            true => {
              std::mem::drop(xb);
              std::mem::drop(xa);
              Rc::new(outcome::<Rc<Array<f64>>>::Unique(xt))
            },
            false => {
              std::mem::drop(xt);
              solve_exact(n, xa, xb)
            },
          }
        },
      }
    },
    false => {
      let v143 = Rc::clone(&st);
      let M = fs_M_owned(v143);
      let v148 = Rc::clone(&st);
      let r = fs_r_owned(v148);
      let k = match ltb(r, n) {
        true => {
          sub_2(n, r)
        },
        false => {
          0u64
        },
      };
      let v174 = Rc::clone(&st);
      let v176 = fs_pc(v174);
      let fc = free_cols(v176, n, r);
      let v187 = Rc::clone(&st);
      let v189 = fs_perm(v187);
      let mD = mark_D(v189, n, r, k);
      let v200 = Clone::clone(&mD);
      let Df = fst::<Rc<Array<bool>>, Rc<Array<u64>>>(v200);
      let tix = snd::<Rc<Array<bool>>, Rc<Array<u64>>>(mD);
      let v210 = Rc::clone(&fc);
      let Cf = mark_C(v210, n, k);
      let v220 = Rc::clone(&st);
      let v221 = fs_Q(v220);
      let v225 = Rc::clone(&st);
      let v226 = fs_perm(v225);
      let v231 = Rc::clone(&xb);
      let v238 = Rc::clone(&fc);
      let v241 = Rc::clone(&Df);
      let sc = scan_null(AT, v231, v221, v226, v238, v241, n, r, k);
      let v251 = Clone::clone(&sc);
      match fst::<bool, bool>(v251) {
        true => {
          std::mem::drop(sc);
          std::mem::drop(Cf);
          std::mem::drop(tix);
          std::mem::drop(Df);
          std::mem::drop(fc);
          std::mem::drop(M);
          std::mem::drop(xa);
          std::mem::drop(xb);
          std::mem::drop(st);
          Rc::new(outcome::<Rc<Array<f64>>>::Inconsistent)
        },
        false => {
          let v264 = match snd::<bool, bool>(sc) {
            true => {
              let v268 = Rc::clone(&xa);
              padded_ok(v268, n, Df, tix, fc, Cf)
            },
            false => {
              std::mem::drop(Cf);
              std::mem::drop(fc);
              std::mem::drop(tix);
              std::mem::drop(Df);
              false
            },
          };
          match &v264 {
            true => {
              std::mem::drop(M);
              std::mem::drop(xa);
              std::mem::drop(xb);
              std::mem::drop(st);
              Rc::new(outcome::<Rc<Array<f64>>>::Multiple)
            },
            false => {
              let v298 = Rc::clone(&st);
              let v300 = fs_pc(v298);
              let f = free_col(v300, n, r);
              let v311 = Rc::clone(&st);
              let v312 = fs_pc(v311);
              let v320 = a::make::<f64>(n, __rocq_global_371);
              let v323 = Rc::clone(&M);
              let x0 = echelon_solve(v323, v312, n, w, r, false, v320);
              let v341 = fs_pc(st);
              let v349 = a::make::<f64>(n, __rocq_global_371);
              let v357 = a::set::<f64>(v349, f, __rocq_global_820);
              let v = echelon_solve(M, v341, n, w, r, true, v357);
              let v378 = ratvec(x0, n);
              match v378 {
                (v380, v382) => {
                  let v394 = fst::<Rc<Array<Rc<BigInt>>>, Rc<BigInt>>(ratvec(v, n));
                  let v397 = Rc::clone(&xa);
                  let v400 = Rc::clone(&xb);
                  match chk_mult(v397, v400, n, v380, v382, v394) {
                    true => {
                      std::mem::drop(xa);
                      std::mem::drop(xb);
                      Rc::new(outcome::<Rc<Array<f64>>>::Multiple)
                    },
                    false => {
                      solve_exact(n, xa, xb)
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<Rc<Array<f64>>>>, Rc<Array<f64>>) -> Rc<outcome<Rc<Array<f64>>>>> {
  let v0: fn(u64, Rc<Array<Rc<Array<f64>>>>, Rc<Array<f64>>) -> Rc<outcome<Rc<Array<f64>>>> = solve;
  let v1: Rc<dyn Fn(u64, Rc<Array<Rc<Array<f64>>>>, Rc<Array<f64>>) -> Rc<outcome<Rc<Array<f64>>>>> = Rc::new(v0);
  v1
}
const __rocq_global_371: f64 = f64::from_bits(0u64);
const __rocq_global_722: f64 = f64::from_bits(4427038433705197568u64);
const __rocq_global_820: f64 = f64::from_bits(4607182418800017408u64);
const __rocq_global_1215: f64 = f64::from_bits(9218868437227405312u64);
const __rocq_global_3377: f64 = f64::from_bits(9223372036854775808u64);
const __rocq_global_3380: f64 = f64::from_bits(18442240474082181120u64);
const __rocq_global_3383: f64 = f64::from_bits(9221120237041090560u64);