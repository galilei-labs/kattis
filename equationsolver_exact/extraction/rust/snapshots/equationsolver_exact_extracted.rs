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
  b::succ(v0)
}

// Rocq: Corelib.BinNums.IntDef.Z.add
// Variant: uncurried
pub fn add_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  b::add(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.opp
pub fn opp(v0: Rc<BigInt>) -> Rc<BigInt> {
  b::neg(v0)
}

// Rocq: Corelib.BinNums.IntDef.Z.sub
// Variant: uncurried
pub fn sub(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  b::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z
pub fn to_Z(v0: u64) -> Rc<BigInt> {
  b::of_uint63(v0)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
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
  let tmp = ltb(i, hi);
  match bdec(tmp) {
    sumbool::left => {
      let cont_ref: &Rc<dyn Fn(u64, St) -> bool> = &cont;
      let s_clone = Clone::clone(&s);
      let tmp_1 = cont_ref(i, s_clone);
      if tmp_1 {
        let tmp_2 = add(i, 1u64);
        let f_ref: &Rc<dyn Fn(u64, St) -> St> = &f;
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

// Rocq: EquationsolverExact.equationsolver_exact_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop_1::<St>(hi, cont, f, i, s)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_r
pub fn fs_r_owned(f: Rc<fstate>) -> u64 {
  let f_fs_r_clone = Clone::clone(&f.fs_r);
  std::mem::drop(f);
  f_fs_r_clone
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_r
// Variant: borrowed
pub fn fs_r(f: &Rc<fstate>) -> u64 {
  let tmp = f;
  Clone::clone(&tmp.fs_r)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_M
pub fn fs_M_owned(f: Rc<fstate>) -> Rc<Array<f64>> {
  let f_fs_M_clone = Rc::clone(&f.fs_M);
  std::mem::drop(f);
  f_fs_M_clone
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_M
// Variant: borrowed
pub fn fs_M(f: &Rc<fstate>) -> Rc<Array<f64>> {
  let tmp = f;
  Rc::clone(&tmp.fs_M)
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
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Corelib.Floats.PrimFloat.leb
// Variant: uncurried
pub fn leb_1(v0: f64, v1: f64) -> bool {
  rocq_float64::leb(v0, v1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.swap_f
// Variant: uncurried
pub fn swap_f(T: Rc<Array<f64>>, w: u64, p: u64, r: u64) -> Rc<Array<f64>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(move |_v6: u64, v7: Rc<Array<f64>>| -> bool {
    std::mem::drop(v7);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new({
    let __anf_capture_25 = w;
    move |j: u64, T: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let r = &r;
      let p = &p;
      let w = &__anf_capture_25;
      let x = a::get::<f64>(&T, add(mul(Clone::clone(r), Clone::clone(w)), j));
      let y = a::get::<f64>(&T, add(mul(Clone::clone(p), Clone::clone(w)), j));
      let tmp = a::set::<f64>(T, add(mul(Clone::clone(r), Clone::clone(w)), j), y);
      let p_clone = Clone::clone(p);
      let w_clone = Clone::clone(w);
      a::set::<f64>(tmp, add(mul(p_clone, w_clone), j), x)
    }
  });
  loop_::<Rc<Array<f64>>>(w, callback, callback_1, 0u64, T)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_Q
pub fn fs_Q(f: Rc<fstate>) -> Rc<Array<f64>> {
  let f_fs_Q_clone = Rc::clone(&f.fs_Q);
  std::mem::drop(f);
  f_fs_Q_clone
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
  let callback: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(move |_v8: u64, v9: Rc<Array<f64>>| -> bool {
    std::mem::drop(v9);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new({
    let __anf_capture_29 = w;
    move |j: u64, T: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let i = &i;
      let r = &r;
      let w = &__anf_capture_29;
      let f = &f;
      let tmp = add(mul(Clone::clone(i), Clone::clone(w)), j);
      let tmp_1 = a::get::<f64>(&T, add(mul(Clone::clone(i), Clone::clone(w)), j));
      let tmp_2 = a::get::<f64>(&T, add(mul(Clone::clone(r), Clone::clone(w)), j));
      let f_clone = Clone::clone(f);
      a::set::<f64>(T, tmp, sub_1(tmp_1, mul_1(f_clone, tmp_2)))
    }
  });
  loop_::<Rc<Array<f64>>>(w, callback, callback_1, lo, T)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_perm
pub fn fs_perm(f: Rc<fstate>) -> Rc<Array<u64>> {
  let f_fs_perm_clone = Rc::clone(&f.fs_perm);
  std::mem::drop(f);
  f_fs_perm_clone
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_pc
pub fn fs_pc(f: Rc<fstate>) -> Rc<Array<u64>> {
  let f_fs_pc_clone = Rc::clone(&f.fs_pc);
  std::mem::drop(f);
  f_fs_pc_clone
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fwd_col
// Variant: uncurried
pub fn fwd_col(n: u64, w: u64, thr: Rc<Array<f64>>, c: u64, st: Rc<fstate>) -> Rc<fstate> {
  let r = fs_r(&st);
  if ltb(r, n) {
    let M = fs_M(&st);
    let callback: Rc<dyn Fn(u64, (u64, f64)) -> bool> = Rc::new(move |_v22: u64, v23: (u64, f64)| -> bool {
      std::mem::drop(v23);
      true
    });
    let M_clone = Rc::clone(&M);
    let callback_1: Rc<dyn Fn(u64, (u64, f64)) -> (u64, f64)> = Rc::new({
      let __anf_capture_38 = w;
      let __anf_capture_40 = c;
      move |i: u64, pm: (u64, f64)| -> (u64, f64) {
        let w = &__anf_capture_38;
        let c = &__anf_capture_40;
        let M = &M_clone;
        let v = abs_1(a::get::<f64>(M, add(mul(i, Clone::clone(w)), Clone::clone(c))));
        let pm_clone = Clone::clone(&pm);
        let tmp = snd::<u64, f64>(pm_clone);
        if ltb_1(tmp, v) {
          std::mem::drop(pm);
          (i, v)
        } else {
          pm
        }
      }
    });
    let tmp_1 = (r, __rocq_global_371);
    let tmp_2 = loop_::<(u64, f64)>(n, callback, callback_1, r, tmp_1);
    match tmp_2 {
      (v111, v113) => {
        let tmp_3 = a::get::<f64>(&thr, c);
        if leb_1(v113, tmp_3) {
          std::mem::drop(M);
          std::mem::drop(thr);
          st
        } else {
          std::mem::drop(thr);
          let M_1 = swap_f(M, w, v111, r);
          let st_clone = Rc::clone(&st);
          let tmp_4 = fs_Q(st_clone);
          let Q = swap_f(tmp_4, n, v111, r);
          let piv = a::get::<f64>(&M_1, add(mul(r, w), c));
          let callback_2: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> bool> = Rc::new(move |_v171: u64, v172: (Rc<Array<f64>>, Rc<Array<f64>>)| -> bool {
            std::mem::drop(v172);
            true
          });
          let callback_3: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>)> = Rc::new({
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
                  let tmp_5 = a::get::<f64>(Q, add(mul(i, Clone::clone(w)), Clone::clone(c)));
                  let f = div_1(tmp_5, Clone::clone(piv));
                  let tmp_6 = 1u64;
                  let tmp_7 = add(Clone::clone(c), tmp_6);
                  let M = axpy_row(v203, Clone::clone(w), i, Clone::clone(r), tmp_7, f);
                  let tmp_8 = a::set::<f64>(M, add(mul(i, Clone::clone(w)), Clone::clone(c)), __rocq_global_371);
                  let n_clone = Clone::clone(n);
                  let r_clone = Clone::clone(r);
                  let tmp_9 = axpy_row(v205, n_clone, i, r_clone, 0u64, f);
                  (tmp_8, tmp_9)
                },
              }
            }
          });
          let tmp_10 = loop_::<(Rc<Array<f64>>, Rc<Array<f64>>)>(n, callback_2, callback_3, add(r, 1u64), (M_1, Q));
          match tmp_10 {
            (v326, v328) => {
              let st_clone_1 = Rc::clone(&st);
              let pm = fs_perm(st_clone_1);
              let x = a::get::<u64>(&pm, v111);
              let y = a::get::<u64>(&pm, r);
              let tmp_11 = add(r, 1u64);
              let tmp_12 = fs_pc(st);
              let tmp_13 = a::set::<u64>(tmp_12, r, c);
              let tmp_14 = a::set::<u64>(pm, v111, y);
              let tmp_15 = a::set::<u64>(tmp_14, r, x);
              Rc::new(fstate { fs_M: v326, fs_Q: v328, fs_r: tmp_11, fs_pc: tmp_13, fs_perm: tmp_15 })
            },
          }
        }
      },
    }
  } else {
    std::mem::drop(thr);
    st
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.tab
// Variant: uncurried
pub fn tab<T: Clone + 'static>(n: u64, d: T, f: Rc<dyn Fn(u64) -> T>) -> Rc<Array<T>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<T>>) -> bool> = Rc::new(move |_v5: u64, v6: Rc<Array<T>>| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<T>>) -> Rc<Array<T>>> = Rc::new({
    move |i: u64, t: Rc<Array<T>>| -> Rc<Array<T>> {
      let f = &f;
      let tmp = f(i);
      a::set::<T>(t, i, tmp)
    }
  });
  let tmp_1 = a::make::<T>(n, d);
  loop_::<Rc<Array<T>>>(n, callback, callback_1, 0u64, tmp_1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.forward
// Variant: uncurried
pub fn forward(n: u64, w: u64, thr: Rc<Array<f64>>, M: Rc<Array<f64>>, Q: Rc<Array<f64>>) -> Rc<fstate> {
  let callback: Rc<dyn Fn(u64, Rc<fstate>) -> bool> = Rc::new(move |_v7: u64, v8: Rc<fstate>| -> bool {
    std::mem::drop(v8);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<fstate>) -> Rc<fstate>> = Rc::new({
    let __anf_capture_22 = n;
    move |v28: u64, v29: Rc<fstate>| -> Rc<fstate> {
      let tmp = Clone::clone(&__anf_capture_22);
      let w_clone = Clone::clone(&w);
      let thr_clone = Rc::clone(&thr);
      fwd_col(tmp, w_clone, thr_clone, v28, v29)
    }
  });
  let tmp_1 = 0u64;
  let tmp_2 = 0u64;
  let tmp_3 = a::make::<u64>(n, 0u64);
  let tmp_4 = 0u64;
  let callback_2: Rc<dyn Fn(u64) -> u64> = Rc::new(move |i: u64| -> u64 {
    i
  });
  let tmp_5 = tab::<u64>(n, tmp_4, callback_2);
  loop_::<Rc<fstate>>(n, callback, callback_1, tmp_1, Rc::new(fstate { fs_M: M, fs_Q: Q, fs_r: tmp_2, fs_pc: tmp_3, fs_perm: tmp_5 }))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.col_thr
// Variant: uncurried
pub fn col_thr(xa: Rc<Array<Rc<Array<f64>>>>, n: u64) -> Rc<Array<f64>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(move |_v4: u64, v5: Rc<Array<f64>>| -> bool {
    std::mem::drop(v5);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new({
    let __anf_capture_19 = n;
    move |j: u64, T: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let xa = &xa;
      let n = &__anf_capture_19;
      let callback_2: Rc<dyn Fn(u64, f64) -> bool> = Rc::new(move |_v25: u64, _v26: f64| -> bool {
        true
      });
      let xa_clone = Rc::clone(xa);
      let callback_3: Rc<dyn Fn(u64, f64) -> f64> = Rc::new({
        let __anf_capture_40 = j;
        move |i: u64, m: f64| -> f64 {
          let xa = &xa_clone;
          let j = &__anf_capture_40;
          let xa_clone_1 = Rc::clone(xa);
          let tmp = a::get::<Rc<Array<f64>>>(&xa_clone_1, i);
          let tmp_1 = &tmp;
          let tmp_2 = a::get::<f64>(tmp_1, Clone::clone(j));
          let v = abs_1(tmp_2);
          if ltb_1(m, v) {
            std::mem::drop(tmp);
            std::mem::drop(xa_clone_1);
            v
          } else {
            std::mem::drop(tmp);
            std::mem::drop(xa_clone_1);
            m
          }
        }
      });
      let n_clone = Clone::clone(n);
      let m = loop_::<f64>(n_clone, callback_2, callback_3, 0u64, __rocq_global_371);
      a::set::<f64>(T, j, mul_1(m, __rocq_global_722))
    }
  });
  let tmp_3 = a::make::<f64>(n, __rocq_global_371);
  loop_::<Rc<Array<f64>>>(n, callback, callback_1, 0u64, tmp_3)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.init_M
// Variant: uncurried
pub fn init_M(xa: Rc<Array<Rc<Array<f64>>>>, xb: Rc<Array<f64>>, n: u64, w: u64) -> Rc<Array<f64>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(move |_v6: u64, v7: Rc<Array<f64>>| -> bool {
    std::mem::drop(v7);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new({
    let __anf_capture_25 = w;
    let __anf_capture_27 = n;
    move |i: u64, M: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let xa = &xa;
      let w = &__anf_capture_25;
      let n = &__anf_capture_27;
      let xb = &xb;
      let xa_clone = Rc::clone(xa);
      let row = a::get::<Rc<Array<f64>>>(&xa_clone, i);
      std::mem::drop(xa_clone);
      let callback_2: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(move |_v41: u64, v42: Rc<Array<f64>>| -> bool {
        std::mem::drop(v42);
        true
      });
      let w_clone = Clone::clone(w);
      let callback_3: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new({
        let __anf_capture_56 = i;
        move |j: u64, M: Rc<Array<f64>>| -> Rc<Array<f64>> {
          let i = &__anf_capture_56;
          let w = &w_clone;
          let row = &row;
          let tmp = add(mul(Clone::clone(i), Clone::clone(w)), j);
          let tmp_1 = a::get::<f64>(row, j);
          a::set::<f64>(M, tmp, tmp_1)
        }
      });
      let tmp_2 = 0u64;
      let M_1 = loop_::<Rc<Array<f64>>>(Clone::clone(n), callback_2, callback_3, tmp_2, M);
      let tmp_3 = add(mul(i, Clone::clone(w)), Clone::clone(n));
      let tmp_4 = a::get::<f64>(xb, i);
      a::set::<f64>(M_1, tmp_3, tmp_4)
    }
  });
  let tmp_5 = a::make::<f64>(mul(n, w), __rocq_global_371);
  loop_::<Rc<Array<f64>>>(n, callback, callback_1, 0u64, tmp_5)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.init_Q
pub fn init_Q(n: u64) -> Rc<Array<f64>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(move |_v3: u64, v4: Rc<Array<f64>>| -> bool {
    std::mem::drop(v4);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new({
    let __anf_capture_14 = n;
    move |i: u64, Q: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let tmp = Clone::clone(&__anf_capture_14);
      a::set::<f64>(Q, add(mul(i, tmp), i), __rocq_global_820)
    }
  });
  let tmp_1 = a::make::<f64>(mul(n, n), __rocq_global_371);
  loop_::<Rc<Array<f64>>>(n, callback, callback_1, 0u64, tmp_1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.transpose
// Variant: uncurried
pub fn transpose(xa: Rc<Array<Rc<Array<f64>>>>, n: u64) -> Rc<Array<f64>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(move |_v4: u64, v5: Rc<Array<f64>>| -> bool {
    std::mem::drop(v5);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new({
    let __anf_capture_19 = n;
    move |i: u64, T: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let xa = &xa;
      let n = &__anf_capture_19;
      let xa_clone = Rc::clone(xa);
      let row = a::get::<Rc<Array<f64>>>(&xa_clone, i);
      std::mem::drop(xa_clone);
      let callback_2: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(move |_v31: u64, v32: Rc<Array<f64>>| -> bool {
        std::mem::drop(v32);
        true
      });
      let n_clone = Clone::clone(n);
      let callback_3: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new({
        let __anf_capture_48 = i;
        move |j: u64, T: Rc<Array<f64>>| -> Rc<Array<f64>> {
          let n = &n_clone;
          let i = &__anf_capture_48;
          let row = &row;
          let tmp = add(mul(j, Clone::clone(n)), Clone::clone(i));
          let tmp_1 = a::get::<f64>(row, j);
          a::set::<f64>(T, tmp, tmp_1)
        }
      });
      let n_clone_1 = Clone::clone(n);
      loop_::<Rc<Array<f64>>>(n_clone_1, callback_2, callback_3, 0u64, T)
    }
  });
  let tmp_2 = a::make::<f64>(mul(n, n), __rocq_global_371);
  loop_::<Rc<Array<f64>>>(n, callback, callback_1, 0u64, tmp_2)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub_2(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.scale_row
// Variant: uncurried
pub fn scale_row(T: Rc<Array<f64>>, w: u64, i: u64, piv: f64) -> Rc<Array<f64>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(move |_v6: u64, v7: Rc<Array<f64>>| -> bool {
    std::mem::drop(v7);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new({
    let __anf_capture_23 = w;
    move |j: u64, T: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let i = &i;
      let w = &__anf_capture_23;
      let piv = &piv;
      let tmp = add(mul(Clone::clone(i), Clone::clone(w)), j);
      let tmp_1 = a::get::<f64>(&T, add(mul(Clone::clone(i), Clone::clone(w)), j));
      let piv_clone = Clone::clone(piv);
      a::set::<f64>(T, tmp, div_1(tmp_1, piv_clone))
    }
  });
  loop_::<Rc<Array<f64>>>(w, callback, callback_1, 0u64, T)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.backsub
// Variant: uncurried
pub fn backsub(n: u64, w: u64, M: Rc<Array<f64>>, Q: Rc<Array<f64>>) -> (Rc<Array<f64>>, Rc<Array<f64>>) {
  let callback: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> bool> = Rc::new(move |_v6: u64, v7: (Rc<Array<f64>>, Rc<Array<f64>>)| -> bool {
    std::mem::drop(v7);
    true
  });
  let callback_1: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>)> = Rc::new({
    let __anf_capture_21 = n;
    move |t: u64, mq: (Rc<Array<f64>>, Rc<Array<f64>>)| -> (Rc<Array<f64>>, Rc<Array<f64>>) {
      let w = &w;
      let n = &__anf_capture_21;
      match mq {
        (v26, v28) => {
          let Q = &v26;
          let tmp = 1u64;
          let tmp_1 = sub_2(Clone::clone(n), tmp);
          let i = sub_2(tmp_1, t);
          let piv = a::get::<f64>(Q, add(mul(i, Clone::clone(w)), i));
          let tmp_2 = a::get::<f64>(Q, add(mul(i, Clone::clone(w)), Clone::clone(n)));
          let xi = div_1(tmp_2, piv);
          let M = a::set::<f64>(v26, add(mul(i, Clone::clone(w)), Clone::clone(n)), xi);
          let Q_1 = scale_row(v28, Clone::clone(n), i, piv);
          let callback_2: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> bool> = Rc::new(move |_v112: u64, v113: (Rc<Array<f64>>, Rc<Array<f64>>)| -> bool {
            std::mem::drop(v113);
            true
          });
          let w_clone = Clone::clone(w);
          let n_clone = Clone::clone(n);
          let callback_3: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>)> = Rc::new({
            let __anf_capture_131 = xi;
            let __anf_capture_135 = i;
            move |i_: u64, mq: (Rc<Array<f64>>, Rc<Array<f64>>)| -> (Rc<Array<f64>>, Rc<Array<f64>>) {
              let w = &w_clone;
              let xi = &__anf_capture_131;
              let n = &n_clone;
              let i = &__anf_capture_135;
              match mq {
                (v140, v142) => {
                  let Q = &v140;
                  let f = a::get::<f64>(Q, add(mul(i_, Clone::clone(w)), Clone::clone(i)));
                  let tmp_3 = add(mul(i_, Clone::clone(w)), Clone::clone(n));
                  let tmp_4 = a::get::<f64>(Q, add(mul(i_, Clone::clone(w)), Clone::clone(n)));
                  let tmp_5 = a::set::<f64>(v140, tmp_3, sub_1(tmp_4, mul_1(f, Clone::clone(xi))));
                  let n_clone_1 = Clone::clone(n);
                  let i_clone = Clone::clone(i);
                  let tmp_6 = axpy_row(v142, n_clone_1, i_, i_clone, 0u64, f);
                  (tmp_5, tmp_6)
                },
              }
            }
          });
          loop_::<(Rc<Array<f64>>, Rc<Array<f64>>)>(i, callback_2, callback_3, 0u64, (M, Q_1))
        },
      }
    }
  });
  loop_::<(Rc<Array<f64>>, Rc<Array<f64>>)>(n, callback, callback_1, 0u64, (M, Q))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.get_col
// Variant: uncurried
pub fn get_col(M: Rc<Array<f64>>, n: u64, w: u64, c: u64) -> Rc<Array<f64>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(move |_v6: u64, v7: Rc<Array<f64>>| -> bool {
    std::mem::drop(v7);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new({
    move |i: u64, x: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let w = &w;
      let c = &c;
      let tmp = a::get::<f64>(&M, add(mul(i, Clone::clone(w)), Clone::clone(c)));
      a::set::<f64>(x, i, tmp)
    }
  });
  let tmp_1 = a::make::<f64>(n, __rocq_global_371);
  loop_::<Rc<Array<f64>>>(n, callback, callback_1, 0u64, tmp_1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.i2z
pub fn i2z(x: u64) -> Rc<BigInt> {
  to_Z(x)
}

// Rocq: Corelib.BinNums.IntDef.Z.mul
// Variant: uncurried
pub fn mul_2(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  b::mul(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.leb
// Variant: uncurried
pub fn leb_owned(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  b::le(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.leb
// Variant: borrowed, uncurried
pub fn leb(v0: &Rc<BigInt>, v1: &Rc<BigInt>) -> bool {
  let tmp = Rc::clone(v0);
  let tmp_1 = Rc::clone(v1);
  b::le(tmp, tmp_1)
}

// Rocq: Corelib.BinNums.IntDef.Z.shiftl
// Variant: uncurried
pub fn shiftl(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  b::shiftl(v0, v1)
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
          let tmp = m1;
          let tmp_1 = m2;
          if leb(tmp, tmp_1) {
            let m1_clone = Rc::clone(m1);
            let tmp_2 = sub(v11, m1_clone);
            let tmp_3 = shiftl(v9, tmp_2);
            let tmp_4 = add_1(v3, tmp_3);
            (tmp_4, v5)
          } else {
            let m2_clone = Rc::clone(m2);
            let tmp_5 = sub(v5, m2_clone);
            let tmp_6 = shiftl(v3, tmp_5);
            let tmp_7 = add_1(tmp_6, v9);
            (tmp_7, v11)
          }
        },
      }
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.d0
pub fn d0(_v0: ()) -> (Rc<BigInt>, Rc<BigInt>) {
  let tmp = b::zero();
  let tmp_1 = b::zero();
  (tmp, tmp_1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dsumf
// Variant: uncurried
pub fn dsumf(len: u64, f: Rc<dyn Fn(u64) -> (Rc<BigInt>, Rc<BigInt>)>) -> (Rc<BigInt>, Rc<BigInt>) {
  let callback: Rc<dyn Fn(u64, (Rc<BigInt>, Rc<BigInt>)) -> bool> = Rc::new(move |_v4: u64, v5: (Rc<BigInt>, Rc<BigInt>)| -> bool {
    std::mem::drop(v5);
    true
  });
  let callback_1: Rc<dyn Fn(u64, (Rc<BigInt>, Rc<BigInt>)) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new({
    move |k: u64, acc: (Rc<BigInt>, Rc<BigInt>)| -> (Rc<BigInt>, Rc<BigInt>) {
      let f = &f;
      let tmp = f(k);
      dadd(acc, tmp)
    }
  });
  loop_::<(Rc<BigInt>, Rc<BigInt>)>(len, callback, callback_1, 0u64, d0(()))
}

// Rocq: Stdlib.ZArith.BinIntDef.Z.abs
pub fn abs_owned(v0: Rc<BigInt>) -> Rc<BigInt> {
  b::abs(v0)
}

// Rocq: Stdlib.ZArith.BinIntDef.Z.abs
// Variant: borrowed
pub fn abs(v0: &Rc<BigInt>) -> Rc<BigInt> {
  let tmp = Rc::clone(v0);
  b::abs(tmp)
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dabs
pub fn dabs(x: (Rc<BigInt>, Rc<BigInt>)) -> (Rc<BigInt>, Rc<BigInt>) {
  let x_clone = Clone::clone(&x);
  let tmp = fst::<Rc<BigInt>, Rc<BigInt>>(x_clone);
  let tmp_1 = abs_owned(tmp);
  let tmp_2 = snd::<Rc<BigInt>, Rc<BigInt>>(x);
  (tmp_1, tmp_2)
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b_1: bool) -> bool {
  if b_1 {
    false
  } else {
    true
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
  let f_1 = if is_zero(f) {
    div_1(__rocq_global_820, f)
  } else {
    f
  };
  ltb_1(f_1, __rocq_global_371)
}

// Rocq: Corelib.Floats.FloatOps.shift
pub fn shift(_v0: ()) -> Rc<BigInt> {
  let tmp = b::one();
  let tmp_1 = b::twice(tmp);
  let tmp_2 = b::twice(tmp_1);
  let tmp_3 = b::twice(tmp_2);
  let tmp_4 = b::twice(tmp_3);
  let tmp_5 = b::twice(tmp_4);
  let tmp_6 = b::twice_plus_one(tmp_5);
  let tmp_7 = b::twice_plus_one(tmp_6);
  let tmp_8 = b::twice(tmp_7);
  let tmp_9 = b::twice_plus_one(tmp_8);
  let tmp_10 = b::twice(tmp_9);
  let tmp_11 = b::twice_plus_one(tmp_10);
  b::identity(tmp_11)
}

// Rocq: Corelib.Floats.FloatOps.prec
pub fn prec(_v0: ()) -> Rc<BigInt> {
  let tmp = b::one();
  let tmp_1 = b::twice_plus_one(tmp);
  let tmp_2 = b::twice(tmp_1);
  let tmp_3 = b::twice_plus_one(tmp_2);
  let tmp_4 = b::twice(tmp_3);
  let tmp_5 = b::twice_plus_one(tmp_4);
  b::identity(tmp_5)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dec
pub fn dec(f: f64) -> (Rc<BigInt>, Rc<BigInt>) {
  if is_nan(f) {
    let tmp = b::zero();
    let tmp_1 = b::zero();
    (tmp, tmp_1)
  } else {
    if is_zero(f) {
      let tmp_2 = b::zero();
      let tmp_3 = b::zero();
      (tmp_2, tmp_3)
    } else {
      if is_infinity(f) {
        let tmp_4 = b::zero();
        let tmp_5 = b::zero();
        (tmp_4, tmp_5)
      } else {
        let tmp_6 = frshiftexp(f);
        match tmp_6 {
          (v52, v54) => {
            let r = &v54;
            let m = to_Z(normfr_mantissa(v52));
            let tmp_7 = if get_sign(f) {
              opp(m)
            } else {
              m
            };
            let r_clone = Clone::clone(r);
            let tmp_8 = to_Z(r_clone);
            let tmp_9 = shift(());
            let tmp_10 = sub(tmp_8, tmp_9);
            let tmp_11 = prec(());
            let tmp_12 = sub(tmp_10, tmp_11);
            (tmp_7, tmp_12)
          },
        }
      }
    }
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.rowabs
// Variant: uncurried
pub fn rowabs(xa: Rc<Array<Rc<Array<f64>>>>, n: u64) -> Rc<Array<(Rc<BigInt>, Rc<BigInt>)>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<(Rc<BigInt>, Rc<BigInt>)>>) -> bool> = Rc::new(move |_v4: u64, v5: Rc<Array<(Rc<BigInt>, Rc<BigInt>)>>| -> bool {
    std::mem::drop(v5);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<(Rc<BigInt>, Rc<BigInt>)>>) -> Rc<Array<(Rc<BigInt>, Rc<BigInt>)>>> = Rc::new({
    let __anf_capture_19 = n;
    move |k: u64, S: Rc<Array<(Rc<BigInt>, Rc<BigInt>)>>| -> Rc<Array<(Rc<BigInt>, Rc<BigInt>)>> {
      let xa = &xa;
      let n = &__anf_capture_19;
      let xa_clone = Rc::clone(xa);
      let row = a::get::<Rc<Array<f64>>>(&xa_clone, k);
      std::mem::drop(xa_clone);
      let callback_2: Rc<dyn Fn(u64) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new({
        move |j: u64| -> (Rc<BigInt>, Rc<BigInt>) {
          let tmp = a::get::<f64>(&row, j);
          dabs(dec(tmp))
        }
      });
      let n_clone = Clone::clone(n);
      a::set::<(Rc<BigInt>, Rc<BigInt>)>(S, k, dsumf(n_clone, callback_2))
    }
  });
  let tmp_1 = a::make::<(Rc<BigInt>, Rc<BigInt>)>(n, d0(()));
  loop_::<Rc<Array<(Rc<BigInt>, Rc<BigInt>)>>>(n, callback, callback_1, 0u64, tmp_1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dneg
pub fn dneg(x: (Rc<BigInt>, Rc<BigInt>)) -> (Rc<BigInt>, Rc<BigInt>) {
  let x_clone = Clone::clone(&x);
  let tmp = fst::<Rc<BigInt>, Rc<BigInt>>(x_clone);
  let tmp_1 = opp(tmp);
  let tmp_2 = snd::<Rc<BigInt>, Rc<BigInt>>(x);
  (tmp_1, tmp_2)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dleb
// Variant: uncurried
pub fn dleb(x: (Rc<BigInt>, Rc<BigInt>), y: (Rc<BigInt>, Rc<BigInt>)) -> bool {
  let tmp = b::zero();
  let tmp_1 = fst::<Rc<BigInt>, Rc<BigInt>>(dadd(y, dneg(x)));
  leb_owned(tmp, tmp_1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dmax
// Variant: uncurried
pub fn dmax(x: (Rc<BigInt>, Rc<BigInt>), y: (Rc<BigInt>, Rc<BigInt>)) -> (Rc<BigInt>, Rc<BigInt>) {
  let x_clone = Clone::clone(&x);
  let tmp = x_clone;
  let y_clone = Clone::clone(&y);
  if dleb(tmp, y_clone) {
    std::mem::drop(x);
    y
  } else {
    std::mem::drop(y);
    x
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

// Rocq: EquationsolverExact.equationsolver_exact_implem.maxb
// Variant: uncurried
pub fn maxb(len: u64, h: Rc<dyn Fn(u64) -> ((Rc<BigInt>, Rc<BigInt>), bool)>) -> ((Rc<BigInt>, Rc<BigInt>), bool) {
  let callback: Rc<dyn Fn(u64, ((Rc<BigInt>, Rc<BigInt>), bool)) -> bool> = Rc::new(move |_v4: u64, v5: ((Rc<BigInt>, Rc<BigInt>), bool)| -> bool {
    std::mem::drop(v5);
    true
  });
  let callback_1: Rc<dyn Fn(u64, ((Rc<BigInt>, Rc<BigInt>), bool)) -> ((Rc<BigInt>, Rc<BigInt>), bool)> = Rc::new({
    move |i: u64, st: ((Rc<BigInt>, Rc<BigInt>), bool)| -> ((Rc<BigInt>, Rc<BigInt>), bool) {
      let h = &h;
      let r = h(i);
      let st_clone = Clone::clone(&st);
      let tmp = fst::<(Rc<BigInt>, Rc<BigInt>), bool>(st_clone);
      let r_clone = Clone::clone(&r);
      (dmax(tmp, fst::<(Rc<BigInt>, Rc<BigInt>), bool>(r_clone)), andb(snd::<(Rc<BigInt>, Rc<BigInt>), bool>(st), snd::<(Rc<BigInt>, Rc<BigInt>), bool>(r)))
    }
  });
  loop_::<((Rc<BigInt>, Rc<BigInt>), bool)>(len, callback, callback_1, 0u64, (d0(()), true))
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

// Rocq: Corelib.Floats.PrimFloat.is_finite
pub fn is_finite(x: f64) -> bool {
  negb(orb(is_nan(x), is_infinity(x)))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dsumb
// Variant: uncurried
pub fn dsumb(len: u64, g: Rc<dyn Fn(u64) -> f64>, f: Rc<dyn Fn(u64, f64) -> (Rc<BigInt>, Rc<BigInt>)>) -> ((Rc<BigInt>, Rc<BigInt>), bool) {
  let callback: Rc<dyn Fn(u64, ((Rc<BigInt>, Rc<BigInt>), bool)) -> bool> = Rc::new(move |_v5: u64, v6: ((Rc<BigInt>, Rc<BigInt>), bool)| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(u64, ((Rc<BigInt>, Rc<BigInt>), bool)) -> ((Rc<BigInt>, Rc<BigInt>), bool)> = Rc::new({
    move |k: u64, st: ((Rc<BigInt>, Rc<BigInt>), bool)| -> ((Rc<BigInt>, Rc<BigInt>), bool) {
      let g = &g;
      let f = &f;
      let d = g(k);
      let st_clone = Clone::clone(&st);
      let tmp = fst::<(Rc<BigInt>, Rc<BigInt>), bool>(st_clone);
      let tmp_1 = f(k, d);
      (dadd(tmp, tmp_1), andb(snd::<(Rc<BigInt>, Rc<BigInt>), bool>(st), is_finite(d)))
    }
  });
  loop_::<((Rc<BigInt>, Rc<BigInt>), bool)>(len, callback, callback_1, 0u64, (d0(()), true))
}

// Rocq: Corelib.Floats.PrimFloat.add
// Variant: uncurried
pub fn add_2(v0: f64, v1: f64) -> f64 {
  rocq_float64::add(v0, v1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fdot
// Variant: uncurried
pub fn fdot_owned(X: Rc<Array<f64>>, ox: u64, Y: Rc<Array<f64>>, oy: u64, len: u64) -> f64 {
  let callback: Rc<dyn Fn(u64, f64) -> bool> = Rc::new(move |_v7: u64, _v8: f64| -> bool {
    true
  });
  let callback_1: Rc<dyn Fn(u64, f64) -> f64> = Rc::new({
    move |k: u64, s: f64| -> f64 {
      let ox = &ox;
      let X = &X;
      let oy = &oy;
      let Y = &Y;
      let tmp = a::get::<f64>(X, add(Clone::clone(ox), k));
      let tmp_1 = a::get::<f64>(Y, add(Clone::clone(oy), k));
      add_2(s, mul_1(tmp, tmp_1))
    }
  });
  loop_::<f64>(len, callback, callback_1, 0u64, __rocq_global_371)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fdot
// Variant: borrowed, uncurried
pub fn fdot(X: &Rc<Array<f64>>, ox: u64, Y: &Rc<Array<f64>>, oy: u64, len: u64) -> f64 {
  let len_1 = len;
  let callback: Rc<dyn Fn(u64, f64) -> bool> = Rc::new(move |_v10: u64, _v11: f64| -> bool {
    true
  });
  let X_clone = Rc::clone(X);
  let Y_clone = Rc::clone(Y);
  let callback_1: Rc<dyn Fn(u64, f64) -> f64> = Rc::new({
    move |k: u64, s: f64| -> f64 {
      let ox = &ox;
      let X = &X_clone;
      let oy = &oy;
      let Y = &Y_clone;
      let tmp = a::get::<f64>(X, add(Clone::clone(ox), k));
      let tmp_1 = a::get::<f64>(Y, add(Clone::clone(oy), k));
      add_2(s, mul_1(tmp, tmp_1))
    }
  });
  loop_::<f64>(len_1, callback, callback_1, 0u64, __rocq_global_371)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dsub
// Variant: uncurried
pub fn dsub(x: (Rc<BigInt>, Rc<BigInt>), y: (Rc<BigInt>, Rc<BigInt>)) -> (Rc<BigInt>, Rc<BigInt>) {
  dadd(x, dneg(y))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dint
pub fn dint_owned(z: Rc<BigInt>) -> (Rc<BigInt>, Rc<BigInt>) {
  let tmp = b::zero();
  (z, tmp)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dint
// Variant: borrowed
pub fn dint(z: &Rc<BigInt>) -> (Rc<BigInt>, Rc<BigInt>) {
  let tmp = b::zero();
  let z_clone = Rc::clone(z);
  (z_clone, tmp)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dmul
// Variant: uncurried
pub fn dmul(x: (Rc<BigInt>, Rc<BigInt>), y: (Rc<BigInt>, Rc<BigInt>)) -> (Rc<BigInt>, Rc<BigInt>) {
  let x_clone = Clone::clone(&x);
  let tmp = fst::<Rc<BigInt>, Rc<BigInt>>(x_clone);
  let y_clone = Clone::clone(&y);
  let tmp_1 = fst::<Rc<BigInt>, Rc<BigInt>>(y_clone);
  let tmp_2 = mul_2(tmp, tmp_1);
  let tmp_3 = snd::<Rc<BigInt>, Rc<BigInt>>(x);
  let tmp_4 = snd::<Rc<BigInt>, Rc<BigInt>>(y);
  let tmp_5 = add_1(tmp_3, tmp_4);
  (tmp_2, tmp_5)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.erow
// Variant: borrowed, uncurried
pub fn erow(n: u64, Q: &Rc<Array<f64>>, AT: &Rc<Array<f64>>, S: &Rc<Array<(Rc<BigInt>, Rc<BigInt>)>>, lamd: (Rc<BigInt>, Rc<BigInt>), mud2: (Rc<BigInt>, Rc<BigInt>), i: u64) -> ((Rc<BigInt>, Rc<BigInt>), bool) {
  let lamd_1 = lamd;
  let mud2_1 = mud2;
  let Q_clone = Rc::clone(Q);
  let AT_clone = Rc::clone(AT);
  let callback: Rc<dyn Fn(u64) -> f64> = Rc::new({
    let __anf_capture_23 = i;
    let __anf_capture_29 = n;
    move |j: u64| -> f64 {
      let i = &__anf_capture_23;
      let Q = &Q_clone;
      let AT = &AT_clone;
      let tmp = mul(Clone::clone(i), Clone::clone(&__anf_capture_29));
      let tmp_1 = mul(j, Clone::clone(&__anf_capture_29));
      let tmp_2 = Clone::clone(&__anf_capture_29);
      fdot(Q, tmp, AT, tmp_1, tmp_2)
    }
  });
  let callback_1: Rc<dyn Fn(u64, f64) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new({
    let __anf_capture_61 = i;
    move |j: u64, d: f64| -> (Rc<BigInt>, Rc<BigInt>) {
      let i = &__anf_capture_61;
      let i_clone = Clone::clone(i);
      let tmp_3 = if eqb(i_clone, j) {
        let tmp_4 = b::one();
        b::identity(tmp_4)
      } else {
        b::zero()
      };
      dabs(dsub(dint_owned(tmp_3), dec(d)))
    }
  });
  let e = dsumb(n, callback, callback_1);
  let Q_clone_1 = Rc::clone(Q);
  let S_clone = Rc::clone(S);
  let callback_2: Rc<dyn Fn(u64) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new({
    let __anf_capture_123 = i;
    let __anf_capture_125 = n;
    move |k: u64| -> (Rc<BigInt>, Rc<BigInt>) {
      let i = &__anf_capture_123;
      let n = &__anf_capture_125;
      let Q = &Q_clone_1;
      let S = &S_clone;
      let tmp_5 = dabs(dec(a::get::<f64>(Q, add(mul(Clone::clone(i), Clone::clone(n)), k))));
      let tmp_6 = a::get::<(Rc<BigInt>, Rc<BigInt>)>(S, k);
      dmul(tmp_5, tmp_6)
    }
  });
  let rr = dsumf(n, callback_2);
  let e_clone = Clone::clone(&e);
  let tmp_7 = dadd(fst::<(Rc<BigInt>, Rc<BigInt>), bool>(e_clone), dmul(lamd_1, rr));
  (dadd(tmp_7, mud2_1), snd::<(Rc<BigInt>, Rc<BigInt>), bool>(e))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.rowR
// Variant: borrowed, uncurried
pub fn rowR(n: u64, Q: &Rc<Array<f64>>, i: u64) -> ((Rc<BigInt>, Rc<BigInt>), bool) {
  let Q_clone = Rc::clone(Q);
  let callback: Rc<dyn Fn(u64) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new({
    let __anf_capture_16 = n;
    move |k: u64| -> (Rc<BigInt>, Rc<BigInt>) {
      let i = &i;
      let n = &__anf_capture_16;
      let tmp = a::get::<f64>(&Q_clone, add(mul(Clone::clone(i), Clone::clone(n)), k));
      dabs(dec(tmp))
    }
  });
  (dsumf(n, callback), true)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.resid
// Variant: borrowed, uncurried
pub fn resid(n: u64, xa: &Rc<Array<Rc<Array<f64>>>>, xb: &Rc<Array<f64>>, xt: &Rc<Array<f64>>, lamd: (Rc<BigInt>, Rc<BigInt>), mud1: (Rc<BigInt>, Rc<BigInt>), i: u64) -> ((Rc<BigInt>, Rc<BigInt>), bool) {
  let n_1 = n;
  let lamd_1 = lamd;
  let mud1_1 = mud1;
  let i_1 = i;
  let xa_clone = Rc::clone(xa);
  let row = a::get::<Rc<Array<f64>>>(&xa_clone, i_1);
  std::mem::drop(xa_clone);
  let row_clone = Rc::clone(&row);
  let xt_clone = Rc::clone(xt);
  let d = fdot_owned(row_clone, 0u64, xt_clone, 0u64, n_1);
  let tmp = dabs(dsub(dec(a::get::<f64>(xb, i_1)), dec(d)));
  let xt_clone_1 = Rc::clone(xt);
  let callback: Rc<dyn Fn(u64) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new({
    let __anf_capture_68 = row;
    move |j: u64| -> (Rc<BigInt>, Rc<BigInt>) {
      let row = &__anf_capture_68;
      let xt = &xt_clone_1;
      let tmp_1 = dec(a::get::<f64>(row, j));
      let tmp_2 = a::get::<f64>(xt, j);
      dabs(dmul(tmp_1, dec(tmp_2)))
    }
  });
  let tmp_3 = dadd(tmp, dmul(lamd_1, dsumf(n_1, callback)));
  (dadd(tmp_3, mud1_1), is_finite(d))
}

// Rocq: Corelib.BinNums.IntDef.Z.ltb
// Variant: uncurried
pub fn ltb_2(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  b::lt(v0, v1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dltb
// Variant: uncurried
pub fn dltb(x: (Rc<BigInt>, Rc<BigInt>), y: (Rc<BigInt>, Rc<BigInt>)) -> bool {
  let tmp = b::zero();
  let tmp_1 = fst::<Rc<BigInt>, Rc<BigInt>>(dadd(y, dneg(x)));
  ltb_2(tmp, tmp_1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.d1
pub fn d1(_v0: ()) -> (Rc<BigInt>, Rc<BigInt>) {
  let tmp = b::one();
  let tmp_1 = b::identity(tmp);
  let tmp_2 = b::zero();
  (tmp_1, tmp_2)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.certify
// Variant: uncurried
pub fn certify(n: u64, xa: Rc<Array<Rc<Array<f64>>>>, xb: Rc<Array<f64>>, AT: Rc<Array<f64>>, Q: Rc<Array<f64>>, xt: Rc<Array<f64>>) -> bool {
  let nz = i2z(n);
  let tmp = b::one();
  let tmp_1 = b::twice_plus_one(tmp);
  let tmp_2 = b::identity(tmp_1);
  let nz_clone = Rc::clone(&nz);
  let tmp_3 = mul_2(tmp_2, nz_clone);
  let tmp_4 = b::one();
  let tmp_5 = b::twice_plus_one(tmp_4);
  let tmp_6 = b::twice(tmp_5);
  let tmp_7 = b::twice_plus_one(tmp_6);
  let tmp_8 = b::twice(tmp_7);
  let tmp_9 = b::twice_plus_one(tmp_8);
  let tmp_10 = b::neg(tmp_9);
  let lamd = (tmp_3, tmp_10);
  let tmp_11 = b::one();
  let tmp_12 = b::twice_plus_one(tmp_11);
  let tmp_13 = b::identity(tmp_12);
  let nz_clone_1 = Rc::clone(&nz);
  let tmp_14 = mul_2(tmp_13, nz_clone_1);
  let tmp_15 = b::one();
  let tmp_16 = b::twice(tmp_15);
  let tmp_17 = b::twice(tmp_16);
  let tmp_18 = b::twice(tmp_17);
  let tmp_19 = b::twice(tmp_18);
  let tmp_20 = b::twice_plus_one(tmp_19);
  let tmp_21 = b::twice_plus_one(tmp_20);
  let tmp_22 = b::twice(tmp_21);
  let tmp_23 = b::twice(tmp_22);
  let tmp_24 = b::twice_plus_one(tmp_23);
  let tmp_25 = b::twice_plus_one(tmp_24);
  let tmp_26 = b::neg(tmp_25);
  let mud1 = (tmp_14, tmp_26);
  let tmp_27 = b::one();
  let tmp_28 = b::twice_plus_one(tmp_27);
  let tmp_29 = b::identity(tmp_28);
  let nz_clone_2 = Rc::clone(&nz);
  let tmp_30 = mul_2(tmp_29, nz_clone_2);
  let tmp_31 = mul_2(tmp_30, nz);
  let tmp_32 = b::one();
  let tmp_33 = b::twice(tmp_32);
  let tmp_34 = b::twice(tmp_33);
  let tmp_35 = b::twice(tmp_34);
  let tmp_36 = b::twice(tmp_35);
  let tmp_37 = b::twice_plus_one(tmp_36);
  let tmp_38 = b::twice_plus_one(tmp_37);
  let tmp_39 = b::twice(tmp_38);
  let tmp_40 = b::twice(tmp_39);
  let tmp_41 = b::twice_plus_one(tmp_40);
  let tmp_42 = b::twice_plus_one(tmp_41);
  let tmp_43 = b::neg(tmp_42);
  let mud2 = (tmp_31, tmp_43);
  let xa_clone = Rc::clone(&xa);
  let S = rowabs(xa_clone, n);
  let Q_clone = Rc::clone(&Q);
  let AT_clone = Rc::clone(&AT);
  let S_clone = Rc::clone(&S);
  let lamd_clone = Clone::clone(&lamd);
  let tmp_44 = lamd_clone;
  let mud2_clone = Clone::clone(&mud2);
  let callback: Rc<dyn Fn(u64) -> ((Rc<BigInt>, Rc<BigInt>), bool)> = Rc::new({
    let __anf_capture_189 = n;
    move |v201: u64| -> ((Rc<BigInt>, Rc<BigInt>), bool) {
      let n = &__anf_capture_189;
      let Q = &Q_clone;
      let AT = &AT_clone;
      let S = &S_clone;
      let tmp_45 = erow(Clone::clone(n), Q, AT, S, Clone::clone(&tmp_44), Clone::clone(&mud2_clone), v201);
      tmp_45
    }
  });
  let tmp_46 = maxb(n, callback);
  match tmp_46 {
    (v225, v227) => {
      let ok1 = &v225;
      let Q_clone_1 = Rc::clone(&Q);
      let callback_1: Rc<dyn Fn(u64) -> ((Rc<BigInt>, Rc<BigInt>), bool)> = Rc::new({
        let __anf_capture_237 = n;
        move |v241: u64| -> ((Rc<BigInt>, Rc<BigInt>), bool) {
          let n = &__anf_capture_237;
          let Q = &Q_clone_1;
          let tmp_47 = rowR(Clone::clone(n), Q, v241);
          tmp_47
        }
      });
      let tmp_48 = maxb(n, callback_1);
      match tmp_48 {
        (v259, _v261) => {
          std::mem::drop(S);
          std::mem::drop(mud2);
          std::mem::drop(AT);
          std::mem::drop(Q);
          let xt_clone = Rc::clone(&xt);
          let callback_2: Rc<dyn Fn(u64) -> ((Rc<BigInt>, Rc<BigInt>), bool)> = Rc::new({
            let __anf_capture_278 = n;
            let __anf_capture_280 = xa;
            let __anf_capture_286 = lamd;
            move |v290: u64| -> ((Rc<BigInt>, Rc<BigInt>), bool) {
              let n = &__anf_capture_278;
              let xa = &__anf_capture_280;
              let xb = &xb;
              let xt = &xt_clone;
              let tmp_49 = resid(Clone::clone(n), xa, xb, xt, Clone::clone(&__anf_capture_286), Clone::clone(&mud1), v290);
              tmp_49
            }
          });
          let tmp_50 = maxb(n, callback_2);
          match tmp_50 {
            (v314, v316) => {
              let tmp_51 = andb(v227, v316);
              let tmp_52 = a::length::<f64>(&xt);
              std::mem::drop(xt);
              let tmp_53 = andb(tmp_51, eqb(tmp_52, n));
              let tmp_54 = d1(());
              let ok1_clone = Clone::clone(ok1);
              let tmp_55 = dltb(ok1_clone, tmp_54);
              let tmp_56 = b::one();
              let tmp_57 = b::twice_plus_one(tmp_56);
              let tmp_58 = b::twice_plus_one(tmp_57);
              let tmp_59 = b::twice_plus_one(tmp_58);
              let tmp_60 = b::twice_plus_one(tmp_59);
              let tmp_61 = b::twice(tmp_60);
              let tmp_62 = b::twice_plus_one(tmp_61);
              let tmp_63 = b::twice(tmp_62);
              let tmp_64 = b::twice(tmp_63);
              let tmp_65 = b::twice(tmp_64);
              let tmp_66 = b::identity(tmp_65);
              let tmp_67 = b::zero();
              let tmp_68 = (tmp_66, tmp_67);
              let tmp_69 = dmul(v259, v314);
              let tmp_70 = andb(tmp_55, dleb(dadd(dmul(tmp_68, tmp_69), v225), d1(())));
              andb(tmp_53, tmp_70)
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
  b::min(v0, v1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.row_exp
// Variant: uncurried
pub fn row_exp(n: u64, row: Rc<Array<f64>>, bi: f64) -> Rc<BigInt> {
  let callback: Rc<dyn Fn(u64, Rc<BigInt>) -> bool> = Rc::new(move |_v5: u64, v6: Rc<BigInt>| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<BigInt>) -> Rc<BigInt>> = Rc::new({
    move |j: u64, E: Rc<BigInt>| -> Rc<BigInt> {
      let tmp = a::get::<f64>(&row, j);
      let tmp_1 = snd::<Rc<BigInt>, Rc<BigInt>>(dec(tmp));
      min(E, tmp_1)
    }
  });
  let tmp_2 = b::zero();
  let tmp_3 = snd::<Rc<BigInt>, Rc<BigInt>>(dec(bi));
  let tmp_4 = min(tmp_2, tmp_3);
  loop_::<Rc<BigInt>>(n, callback, callback_1, 0u64, tmp_4)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.scale
// Variant: uncurried
pub fn scale_owned(f: f64, E: Rc<BigInt>) -> Rc<BigInt> {
  let tmp = fst::<Rc<BigInt>, Rc<BigInt>>(dec(f));
  let tmp_1 = snd::<Rc<BigInt>, Rc<BigInt>>(dec(f));
  let tmp_2 = sub(tmp_1, E);
  shiftl(tmp, tmp_2)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.scale
// Variant: borrowed, uncurried
pub fn scale(f: f64, E: &Rc<BigInt>) -> Rc<BigInt> {
  let f_1 = f;
  let tmp = fst::<Rc<BigInt>, Rc<BigInt>>(dec(f_1));
  let tmp_1 = snd::<Rc<BigInt>, Rc<BigInt>>(dec(f_1));
  let E_clone = Rc::clone(E);
  let tmp_2 = sub(tmp_1, E_clone);
  shiftl(tmp, tmp_2)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fill_row
// Variant: uncurried
pub fn fill_row(n: u64, w: u64, i: u64, row: Rc<Array<f64>>, E: Rc<BigInt>, T: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = Rc::new(move |_v8: u64, v9: Rc<Array<Rc<BigInt>>>| -> bool {
    std::mem::drop(v9);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new({
    move |j: u64, T: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let i = &i;
      let w = &w;
      let row = &row;
      let E = &E;
      let tmp = add(mul(Clone::clone(i), Clone::clone(w)), j);
      let tmp_1 = scale(a::get::<f64>(row, j), E);
      a::set::<Rc<BigInt>>(T, tmp, tmp_1)
    }
  });
  loop_::<Rc<Array<Rc<BigInt>>>>(n, callback, callback_1, 0u64, T)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.build_step
// Variant: uncurried
pub fn build_step(a_1: Rc<Array<Rc<Array<f64>>>>, b_1: Rc<Array<f64>>, n: u64, w: u64, i: u64, T: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let row = a::get::<Rc<Array<f64>>>(&a_1, i);
  std::mem::drop(a_1);
  let bi = a::get::<f64>(&b_1, i);
  std::mem::drop(b_1);
  let row_clone = Rc::clone(&row);
  let E = row_exp(n, row_clone, bi);
  let E_clone = Rc::clone(&E);
  let T_1 = fill_row(n, w, i, row, E_clone, T);
  let tmp = add(mul(i, w), n);
  let tmp_1 = scale_owned(bi, E);
  a::set::<Rc<BigInt>>(T_1, tmp, tmp_1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.build
// Variant: uncurried
pub fn build(a_1: Rc<Array<Rc<Array<f64>>>>, b_1: Rc<Array<f64>>, n: u64, w: u64) -> Rc<Array<Rc<BigInt>>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = Rc::new(move |_v6: u64, v7: Rc<Array<Rc<BigInt>>>| -> bool {
    std::mem::drop(v7);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new({
    let __anf_capture_27 = n;
    let __anf_capture_29 = w;
    move |v31: u64, v32: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let a_clone = Rc::clone(&a_1);
      let b_clone = Rc::clone(&b_1);
      let tmp = Clone::clone(&__anf_capture_27);
      let tmp_1 = Clone::clone(&__anf_capture_29);
      build_step(a_clone, b_clone, tmp, tmp_1, v31, v32)
    }
  });
  let tmp_2 = mul(n, w);
  let tmp_3 = b::zero();
  let tmp_4 = a::make::<Rc<BigInt>>(tmp_2, tmp_3);
  loop_::<Rc<Array<Rc<BigInt>>>>(n, callback, callback_1, 0u64, tmp_4)
}

// Rocq: Corelib.BinNums.IntDef.Z.eqb
// Variant: uncurried
pub fn eqb_2(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  b::equal(v0, v1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.find_piv
// Variant: uncurried
pub fn find_piv(T: Rc<Array<Rc<BigInt>>>, n: u64, w: u64, c: u64, r: u64) -> u64 {
  let callback: Rc<dyn Fn(u64, u64) -> bool> = Rc::new(move |_v7: u64, _v8: u64| -> bool {
    true
  });
  let callback_1: Rc<dyn Fn(u64, u64) -> u64> = Rc::new({
    let __anf_capture_24 = n;
    move |i: u64, s: u64| -> u64 {
      let n = &__anf_capture_24;
      let w = &w;
      let c = &c;
      let T = &T;
      let n_clone = Clone::clone(n);
      if eqb(s, n_clone) {
        let tmp = a::get::<Rc<BigInt>>(T, add(mul(i, Clone::clone(w)), Clone::clone(c)));
        let tmp_1 = b::zero();
        if eqb_2(tmp, tmp_1) {
          s
        } else {
          i
        }
      } else {
        s
      }
    }
  });
  loop_::<u64>(n, callback, callback_1, r, n)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.swap_rows
// Variant: uncurried
pub fn swap_rows(T: Rc<Array<Rc<BigInt>>>, w: u64, q: u64, r: u64) -> Rc<Array<Rc<BigInt>>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = Rc::new(move |_v6: u64, v7: Rc<Array<Rc<BigInt>>>| -> bool {
    std::mem::drop(v7);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new({
    let __anf_capture_25 = w;
    move |j: u64, T: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let r = &r;
      let q = &q;
      let w = &__anf_capture_25;
      let x = a::get::<Rc<BigInt>>(&T, add(mul(Clone::clone(r), Clone::clone(w)), j));
      let y = a::get::<Rc<BigInt>>(&T, add(mul(Clone::clone(q), Clone::clone(w)), j));
      let tmp = a::set::<Rc<BigInt>>(T, add(mul(Clone::clone(r), Clone::clone(w)), j), y);
      let q_clone = Clone::clone(q);
      let w_clone = Clone::clone(w);
      a::set::<Rc<BigInt>>(tmp, add(mul(q_clone, w_clone), j), x)
    }
  });
  loop_::<Rc<Array<Rc<BigInt>>>>(w, callback, callback_1, 0u64, T)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.upd_row
// Variant: uncurried
pub fn upd_row(T: Rc<Array<Rc<BigInt>>>, w: u64, i: u64, r: u64, a_1: Rc<BigInt>, b_1: Rc<BigInt>) -> Rc<Array<Rc<BigInt>>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = Rc::new(move |_v8: u64, v9: Rc<Array<Rc<BigInt>>>| -> bool {
    std::mem::drop(v9);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new({
    let __anf_capture_33 = w;
    move |j: u64, T: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let i = &i;
      let a_1 = &a_1;
      let r = &r;
      let w = &__anf_capture_33;
      let b_1 = &b_1;
      let tmp = add(mul(Clone::clone(i), Clone::clone(w)), j);
      let tmp_1 = a::get::<Rc<BigInt>>(&T, add(mul(Clone::clone(i), Clone::clone(w)), j));
      let a_clone = Rc::clone(a_1);
      let tmp_2 = mul_2(a_clone, tmp_1);
      let tmp_3 = a::get::<Rc<BigInt>>(&T, add(mul(Clone::clone(r), Clone::clone(w)), j));
      let b_clone = Rc::clone(b_1);
      let tmp_4 = mul_2(b_clone, tmp_3);
      let tmp_5 = sub(tmp_2, tmp_4);
      a::set::<Rc<BigInt>>(T, tmp, tmp_5)
    }
  });
  loop_::<Rc<Array<Rc<BigInt>>>>(w, callback, callback_1, 0u64, T)
}

// Rocq: Corelib.BinNums.IntDef.Z.pos_div_eucl
// Variant: uncurried
pub fn pos_div_eucl_1(a_1: Rc<BigInt>, b_1: Rc<BigInt>) -> (Rc<BigInt>, Rc<BigInt>) {
  pos_div_eucl(a_1, b_1)
}

// Rocq: Corelib.BinNums.IntDef.Z.pos_div_eucl (local: pos_div_eucl)
// Variant: uncurried, lifted
pub fn pos_div_eucl(a_1: Rc<BigInt>, b_1: Rc<BigInt>) -> (Rc<BigInt>, Rc<BigInt>) {
  let a_clone = Rc::clone(&a_1);
  match b::positive_tag(a_clone) {
    b::PositiveTag::Odd => {
      let a_ = b::positive_tail(a_1);
      let b_clone = Rc::clone(&b_1);
      let tmp = pos_div_eucl(a_, b_clone);
      match tmp {
        (v18, v20) => {
          let tmp_1 = b::one();
          let tmp_2 = b::twice(tmp_1);
          let tmp_3 = b::identity(tmp_2);
          let tmp_4 = mul_2(tmp_3, v20);
          let tmp_5 = b::one();
          let tmp_6 = b::identity(tmp_5);
          let r_ = add_1(tmp_4, tmp_6);
          let r__clone = Rc::clone(&r_);
          let b_clone_1 = Rc::clone(&b_1);
          if ltb_2(r__clone, b_clone_1) {
            std::mem::drop(b_1);
            let tmp_7 = b::one();
            let tmp_8 = b::twice(tmp_7);
            let tmp_9 = b::identity(tmp_8);
            let tmp_10 = mul_2(tmp_9, v18);
            (tmp_10, r_)
          } else {
            let tmp_11 = b::one();
            let tmp_12 = b::twice(tmp_11);
            let tmp_13 = b::identity(tmp_12);
            let tmp_14 = mul_2(tmp_13, v18);
            let tmp_15 = b::one();
            let tmp_16 = b::identity(tmp_15);
            let tmp_17 = add_1(tmp_14, tmp_16);
            let tmp_18 = sub(r_, b_1);
            (tmp_17, tmp_18)
          }
        },
      }
    },
    b::PositiveTag::Even => {
      let a_ = b::positive_tail(a_1);
      let b_clone_2 = Rc::clone(&b_1);
      let tmp_19 = pos_div_eucl(a_, b_clone_2);
      match tmp_19 {
        (v129, v131) => {
          let tmp_20 = b::one();
          let tmp_21 = b::twice(tmp_20);
          let tmp_22 = b::identity(tmp_21);
          let r_ = mul_2(tmp_22, v131);
          let r__clone_1 = Rc::clone(&r_);
          let b_clone_3 = Rc::clone(&b_1);
          if ltb_2(r__clone_1, b_clone_3) {
            std::mem::drop(b_1);
            let tmp_23 = b::one();
            let tmp_24 = b::twice(tmp_23);
            let tmp_25 = b::identity(tmp_24);
            let tmp_26 = mul_2(tmp_25, v129);
            (tmp_26, r_)
          } else {
            let tmp_27 = b::one();
            let tmp_28 = b::twice(tmp_27);
            let tmp_29 = b::identity(tmp_28);
            let tmp_30 = mul_2(tmp_29, v129);
            let tmp_31 = b::one();
            let tmp_32 = b::identity(tmp_31);
            let tmp_33 = add_1(tmp_30, tmp_32);
            let tmp_34 = sub(r_, b_1);
            (tmp_33, tmp_34)
          }
        },
      }
    },
    b::PositiveTag::One => {
      let tmp_35 = b::one();
      let tmp_36 = b::twice(tmp_35);
      let tmp_37 = b::identity(tmp_36);
      if leb_owned(tmp_37, b_1) {
        std::mem::drop(a_1);
        let tmp_38 = b::zero();
        let tmp_39 = b::one();
        let tmp_40 = b::identity(tmp_39);
        (tmp_38, tmp_40)
      } else {
        std::mem::drop(a_1);
        let tmp_41 = b::one();
        let tmp_42 = b::identity(tmp_41);
        let tmp_43 = b::zero();
        (tmp_42, tmp_43)
      }
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.div_eucl
// Variant: uncurried
pub fn div_eucl(a_1: Rc<BigInt>, b_1: Rc<BigInt>) -> (Rc<BigInt>, Rc<BigInt>) {
  let a_clone = Rc::clone(&a_1);
  match b::integer_tag(a_clone) {
    b::IntegerTag::Zero => {
      std::mem::drop(a_1);
      std::mem::drop(b_1);
      let tmp = b::zero();
      let tmp_1 = b::zero();
      (tmp, tmp_1)
    },
    b::IntegerTag::Positive => {
      let a_clone_1 = Rc::clone(&a_1);
      let a_ = b::integer_magnitude(a_clone_1);
      let b_clone = Rc::clone(&b_1);
      let tmp_2 = b::integer_tag(b_clone);
      match &tmp_2 {
        b::IntegerTag::Zero => {
          std::mem::drop(a_);
          std::mem::drop(b_1);
          let tmp_3 = b::zero();
          (tmp_3, a_1)
        },
        b::IntegerTag::Positive => {
          std::mem::drop(a_1);
          let b_clone_1 = Rc::clone(&b_1);
          let p = b::integer_magnitude(b_clone_1);
          std::mem::drop(p);
          pos_div_eucl_1(a_, b_1)
        },
        b::IntegerTag::Negative => {
          let b_clone_2 = Rc::clone(&b_1);
          let b_ = b::integer_magnitude(b_clone_2);
          let tmp_4 = b::identity(b_);
          let tmp_5 = pos_div_eucl_1(a_, tmp_4);
          match tmp_5 {
            (v62, v64) => {
              let q = &v64;
              let q_clone = Rc::clone(q);
              match b::integer_tag(q_clone) {
                b::IntegerTag::Zero => {
                  std::mem::drop(b_1);
                  std::mem::drop(a_1);
                  std::mem::drop(v64);
                  let tmp_6 = opp(v62);
                  let tmp_7 = b::zero();
                  (tmp_6, tmp_7)
                },
                b::IntegerTag::Positive => {
                  std::mem::drop(a_1);
                  let q_clone_1 = Rc::clone(q);
                  let p = b::integer_magnitude(q_clone_1);
                  std::mem::drop(p);
                  let tmp_8 = b::one();
                  let tmp_9 = b::identity(tmp_8);
                  let tmp_10 = add_1(v62, tmp_9);
                  let tmp_11 = opp(tmp_10);
                  let tmp_12 = add_1(b_1, v64);
                  (tmp_11, tmp_12)
                },
                b::IntegerTag::Negative => {
                  std::mem::drop(a_1);
                  let q_clone_2 = Rc::clone(q);
                  let p = b::integer_magnitude(q_clone_2);
                  std::mem::drop(p);
                  let tmp_13 = b::one();
                  let tmp_14 = b::identity(tmp_13);
                  let tmp_15 = add_1(v62, tmp_14);
                  let tmp_16 = opp(tmp_15);
                  let tmp_17 = add_1(b_1, v64);
                  (tmp_16, tmp_17)
                },
              }
            },
          }
        },
      }
    },
    b::IntegerTag::Negative => {
      let a_clone_2 = Rc::clone(&a_1);
      let a_ = b::integer_magnitude(a_clone_2);
      let b_clone_3 = Rc::clone(&b_1);
      let tmp_18 = b::integer_tag(b_clone_3);
      match &tmp_18 {
        b::IntegerTag::Zero => {
          std::mem::drop(a_);
          std::mem::drop(b_1);
          let tmp_19 = b::zero();
          (tmp_19, a_1)
        },
        b::IntegerTag::Positive => {
          let b_clone_4 = Rc::clone(&b_1);
          let p = b::integer_magnitude(b_clone_4);
          let b_clone_5 = Rc::clone(&b_1);
          let tmp_20 = pos_div_eucl_1(a_, b_clone_5);
          match tmp_20 {
            (v186, v188) => {
              let q = &v188;
              let q_clone_3 = Rc::clone(q);
              match b::integer_tag(q_clone_3) {
                b::IntegerTag::Zero => {
                  std::mem::drop(p);
                  std::mem::drop(b_1);
                  std::mem::drop(a_1);
                  std::mem::drop(v188);
                  let tmp_21 = opp(v186);
                  let tmp_22 = b::zero();
                  (tmp_21, tmp_22)
                },
                b::IntegerTag::Positive => {
                  std::mem::drop(p);
                  std::mem::drop(a_1);
                  let q_clone_4 = Rc::clone(q);
                  let p_1 = b::integer_magnitude(q_clone_4);
                  std::mem::drop(p_1);
                  let tmp_23 = b::one();
                  let tmp_24 = b::identity(tmp_23);
                  let tmp_25 = add_1(v186, tmp_24);
                  let tmp_26 = opp(tmp_25);
                  let tmp_27 = sub(b_1, v188);
                  (tmp_26, tmp_27)
                },
                b::IntegerTag::Negative => {
                  std::mem::drop(p);
                  std::mem::drop(a_1);
                  let q_clone_5 = Rc::clone(q);
                  let p_1 = b::integer_magnitude(q_clone_5);
                  std::mem::drop(p_1);
                  let tmp_28 = b::one();
                  let tmp_29 = b::identity(tmp_28);
                  let tmp_30 = add_1(v186, tmp_29);
                  let tmp_31 = opp(tmp_30);
                  let tmp_32 = sub(b_1, v188);
                  (tmp_31, tmp_32)
                },
              }
            },
          }
        },
        b::IntegerTag::Negative => {
          std::mem::drop(a_1);
          let b_ = b::integer_magnitude(b_1);
          let tmp_33 = b::identity(b_);
          let tmp_34 = pos_div_eucl_1(a_, tmp_33);
          match tmp_34 {
            (v289, v291) => {
              let tmp_35 = opp(v291);
              (v289, tmp_35)
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
  b::modulo(v0, v1)
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
  if ltb_2(tmp, b_clone) {
    let b_clone_1 = Rc::clone(&b_1);
    let tmp_1 = modulo(a_1, b_clone_1);
    zgcd_loop(b_1, tmp_1, ())
  } else {
    std::mem::drop(b_1);
    a_1
  }
}

// Rocq: StdGalilei.bigint.zgcd
// Variant: uncurried
pub fn zgcd_owned(a_1: Rc<BigInt>, b_1: Rc<BigInt>) -> Rc<BigInt> {
  let tmp = abs_owned(a_1);
  let tmp_1 = abs_owned(b_1);
  zgcd_loop_1(tmp, tmp_1)
}

// Rocq: StdGalilei.bigint.zgcd
// Variant: borrowed, uncurried
pub fn zgcd(a_1: &Rc<BigInt>, b_1: &Rc<BigInt>) -> Rc<BigInt> {
  let tmp = abs(a_1);
  let tmp_1 = abs(b_1);
  zgcd_loop_1(tmp, tmp_1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.row_gcd
// Variant: uncurried
pub fn row_gcd(T: Rc<Array<Rc<BigInt>>>, w: u64, i: u64) -> Rc<BigInt> {
  let callback: Rc<dyn Fn(u64, Rc<BigInt>) -> bool> = Rc::new(move |_v5: u64, v6: Rc<BigInt>| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<BigInt>) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_22 = w;
    move |j: u64, g: Rc<BigInt>| -> Rc<BigInt> {
      let i = &i;
      let w = &__anf_capture_22;
      let tmp = a::get::<Rc<BigInt>>(&T, add(mul(Clone::clone(i), Clone::clone(w)), j));
      zgcd_owned(g, tmp)
    }
  });
  let tmp_1 = b::zero();
  loop_::<Rc<BigInt>>(w, callback, callback_1, 0u64, tmp_1)
}

// Rocq: Corelib.BinNums.IntDef.Z.div
// Variant: uncurried
pub fn div_owned(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  b::div(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.div
// Variant: borrowed, uncurried
pub fn div(v0: &Rc<BigInt>, v1: &Rc<BigInt>) -> Rc<BigInt> {
  let tmp = Rc::clone(v0);
  let tmp_1 = Rc::clone(v1);
  b::div(tmp, tmp_1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.div_row
// Variant: uncurried
pub fn div_row(T: Rc<Array<Rc<BigInt>>>, w: u64, i: u64, g: Rc<BigInt>) -> Rc<Array<Rc<BigInt>>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = Rc::new(move |_v6: u64, v7: Rc<Array<Rc<BigInt>>>| -> bool {
    std::mem::drop(v7);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new({
    let __anf_capture_23 = w;
    move |j: u64, T: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let i = &i;
      let w = &__anf_capture_23;
      let g = &g;
      let tmp = add(mul(Clone::clone(i), Clone::clone(w)), j);
      let tmp_1 = a::get::<Rc<BigInt>>(&T, add(mul(Clone::clone(i), Clone::clone(w)), j));
      let g_clone = Rc::clone(g);
      let tmp_2 = div_owned(tmp_1, g_clone);
      a::set::<Rc<BigInt>>(T, tmp, tmp_2)
    }
  });
  loop_::<Rc<Array<Rc<BigInt>>>>(w, callback, callback_1, 0u64, T)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.elim_row
// Variant: uncurried
pub fn elim_row(w: u64, c: u64, r: u64, a_1: Rc<BigInt>, i: u64, T: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  if eqb(i, r) {
    std::mem::drop(a_1);
    T
  } else {
    let b_1 = a::get::<Rc<BigInt>>(&T, add(mul(i, w), c));
    let tmp = b::zero();
    let b_clone = Rc::clone(&b_1);
    if eqb_2(b_clone, tmp) {
      std::mem::drop(b_1);
      std::mem::drop(a_1);
      T
    } else {
      let T_1 = upd_row(T, w, i, r, a_1, b_1);
      let T_clone = Rc::clone(&T_1);
      let g = row_gcd(T_clone, w, i);
      let tmp_1 = b::one();
      let tmp_2 = b::identity(tmp_1);
      let g_clone = Rc::clone(&g);
      if ltb_2(tmp_2, g_clone) {
        div_row(T_1, w, i, g)
      } else {
        std::mem::drop(g);
        T_1
      }
    }
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.col_step
// Variant: uncurried
pub fn col_step(n: u64, w: u64, c: u64, st: (Rc<Array<Rc<BigInt>>>, u64)) -> (Rc<Array<Rc<BigInt>>>, u64) {
  match st {
    (v5, v7) => {
      let r = &v5;
      let r_clone = Rc::clone(r);
      let q = find_piv(r_clone, n, w, c, v7);
      if eqb(q, n) {
        (v5, v7)
      } else {
        let T = swap_rows(v5, w, q, v7);
        let a_1 = a::get::<Rc<BigInt>>(&T, add(mul(v7, w), c));
        let callback: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = Rc::new(move |_v65: u64, v66: Rc<Array<Rc<BigInt>>>| -> bool {
          std::mem::drop(v66);
          true
        });
        let callback_1: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new({
          let __anf_capture_82 = w;
          let __anf_capture_84 = c;
          let __anf_capture_86 = v7;
          move |v90: u64, v91: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
            let tmp = Clone::clone(&__anf_capture_82);
            let tmp_1 = Clone::clone(&__anf_capture_84);
            let tmp_2 = Clone::clone(&__anf_capture_86);
            let a_clone = Rc::clone(&a_1);
            elim_row(tmp, tmp_1, tmp_2, a_clone, v90, v91)
          }
        });
        let tmp_3 = loop_::<Rc<Array<Rc<BigInt>>>>(n, callback, callback_1, 0u64, T);
        (tmp_3, add(v7, 1u64))
      }
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.eliminate
// Variant: uncurried
pub fn eliminate(n: u64, w: u64, T: Rc<Array<Rc<BigInt>>>) -> (Rc<Array<Rc<BigInt>>>, u64) {
  let callback: Rc<dyn Fn(u64, (Rc<Array<Rc<BigInt>>>, u64)) -> bool> = Rc::new(move |_v5: u64, v6: (Rc<Array<Rc<BigInt>>>, u64)| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(u64, (Rc<Array<Rc<BigInt>>>, u64)) -> (Rc<Array<Rc<BigInt>>>, u64)> = Rc::new({
    let __anf_capture_18 = n;
    move |v22: u64, v23: (Rc<Array<Rc<BigInt>>>, u64)| -> (Rc<Array<Rc<BigInt>>>, u64) {
      let tmp = Clone::clone(&__anf_capture_18);
      let w_clone = Clone::clone(&w);
      col_step(tmp, w_clone, v22, v23)
    }
  });
  loop_::<(Rc<Array<Rc<BigInt>>>, u64)>(n, callback, callback_1, 0u64, (T, 0u64))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.inconsistent
// Variant: uncurried
pub fn inconsistent(T: Rc<Array<Rc<BigInt>>>, n: u64, w: u64, r: u64) -> bool {
  let callback: Rc<dyn Fn(u64, bool) -> bool> = Rc::new(move |_v6: u64, _v7: bool| -> bool {
    true
  });
  let callback_1: Rc<dyn Fn(u64, bool) -> bool> = Rc::new({
    let __anf_capture_23 = n;
    move |i: u64, fl: bool| -> bool {
      let w = &w;
      let n = &__anf_capture_23;
      let tmp = a::get::<Rc<BigInt>>(&T, add(mul(i, Clone::clone(w)), Clone::clone(n)));
      let tmp_1 = b::zero();
      orb(fl, negb(eqb_2(tmp, tmp_1)))
    }
  });
  loop_::<bool>(n, callback, callback_1, r, false)
}

// Rocq: Corelib.Floats.SpecFloat.digits2_pos
pub fn digits2_pos_1(n: Rc<BigInt>) -> Rc<BigInt> {
  digits2_pos(n)
}

// Rocq: Corelib.Floats.SpecFloat.digits2_pos (local: digits2_pos)
// Variant: lifted
pub fn digits2_pos(n: Rc<BigInt>) -> Rc<BigInt> {
  let n_clone = Rc::clone(&n);
  match b::positive_tag(n_clone) {
    b::PositiveTag::Odd => {
      let p = b::positive_tail(n);
      let tmp = digits2_pos(p);
      succ(tmp)
    },
    b::PositiveTag::Even => {
      let p = b::positive_tail(n);
      let tmp_1 = digits2_pos(p);
      succ(tmp_1)
    },
    b::PositiveTag::One => {
      std::mem::drop(n);
      b::one()
    },
  }
}

// Rocq: Corelib.Floats.SpecFloat.Zdigits2
pub fn Zdigits2(n: Rc<BigInt>) -> Rc<BigInt> {
  let n_clone = Rc::clone(&n);
  match b::integer_tag(n_clone) {
    b::IntegerTag::Zero => {
      n
    },
    b::IntegerTag::Positive => {
      let p = b::integer_magnitude(n);
      let tmp = digits2_pos_1(p);
      b::identity(tmp)
    },
    b::IntegerTag::Negative => {
      let p = b::integer_magnitude(n);
      let tmp_1 = digits2_pos_1(p);
      b::identity(tmp_1)
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.max
// Variant: uncurried
pub fn max(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  b::max(v0, v1)
}

// Rocq: Corelib.Floats.SpecFloat.emin
// Variant: uncurried
pub fn emin(prec_1: Rc<BigInt>, emax_1: Rc<BigInt>) -> Rc<BigInt> {
  let tmp = b::one();
  let tmp_1 = b::twice_plus_one(tmp);
  let tmp_2 = b::identity(tmp_1);
  let tmp_3 = sub(tmp_2, emax_1);
  sub(tmp_3, prec_1)
}

// Rocq: Corelib.Floats.SpecFloat.fexp
// Variant: uncurried
pub fn fexp(prec_1: Rc<BigInt>, emax_1: Rc<BigInt>, e: Rc<BigInt>) -> Rc<BigInt> {
  let prec_clone = Rc::clone(&prec_1);
  let tmp = sub(e, prec_clone);
  let tmp_1 = emin(prec_1, emax_1);
  max(tmp, tmp_1)
}

// Rocq: Corelib.BinNums.IntDef.Z.even
pub fn even(v0: Rc<BigInt>) -> bool {
  b::even(v0)
}

// Rocq: Corelib.Floats.SpecFloat.new_location_even
// Variant: uncurried
pub fn new_location_even(nb_steps: Rc<BigInt>, k: Rc<BigInt>) -> Rc<location> {
  let tmp = b::zero();
  let k_clone = Rc::clone(&k);
  if eqb_2(k_clone, tmp) {
    std::mem::drop(nb_steps);
    std::mem::drop(k);
    Rc::new(location::loc_Exact)
  } else {
    let tmp_1 = b::one();
    let tmp_2 = b::twice(tmp_1);
    let tmp_3 = b::identity(tmp_2);
    let tmp_4 = mul_2(tmp_3, k);
    Rc::new(location::loc_Inexact(compare(tmp_4, nb_steps)))
  }
}

// Rocq: Corelib.Floats.SpecFloat.new_location_odd
// Variant: uncurried
pub fn new_location_odd(nb_steps: Rc<BigInt>, k: Rc<BigInt>) -> Rc<location> {
  let tmp = b::zero();
  let k_clone = Rc::clone(&k);
  if eqb_2(k_clone, tmp) {
    std::mem::drop(nb_steps);
    std::mem::drop(k);
    Rc::new(location::loc_Exact)
  } else {
    let tmp_1 = b::one();
    let tmp_2 = b::twice(tmp_1);
    let tmp_3 = b::identity(tmp_2);
    let tmp_4 = mul_2(tmp_3, k);
    let tmp_5 = b::one();
    let tmp_6 = b::identity(tmp_5);
    let tmp_7 = add_1(tmp_4, tmp_6);
    let tmp_8 = match compare(tmp_7, nb_steps) {
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
    Rc::new(location::loc_Inexact(tmp_8))
  }
}

// Rocq: Corelib.Floats.SpecFloat.new_location
pub fn new_location(nb_steps: Rc<BigInt>) -> Rc<dyn Fn(Rc<BigInt>) -> Rc<location>> {
  let nb_steps_clone = Rc::clone(&nb_steps);
  let tmp: Rc<dyn Fn(Rc<BigInt>) -> Rc<location>> = if even(nb_steps_clone) {
    let callback: Rc<dyn Fn(Rc<BigInt>) -> Rc<location>> = Rc::new({
      let __anf_capture_10 = nb_steps;
      move |v12: Rc<BigInt>| -> Rc<location> {
        let tmp_1 = Rc::clone(&__anf_capture_10);
        new_location_even(tmp_1, v12)
      }
    });
    callback
  } else {
    let callback_1: Rc<dyn Fn(Rc<BigInt>) -> Rc<location>> = Rc::new({
      let __anf_capture_28 = nb_steps;
      move |v30: Rc<BigInt>| -> Rc<location> {
        let tmp_2 = Rc::clone(&__anf_capture_28);
        new_location_odd(tmp_2, v30)
      }
    });
    callback_1
  };
  tmp
}

// Rocq: Corelib.Floats.SpecFloat.SFdiv_core_binary
// Variant: uncurried
pub fn SFdiv_core_binary(prec_1: Rc<BigInt>, emax_1: Rc<BigInt>, m1: Rc<BigInt>, e1: Rc<BigInt>, m2: Rc<BigInt>, e2: Rc<BigInt>) -> ((Rc<BigInt>, Rc<BigInt>), Rc<location>) {
  let m1_clone = Rc::clone(&m1);
  let d1_1 = Zdigits2(m1_clone);
  let m2_clone = Rc::clone(&m2);
  let d2 = Zdigits2(m2_clone);
  let e1_clone = Rc::clone(&e1);
  let tmp = add_1(d1_1, e1_clone);
  let e2_clone = Rc::clone(&e2);
  let tmp_1 = add_1(d2, e2_clone);
  let tmp_2 = sub(tmp, tmp_1);
  let tmp_3 = fexp(prec_1, emax_1, tmp_2);
  let e1_clone_1 = Rc::clone(&e1);
  let e2_clone_1 = Rc::clone(&e2);
  let tmp_4 = sub(e1_clone_1, e2_clone_1);
  let e_ = min(tmp_3, tmp_4);
  let tmp_5 = sub(e1, e2);
  let e__clone = Rc::clone(&e_);
  let s = sub(tmp_5, e__clone);
  let s_clone = Rc::clone(&s);
  let m_ = match b::integer_tag(s_clone) {
    b::IntegerTag::Zero => {
      std::mem::drop(s);
      m1
    },
    b::IntegerTag::Positive => {
      let s_clone_1 = Rc::clone(&s);
      let p = b::integer_magnitude(s_clone_1);
      std::mem::drop(p);
      shiftl(m1, s)
    },
    b::IntegerTag::Negative => {
      std::mem::drop(m1);
      let p = b::integer_magnitude(s);
      std::mem::drop(p);
      b::zero()
    },
  };
  let m2_clone_1 = Rc::clone(&m2);
  let tmp_6 = div_eucl(m_, m2_clone_1);
  match tmp_6 {
    (v105, v107) => {
      let tmp_7 = (v105, e_);
      let tmp_8: Rc<dyn Fn(Rc<BigInt>) -> Rc<location>> = new_location(m2);
      let tmp_9: &Rc<dyn Fn(Rc<BigInt>) -> Rc<location>> = &tmp_8;
      let tmp_10 = tmp_9(v107);
      std::mem::drop(tmp_8);
      (tmp_7, tmp_10)
    },
  }
}

// Rocq: Corelib.Floats.FloatOps.emax
pub fn emax(_v0: ()) -> Rc<BigInt> {
  let tmp = b::one();
  let tmp_1 = b::twice(tmp);
  let tmp_2 = b::twice(tmp_1);
  let tmp_3 = b::twice(tmp_2);
  let tmp_4 = b::twice(tmp_3);
  let tmp_5 = b::twice(tmp_4);
  let tmp_6 = b::twice(tmp_5);
  let tmp_7 = b::twice(tmp_6);
  let tmp_8 = b::twice(tmp_7);
  let tmp_9 = b::twice(tmp_8);
  let tmp_10 = b::twice(tmp_9);
  b::identity(tmp_10)
}

// Rocq: Corelib.Floats.SpecFloat.iter_pos
// Variant: uncurried
pub fn iter_pos_1<A: Clone + 'static>(f: Rc<dyn Fn(A) -> A>, n: Rc<BigInt>) -> Rc<dyn Fn(A) -> A> {
  let tmp: Rc<dyn Fn(A) -> A> = iter_pos_curried_owned::<A>(f, n);
  tmp
}

// Rocq: Corelib.Floats.SpecFloat.iter_pos (local: iter_pos)
// Variant: lifted
pub fn iter_pos_curried_owned<A: Clone + 'static>(f: Rc<dyn Fn(A) -> A>, n: Rc<BigInt>) -> Rc<dyn Fn(A) -> A> {
  let callback: Rc<dyn Fn(A) -> A> = Rc::new({
    move |x: A| -> A {
      let f = &f;
      let n = &n;
      let tmp = iter_pos::<A>(f, n, x);
      tmp
    }
  });
  callback
}

// Rocq: Corelib.Floats.SpecFloat.iter_pos (local: iter_pos)
// Variant: uncurried, lifted
pub fn iter_pos_owned<A: Clone + 'static>(f: Rc<dyn Fn(A) -> A>, n: Rc<BigInt>, x: A) -> A {
  let n_clone = Rc::clone(&n);
  match b::positive_tag(n_clone) {
    b::PositiveTag::Odd => {
      let n_ = b::positive_tail(n);
      let f_ref: &Rc<dyn Fn(A) -> A> = &f;
      let tmp = f_ref(x);
      let f_clone: Rc<dyn Fn(A) -> A> = Rc::clone(&f);
      let n__clone = Rc::clone(&n_);
      let tmp_1 = iter_pos_owned::<A>(f_clone, n__clone, tmp);
      iter_pos_owned::<A>(f, n_, tmp_1)
    },
    b::PositiveTag::Even => {
      let n_ = b::positive_tail(n);
      let f_clone_1: Rc<dyn Fn(A) -> A> = Rc::clone(&f);
      let n__clone_1 = Rc::clone(&n_);
      let tmp_2 = iter_pos_owned::<A>(f_clone_1, n__clone_1, x);
      iter_pos_owned::<A>(f, n_, tmp_2)
    },
    b::PositiveTag::One => {
      std::mem::drop(n);
      let f_ref_1: &Rc<dyn Fn(A) -> A> = &f;
      let tmp_3 = f_ref_1(x);
      std::mem::drop(f);
      tmp_3
    },
  }
}

// Rocq: Corelib.Floats.SpecFloat.iter_pos (local: iter_pos)
// Variant: borrowed, uncurried, lifted
pub fn iter_pos<A: Clone + 'static>(f: &Rc<dyn Fn(A) -> A>, n: &Rc<BigInt>, x: A) -> A {
  let x_1 = x;
  let n_clone = Rc::clone(n);
  match b::positive_tag(n_clone) {
    b::PositiveTag::Odd => {
      let n_clone_1 = Rc::clone(n);
      let n_ = b::positive_tail(n_clone_1);
      let tmp = f(x_1);
      let f_clone: Rc<dyn Fn(A) -> A> = Rc::clone(f);
      let n__clone = Rc::clone(&n_);
      let tmp_1 = iter_pos_owned::<A>(f_clone, n__clone, tmp);
      let f_clone_1: Rc<dyn Fn(A) -> A> = Rc::clone(f);
      iter_pos_owned::<A>(f_clone_1, n_, tmp_1)
    },
    b::PositiveTag::Even => {
      let n_clone_2 = Rc::clone(n);
      let n_ = b::positive_tail(n_clone_2);
      let f_clone_2: Rc<dyn Fn(A) -> A> = Rc::clone(f);
      let n__clone_1 = Rc::clone(&n_);
      let tmp_2 = iter_pos_owned::<A>(f_clone_2, n__clone_1, x_1);
      let f_clone_3: Rc<dyn Fn(A) -> A> = Rc::clone(f);
      iter_pos_owned::<A>(f_clone_3, n_, tmp_2)
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
      let s_clone = Rc::clone(s);
      match b::integer_tag(s_clone) {
        b::IntegerTag::Zero => {
          std::mem::drop(v9);
          let tmp = b::zero();
          __rocq_reuse::rebuild(v2, shr_record { shr_m: tmp, shr_r: false, shr_s: s_1 })
        },
        b::IntegerTag::Positive => {
          let p0 = b::integer_magnitude(v9);
          let p0_clone = Rc::clone(&p0);
          match b::positive_tag(p0_clone) {
            b::PositiveTag::Odd => {
              let p = b::positive_tail(p0);
              let tmp_1 = b::identity(p);
              __rocq_reuse::rebuild(v2, shr_record { shr_m: tmp_1, shr_r: true, shr_s: s_1 })
            },
            b::PositiveTag::Even => {
              let p = b::positive_tail(p0);
              let tmp_2 = b::identity(p);
              __rocq_reuse::rebuild(v2, shr_record { shr_m: tmp_2, shr_r: false, shr_s: s_1 })
            },
            b::PositiveTag::One => {
              std::mem::drop(p0);
              let tmp_3 = b::zero();
              __rocq_reuse::rebuild(v2, shr_record { shr_m: tmp_3, shr_r: true, shr_s: s_1 })
            },
          }
        },
        b::IntegerTag::Negative => {
          let p0 = b::integer_magnitude(v9);
          let p0_clone_1 = Rc::clone(&p0);
          match b::positive_tag(p0_clone_1) {
            b::PositiveTag::Odd => {
              let p = b::positive_tail(p0);
              let tmp_4 = b::neg(p);
              __rocq_reuse::rebuild(v2, shr_record { shr_m: tmp_4, shr_r: true, shr_s: s_1 })
            },
            b::PositiveTag::Even => {
              let p = b::positive_tail(p0);
              let tmp_5 = b::neg(p);
              __rocq_reuse::rebuild(v2, shr_record { shr_m: tmp_5, shr_r: false, shr_s: s_1 })
            },
            b::PositiveTag::One => {
              std::mem::drop(p0);
              let tmp_6 = b::zero();
              __rocq_reuse::rebuild(v2, shr_record { shr_m: tmp_6, shr_r: true, shr_s: s_1 })
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
  let n_clone = Rc::clone(&n);
  match b::integer_tag(n_clone) {
    b::IntegerTag::Zero => {
      std::mem::drop(n);
      (mrs, e)
    },
    b::IntegerTag::Positive => {
      let n_clone_1 = Rc::clone(&n);
      let p = b::integer_magnitude(n_clone_1);
      let tmp: fn(Rc<shr_record>) -> Rc<shr_record> = shr_1;
      let tmp_1: Rc<dyn Fn(Rc<shr_record>) -> Rc<shr_record>> = Rc::new(tmp);
      let tmp_2: Rc<dyn Fn(Rc<shr_record>) -> Rc<shr_record>> = iter_pos_1::<Rc<shr_record>>(tmp_1, p);
      let tmp_3: &Rc<dyn Fn(Rc<shr_record>) -> Rc<shr_record>> = &tmp_2;
      let tmp_4 = tmp_3(mrs);
      std::mem::drop(tmp_2);
      let tmp_5 = add_1(e, n);
      (tmp_4, tmp_5)
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
  let m_clone = Rc::clone(&m);
  let tmp = shr_record_of_loc(m_clone, l);
  let tmp_1 = Zdigits2(m);
  let e_clone = Rc::clone(&e);
  let tmp_2 = add_1(tmp_1, e_clone);
  let tmp_3 = fexp(prec_1, emax_1, tmp_2);
  let e_clone_1 = Rc::clone(&e);
  let tmp_4 = sub(tmp_3, e_clone_1);
  shr(tmp, e, tmp_4)
}

// Rocq: Corelib.Floats.SpecFloat.round_nearest_even
// Variant: uncurried
pub fn round_nearest_even(mx: Rc<BigInt>, lx: Rc<location>) -> Rc<BigInt> {
  let (v2, v3) = __rocq_reuse::reset(lx, |__payload| Clone::clone(__payload));
  std::mem::drop(v3);
  match v2 {
    location::loc_Exact => {
      mx
    },
    location::loc_Inexact(v10) => {
      match v10 {
        std::cmp::Ordering::Equal => {
          let mx_clone = Rc::clone(&mx);
          if even(mx_clone) {
            mx
          } else {
            let tmp = b::one();
            let tmp_1 = b::identity(tmp);
            add_1(mx, tmp_1)
          }
        },
        std::cmp::Ordering::Less => {
          mx
        },
        std::cmp::Ordering::Greater => {
          let tmp_2 = b::one();
          let tmp_3 = b::identity(tmp_2);
          add_1(mx, tmp_3)
        },
      }
    },
  }
}

// Rocq: Corelib.Floats.SpecFloat.shr_m
pub fn shr_m_owned(s: Rc<shr_record>) -> Rc<BigInt> {
  let s_shr_m_clone = Rc::clone(&s.shr_m);
  std::mem::drop(s);
  s_shr_m_clone
}

// Rocq: Corelib.Floats.SpecFloat.shr_m
// Variant: borrowed
pub fn shr_m(s: &Rc<shr_record>) -> Rc<BigInt> {
  let tmp = s;
  Rc::clone(&tmp.shr_m)
}

// Rocq: Corelib.Floats.SpecFloat.loc_of_shr_record
pub fn loc_of_shr_record(mrs: Rc<shr_record>) -> Rc<location> {
  let (v1, v2) = __rocq_reuse::reset(mrs, |__payload| Clone::clone(__payload));
  std::mem::drop(v2);
  match v1 {
    shr_record { shr_m: v9, shr_r: v11, shr_s: v13 } => {
      let shr_m_1 = &v13;
      if v11 {
        if *shr_m_1 {
          std::mem::drop(v9);
          Rc::new(location::loc_Inexact(std::cmp::Ordering::Greater))
        } else {
          std::mem::drop(v9);
          Rc::new(location::loc_Inexact(std::cmp::Ordering::Equal))
        }
      } else {
        if *shr_m_1 {
          std::mem::drop(v9);
          Rc::new(location::loc_Inexact(std::cmp::Ordering::Less))
        } else {
          std::mem::drop(v9);
          Rc::new(location::loc_Exact)
        }
      }
    },
  }
}

// Rocq: Corelib.Floats.SpecFloat.binary_round_aux
// Variant: uncurried
pub fn binary_round_aux(prec_1: Rc<BigInt>, emax_1: Rc<BigInt>, sx: bool, mx: Rc<BigInt>, ex: Rc<BigInt>, lx: Rc<location>) -> Rc<spec_float> {
  let prec_clone = Rc::clone(&prec_1);
  let emax_clone = Rc::clone(&emax_1);
  let tmp = shr_fexp(prec_clone, emax_clone, mx, ex, lx);
  match tmp {
    (v21, v23) => {
      let e_ = &v21;
      let tmp_1 = shr_m(e_);
      let tmp_2 = round_nearest_even(tmp_1, loc_of_shr_record(v21));
      let tmp_3 = Rc::new(location::loc_Exact);
      let prec_clone_1 = Rc::clone(&prec_1);
      let emax_clone_1 = Rc::clone(&emax_1);
      let tmp_4 = shr_fexp(prec_clone_1, emax_clone_1, tmp_2, v23, tmp_3);
      match tmp_4 {
        (v57, v59) => {
          let mrs__ = &v59;
          let tmp_5 = shr_m_owned(v57);
          let tmp_6 = Rc::clone(&tmp_5);
          match b::integer_tag(tmp_6) {
            b::IntegerTag::Zero => {
              std::mem::drop(tmp_5);
              std::mem::drop(emax_1);
              std::mem::drop(prec_1);
              std::mem::drop(v59);
              Rc::new(spec_float::S754_zero { s: sx })
            },
            b::IntegerTag::Positive => {
              let m = b::integer_magnitude(tmp_5);
              let tmp_7 = sub(emax_1, prec_1);
              let mrs___clone = Rc::clone(mrs__);
              if leb_owned(mrs___clone, tmp_7) {
                Rc::new(spec_float::S754_finite { s: sx, m, e: v59 })
              } else {
                std::mem::drop(m);
                std::mem::drop(v59);
                Rc::new(spec_float::S754_infinity { s: sx })
              }
            },
            b::IntegerTag::Negative => {
              std::mem::drop(emax_1);
              std::mem::drop(prec_1);
              std::mem::drop(v59);
              let p = b::integer_magnitude(tmp_5);
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
  if b1 {
    if b2 {
      false
    } else {
      true
    }
  } else {
    b2
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
  let tmp = emax(());
  let tmp_1 = prec(());
  let tmp_2 = emax(());
  let tmp_3 = emin(tmp_1, tmp_2);
  let tmp_4 = sub(tmp, tmp_3);
  let e_clone = Rc::clone(e);
  let tmp_5 = min(e_clone, tmp_4);
  let tmp_6 = prec(());
  let tmp_7 = emax(());
  let tmp_8 = emin(tmp_6, tmp_7);
  let tmp_9 = emax(());
  let tmp_10 = sub(tmp_8, tmp_9);
  let tmp_11 = b::one();
  let tmp_12 = b::identity(tmp_11);
  let tmp_13 = sub(tmp_10, tmp_12);
  let e_ = max(tmp_5, tmp_13);
  let tmp_14 = shift(());
  let tmp_15 = add_1(e_, tmp_14);
  ldshiftexp(f_1, z2i(tmp_15))
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
      if v11 {
        __rocq_global_3377
      } else {
        __rocq_global_371
      }
    },
    spec_float::S754_infinity { s: v23 } => {
      if v23 {
        __rocq_global_3380
      } else {
        __rocq_global_1215
      }
    },
    spec_float::S754_nan => {
      __rocq_global_3383
    },
    spec_float::S754_finite { s: v38, m: v40, e: v42 } => {
      let e = &v38;
      let s = &v42;
      let tmp = b::identity(v40);
      let pm = of_uint63(z2i(tmp));
      let f = ldexp_(pm, s);
      if *e {
        std::mem::drop(v42);
        opp_1(f)
      } else {
        std::mem::drop(v42);
        f
      }
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.qr
// Variant: uncurried
pub fn qr(sx: bool, mx: Rc<BigInt>, sy: bool, my: Rc<BigInt>) -> f64 {
  let tmp = prec(());
  let tmp_1 = emax(());
  let tmp_2 = b::identity(mx);
  let tmp_3 = b::zero();
  let tmp_4 = b::identity(my);
  let tmp_5 = b::zero();
  let tmp_6 = SFdiv_core_binary(tmp, tmp_1, tmp_2, tmp_3, tmp_4, tmp_5);
  match &tmp_6 {
    (lz, p) => {
      match lz {
        (ez, mz) => {
          let tmp_7 = prec(());
          let tmp_8 = emax(());
          let tmp_9 = xorb(sx, sy);
          let ez_clone = Rc::clone(ez);
          let mz_clone = Rc::clone(mz);
          let p_clone = Rc::clone(p);
          let tmp_10 = binary_round_aux(tmp_7, tmp_8, tmp_9, ez_clone, mz_clone, p_clone);
          let (v81, v82) = __rocq_reuse::reset(tmp_10, |__payload| Clone::clone(__payload));
          match v81 {
            spec_float::S754_zero { s: _v91 } => {
              std::mem::drop(v82);
              std::mem::drop(tmp_6);
              __rocq_global_371
            },
            spec_float::S754_infinity { s: _v96 } => {
              std::mem::drop(v82);
              std::mem::drop(tmp_6);
              __rocq_global_371
            },
            spec_float::S754_nan => {
              std::mem::drop(v82);
              std::mem::drop(tmp_6);
              __rocq_global_371
            },
            spec_float::S754_finite { s: v104, m: v106, e: v108 } => {
              std::mem::drop(tmp_6);
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
  let num_clone = Rc::clone(&num);
  match b::integer_tag(num_clone) {
    b::IntegerTag::Zero => {
      std::mem::drop(num);
      std::mem::drop(den);
      __rocq_global_371
    },
    b::IntegerTag::Positive => {
      let mx = b::integer_magnitude(num);
      let den_clone = Rc::clone(&den);
      match b::integer_tag(den_clone) {
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
      let den_clone_1 = Rc::clone(&den);
      match b::integer_tag(den_clone_1) {
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
  let callback: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(move |_v5: u64, v6: Rc<Array<f64>>| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new({
    let __anf_capture_20 = n;
    move |i: u64, out: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let n = &__anf_capture_20;
      let w = &w;
      let tmp = a::get::<Rc<BigInt>>(&T, add(mul(i, Clone::clone(w)), Clone::clone(n)));
      let tmp_1 = a::get::<Rc<BigInt>>(&T, add(mul(i, Clone::clone(w)), i));
      a::set::<f64>(out, i, qround(tmp, tmp_1))
    }
  });
  let tmp_2 = a::make::<f64>(n, __rocq_global_371);
  loop_::<Rc<Array<f64>>>(n, callback, callback_1, 0u64, tmp_2)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.solve_exact
// Variant: uncurried
pub fn solve_exact(n: u64, a_1: Rc<Array<Rc<Array<f64>>>>, b_1: Rc<Array<f64>>) -> Rc<outcome<Rc<Array<f64>>>> {
  let w = add(n, 1u64);
  let T = build(a_1, b_1, n, w);
  let tmp = eliminate(n, w, T);
  match tmp {
    (v30, v32) => {
      let r = &v30;
      let r_clone = Rc::clone(r);
      if inconsistent(r_clone, n, w, v32) {
        std::mem::drop(v30);
        Rc::new(outcome::<Rc<Array<f64>>>::Inconsistent)
      } else {
        if ltb(v32, n) {
          std::mem::drop(v30);
          Rc::new(outcome::<Rc<Array<f64>>>::Multiple)
        } else {
          let tmp_1 = output(v30, n, w);
          Rc::new(outcome::<Rc<Array<f64>>>::Unique(tmp_1))
        }
      }
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.free_cols
// Variant: uncurried
pub fn free_cols(pc: Rc<Array<u64>>, n: u64, r: u64) -> Rc<Array<u64>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<bool>>) -> bool> = Rc::new(move |_v5: u64, v6: Rc<Array<bool>>| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new({
    move |t: u64, isp: Rc<Array<bool>>| -> Rc<Array<bool>> {
      let tmp = a::get::<u64>(&pc, t);
      a::set::<bool>(isp, tmp, true)
    }
  });
  let tmp_1 = a::make::<bool>(n, false);
  let isp = loop_::<Rc<Array<bool>>>(r, callback, callback_1, 0u64, tmp_1);
  let callback_2: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> bool> = Rc::new(move |_v59: u64, v60: (Rc<Array<u64>>, u64)| -> bool {
    std::mem::drop(v60);
    true
  });
  let callback_3: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> (Rc<Array<u64>>, u64)> = Rc::new({
    move |c: u64, st: (Rc<Array<u64>>, u64)| -> (Rc<Array<u64>>, u64) {
      let isp = &isp;
      match st {
        (v75, v77) => {
          if a::get::<bool>(isp, c) {
            (v75, v77)
          } else {
            let tmp_2 = a::set::<u64>(v75, v77, c);
            (tmp_2, add(v77, 1u64))
          }
        },
      }
    }
  });
  let tmp_3 = a::make::<u64>(n, 0u64);
  fst::<Rc<Array<u64>>, u64>(loop_::<(Rc<Array<u64>>, u64)>(n, callback_2, callback_3, 0u64, (tmp_3, 0u64)))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.mark_D
// Variant: uncurried
pub fn mark_D(perm: Rc<Array<u64>>, n: u64, r: u64, k: u64) -> (Rc<Array<bool>>, Rc<Array<u64>>) {
  let callback: Rc<dyn Fn(u64, (Rc<Array<bool>>, Rc<Array<u64>>)) -> bool> = Rc::new(move |_v6: u64, v7: (Rc<Array<bool>>, Rc<Array<u64>>)| -> bool {
    std::mem::drop(v7);
    true
  });
  let callback_1: Rc<dyn Fn(u64, (Rc<Array<bool>>, Rc<Array<u64>>)) -> (Rc<Array<bool>>, Rc<Array<u64>>)> = Rc::new({
    move |t: u64, st: (Rc<Array<bool>>, Rc<Array<u64>>)| -> (Rc<Array<bool>>, Rc<Array<u64>>) {
      let r = &r;
      let d = a::get::<u64>(&perm, add(Clone::clone(r), t));
      let st_clone = Clone::clone(&st);
      let tmp = fst::<Rc<Array<bool>>, Rc<Array<u64>>>(st_clone);
      let tmp_1 = a::set::<bool>(tmp, d, true);
      let tmp_2 = snd::<Rc<Array<bool>>, Rc<Array<u64>>>(st);
      let tmp_3 = a::set::<u64>(tmp_2, d, t);
      (tmp_1, tmp_3)
    }
  });
  let tmp_4 = a::make::<bool>(n, false);
  let tmp_5 = a::make::<u64>(n, 0u64);
  loop_::<(Rc<Array<bool>>, Rc<Array<u64>>)>(k, callback, callback_1, 0u64, (tmp_4, tmp_5))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.mark_C
// Variant: uncurried
pub fn mark_C(fc: Rc<Array<u64>>, n: u64, k: u64) -> Rc<Array<bool>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<bool>>) -> bool> = Rc::new(move |_v5: u64, v6: Rc<Array<bool>>| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new({
    move |t: u64, C: Rc<Array<bool>>| -> Rc<Array<bool>> {
      let tmp = a::get::<u64>(&fc, t);
      a::set::<bool>(C, tmp, true)
    }
  });
  let tmp_1 = a::make::<bool>(n, false);
  loop_::<Rc<Array<bool>>>(k, callback, callback_1, 0u64, tmp_1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.rat1
pub fn rat1(f: f64) -> (Rc<BigInt>, Rc<BigInt>) {
  let tmp = dec(f);
  match tmp {
    (v6, v8) => {
      let e = &v6;
      let m = &v8;
      let tmp_1 = b::zero();
      let m_clone = Rc::clone(m);
      if leb_owned(tmp_1, m_clone) {
        let tmp_2 = shiftl(v6, v8);
        let tmp_3 = b::one();
        let tmp_4 = b::identity(tmp_3);
        (tmp_2, tmp_4)
      } else {
        let tmp_5 = b::one();
        let tmp_6 = b::identity(tmp_5);
        let tmp_7 = opp(v8);
        let den = shiftl(tmp_6, tmp_7);
        let tmp_8 = 64u64;
        let callback: Rc<dyn Fn(u64, ((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool)) -> bool> = Rc::new(move |_v56: u64, st: ((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool)| -> bool {
          negb(snd::<(((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool>(st))
        });
        let den_clone = Rc::clone(&den);
        let e_clone = Rc::clone(e);
        let callback_1: Rc<dyn Fn(u64, ((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool)) -> ((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool)> = Rc::new({
          move |_v80: u64, st: ((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool)| -> ((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool) {
            let den = &den_clone;
            let e = &e_clone;
            let st_clone = Clone::clone(&st);
            let tmp_9 = fst::<(((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool>(st_clone);
            match tmp_9 {
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
                                let q_clone = Rc::clone(&q);
                                let y2_clone = Rc::clone(y2);
                                let tmp_10 = mul_2(q_clone, y2_clone);
                                let h = add_1(tmp_10, v101);
                                let q_clone_1 = Rc::clone(&q);
                                let y0_clone = Rc::clone(y0);
                                let tmp_11 = mul_2(q_clone_1, y0_clone);
                                let k = add_1(tmp_11, v90);
                                let tmp_12 = b::one();
                                let tmp_13 = b::twice(tmp_12);
                                let tmp_14 = b::twice(tmp_13);
                                let tmp_15 = b::twice(tmp_14);
                                let tmp_16 = b::twice(tmp_15);
                                let tmp_17 = b::twice(tmp_16);
                                let tmp_18 = b::twice(tmp_17);
                                let tmp_19 = b::twice(tmp_18);
                                let tmp_20 = b::twice(tmp_19);
                                let tmp_21 = b::twice(tmp_20);
                                let tmp_22 = b::twice(tmp_21);
                                let tmp_23 = b::twice(tmp_22);
                                let tmp_24 = b::twice(tmp_23);
                                let tmp_25 = b::twice(tmp_24);
                                let tmp_26 = b::twice(tmp_25);
                                let tmp_27 = b::twice(tmp_26);
                                let tmp_28 = b::twice(tmp_27);
                                let tmp_29 = b::twice(tmp_28);
                                let tmp_30 = b::twice(tmp_29);
                                let tmp_31 = b::twice(tmp_30);
                                let tmp_32 = b::twice(tmp_31);
                                let tmp_33 = b::twice(tmp_32);
                                let tmp_34 = b::twice(tmp_33);
                                let tmp_35 = b::twice(tmp_34);
                                let tmp_36 = b::twice(tmp_35);
                                let tmp_37 = b::twice(tmp_36);
                                let tmp_38 = b::twice(tmp_37);
                                let tmp_39 = b::twice(tmp_38);
                                let tmp_40 = b::twice(tmp_39);
                                let tmp_41 = b::twice(tmp_40);
                                let tmp_42 = b::twice(tmp_41);
                                let tmp_43 = b::identity(tmp_42);
                                let k_clone = Rc::clone(&k);
                                if ltb_2(tmp_43, k_clone) {
                                  std::mem::drop(k);
                                  std::mem::drop(h);
                                  std::mem::drop(q);
                                  std::mem::drop(v106);
                                  std::mem::drop(v95);
                                  std::mem::drop(v112);
                                  std::mem::drop(v110);
                                  (fst::<(((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool>(st), true)
                                } else {
                                  std::mem::drop(st);
                                  let an_clone = Rc::clone(an);
                                  let tmp_44 = mul_2(q, an_clone);
                                  let rem = sub(v110, tmp_44);
                                  let e_clone_1 = Rc::clone(e);
                                  let k_clone_1 = Rc::clone(&k);
                                  let tmp_45 = mul_2(e_clone_1, k_clone_1);
                                  let h_clone = Rc::clone(&h);
                                  let den_clone_1 = Rc::clone(den);
                                  let tmp_46 = mul_2(h_clone, den_clone_1);
                                  let tmp_47 = sub(tmp_45, tmp_46);
                                  let tmp_48 = abs_owned(tmp_47);
                                  let tmp_49 = b::one();
                                  let tmp_50 = b::twice(tmp_49);
                                  let tmp_51 = b::twice_plus_one(tmp_50);
                                  let tmp_52 = b::twice(tmp_51);
                                  let tmp_53 = b::twice(tmp_52);
                                  let tmp_54 = b::twice(tmp_53);
                                  let tmp_55 = b::identity(tmp_54);
                                  let tmp_56 = shiftl(tmp_48, tmp_55);
                                  let tmp_57 = abs(e);
                                  let k_clone_2 = Rc::clone(&k);
                                  let tmp_58 = mul_2(tmp_57, k_clone_2);
                                  let close = leb_owned(tmp_56, tmp_58);
                                  let rem_clone = Rc::clone(&rem);
                                  let tmp_59 = (((((v112, rem_clone), h), v106), k), v95);
                                  let tmp_60 = b::zero();
                                  (tmp_59, orb(eqb_2(rem, tmp_60), close))
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
        });
        let tmp_61 = (v6, den);
        let tmp_62 = b::one();
        let tmp_63 = b::identity(tmp_62);
        let tmp_64 = (tmp_61, tmp_63);
        let tmp_65 = b::zero();
        let tmp_66 = (tmp_64, tmp_65);
        let tmp_67 = b::zero();
        let tmp_68 = (tmp_66, tmp_67);
        let tmp_69 = b::one();
        let tmp_70 = b::identity(tmp_69);
        let st = loop_::<((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool)>(tmp_8, callback, callback_1, 0u64, ((tmp_68, tmp_70), false));
        let tmp_71 = fst::<(((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool>(st);
        match tmp_71 {
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
                            let tmp_72 = b::zero();
                            let p0_clone = Rc::clone(p0);
                            if ltb_2(tmp_72, p0_clone) {
                              std::mem::drop(v498);
                              std::mem::drop(v500);
                              std::mem::drop(v490);
                              std::mem::drop(v479);
                              (v495, v484)
                            } else {
                              std::mem::drop(v498);
                              std::mem::drop(v500);
                              std::mem::drop(v490);
                              std::mem::drop(v479);
                              std::mem::drop(v495);
                              std::mem::drop(v484);
                              let tmp_73 = b::zero();
                              let tmp_74 = b::one();
                              let tmp_75 = b::identity(tmp_74);
                              (tmp_73, tmp_75)
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
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.ratvec
// Variant: uncurried
pub fn ratvec(x: Rc<Array<f64>>, n: u64) -> (Rc<Array<Rc<BigInt>>>, Rc<BigInt>) {
  let callback: Rc<dyn Fn(u64, ((Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>), Rc<BigInt>)) -> bool> = Rc::new(move |_v4: u64, v5: ((Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>), Rc<BigInt>)| -> bool {
    std::mem::drop(v5);
    true
  });
  let callback_1: Rc<dyn Fn(u64, ((Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>), Rc<BigInt>)) -> ((Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>), Rc<BigInt>)> = Rc::new({
    move |j: u64, st: ((Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>), Rc<BigInt>)| -> ((Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>), Rc<BigInt>) {
      let x = &x;
      match st {
        (v20, v22) => {
          let y = &v22;
          match v20 {
            (v26, v28) => {
              let tmp = a::get::<f64>(x, j);
              let tmp_1 = rat1(tmp);
              match tmp_1 {
                (v38, v40) => {
                  let h = &v40;
                  let tmp_2 = a::set::<Rc<BigInt>>(v26, j, v38);
                  let h_clone = Rc::clone(h);
                  let tmp_3 = a::set::<Rc<BigInt>>(v28, j, h_clone);
                  let tmp_4 = (tmp_2, tmp_3);
                  let tmp_5 = zgcd(y, h);
                  let tmp_6 = div_owned(v22, tmp_5);
                  let tmp_7 = mul_2(tmp_6, v40);
                  (tmp_4, tmp_7)
                },
              }
            },
          }
        },
      }
    }
  });
  let tmp_8 = b::zero();
  let tmp_9 = a::make::<Rc<BigInt>>(n, tmp_8);
  let tmp_10 = b::one();
  let tmp_11 = b::identity(tmp_10);
  let tmp_12 = a::make::<Rc<BigInt>>(n, tmp_11);
  let tmp_13 = (tmp_9, tmp_12);
  let tmp_14 = b::one();
  let tmp_15 = b::identity(tmp_14);
  let tmp_16 = loop_::<((Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>), Rc<BigInt>)>(n, callback, callback_1, 0u64, (tmp_13, tmp_15));
  match tmp_16 {
    (v143, v145) => {
      let p = &v145;
      match v143 {
        (v149, v151) => {
          let callback_2: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = Rc::new(move |_v155: u64, v156: Rc<Array<Rc<BigInt>>>| -> bool {
            std::mem::drop(v156);
            true
          });
          let p_clone = Rc::clone(p);
          let callback_3: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new({
            move |j: u64, P: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
              let K = &v149;
              let H = &v151;
              let p = &p_clone;
              let tmp_17 = a::get::<Rc<BigInt>>(K, j);
              let tmp_18 = a::get::<Rc<BigInt>>(H, j);
              let p_clone_1 = Rc::clone(p);
              let tmp_19 = div_owned(p_clone_1, tmp_18);
              let tmp_20 = mul_2(tmp_17, tmp_19);
              a::set::<Rc<BigInt>>(P, j, tmp_20)
            }
          });
          let tmp_21 = b::zero();
          let tmp_22 = a::make::<Rc<BigInt>>(n, tmp_21);
          let tmp_23 = loop_::<Rc<Array<Rc<BigInt>>>>(n, callback_2, callback_3, 0u64, tmp_22);
          (tmp_23, v145)
        },
      }
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.get_row
// Variant: borrowed, uncurried
pub fn get_row(Q: &Rc<Array<f64>>, n: u64, i: u64) -> Rc<Array<f64>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(move |_v7: u64, v8: Rc<Array<f64>>| -> bool {
    std::mem::drop(v8);
    true
  });
  let Q_clone = Rc::clone(Q);
  let callback_1: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new({
    let __anf_capture_25 = n;
    move |k: u64, x: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let i = &i;
      let n = &__anf_capture_25;
      let tmp = a::get::<f64>(&Q_clone, add(mul(Clone::clone(i), Clone::clone(n)), k));
      a::set::<f64>(x, k, tmp)
    }
  });
  let tmp_1 = a::make::<f64>(n, __rocq_global_371);
  loop_::<Rc<Array<f64>>>(n, callback, callback_1, 0u64, tmp_1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.yv
// Variant: borrowed, uncurried
pub fn yv(Q: &Rc<Array<f64>>, n: u64, r: u64, t: u64) -> Rc<Array<Rc<BigInt>>> {
  let n_1 = n;
  let r_1 = r;
  let t_1 = t;
  let tmp = get_row(Q, n_1, add(r_1, t_1));
  fst::<Rc<Array<Rc<BigInt>>>, Rc<BigInt>>(ratvec(tmp, n_1))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.allf
// Variant: uncurried
pub fn allf(len: u64, p: Rc<dyn Fn(u64) -> bool>) -> bool {
  let callback: Rc<dyn Fn(u64, bool) -> bool> = Rc::new(move |_v4: u64, _v5: bool| -> bool {
    true
  });
  let callback_1: Rc<dyn Fn(u64, bool) -> bool> = Rc::new({
    move |k: u64, b_1: bool| -> bool {
      let p = &p;
      let tmp = p(k);
      andb(b_1, tmp)
    }
  });
  loop_::<bool>(len, callback, callback_1, 0u64, true)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dzero
pub fn dzero(x: (Rc<BigInt>, Rc<BigInt>)) -> bool {
  let tmp = fst::<Rc<BigInt>, Rc<BigInt>>(x);
  let tmp_1 = b::zero();
  eqb_2(tmp, tmp_1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.zdot
// Variant: uncurried
pub fn zdot_owned(X: Rc<Array<f64>>, o: u64, Y: Rc<Array<Rc<BigInt>>>, len: u64) -> (Rc<BigInt>, Rc<BigInt>) {
  let callback: Rc<dyn Fn(u64) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new({
    move |k: u64| -> (Rc<BigInt>, Rc<BigInt>) {
      let o = &o;
      let X = &X;
      let Y = &Y;
      let tmp = dec(a::get::<f64>(X, add(Clone::clone(o), k)));
      let tmp_1 = a::get::<Rc<BigInt>>(Y, k);
      dmul(tmp, dint_owned(tmp_1))
    }
  });
  dsumf(len, callback)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.zdot
// Variant: borrowed, uncurried
pub fn zdot(X: &Rc<Array<f64>>, o: u64, Y: &Rc<Array<Rc<BigInt>>>, len: u64) -> (Rc<BigInt>, Rc<BigInt>) {
  let len_1 = len;
  let X_clone = Rc::clone(X);
  let Y_clone = Rc::clone(Y);
  let callback: Rc<dyn Fn(u64) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new({
    move |k: u64| -> (Rc<BigInt>, Rc<BigInt>) {
      let o = &o;
      let X = &X_clone;
      let Y = &Y_clone;
      let tmp = dec(a::get::<f64>(X, add(Clone::clone(o), k)));
      let tmp_1 = a::get::<Rc<BigInt>>(Y, k);
      dmul(tmp, dint_owned(tmp_1))
    }
  });
  dsumf(len_1, callback)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.chk_incons
// Variant: uncurried
pub fn chk_incons(AT: Rc<Array<f64>>, xb: Rc<Array<f64>>, n: u64, y: Rc<Array<Rc<BigInt>>>) -> bool {
  let y_clone = Rc::clone(&y);
  let callback: Rc<dyn Fn(u64) -> bool> = Rc::new({
    let __anf_capture_18 = n;
    move |j: u64| -> bool {
      let AT = &AT;
      let y = &y_clone;
      let n = &__anf_capture_18;
      let tmp = zdot(AT, mul(j, Clone::clone(n)), y, Clone::clone(n));
      dzero(tmp)
    }
  });
  andb(allf(n, callback), negb(dzero(zdot_owned(xb, 0u64, y, n))))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.chk_red
// Variant: uncurried
pub fn chk_red(AT: Rc<Array<f64>>, xb: Rc<Array<f64>>, n: u64, y: Rc<Array<Rc<BigInt>>>, d: u64, Df: Rc<Array<bool>>) -> bool {
  let y_clone = Rc::clone(&y);
  let callback: Rc<dyn Fn(u64) -> bool> = Rc::new({
    let __anf_capture_21 = n;
    move |j: u64| -> bool {
      let AT = &AT;
      let y = &y_clone;
      let n = &__anf_capture_21;
      let tmp = zdot(AT, mul(j, Clone::clone(n)), y, Clone::clone(n));
      dzero(tmp)
    }
  });
  let tmp_1 = allf(n, callback);
  let y_clone_1 = Rc::clone(&y);
  let tmp_2 = andb(tmp_1, dzero(zdot_owned(xb, 0u64, y_clone_1, n)));
  let tmp_3 = a::get::<Rc<BigInt>>(&y, d);
  let tmp_4 = b::zero();
  let tmp_5 = negb(eqb_2(tmp_3, tmp_4));
  let callback_1: Rc<dyn Fn(u64) -> bool> = Rc::new({
    let __anf_capture_99 = d;
    let __anf_capture_101 = y;
    move |i: u64| -> bool {
      let Df = &Df;
      let d = &__anf_capture_99;
      let y = &__anf_capture_101;
      let tmp_6 = negb(a::get::<bool>(Df, i));
      let tmp_7 = eqb(i, Clone::clone(d));
      let tmp_8 = a::get::<Rc<BigInt>>(y, i);
      let tmp_9 = b::zero();
      let tmp_10 = orb(tmp_7, eqb_2(tmp_8, tmp_9));
      orb(tmp_6, tmp_10)
    }
  });
  let tmp_11 = andb(tmp_5, allf(n, callback_1));
  andb(tmp_2, tmp_11)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.scan_null
// Variant: uncurried
pub fn scan_null(AT: Rc<Array<f64>>, xb: Rc<Array<f64>>, Q: Rc<Array<f64>>, perm: Rc<Array<u64>>, fc: Rc<Array<u64>>, Df: Rc<Array<bool>>, n: u64, r: u64, k: u64) -> (bool, bool) {
  let callback: Rc<dyn Fn(u64, (bool, bool)) -> bool> = Rc::new(move |_v11: u64, v12: (bool, bool)| -> bool {
    std::mem::drop(v12);
    true
  });
  let callback_1: Rc<dyn Fn(u64, (bool, bool)) -> (bool, bool)> = Rc::new({
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
      let d = a::get::<u64>(perm, add(Clone::clone(r), t));
      let s_clone = Clone::clone(&s);
      let tmp = fst::<bool, bool>(s_clone);
      let AT_clone = Rc::clone(AT);
      let xb_clone = Rc::clone(xb);
      let n_clone = Clone::clone(n);
      let y_clone = Rc::clone(&y);
      let tmp_1 = orb(tmp, chk_incons(AT_clone, xb_clone, n_clone, y_clone));
      let tmp_2 = snd::<bool, bool>(s);
      let tmp_3 = andb(ltb(d, Clone::clone(n)), ltb(a::get::<u64>(fc, t), Clone::clone(n)));
      let AT_clone_1 = Rc::clone(AT);
      let xb_clone_1 = Rc::clone(xb);
      let n_clone_1 = Clone::clone(n);
      let Df_clone = Rc::clone(Df);
      let tmp_4 = andb(tmp_3, chk_red(AT_clone_1, xb_clone_1, n_clone_1, y, d, Df_clone));
      (tmp_1, andb(tmp_2, tmp_4))
    }
  });
  loop_::<(bool, bool)>(k, callback, callback_1, 0u64, (false, ltb(r, n)))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.bentry
// Variant: borrowed, uncurried
pub fn bentry(xa: &Rc<Array<Rc<Array<f64>>>>, Df: &Rc<Array<bool>>, tix: &Rc<Array<u64>>, fc: &Rc<Array<u64>>, Cf: &Rc<Array<bool>>, i: u64, j: u64) -> f64 {
  let i_1 = i;
  let j_1 = j;
  if a::get::<bool>(Df, i_1) {
    let tmp = a::get::<u64>(tix, i_1);
    let tmp_1 = a::get::<u64>(fc, tmp);
    if eqb(j_1, tmp_1) {
      __rocq_global_820
    } else {
      __rocq_global_371
    }
  } else {
    if a::get::<bool>(Cf, j_1) {
      __rocq_global_371
    } else {
      let xa_clone = Rc::clone(xa);
      let tmp_2 = a::get::<Rc<Array<f64>>>(&xa_clone, i_1);
      std::mem::drop(xa_clone);
      let tmp_3 = a::get::<f64>(&tmp_2, j_1);
      std::mem::drop(tmp_2);
      tmp_3
    }
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.padB
// Variant: uncurried
pub fn padB(xa: Rc<Array<Rc<Array<f64>>>>, n: u64, Df: Rc<Array<bool>>, tix: Rc<Array<u64>>, fc: Rc<Array<u64>>, Cf: Rc<Array<bool>>) -> Rc<Array<Rc<Array<f64>>>> {
  let tmp = a::make::<f64>(0u64, __rocq_global_371);
  let callback: Rc<dyn Fn(u64) -> Rc<Array<f64>>> = Rc::new({
    let __anf_capture_38 = n;
    move |i: u64| -> Rc<Array<f64>> {
      let xa = &xa;
      let Df = &Df;
      let tix = &tix;
      let fc = &fc;
      let Cf = &Cf;
      let n = &__anf_capture_38;
      let tmp_1 = __rocq_global_371;
      let xa_clone = Rc::clone(xa);
      let Df_clone = Rc::clone(Df);
      let tix_clone = Rc::clone(tix);
      let fc_clone = Rc::clone(fc);
      let Cf_clone = Rc::clone(Cf);
      let callback_1: Rc<dyn Fn(u64) -> f64> = Rc::new({
        move |j: u64| -> f64 {
          let xa = &xa_clone;
          let Df = &Df_clone;
          let tix = &tix_clone;
          let fc = &fc_clone;
          let Cf = &Cf_clone;
          let i_clone = Clone::clone(&i);
          bentry(xa, Df, tix, fc, Cf, i_clone, j)
        }
      });
      let n_clone = Clone::clone(n);
      tab::<f64>(n_clone, tmp_1, callback_1)
    }
  });
  tab::<Rc<Array<f64>>>(n, tmp, callback)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.certify_inj
// Variant: uncurried
pub fn certify_inj(n: u64, xa: Rc<Array<Rc<Array<f64>>>>, AT: Rc<Array<f64>>, Q: Rc<Array<f64>>) -> bool {
  let nz = i2z(n);
  let tmp = b::one();
  let tmp_1 = b::twice_plus_one(tmp);
  let tmp_2 = b::identity(tmp_1);
  let nz_clone = Rc::clone(&nz);
  let tmp_3 = mul_2(tmp_2, nz_clone);
  let tmp_4 = b::one();
  let tmp_5 = b::twice_plus_one(tmp_4);
  let tmp_6 = b::twice(tmp_5);
  let tmp_7 = b::twice_plus_one(tmp_6);
  let tmp_8 = b::twice(tmp_7);
  let tmp_9 = b::twice_plus_one(tmp_8);
  let tmp_10 = b::neg(tmp_9);
  let lamd = (tmp_3, tmp_10);
  let tmp_11 = b::one();
  let tmp_12 = b::twice_plus_one(tmp_11);
  let tmp_13 = b::identity(tmp_12);
  let nz_clone_1 = Rc::clone(&nz);
  let tmp_14 = mul_2(tmp_13, nz_clone_1);
  let tmp_15 = mul_2(tmp_14, nz);
  let tmp_16 = b::one();
  let tmp_17 = b::twice(tmp_16);
  let tmp_18 = b::twice(tmp_17);
  let tmp_19 = b::twice(tmp_18);
  let tmp_20 = b::twice(tmp_19);
  let tmp_21 = b::twice_plus_one(tmp_20);
  let tmp_22 = b::twice_plus_one(tmp_21);
  let tmp_23 = b::twice(tmp_22);
  let tmp_24 = b::twice(tmp_23);
  let tmp_25 = b::twice_plus_one(tmp_24);
  let tmp_26 = b::twice_plus_one(tmp_25);
  let tmp_27 = b::neg(tmp_26);
  let mud2 = (tmp_15, tmp_27);
  let S = rowabs(xa, n);
  let callback: Rc<dyn Fn(u64) -> ((Rc<BigInt>, Rc<BigInt>), bool)> = Rc::new({
    let __anf_capture_127 = n;
    move |v139: u64| -> ((Rc<BigInt>, Rc<BigInt>), bool) {
      let n = &__anf_capture_127;
      let Q = &Q;
      let AT = &AT;
      let S = &S;
      let tmp_28 = erow(Clone::clone(n), Q, AT, S, Clone::clone(&lamd), Clone::clone(&mud2), v139);
      tmp_28
    }
  });
  let tmp_29 = maxb(n, callback);
  match tmp_29 {
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
  let B_clone = Rc::clone(&B);
  let tmp = col_thr(B_clone, n);
  let tmp_1 = a::make::<f64>(n, __rocq_global_371);
  let B_clone_1 = Rc::clone(&B);
  let tmp_2 = init_M(B_clone_1, tmp_1, n, w);
  let tmp_3 = init_Q(n);
  let st = forward(n, w, tmp, tmp_2, tmp_3);
  let tmp_4 = fs_r(&st);
  if eqb(tmp_4, n) {
    let B_clone_2 = Rc::clone(&B);
    let tmp_5 = transpose(B_clone_2, n);
    let st_clone = Rc::clone(&st);
    let tmp_6 = fs_M_owned(st_clone);
    let tmp_7 = fs_Q(st);
    let tmp_8 = snd::<Rc<Array<f64>>, Rc<Array<f64>>>(backsub(n, w, tmp_6, tmp_7));
    certify_inj(n, B, tmp_5, tmp_8)
  } else {
    std::mem::drop(B);
    std::mem::drop(st);
    false
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.free_col
// Variant: uncurried
pub fn free_col(pc: Rc<Array<u64>>, n: u64, r: u64) -> u64 {
  let callback: Rc<dyn Fn(u64, Rc<Array<bool>>) -> bool> = Rc::new(move |_v5: u64, v6: Rc<Array<bool>>| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new({
    move |t: u64, isp: Rc<Array<bool>>| -> Rc<Array<bool>> {
      let tmp = a::get::<u64>(&pc, t);
      a::set::<bool>(isp, tmp, true)
    }
  });
  let tmp_1 = a::make::<bool>(n, false);
  let isp = loop_::<Rc<Array<bool>>>(r, callback, callback_1, 0u64, tmp_1);
  let callback_2: Rc<dyn Fn(u64, u64) -> bool> = Rc::new(move |_v58: u64, _v59: u64| -> bool {
    true
  });
  let callback_3: Rc<dyn Fn(u64, u64) -> u64> = Rc::new({
    let __anf_capture_71 = n;
    move |c: u64, f: u64| -> u64 {
      let n = &__anf_capture_71;
      let isp = &isp;
      let tmp_2 = eqb(f, Clone::clone(n));
      let tmp_3 = negb(a::get::<bool>(isp, c));
      if andb(tmp_2, tmp_3) {
        c
      } else {
        f
      }
    }
  });
  loop_::<u64>(n, callback_2, callback_3, 0u64, n)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.echelon_solve
// Variant: uncurried
pub fn echelon_solve(M: Rc<Array<f64>>, pc: Rc<Array<u64>>, n: u64, w: u64, r: u64, homog: bool, x: Rc<Array<f64>>) -> Rc<Array<f64>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<f64>>) -> bool> = Rc::new(move |_v9: u64, v10: Rc<Array<f64>>| -> bool {
    std::mem::drop(v10);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new({
    let __anf_capture_30 = r;
    move |s: u64, x: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let r = &__anf_capture_30;
      let pc = &pc;
      let homog = &homog;
      let n = &n;
      let w = &w;
      let M = &M;
      let tmp = 1u64;
      let tmp_1 = sub_2(Clone::clone(r), tmp);
      let t = sub_2(tmp_1, s);
      let c = a::get::<u64>(pc, t);
      let s0 = if *homog {
        __rocq_global_371
      } else {
        a::get::<f64>(M, add(mul(t, Clone::clone(w)), Clone::clone(n)))
      };
      let callback_2: Rc<dyn Fn(u64, f64) -> bool> = Rc::new(move |_v85: u64, _v86: f64| -> bool {
        true
      });
      let w_clone = Clone::clone(w);
      let M_clone = Rc::clone(M);
      let x_clone = Rc::clone(&x);
      let callback_3: Rc<dyn Fn(u64, f64) -> f64> = Rc::new({
        let __anf_capture_103 = t;
        move |j: u64, acc: f64| -> f64 {
          let t = &__anf_capture_103;
          let w = &w_clone;
          let M = &M_clone;
          let x = &x_clone;
          let tmp_2 = a::get::<f64>(M, add(mul(Clone::clone(t), Clone::clone(w)), j));
          let tmp_3 = a::get::<f64>(x, j);
          sub_1(acc, mul_1(tmp_2, tmp_3))
        }
      });
      let tmp_4 = add(c, 1u64);
      let acc = loop_::<f64>(Clone::clone(n), callback_2, callback_3, tmp_4, s0);
      let tmp_5 = a::get::<f64>(M, add(mul(t, Clone::clone(w)), c));
      a::set::<f64>(x, c, div_1(acc, tmp_5))
    }
  });
  loop_::<Rc<Array<f64>>>(r, callback, callback_1, 0u64, x)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.chk_mult
// Variant: uncurried
pub fn chk_mult(xa: Rc<Array<Rc<Array<f64>>>>, xb: Rc<Array<f64>>, n: u64, p: Rc<Array<Rc<BigInt>>>, q: Rc<BigInt>, v: Rc<Array<Rc<BigInt>>>) -> bool {
  let tmp = b::zero();
  let q_clone = Rc::clone(&q);
  let tmp_1 = negb(eqb_2(q_clone, tmp));
  let v_clone = Rc::clone(&v);
  let callback: Rc<dyn Fn(u64) -> bool> = Rc::new({
    move |j: u64| -> bool {
      let tmp_2 = a::get::<Rc<BigInt>>(&v_clone, j);
      let tmp_3 = b::zero();
      eqb_2(tmp_2, tmp_3)
    }
  });
  let tmp_4 = andb(tmp_1, negb(allf(n, callback)));
  let callback_1: Rc<dyn Fn(u64) -> bool> = Rc::new({
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
      let xa_clone = Rc::clone(xa);
      let row = a::get::<Rc<Array<f64>>>(&xa_clone, i);
      std::mem::drop(xa_clone);
      let row_clone = Rc::clone(&row);
      let p_clone = Rc::clone(p);
      let tmp_5 = dzero(dsub(zdot_owned(row_clone, 0u64, p_clone, Clone::clone(n)), dmul(dint(q), dec(a::get::<f64>(xb, i)))));
      let v_clone_1 = Rc::clone(v);
      let n_clone = Clone::clone(n);
      andb(tmp_5, dzero(zdot_owned(row, 0u64, v_clone_1, n_clone)))
    }
  });
  andb(tmp_4, allf(n, callback_1))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.solve
// Variant: uncurried
pub fn solve(n: u64, xa: Rc<Array<Rc<Array<f64>>>>, xb: Rc<Array<f64>>) -> Rc<outcome<Rc<Array<f64>>>> {
  let w = add(n, 1u64);
  let xa_clone = Rc::clone(&xa);
  let tmp = col_thr(xa_clone, n);
  let xa_clone_1 = Rc::clone(&xa);
  let xb_clone = Rc::clone(&xb);
  let tmp_1 = init_M(xa_clone_1, xb_clone, n, w);
  let tmp_2 = init_Q(n);
  let st = forward(n, w, tmp, tmp_1, tmp_2);
  let xa_clone_2 = Rc::clone(&xa);
  let AT = transpose(xa_clone_2, n);
  let st_clone = Rc::clone(&st);
  let tmp_3 = fs_r_owned(st_clone);
  if eqb(tmp_3, n) {
    let st_clone_1 = Rc::clone(&st);
    let tmp_4 = fs_M_owned(st_clone_1);
    let tmp_5 = fs_Q(st);
    let tmp_6 = backsub(n, w, tmp_4, tmp_5);
    match tmp_6 {
      (v85, v87) => {
        let xt = get_col(v85, n, w, n);
        let xa_clone_3 = Rc::clone(&xa);
        let xb_clone_1 = Rc::clone(&xb);
        let xt_clone = Rc::clone(&xt);
        if certify(n, xa_clone_3, xb_clone_1, AT, v87, xt_clone) {
          std::mem::drop(xb);
          std::mem::drop(xa);
          Rc::new(outcome::<Rc<Array<f64>>>::Unique(xt))
        } else {
          std::mem::drop(xt);
          solve_exact(n, xa, xb)
        }
      },
    }
  } else {
    let st_clone_2 = Rc::clone(&st);
    let M = fs_M_owned(st_clone_2);
    let st_clone_3 = Rc::clone(&st);
    let r = fs_r_owned(st_clone_3);
    let k = if ltb(r, n) {
      sub_2(n, r)
    } else {
      0u64
    };
    let st_clone_4 = Rc::clone(&st);
    let tmp_7 = fs_pc(st_clone_4);
    let fc = free_cols(tmp_7, n, r);
    let st_clone_5 = Rc::clone(&st);
    let tmp_8 = fs_perm(st_clone_5);
    let mD = mark_D(tmp_8, n, r, k);
    let mD_clone = Clone::clone(&mD);
    let Df = fst::<Rc<Array<bool>>, Rc<Array<u64>>>(mD_clone);
    let tix = snd::<Rc<Array<bool>>, Rc<Array<u64>>>(mD);
    let fc_clone = Rc::clone(&fc);
    let Cf = mark_C(fc_clone, n, k);
    let st_clone_6 = Rc::clone(&st);
    let tmp_9 = fs_Q(st_clone_6);
    let st_clone_7 = Rc::clone(&st);
    let tmp_10 = fs_perm(st_clone_7);
    let xb_clone_2 = Rc::clone(&xb);
    let fc_clone_1 = Rc::clone(&fc);
    let Df_clone = Rc::clone(&Df);
    let sc = scan_null(AT, xb_clone_2, tmp_9, tmp_10, fc_clone_1, Df_clone, n, r, k);
    let sc_clone = Clone::clone(&sc);
    if fst::<bool, bool>(sc_clone) {
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
    } else {
      let tmp_11 = if snd::<bool, bool>(sc) {
        let xa_clone_4 = Rc::clone(&xa);
        padded_ok(xa_clone_4, n, Df, tix, fc, Cf)
      } else {
        std::mem::drop(Cf);
        std::mem::drop(fc);
        std::mem::drop(tix);
        std::mem::drop(Df);
        false
      };
      if tmp_11 {
        std::mem::drop(M);
        std::mem::drop(xa);
        std::mem::drop(xb);
        std::mem::drop(st);
        Rc::new(outcome::<Rc<Array<f64>>>::Multiple)
      } else {
        let st_clone_8 = Rc::clone(&st);
        let tmp_12 = fs_pc(st_clone_8);
        let f = free_col(tmp_12, n, r);
        let st_clone_9 = Rc::clone(&st);
        let tmp_13 = fs_pc(st_clone_9);
        let tmp_14 = a::make::<f64>(n, __rocq_global_371);
        let M_clone = Rc::clone(&M);
        let x0 = echelon_solve(M_clone, tmp_13, n, w, r, false, tmp_14);
        let tmp_15 = fs_pc(st);
        let tmp_16 = a::make::<f64>(n, __rocq_global_371);
        let tmp_17 = a::set::<f64>(tmp_16, f, __rocq_global_820);
        let v = echelon_solve(M, tmp_15, n, w, r, true, tmp_17);
        let tmp_18 = ratvec(x0, n);
        match tmp_18 {
          (v380, v382) => {
            let tmp_19 = fst::<Rc<Array<Rc<BigInt>>>, Rc<BigInt>>(ratvec(v, n));
            let xa_clone_5 = Rc::clone(&xa);
            let xb_clone_3 = Rc::clone(&xb);
            if chk_mult(xa_clone_5, xb_clone_3, n, v380, v382, tmp_19) {
              std::mem::drop(xa);
              std::mem::drop(xb);
              Rc::new(outcome::<Rc<Array<f64>>>::Multiple)
            } else {
              solve_exact(n, xa, xb)
            }
          },
        }
      }
    }
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
const __rocq_global_371: f64 = f64::from_bits(0u64);
const __rocq_global_722: f64 = f64::from_bits(4427038433705197568u64);
const __rocq_global_820: f64 = f64::from_bits(4607182418800017408u64);
const __rocq_global_1215: f64 = f64::from_bits(9218868437227405312u64);
const __rocq_global_3377: f64 = f64::from_bits(9223372036854775808u64);
const __rocq_global_3380: f64 = f64::from_bits(18442240474082181120u64);
const __rocq_global_3383: f64 = f64::from_bits(9221120237041090560u64);