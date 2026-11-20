#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};
#[allow(unused_imports)] use rocq_bigint::{self as b, BigInt};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

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
  pub fs_M: Array<f64>,
  pub fs_Q: Array<f64>,
  pub fs_r: Int63,
  pub fs_pc: Array<Int63>,
  pub fs_perm: Array<Int63>,
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

pub type uint = Int63;

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
pub fn wloop_1<St: Clone + 'static>(hi: Int63, cont: Rc<dyn Fn(Int63, St) -> bool>, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.wloop (local: wloop)
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

// Rocq: EquationsolverExact.equationsolver_exact_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: Int63, cont: Rc<dyn Fn(Int63, St) -> bool>, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop_1::<St>(hi, cont, f, i, s)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_r
pub fn fs_r_owned(f: Rc<fstate>) -> Int63 {
  let f_fs_r_clone = Clone::clone(&f.fs_r);
  std::mem::drop(f);
  f_fs_r_clone
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_r
// Variant: borrowed
pub fn fs_r(f: &Rc<fstate>) -> Int63 {
  let tmp = f;
  Clone::clone(&tmp.fs_r)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_M
pub fn fs_M_owned(f: Rc<fstate>) -> Array<f64> {
  let f_fs_M_clone = Clone::clone(&f.fs_M);
  std::mem::drop(f);
  f_fs_M_clone
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_M
// Variant: borrowed
pub fn fs_M(f: &Rc<fstate>) -> Array<f64> {
  let tmp = f;
  Clone::clone(&tmp.fs_M)
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.swap_f
// Variant: uncurried
pub fn swap_f(T: Array<f64>, w: Int63, p: Int63, r: Int63) -> Array<f64> {
  let callback: Rc<dyn Fn(Int63, Array<f64>) -> bool> = Rc::new(move |_v6: Int63, v7: Array<f64>| -> bool {
    std::mem::drop(v7);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<f64>) -> Array<f64>> = Rc::new({
    let __anf_capture_25 = w;
    move |j: Int63, T: Array<f64>| -> Array<f64> {
      let r = &r;
      let p = &p;
      let w = &__anf_capture_25;
      let x = T.get_cloned(Clone::clone(r) * Clone::clone(w) + j);
      let y = T.get_cloned(Clone::clone(p) * Clone::clone(w) + j);
      let tmp = T.set(Clone::clone(r) * Clone::clone(w) + j, y);
      let p_clone = Clone::clone(p);
      let w_clone = Clone::clone(w);
      tmp.set(p_clone * w_clone + j, x)
    }
  });
  loop_::<Array<f64>>(w, callback, callback_1, int63!(0), T)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_Q
pub fn fs_Q(f: Rc<fstate>) -> Array<f64> {
  let f_fs_Q_clone = Clone::clone(&f.fs_Q);
  std::mem::drop(f);
  f_fs_Q_clone
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.axpy_row
// Variant: uncurried
pub fn axpy_row(T: Array<f64>, w: Int63, i: Int63, r: Int63, lo: Int63, f: f64) -> Array<f64> {
  let callback: Rc<dyn Fn(Int63, Array<f64>) -> bool> = Rc::new(move |_v8: Int63, v9: Array<f64>| -> bool {
    std::mem::drop(v9);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<f64>) -> Array<f64>> = Rc::new({
    let __anf_capture_29 = w;
    move |j: Int63, T: Array<f64>| -> Array<f64> {
      let i = &i;
      let r = &r;
      let w = &__anf_capture_29;
      let f = &f;
      let tmp = Clone::clone(i) * Clone::clone(w) + j;
      let tmp_1 = T.get_cloned(Clone::clone(i) * Clone::clone(w) + j);
      let tmp_2 = T.get_cloned(Clone::clone(r) * Clone::clone(w) + j);
      let f_clone = Clone::clone(f);
      T.set(tmp, rocq_float64::sub(tmp_1, rocq_float64::mul(f_clone, tmp_2)))
    }
  });
  loop_::<Array<f64>>(w, callback, callback_1, lo, T)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_perm
pub fn fs_perm(f: Rc<fstate>) -> Array<Int63> {
  let f_fs_perm_clone = Clone::clone(&f.fs_perm);
  std::mem::drop(f);
  f_fs_perm_clone
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fs_pc
pub fn fs_pc(f: Rc<fstate>) -> Array<Int63> {
  let f_fs_pc_clone = Clone::clone(&f.fs_pc);
  std::mem::drop(f);
  f_fs_pc_clone
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fwd_col
// Variant: uncurried
pub fn fwd_col(n: Int63, w: Int63, thr: Array<f64>, c: Int63, st: Rc<fstate>) -> Rc<fstate> {
  let r = fs_r(&st);
  if r < n {
    let st_ref = &st;
    let M = fs_M(st_ref);
    let callback: Rc<dyn Fn(Int63, (Int63, f64)) -> bool> = Rc::new(move |_v22: Int63, v23: (Int63, f64)| -> bool {
      std::mem::drop(v23);
      true
    });
    let M_clone = Clone::clone(&M);
    let callback_1: Rc<dyn Fn(Int63, (Int63, f64)) -> (Int63, f64)> = Rc::new({
      let __anf_capture_38 = w;
      let __anf_capture_40 = c;
      move |i: Int63, pm: (Int63, f64)| -> (Int63, f64) {
        let w = &__anf_capture_38;
        let c = &__anf_capture_40;
        let M = &M_clone;
        let v = rocq_float64::abs(M.get_cloned(i * Clone::clone(w) + Clone::clone(c)));
        let pm_clone = Clone::clone(&pm);
        let tmp = snd::<Int63, f64>(pm_clone);
        if rocq_float64::ltb(tmp, v) {
          std::mem::drop(pm);
          (i, v)
        } else {
          pm
        }
      }
    });
    let tmp_1 = (r, __rocq_global_371);
    let tmp_2 = loop_::<(Int63, f64)>(n, callback, callback_1, r, tmp_1);
    match tmp_2 {
      (v111, v113) => {
        let tmp_3 = thr.get_cloned(c);
        if rocq_float64::leb(v113, tmp_3) {
          std::mem::drop(M);
          std::mem::drop(thr);
          st
        } else {
          std::mem::drop(thr);
          let M_1 = swap_f(M, w, v111, r);
          let st_clone = Rc::clone(&st);
          let Q = swap_f(fs_Q(st_clone), n, v111, r);
          let piv = M_1.get_cloned(r * w + c);
          let callback_2: Rc<dyn Fn(Int63, (Array<f64>, Array<f64>)) -> bool> = Rc::new(move |_v171: Int63, v172: (Array<f64>, Array<f64>)| -> bool {
            std::mem::drop(v172);
            true
          });
          let callback_3: Rc<dyn Fn(Int63, (Array<f64>, Array<f64>)) -> (Array<f64>, Array<f64>)> = Rc::new({
            let __anf_capture_192 = w;
            let __anf_capture_194 = c;
            let __anf_capture_196 = n;
            let __anf_capture_198 = r;
            move |i: Int63, mq: (Array<f64>, Array<f64>)| -> (Array<f64>, Array<f64>) {
              let piv = &piv;
              let w = &__anf_capture_192;
              let c = &__anf_capture_194;
              let n = &__anf_capture_196;
              let r = &__anf_capture_198;
              match mq {
                (v203, v205) => {
                  let Q = &v203;
                  let tmp_4 = Q.get_cloned(i * Clone::clone(w) + Clone::clone(c));
                  let f = rocq_float64::div(tmp_4, Clone::clone(piv));
                  let tmp_5 = int63!(1);
                  let tmp_6 = Clone::clone(c) + tmp_5;
                  let M = axpy_row(v203, Clone::clone(w), i, Clone::clone(r), tmp_6, f);
                  let tmp_7 = M.set(i * Clone::clone(w) + Clone::clone(c), __rocq_global_371);
                  let n_clone = Clone::clone(n);
                  let r_clone = Clone::clone(r);
                  (tmp_7, axpy_row(v205, n_clone, i, r_clone, int63!(0), f))
                },
              }
            }
          });
          let tmp_8 = loop_::<(Array<f64>, Array<f64>)>(n, callback_2, callback_3, r + int63!(1), (M_1, Q));
          match tmp_8 {
            (v326, v328) => {
              let st_clone_1 = Rc::clone(&st);
              let pm = fs_perm(st_clone_1);
              let x = pm.get_cloned(v111);
              let y = pm.get_cloned(r);
              Rc::new(fstate { fs_M: v326, fs_Q: v328, fs_r: r + int63!(1), fs_pc: fs_pc(st).set(r, c), fs_perm: pm.set(v111, y).set(r, x) })
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
pub fn tab<T: Clone + 'static>(n: Int63, d: T, f: Rc<dyn Fn(Int63) -> T>) -> Array<T> {
  let callback: Rc<dyn Fn(Int63, Array<T>) -> bool> = Rc::new(move |_v5: Int63, v6: Array<T>| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<T>) -> Array<T>> = Rc::new({
    move |i: Int63, t: Array<T>| -> Array<T> {
      let f = &f;
      let tmp = f(i);
      t.set(i, tmp)
    }
  });
  let tmp_1 = Array::<T>::make(n, d);
  loop_::<Array<T>>(n, callback, callback_1, int63!(0), tmp_1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.forward
// Variant: uncurried
pub fn forward(n: Int63, w: Int63, thr: Array<f64>, M: Array<f64>, Q: Array<f64>) -> Rc<fstate> {
  let callback: Rc<dyn Fn(Int63, Rc<fstate>) -> bool> = Rc::new(move |_v7: Int63, v8: Rc<fstate>| -> bool {
    std::mem::drop(v8);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Rc<fstate>) -> Rc<fstate>> = Rc::new({
    let __anf_capture_22 = n;
    move |v28: Int63, v29: Rc<fstate>| -> Rc<fstate> {
      let tmp = Clone::clone(&__anf_capture_22);
      let w_clone = Clone::clone(&w);
      let thr_clone = Clone::clone(&thr);
      fwd_col(tmp, w_clone, thr_clone, v28, v29)
    }
  });
  let tmp_1 = int63!(0);
  let tmp_2 = int63!(0);
  let tmp_3 = Array::<Int63>::make(n, int63!(0));
  let tmp_4 = int63!(0);
  let callback_2: Rc<dyn Fn(Int63) -> Int63> = Rc::new(move |i: Int63| -> Int63 {
    i
  });
  let tmp_5 = tab::<Int63>(n, tmp_4, callback_2);
  loop_::<Rc<fstate>>(n, callback, callback_1, tmp_1, Rc::new(fstate { fs_M: M, fs_Q: Q, fs_r: tmp_2, fs_pc: tmp_3, fs_perm: tmp_5 }))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.col_thr
// Variant: uncurried
pub fn col_thr(xa: Array<Array<f64>>, n: Int63) -> Array<f64> {
  let callback: Rc<dyn Fn(Int63, Array<f64>) -> bool> = Rc::new(move |_v4: Int63, v5: Array<f64>| -> bool {
    std::mem::drop(v5);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<f64>) -> Array<f64>> = Rc::new({
    let __anf_capture_19 = n;
    move |j: Int63, T: Array<f64>| -> Array<f64> {
      let xa = &xa;
      let n = &__anf_capture_19;
      let callback_2: Rc<dyn Fn(Int63, f64) -> bool> = Rc::new(move |_v25: Int63, _v26: f64| -> bool {
        true
      });
      let xa_clone = Clone::clone(xa);
      let callback_3: Rc<dyn Fn(Int63, f64) -> f64> = Rc::new({
        let __anf_capture_40 = j;
        move |i: Int63, m: f64| -> f64 {
          let xa = &xa_clone;
          let j = &__anf_capture_40;
          let xa_clone_1 = Clone::clone(xa);
          let tmp = &xa_clone_1;
          let tmp_1 = tmp.get_cloned(i);
          let tmp_2 = &tmp_1;
          let tmp_3 = tmp_2.get_cloned(Clone::clone(j));
          let v = rocq_float64::abs(tmp_3);
          if rocq_float64::ltb(m, v) {
            std::mem::drop(tmp_1);
            std::mem::drop(xa_clone_1);
            v
          } else {
            std::mem::drop(tmp_1);
            std::mem::drop(xa_clone_1);
            m
          }
        }
      });
      let n_clone = Clone::clone(n);
      let m = loop_::<f64>(n_clone, callback_2, callback_3, int63!(0), __rocq_global_371);
      T.set(j, rocq_float64::mul(m, __rocq_global_722))
    }
  });
  let tmp_4 = Array::<f64>::make(n, __rocq_global_371);
  loop_::<Array<f64>>(n, callback, callback_1, int63!(0), tmp_4)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.init_M
// Variant: uncurried
pub fn init_M(xa: Array<Array<f64>>, xb: Array<f64>, n: Int63, w: Int63) -> Array<f64> {
  let callback: Rc<dyn Fn(Int63, Array<f64>) -> bool> = Rc::new(move |_v6: Int63, v7: Array<f64>| -> bool {
    std::mem::drop(v7);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<f64>) -> Array<f64>> = Rc::new({
    let __anf_capture_25 = w;
    let __anf_capture_27 = n;
    move |i: Int63, M: Array<f64>| -> Array<f64> {
      let xa = &xa;
      let w = &__anf_capture_25;
      let n = &__anf_capture_27;
      let xb = &xb;
      let xa_clone = Clone::clone(xa);
      let tmp = &xa_clone;
      let row = tmp.get_cloned(i);
      std::mem::drop(xa_clone);
      let callback_2: Rc<dyn Fn(Int63, Array<f64>) -> bool> = Rc::new(move |_v41: Int63, v42: Array<f64>| -> bool {
        std::mem::drop(v42);
        true
      });
      let w_clone = Clone::clone(w);
      let callback_3: Rc<dyn Fn(Int63, Array<f64>) -> Array<f64>> = Rc::new({
        let __anf_capture_56 = i;
        move |j: Int63, M: Array<f64>| -> Array<f64> {
          let i = &__anf_capture_56;
          let w = &w_clone;
          let row = &row;
          let tmp_1 = Clone::clone(i) * Clone::clone(w) + j;
          let tmp_2 = row.get_cloned(j);
          M.set(tmp_1, tmp_2)
        }
      });
      let tmp_3 = int63!(0);
      let M_1 = loop_::<Array<f64>>(Clone::clone(n), callback_2, callback_3, tmp_3, M);
      let tmp_4 = i * Clone::clone(w) + Clone::clone(n);
      let tmp_5 = xb.get_cloned(i);
      M_1.set(tmp_4, tmp_5)
    }
  });
  let tmp_6 = n * w;
  loop_::<Array<f64>>(n, callback, callback_1, int63!(0), Array::<f64>::make(tmp_6, __rocq_global_371))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.init_Q
pub fn init_Q(n: Int63) -> Array<f64> {
  let callback: Rc<dyn Fn(Int63, Array<f64>) -> bool> = Rc::new(move |_v3: Int63, v4: Array<f64>| -> bool {
    std::mem::drop(v4);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<f64>) -> Array<f64>> = Rc::new({
    let __anf_capture_14 = n;
    move |i: Int63, Q: Array<f64>| -> Array<f64> {
      let tmp = Clone::clone(&__anf_capture_14);
      Q.set(i * tmp + i, __rocq_global_820)
    }
  });
  let tmp_1 = n * n;
  loop_::<Array<f64>>(n, callback, callback_1, int63!(0), Array::<f64>::make(tmp_1, __rocq_global_371))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.transpose
// Variant: uncurried
pub fn transpose(xa: Array<Array<f64>>, n: Int63) -> Array<f64> {
  let callback: Rc<dyn Fn(Int63, Array<f64>) -> bool> = Rc::new(move |_v4: Int63, v5: Array<f64>| -> bool {
    std::mem::drop(v5);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<f64>) -> Array<f64>> = Rc::new({
    let __anf_capture_19 = n;
    move |i: Int63, T: Array<f64>| -> Array<f64> {
      let xa = &xa;
      let n = &__anf_capture_19;
      let xa_clone = Clone::clone(xa);
      let tmp = &xa_clone;
      let row = tmp.get_cloned(i);
      std::mem::drop(xa_clone);
      let callback_2: Rc<dyn Fn(Int63, Array<f64>) -> bool> = Rc::new(move |_v31: Int63, v32: Array<f64>| -> bool {
        std::mem::drop(v32);
        true
      });
      let n_clone = Clone::clone(n);
      let callback_3: Rc<dyn Fn(Int63, Array<f64>) -> Array<f64>> = Rc::new({
        let __anf_capture_48 = i;
        move |j: Int63, T: Array<f64>| -> Array<f64> {
          let n = &n_clone;
          let i = &__anf_capture_48;
          let row = &row;
          let tmp_1 = j * Clone::clone(n) + Clone::clone(i);
          let tmp_2 = row.get_cloned(j);
          T.set(tmp_1, tmp_2)
        }
      });
      let n_clone_1 = Clone::clone(n);
      loop_::<Array<f64>>(n_clone_1, callback_2, callback_3, int63!(0), T)
    }
  });
  let tmp_3 = n * n;
  loop_::<Array<f64>>(n, callback, callback_1, int63!(0), Array::<f64>::make(tmp_3, __rocq_global_371))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.scale_row
// Variant: uncurried
pub fn scale_row(T: Array<f64>, w: Int63, i: Int63, piv: f64) -> Array<f64> {
  let callback: Rc<dyn Fn(Int63, Array<f64>) -> bool> = Rc::new(move |_v6: Int63, v7: Array<f64>| -> bool {
    std::mem::drop(v7);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<f64>) -> Array<f64>> = Rc::new({
    let __anf_capture_23 = w;
    move |j: Int63, T: Array<f64>| -> Array<f64> {
      let i = &i;
      let w = &__anf_capture_23;
      let piv = &piv;
      let tmp = Clone::clone(i) * Clone::clone(w) + j;
      let tmp_1 = T.get_cloned(Clone::clone(i) * Clone::clone(w) + j);
      let piv_clone = Clone::clone(piv);
      T.set(tmp, rocq_float64::div(tmp_1, piv_clone))
    }
  });
  loop_::<Array<f64>>(w, callback, callback_1, int63!(0), T)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.backsub
// Variant: uncurried
pub fn backsub(n: Int63, w: Int63, M: Array<f64>, Q: Array<f64>) -> (Array<f64>, Array<f64>) {
  let callback: Rc<dyn Fn(Int63, (Array<f64>, Array<f64>)) -> bool> = Rc::new(move |_v6: Int63, v7: (Array<f64>, Array<f64>)| -> bool {
    std::mem::drop(v7);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, (Array<f64>, Array<f64>)) -> (Array<f64>, Array<f64>)> = Rc::new({
    let __anf_capture_21 = n;
    move |t: Int63, mq: (Array<f64>, Array<f64>)| -> (Array<f64>, Array<f64>) {
      let w = &w;
      let n = &__anf_capture_21;
      match mq {
        (v26, v28) => {
          let Q = &v26;
          let tmp = int63!(1);
          let i = Clone::clone(n) - tmp - t;
          let piv = Q.get_cloned(i * Clone::clone(w) + i);
          let tmp_1 = Q.get_cloned(i * Clone::clone(w) + Clone::clone(n));
          let xi = rocq_float64::div(tmp_1, piv);
          let M = v26.set(i * Clone::clone(w) + Clone::clone(n), xi);
          let Q_1 = scale_row(v28, Clone::clone(n), i, piv);
          let callback_2: Rc<dyn Fn(Int63, (Array<f64>, Array<f64>)) -> bool> = Rc::new(move |_v112: Int63, v113: (Array<f64>, Array<f64>)| -> bool {
            std::mem::drop(v113);
            true
          });
          let w_clone = Clone::clone(w);
          let n_clone = Clone::clone(n);
          let callback_3: Rc<dyn Fn(Int63, (Array<f64>, Array<f64>)) -> (Array<f64>, Array<f64>)> = Rc::new({
            let __anf_capture_131 = xi;
            let __anf_capture_135 = i;
            move |i_: Int63, mq: (Array<f64>, Array<f64>)| -> (Array<f64>, Array<f64>) {
              let w = &w_clone;
              let xi = &__anf_capture_131;
              let n = &n_clone;
              let i = &__anf_capture_135;
              match mq {
                (v140, v142) => {
                  let Q = &v140;
                  let f = Q.get_cloned(i_ * Clone::clone(w) + Clone::clone(i));
                  let tmp_2 = i_ * Clone::clone(w) + Clone::clone(n);
                  let tmp_3 = Q.get_cloned(i_ * Clone::clone(w) + Clone::clone(n));
                  let tmp_4 = v140.set(tmp_2, rocq_float64::sub(tmp_3, rocq_float64::mul(f, Clone::clone(xi))));
                  let n_clone_1 = Clone::clone(n);
                  let i_clone = Clone::clone(i);
                  (tmp_4, axpy_row(v142, n_clone_1, i_, i_clone, int63!(0), f))
                },
              }
            }
          });
          loop_::<(Array<f64>, Array<f64>)>(i, callback_2, callback_3, int63!(0), (M, Q_1))
        },
      }
    }
  });
  loop_::<(Array<f64>, Array<f64>)>(n, callback, callback_1, int63!(0), (M, Q))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.get_col
// Variant: uncurried
pub fn get_col(M: Array<f64>, n: Int63, w: Int63, c: Int63) -> Array<f64> {
  let callback: Rc<dyn Fn(Int63, Array<f64>) -> bool> = Rc::new(move |_v6: Int63, v7: Array<f64>| -> bool {
    std::mem::drop(v7);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<f64>) -> Array<f64>> = Rc::new({
    move |i: Int63, x: Array<f64>| -> Array<f64> {
      let w = &w;
      let c = &c;
      let tmp = M.get_cloned(i * Clone::clone(w) + Clone::clone(c));
      x.set(i, tmp)
    }
  });
  let tmp_1 = Array::<f64>::make(n, __rocq_global_371);
  loop_::<Array<f64>>(n, callback, callback_1, int63!(0), tmp_1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.i2z
pub fn i2z(x: Int63) -> Rc<BigInt> {
  b::of_uint63(x)
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
          let m1_clone = Rc::clone(m1);
          let m2_clone = Rc::clone(m2);
          if b::le(m1_clone, m2_clone) {
            let m1_clone_1 = Rc::clone(m1);
            let tmp = b::sub(v11, m1_clone_1);
            let tmp_1 = b::shiftl(v9, tmp);
            let tmp_2 = b::add(v3, tmp_1);
            (tmp_2, v5)
          } else {
            let m2_clone_1 = Rc::clone(m2);
            let tmp_3 = b::sub(v5, m2_clone_1);
            let tmp_4 = b::shiftl(v3, tmp_3);
            let tmp_5 = b::add(tmp_4, v9);
            (tmp_5, v11)
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
pub fn dsumf(len: Int63, f: Rc<dyn Fn(Int63) -> (Rc<BigInt>, Rc<BigInt>)>) -> (Rc<BigInt>, Rc<BigInt>) {
  let callback: Rc<dyn Fn(Int63, (Rc<BigInt>, Rc<BigInt>)) -> bool> = Rc::new(move |_v4: Int63, v5: (Rc<BigInt>, Rc<BigInt>)| -> bool {
    std::mem::drop(v5);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, (Rc<BigInt>, Rc<BigInt>)) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new({
    move |k: Int63, acc: (Rc<BigInt>, Rc<BigInt>)| -> (Rc<BigInt>, Rc<BigInt>) {
      let f = &f;
      let tmp = f(k);
      dadd(acc, tmp)
    }
  });
  loop_::<(Rc<BigInt>, Rc<BigInt>)>(len, callback, callback_1, int63!(0), d0(()))
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
  let tmp_1 = b::abs(tmp);
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

// Rocq: Corelib.Floats.PrimFloat.is_nan
pub fn is_nan(f: f64) -> bool {
  negb(rocq_float64::eqb(f, f))
}

// Rocq: Corelib.Floats.PrimFloat.is_zero
pub fn is_zero(f: f64) -> bool {
  rocq_float64::eqb(f, __rocq_global_371)
}

// Rocq: Corelib.Floats.PrimFloat.is_infinity
pub fn is_infinity(f: f64) -> bool {
  rocq_float64::eqb(rocq_float64::abs(f), __rocq_global_1215)
}

// Rocq: Corelib.Floats.PrimFloat.frshiftexp
pub fn frshiftexp(x: f64) -> (f64, Int63) {
  (rocq_float64::frshiftexp_fraction(x), rocq_float64::frshiftexp_exponent(x))
}

// Rocq: Corelib.Floats.PrimFloat.get_sign
pub fn get_sign(f: f64) -> bool {
  let f_1 = if is_zero(f) {
    rocq_float64::div(__rocq_global_820, f)
  } else {
    f
  };
  rocq_float64::ltb(f_1, __rocq_global_371)
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
            let m = b::of_uint63(rocq_float64::normfr_mantissa(v52));
            let tmp_7 = if get_sign(f) {
              b::neg(m)
            } else {
              m
            };
            let r_clone = Clone::clone(r);
            let tmp_8 = b::of_uint63(r_clone);
            let tmp_9 = shift(());
            let tmp_10 = b::sub(tmp_8, tmp_9);
            let tmp_11 = prec(());
            let tmp_12 = b::sub(tmp_10, tmp_11);
            (tmp_7, tmp_12)
          },
        }
      }
    }
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.rowabs
// Variant: uncurried
pub fn rowabs(xa: Array<Array<f64>>, n: Int63) -> Array<(Rc<BigInt>, Rc<BigInt>)> {
  let callback: Rc<dyn Fn(Int63, Array<(Rc<BigInt>, Rc<BigInt>)>) -> bool> = Rc::new(move |_v4: Int63, v5: Array<(Rc<BigInt>, Rc<BigInt>)>| -> bool {
    std::mem::drop(v5);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<(Rc<BigInt>, Rc<BigInt>)>) -> Array<(Rc<BigInt>, Rc<BigInt>)>> = Rc::new({
    let __anf_capture_19 = n;
    move |k: Int63, S: Array<(Rc<BigInt>, Rc<BigInt>)>| -> Array<(Rc<BigInt>, Rc<BigInt>)> {
      let xa = &xa;
      let n = &__anf_capture_19;
      let xa_clone = Clone::clone(xa);
      let tmp = &xa_clone;
      let row = tmp.get_cloned(k);
      std::mem::drop(xa_clone);
      let callback_2: Rc<dyn Fn(Int63) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new({
        move |j: Int63| -> (Rc<BigInt>, Rc<BigInt>) {
          let tmp_1 = row.get_cloned(j);
          dabs(dec(tmp_1))
        }
      });
      let n_clone = Clone::clone(n);
      S.set(k, dsumf(n_clone, callback_2))
    }
  });
  let tmp_2 = Array::<(Rc<BigInt>, Rc<BigInt>)>::make(n, d0(()));
  loop_::<Array<(Rc<BigInt>, Rc<BigInt>)>>(n, callback, callback_1, int63!(0), tmp_2)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dneg
pub fn dneg(x: (Rc<BigInt>, Rc<BigInt>)) -> (Rc<BigInt>, Rc<BigInt>) {
  let x_clone = Clone::clone(&x);
  let tmp = fst::<Rc<BigInt>, Rc<BigInt>>(x_clone);
  let tmp_1 = b::neg(tmp);
  let tmp_2 = snd::<Rc<BigInt>, Rc<BigInt>>(x);
  (tmp_1, tmp_2)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dleb
// Variant: uncurried
pub fn dleb(x: (Rc<BigInt>, Rc<BigInt>), y: (Rc<BigInt>, Rc<BigInt>)) -> bool {
  let tmp = b::zero();
  let tmp_1 = fst::<Rc<BigInt>, Rc<BigInt>>(dadd(y, dneg(x)));
  b::le(tmp, tmp_1)
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
pub fn maxb(len: Int63, h: Rc<dyn Fn(Int63) -> ((Rc<BigInt>, Rc<BigInt>), bool)>) -> ((Rc<BigInt>, Rc<BigInt>), bool) {
  let callback: Rc<dyn Fn(Int63, ((Rc<BigInt>, Rc<BigInt>), bool)) -> bool> = Rc::new(move |_v4: Int63, v5: ((Rc<BigInt>, Rc<BigInt>), bool)| -> bool {
    std::mem::drop(v5);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, ((Rc<BigInt>, Rc<BigInt>), bool)) -> ((Rc<BigInt>, Rc<BigInt>), bool)> = Rc::new({
    move |i: Int63, st: ((Rc<BigInt>, Rc<BigInt>), bool)| -> ((Rc<BigInt>, Rc<BigInt>), bool) {
      let h = &h;
      let r = h(i);
      let st_clone = Clone::clone(&st);
      let tmp = fst::<(Rc<BigInt>, Rc<BigInt>), bool>(st_clone);
      let r_clone = Clone::clone(&r);
      (dmax(tmp, fst::<(Rc<BigInt>, Rc<BigInt>), bool>(r_clone)), andb(snd::<(Rc<BigInt>, Rc<BigInt>), bool>(st), snd::<(Rc<BigInt>, Rc<BigInt>), bool>(r)))
    }
  });
  loop_::<((Rc<BigInt>, Rc<BigInt>), bool)>(len, callback, callback_1, int63!(0), (d0(()), true))
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
pub fn dsumb(len: Int63, g: Rc<dyn Fn(Int63) -> f64>, f: Rc<dyn Fn(Int63, f64) -> (Rc<BigInt>, Rc<BigInt>)>) -> ((Rc<BigInt>, Rc<BigInt>), bool) {
  let callback: Rc<dyn Fn(Int63, ((Rc<BigInt>, Rc<BigInt>), bool)) -> bool> = Rc::new(move |_v5: Int63, v6: ((Rc<BigInt>, Rc<BigInt>), bool)| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, ((Rc<BigInt>, Rc<BigInt>), bool)) -> ((Rc<BigInt>, Rc<BigInt>), bool)> = Rc::new({
    move |k: Int63, st: ((Rc<BigInt>, Rc<BigInt>), bool)| -> ((Rc<BigInt>, Rc<BigInt>), bool) {
      let g = &g;
      let f = &f;
      let d = g(k);
      let st_clone = Clone::clone(&st);
      let tmp = fst::<(Rc<BigInt>, Rc<BigInt>), bool>(st_clone);
      let tmp_1 = f(k, d);
      (dadd(tmp, tmp_1), andb(snd::<(Rc<BigInt>, Rc<BigInt>), bool>(st), is_finite(d)))
    }
  });
  loop_::<((Rc<BigInt>, Rc<BigInt>), bool)>(len, callback, callback_1, int63!(0), (d0(()), true))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fdot
// Variant: uncurried
pub fn fdot_owned(X: Array<f64>, ox: Int63, Y: Array<f64>, oy: Int63, len: Int63) -> f64 {
  let callback: Rc<dyn Fn(Int63, f64) -> bool> = Rc::new(move |_v7: Int63, _v8: f64| -> bool {
    true
  });
  let callback_1: Rc<dyn Fn(Int63, f64) -> f64> = Rc::new({
    move |k: Int63, s: f64| -> f64 {
      let ox = &ox;
      let X = &X;
      let oy = &oy;
      let Y = &Y;
      let tmp = X.get_cloned(Clone::clone(ox) + k);
      let tmp_1 = Y.get_cloned(Clone::clone(oy) + k);
      rocq_float64::add(s, rocq_float64::mul(tmp, tmp_1))
    }
  });
  loop_::<f64>(len, callback, callback_1, int63!(0), __rocq_global_371)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fdot
// Variant: borrowed, uncurried
pub fn fdot(X: &Array<f64>, ox: Int63, Y: &Array<f64>, oy: Int63, len: Int63) -> f64 {
  let len_1 = len;
  let callback: Rc<dyn Fn(Int63, f64) -> bool> = Rc::new(move |_v10: Int63, _v11: f64| -> bool {
    true
  });
  let X_clone = Clone::clone(X);
  let Y_clone = Clone::clone(Y);
  let callback_1: Rc<dyn Fn(Int63, f64) -> f64> = Rc::new({
    move |k: Int63, s: f64| -> f64 {
      let ox = &ox;
      let X = &X_clone;
      let oy = &oy;
      let Y = &Y_clone;
      let tmp = X.get_cloned(Clone::clone(ox) + k);
      let tmp_1 = Y.get_cloned(Clone::clone(oy) + k);
      rocq_float64::add(s, rocq_float64::mul(tmp, tmp_1))
    }
  });
  loop_::<f64>(len_1, callback, callback_1, int63!(0), __rocq_global_371)
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
  let tmp_2 = b::mul(tmp, tmp_1);
  let tmp_3 = snd::<Rc<BigInt>, Rc<BigInt>>(x);
  let tmp_4 = snd::<Rc<BigInt>, Rc<BigInt>>(y);
  let tmp_5 = b::add(tmp_3, tmp_4);
  (tmp_2, tmp_5)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.erow
// Variant: borrowed, uncurried
pub fn erow(n: Int63, Q: &Array<f64>, AT: &Array<f64>, S: &Array<(Rc<BigInt>, Rc<BigInt>)>, lamd: (Rc<BigInt>, Rc<BigInt>), mud2: (Rc<BigInt>, Rc<BigInt>), i: Int63) -> ((Rc<BigInt>, Rc<BigInt>), bool) {
  let lamd_1 = lamd;
  let mud2_1 = mud2;
  let Q_clone = Clone::clone(Q);
  let AT_clone = Clone::clone(AT);
  let callback: Rc<dyn Fn(Int63) -> f64> = Rc::new({
    let __anf_capture_23 = i;
    let __anf_capture_29 = n;
    move |j: Int63| -> f64 {
      let i = &__anf_capture_23;
      let Q = &Q_clone;
      let AT = &AT_clone;
      let tmp = Clone::clone(i) * Clone::clone(&__anf_capture_29);
      let tmp_1 = j * Clone::clone(&__anf_capture_29);
      let tmp_2 = Clone::clone(&__anf_capture_29);
      fdot(Q, tmp, AT, tmp_1, tmp_2)
    }
  });
  let callback_1: Rc<dyn Fn(Int63, f64) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new({
    let __anf_capture_61 = i;
    move |j: Int63, d: f64| -> (Rc<BigInt>, Rc<BigInt>) {
      let i = &__anf_capture_61;
      let i_clone = Clone::clone(i);
      let tmp_3 = if i_clone == j {
        let tmp_4 = b::one();
        b::identity(tmp_4)
      } else {
        b::zero()
      };
      dabs(dsub(dint_owned(tmp_3), dec(d)))
    }
  });
  let e = dsumb(n, callback, callback_1);
  let Q_clone_1 = Clone::clone(Q);
  let S_clone = Clone::clone(S);
  let callback_2: Rc<dyn Fn(Int63) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new({
    let __anf_capture_123 = i;
    let __anf_capture_125 = n;
    move |k: Int63| -> (Rc<BigInt>, Rc<BigInt>) {
      let i = &__anf_capture_123;
      let n = &__anf_capture_125;
      let Q = &Q_clone_1;
      let S = &S_clone;
      let tmp_5 = dabs(dec(Q.get_cloned(Clone::clone(i) * Clone::clone(n) + k)));
      let tmp_6 = S.get_cloned(k);
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
pub fn rowR(n: Int63, Q: &Array<f64>, i: Int63) -> ((Rc<BigInt>, Rc<BigInt>), bool) {
  let Q_clone = Clone::clone(Q);
  let callback: Rc<dyn Fn(Int63) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new({
    let __anf_capture_16 = n;
    move |k: Int63| -> (Rc<BigInt>, Rc<BigInt>) {
      let i = &i;
      let n = &__anf_capture_16;
      let tmp = Q_clone.get_cloned(Clone::clone(i) * Clone::clone(n) + k);
      dabs(dec(tmp))
    }
  });
  (dsumf(n, callback), true)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.resid
// Variant: borrowed, uncurried
pub fn resid(n: Int63, xa: &Array<Array<f64>>, xb: &Array<f64>, xt: &Array<f64>, lamd: (Rc<BigInt>, Rc<BigInt>), mud1: (Rc<BigInt>, Rc<BigInt>), i: Int63) -> ((Rc<BigInt>, Rc<BigInt>), bool) {
  let n_1 = n;
  let lamd_1 = lamd;
  let mud1_1 = mud1;
  let i_1 = i;
  let xa_clone = Clone::clone(xa);
  let tmp = &xa_clone;
  let row = tmp.get_cloned(i_1);
  std::mem::drop(xa_clone);
  let tmp_1 = int63!(0);
  let row_clone = Clone::clone(&row);
  let d = fdot_owned(row_clone, int63!(0), Clone::clone(xt), tmp_1, n_1);
  let tmp_2 = dabs(dsub(dec(xb.get_cloned(i_1)), dec(d)));
  let xt_clone = Clone::clone(xt);
  let callback: Rc<dyn Fn(Int63) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new({
    let __anf_capture_68 = row;
    move |j: Int63| -> (Rc<BigInt>, Rc<BigInt>) {
      let row = &__anf_capture_68;
      let xt = &xt_clone;
      let tmp_3 = dec(row.get_cloned(j));
      let tmp_4 = xt.get_cloned(j);
      dabs(dmul(tmp_3, dec(tmp_4)))
    }
  });
  let tmp_5 = dadd(tmp_2, dmul(lamd_1, dsumf(n_1, callback)));
  (dadd(tmp_5, mud1_1), is_finite(d))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dltb
// Variant: uncurried
pub fn dltb(x: (Rc<BigInt>, Rc<BigInt>), y: (Rc<BigInt>, Rc<BigInt>)) -> bool {
  let tmp = b::zero();
  let tmp_1 = fst::<Rc<BigInt>, Rc<BigInt>>(dadd(y, dneg(x)));
  b::lt(tmp, tmp_1)
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
pub fn certify(n: Int63, xa: Array<Array<f64>>, xb: Array<f64>, AT: Array<f64>, Q: Array<f64>, xt: Array<f64>) -> bool {
  let nz = i2z(n);
  let tmp = b::one();
  let tmp_1 = b::twice_plus_one(tmp);
  let tmp_2 = b::identity(tmp_1);
  let nz_clone = Rc::clone(&nz);
  let tmp_3 = b::mul(tmp_2, nz_clone);
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
  let tmp_14 = b::mul(tmp_13, nz_clone_1);
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
  let tmp_30 = b::mul(tmp_29, nz_clone_2);
  let tmp_31 = b::mul(tmp_30, nz);
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
  let xa_clone = Clone::clone(&xa);
  let S = rowabs(xa_clone, n);
  let Q_clone = Clone::clone(&Q);
  let AT_clone = Clone::clone(&AT);
  let S_clone = Clone::clone(&S);
  let lamd_clone = Clone::clone(&lamd);
  let tmp_44 = lamd_clone;
  let mud2_clone = Clone::clone(&mud2);
  let callback: Rc<dyn Fn(Int63) -> ((Rc<BigInt>, Rc<BigInt>), bool)> = Rc::new({
    let __anf_capture_189 = n;
    move |v201: Int63| -> ((Rc<BigInt>, Rc<BigInt>), bool) {
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
      let Q_clone_1 = Clone::clone(&Q);
      let callback_1: Rc<dyn Fn(Int63) -> ((Rc<BigInt>, Rc<BigInt>), bool)> = Rc::new({
        let __anf_capture_237 = n;
        move |v241: Int63| -> ((Rc<BigInt>, Rc<BigInt>), bool) {
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
          let xt_clone = Clone::clone(&xt);
          let callback_2: Rc<dyn Fn(Int63) -> ((Rc<BigInt>, Rc<BigInt>), bool)> = Rc::new({
            let __anf_capture_278 = n;
            let __anf_capture_280 = xa;
            let __anf_capture_286 = lamd;
            move |v290: Int63| -> ((Rc<BigInt>, Rc<BigInt>), bool) {
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
              let tmp_52 = xt.length();
              std::mem::drop(xt);
              let tmp_53 = andb(tmp_51, tmp_52 == n);
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

// Rocq: EquationsolverExact.equationsolver_exact_implem.row_exp
// Variant: uncurried
pub fn row_exp(n: Int63, row: Array<f64>, bi: f64) -> Rc<BigInt> {
  let callback: Rc<dyn Fn(Int63, Rc<BigInt>) -> bool> = Rc::new(move |_v5: Int63, v6: Rc<BigInt>| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Rc<BigInt>) -> Rc<BigInt>> = Rc::new({
    move |j: Int63, E: Rc<BigInt>| -> Rc<BigInt> {
      let tmp = row.get_cloned(j);
      let tmp_1 = snd::<Rc<BigInt>, Rc<BigInt>>(dec(tmp));
      b::min(E, tmp_1)
    }
  });
  let tmp_2 = b::zero();
  let tmp_3 = snd::<Rc<BigInt>, Rc<BigInt>>(dec(bi));
  let tmp_4 = b::min(tmp_2, tmp_3);
  loop_::<Rc<BigInt>>(n, callback, callback_1, int63!(0), tmp_4)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.scale
// Variant: uncurried
pub fn scale_owned(f: f64, E: Rc<BigInt>) -> Rc<BigInt> {
  let tmp = fst::<Rc<BigInt>, Rc<BigInt>>(dec(f));
  let tmp_1 = snd::<Rc<BigInt>, Rc<BigInt>>(dec(f));
  let tmp_2 = b::sub(tmp_1, E);
  b::shiftl(tmp, tmp_2)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.scale
// Variant: borrowed, uncurried
pub fn scale(f: f64, E: &Rc<BigInt>) -> Rc<BigInt> {
  let f_1 = f;
  let tmp = fst::<Rc<BigInt>, Rc<BigInt>>(dec(f_1));
  let tmp_1 = snd::<Rc<BigInt>, Rc<BigInt>>(dec(f_1));
  let E_clone = Rc::clone(E);
  let tmp_2 = b::sub(tmp_1, E_clone);
  b::shiftl(tmp, tmp_2)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.fill_row
// Variant: uncurried
pub fn fill_row(n: Int63, w: Int63, i: Int63, row: Array<f64>, E: Rc<BigInt>, T: Array<Rc<BigInt>>) -> Array<Rc<BigInt>> {
  let callback: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> bool> = Rc::new(move |_v8: Int63, v9: Array<Rc<BigInt>>| -> bool {
    std::mem::drop(v9);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = Rc::new({
    move |j: Int63, T: Array<Rc<BigInt>>| -> Array<Rc<BigInt>> {
      let i = &i;
      let w = &w;
      let row = &row;
      let E = &E;
      let tmp = Clone::clone(i) * Clone::clone(w) + j;
      let tmp_1 = scale(row.get_cloned(j), E);
      T.set(tmp, tmp_1)
    }
  });
  loop_::<Array<Rc<BigInt>>>(n, callback, callback_1, int63!(0), T)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.build_step
// Variant: uncurried
pub fn build_step(a_1: Array<Array<f64>>, b_1: Array<f64>, n: Int63, w: Int63, i: Int63, T: Array<Rc<BigInt>>) -> Array<Rc<BigInt>> {
  let tmp = a_1;
  let tmp_1 = &tmp;
  let row = tmp_1.get_cloned(i);
  std::mem::drop(tmp);
  let bi = b_1.get_cloned(i);
  std::mem::drop(b_1);
  let row_clone = Clone::clone(&row);
  let E = row_exp(n, row_clone, bi);
  let E_clone = Rc::clone(&E);
  let T_1 = fill_row(n, w, i, row, E_clone, T);
  let tmp_2 = i * w + n;
  let tmp_3 = scale_owned(bi, E);
  T_1.set(tmp_2, tmp_3)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.build
// Variant: uncurried
pub fn build(a_1: Array<Array<f64>>, b_1: Array<f64>, n: Int63, w: Int63) -> Array<Rc<BigInt>> {
  let callback: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> bool> = Rc::new(move |_v6: Int63, v7: Array<Rc<BigInt>>| -> bool {
    std::mem::drop(v7);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = Rc::new({
    let __anf_capture_27 = n;
    let __anf_capture_29 = w;
    move |v31: Int63, v32: Array<Rc<BigInt>>| -> Array<Rc<BigInt>> {
      let a_clone = Clone::clone(&a_1);
      let b_clone = Clone::clone(&b_1);
      let tmp = Clone::clone(&__anf_capture_27);
      let tmp_1 = Clone::clone(&__anf_capture_29);
      build_step(a_clone, b_clone, tmp, tmp_1, v31, v32)
    }
  });
  let tmp_2 = n * w;
  let tmp_3 = b::zero();
  loop_::<Array<Rc<BigInt>>>(n, callback, callback_1, int63!(0), Array::<Rc<BigInt>>::make(tmp_2, tmp_3))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.find_piv
// Variant: uncurried
pub fn find_piv(T: Array<Rc<BigInt>>, n: Int63, w: Int63, c: Int63, r: Int63) -> Int63 {
  let callback: Rc<dyn Fn(Int63, Int63) -> bool> = Rc::new(move |_v7: Int63, _v8: Int63| -> bool {
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Int63) -> Int63> = Rc::new({
    let __anf_capture_24 = n;
    move |i: Int63, s: Int63| -> Int63 {
      let n = &__anf_capture_24;
      let w = &w;
      let c = &c;
      let T = &T;
      let n_clone = Clone::clone(n);
      if s == n_clone {
        let tmp = T.get_cloned(i * Clone::clone(w) + Clone::clone(c));
        let tmp_1 = b::zero();
        if b::equal(tmp, tmp_1) {
          s
        } else {
          i
        }
      } else {
        s
      }
    }
  });
  loop_::<Int63>(n, callback, callback_1, r, n)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.swap_rows
// Variant: uncurried
pub fn swap_rows(T: Array<Rc<BigInt>>, w: Int63, q: Int63, r: Int63) -> Array<Rc<BigInt>> {
  let callback: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> bool> = Rc::new(move |_v6: Int63, v7: Array<Rc<BigInt>>| -> bool {
    std::mem::drop(v7);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = Rc::new({
    let __anf_capture_25 = w;
    move |j: Int63, T: Array<Rc<BigInt>>| -> Array<Rc<BigInt>> {
      let r = &r;
      let q = &q;
      let w = &__anf_capture_25;
      let x = T.get_cloned(Clone::clone(r) * Clone::clone(w) + j);
      let y = T.get_cloned(Clone::clone(q) * Clone::clone(w) + j);
      let tmp = T.set(Clone::clone(r) * Clone::clone(w) + j, y);
      let q_clone = Clone::clone(q);
      let w_clone = Clone::clone(w);
      tmp.set(q_clone * w_clone + j, x)
    }
  });
  loop_::<Array<Rc<BigInt>>>(w, callback, callback_1, int63!(0), T)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.upd_row
// Variant: uncurried
pub fn upd_row(T: Array<Rc<BigInt>>, w: Int63, i: Int63, r: Int63, a_1: Rc<BigInt>, b_1: Rc<BigInt>) -> Array<Rc<BigInt>> {
  let callback: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> bool> = Rc::new(move |_v8: Int63, v9: Array<Rc<BigInt>>| -> bool {
    std::mem::drop(v9);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = Rc::new({
    let __anf_capture_33 = w;
    move |j: Int63, T: Array<Rc<BigInt>>| -> Array<Rc<BigInt>> {
      let i = &i;
      let a_1 = &a_1;
      let r = &r;
      let w = &__anf_capture_33;
      let b_1 = &b_1;
      let tmp = Clone::clone(i) * Clone::clone(w) + j;
      let tmp_1 = T.get_cloned(Clone::clone(i) * Clone::clone(w) + j);
      let a_clone = Rc::clone(a_1);
      let tmp_2 = b::mul(a_clone, tmp_1);
      let tmp_3 = T.get_cloned(Clone::clone(r) * Clone::clone(w) + j);
      let b_clone = Rc::clone(b_1);
      let tmp_4 = b::mul(b_clone, tmp_3);
      let tmp_5 = b::sub(tmp_2, tmp_4);
      T.set(tmp, tmp_5)
    }
  });
  loop_::<Array<Rc<BigInt>>>(w, callback, callback_1, int63!(0), T)
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
          let tmp_4 = b::mul(tmp_3, v20);
          let tmp_5 = b::one();
          let tmp_6 = b::identity(tmp_5);
          let r_ = b::add(tmp_4, tmp_6);
          let r__clone = Rc::clone(&r_);
          let b_clone_1 = Rc::clone(&b_1);
          if b::lt(r__clone, b_clone_1) {
            std::mem::drop(b_1);
            let tmp_7 = b::one();
            let tmp_8 = b::twice(tmp_7);
            let tmp_9 = b::identity(tmp_8);
            let tmp_10 = b::mul(tmp_9, v18);
            (tmp_10, r_)
          } else {
            let tmp_11 = b::one();
            let tmp_12 = b::twice(tmp_11);
            let tmp_13 = b::identity(tmp_12);
            let tmp_14 = b::mul(tmp_13, v18);
            let tmp_15 = b::one();
            let tmp_16 = b::identity(tmp_15);
            let tmp_17 = b::add(tmp_14, tmp_16);
            let tmp_18 = b::sub(r_, b_1);
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
          let r_ = b::mul(tmp_22, v131);
          let r__clone_1 = Rc::clone(&r_);
          let b_clone_3 = Rc::clone(&b_1);
          if b::lt(r__clone_1, b_clone_3) {
            std::mem::drop(b_1);
            let tmp_23 = b::one();
            let tmp_24 = b::twice(tmp_23);
            let tmp_25 = b::identity(tmp_24);
            let tmp_26 = b::mul(tmp_25, v129);
            (tmp_26, r_)
          } else {
            let tmp_27 = b::one();
            let tmp_28 = b::twice(tmp_27);
            let tmp_29 = b::identity(tmp_28);
            let tmp_30 = b::mul(tmp_29, v129);
            let tmp_31 = b::one();
            let tmp_32 = b::identity(tmp_31);
            let tmp_33 = b::add(tmp_30, tmp_32);
            let tmp_34 = b::sub(r_, b_1);
            (tmp_33, tmp_34)
          }
        },
      }
    },
    b::PositiveTag::One => {
      let tmp_35 = b::one();
      let tmp_36 = b::twice(tmp_35);
      let tmp_37 = b::identity(tmp_36);
      if b::le(tmp_37, b_1) {
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
                  let tmp_6 = b::neg(v62);
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
                  let tmp_10 = b::add(v62, tmp_9);
                  let tmp_11 = b::neg(tmp_10);
                  let tmp_12 = b::add(b_1, v64);
                  (tmp_11, tmp_12)
                },
                b::IntegerTag::Negative => {
                  std::mem::drop(a_1);
                  let q_clone_2 = Rc::clone(q);
                  let p = b::integer_magnitude(q_clone_2);
                  std::mem::drop(p);
                  let tmp_13 = b::one();
                  let tmp_14 = b::identity(tmp_13);
                  let tmp_15 = b::add(v62, tmp_14);
                  let tmp_16 = b::neg(tmp_15);
                  let tmp_17 = b::add(b_1, v64);
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
                  let tmp_21 = b::neg(v186);
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
                  let tmp_25 = b::add(v186, tmp_24);
                  let tmp_26 = b::neg(tmp_25);
                  let tmp_27 = b::sub(b_1, v188);
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
                  let tmp_30 = b::add(v186, tmp_29);
                  let tmp_31 = b::neg(tmp_30);
                  let tmp_32 = b::sub(b_1, v188);
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
              let tmp_35 = b::neg(v291);
              (v289, tmp_35)
            },
          }
        },
      }
    },
  }
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
pub fn zgcd_owned(a_1: Rc<BigInt>, b_1: Rc<BigInt>) -> Rc<BigInt> {
  let tmp = b::abs(a_1);
  let tmp_1 = b::abs(b_1);
  zgcd_loop_1(tmp, tmp_1)
}

// Rocq: StdGalilei.bigint.zgcd
// Variant: borrowed, uncurried
pub fn zgcd(a_1: &Rc<BigInt>, b_1: &Rc<BigInt>) -> Rc<BigInt> {
  let a_clone = Rc::clone(a_1);
  let tmp = b::abs(a_clone);
  let b_clone = Rc::clone(b_1);
  let tmp_1 = b::abs(b_clone);
  zgcd_loop_1(tmp, tmp_1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.row_gcd
// Variant: uncurried
pub fn row_gcd(T: Array<Rc<BigInt>>, w: Int63, i: Int63) -> Rc<BigInt> {
  let callback: Rc<dyn Fn(Int63, Rc<BigInt>) -> bool> = Rc::new(move |_v5: Int63, v6: Rc<BigInt>| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Rc<BigInt>) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_22 = w;
    move |j: Int63, g: Rc<BigInt>| -> Rc<BigInt> {
      let i = &i;
      let w = &__anf_capture_22;
      let tmp = T.get_cloned(Clone::clone(i) * Clone::clone(w) + j);
      zgcd_owned(g, tmp)
    }
  });
  let tmp_1 = b::zero();
  loop_::<Rc<BigInt>>(w, callback, callback_1, int63!(0), tmp_1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.div_row
// Variant: uncurried
pub fn div_row(T: Array<Rc<BigInt>>, w: Int63, i: Int63, g: Rc<BigInt>) -> Array<Rc<BigInt>> {
  let callback: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> bool> = Rc::new(move |_v6: Int63, v7: Array<Rc<BigInt>>| -> bool {
    std::mem::drop(v7);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = Rc::new({
    let __anf_capture_23 = w;
    move |j: Int63, T: Array<Rc<BigInt>>| -> Array<Rc<BigInt>> {
      let i = &i;
      let w = &__anf_capture_23;
      let g = &g;
      let tmp = Clone::clone(i) * Clone::clone(w) + j;
      let tmp_1 = T.get_cloned(Clone::clone(i) * Clone::clone(w) + j);
      let g_clone = Rc::clone(g);
      let tmp_2 = b::div(tmp_1, g_clone);
      T.set(tmp, tmp_2)
    }
  });
  loop_::<Array<Rc<BigInt>>>(w, callback, callback_1, int63!(0), T)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.elim_row
// Variant: uncurried
pub fn elim_row(w: Int63, c: Int63, r: Int63, a_1: Rc<BigInt>, i: Int63, T: Array<Rc<BigInt>>) -> Array<Rc<BigInt>> {
  if i == r {
    std::mem::drop(a_1);
    T
  } else {
    let b_1 = T.get_cloned(i * w + c);
    let tmp = b::zero();
    let b_clone = Rc::clone(&b_1);
    if b::equal(b_clone, tmp) {
      std::mem::drop(b_1);
      std::mem::drop(a_1);
      T
    } else {
      let T_1 = upd_row(T, w, i, r, a_1, b_1);
      let T_clone = Clone::clone(&T_1);
      let g = row_gcd(T_clone, w, i);
      let tmp_1 = b::one();
      let tmp_2 = b::identity(tmp_1);
      let g_clone = Rc::clone(&g);
      if b::lt(tmp_2, g_clone) {
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
pub fn col_step(n: Int63, w: Int63, c: Int63, st: (Array<Rc<BigInt>>, Int63)) -> (Array<Rc<BigInt>>, Int63) {
  match st {
    (v5, v7) => {
      let r = &v5;
      let r_clone = Clone::clone(r);
      let q = find_piv(r_clone, n, w, c, v7);
      if q == n {
        (v5, v7)
      } else {
        let T = swap_rows(v5, w, q, v7);
        let a_1 = T.get_cloned(v7 * w + c);
        let callback: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> bool> = Rc::new(move |_v65: Int63, v66: Array<Rc<BigInt>>| -> bool {
          std::mem::drop(v66);
          true
        });
        let callback_1: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = Rc::new({
          let __anf_capture_82 = w;
          let __anf_capture_84 = c;
          let __anf_capture_86 = v7;
          move |v90: Int63, v91: Array<Rc<BigInt>>| -> Array<Rc<BigInt>> {
            let tmp = Clone::clone(&__anf_capture_82);
            let tmp_1 = Clone::clone(&__anf_capture_84);
            let tmp_2 = Clone::clone(&__anf_capture_86);
            let a_clone = Rc::clone(&a_1);
            elim_row(tmp, tmp_1, tmp_2, a_clone, v90, v91)
          }
        });
        (loop_::<Array<Rc<BigInt>>>(n, callback, callback_1, int63!(0), T), v7 + int63!(1))
      }
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.eliminate
// Variant: uncurried
pub fn eliminate(n: Int63, w: Int63, T: Array<Rc<BigInt>>) -> (Array<Rc<BigInt>>, Int63) {
  let callback: Rc<dyn Fn(Int63, (Array<Rc<BigInt>>, Int63)) -> bool> = Rc::new(move |_v5: Int63, v6: (Array<Rc<BigInt>>, Int63)| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, (Array<Rc<BigInt>>, Int63)) -> (Array<Rc<BigInt>>, Int63)> = Rc::new({
    let __anf_capture_18 = n;
    move |v22: Int63, v23: (Array<Rc<BigInt>>, Int63)| -> (Array<Rc<BigInt>>, Int63) {
      let tmp = Clone::clone(&__anf_capture_18);
      let w_clone = Clone::clone(&w);
      col_step(tmp, w_clone, v22, v23)
    }
  });
  loop_::<(Array<Rc<BigInt>>, Int63)>(n, callback, callback_1, int63!(0), (T, int63!(0)))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.inconsistent
// Variant: uncurried
pub fn inconsistent(T: Array<Rc<BigInt>>, n: Int63, w: Int63, r: Int63) -> bool {
  let callback: Rc<dyn Fn(Int63, bool) -> bool> = Rc::new(move |_v6: Int63, _v7: bool| -> bool {
    true
  });
  let callback_1: Rc<dyn Fn(Int63, bool) -> bool> = Rc::new({
    let __anf_capture_23 = n;
    move |i: Int63, fl: bool| -> bool {
      let w = &w;
      let n = &__anf_capture_23;
      let tmp = T.get_cloned(i * Clone::clone(w) + Clone::clone(n));
      let tmp_1 = b::zero();
      orb(fl, negb(b::equal(tmp, tmp_1)))
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
      b::succ(tmp)
    },
    b::PositiveTag::Even => {
      let p = b::positive_tail(n);
      let tmp_1 = digits2_pos(p);
      b::succ(tmp_1)
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

// Rocq: Corelib.Floats.SpecFloat.emin
// Variant: uncurried
pub fn emin(prec_1: Rc<BigInt>, emax_1: Rc<BigInt>) -> Rc<BigInt> {
  let tmp = b::one();
  let tmp_1 = b::twice_plus_one(tmp);
  let tmp_2 = b::identity(tmp_1);
  let tmp_3 = b::sub(tmp_2, emax_1);
  b::sub(tmp_3, prec_1)
}

// Rocq: Corelib.Floats.SpecFloat.fexp
// Variant: uncurried
pub fn fexp(prec_1: Rc<BigInt>, emax_1: Rc<BigInt>, e: Rc<BigInt>) -> Rc<BigInt> {
  let prec_clone = Rc::clone(&prec_1);
  let tmp = b::sub(e, prec_clone);
  let tmp_1 = emin(prec_1, emax_1);
  b::max(tmp, tmp_1)
}

// Rocq: Corelib.Floats.SpecFloat.new_location_even
// Variant: uncurried
pub fn new_location_even(nb_steps: Rc<BigInt>, k: Rc<BigInt>) -> Rc<location> {
  let tmp = b::zero();
  let k_clone = Rc::clone(&k);
  if b::equal(k_clone, tmp) {
    std::mem::drop(nb_steps);
    std::mem::drop(k);
    Rc::new(location::loc_Exact)
  } else {
    let tmp_1 = b::one();
    let tmp_2 = b::twice(tmp_1);
    let tmp_3 = b::identity(tmp_2);
    let tmp_4 = b::mul(tmp_3, k);
    Rc::new(location::loc_Inexact(b::compare(tmp_4, nb_steps)))
  }
}

// Rocq: Corelib.Floats.SpecFloat.new_location_odd
// Variant: uncurried
pub fn new_location_odd(nb_steps: Rc<BigInt>, k: Rc<BigInt>) -> Rc<location> {
  let tmp = b::zero();
  let k_clone = Rc::clone(&k);
  if b::equal(k_clone, tmp) {
    std::mem::drop(nb_steps);
    std::mem::drop(k);
    Rc::new(location::loc_Exact)
  } else {
    let tmp_1 = b::one();
    let tmp_2 = b::twice(tmp_1);
    let tmp_3 = b::identity(tmp_2);
    let tmp_4 = b::mul(tmp_3, k);
    let tmp_5 = b::one();
    let tmp_6 = b::identity(tmp_5);
    let tmp_7 = b::add(tmp_4, tmp_6);
    let tmp_8 = match b::compare(tmp_7, nb_steps) {
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
  let tmp: Rc<dyn Fn(Rc<BigInt>) -> Rc<location>> = if b::even(nb_steps_clone) {
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
  let tmp = b::add(d1_1, e1_clone);
  let e2_clone = Rc::clone(&e2);
  let tmp_1 = b::add(d2, e2_clone);
  let tmp_2 = b::sub(tmp, tmp_1);
  let tmp_3 = fexp(prec_1, emax_1, tmp_2);
  let e1_clone_1 = Rc::clone(&e1);
  let e2_clone_1 = Rc::clone(&e2);
  let tmp_4 = b::sub(e1_clone_1, e2_clone_1);
  let e_ = b::min(tmp_3, tmp_4);
  let tmp_5 = b::sub(e1, e2);
  let e__clone = Rc::clone(&e_);
  let s = b::sub(tmp_5, e__clone);
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
      b::shiftl(m1, s)
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
      let tmp_5 = b::add(e, n);
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
  let tmp_2 = b::add(tmp_1, e_clone);
  let tmp_3 = fexp(prec_1, emax_1, tmp_2);
  let e_clone_1 = Rc::clone(&e);
  let tmp_4 = b::sub(tmp_3, e_clone_1);
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
          if b::even(mx_clone) {
            mx
          } else {
            let tmp = b::one();
            let tmp_1 = b::identity(tmp);
            b::add(mx, tmp_1)
          }
        },
        std::cmp::Ordering::Less => {
          mx
        },
        std::cmp::Ordering::Greater => {
          let tmp_2 = b::one();
          let tmp_3 = b::identity(tmp_2);
          b::add(mx, tmp_3)
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
              let tmp_7 = b::sub(emax_1, prec_1);
              let mrs___clone = Rc::clone(mrs__);
              if b::le(mrs___clone, tmp_7) {
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

// Rocq: EquationsolverExact.equationsolver_exact_implem.z2i
pub fn z2i(z: Rc<BigInt>) -> Int63 {
  b::to_uint63(z)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.ldexp'
// Variant: borrowed, uncurried
pub fn ldexp_(f: f64, e: &Rc<BigInt>) -> f64 {
  let f_1 = f;
  let tmp = emax(());
  let tmp_1 = prec(());
  let tmp_2 = emax(());
  let tmp_3 = emin(tmp_1, tmp_2);
  let tmp_4 = b::sub(tmp, tmp_3);
  let e_clone = Rc::clone(e);
  let tmp_5 = b::min(e_clone, tmp_4);
  let tmp_6 = prec(());
  let tmp_7 = emax(());
  let tmp_8 = emin(tmp_6, tmp_7);
  let tmp_9 = emax(());
  let tmp_10 = b::sub(tmp_8, tmp_9);
  let tmp_11 = b::one();
  let tmp_12 = b::identity(tmp_11);
  let tmp_13 = b::sub(tmp_10, tmp_12);
  let e_ = b::max(tmp_5, tmp_13);
  let tmp_14 = shift(());
  let tmp_15 = b::add(e_, tmp_14);
  rocq_float64::ldshiftexp(f_1, z2i(tmp_15))
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
      let pm = rocq_float64::of_uint63(z2i(tmp));
      let f = ldexp_(pm, s);
      if *e {
        std::mem::drop(v42);
        rocq_float64::opp(f)
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
pub fn output(T: Array<Rc<BigInt>>, n: Int63, w: Int63) -> Array<f64> {
  let callback: Rc<dyn Fn(Int63, Array<f64>) -> bool> = Rc::new(move |_v5: Int63, v6: Array<f64>| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<f64>) -> Array<f64>> = Rc::new({
    let __anf_capture_20 = n;
    move |i: Int63, out: Array<f64>| -> Array<f64> {
      let n = &__anf_capture_20;
      let w = &w;
      let tmp = T.get_cloned(i * Clone::clone(w) + Clone::clone(n));
      let tmp_1 = T.get_cloned(i * Clone::clone(w) + i);
      out.set(i, qround(tmp, tmp_1))
    }
  });
  let tmp_2 = Array::<f64>::make(n, __rocq_global_371);
  loop_::<Array<f64>>(n, callback, callback_1, int63!(0), tmp_2)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.solve_exact
// Variant: uncurried
pub fn solve_exact(n: Int63, a_1: Array<Array<f64>>, b_1: Array<f64>) -> Rc<outcome<Array<f64>>> {
  let w = n + int63!(1);
  let T = build(a_1, b_1, n, w);
  let tmp = eliminate(n, w, T);
  match tmp {
    (v30, v32) => {
      let r = &v30;
      let r_clone = Clone::clone(r);
      if inconsistent(r_clone, n, w, v32) {
        std::mem::drop(v30);
        Rc::new(outcome::<Array<f64>>::Inconsistent)
      } else {
        if v32 < n {
          std::mem::drop(v30);
          Rc::new(outcome::<Array<f64>>::Multiple)
        } else {
          Rc::new(outcome::<Array<f64>>::Unique(output(v30, n, w)))
        }
      }
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.free_cols
// Variant: uncurried
pub fn free_cols(pc: Array<Int63>, n: Int63, r: Int63) -> Array<Int63> {
  let callback: Rc<dyn Fn(Int63, Array<bool>) -> bool> = Rc::new(move |_v5: Int63, v6: Array<bool>| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<bool>) -> Array<bool>> = Rc::new({
    move |t: Int63, isp: Array<bool>| -> Array<bool> {
      let tmp = pc.get_cloned(t);
      isp.set(tmp, true)
    }
  });
  let isp = loop_::<Array<bool>>(r, callback, callback_1, int63!(0), Array::<bool>::make(n, false));
  let callback_2: Rc<dyn Fn(Int63, (Array<Int63>, Int63)) -> bool> = Rc::new(move |_v59: Int63, v60: (Array<Int63>, Int63)| -> bool {
    std::mem::drop(v60);
    true
  });
  let callback_3: Rc<dyn Fn(Int63, (Array<Int63>, Int63)) -> (Array<Int63>, Int63)> = Rc::new({
    move |c: Int63, st: (Array<Int63>, Int63)| -> (Array<Int63>, Int63) {
      let isp = &isp;
      match st {
        (v75, v77) => {
          if isp.get_cloned(c) {
            (v75, v77)
          } else {
            (v75.set(v77, c), v77 + int63!(1))
          }
        },
      }
    }
  });
  let tmp_1 = Array::<Int63>::make(n, int63!(0));
  fst::<Array<Int63>, Int63>(loop_::<(Array<Int63>, Int63)>(n, callback_2, callback_3, int63!(0), (tmp_1, int63!(0))))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.mark_D
// Variant: uncurried
pub fn mark_D(perm: Array<Int63>, n: Int63, r: Int63, k: Int63) -> (Array<bool>, Array<Int63>) {
  let callback: Rc<dyn Fn(Int63, (Array<bool>, Array<Int63>)) -> bool> = Rc::new(move |_v6: Int63, v7: (Array<bool>, Array<Int63>)| -> bool {
    std::mem::drop(v7);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, (Array<bool>, Array<Int63>)) -> (Array<bool>, Array<Int63>)> = Rc::new({
    move |t: Int63, st: (Array<bool>, Array<Int63>)| -> (Array<bool>, Array<Int63>) {
      let r = &r;
      let d = perm.get_cloned(Clone::clone(r) + t);
      let st_clone = Clone::clone(&st);
      (fst::<Array<bool>, Array<Int63>>(st_clone).set(d, true), snd::<Array<bool>, Array<Int63>>(st).set(d, t))
    }
  });
  loop_::<(Array<bool>, Array<Int63>)>(k, callback, callback_1, int63!(0), (Array::<bool>::make(n, false), Array::<Int63>::make(n, int63!(0))))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.mark_C
// Variant: uncurried
pub fn mark_C(fc: Array<Int63>, n: Int63, k: Int63) -> Array<bool> {
  let callback: Rc<dyn Fn(Int63, Array<bool>) -> bool> = Rc::new(move |_v5: Int63, v6: Array<bool>| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<bool>) -> Array<bool>> = Rc::new({
    move |t: Int63, C: Array<bool>| -> Array<bool> {
      let tmp = fc.get_cloned(t);
      C.set(tmp, true)
    }
  });
  loop_::<Array<bool>>(k, callback, callback_1, int63!(0), Array::<bool>::make(n, false))
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
      if b::le(tmp_1, m_clone) {
        let tmp_2 = b::shiftl(v6, v8);
        let tmp_3 = b::one();
        let tmp_4 = b::identity(tmp_3);
        (tmp_2, tmp_4)
      } else {
        let tmp_5 = b::one();
        let tmp_6 = b::identity(tmp_5);
        let tmp_7 = b::neg(v8);
        let den = b::shiftl(tmp_6, tmp_7);
        let tmp_8 = int63!(64);
        let callback: Rc<dyn Fn(Int63, ((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool)) -> bool> = Rc::new(move |_v56: Int63, st: ((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool)| -> bool {
          negb(snd::<(((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool>(st))
        });
        let den_clone = Rc::clone(&den);
        let e_clone = Rc::clone(e);
        let callback_1: Rc<dyn Fn(Int63, ((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool)) -> ((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool)> = Rc::new({
          move |_v80: Int63, st: ((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool)| -> ((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool) {
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
                                let ad_clone = Rc::clone(ad);
                                let an_clone = Rc::clone(an);
                                let q = b::div(ad_clone, an_clone);
                                let q_clone = Rc::clone(&q);
                                let y2_clone = Rc::clone(y2);
                                let tmp_10 = b::mul(q_clone, y2_clone);
                                let h = b::add(tmp_10, v101);
                                let q_clone_1 = Rc::clone(&q);
                                let y0_clone = Rc::clone(y0);
                                let tmp_11 = b::mul(q_clone_1, y0_clone);
                                let k = b::add(tmp_11, v90);
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
                                if b::lt(tmp_43, k_clone) {
                                  std::mem::drop(k);
                                  std::mem::drop(h);
                                  std::mem::drop(q);
                                  std::mem::drop(v110);
                                  std::mem::drop(v106);
                                  std::mem::drop(v112);
                                  std::mem::drop(v95);
                                  (fst::<(((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool>(st), true)
                                } else {
                                  std::mem::drop(st);
                                  let an_clone_1 = Rc::clone(an);
                                  let tmp_44 = b::mul(q, an_clone_1);
                                  let rem = b::sub(v110, tmp_44);
                                  let e_clone_1 = Rc::clone(e);
                                  let k_clone_1 = Rc::clone(&k);
                                  let tmp_45 = b::mul(e_clone_1, k_clone_1);
                                  let h_clone = Rc::clone(&h);
                                  let den_clone_1 = Rc::clone(den);
                                  let tmp_46 = b::mul(h_clone, den_clone_1);
                                  let tmp_47 = b::sub(tmp_45, tmp_46);
                                  let tmp_48 = b::abs(tmp_47);
                                  let tmp_49 = b::one();
                                  let tmp_50 = b::twice(tmp_49);
                                  let tmp_51 = b::twice_plus_one(tmp_50);
                                  let tmp_52 = b::twice(tmp_51);
                                  let tmp_53 = b::twice(tmp_52);
                                  let tmp_54 = b::twice(tmp_53);
                                  let tmp_55 = b::identity(tmp_54);
                                  let tmp_56 = b::shiftl(tmp_48, tmp_55);
                                  let e_clone_2 = Rc::clone(e);
                                  let tmp_57 = b::abs(e_clone_2);
                                  let k_clone_2 = Rc::clone(&k);
                                  let tmp_58 = b::mul(tmp_57, k_clone_2);
                                  let close = b::le(tmp_56, tmp_58);
                                  let rem_clone = Rc::clone(&rem);
                                  let tmp_59 = (((((v112, rem_clone), h), v106), k), v95);
                                  let tmp_60 = b::zero();
                                  (tmp_59, orb(b::equal(rem, tmp_60), close))
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
        let st = loop_::<((((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool)>(tmp_8, callback, callback_1, int63!(0), ((tmp_68, tmp_70), false));
        let tmp_71 = fst::<(((((Rc<BigInt>, Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), Rc<BigInt>), bool>(st);
        match tmp_71 {
          (v480, v482) => {
            match v480 {
              (v485, v487) => {
                let p0 = &v487;
                match v485 {
                  (v491, v493) => {
                    match v491 {
                      (v496, v498) => {
                        match v496 {
                          (v501, v503) => {
                            let tmp_72 = b::zero();
                            let p0_clone = Rc::clone(p0);
                            if b::lt(tmp_72, p0_clone) {
                              std::mem::drop(v501);
                              std::mem::drop(v503);
                              std::mem::drop(v493);
                              std::mem::drop(v482);
                              (v498, v487)
                            } else {
                              std::mem::drop(v501);
                              std::mem::drop(v503);
                              std::mem::drop(v493);
                              std::mem::drop(v482);
                              std::mem::drop(v498);
                              std::mem::drop(v487);
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
pub fn ratvec(x: Array<f64>, n: Int63) -> (Array<Rc<BigInt>>, Rc<BigInt>) {
  let callback: Rc<dyn Fn(Int63, ((Array<Rc<BigInt>>, Array<Rc<BigInt>>), Rc<BigInt>)) -> bool> = Rc::new(move |_v4: Int63, v5: ((Array<Rc<BigInt>>, Array<Rc<BigInt>>), Rc<BigInt>)| -> bool {
    std::mem::drop(v5);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, ((Array<Rc<BigInt>>, Array<Rc<BigInt>>), Rc<BigInt>)) -> ((Array<Rc<BigInt>>, Array<Rc<BigInt>>), Rc<BigInt>)> = Rc::new({
    move |j: Int63, st: ((Array<Rc<BigInt>>, Array<Rc<BigInt>>), Rc<BigInt>)| -> ((Array<Rc<BigInt>>, Array<Rc<BigInt>>), Rc<BigInt>) {
      let x = &x;
      match st {
        (v20, v22) => {
          let y = &v22;
          match v20 {
            (v26, v28) => {
              let tmp = x.get_cloned(j);
              let tmp_1 = rat1(tmp);
              match tmp_1 {
                (v38, v40) => {
                  let h = &v40;
                  let tmp_2 = v26.set(j, v38);
                  let h_clone = Rc::clone(h);
                  let tmp_3 = (tmp_2, v28.set(j, h_clone));
                  let tmp_4 = zgcd(y, h);
                  let tmp_5 = b::div(v22, tmp_4);
                  let tmp_6 = b::mul(tmp_5, v40);
                  (tmp_3, tmp_6)
                },
              }
            },
          }
        },
      }
    }
  });
  let tmp_7 = b::zero();
  let tmp_8 = Array::<Rc<BigInt>>::make(n, tmp_7);
  let tmp_9 = b::one();
  let tmp_10 = b::identity(tmp_9);
  let tmp_11 = (tmp_8, Array::<Rc<BigInt>>::make(n, tmp_10));
  let tmp_12 = b::one();
  let tmp_13 = b::identity(tmp_12);
  let tmp_14 = loop_::<((Array<Rc<BigInt>>, Array<Rc<BigInt>>), Rc<BigInt>)>(n, callback, callback_1, int63!(0), (tmp_11, tmp_13));
  match tmp_14 {
    (v143, v145) => {
      let p = &v145;
      match v143 {
        (v149, v151) => {
          let callback_2: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> bool> = Rc::new(move |_v155: Int63, v156: Array<Rc<BigInt>>| -> bool {
            std::mem::drop(v156);
            true
          });
          let p_clone = Rc::clone(p);
          let callback_3: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = Rc::new({
            move |j: Int63, P: Array<Rc<BigInt>>| -> Array<Rc<BigInt>> {
              let K = &v149;
              let H = &v151;
              let p = &p_clone;
              let tmp_15 = K.get_cloned(j);
              let tmp_16 = H.get_cloned(j);
              let p_clone_1 = Rc::clone(p);
              let tmp_17 = b::div(p_clone_1, tmp_16);
              let tmp_18 = b::mul(tmp_15, tmp_17);
              P.set(j, tmp_18)
            }
          });
          let tmp_19 = b::zero();
          let tmp_20 = Array::<Rc<BigInt>>::make(n, tmp_19);
          (loop_::<Array<Rc<BigInt>>>(n, callback_2, callback_3, int63!(0), tmp_20), v145)
        },
      }
    },
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.get_row
// Variant: borrowed, uncurried
pub fn get_row(Q: &Array<f64>, n: Int63, i: Int63) -> Array<f64> {
  let callback: Rc<dyn Fn(Int63, Array<f64>) -> bool> = Rc::new(move |_v7: Int63, v8: Array<f64>| -> bool {
    std::mem::drop(v8);
    true
  });
  let Q_clone = Clone::clone(Q);
  let callback_1: Rc<dyn Fn(Int63, Array<f64>) -> Array<f64>> = Rc::new({
    let __anf_capture_25 = n;
    move |k: Int63, x: Array<f64>| -> Array<f64> {
      let i = &i;
      let n = &__anf_capture_25;
      let tmp = Q_clone.get_cloned(Clone::clone(i) * Clone::clone(n) + k);
      x.set(k, tmp)
    }
  });
  let tmp_1 = Array::<f64>::make(n, __rocq_global_371);
  loop_::<Array<f64>>(n, callback, callback_1, int63!(0), tmp_1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.yv
// Variant: borrowed, uncurried
pub fn yv(Q: &Array<f64>, n: Int63, r: Int63, t: Int63) -> Array<Rc<BigInt>> {
  let n_1 = n;
  let r_1 = r;
  let t_1 = t;
  fst::<Array<Rc<BigInt>>, Rc<BigInt>>(ratvec(get_row(Q, n_1, r_1 + t_1), n_1))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.allf
// Variant: uncurried
pub fn allf(len: Int63, p: Rc<dyn Fn(Int63) -> bool>) -> bool {
  let callback: Rc<dyn Fn(Int63, bool) -> bool> = Rc::new(move |_v4: Int63, _v5: bool| -> bool {
    true
  });
  let callback_1: Rc<dyn Fn(Int63, bool) -> bool> = Rc::new({
    move |k: Int63, b_1: bool| -> bool {
      let p = &p;
      let tmp = p(k);
      andb(b_1, tmp)
    }
  });
  loop_::<bool>(len, callback, callback_1, int63!(0), true)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.dzero
pub fn dzero(x: (Rc<BigInt>, Rc<BigInt>)) -> bool {
  let tmp = fst::<Rc<BigInt>, Rc<BigInt>>(x);
  let tmp_1 = b::zero();
  b::equal(tmp, tmp_1)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.zdot
// Variant: uncurried
pub fn zdot_owned(X: Array<f64>, o: Int63, Y: Array<Rc<BigInt>>, len: Int63) -> (Rc<BigInt>, Rc<BigInt>) {
  let callback: Rc<dyn Fn(Int63) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new({
    move |k: Int63| -> (Rc<BigInt>, Rc<BigInt>) {
      let o = &o;
      let X = &X;
      let Y = &Y;
      let tmp = dec(X.get_cloned(Clone::clone(o) + k));
      let tmp_1 = Y.get_cloned(k);
      dmul(tmp, dint_owned(tmp_1))
    }
  });
  dsumf(len, callback)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.zdot
// Variant: borrowed, uncurried
pub fn zdot(X: &Array<f64>, o: Int63, Y: &Array<Rc<BigInt>>, len: Int63) -> (Rc<BigInt>, Rc<BigInt>) {
  let len_1 = len;
  let X_clone = Clone::clone(X);
  let Y_clone = Clone::clone(Y);
  let callback: Rc<dyn Fn(Int63) -> (Rc<BigInt>, Rc<BigInt>)> = Rc::new({
    move |k: Int63| -> (Rc<BigInt>, Rc<BigInt>) {
      let o = &o;
      let X = &X_clone;
      let Y = &Y_clone;
      let tmp = dec(X.get_cloned(Clone::clone(o) + k));
      let tmp_1 = Y.get_cloned(k);
      dmul(tmp, dint_owned(tmp_1))
    }
  });
  dsumf(len_1, callback)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.chk_incons
// Variant: uncurried
pub fn chk_incons(AT: Array<f64>, xb: Array<f64>, n: Int63, y: Array<Rc<BigInt>>) -> bool {
  let y_clone = Clone::clone(&y);
  let callback: Rc<dyn Fn(Int63) -> bool> = Rc::new({
    let __anf_capture_18 = n;
    move |j: Int63| -> bool {
      let AT = &AT;
      let y = &y_clone;
      let n = &__anf_capture_18;
      let tmp = zdot(AT, j * Clone::clone(n), y, Clone::clone(n));
      dzero(tmp)
    }
  });
  andb(allf(n, callback), negb(dzero(zdot_owned(xb, int63!(0), y, n))))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.chk_red
// Variant: uncurried
pub fn chk_red(AT: Array<f64>, xb: Array<f64>, n: Int63, y: Array<Rc<BigInt>>, d: Int63, Df: Array<bool>) -> bool {
  let y_clone = Clone::clone(&y);
  let callback: Rc<dyn Fn(Int63) -> bool> = Rc::new({
    let __anf_capture_21 = n;
    move |j: Int63| -> bool {
      let AT = &AT;
      let y = &y_clone;
      let n = &__anf_capture_21;
      let tmp = zdot(AT, j * Clone::clone(n), y, Clone::clone(n));
      dzero(tmp)
    }
  });
  let tmp_1 = allf(n, callback);
  let y_clone_1 = Clone::clone(&y);
  let tmp_2 = andb(tmp_1, dzero(zdot_owned(xb, int63!(0), y_clone_1, n)));
  let tmp_3 = y.get_cloned(d);
  let tmp_4 = b::zero();
  let tmp_5 = negb(b::equal(tmp_3, tmp_4));
  let callback_1: Rc<dyn Fn(Int63) -> bool> = Rc::new({
    let __anf_capture_99 = d;
    let __anf_capture_101 = y;
    move |i: Int63| -> bool {
      let Df = &Df;
      let d = &__anf_capture_99;
      let y = &__anf_capture_101;
      let tmp_6 = negb(Df.get_cloned(i));
      let tmp_7 = i == Clone::clone(d);
      let tmp_8 = y.get_cloned(i);
      let tmp_9 = b::zero();
      let tmp_10 = orb(tmp_7, b::equal(tmp_8, tmp_9));
      orb(tmp_6, tmp_10)
    }
  });
  let tmp_11 = andb(tmp_5, allf(n, callback_1));
  andb(tmp_2, tmp_11)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.scan_null
// Variant: uncurried
pub fn scan_null(AT: Array<f64>, xb: Array<f64>, Q: Array<f64>, perm: Array<Int63>, fc: Array<Int63>, Df: Array<bool>, n: Int63, r: Int63, k: Int63) -> (bool, bool) {
  let callback: Rc<dyn Fn(Int63, (bool, bool)) -> bool> = Rc::new(move |_v11: Int63, v12: (bool, bool)| -> bool {
    std::mem::drop(v12);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, (bool, bool)) -> (bool, bool)> = Rc::new({
    let __anf_capture_38 = r;
    let __anf_capture_48 = n;
    move |t: Int63, s: (bool, bool)| -> (bool, bool) {
      let Q = &Q;
      let r = &__anf_capture_38;
      let perm = &perm;
      let fc = &fc;
      let AT = &AT;
      let xb = &xb;
      let n = &__anf_capture_48;
      let Df = &Df;
      let y = yv(Q, Clone::clone(n), Clone::clone(r), t);
      let d = perm.get_cloned(Clone::clone(r) + t);
      let s_clone = Clone::clone(&s);
      let tmp = fst::<bool, bool>(s_clone);
      let AT_clone = Clone::clone(AT);
      let xb_clone = Clone::clone(xb);
      let n_clone = Clone::clone(n);
      let y_clone = Clone::clone(&y);
      let tmp_1 = orb(tmp, chk_incons(AT_clone, xb_clone, n_clone, y_clone));
      let tmp_2 = snd::<bool, bool>(s);
      let tmp_3 = andb(d < Clone::clone(n), fc.get_cloned(t) < Clone::clone(n));
      let AT_clone_1 = Clone::clone(AT);
      let xb_clone_1 = Clone::clone(xb);
      let n_clone_1 = Clone::clone(n);
      let Df_clone = Clone::clone(Df);
      let tmp_4 = andb(tmp_3, chk_red(AT_clone_1, xb_clone_1, n_clone_1, y, d, Df_clone));
      (tmp_1, andb(tmp_2, tmp_4))
    }
  });
  loop_::<(bool, bool)>(k, callback, callback_1, int63!(0), (false, r < n))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.bentry
// Variant: borrowed, uncurried
pub fn bentry(xa: &Array<Array<f64>>, Df: &Array<bool>, tix: &Array<Int63>, fc: &Array<Int63>, Cf: &Array<bool>, i: Int63, j: Int63) -> f64 {
  let i_1 = i;
  let j_1 = j;
  if Df.get_cloned(i_1) {
    let tmp = fc.get_cloned(tix.get_cloned(i_1));
    if j_1 == tmp {
      __rocq_global_820
    } else {
      __rocq_global_371
    }
  } else {
    if Cf.get_cloned(j_1) {
      __rocq_global_371
    } else {
      let xa_clone = Clone::clone(xa);
      let tmp_1 = &xa_clone;
      let tmp_2 = tmp_1.get_cloned(i_1);
      std::mem::drop(xa_clone);
      let tmp_3 = tmp_2.get_cloned(j_1);
      std::mem::drop(tmp_2);
      tmp_3
    }
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.padB
// Variant: uncurried
pub fn padB(xa: Array<Array<f64>>, n: Int63, Df: Array<bool>, tix: Array<Int63>, fc: Array<Int63>, Cf: Array<bool>) -> Array<Array<f64>> {
  let tmp = Array::<f64>::make(int63!(0), __rocq_global_371);
  let callback: Rc<dyn Fn(Int63) -> Array<f64>> = Rc::new({
    let __anf_capture_38 = n;
    move |i: Int63| -> Array<f64> {
      let xa = &xa;
      let Df = &Df;
      let tix = &tix;
      let fc = &fc;
      let Cf = &Cf;
      let n = &__anf_capture_38;
      let tmp_1 = __rocq_global_371;
      let xa_clone = Clone::clone(xa);
      let Df_clone = Clone::clone(Df);
      let tix_clone = Clone::clone(tix);
      let fc_clone = Clone::clone(fc);
      let Cf_clone = Clone::clone(Cf);
      let callback_1: Rc<dyn Fn(Int63) -> f64> = Rc::new({
        move |j: Int63| -> f64 {
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
  tab::<Array<f64>>(n, tmp, callback)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.certify_inj
// Variant: uncurried
pub fn certify_inj(n: Int63, xa: Array<Array<f64>>, AT: Array<f64>, Q: Array<f64>) -> bool {
  let nz = i2z(n);
  let tmp = b::one();
  let tmp_1 = b::twice_plus_one(tmp);
  let tmp_2 = b::identity(tmp_1);
  let nz_clone = Rc::clone(&nz);
  let tmp_3 = b::mul(tmp_2, nz_clone);
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
  let tmp_14 = b::mul(tmp_13, nz_clone_1);
  let tmp_15 = b::mul(tmp_14, nz);
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
  let callback: Rc<dyn Fn(Int63) -> ((Rc<BigInt>, Rc<BigInt>), bool)> = Rc::new({
    let __anf_capture_127 = n;
    move |v139: Int63| -> ((Rc<BigInt>, Rc<BigInt>), bool) {
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
pub fn padded_ok(xa: Array<Array<f64>>, n: Int63, Df: Array<bool>, tix: Array<Int63>, fc: Array<Int63>, Cf: Array<bool>) -> bool {
  let B = padB(xa, n, Df, tix, fc, Cf);
  let w = n + int63!(1);
  let B_clone = Clone::clone(&B);
  let tmp = col_thr(B_clone, n);
  let tmp_1 = Array::<f64>::make(n, __rocq_global_371);
  let B_clone_1 = Clone::clone(&B);
  let tmp_2 = init_M(B_clone_1, tmp_1, n, w);
  let tmp_3 = init_Q(n);
  let st = forward(n, w, tmp, tmp_2, tmp_3);
  let tmp_4 = fs_r(&st);
  if tmp_4 == n {
    let B_clone_2 = Clone::clone(&B);
    let tmp_5 = transpose(B_clone_2, n);
    let st_clone = Rc::clone(&st);
    let tmp_6 = backsub(n, w, fs_M_owned(st_clone), fs_Q(st));
    certify_inj(n, B, tmp_5, snd::<Array<f64>, Array<f64>>(tmp_6))
  } else {
    std::mem::drop(B);
    std::mem::drop(st);
    false
  }
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.free_col
// Variant: uncurried
pub fn free_col(pc: Array<Int63>, n: Int63, r: Int63) -> Int63 {
  let callback: Rc<dyn Fn(Int63, Array<bool>) -> bool> = Rc::new(move |_v5: Int63, v6: Array<bool>| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<bool>) -> Array<bool>> = Rc::new({
    move |t: Int63, isp: Array<bool>| -> Array<bool> {
      let tmp = pc.get_cloned(t);
      isp.set(tmp, true)
    }
  });
  let isp = loop_::<Array<bool>>(r, callback, callback_1, int63!(0), Array::<bool>::make(n, false));
  let callback_2: Rc<dyn Fn(Int63, Int63) -> bool> = Rc::new(move |_v58: Int63, _v59: Int63| -> bool {
    true
  });
  let callback_3: Rc<dyn Fn(Int63, Int63) -> Int63> = Rc::new({
    let __anf_capture_71 = n;
    move |c: Int63, f: Int63| -> Int63 {
      let n = &__anf_capture_71;
      let isp = &isp;
      let tmp_1 = f == Clone::clone(n);
      let tmp_2 = negb(isp.get_cloned(c));
      if andb(tmp_1, tmp_2) {
        c
      } else {
        f
      }
    }
  });
  loop_::<Int63>(n, callback_2, callback_3, int63!(0), n)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.echelon_solve
// Variant: uncurried
pub fn echelon_solve(M: Array<f64>, pc: Array<Int63>, n: Int63, w: Int63, r: Int63, homog: bool, x: Array<f64>) -> Array<f64> {
  let callback: Rc<dyn Fn(Int63, Array<f64>) -> bool> = Rc::new(move |_v9: Int63, v10: Array<f64>| -> bool {
    std::mem::drop(v10);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<f64>) -> Array<f64>> = Rc::new({
    let __anf_capture_30 = r;
    move |s: Int63, x: Array<f64>| -> Array<f64> {
      let r = &__anf_capture_30;
      let pc = &pc;
      let homog = &homog;
      let n = &n;
      let w = &w;
      let M = &M;
      let tmp = int63!(1);
      let t = Clone::clone(r) - tmp - s;
      let c = pc.get_cloned(t);
      let s0 = if *homog {
        __rocq_global_371
      } else {
        M.get_cloned(t * Clone::clone(w) + Clone::clone(n))
      };
      let callback_2: Rc<dyn Fn(Int63, f64) -> bool> = Rc::new(move |_v85: Int63, _v86: f64| -> bool {
        true
      });
      let w_clone = Clone::clone(w);
      let M_clone = Clone::clone(M);
      let x_clone = Clone::clone(&x);
      let callback_3: Rc<dyn Fn(Int63, f64) -> f64> = Rc::new({
        let __anf_capture_103 = t;
        move |j: Int63, acc: f64| -> f64 {
          let t = &__anf_capture_103;
          let w = &w_clone;
          let M = &M_clone;
          let x = &x_clone;
          let tmp_1 = M.get_cloned(Clone::clone(t) * Clone::clone(w) + j);
          let tmp_2 = x.get_cloned(j);
          rocq_float64::sub(acc, rocq_float64::mul(tmp_1, tmp_2))
        }
      });
      let tmp_3 = c + int63!(1);
      let acc = loop_::<f64>(Clone::clone(n), callback_2, callback_3, tmp_3, s0);
      let tmp_4 = M.get_cloned(t * Clone::clone(w) + c);
      x.set(c, rocq_float64::div(acc, tmp_4))
    }
  });
  loop_::<Array<f64>>(r, callback, callback_1, int63!(0), x)
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.chk_mult
// Variant: uncurried
pub fn chk_mult(xa: Array<Array<f64>>, xb: Array<f64>, n: Int63, p: Array<Rc<BigInt>>, q: Rc<BigInt>, v: Array<Rc<BigInt>>) -> bool {
  let tmp = b::zero();
  let q_clone = Rc::clone(&q);
  let tmp_1 = negb(b::equal(q_clone, tmp));
  let v_clone = Clone::clone(&v);
  let callback: Rc<dyn Fn(Int63) -> bool> = Rc::new({
    move |j: Int63| -> bool {
      let tmp_2 = v_clone.get_cloned(j);
      let tmp_3 = b::zero();
      b::equal(tmp_2, tmp_3)
    }
  });
  let tmp_4 = andb(tmp_1, negb(allf(n, callback)));
  let callback_1: Rc<dyn Fn(Int63) -> bool> = Rc::new({
    let __anf_capture_74 = q;
    let __anf_capture_78 = v;
    let __anf_capture_80 = n;
    move |i: Int63| -> bool {
      let xa = &xa;
      let p = &p;
      let q = &__anf_capture_74;
      let xb = &xb;
      let v = &__anf_capture_78;
      let n = &__anf_capture_80;
      let xa_clone = Clone::clone(xa);
      let tmp_5 = &xa_clone;
      let row = tmp_5.get_cloned(i);
      std::mem::drop(xa_clone);
      let row_clone = Clone::clone(&row);
      let tmp_6 = dzero(dsub(zdot_owned(row_clone, int63!(0), Clone::clone(p), Clone::clone(n)), dmul(dint(q), dec(xb.get_cloned(i)))));
      let v_clone_1 = Clone::clone(v);
      let n_clone = Clone::clone(n);
      andb(tmp_6, dzero(zdot_owned(row, int63!(0), v_clone_1, n_clone)))
    }
  });
  andb(tmp_4, allf(n, callback_1))
}

// Rocq: EquationsolverExact.equationsolver_exact_implem.solve
// Variant: uncurried
pub fn solve(n: Int63, xa: Array<Array<f64>>, xb: Array<f64>) -> Rc<outcome<Array<f64>>> {
  let w = n + int63!(1);
  let xa_clone = Clone::clone(&xa);
  let tmp = col_thr(xa_clone, n);
  let xa_clone_1 = Clone::clone(&xa);
  let xb_clone = Clone::clone(&xb);
  let tmp_1 = init_M(xa_clone_1, xb_clone, n, w);
  let tmp_2 = init_Q(n);
  let st = forward(n, w, tmp, tmp_1, tmp_2);
  let xa_clone_2 = Clone::clone(&xa);
  let AT = transpose(xa_clone_2, n);
  let st_clone = Rc::clone(&st);
  let tmp_3 = fs_r_owned(st_clone);
  if tmp_3 == n {
    let st_clone_1 = Rc::clone(&st);
    let tmp_4 = backsub(n, w, fs_M_owned(st_clone_1), fs_Q(st));
    match tmp_4 {
      (v85, v87) => {
        let xt = get_col(v85, n, w, n);
        let xa_clone_3 = Clone::clone(&xa);
        let xb_clone_1 = Clone::clone(&xb);
        let xt_clone = Clone::clone(&xt);
        if certify(n, xa_clone_3, xb_clone_1, AT, v87, xt_clone) {
          std::mem::drop(xb);
          std::mem::drop(xa);
          Rc::new(outcome::<Array<f64>>::Unique(xt))
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
    let k = if r < n {
      n - r
    } else {
      int63!(0)
    };
    let st_clone_4 = Rc::clone(&st);
    let fc = free_cols(fs_pc(st_clone_4), n, r);
    let st_clone_5 = Rc::clone(&st);
    let mD = mark_D(fs_perm(st_clone_5), n, r, k);
    let mD_clone = Clone::clone(&mD);
    let Df = fst::<Array<bool>, Array<Int63>>(mD_clone);
    let tix = snd::<Array<bool>, Array<Int63>>(mD);
    let fc_clone = Clone::clone(&fc);
    let Cf = mark_C(fc_clone, n, k);
    let st_clone_6 = Rc::clone(&st);
    let tmp_5 = fs_Q(st_clone_6);
    let st_clone_7 = Rc::clone(&st);
    let tmp_6 = fs_perm(st_clone_7);
    let xb_clone_2 = Clone::clone(&xb);
    let fc_clone_1 = Clone::clone(&fc);
    let Df_clone = Clone::clone(&Df);
    let sc = scan_null(AT, xb_clone_2, tmp_5, tmp_6, fc_clone_1, Df_clone, n, r, k);
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
      Rc::new(outcome::<Array<f64>>::Inconsistent)
    } else {
      let tmp_7 = if snd::<bool, bool>(sc) {
        let xa_clone_4 = Clone::clone(&xa);
        padded_ok(xa_clone_4, n, Df, tix, fc, Cf)
      } else {
        std::mem::drop(Cf);
        std::mem::drop(fc);
        std::mem::drop(tix);
        std::mem::drop(Df);
        false
      };
      if tmp_7 {
        std::mem::drop(M);
        std::mem::drop(xa);
        std::mem::drop(xb);
        std::mem::drop(st);
        Rc::new(outcome::<Array<f64>>::Multiple)
      } else {
        let st_clone_8 = Rc::clone(&st);
        let f = free_col(fs_pc(st_clone_8), n, r);
        let st_clone_9 = Rc::clone(&st);
        let tmp_8 = fs_pc(st_clone_9);
        let tmp_9 = Array::<f64>::make(n, __rocq_global_371);
        let M_clone = Clone::clone(&M);
        let x0 = echelon_solve(M_clone, tmp_8, n, w, r, false, tmp_9);
        let tmp_10 = fs_pc(st);
        let tmp_11 = Array::<f64>::make(n, __rocq_global_371);
        let v = echelon_solve(M, tmp_10, n, w, r, true, tmp_11.set(f, __rocq_global_820));
        let tmp_12 = ratvec(x0, n);
        match tmp_12 {
          (v380, v382) => {
            let tmp_13 = fst::<Array<Rc<BigInt>>, Rc<BigInt>>(ratvec(v, n));
            let xa_clone_5 = Clone::clone(&xa);
            let xb_clone_3 = Clone::clone(&xb);
            if chk_mult(xa_clone_5, xb_clone_3, n, v380, v382, tmp_13) {
              std::mem::drop(xa);
              std::mem::drop(xb);
              Rc::new(outcome::<Array<f64>>::Multiple)
            } else {
              solve_exact(n, xa, xb)
            }
          },
        }
      }
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