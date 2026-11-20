#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};
#[allow(unused_imports)] use rocq_bigint::{self as b, BigInt};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::PositiveTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::NaturalTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::IntegerTag>; };

pub type uint = Int63;

pub type sint = Int63;

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.loop
// Variant: uncurried
pub fn loop__1<S: Clone + 'static>(f: Rc<dyn Fn(Int63, S) -> S>, hi: Int63, i: Int63, s: S) -> S {
  loop_::<S>((), f, hi, i, s, ())
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.loop (local: loop)
// Variant: uncurried, lifted
pub fn loop_<S: Clone + 'static>(_S_1: (), f: Rc<dyn Fn(Int63, S) -> S>, hi: Int63, i: Int63, s: S, _H: ()) -> S {
  let tmp = i < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let f_ref: &Rc<dyn Fn(Int63, S) -> S> = &f;
      let tmp_2 = f_ref(i, s);
      loop_::<S>((), f, hi, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      std::mem::drop(f);
      s
    },
  }
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.for_
// Variant: uncurried
pub fn for_<S: Clone + 'static>(lo: Int63, hi: Int63, s: S, f: Rc<dyn Fn(Int63, S) -> S>) -> S {
  loop__1::<S>(f, hi, lo, s)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.uconv
pub fn uconv_1(x: Int63) -> Rc<BigInt> {
  uconv(x, ())
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.uconv (local: uconv)
// Variant: uncurried, lifted
pub fn uconv(x: Int63, _H: ()) -> Rc<BigInt> {
  let tmp = x == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      b::zero()
    },
    sumbool::right => {
      let tmp_1 = b::one();
      let tmp_2 = b::twice(tmp_1);
      let tmp_3 = b::identity(tmp_2);
      let tmp_4 = uconv(x / int63!(2), ());
      let tmp_5 = b::mul(tmp_3, tmp_4);
      let tmp_6 = x % int63!(2);
      let tmp_7 = int63!(0);
      let tmp_8 = if tmp_6 == tmp_7 {
        b::zero()
      } else {
        let tmp_9 = b::one();
        b::identity(tmp_9)
      };
      b::add(tmp_5, tmp_8)
    },
  }
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.sconv
pub fn sconv(x: Int63) -> Rc<BigInt> {
  if x < int63!(4611686018427387904) {
    uconv_1(x)
  } else {
    let tmp = uconv_1(int63!(0) - x);
    b::neg(tmp)
  }
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.ztab
// Variant: uncurried
pub fn ztab(n: Int63, m: Int63, xe: Array<Array<Int63>>) -> Array<Rc<BigInt>> {
  let tmp = int63!(0);
  let tmp_1 = n * m;
  let tmp_2 = b::zero();
  let tmp_3 = Array::<Rc<BigInt>>::make(tmp_1, tmp_2);
  let callback: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = Rc::new({
    let __anf_capture_25 = m;
    move |i: Int63, T: Array<Rc<BigInt>>| -> Array<Rc<BigInt>> {
      let xe = &xe;
      let m = &__anf_capture_25;
      let xe_clone = Clone::clone(xe);
      let tmp_4 = &xe_clone;
      let row = tmp_4.get_cloned(i);
      std::mem::drop(xe_clone);
      let tmp_5 = int63!(0);
      let m_clone = Clone::clone(m);
      let callback_1: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = Rc::new({
        let __anf_capture_45 = i;
        move |j: Int63, T: Array<Rc<BigInt>>| -> Array<Rc<BigInt>> {
          let i = &__anf_capture_45;
          let m = &m_clone;
          let row = &row;
          let tmp_6 = Clone::clone(i) * Clone::clone(m) + j;
          let tmp_7 = row.get_cloned(j);
          let tmp_8 = sconv(tmp_7);
          T.set(tmp_6, tmp_8)
        }
      });
      let m_clone_1 = Clone::clone(m);
      for_::<Array<Rc<BigInt>>>(tmp_5, m_clone_1, T, callback_1)
    }
  });
  for_::<Array<Rc<BigInt>>>(tmp, n, tmp_3, callback)
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

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.find_piv
// Variant: uncurried
pub fn find_piv(n: Int63, m: Int63, c: Int63, T: Array<Rc<BigInt>>, U: Array<bool>) -> Int63 {
  let tmp = int63!(0);
  let callback: Rc<dyn Fn(Int63, Int63) -> Int63> = Rc::new({
    let __anf_capture_19 = n;
    move |i: Int63, r: Int63| -> Int63 {
      let n = &__anf_capture_19;
      let U = &U;
      let m = &m;
      let c = &c;
      let T = &T;
      let n_clone = Clone::clone(n);
      if r == n_clone {
        if U.get_cloned(i) {
          r
        } else {
          let tmp_1 = T.get_cloned(i * Clone::clone(m) + Clone::clone(c));
          let tmp_2 = b::zero();
          if b::equal(tmp_1, tmp_2) {
            r
          } else {
            i
          }
        }
      } else {
        r
      }
    }
  });
  for_::<Int63>(tmp, n, n, callback)
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

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.row_gcd
// Variant: uncurried
pub fn row_gcd(m: Int63, i: Int63, T: Array<Rc<BigInt>>) -> Rc<BigInt> {
  let tmp = int63!(0);
  let tmp_1 = b::zero();
  let callback: Rc<dyn Fn(Int63, Rc<BigInt>) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_16 = m;
    move |j: Int63, g: Rc<BigInt>| -> Rc<BigInt> {
      let i = &i;
      let m = &__anf_capture_16;
      let tmp_2 = T.get_cloned(Clone::clone(i) * Clone::clone(m) + j);
      zgcd(g, tmp_2)
    }
  });
  for_::<Rc<BigInt>>(tmp, m, tmp_1, callback)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.div_row
// Variant: uncurried
pub fn div_row(m: Int63, i: Int63, g: Rc<BigInt>, T: Array<Rc<BigInt>>) -> Array<Rc<BigInt>> {
  let tmp = int63!(0);
  let callback: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = Rc::new({
    let __anf_capture_16 = m;
    move |j: Int63, T: Array<Rc<BigInt>>| -> Array<Rc<BigInt>> {
      let i = &i;
      let m = &__anf_capture_16;
      let g = &g;
      let tmp_1 = Clone::clone(i) * Clone::clone(m) + j;
      let tmp_2 = T.get_cloned(Clone::clone(i) * Clone::clone(m) + j);
      let g_clone = Rc::clone(g);
      let tmp_3 = b::div(tmp_2, g_clone);
      T.set(tmp_1, tmp_3)
    }
  });
  for_::<Array<Rc<BigInt>>>(tmp, m, T, callback)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.norm_row
// Variant: uncurried
pub fn norm_row(m: Int63, i: Int63, T: Array<Rc<BigInt>>) -> Array<Rc<BigInt>> {
  let T_clone = Clone::clone(&T);
  let g = row_gcd(m, i, T_clone);
  let tmp = b::one();
  let tmp_1 = b::identity(tmp);
  let g_clone = Rc::clone(&g);
  if b::lt(tmp_1, g_clone) {
    div_row(m, i, g, T)
  } else {
    std::mem::drop(g);
    T
  }
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.upd_row
// Variant: uncurried
pub fn upd_row(m: Int63, i: Int63, s: Int63, p: Rc<BigInt>, f: Rc<BigInt>, T: Array<Rc<BigInt>>) -> Array<Rc<BigInt>> {
  let tmp = int63!(0);
  let callback: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = Rc::new({
    let __anf_capture_26 = m;
    move |j: Int63, T: Array<Rc<BigInt>>| -> Array<Rc<BigInt>> {
      let i = &i;
      let p = &p;
      let s = &s;
      let m = &__anf_capture_26;
      let f = &f;
      let tmp_1 = Clone::clone(i) * Clone::clone(m) + j;
      let tmp_2 = T.get_cloned(Clone::clone(i) * Clone::clone(m) + j);
      let p_clone = Rc::clone(p);
      let tmp_3 = b::mul(p_clone, tmp_2);
      let tmp_4 = T.get_cloned(Clone::clone(s) * Clone::clone(m) + j);
      let f_clone = Rc::clone(f);
      let tmp_5 = b::mul(f_clone, tmp_4);
      let tmp_6 = b::sub(tmp_3, tmp_5);
      T.set(tmp_1, tmp_6)
    }
  });
  for_::<Array<Rc<BigInt>>>(tmp, m, T, callback)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.elim_rows
// Variant: uncurried
pub fn elim_rows(n: Int63, m: Int63, s: Int63, c: Int63, T: Array<Rc<BigInt>>) -> Array<Rc<BigInt>> {
  let p = T.get_cloned(s * m + c);
  let tmp = int63!(0);
  let callback: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = Rc::new({
    let __anf_capture_33 = c;
    let __anf_capture_35 = s;
    let __anf_capture_39 = m;
    move |i: Int63, T: Array<Rc<BigInt>>| -> Array<Rc<BigInt>> {
      let c = &__anf_capture_33;
      let s = &__anf_capture_35;
      let p = &p;
      let m = &__anf_capture_39;
      let s_clone = Clone::clone(s);
      if i == s_clone {
        T
      } else {
        let f = T.get_cloned(i * Clone::clone(m) + Clone::clone(c));
        let tmp_1 = b::zero();
        let f_clone = Rc::clone(&f);
        if b::equal(f_clone, tmp_1) {
          std::mem::drop(f);
          T
        } else {
          let m_clone = Clone::clone(m);
          let s_clone_1 = Clone::clone(s);
          let p_clone = Rc::clone(p);
          let tmp_2 = upd_row(m_clone, i, s_clone_1, p_clone, f, T);
          let m_clone_1 = Clone::clone(m);
          norm_row(m_clone_1, i, tmp_2)
        }
      }
    }
  });
  for_::<Array<Rc<BigInt>>>(tmp, n, T, callback)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.col_step
// Variant: uncurried
pub fn col_step(n: Int63, m: Int63, c: Int63, st: (Array<Rc<BigInt>>, Array<bool>)) -> (Array<Rc<BigInt>>, Array<bool>) {
  let st_clone = Clone::clone(&st);
  let T = fst::<Array<Rc<BigInt>>, Array<bool>>(st_clone);
  let st_clone_1 = Clone::clone(&st);
  let U = snd::<Array<Rc<BigInt>>, Array<bool>>(st_clone_1);
  let T_clone = Clone::clone(&T);
  let U_clone = Clone::clone(&U);
  let s = find_piv(n, m, c, T_clone, U_clone);
  if s == n {
    std::mem::drop(U);
    std::mem::drop(T);
    st
  } else {
    std::mem::drop(st);
    (elim_rows(n, m, s, c, T), U.set(s, true))
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

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.count_nz
// Variant: borrowed, uncurried
pub fn count_nz(m: Int63, i: Int63, T: &Array<Rc<BigInt>>) -> Int63 {
  let tmp = int63!(0);
  let tmp_1 = int63!(0);
  let T_clone = Clone::clone(T);
  let callback: Rc<dyn Fn(Int63, Int63) -> Int63> = Rc::new({
    let __anf_capture_20 = m;
    move |j: Int63, k: Int63| -> Int63 {
      let i = &i;
      let m = &__anf_capture_20;
      let T = &T_clone;
      let tmp_2 = T.get_cloned(Clone::clone(i) * Clone::clone(m) + j);
      let tmp_3 = b::zero();
      if b::equal(tmp_2, tmp_3) {
        k
      } else {
        k + int63!(1)
      }
    }
  });
  for_::<Int63>(tmp, m, tmp_1, callback)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.valid_impl
// Variant: uncurried
pub fn valid_impl(xm: Int63, xe: Array<Array<Int63>>) -> bool {
  let n = xe.length();
  let tmp = int63!(0);
  let tmp_1 = (ztab(n, xm, xe), Array::<bool>::make(n, false));
  let callback: Rc<dyn Fn(Int63, (Array<Rc<BigInt>>, Array<bool>)) -> (Array<Rc<BigInt>>, Array<bool>)> = Rc::new({
    let __anf_capture_33 = n;
    let __anf_capture_35 = xm;
    move |v37: Int63, v38: (Array<Rc<BigInt>>, Array<bool>)| -> (Array<Rc<BigInt>>, Array<bool>) {
      let tmp_2 = Clone::clone(&__anf_capture_33);
      let tmp_3 = Clone::clone(&__anf_capture_35);
      col_step(tmp_2, tmp_3, v37, v38)
    }
  });
  let st = for_::<(Array<Rc<BigInt>>, Array<bool>)>(tmp, xm, tmp_1, callback);
  let T = fst::<Array<Rc<BigInt>>, Array<bool>>(st);
  let tmp_4 = int63!(0);
  let tmp_5 = true;
  let callback_1: Rc<dyn Fn(Int63, bool) -> bool> = Rc::new({
    let __anf_capture_76 = xm;
    move |i: Int63, b_1: bool| -> bool {
      let xm = &__anf_capture_76;
      let T = &T;
      if b_1 {
        let tmp_6 = count_nz(Clone::clone(xm), i, T);
        negb(tmp_6 == int63!(1))
      } else {
        false
      }
    }
  });
  for_::<bool>(tmp_4, n, tmp_5, callback_1)
}
