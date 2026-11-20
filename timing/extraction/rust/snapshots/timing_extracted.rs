#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};
#[allow(unused_imports)] use rocq_bigint::{self as b, BigInt};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

pub enum option<A: 'static> {
  Some(A),
  None,
}

impl<A: Clone + 'static> Clone for option<A> {
  fn clone(&self) -> Self {
    match self {
      option::Some(__field0) => option::Some(Clone::clone(__field0)),
      option::None => option::None,
    }
  }
}

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

// Rocq: Timing.timing_implem.f_K1
pub fn f_K1() -> f64 {
  f64::from_bits(4607182418804211712u64)
}

// Rocq: Timing.timing_implem.f_u
pub fn f_u() -> f64 {
  f64::from_bits(4372995238176751616u64)
}

// Rocq: Timing.timing_implem.f_s30
pub fn f_s30() -> f64 {
  f64::from_bits(4472074429978902528u64)
}

// Rocq: Timing.timing_implem.cut
pub fn cut() -> Int63 {
  int63!(16)
}

// Rocq: Timing.timing_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Timing.timing_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: Int63, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop::<St>(hi, f, i, s, ())
}

// Rocq: Timing.timing_implem.wloop (local: wloop)
// Variant: uncurried, lifted
pub fn wloop<St: Clone + 'static>(hi: Int63, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St, _H: ()) -> St {
  let tmp = i < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let f_ref: &Rc<dyn Fn(Int63, St) -> St> = &f;
      let tmp_2 = f_ref(i, s);
      wloop::<St>(hi, f, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      std::mem::drop(f);
      s
    },
  }
}

// Rocq: Timing.timing_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: Int63, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop_1::<St>(hi, f, i, s)
}

// Rocq: Timing.timing_implem.cnt_step
// Variant: uncurried
pub fn cnt_step(xs: Array<Int63>, xd: Array<Int63>, j: Int63, c: Array<Int63>) -> Array<Int63> {
  let s = xs.get_cloned(j);
  let d = xd.get_cloned(j);
  if s == d {
    std::mem::drop(xs);
    std::mem::drop(xd);
    c
  } else {
    std::mem::drop(xs);
    std::mem::drop(xd);
    let tmp = c.get_cloned(s);
    let c1 = c.set(s, tmp + int63!(1));
    let tmp_1 = c1.get_cloned(d);
    c1.set(d, tmp_1 + int63!(1))
  }
}

// Rocq: Timing.timing_implem.out_step
// Variant: uncurried
pub fn out_step(xs: Array<Int63>, xd: Array<Int63>, xf: Array<f64>, j: Int63, o: Array<f64>) -> Array<f64> {
  let s = xs.get_cloned(j);
  let d = xd.get_cloned(j);
  if s == d {
    std::mem::drop(xs);
    std::mem::drop(xf);
    std::mem::drop(xd);
    o
  } else {
    std::mem::drop(xs);
    std::mem::drop(xd);
    let tmp = o.get_cloned(s);
    let tmp_1 = xf.get_cloned(j);
    std::mem::drop(xf);
    o.set(s, rocq_float64::add(tmp, tmp_1))
  }
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

// Rocq: Timing.timing_implem.elink
// Variant: borrowed, uncurried
pub fn elink(xs: &Array<Int63>, xd: &Array<Int63>, xf: &Array<f64>, v: &Array<f64>, e: &Array<f64>, j: Int63, st: (Array<f64>, Array<f64>)) -> (Array<f64>, Array<f64>) {
  let j_1 = j;
  let st_1 = st;
  let s = xs.get_cloned(j_1);
  let d = xd.get_cloned(j_1);
  if s == d {
    st_1
  } else {
    let a_1 = rocq_float64::abs(rocq_float64::mul(xf.get_cloned(j_1), v.get_cloned(s)));
    let st_clone = Clone::clone(&st_1);
    let ein = fst::<Array<f64>, Array<f64>>(st_clone);
    let mac = snd::<Array<f64>, Array<f64>>(st_1);
    let tmp = mac.get_cloned(d);
    let mac1 = mac.set(d, rocq_float64::add(tmp, a_1));
    let tmp_1 = ein.get_cloned(d);
    let tmp_2 = ein.set(d, rocq_float64::add(tmp_1, rocq_float64::mul(xf.get_cloned(j_1), e.get_cloned(s))));
    let tmp_3 = mac1.get_cloned(s);
    (tmp_2, mac1.set(s, rocq_float64::add(tmp_3, a_1)))
  }
}

// Rocq: Timing.timing_implem.up
pub fn up(y: f64) -> f64 {
  rocq_float64::add(rocq_float64::mul(y, __rocq_global_416), __rocq_global_419)
}

// Rocq: Timing.timing_implem.coef
// Variant: borrowed, uncurried
pub fn coef(ou: &Array<f64>, x: Int63) -> f64 {
  let x_1 = x;
  rocq_float64::add(rocq_float64::abs(rocq_float64::sub(f64::from_bits(4607182418800017408u64), ou.get_cloned(x_1))), __rocq_global_444)
}

// Rocq: Timing.timing_implem.kx
// Variant: borrowed, uncurried
pub fn kx(c: &Array<Int63>, x: Int63) -> f64 {
  let x_1 = x;
  rocq_float64::mul(rocq_float64::of_uint63(c.get_cloned(x_1) + c.get_cloned(x_1) + int63!(3)), __rocq_global_419)
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

// Rocq: Timing.timing_implem.efort
// Variant: borrowed, uncurried
pub fn efort(ou: &Array<f64>, c: &Array<Int63>, v: &Array<f64>, e: &Array<f64>, ein: &Array<f64>, mac: &Array<f64>, x: Int63, st: (Array<f64>, bool)) -> (Array<f64>, bool) {
  let x_1 = x;
  let st_1 = st;
  let tmp = rocq_float64::add(rocq_float64::mul(coef(ou, x_1), e.get_cloned(x_1)), ein.get_cloned(x_1));
  let tmp_1 = kx(c, x_1);
  let tmp_2 = rocq_float64::add(rocq_float64::abs(v.get_cloned(x_1)), mac.get_cloned(x_1));
  let tmp_3 = rocq_float64::add(tmp_2, f64::from_bits(4607182418800017408u64));
  let y = up(rocq_float64::add(tmp, rocq_float64::mul(tmp_1, tmp_3)));
  let st_clone = Clone::clone(&st_1);
  (fst::<Array<f64>, bool>(st_clone).set(x_1, y), andb(snd::<Array<f64>, bool>(st_1), rocq_float64::leb(y, f64::from_bits(4607182418800017408u64))))
}

// Rocq: Timing.timing_implem.ebound
// Variant: uncurried
pub fn ebound(n: Int63, L: Int63, xs: Array<Int63>, xd: Array<Int63>, xf: Array<f64>, ou: Array<f64>, c: Array<Int63>, v: Array<f64>, e: Array<f64>) -> (Array<f64>, bool) {
  let v_clone = Clone::clone(&v);
  let e_clone = Clone::clone(&e);
  let callback: Rc<dyn Fn(Int63, (Array<f64>, Array<f64>)) -> (Array<f64>, Array<f64>)> = Rc::new({
    move |v33: Int63, v34: (Array<f64>, Array<f64>)| -> (Array<f64>, Array<f64>) {
      let xs = &xs;
      let xd = &xd;
      let xf = &xf;
      let v = &v_clone;
      let e = &e_clone;
      let tmp = elink(xs, xd, xf, v, e, v33, v34);
      tmp
    }
  });
  let st = loop_::<(Array<f64>, Array<f64>)>(L, callback, int63!(0), (Array::<f64>::make(n, f64::from_bits(0u64)), Array::<f64>::make(n, f64::from_bits(0u64))));
  let st_clone = Clone::clone(&st);
  let tmp_1 = fst::<Array<f64>, Array<f64>>(st_clone);
  let tmp_2 = snd::<Array<f64>, Array<f64>>(st);
  let callback_1: Rc<dyn Fn(Int63, (Array<f64>, bool)) -> (Array<f64>, bool)> = Rc::new({
    let __anf_capture_108 = v;
    let __anf_capture_110 = e;
    move |v116: Int63, v117: (Array<f64>, bool)| -> (Array<f64>, bool) {
      let ou = &ou;
      let c = &c;
      let v = &__anf_capture_108;
      let e = &__anf_capture_110;
      let v112 = &tmp_1;
      let v114 = &tmp_2;
      let tmp_3 = efort(ou, c, v, e, v112, v114, v116, v117);
      tmp_3
    }
  });
  let tmp_4 = Array::<f64>::make(n, f64::from_bits(0u64));
  loop_::<(Array<f64>, bool)>(n, callback_1, int63!(0), (tmp_4, true))
}

// Rocq: Timing.timing_implem.link_f
// Variant: uncurried
pub fn link_f(xs: Array<Int63>, xd: Array<Int63>, xf: Array<f64>, v: Array<f64>, j: Int63, w: Array<f64>) -> Array<f64> {
  let s = xs.get_cloned(j);
  let d = xd.get_cloned(j);
  if s == d {
    std::mem::drop(xs);
    std::mem::drop(xf);
    std::mem::drop(v);
    std::mem::drop(xd);
    w
  } else {
    std::mem::drop(xs);
    std::mem::drop(xd);
    let tmp = xf.get_cloned(j);
    std::mem::drop(xf);
    let tmp_1 = v.get_cloned(s);
    std::mem::drop(v);
    let a_1 = rocq_float64::mul(tmp, tmp_1);
    let tmp_2 = w.get_cloned(d);
    let w1 = w.set(d, rocq_float64::add(tmp_2, a_1));
    let tmp_3 = w1.get_cloned(s);
    w1.set(s, rocq_float64::sub(tmp_3, a_1))
  }
}

// Rocq: Timing.timing_implem.unit_f
// Variant: uncurried
pub fn unit_f(L: Int63, xs: Array<Int63>, xd: Array<Int63>, xf: Array<f64>, v: Array<f64>) -> Array<f64> {
  let v_clone = Clone::clone(&v);
  let callback: Rc<dyn Fn(Int63, Array<f64>) -> Array<f64>> = Rc::new({
    move |v24: Int63, v25: Array<f64>| -> Array<f64> {
      let xs_clone = Clone::clone(&xs);
      let xd_clone = Clone::clone(&xd);
      let xf_clone = Clone::clone(&xf);
      let tmp = Clone::clone(&v_clone);
      link_f(xs_clone, xd_clone, xf_clone, tmp, v24, v25)
    }
  });
  let tmp_1 = int63!(0);
  let v_ref = &v;
  let tmp_2 = v_ref.copy();
  std::mem::drop(v);
  loop_::<Array<f64>>(L, callback, tmp_1, tmp_2)
}

// Rocq: Timing.timing_implem.tstep
// Variant: borrowed, uncurried
pub fn tstep(n: Int63, L: Int63, xs: &Array<Int63>, xd: &Array<Int63>, xf: &Array<f64>, ou: &Array<f64>, c: &Array<Int63>, _j: Int63, st: ((Array<f64>, Array<f64>), bool)) -> ((Array<f64>, Array<f64>), bool) {
  let n_1 = n;
  let L_1 = L;
  let st_1 = st;
  match &st_1 {
    (ok, p) => {
      match ok {
        (e, v) => {
          if *p {
            let r = ebound(n_1, L_1, Clone::clone(xs), Clone::clone(xd), Clone::clone(xf), Clone::clone(ou), Clone::clone(c), Clone::clone(e), Clone::clone(v));
            let xs_clone = Clone::clone(xs);
            let xd_clone = Clone::clone(xd);
            let xf_clone = Clone::clone(xf);
            let e_clone = Clone::clone(e);
            std::mem::drop(st_1);
            let tmp = unit_f(L_1, xs_clone, xd_clone, xf_clone, e_clone);
            let r_clone = Clone::clone(&r);
            ((tmp, fst::<Array<f64>, bool>(r_clone)), snd::<Array<f64>, bool>(r))
          } else {
            st_1
          }
        },
      }
    },
  }
}

// Rocq: Timing.timing_implem.adj_step
// Variant: uncurried
pub fn adj_step(n: Int63, xs: Array<Int63>, xd: Array<Int63>, l: Int63, a_1: Array<bool>) -> Array<bool> {
  let s = xs.get_cloned(l);
  let d = xd.get_cloned(l);
  if s == d {
    std::mem::drop(xs);
    std::mem::drop(xd);
    a_1
  } else {
    std::mem::drop(xs);
    std::mem::drop(xd);
    a_1.set(s * n + d, true).set(d * n + s, true)
  }
}

// Rocq: Timing.timing_implem.fmin
// Variant: uncurried
pub fn fmin(b_1: f64, x: f64) -> f64 {
  if rocq_float64::ltb(x, b_1) {
    x
  } else {
    b_1
  }
}

// Rocq: Timing.timing_implem.faced_f
// Variant: uncurried
pub fn faced_f_owned(n: Int63, adj: Array<bool>, v: Array<f64>, i: Int63) -> f64 {
  let v_clone = Clone::clone(&v);
  let callback: Rc<dyn Fn(Int63, f64) -> f64> = Rc::new({
    let __anf_capture_15 = i;
    let __anf_capture_17 = n;
    move |k: Int63, acc: f64| -> f64 {
      let i = &__anf_capture_15;
      let n = &__anf_capture_17;
      let adj = &adj;
      let v = &v_clone;
      let tmp = Clone::clone(i) * Clone::clone(n) + k;
      if adj.get_cloned(tmp) {
        let tmp_1 = v.get_cloned(k);
        rocq_float64::add(acc, tmp_1)
      } else {
        acc
      }
    }
  });
  let tmp_2 = int63!(0);
  let tmp_3 = v.get_cloned(i);
  std::mem::drop(v);
  loop_::<f64>(n, callback, tmp_2, tmp_3)
}

// Rocq: Timing.timing_implem.faced_f
// Variant: borrowed, uncurried
pub fn faced_f(n: Int63, adj: &Array<bool>, v: &Array<f64>, i: Int63) -> f64 {
  let adj_clone = Clone::clone(adj);
  let v_clone = Clone::clone(v);
  let callback: Rc<dyn Fn(Int63, f64) -> f64> = Rc::new({
    let __anf_capture_18 = i;
    let __anf_capture_20 = n;
    move |k: Int63, acc: f64| -> f64 {
      let i = &__anf_capture_18;
      let n = &__anf_capture_20;
      let adj = &adj_clone;
      let v = &v_clone;
      let tmp = Clone::clone(i) * Clone::clone(n) + k;
      if adj.get_cloned(tmp) {
        let tmp_1 = v.get_cloned(k);
        rocq_float64::add(acc, tmp_1)
      } else {
        acc
      }
    }
  });
  loop_::<f64>(n, callback, int63!(0), v.get_cloned(i))
}

// Rocq: Timing.timing_implem.gmax
// Variant: uncurried
pub fn gmax(n: Int63, g: Rc<dyn Fn(Int63) -> f64>) -> f64 {
  let callback: Rc<dyn Fn(Int63, f64) -> f64> = Rc::new({
    move |i: Int63, m: f64| -> f64 {
      let g = &g;
      let tmp = g(i);
      if rocq_float64::ltb(m, tmp) {
        g(i)
      } else {
        m
      }
    }
  });
  loop_::<f64>(n, callback, int63!(0), f64::from_bits(0u64))
}

// Rocq: Timing.timing_implem.fpair
// Variant: borrowed, uncurried
pub fn fpair(n: Int63, adj: &Array<bool>, v: &Array<f64>, e: &Array<f64>, i: Int63) -> (f64, f64) {
  let adj_clone = Clone::clone(adj);
  let e_clone = Clone::clone(e);
  let v_clone = Clone::clone(v);
  let callback: Rc<dyn Fn(Int63, (f64, f64)) -> (f64, f64)> = Rc::new({
    let __anf_capture_22 = i;
    let __anf_capture_24 = n;
    move |k: Int63, st: (f64, f64)| -> (f64, f64) {
      let i = &__anf_capture_22;
      let n = &__anf_capture_24;
      let adj = &adj_clone;
      let e = &e_clone;
      let v = &v_clone;
      let tmp = Clone::clone(i) * Clone::clone(n) + k;
      if adj.get_cloned(tmp) {
        let st_clone = Clone::clone(&st);
        let tmp_1 = rocq_float64::add(fst::<f64, f64>(st_clone), e.get_cloned(k));
        let tmp_2 = snd::<f64, f64>(st);
        let tmp_3 = v.get_cloned(k);
        (tmp_1, rocq_float64::add(tmp_2, rocq_float64::abs(tmp_3)))
      } else {
        st
      }
    }
  });
  loop_::<(f64, f64)>(n, callback, int63!(0), (e.get_cloned(i), rocq_float64::abs(v.get_cloned(i))))
}

// Rocq: Timing.timing_implem.fbound
// Variant: borrowed, uncurried
pub fn fbound(n: Int63, adj: &Array<bool>, v: &Array<f64>, e: &Array<f64>, nu: f64, i: Int63) -> f64 {
  let n_1 = n;
  let nu_1 = nu;
  let i_1 = i;
  let p = fpair(n_1, adj, v, e, i_1);
  let p_clone = Clone::clone(&p);
  let tmp = fst::<f64, f64>(p_clone);
  let tmp_1 = rocq_float64::add(snd::<f64, f64>(p), f64::from_bits(4607182418800017408u64));
  up(rocq_float64::add(tmp, rocq_float64::mul(nu_1, tmp_1)))
}

// Rocq: Corelib.Floats.PrimFloat.frshiftexp
pub fn frshiftexp(x: f64) -> (f64, Int63) {
  (rocq_float64::frshiftexp_fraction(x), rocq_float64::frshiftexp_exponent(x))
}

// Rocq: Timing.timing_implem.zofi_rec
pub fn zofi_rec_1(i: Int63) -> Rc<BigInt> {
  zofi_rec(i, ())
}

// Rocq: Timing.timing_implem.zofi_rec (local: zofi_rec)
// Variant: uncurried, lifted
pub fn zofi_rec(i: Int63, _H: ()) -> Rc<BigInt> {
  let tmp = i == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      b::zero()
    },
    sumbool::right => {
      let r = zofi_rec(i / int63!(2), ());
      let tmp_1 = i % int63!(2);
      let tmp_2 = int63!(0);
      let bit = if tmp_1 == tmp_2 {
        b::zero()
      } else {
        let tmp_3 = b::one();
        b::identity(tmp_3)
      };
      let tmp_4 = b::one();
      let tmp_5 = b::twice(tmp_4);
      let tmp_6 = b::identity(tmp_5);
      let tmp_7 = b::mul(tmp_6, r);
      b::add(tmp_7, bit)
    },
  }
}

// Rocq: Timing.timing_implem.zofi
pub fn zofi(i: Int63) -> Rc<BigInt> {
  zofi_rec_1(i)
}

// Rocq: Timing.timing_implem.fex
pub fn fex(f: f64) -> (Rc<BigInt>, Rc<BigInt>) {
  let tmp = frshiftexp(f);
  match tmp {
    (v6, v8) => {
      let z = &v8;
      let m = zofi(rocq_float64::normfr_mantissa(v6));
      let tmp_1 = f64::from_bits(0u64);
      let tmp_2 = if rocq_float64::ltb(f, tmp_1) {
        b::neg(m)
      } else {
        m
      };
      let z_clone = Clone::clone(z);
      let tmp_3 = zofi(z_clone);
      let tmp_4 = b::one();
      let tmp_5 = b::twice(tmp_4);
      let tmp_6 = b::twice(tmp_5);
      let tmp_7 = b::twice(tmp_6);
      let tmp_8 = b::twice(tmp_7);
      let tmp_9 = b::twice_plus_one(tmp_8);
      let tmp_10 = b::twice_plus_one(tmp_9);
      let tmp_11 = b::twice(tmp_10);
      let tmp_12 = b::twice_plus_one(tmp_11);
      let tmp_13 = b::twice(tmp_12);
      let tmp_14 = b::twice_plus_one(tmp_13);
      let tmp_15 = b::twice(tmp_14);
      let tmp_16 = b::identity(tmp_15);
      let tmp_17 = b::sub(tmp_3, tmp_16);
      (tmp_2, tmp_17)
    },
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

// Rocq: Timing.timing_implem.dlt
// Variant: uncurried
pub fn dlt(x: Rc<BigInt>, a_1: Rc<BigInt>, y: Rc<BigInt>, b_1: Rc<BigInt>) -> bool {
  let a_clone = Rc::clone(&a_1);
  let b_clone = Rc::clone(&b_1);
  if b::le(a_clone, b_clone) {
    let tmp = b::sub(b_1, a_1);
    let tmp_1 = b::shiftl(y, tmp);
    b::lt(x, tmp_1)
  } else {
    let tmp_2 = b::sub(a_1, b_1);
    let tmp_3 = b::shiftl(x, tmp_2);
    b::lt(tmp_3, y)
  }
}

// Rocq: Timing.timing_implem.fcheck
// Variant: uncurried
pub fn fcheck(B: f64, o: f64) -> bool {
  let tmp = fex(B);
  match tmp {
    (v7, v9) => {
      let eb = &v7;
      let mb = &v9;
      let tmp_1 = fex(o);
      match tmp_1 {
        (v18, v20) => {
          let tmp_2 = b::one();
          let tmp_3 = b::identity(tmp_2);
          let tmp_4 = b::one();
          let tmp_5 = b::twice(tmp_4);
          let tmp_6 = b::twice_plus_one(tmp_5);
          let tmp_7 = b::twice(tmp_6);
          let tmp_8 = b::twice(tmp_7);
          let tmp_9 = b::neg(tmp_8);
          let eb_clone = Rc::clone(eb);
          let mb_clone = Rc::clone(mb);
          let tmp_10 = dlt(eb_clone, mb_clone, tmp_3, tmp_9);
          let tmp_11 = b::one();
          let tmp_12 = b::twice(tmp_11);
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
          let tmp_31 = b::twice_plus_one(tmp_30);
          let tmp_32 = b::identity(tmp_31);
          let tmp_33 = b::mul(v7, tmp_32);
          orb(tmp_10, dlt(tmp_33, v9, v18, v20))
        },
      }
    },
  }
}

// Rocq: Timing.timing_implem.PP
pub fn PP(_v0: ()) -> Rc<BigInt> {
  let tmp = b::one();
  let tmp_1 = b::twice_plus_one(tmp);
  let tmp_2 = b::twice(tmp_1);
  let tmp_3 = b::twice(tmp_2);
  let tmp_4 = b::twice(tmp_3);
  let tmp_5 = b::twice(tmp_4);
  let tmp_6 = b::twice(tmp_5);
  b::identity(tmp_6)
}

// Rocq: Timing.timing_implem.fixv
pub fn fixv(f: f64) -> Rc<BigInt> {
  let d = fex(f);
  let d_clone = Clone::clone(&d);
  let tmp = fst::<Rc<BigInt>, Rc<BigInt>>(d_clone);
  let tmp_1 = snd::<Rc<BigInt>, Rc<BigInt>>(d);
  let tmp_2 = PP(());
  let tmp_3 = b::add(tmp_1, tmp_2);
  b::shiftl(tmp, tmp_3)
}

// Rocq: Timing.timing_implem.link_step
// Variant: uncurried
pub fn link_step(m: Int63, xs: Array<Int63>, xd: Array<Int63>, xf: Array<f64>, l: Int63, A: Array<Rc<BigInt>>) -> Array<Rc<BigInt>> {
  let s = xs.get_cloned(l);
  std::mem::drop(xs);
  let d = xd.get_cloned(l);
  std::mem::drop(xd);
  let tmp = xf.get_cloned(l);
  std::mem::drop(xf);
  let F = fixv(tmp);
  let tmp_1 = d * m + s;
  let tmp_2 = A.get_cloned(d * m + s);
  let F_clone = Rc::clone(&F);
  let tmp_3 = b::add(tmp_2, F_clone);
  let A1 = A.set(tmp_1, tmp_3);
  let tmp_4 = s * m + s;
  let tmp_5 = A1.get_cloned(s * m + s);
  let tmp_6 = b::sub(tmp_5, F);
  A1.set(tmp_4, tmp_6)
}

// Rocq: Timing.timing_implem.build
// Variant: uncurried
pub fn build(len: Int63, f: Rc<dyn Fn(Int63) -> Rc<BigInt>>) -> Array<Rc<BigInt>> {
  let callback: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = Rc::new({
    move |k: Int63, a_1: Array<Rc<BigInt>>| -> Array<Rc<BigInt>> {
      let f = &f;
      let tmp = f(k);
      a_1.set(k, tmp)
    }
  });
  let tmp_1 = b::zero();
  let tmp_2 = Array::<Rc<BigInt>>::make(len, tmp_1);
  loop_::<Array<Rc<BigInt>>>(len, callback, int63!(0), tmp_2)
}

// Rocq: Timing.timing_implem.ONE
pub fn ONE(_v0: ()) -> Rc<BigInt> {
  let tmp = b::one();
  let tmp_1 = b::identity(tmp);
  let tmp_2 = PP(());
  b::shiftl(tmp_1, tmp_2)
}

// Rocq: Timing.timing_implem.ident
pub fn ident(m: Int63) -> Array<Rc<BigInt>> {
  let tmp = m * m;
  let callback: Rc<dyn Fn(Int63) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_11 = m;
    move |k: Int63| -> Rc<BigInt> {
      let m = &__anf_capture_11;
      let tmp_1 = k / Clone::clone(m);
      let tmp_2 = k % Clone::clone(m);
      if tmp_1 == tmp_2 {
        ONE(())
      } else {
        b::zero()
      }
    }
  });
  build(tmp, callback)
}

// Rocq: Timing.timing_implem.amat
// Variant: uncurried
pub fn amat(m: Int63, L: Int63, xs: Array<Int63>, xd: Array<Int63>, xf: Array<f64>) -> Array<Rc<BigInt>> {
  let callback: Rc<dyn Fn(Int63, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = Rc::new({
    let __anf_capture_15 = m;
    move |v23: Int63, v24: Array<Rc<BigInt>>| -> Array<Rc<BigInt>> {
      let tmp = Clone::clone(&__anf_capture_15);
      let xs_clone = Clone::clone(&xs);
      let xd_clone = Clone::clone(&xd);
      let xf_clone = Clone::clone(&xf);
      link_step(tmp, xs_clone, xd_clone, xf_clone, v23, v24)
    }
  });
  loop_::<Array<Rc<BigInt>>>(L, callback, int63!(0), ident(m))
}

// Rocq: Timing.timing_implem.splitb
pub fn splitb(s: Int63) -> bool {
  andb(__rocq_global_1401 < s, s % int63!(2) == int63!(0))
}

// Rocq: Timing.timing_implem.quad
// Variant: uncurried
pub fn quad(X: Array<Rc<BigInt>>, s: Int63, h: Int63, di: Int63, dj: Int63) -> Array<Rc<BigInt>> {
  let tmp = h * h;
  let callback: Rc<dyn Fn(Int63) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_27 = h;
    move |k: Int63| -> Rc<BigInt> {
      let di = &di;
      let s = &s;
      let h = &__anf_capture_27;
      let dj = &dj;
      let X = &X;
      let tmp_1 = k / Clone::clone(h);
      let tmp_2 = (Clone::clone(di) + tmp_1) * Clone::clone(s);
      let tmp_3 = k % Clone::clone(h);
      let tmp_4 = tmp_2 + (Clone::clone(dj) + tmp_3);
      X.get_cloned(tmp_4)
    }
  });
  build(tmp, callback)
}

// Rocq: Timing.timing_implem.madd
// Variant: uncurried
pub fn madd(h: Int63, A: Array<Rc<BigInt>>, B: Array<Rc<BigInt>>) -> Array<Rc<BigInt>> {
  let tmp = h * h;
  let callback: Rc<dyn Fn(Int63) -> Rc<BigInt>> = Rc::new({
    move |k: Int63| -> Rc<BigInt> {
      let A = &A;
      let B = &B;
      let tmp_1 = A.get_cloned(k);
      let tmp_2 = B.get_cloned(k);
      b::add(tmp_1, tmp_2)
    }
  });
  build(tmp, callback)
}

// Rocq: Timing.timing_implem.msub
// Variant: uncurried
pub fn msub(h: Int63, A: Array<Rc<BigInt>>, B: Array<Rc<BigInt>>) -> Array<Rc<BigInt>> {
  let tmp = h * h;
  let callback: Rc<dyn Fn(Int63) -> Rc<BigInt>> = Rc::new({
    move |k: Int63| -> Rc<BigInt> {
      let A = &A;
      let B = &B;
      let tmp_1 = A.get_cloned(k);
      let tmp_2 = B.get_cloned(k);
      b::sub(tmp_1, tmp_2)
    }
  });
  build(tmp, callback)
}

// Rocq: Timing.timing_implem.comb
// Variant: uncurried
pub fn comb(s: Int63, h: Int63, C11: Array<Rc<BigInt>>, C12: Array<Rc<BigInt>>, C21: Array<Rc<BigInt>>, C22: Array<Rc<BigInt>>) -> Array<Rc<BigInt>> {
  let tmp = s * s;
  let callback: Rc<dyn Fn(Int63) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_26 = s;
    move |k: Int63| -> Rc<BigInt> {
      let s = &__anf_capture_26;
      let C11 = &C11;
      let C12 = &C12;
      let C21 = &C21;
      let h = &h;
      let C22 = &C22;
      let i = k / Clone::clone(s);
      let j = k % Clone::clone(s);
      let h_clone = Clone::clone(h);
      if i < h_clone {
        let h_clone_1 = Clone::clone(h);
        if j < h_clone_1 {
          let tmp_1 = i * Clone::clone(h) + j;
          C11.get_cloned(tmp_1)
        } else {
          let tmp_2 = i * Clone::clone(h) + (j - Clone::clone(h));
          C12.get_cloned(tmp_2)
        }
      } else {
        let h_clone_2 = Clone::clone(h);
        if j < h_clone_2 {
          let tmp_3 = (i - Clone::clone(h)) * Clone::clone(h) + j;
          C21.get_cloned(tmp_3)
        } else {
          let tmp_4 = (i - Clone::clone(h)) * Clone::clone(h) + (j - Clone::clone(h));
          C22.get_cloned(tmp_4)
        }
      }
    }
  });
  build(tmp, callback)
}

// Rocq: Timing.timing_implem.dot
// Variant: borrowed, uncurried
pub fn dot(s: Int63, X: &Array<Rc<BigInt>>, Y: &Array<Rc<BigInt>>, i: Int63, j: Int63) -> Rc<BigInt> {
  let X_clone = Clone::clone(X);
  let Y_clone = Clone::clone(Y);
  let callback: Rc<dyn Fn(Int63, Rc<BigInt>) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_26 = s;
    move |k: Int63, acc: Rc<BigInt>| -> Rc<BigInt> {
      let i = &i;
      let X = &X_clone;
      let s = &__anf_capture_26;
      let j = &j;
      let Y = &Y_clone;
      let tmp = X.get_cloned(Clone::clone(i) * Clone::clone(s) + k);
      let tmp_1 = Y.get_cloned(k * Clone::clone(s) + Clone::clone(j));
      let tmp_2 = b::mul(tmp, tmp_1);
      b::add(acc, tmp_2)
    }
  });
  let tmp_3 = b::zero();
  loop_::<Rc<BigInt>>(s, callback, int63!(0), tmp_3)
}

// Rocq: Timing.timing_implem.naive
// Variant: uncurried
pub fn naive(s: Int63, X: Array<Rc<BigInt>>, Y: Array<Rc<BigInt>>) -> Array<Rc<BigInt>> {
  let tmp = s * s;
  let callback: Rc<dyn Fn(Int63) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_17 = s;
    move |k: Int63| -> Rc<BigInt> {
      let s = &__anf_capture_17;
      let X = &X;
      let Y = &Y;
      let tmp_1 = k / Clone::clone(s);
      let tmp_2 = k % Clone::clone(s);
      let s_clone = Clone::clone(s);
      dot(s_clone, X, Y, tmp_1, tmp_2)
    }
  });
  build(tmp, callback)
}

// Rocq: Timing.timing_implem.strass
// Variant: uncurried
pub fn strass_1(s: Int63, X: Array<Rc<BigInt>>, Y: Array<Rc<BigInt>>) -> Array<Rc<BigInt>> {
  strass(s, X, Y, ())
}

// Rocq: Timing.timing_implem.strass (local: strass)
// Variant: uncurried, lifted
pub fn strass(s: Int63, X: Array<Rc<BigInt>>, Y: Array<Rc<BigInt>>, _H: ()) -> Array<Rc<BigInt>> {
  let tmp = splitb(s);
  match bdec(tmp) {
    sumbool::left => {
      let h = s / int63!(2);
      let sr: Rc<dyn Fn(Array<Rc<BigInt>>, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = Rc::new({
        let __anf_capture_24 = h;
        move |A: Array<Rc<BigInt>>, B: Array<Rc<BigInt>>| -> Array<Rc<BigInt>> {
          let tmp_1 = Clone::clone(&__anf_capture_24);
          strass(tmp_1, A, B, ())
        }
      });
      let X_clone = Clone::clone(&X);
      let A11 = quad(X_clone, s, h, int63!(0), int63!(0));
      let X_clone_1 = Clone::clone(&X);
      let A12 = quad(X_clone_1, s, h, int63!(0), h);
      let X_clone_2 = Clone::clone(&X);
      let A21 = quad(X_clone_2, s, h, h, int63!(0));
      let A22 = quad(X, s, h, h, h);
      let Y_clone = Clone::clone(&Y);
      let B11 = quad(Y_clone, s, h, int63!(0), int63!(0));
      let Y_clone_1 = Clone::clone(&Y);
      let B12 = quad(Y_clone_1, s, h, int63!(0), h);
      let Y_clone_2 = Clone::clone(&Y);
      let B21 = quad(Y_clone_2, s, h, h, int63!(0));
      let B22 = quad(Y, s, h, h, h);
      let A11_clone = Clone::clone(&A11);
      let A22_clone = Clone::clone(&A22);
      let tmp_2 = madd(h, A11_clone, A22_clone);
      let B11_clone = Clone::clone(&B11);
      let B22_clone = Clone::clone(&B22);
      let tmp_3 = madd(h, B11_clone, B22_clone);
      let sr_ref: &Rc<dyn Fn(Array<Rc<BigInt>>, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = &sr;
      let M1 = sr_ref(tmp_2, tmp_3);
      let A21_clone = Clone::clone(&A21);
      let A22_clone_1 = Clone::clone(&A22);
      let tmp_4 = madd(h, A21_clone, A22_clone_1);
      let sr_ref_1: &Rc<dyn Fn(Array<Rc<BigInt>>, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = &sr;
      let B11_clone_1 = Clone::clone(&B11);
      let M2 = sr_ref_1(tmp_4, B11_clone_1);
      let B12_clone = Clone::clone(&B12);
      let B22_clone_1 = Clone::clone(&B22);
      let tmp_5 = msub(h, B12_clone, B22_clone_1);
      let sr_ref_2: &Rc<dyn Fn(Array<Rc<BigInt>>, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = &sr;
      let A11_clone_1 = Clone::clone(&A11);
      let M3 = sr_ref_2(A11_clone_1, tmp_5);
      let B21_clone = Clone::clone(&B21);
      let B11_clone_2 = Clone::clone(&B11);
      let tmp_6 = msub(h, B21_clone, B11_clone_2);
      let sr_ref_3: &Rc<dyn Fn(Array<Rc<BigInt>>, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = &sr;
      let A22_clone_2 = Clone::clone(&A22);
      let M4 = sr_ref_3(A22_clone_2, tmp_6);
      let A11_clone_2 = Clone::clone(&A11);
      let A12_clone = Clone::clone(&A12);
      let tmp_7 = madd(h, A11_clone_2, A12_clone);
      let sr_ref_4: &Rc<dyn Fn(Array<Rc<BigInt>>, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = &sr;
      let B22_clone_2 = Clone::clone(&B22);
      let M5 = sr_ref_4(tmp_7, B22_clone_2);
      let tmp_8 = msub(h, A21, A11);
      let tmp_9 = madd(h, B11, B12);
      let sr_ref_5: &Rc<dyn Fn(Array<Rc<BigInt>>, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = &sr;
      let M6 = sr_ref_5(tmp_8, tmp_9);
      let tmp_10 = msub(h, A12, A22);
      let tmp_11 = madd(h, B21, B22);
      let sr_ref_6: &Rc<dyn Fn(Array<Rc<BigInt>>, Array<Rc<BigInt>>) -> Array<Rc<BigInt>>> = &sr;
      let M7 = sr_ref_6(tmp_10, tmp_11);
      std::mem::drop(sr);
      let M1_clone = Clone::clone(&M1);
      let M4_clone = Clone::clone(&M4);
      let tmp_12 = madd(h, M1_clone, M4_clone);
      let M5_clone = Clone::clone(&M5);
      let tmp_13 = msub(h, tmp_12, M5_clone);
      let tmp_14 = madd(h, tmp_13, M7);
      let M3_clone = Clone::clone(&M3);
      let tmp_15 = madd(h, M3_clone, M5);
      let M2_clone = Clone::clone(&M2);
      let tmp_16 = madd(h, M2_clone, M4);
      let tmp_17 = msub(h, M1, M2);
      let tmp_18 = madd(h, tmp_17, M3);
      let tmp_19 = madd(h, tmp_18, M6);
      comb(s, h, tmp_14, tmp_15, tmp_16, tmp_19)
    },
    sumbool::right => {
      naive(s, X, Y)
    },
  }
}

// Rocq: Timing.timing_implem.mulr
// Variant: uncurried
pub fn mulr(m: Int63, X: Array<Rc<BigInt>>, Y: Array<Rc<BigInt>>) -> Array<Rc<BigInt>> {
  let C = strass_1(m, X, Y);
  let tmp = m * m;
  let callback: Rc<dyn Fn(Int63) -> Rc<BigInt>> = Rc::new({
    move |k: Int63| -> Rc<BigInt> {
      let tmp_1 = C.get_cloned(k);
      let tmp_2 = PP(());
      b::shiftr(tmp_1, tmp_2)
    }
  });
  build(tmp, callback)
}

// Rocq: Timing.timing_implem.pw
// Variant: uncurried
pub fn pw_1(m: Int63, t: Int63, R: Rc<option<Array<Rc<BigInt>>>>, B: Array<Rc<BigInt>>) -> Rc<option<Array<Rc<BigInt>>>> {
  pw(m, t, R, B, ())
}

// Rocq: Timing.timing_implem.pw (local: pw)
// Variant: uncurried, lifted
pub fn pw(m: Int63, t: Int63, R: Rc<option<Array<Rc<BigInt>>>>, B: Array<Rc<BigInt>>, _H: ()) -> Rc<option<Array<Rc<BigInt>>>> {
  let tmp = t == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      std::mem::drop(B);
      R
    },
    sumbool::right => {
      let tmp_1 = t % int63!(2);
      let tmp_2 = int63!(0);
      let R_ = if tmp_1 == tmp_2 {
        R
      } else {
        let tmp_3 = match &*R {
          option::Some(X) => {
            let X_clone = Clone::clone(X);
            std::mem::drop(R);
            let B_clone = Clone::clone(&B);
            mulr(m, X_clone, B_clone)
          },
          option::None => {
            std::mem::drop(R);
            Clone::clone(&B)
          },
        };
        Rc::new(option::<Array<Rc<BigInt>>>::Some(tmp_3))
      };
      let t_ = t / int63!(2);
      if t_ == int63!(0) {
        std::mem::drop(B);
        R_
      } else {
        let B_clone_1 = Clone::clone(&B);
        let tmp_4 = mulr(m, B_clone_1, B);
        pw(m, t_, R_, tmp_4, ())
      }
    },
  }
}

// Rocq: Timing.timing_implem.faced_z
// Variant: uncurried
pub fn faced_z_owned(n: Int63, adj: Array<bool>, v: Array<Rc<BigInt>>, i: Int63) -> Rc<BigInt> {
  let tmp = v.get_cloned(i);
  let callback: Rc<dyn Fn(Int63, Rc<BigInt>) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_18 = i;
    let __anf_capture_20 = n;
    let __anf_capture_24 = v;
    move |k: Int63, acc: Rc<BigInt>| -> Rc<BigInt> {
      let i = &__anf_capture_18;
      let n = &__anf_capture_20;
      let adj = &adj;
      let v = &__anf_capture_24;
      let tmp_1 = Clone::clone(i) * Clone::clone(n) + k;
      if adj.get_cloned(tmp_1) {
        let tmp_2 = v.get_cloned(k);
        b::add(acc, tmp_2)
      } else {
        acc
      }
    }
  });
  let tmp_3 = b::zero();
  let tmp_4 = loop_::<Rc<BigInt>>(n, callback, int63!(0), tmp_3);
  b::add(tmp, tmp_4)
}

// Rocq: Timing.timing_implem.faced_z
// Variant: borrowed, uncurried
pub fn faced_z(n: Int63, adj: &Array<bool>, v: &Array<Rc<BigInt>>, i: Int63) -> Rc<BigInt> {
  let tmp = v.get_cloned(i);
  let adj_clone = Clone::clone(adj);
  let v_clone = Clone::clone(v);
  let callback: Rc<dyn Fn(Int63, Rc<BigInt>) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_22 = i;
    let __anf_capture_24 = n;
    move |k: Int63, acc: Rc<BigInt>| -> Rc<BigInt> {
      let i = &__anf_capture_22;
      let n = &__anf_capture_24;
      let adj = &adj_clone;
      let v = &v_clone;
      let tmp_1 = Clone::clone(i) * Clone::clone(n) + k;
      if adj.get_cloned(tmp_1) {
        let tmp_2 = v.get_cloned(k);
        b::add(acc, tmp_2)
      } else {
        acc
      }
    }
  });
  let tmp_3 = b::zero();
  let tmp_4 = loop_::<Rc<BigInt>>(n, callback, int63!(0), tmp_3);
  b::add(tmp, tmp_4)
}

// Rocq: Timing.timing_implem.iofp
pub fn iofp_1(p: Rc<BigInt>) -> Int63 {
  iofp(p)
}

// Rocq: Timing.timing_implem.iofp (local: iofp)
// Variant: lifted
pub fn iofp(p: Rc<BigInt>) -> Int63 {
  let p_clone = Rc::clone(&p);
  match b::positive_tag(p_clone) {
    b::PositiveTag::Odd => {
      let q = b::positive_tail(p);
      int63!(2) * iofp(q) + int63!(1)
    },
    b::PositiveTag::Even => {
      let q = b::positive_tail(p);
      int63!(2) * iofp(q)
    },
    b::PositiveTag::One => {
      std::mem::drop(p);
      int63!(1)
    },
  }
}

// Rocq: Timing.timing_implem.iofz
pub fn iofz(z: Rc<BigInt>) -> Int63 {
  let z_clone = Rc::clone(&z);
  match b::integer_tag(z_clone) {
    b::IntegerTag::Zero => {
      std::mem::drop(z);
      int63!(0)
    },
    b::IntegerTag::Positive => {
      let p = b::integer_magnitude(z);
      iofp_1(p)
    },
    b::IntegerTag::Negative => {
      let p = b::integer_magnitude(z);
      std::mem::drop(p);
      int63!(0)
    },
  }
}

// Rocq: Timing.timing_implem.cv
pub fn cv(z: Rc<BigInt>) -> f64 {
  let tmp = b::one();
  let tmp_1 = b::twice(tmp);
  let tmp_2 = b::identity(tmp_1);
  let tmp_3 = PP(());
  let tmp_4 = b::mul(tmp_2, tmp_3);
  let tmp_5 = b::one();
  let tmp_6 = b::twice_plus_one(tmp_5);
  let tmp_7 = b::twice_plus_one(tmp_6);
  let tmp_8 = b::twice_plus_one(tmp_7);
  let tmp_9 = b::twice(tmp_8);
  let tmp_10 = b::identity(tmp_9);
  let tmp_11 = b::sub(tmp_4, tmp_10);
  let tmp_12 = b::shiftr(z, tmp_11);
  rocq_float64::div(rocq_float64::of_uint63(iofz(tmp_12)), rocq_float64::of_uint63(int63!(1073741824)))
}

// Rocq: Timing.timing_implem.conv
pub fn conv(z: Rc<BigInt>) -> f64 {
  let tmp = b::zero();
  let z_clone = Rc::clone(&z);
  if b::lt(z_clone, tmp) {
    let tmp_1 = b::neg(z);
    rocq_float64::opp(cv(tmp_1))
  } else {
    cv(z)
  }
}

// Rocq: Timing.timing_implem.timing_exact
// Variant: uncurried
pub fn timing_exact(xt: Int63, xu: Array<f64>, xs: Array<Int63>, xd: Array<Int63>, xf: Array<f64>) -> f64 {
  let n = xu.length();
  let L = xs.length();
  let m = (n + int63!(7)) / int63!(8) * int63!(8);
  let xs_clone = Clone::clone(&xs);
  let xd_clone = Clone::clone(&xd);
  let A = amat(m, L, xs_clone, xd_clone, xf);
  let tmp = pw_1(m, xt, Rc::new(option::<Array<Rc<BigInt>>>::None), A);
  let (v60, v61) = __rocq_reuse::reset(tmp, |__payload| Clone::clone(__payload));
  std::mem::drop(v61);
  let Rf = match v60 {
    option::Some(v66) => {
      v66
    },
    option::None => {
      ident(m)
    },
  };
  let callback: Rc<dyn Fn(Int63) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_83 = n;
    let __anf_capture_85 = xu;
    move |s: Int63| -> Rc<BigInt> {
      let n = &__anf_capture_83;
      let xu = &__anf_capture_85;
      let n_clone = Clone::clone(n);
      if s < n_clone {
        let tmp_1 = xu.get_cloned(s);
        fixv(tmp_1)
      } else {
        b::zero()
      }
    }
  });
  let uh = build(m, callback);
  let callback_1: Rc<dyn Fn(Int63) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_129 = m;
    move |i: Int63| -> Rc<BigInt> {
      let Rf = &Rf;
      let uh = &uh;
      let m = &__anf_capture_129;
      let m_clone = Clone::clone(m);
      let Rf_clone = Clone::clone(Rf);
      let uh_clone = Clone::clone(uh);
      let callback_2: Rc<dyn Fn(Int63, Rc<BigInt>) -> Rc<BigInt>> = Rc::new({
        move |k: Int63, acc: Rc<BigInt>| -> Rc<BigInt> {
          let i = &i;
          let m = &m_clone;
          let Rf = &Rf_clone;
          let uh = &uh_clone;
          let tmp_2 = Rf.get_cloned(Clone::clone(i) * Clone::clone(m) + k);
          let tmp_3 = uh.get_cloned(k);
          let tmp_4 = b::mul(tmp_2, tmp_3);
          b::add(acc, tmp_4)
        }
      });
      let tmp_5 = b::zero();
      let m_clone_1 = Clone::clone(m);
      loop_::<Rc<BigInt>>(m_clone_1, callback_2, int63!(0), tmp_5)
    }
  });
  let v = build(m, callback_1);
  let callback_3: Rc<dyn Fn(Int63, Array<bool>) -> Array<bool>> = Rc::new({
    let __anf_capture_215 = n;
    let __anf_capture_217 = xs;
    let __anf_capture_219 = xd;
    move |v221: Int63, v222: Array<bool>| -> Array<bool> {
      let tmp_6 = Clone::clone(&__anf_capture_215);
      let tmp_7 = Clone::clone(&__anf_capture_217);
      let tmp_8 = Clone::clone(&__anf_capture_219);
      adj_step(tmp_6, tmp_7, tmp_8, v221, v222)
    }
  });
  let adj = loop_::<Array<bool>>(L, callback_3, int63!(0), Array::<bool>::make(n * n, false));
  let adj_clone = Clone::clone(&adj);
  let v_clone = Clone::clone(&v);
  let callback_4: Rc<dyn Fn(Int63, Rc<BigInt>) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_273 = n;
    move |i: Int63, b_1: Rc<BigInt>| -> Rc<BigInt> {
      let tmp_9 = faced_z(Clone::clone(&__anf_capture_273), &adj_clone, &v_clone, i);
      b::min(b_1, tmp_9)
    }
  });
  let tmp_10 = faced_z_owned(n, adj, v, int63!(0));
  let best = loop_::<Rc<BigInt>>(n, callback_4, int63!(1), tmp_10);
  conv(best)
}

// Rocq: Timing.timing_implem.timing_impl
// Variant: uncurried
pub fn timing_impl(xt: Int63, xu: Array<f64>, xs: Array<Int63>, xd: Array<Int63>, xf: Array<f64>) -> f64 {
  let n = xu.length();
  let L = xs.length();
  let xs_clone = Clone::clone(&xs);
  let xd_clone = Clone::clone(&xd);
  let callback: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
    move |v21: Int63, v22: Array<Int63>| -> Array<Int63> {
      let tmp = Clone::clone(&xs_clone);
      let tmp_1 = Clone::clone(&xd_clone);
      cnt_step(tmp, tmp_1, v21, v22)
    }
  });
  let c = loop_::<Array<Int63>>(L, callback, int63!(0), Array::<Int63>::make(n, int63!(0)));
  let xs_clone_1 = Clone::clone(&xs);
  let xd_clone_1 = Clone::clone(&xd);
  let xf_clone = Clone::clone(&xf);
  let callback_1: Rc<dyn Fn(Int63, Array<f64>) -> Array<f64>> = Rc::new({
    move |v72: Int63, v73: Array<f64>| -> Array<f64> {
      let tmp_2 = Clone::clone(&xs_clone_1);
      let tmp_3 = Clone::clone(&xd_clone_1);
      let tmp_4 = Clone::clone(&xf_clone);
      out_step(tmp_2, tmp_3, tmp_4, v72, v73)
    }
  });
  let ou = loop_::<Array<f64>>(L, callback_1, int63!(0), Array::<f64>::make(n, f64::from_bits(0u64)));
  let xs_clone_2 = Clone::clone(&xs);
  let xd_clone_2 = Clone::clone(&xd);
  let xf_clone_1 = Clone::clone(&xf);
  let ou_clone = Clone::clone(&ou);
  let c_clone = Clone::clone(&c);
  let callback_2: Rc<dyn Fn(Int63, ((Array<f64>, Array<f64>), bool)) -> ((Array<f64>, Array<f64>), bool)> = Rc::new({
    let __anf_capture_129 = n;
    let __anf_capture_131 = L;
    move |v143: Int63, v144: ((Array<f64>, Array<f64>), bool)| -> ((Array<f64>, Array<f64>), bool) {
      let n = &__anf_capture_129;
      let L = &__anf_capture_131;
      let xs = &xs_clone_2;
      let xd = &xd_clone_2;
      let xf = &xf_clone_1;
      let ou = &ou_clone;
      let c = &c_clone;
      let tmp_5 = tstep(Clone::clone(n), Clone::clone(L), xs, xd, xf, ou, c, v143, v144);
      tmp_5
    }
  });
  let tmp_6 = Array::<f64>::make(n, f64::from_bits(0u64));
  let xu_clone = Clone::clone(&xu);
  let tmp_7 = loop_::<((Array<f64>, Array<f64>), bool)>(xt, callback_2, int63!(0), ((xu_clone, tmp_6), true));
  match tmp_7 {
    (v198, v200) => {
      let p = &v200;
      match v198 {
        (v204, v206) => {
          let e = &v204;
          let v = &v206;
          if *p {
            let xs_clone_3 = Clone::clone(&xs);
            let xd_clone_3 = Clone::clone(&xd);
            let callback_3: Rc<dyn Fn(Int63, Array<bool>) -> Array<bool>> = Rc::new({
              let __anf_capture_221 = n;
              move |v227: Int63, v228: Array<bool>| -> Array<bool> {
                let tmp_8 = Clone::clone(&__anf_capture_221);
                let tmp_9 = Clone::clone(&xs_clone_3);
                let tmp_10 = Clone::clone(&xd_clone_3);
                adj_step(tmp_8, tmp_9, tmp_10, v227, v228)
              }
            });
            let adj = loop_::<Array<bool>>(L, callback_3, int63!(0), Array::<bool>::make(n * n, false));
            let adj_clone = Clone::clone(&adj);
            let e_clone = Clone::clone(e);
            let callback_4: Rc<dyn Fn(Int63, f64) -> f64> = Rc::new({
              let __anf_capture_278 = n;
              move |i: Int63, b_1: f64| -> f64 {
                let tmp_11 = faced_f(Clone::clone(&__anf_capture_278), &adj_clone, &e_clone, i);
                fmin(b_1, tmp_11)
              }
            });
            let tmp_12 = int63!(0);
            let adj_clone_1 = Clone::clone(&adj);
            let tmp_13 = faced_f_owned(n, adj_clone_1, Clone::clone(e), tmp_12);
            let o = loop_::<f64>(n, callback_4, int63!(1), tmp_13);
            let nu = rocq_float64::mul(rocq_float64::of_uint63(n + int63!(1)), __rocq_global_419);
            let adj_clone_2 = Clone::clone(&adj);
            let e_clone_1 = Clone::clone(e);
            let v_clone = Clone::clone(v);
            let callback_5: Rc<dyn Fn(Int63) -> f64> = Rc::new({
              let __anf_capture_360 = n;
              move |v370: Int63| -> f64 {
                let n = &__anf_capture_360;
                let adj = &adj_clone_2;
                let e = &e_clone_1;
                let v = &v_clone;
                let n_clone = Clone::clone(n);
                let nu_clone = Clone::clone(&nu);
                fbound(n_clone, adj, e, v, nu_clone, v370)
              }
            });
            let B = gmax(n, callback_5);
            if fcheck(B, o) {
              std::mem::drop(adj);
              std::mem::drop(ou);
              std::mem::drop(c);
              std::mem::drop(xu);
              std::mem::drop(xf);
              std::mem::drop(xd);
              std::mem::drop(xs);
              std::mem::drop(v206);
              std::mem::drop(v204);
              o
            } else {
              std::mem::drop(adj);
              std::mem::drop(ou);
              std::mem::drop(c);
              std::mem::drop(v206);
              std::mem::drop(v204);
              timing_exact(xt, xu, xs, xd, xf)
            }
          } else {
            std::mem::drop(ou);
            std::mem::drop(c);
            std::mem::drop(v206);
            std::mem::drop(v204);
            timing_exact(xt, xu, xs, xd, xf)
          }
        },
      }
    },
  }
}
const __rocq_global_416: f64 = f64::from_bits(4607182418804211712u64);
const __rocq_global_419: f64 = f64::from_bits(4372995238176751616u64);
const __rocq_global_444: f64 = f64::from_bits(4472074429978902528u64);
const __rocq_global_1401: Int63 = int63!(16);