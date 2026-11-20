#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;
#[allow(unused_imports)] use rocq_bigint::BigInt;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

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

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::PositiveTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::NaturalTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::IntegerTag>; };

pub type uint = u64;

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
pub fn cut() -> u64 {
  16u64
}

// Rocq: Corelib.BinNums.IntDef.Z.add
// Variant: uncurried
pub fn add(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::add(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.opp
pub fn opp(v0: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::neg(v0)
}

// Rocq: Corelib.BinNums.IntDef.Z.sub
// Variant: uncurried
pub fn sub(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Timing.timing_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add_1(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Timing.timing_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: u64, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop::<St>(hi, f, i, s, ())
}

// Rocq: Timing.timing_implem.wloop (local: wloop)
// Variant: uncurried, lifted
pub fn wloop<St: Clone + 'static>(hi: u64, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St, _H: ()) -> St {
  let tmp = ltb(i, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add_1(i, 1u64);
      let f_ref: &Rc<dyn Fn(u64, St) -> St> = &f;
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
pub fn loop_<St: Clone + 'static>(hi: u64, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop_1::<St>(hi, f, i, s)
}

// Rocq: Timing.timing_implem.cnt_step
// Variant: uncurried
pub fn cnt_step(xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, j: u64, c: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let s = rocq_array::get::<u64>(&xs, j);
  let d = rocq_array::get::<u64>(&xd, j);
  if eqb(s, d) {
    std::mem::drop(xs);
    std::mem::drop(xd);
    c
  } else {
    std::mem::drop(xs);
    std::mem::drop(xd);
    let tmp = rocq_array::get::<u64>(&c, s);
    let c1 = rocq_array::set::<u64>(c, s, add_1(tmp, 1u64));
    let tmp_1 = rocq_array::get::<u64>(&c1, d);
    rocq_array::set::<u64>(c1, d, add_1(tmp_1, 1u64))
  }
}

// Rocq: Corelib.Floats.PrimFloat.add
// Variant: uncurried
pub fn add_2(v0: f64, v1: f64) -> f64 {
  rocq_float64::add(v0, v1)
}

// Rocq: Timing.timing_implem.out_step
// Variant: uncurried
pub fn out_step(xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, xf: Rc<Array<f64>>, j: u64, o: Rc<Array<f64>>) -> Rc<Array<f64>> {
  let s = rocq_array::get::<u64>(&xs, j);
  let d = rocq_array::get::<u64>(&xd, j);
  if eqb(s, d) {
    std::mem::drop(xs);
    std::mem::drop(xf);
    std::mem::drop(xd);
    o
  } else {
    std::mem::drop(xs);
    std::mem::drop(xd);
    let tmp = rocq_array::get::<f64>(&o, s);
    let tmp_1 = rocq_array::get::<f64>(&xf, j);
    std::mem::drop(xf);
    rocq_array::set::<f64>(o, s, add_2(tmp, tmp_1))
  }
}

// Rocq: Corelib.Floats.PrimFloat.abs
pub fn abs(v0: f64) -> f64 {
  rocq_float64::abs(v0)
}

// Rocq: Corelib.Floats.PrimFloat.mul
// Variant: uncurried
pub fn mul(v0: f64, v1: f64) -> f64 {
  rocq_float64::mul(v0, v1)
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
pub fn elink(xs: &Rc<Array<u64>>, xd: &Rc<Array<u64>>, xf: &Rc<Array<f64>>, v: &Rc<Array<f64>>, e: &Rc<Array<f64>>, j: u64, st: (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>) {
  let j_1 = j;
  let st_1 = st;
  let s = rocq_array::get::<u64>(xs, j_1);
  let d = rocq_array::get::<u64>(xd, j_1);
  if eqb(s, d) {
    st_1
  } else {
    let a = abs(mul(rocq_array::get::<f64>(xf, j_1), rocq_array::get::<f64>(v, s)));
    let st_clone = Clone::clone(&st_1);
    let ein = fst::<Rc<Array<f64>>, Rc<Array<f64>>>(st_clone);
    let mac = snd::<Rc<Array<f64>>, Rc<Array<f64>>>(st_1);
    let tmp = rocq_array::get::<f64>(&mac, d);
    let mac1 = rocq_array::set::<f64>(mac, d, add_2(tmp, a));
    let tmp_1 = rocq_array::get::<f64>(&ein, d);
    let tmp_2 = rocq_array::set::<f64>(ein, d, add_2(tmp_1, mul(rocq_array::get::<f64>(xf, j_1), rocq_array::get::<f64>(e, s))));
    let tmp_3 = rocq_array::get::<f64>(&mac1, s);
    let tmp_4 = rocq_array::set::<f64>(mac1, s, add_2(tmp_3, a));
    (tmp_2, tmp_4)
  }
}

// Rocq: Timing.timing_implem.up
pub fn up(y: f64) -> f64 {
  add_2(mul(y, __rocq_global_416), __rocq_global_419)
}

// Rocq: Corelib.Floats.PrimFloat.sub
// Variant: uncurried
pub fn sub_1(v0: f64, v1: f64) -> f64 {
  rocq_float64::sub(v0, v1)
}

// Rocq: Timing.timing_implem.coef
// Variant: borrowed, uncurried
pub fn coef(ou: &Rc<Array<f64>>, x: u64) -> f64 {
  let x_1 = x;
  add_2(abs(sub_1(f64::from_bits(4607182418800017408u64), rocq_array::get::<f64>(ou, x_1))), __rocq_global_444)
}

// Rocq: Corelib.Floats.PrimFloat.of_uint63
pub fn of_uint63(v0: u64) -> f64 {
  rocq_float64::of_uint63(v0)
}

// Rocq: Timing.timing_implem.kx
// Variant: borrowed, uncurried
pub fn kx(c: &Rc<Array<u64>>, x: u64) -> f64 {
  let x_1 = x;
  let tmp = add_1(rocq_array::get::<u64>(c, x_1), rocq_array::get::<u64>(c, x_1));
  mul(of_uint63(add_1(tmp, 3u64)), __rocq_global_419)
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

// Rocq: Corelib.Floats.PrimFloat.leb
// Variant: uncurried
pub fn leb(v0: f64, v1: f64) -> bool {
  rocq_float64::leb(v0, v1)
}

// Rocq: Timing.timing_implem.efort
// Variant: borrowed, uncurried
pub fn efort(ou: &Rc<Array<f64>>, c: &Rc<Array<u64>>, v: &Rc<Array<f64>>, e: &Rc<Array<f64>>, ein: &Rc<Array<f64>>, mac: &Rc<Array<f64>>, x: u64, st: (Rc<Array<f64>>, bool)) -> (Rc<Array<f64>>, bool) {
  let x_1 = x;
  let st_1 = st;
  let tmp = add_2(mul(coef(ou, x_1), rocq_array::get::<f64>(e, x_1)), rocq_array::get::<f64>(ein, x_1));
  let tmp_1 = kx(c, x_1);
  let tmp_2 = add_2(abs(rocq_array::get::<f64>(v, x_1)), rocq_array::get::<f64>(mac, x_1));
  let tmp_3 = add_2(tmp_2, f64::from_bits(4607182418800017408u64));
  let y = up(add_2(tmp, mul(tmp_1, tmp_3)));
  let st_clone = Clone::clone(&st_1);
  let tmp_4 = fst::<Rc<Array<f64>>, bool>(st_clone);
  let tmp_5 = rocq_array::set::<f64>(tmp_4, x_1, y);
  (tmp_5, andb(snd::<Rc<Array<f64>>, bool>(st_1), leb(y, f64::from_bits(4607182418800017408u64))))
}

// Rocq: Timing.timing_implem.ebound
// Variant: uncurried
pub fn ebound(n: u64, L: u64, xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, xf: Rc<Array<f64>>, ou: Rc<Array<f64>>, c: Rc<Array<u64>>, v: Rc<Array<f64>>, e: Rc<Array<f64>>) -> (Rc<Array<f64>>, bool) {
  let v_clone = Rc::clone(&v);
  let e_clone = Rc::clone(&e);
  let callback: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>)> = Rc::new({
    move |v33: u64, v34: (Rc<Array<f64>>, Rc<Array<f64>>)| -> (Rc<Array<f64>>, Rc<Array<f64>>) {
      let xs = &xs;
      let xd = &xd;
      let xf = &xf;
      let v = &v_clone;
      let e = &e_clone;
      let tmp = elink(xs, xd, xf, v, e, v33, v34);
      tmp
    }
  });
  let tmp_1 = rocq_array::make::<f64>(n, f64::from_bits(0u64));
  let tmp_2 = rocq_array::make::<f64>(n, f64::from_bits(0u64));
  let st = loop_::<(Rc<Array<f64>>, Rc<Array<f64>>)>(L, callback, 0u64, (tmp_1, tmp_2));
  let st_clone = Clone::clone(&st);
  let tmp_3 = fst::<Rc<Array<f64>>, Rc<Array<f64>>>(st_clone);
  let tmp_4 = snd::<Rc<Array<f64>>, Rc<Array<f64>>>(st);
  let callback_1: Rc<dyn Fn(u64, (Rc<Array<f64>>, bool)) -> (Rc<Array<f64>>, bool)> = Rc::new({
    let __anf_capture_108 = v;
    let __anf_capture_110 = e;
    move |v116: u64, v117: (Rc<Array<f64>>, bool)| -> (Rc<Array<f64>>, bool) {
      let ou = &ou;
      let c = &c;
      let v = &__anf_capture_108;
      let e = &__anf_capture_110;
      let v112 = &tmp_3;
      let v114 = &tmp_4;
      let tmp_5 = efort(ou, c, v, e, v112, v114, v116, v117);
      tmp_5
    }
  });
  let tmp_6 = rocq_array::make::<f64>(n, f64::from_bits(0u64));
  loop_::<(Rc<Array<f64>>, bool)>(n, callback_1, 0u64, (tmp_6, true))
}

// Rocq: Timing.timing_implem.link_f
// Variant: uncurried
pub fn link_f(xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, xf: Rc<Array<f64>>, v: Rc<Array<f64>>, j: u64, w: Rc<Array<f64>>) -> Rc<Array<f64>> {
  let s = rocq_array::get::<u64>(&xs, j);
  let d = rocq_array::get::<u64>(&xd, j);
  if eqb(s, d) {
    std::mem::drop(xs);
    std::mem::drop(xf);
    std::mem::drop(v);
    std::mem::drop(xd);
    w
  } else {
    std::mem::drop(xs);
    std::mem::drop(xd);
    let tmp = rocq_array::get::<f64>(&xf, j);
    std::mem::drop(xf);
    let tmp_1 = rocq_array::get::<f64>(&v, s);
    std::mem::drop(v);
    let a = mul(tmp, tmp_1);
    let tmp_2 = rocq_array::get::<f64>(&w, d);
    let w1 = rocq_array::set::<f64>(w, d, add_2(tmp_2, a));
    let tmp_3 = rocq_array::get::<f64>(&w1, s);
    rocq_array::set::<f64>(w1, s, sub_1(tmp_3, a))
  }
}

// Rocq: Timing.timing_implem.unit_f
// Variant: uncurried
pub fn unit_f(L: u64, xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, xf: Rc<Array<f64>>, v: Rc<Array<f64>>) -> Rc<Array<f64>> {
  let v_clone = Rc::clone(&v);
  let callback: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new({
    move |v24: u64, v25: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let xs_clone = Rc::clone(&xs);
      let xd_clone = Rc::clone(&xd);
      let xf_clone = Rc::clone(&xf);
      let tmp = Rc::clone(&v_clone);
      link_f(xs_clone, xd_clone, xf_clone, tmp, v24, v25)
    }
  });
  let tmp_1 = 0u64;
  let tmp_2 = rocq_array::copy::<f64>(&v);
  std::mem::drop(v);
  loop_::<Rc<Array<f64>>>(L, callback, tmp_1, tmp_2)
}

// Rocq: Timing.timing_implem.tstep
// Variant: borrowed, uncurried
pub fn tstep(n: u64, L: u64, xs: &Rc<Array<u64>>, xd: &Rc<Array<u64>>, xf: &Rc<Array<f64>>, ou: &Rc<Array<f64>>, c: &Rc<Array<u64>>, _j: u64, st: ((Rc<Array<f64>>, Rc<Array<f64>>), bool)) -> ((Rc<Array<f64>>, Rc<Array<f64>>), bool) {
  let n_1 = n;
  let L_1 = L;
  let st_1 = st;
  match &st_1 {
    (ok, p) => {
      match ok {
        (e, v) => {
          if *p {
            let xs_clone = Rc::clone(xs);
            let xd_clone = Rc::clone(xd);
            let xf_clone = Rc::clone(xf);
            let ou_clone = Rc::clone(ou);
            let c_clone = Rc::clone(c);
            let e_clone = Rc::clone(e);
            let v_clone = Rc::clone(v);
            let r = ebound(n_1, L_1, xs_clone, xd_clone, xf_clone, ou_clone, c_clone, e_clone, v_clone);
            let xs_clone_1 = Rc::clone(xs);
            let xd_clone_1 = Rc::clone(xd);
            let xf_clone_1 = Rc::clone(xf);
            let e_clone_1 = Rc::clone(e);
            std::mem::drop(st_1);
            let tmp = unit_f(L_1, xs_clone_1, xd_clone_1, xf_clone_1, e_clone_1);
            let r_clone = Clone::clone(&r);
            let tmp_1 = fst::<Rc<Array<f64>>, bool>(r_clone);
            ((tmp, tmp_1), snd::<Rc<Array<f64>>, bool>(r))
          } else {
            st_1
          }
        },
      }
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul_1(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Timing.timing_implem.adj_step
// Variant: uncurried
pub fn adj_step(n: u64, xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, l: u64, a: Rc<Array<bool>>) -> Rc<Array<bool>> {
  let s = rocq_array::get::<u64>(&xs, l);
  let d = rocq_array::get::<u64>(&xd, l);
  if eqb(s, d) {
    std::mem::drop(xs);
    std::mem::drop(xd);
    a
  } else {
    std::mem::drop(xs);
    std::mem::drop(xd);
    let tmp = rocq_array::set::<bool>(a, add_1(mul_1(s, n), d), true);
    rocq_array::set::<bool>(tmp, add_1(mul_1(d, n), s), true)
  }
}

// Rocq: Corelib.Floats.PrimFloat.ltb
// Variant: uncurried
pub fn ltb_1(v0: f64, v1: f64) -> bool {
  rocq_float64::ltb(v0, v1)
}

// Rocq: Timing.timing_implem.fmin
// Variant: uncurried
pub fn fmin(b: f64, x: f64) -> f64 {
  if ltb_1(x, b) {
    x
  } else {
    b
  }
}

// Rocq: Timing.timing_implem.faced_f
// Variant: uncurried
pub fn faced_f_owned(n: u64, adj: Rc<Array<bool>>, v: Rc<Array<f64>>, i: u64) -> f64 {
  let v_clone = Rc::clone(&v);
  let callback: Rc<dyn Fn(u64, f64) -> f64> = Rc::new({
    let __anf_capture_15 = i;
    let __anf_capture_17 = n;
    move |k: u64, acc: f64| -> f64 {
      let i = &__anf_capture_15;
      let n = &__anf_capture_17;
      let adj = &adj;
      let v = &v_clone;
      let tmp = add_1(mul_1(Clone::clone(i), Clone::clone(n)), k);
      if rocq_array::get::<bool>(adj, tmp) {
        let tmp_1 = rocq_array::get::<f64>(v, k);
        add_2(acc, tmp_1)
      } else {
        acc
      }
    }
  });
  let tmp_2 = 0u64;
  let tmp_3 = rocq_array::get::<f64>(&v, i);
  std::mem::drop(v);
  loop_::<f64>(n, callback, tmp_2, tmp_3)
}

// Rocq: Timing.timing_implem.faced_f
// Variant: borrowed, uncurried
pub fn faced_f(n: u64, adj: &Rc<Array<bool>>, v: &Rc<Array<f64>>, i: u64) -> f64 {
  let adj_clone = Rc::clone(adj);
  let v_clone = Rc::clone(v);
  let callback: Rc<dyn Fn(u64, f64) -> f64> = Rc::new({
    let __anf_capture_18 = i;
    let __anf_capture_20 = n;
    move |k: u64, acc: f64| -> f64 {
      let i = &__anf_capture_18;
      let n = &__anf_capture_20;
      let adj = &adj_clone;
      let v = &v_clone;
      let tmp = add_1(mul_1(Clone::clone(i), Clone::clone(n)), k);
      if rocq_array::get::<bool>(adj, tmp) {
        let tmp_1 = rocq_array::get::<f64>(v, k);
        add_2(acc, tmp_1)
      } else {
        acc
      }
    }
  });
  loop_::<f64>(n, callback, 0u64, rocq_array::get::<f64>(v, i))
}

// Rocq: Timing.timing_implem.gmax
// Variant: uncurried
pub fn gmax(n: u64, g: Rc<dyn Fn(u64) -> f64>) -> f64 {
  let callback: Rc<dyn Fn(u64, f64) -> f64> = Rc::new({
    move |i: u64, m: f64| -> f64 {
      let g = &g;
      let tmp = g(i);
      if ltb_1(m, tmp) {
        g(i)
      } else {
        m
      }
    }
  });
  loop_::<f64>(n, callback, 0u64, f64::from_bits(0u64))
}

// Rocq: Timing.timing_implem.fpair
// Variant: borrowed, uncurried
pub fn fpair(n: u64, adj: &Rc<Array<bool>>, v: &Rc<Array<f64>>, e: &Rc<Array<f64>>, i: u64) -> (f64, f64) {
  let adj_clone = Rc::clone(adj);
  let e_clone = Rc::clone(e);
  let v_clone = Rc::clone(v);
  let callback: Rc<dyn Fn(u64, (f64, f64)) -> (f64, f64)> = Rc::new({
    let __anf_capture_22 = i;
    let __anf_capture_24 = n;
    move |k: u64, st: (f64, f64)| -> (f64, f64) {
      let i = &__anf_capture_22;
      let n = &__anf_capture_24;
      let adj = &adj_clone;
      let e = &e_clone;
      let v = &v_clone;
      let tmp = add_1(mul_1(Clone::clone(i), Clone::clone(n)), k);
      if rocq_array::get::<bool>(adj, tmp) {
        let st_clone = Clone::clone(&st);
        let tmp_1 = add_2(fst::<f64, f64>(st_clone), rocq_array::get::<f64>(e, k));
        let tmp_2 = snd::<f64, f64>(st);
        let tmp_3 = rocq_array::get::<f64>(v, k);
        (tmp_1, add_2(tmp_2, abs(tmp_3)))
      } else {
        st
      }
    }
  });
  loop_::<(f64, f64)>(n, callback, 0u64, (rocq_array::get::<f64>(e, i), abs(rocq_array::get::<f64>(v, i))))
}

// Rocq: Timing.timing_implem.fbound
// Variant: borrowed, uncurried
pub fn fbound(n: u64, adj: &Rc<Array<bool>>, v: &Rc<Array<f64>>, e: &Rc<Array<f64>>, nu: f64, i: u64) -> f64 {
  let n_1 = n;
  let nu_1 = nu;
  let i_1 = i;
  let p = fpair(n_1, adj, v, e, i_1);
  let p_clone = Clone::clone(&p);
  let tmp = fst::<f64, f64>(p_clone);
  let tmp_1 = add_2(snd::<f64, f64>(p), f64::from_bits(4607182418800017408u64));
  up(add_2(tmp, mul(nu_1, tmp_1)))
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.mul
// Variant: uncurried
pub fn mul_2(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::mul(v0, v1)
}

// Rocq: Timing.timing_implem.zofi_rec
pub fn zofi_rec_1(i: u64) -> Rc<BigInt> {
  zofi_rec(i, ())
}

// Rocq: Timing.timing_implem.zofi_rec (local: zofi_rec)
// Variant: uncurried, lifted
pub fn zofi_rec(i: u64, _H: ()) -> Rc<BigInt> {
  let tmp = eqb(i, 0u64);
  match bdec(tmp) {
    sumbool::left => {
      rocq_bigint::zero()
    },
    sumbool::right => {
      let r = zofi_rec(div(i, 2u64), ());
      let tmp_1 = mod_(i, 2u64);
      let tmp_2 = 0u64;
      let bit = if eqb(tmp_1, tmp_2) {
        rocq_bigint::zero()
      } else {
        let tmp_3 = rocq_bigint::one();
        rocq_bigint::identity(tmp_3)
      };
      let tmp_4 = rocq_bigint::one();
      let tmp_5 = rocq_bigint::twice(tmp_4);
      let tmp_6 = rocq_bigint::identity(tmp_5);
      let tmp_7 = mul_2(tmp_6, r);
      add(tmp_7, bit)
    },
  }
}

// Rocq: Timing.timing_implem.zofi
pub fn zofi(i: u64) -> Rc<BigInt> {
  zofi_rec_1(i)
}

// Rocq: Corelib.Floats.PrimFloat.normfr_mantissa
pub fn normfr_mantissa(v0: f64) -> u64 {
  rocq_float64::normfr_mantissa(v0)
}

// Rocq: Timing.timing_implem.fex
pub fn fex(f: f64) -> (Rc<BigInt>, Rc<BigInt>) {
  let tmp = frshiftexp(f);
  match tmp {
    (v6, v8) => {
      let z = &v8;
      let m = zofi(normfr_mantissa(v6));
      let tmp_1 = f64::from_bits(0u64);
      let tmp_2 = if ltb_1(f, tmp_1) {
        opp(m)
      } else {
        m
      };
      let z_clone = Clone::clone(z);
      let tmp_3 = zofi(z_clone);
      let tmp_4 = rocq_bigint::one();
      let tmp_5 = rocq_bigint::twice(tmp_4);
      let tmp_6 = rocq_bigint::twice(tmp_5);
      let tmp_7 = rocq_bigint::twice(tmp_6);
      let tmp_8 = rocq_bigint::twice(tmp_7);
      let tmp_9 = rocq_bigint::twice_plus_one(tmp_8);
      let tmp_10 = rocq_bigint::twice_plus_one(tmp_9);
      let tmp_11 = rocq_bigint::twice(tmp_10);
      let tmp_12 = rocq_bigint::twice_plus_one(tmp_11);
      let tmp_13 = rocq_bigint::twice(tmp_12);
      let tmp_14 = rocq_bigint::twice_plus_one(tmp_13);
      let tmp_15 = rocq_bigint::twice(tmp_14);
      let tmp_16 = rocq_bigint::identity(tmp_15);
      let tmp_17 = sub(tmp_3, tmp_16);
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

// Rocq: Corelib.BinNums.IntDef.Z.leb
// Variant: uncurried
pub fn leb_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::le(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.ltb
// Variant: uncurried
pub fn ltb_2(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::lt(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.shiftl
// Variant: uncurried
pub fn shiftl(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::shiftl(v0, v1)
}

// Rocq: Timing.timing_implem.dlt
// Variant: uncurried
pub fn dlt(x: Rc<BigInt>, a: Rc<BigInt>, y: Rc<BigInt>, b: Rc<BigInt>) -> bool {
  let a_clone = Rc::clone(&a);
  let b_clone = Rc::clone(&b);
  if leb_1(a_clone, b_clone) {
    let tmp = sub(b, a);
    let tmp_1 = shiftl(y, tmp);
    ltb_2(x, tmp_1)
  } else {
    let tmp_2 = sub(a, b);
    let tmp_3 = shiftl(x, tmp_2);
    ltb_2(tmp_3, y)
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
          let tmp_2 = rocq_bigint::one();
          let tmp_3 = rocq_bigint::identity(tmp_2);
          let tmp_4 = rocq_bigint::one();
          let tmp_5 = rocq_bigint::twice(tmp_4);
          let tmp_6 = rocq_bigint::twice_plus_one(tmp_5);
          let tmp_7 = rocq_bigint::twice(tmp_6);
          let tmp_8 = rocq_bigint::twice(tmp_7);
          let tmp_9 = rocq_bigint::neg(tmp_8);
          let eb_clone = Rc::clone(eb);
          let mb_clone = Rc::clone(mb);
          let tmp_10 = dlt(eb_clone, mb_clone, tmp_3, tmp_9);
          let tmp_11 = rocq_bigint::one();
          let tmp_12 = rocq_bigint::twice(tmp_11);
          let tmp_13 = rocq_bigint::twice(tmp_12);
          let tmp_14 = rocq_bigint::twice(tmp_13);
          let tmp_15 = rocq_bigint::twice(tmp_14);
          let tmp_16 = rocq_bigint::twice(tmp_15);
          let tmp_17 = rocq_bigint::twice(tmp_16);
          let tmp_18 = rocq_bigint::twice(tmp_17);
          let tmp_19 = rocq_bigint::twice(tmp_18);
          let tmp_20 = rocq_bigint::twice(tmp_19);
          let tmp_21 = rocq_bigint::twice(tmp_20);
          let tmp_22 = rocq_bigint::twice(tmp_21);
          let tmp_23 = rocq_bigint::twice(tmp_22);
          let tmp_24 = rocq_bigint::twice(tmp_23);
          let tmp_25 = rocq_bigint::twice(tmp_24);
          let tmp_26 = rocq_bigint::twice(tmp_25);
          let tmp_27 = rocq_bigint::twice(tmp_26);
          let tmp_28 = rocq_bigint::twice(tmp_27);
          let tmp_29 = rocq_bigint::twice(tmp_28);
          let tmp_30 = rocq_bigint::twice(tmp_29);
          let tmp_31 = rocq_bigint::twice_plus_one(tmp_30);
          let tmp_32 = rocq_bigint::identity(tmp_31);
          let tmp_33 = mul_2(v7, tmp_32);
          orb(tmp_10, dlt(tmp_33, v9, v18, v20))
        },
      }
    },
  }
}

// Rocq: Timing.timing_implem.PP
pub fn PP(_v0: ()) -> Rc<BigInt> {
  let tmp = rocq_bigint::one();
  let tmp_1 = rocq_bigint::twice_plus_one(tmp);
  let tmp_2 = rocq_bigint::twice(tmp_1);
  let tmp_3 = rocq_bigint::twice(tmp_2);
  let tmp_4 = rocq_bigint::twice(tmp_3);
  let tmp_5 = rocq_bigint::twice(tmp_4);
  let tmp_6 = rocq_bigint::twice(tmp_5);
  rocq_bigint::identity(tmp_6)
}

// Rocq: Timing.timing_implem.fixv
pub fn fixv(f: f64) -> Rc<BigInt> {
  let d = fex(f);
  let d_clone = Clone::clone(&d);
  let tmp = fst::<Rc<BigInt>, Rc<BigInt>>(d_clone);
  let tmp_1 = snd::<Rc<BigInt>, Rc<BigInt>>(d);
  let tmp_2 = PP(());
  let tmp_3 = add(tmp_1, tmp_2);
  shiftl(tmp, tmp_3)
}

// Rocq: Timing.timing_implem.link_step
// Variant: uncurried
pub fn link_step(m: u64, xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, xf: Rc<Array<f64>>, l: u64, A: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let s = rocq_array::get::<u64>(&xs, l);
  std::mem::drop(xs);
  let d = rocq_array::get::<u64>(&xd, l);
  std::mem::drop(xd);
  let tmp = rocq_array::get::<f64>(&xf, l);
  std::mem::drop(xf);
  let F = fixv(tmp);
  let tmp_1 = add_1(mul_1(d, m), s);
  let tmp_2 = rocq_array::get::<Rc<BigInt>>(&A, add_1(mul_1(d, m), s));
  let F_clone = Rc::clone(&F);
  let tmp_3 = add(tmp_2, F_clone);
  let A1 = rocq_array::set::<Rc<BigInt>>(A, tmp_1, tmp_3);
  let tmp_4 = add_1(mul_1(s, m), s);
  let tmp_5 = rocq_array::get::<Rc<BigInt>>(&A1, add_1(mul_1(s, m), s));
  let tmp_6 = sub(tmp_5, F);
  rocq_array::set::<Rc<BigInt>>(A1, tmp_4, tmp_6)
}

// Rocq: Timing.timing_implem.build
// Variant: uncurried
pub fn build(len: u64, f: Rc<dyn Fn(u64) -> Rc<BigInt>>) -> Rc<Array<Rc<BigInt>>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new({
    move |k: u64, a: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let f = &f;
      let tmp = f(k);
      rocq_array::set::<Rc<BigInt>>(a, k, tmp)
    }
  });
  let tmp_1 = rocq_bigint::zero();
  let tmp_2 = rocq_array::make::<Rc<BigInt>>(len, tmp_1);
  loop_::<Rc<Array<Rc<BigInt>>>>(len, callback, 0u64, tmp_2)
}

// Rocq: Timing.timing_implem.ONE
pub fn ONE(_v0: ()) -> Rc<BigInt> {
  let tmp = rocq_bigint::one();
  let tmp_1 = rocq_bigint::identity(tmp);
  let tmp_2 = PP(());
  shiftl(tmp_1, tmp_2)
}

// Rocq: Timing.timing_implem.ident
pub fn ident(m: u64) -> Rc<Array<Rc<BigInt>>> {
  let tmp = mul_1(m, m);
  let callback: Rc<dyn Fn(u64) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_11 = m;
    move |k: u64| -> Rc<BigInt> {
      let m = &__anf_capture_11;
      let tmp_1 = div(k, Clone::clone(m));
      let tmp_2 = mod_(k, Clone::clone(m));
      if eqb(tmp_1, tmp_2) {
        ONE(())
      } else {
        rocq_bigint::zero()
      }
    }
  });
  build(tmp, callback)
}

// Rocq: Timing.timing_implem.amat
// Variant: uncurried
pub fn amat(m: u64, L: u64, xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, xf: Rc<Array<f64>>) -> Rc<Array<Rc<BigInt>>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new({
    let __anf_capture_15 = m;
    move |v23: u64, v24: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let tmp = Clone::clone(&__anf_capture_15);
      let xs_clone = Rc::clone(&xs);
      let xd_clone = Rc::clone(&xd);
      let xf_clone = Rc::clone(&xf);
      link_step(tmp, xs_clone, xd_clone, xf_clone, v23, v24)
    }
  });
  let tmp_1 = ident(m);
  loop_::<Rc<Array<Rc<BigInt>>>>(L, callback, 0u64, tmp_1)
}

// Rocq: Timing.timing_implem.splitb
pub fn splitb(s: u64) -> bool {
  andb(ltb(__rocq_global_1401, s), eqb(mod_(s, 2u64), 0u64))
}

// Rocq: Timing.timing_implem.quad
// Variant: uncurried
pub fn quad(X: Rc<Array<Rc<BigInt>>>, s: u64, h: u64, di: u64, dj: u64) -> Rc<Array<Rc<BigInt>>> {
  let tmp = mul_1(h, h);
  let callback: Rc<dyn Fn(u64) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_27 = h;
    move |k: u64| -> Rc<BigInt> {
      let di = &di;
      let s = &s;
      let h = &__anf_capture_27;
      let dj = &dj;
      let X = &X;
      let tmp_1 = div(k, Clone::clone(h));
      let tmp_2 = mul_1(add_1(Clone::clone(di), tmp_1), Clone::clone(s));
      let tmp_3 = mod_(k, Clone::clone(h));
      let tmp_4 = add_1(Clone::clone(dj), tmp_3);
      let tmp_5 = add_1(tmp_2, tmp_4);
      rocq_array::get::<Rc<BigInt>>(X, tmp_5)
    }
  });
  build(tmp, callback)
}

// Rocq: Timing.timing_implem.madd
// Variant: uncurried
pub fn madd(h: u64, A: Rc<Array<Rc<BigInt>>>, B: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let tmp = mul_1(h, h);
  let callback: Rc<dyn Fn(u64) -> Rc<BigInt>> = Rc::new({
    move |k: u64| -> Rc<BigInt> {
      let A = &A;
      let B = &B;
      let tmp_1 = rocq_array::get::<Rc<BigInt>>(A, k);
      let tmp_2 = rocq_array::get::<Rc<BigInt>>(B, k);
      add(tmp_1, tmp_2)
    }
  });
  build(tmp, callback)
}

// Rocq: Timing.timing_implem.msub
// Variant: uncurried
pub fn msub(h: u64, A: Rc<Array<Rc<BigInt>>>, B: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let tmp = mul_1(h, h);
  let callback: Rc<dyn Fn(u64) -> Rc<BigInt>> = Rc::new({
    move |k: u64| -> Rc<BigInt> {
      let A = &A;
      let B = &B;
      let tmp_1 = rocq_array::get::<Rc<BigInt>>(A, k);
      let tmp_2 = rocq_array::get::<Rc<BigInt>>(B, k);
      sub(tmp_1, tmp_2)
    }
  });
  build(tmp, callback)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub_2(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Timing.timing_implem.comb
// Variant: uncurried
pub fn comb(s: u64, h: u64, C11: Rc<Array<Rc<BigInt>>>, C12: Rc<Array<Rc<BigInt>>>, C21: Rc<Array<Rc<BigInt>>>, C22: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let tmp = mul_1(s, s);
  let callback: Rc<dyn Fn(u64) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_26 = s;
    move |k: u64| -> Rc<BigInt> {
      let s = &__anf_capture_26;
      let C11 = &C11;
      let C12 = &C12;
      let C21 = &C21;
      let h = &h;
      let C22 = &C22;
      let i = div(k, Clone::clone(s));
      let j = mod_(k, Clone::clone(s));
      let h_clone = Clone::clone(h);
      if ltb(i, h_clone) {
        let h_clone_1 = Clone::clone(h);
        if ltb(j, h_clone_1) {
          let tmp_1 = add_1(mul_1(i, Clone::clone(h)), j);
          rocq_array::get::<Rc<BigInt>>(C11, tmp_1)
        } else {
          let tmp_2 = add_1(mul_1(i, Clone::clone(h)), sub_2(j, Clone::clone(h)));
          rocq_array::get::<Rc<BigInt>>(C12, tmp_2)
        }
      } else {
        let h_clone_2 = Clone::clone(h);
        if ltb(j, h_clone_2) {
          let tmp_3 = add_1(mul_1(sub_2(i, Clone::clone(h)), Clone::clone(h)), j);
          rocq_array::get::<Rc<BigInt>>(C21, tmp_3)
        } else {
          let tmp_4 = add_1(mul_1(sub_2(i, Clone::clone(h)), Clone::clone(h)), sub_2(j, Clone::clone(h)));
          rocq_array::get::<Rc<BigInt>>(C22, tmp_4)
        }
      }
    }
  });
  build(tmp, callback)
}

// Rocq: Timing.timing_implem.dot
// Variant: borrowed, uncurried
pub fn dot(s: u64, X: &Rc<Array<Rc<BigInt>>>, Y: &Rc<Array<Rc<BigInt>>>, i: u64, j: u64) -> Rc<BigInt> {
  let X_clone = Rc::clone(X);
  let Y_clone = Rc::clone(Y);
  let callback: Rc<dyn Fn(u64, Rc<BigInt>) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_26 = s;
    move |k: u64, acc: Rc<BigInt>| -> Rc<BigInt> {
      let i = &i;
      let X = &X_clone;
      let s = &__anf_capture_26;
      let j = &j;
      let Y = &Y_clone;
      let tmp = rocq_array::get::<Rc<BigInt>>(X, add_1(mul_1(Clone::clone(i), Clone::clone(s)), k));
      let tmp_1 = rocq_array::get::<Rc<BigInt>>(Y, add_1(mul_1(k, Clone::clone(s)), Clone::clone(j)));
      let tmp_2 = mul_2(tmp, tmp_1);
      add(acc, tmp_2)
    }
  });
  let tmp_3 = rocq_bigint::zero();
  loop_::<Rc<BigInt>>(s, callback, 0u64, tmp_3)
}

// Rocq: Timing.timing_implem.naive
// Variant: uncurried
pub fn naive(s: u64, X: Rc<Array<Rc<BigInt>>>, Y: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let tmp = mul_1(s, s);
  let callback: Rc<dyn Fn(u64) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_17 = s;
    move |k: u64| -> Rc<BigInt> {
      let s = &__anf_capture_17;
      let X = &X;
      let Y = &Y;
      let tmp_1 = div(k, Clone::clone(s));
      let tmp_2 = mod_(k, Clone::clone(s));
      let s_clone = Clone::clone(s);
      dot(s_clone, X, Y, tmp_1, tmp_2)
    }
  });
  build(tmp, callback)
}

// Rocq: Timing.timing_implem.strass
// Variant: uncurried
pub fn strass_1(s: u64, X: Rc<Array<Rc<BigInt>>>, Y: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  strass(s, X, Y, ())
}

// Rocq: Timing.timing_implem.strass (local: strass)
// Variant: uncurried, lifted
pub fn strass(s: u64, X: Rc<Array<Rc<BigInt>>>, Y: Rc<Array<Rc<BigInt>>>, _H: ()) -> Rc<Array<Rc<BigInt>>> {
  let tmp = splitb(s);
  match bdec(tmp) {
    sumbool::left => {
      let h = div(s, 2u64);
      let sr: Rc<dyn Fn(Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new({
        let __anf_capture_24 = h;
        move |A: Rc<Array<Rc<BigInt>>>, B: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
          let tmp_1 = Clone::clone(&__anf_capture_24);
          strass(tmp_1, A, B, ())
        }
      });
      let X_clone = Rc::clone(&X);
      let A11 = quad(X_clone, s, h, 0u64, 0u64);
      let X_clone_1 = Rc::clone(&X);
      let A12 = quad(X_clone_1, s, h, 0u64, h);
      let X_clone_2 = Rc::clone(&X);
      let A21 = quad(X_clone_2, s, h, h, 0u64);
      let A22 = quad(X, s, h, h, h);
      let Y_clone = Rc::clone(&Y);
      let B11 = quad(Y_clone, s, h, 0u64, 0u64);
      let Y_clone_1 = Rc::clone(&Y);
      let B12 = quad(Y_clone_1, s, h, 0u64, h);
      let Y_clone_2 = Rc::clone(&Y);
      let B21 = quad(Y_clone_2, s, h, h, 0u64);
      let B22 = quad(Y, s, h, h, h);
      let A11_clone = Rc::clone(&A11);
      let A22_clone = Rc::clone(&A22);
      let tmp_2 = madd(h, A11_clone, A22_clone);
      let B11_clone = Rc::clone(&B11);
      let B22_clone = Rc::clone(&B22);
      let tmp_3 = madd(h, B11_clone, B22_clone);
      let sr_ref: &Rc<dyn Fn(Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = &sr;
      let M1 = sr_ref(tmp_2, tmp_3);
      let A21_clone = Rc::clone(&A21);
      let A22_clone_1 = Rc::clone(&A22);
      let tmp_4 = madd(h, A21_clone, A22_clone_1);
      let sr_ref_1: &Rc<dyn Fn(Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = &sr;
      let B11_clone_1 = Rc::clone(&B11);
      let M2 = sr_ref_1(tmp_4, B11_clone_1);
      let B12_clone = Rc::clone(&B12);
      let B22_clone_1 = Rc::clone(&B22);
      let tmp_5 = msub(h, B12_clone, B22_clone_1);
      let sr_ref_2: &Rc<dyn Fn(Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = &sr;
      let A11_clone_1 = Rc::clone(&A11);
      let M3 = sr_ref_2(A11_clone_1, tmp_5);
      let B21_clone = Rc::clone(&B21);
      let B11_clone_2 = Rc::clone(&B11);
      let tmp_6 = msub(h, B21_clone, B11_clone_2);
      let sr_ref_3: &Rc<dyn Fn(Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = &sr;
      let A22_clone_2 = Rc::clone(&A22);
      let M4 = sr_ref_3(A22_clone_2, tmp_6);
      let A11_clone_2 = Rc::clone(&A11);
      let A12_clone = Rc::clone(&A12);
      let tmp_7 = madd(h, A11_clone_2, A12_clone);
      let sr_ref_4: &Rc<dyn Fn(Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = &sr;
      let B22_clone_2 = Rc::clone(&B22);
      let M5 = sr_ref_4(tmp_7, B22_clone_2);
      let tmp_8 = msub(h, A21, A11);
      let tmp_9 = madd(h, B11, B12);
      let sr_ref_5: &Rc<dyn Fn(Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = &sr;
      let M6 = sr_ref_5(tmp_8, tmp_9);
      let tmp_10 = msub(h, A12, A22);
      let tmp_11 = madd(h, B21, B22);
      let sr_ref_6: &Rc<dyn Fn(Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = &sr;
      let M7 = sr_ref_6(tmp_10, tmp_11);
      std::mem::drop(sr);
      let M1_clone = Rc::clone(&M1);
      let M4_clone = Rc::clone(&M4);
      let tmp_12 = madd(h, M1_clone, M4_clone);
      let M5_clone = Rc::clone(&M5);
      let tmp_13 = msub(h, tmp_12, M5_clone);
      let tmp_14 = madd(h, tmp_13, M7);
      let M3_clone = Rc::clone(&M3);
      let tmp_15 = madd(h, M3_clone, M5);
      let M2_clone = Rc::clone(&M2);
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

// Rocq: Corelib.BinNums.IntDef.Z.shiftr
// Variant: uncurried
pub fn shiftr(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::shiftr(v0, v1)
}

// Rocq: Timing.timing_implem.mulr
// Variant: uncurried
pub fn mulr(m: u64, X: Rc<Array<Rc<BigInt>>>, Y: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let C = strass_1(m, X, Y);
  let tmp = mul_1(m, m);
  let callback: Rc<dyn Fn(u64) -> Rc<BigInt>> = Rc::new({
    move |k: u64| -> Rc<BigInt> {
      let tmp_1 = rocq_array::get::<Rc<BigInt>>(&C, k);
      let tmp_2 = PP(());
      shiftr(tmp_1, tmp_2)
    }
  });
  build(tmp, callback)
}

// Rocq: Timing.timing_implem.pw
// Variant: uncurried
pub fn pw_1(m: u64, t: u64, R: Rc<option<Rc<Array<Rc<BigInt>>>>>, B: Rc<Array<Rc<BigInt>>>) -> Rc<option<Rc<Array<Rc<BigInt>>>>> {
  pw(m, t, R, B, ())
}

// Rocq: Timing.timing_implem.pw (local: pw)
// Variant: uncurried, lifted
pub fn pw(m: u64, t: u64, R: Rc<option<Rc<Array<Rc<BigInt>>>>>, B: Rc<Array<Rc<BigInt>>>, _H: ()) -> Rc<option<Rc<Array<Rc<BigInt>>>>> {
  let tmp = eqb(t, 0u64);
  match bdec(tmp) {
    sumbool::left => {
      std::mem::drop(B);
      R
    },
    sumbool::right => {
      let tmp_1 = mod_(t, 2u64);
      let tmp_2 = 0u64;
      let R_ = if eqb(tmp_1, tmp_2) {
        R
      } else {
        let tmp_3 = match &*R {
          option::Some(X) => {
            let X_clone = Rc::clone(X);
            std::mem::drop(R);
            let B_clone = Rc::clone(&B);
            mulr(m, X_clone, B_clone)
          },
          option::None => {
            std::mem::drop(R);
            Rc::clone(&B)
          },
        };
        Rc::new(option::<Rc<Array<Rc<BigInt>>>>::Some(tmp_3))
      };
      let t_ = div(t, 2u64);
      if eqb(t_, 0u64) {
        std::mem::drop(B);
        R_
      } else {
        let B_clone_1 = Rc::clone(&B);
        let tmp_4 = mulr(m, B_clone_1, B);
        pw(m, t_, R_, tmp_4, ())
      }
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.min
// Variant: uncurried
pub fn min(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::min(v0, v1)
}

// Rocq: Timing.timing_implem.faced_z
// Variant: uncurried
pub fn faced_z_owned(n: u64, adj: Rc<Array<bool>>, v: Rc<Array<Rc<BigInt>>>, i: u64) -> Rc<BigInt> {
  let tmp = rocq_array::get::<Rc<BigInt>>(&v, i);
  let callback: Rc<dyn Fn(u64, Rc<BigInt>) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_19 = i;
    let __anf_capture_21 = n;
    let __anf_capture_25 = v;
    move |k: u64, acc: Rc<BigInt>| -> Rc<BigInt> {
      let i = &__anf_capture_19;
      let n = &__anf_capture_21;
      let adj = &adj;
      let v = &__anf_capture_25;
      let tmp_1 = add_1(mul_1(Clone::clone(i), Clone::clone(n)), k);
      if rocq_array::get::<bool>(adj, tmp_1) {
        let tmp_2 = rocq_array::get::<Rc<BigInt>>(v, k);
        add(acc, tmp_2)
      } else {
        acc
      }
    }
  });
  let tmp_3 = rocq_bigint::zero();
  let tmp_4 = loop_::<Rc<BigInt>>(n, callback, 0u64, tmp_3);
  add(tmp, tmp_4)
}

// Rocq: Timing.timing_implem.faced_z
// Variant: borrowed, uncurried
pub fn faced_z(n: u64, adj: &Rc<Array<bool>>, v: &Rc<Array<Rc<BigInt>>>, i: u64) -> Rc<BigInt> {
  let tmp = rocq_array::get::<Rc<BigInt>>(v, i);
  let adj_clone = Rc::clone(adj);
  let v_clone = Rc::clone(v);
  let callback: Rc<dyn Fn(u64, Rc<BigInt>) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_23 = i;
    let __anf_capture_25 = n;
    move |k: u64, acc: Rc<BigInt>| -> Rc<BigInt> {
      let i = &__anf_capture_23;
      let n = &__anf_capture_25;
      let adj = &adj_clone;
      let v = &v_clone;
      let tmp_1 = add_1(mul_1(Clone::clone(i), Clone::clone(n)), k);
      if rocq_array::get::<bool>(adj, tmp_1) {
        let tmp_2 = rocq_array::get::<Rc<BigInt>>(v, k);
        add(acc, tmp_2)
      } else {
        acc
      }
    }
  });
  let tmp_3 = rocq_bigint::zero();
  let tmp_4 = loop_::<Rc<BigInt>>(n, callback, 0u64, tmp_3);
  add(tmp, tmp_4)
}

// Rocq: Corelib.Floats.PrimFloat.opp
pub fn opp_1(v0: f64) -> f64 {
  rocq_float64::opp(v0)
}

// Rocq: Corelib.Floats.PrimFloat.div
// Variant: uncurried
pub fn div_1(v0: f64, v1: f64) -> f64 {
  rocq_float64::div(v0, v1)
}

// Rocq: Timing.timing_implem.iofp
pub fn iofp_1(p: Rc<BigInt>) -> u64 {
  iofp(p)
}

// Rocq: Timing.timing_implem.iofp (local: iofp)
// Variant: lifted
pub fn iofp(p: Rc<BigInt>) -> u64 {
  let p_clone = Rc::clone(&p);
  match rocq_bigint::positive_tag(p_clone) {
    rocq_bigint::PositiveTag::Odd => {
      let q = rocq_bigint::positive_tail(p);
      add_1(mul_1(2u64, iofp(q)), 1u64)
    },
    rocq_bigint::PositiveTag::Even => {
      let q = rocq_bigint::positive_tail(p);
      mul_1(2u64, iofp(q))
    },
    rocq_bigint::PositiveTag::One => {
      std::mem::drop(p);
      1u64
    },
  }
}

// Rocq: Timing.timing_implem.iofz
pub fn iofz(z: Rc<BigInt>) -> u64 {
  let z_clone = Rc::clone(&z);
  match rocq_bigint::integer_tag(z_clone) {
    rocq_bigint::IntegerTag::Zero => {
      std::mem::drop(z);
      0u64
    },
    rocq_bigint::IntegerTag::Positive => {
      let p = rocq_bigint::integer_magnitude(z);
      iofp_1(p)
    },
    rocq_bigint::IntegerTag::Negative => {
      let p = rocq_bigint::integer_magnitude(z);
      std::mem::drop(p);
      0u64
    },
  }
}

// Rocq: Timing.timing_implem.cv
pub fn cv(z: Rc<BigInt>) -> f64 {
  let tmp = rocq_bigint::one();
  let tmp_1 = rocq_bigint::twice(tmp);
  let tmp_2 = rocq_bigint::identity(tmp_1);
  let tmp_3 = PP(());
  let tmp_4 = mul_2(tmp_2, tmp_3);
  let tmp_5 = rocq_bigint::one();
  let tmp_6 = rocq_bigint::twice_plus_one(tmp_5);
  let tmp_7 = rocq_bigint::twice_plus_one(tmp_6);
  let tmp_8 = rocq_bigint::twice_plus_one(tmp_7);
  let tmp_9 = rocq_bigint::twice(tmp_8);
  let tmp_10 = rocq_bigint::identity(tmp_9);
  let tmp_11 = sub(tmp_4, tmp_10);
  let tmp_12 = shiftr(z, tmp_11);
  div_1(of_uint63(iofz(tmp_12)), of_uint63(1073741824u64))
}

// Rocq: Timing.timing_implem.conv
pub fn conv(z: Rc<BigInt>) -> f64 {
  let tmp = rocq_bigint::zero();
  let z_clone = Rc::clone(&z);
  if ltb_2(z_clone, tmp) {
    let tmp_1 = opp(z);
    opp_1(cv(tmp_1))
  } else {
    cv(z)
  }
}

// Rocq: Timing.timing_implem.timing_exact
// Variant: uncurried
pub fn timing_exact(xt: u64, xu: Rc<Array<f64>>, xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, xf: Rc<Array<f64>>) -> f64 {
  let n = rocq_array::length::<f64>(&xu);
  let L = rocq_array::length::<u64>(&xs);
  let m = mul_1(div(add_1(n, 7u64), 8u64), 8u64);
  let xs_clone = Rc::clone(&xs);
  let xd_clone = Rc::clone(&xd);
  let A = amat(m, L, xs_clone, xd_clone, xf);
  let tmp = pw_1(m, xt, Rc::new(option::<Rc<Array<Rc<BigInt>>>>::None), A);
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
  let callback: Rc<dyn Fn(u64) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_83 = n;
    let __anf_capture_85 = xu;
    move |s: u64| -> Rc<BigInt> {
      let n = &__anf_capture_83;
      let xu = &__anf_capture_85;
      let n_clone = Clone::clone(n);
      if ltb(s, n_clone) {
        let tmp_1 = rocq_array::get::<f64>(xu, s);
        fixv(tmp_1)
      } else {
        rocq_bigint::zero()
      }
    }
  });
  let uh = build(m, callback);
  let callback_1: Rc<dyn Fn(u64) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_129 = m;
    move |i: u64| -> Rc<BigInt> {
      let Rf = &Rf;
      let uh = &uh;
      let m = &__anf_capture_129;
      let m_clone = Clone::clone(m);
      let Rf_clone = Rc::clone(Rf);
      let uh_clone = Rc::clone(uh);
      let callback_2: Rc<dyn Fn(u64, Rc<BigInt>) -> Rc<BigInt>> = Rc::new({
        move |k: u64, acc: Rc<BigInt>| -> Rc<BigInt> {
          let i = &i;
          let m = &m_clone;
          let Rf = &Rf_clone;
          let uh = &uh_clone;
          let tmp_2 = rocq_array::get::<Rc<BigInt>>(Rf, add_1(mul_1(Clone::clone(i), Clone::clone(m)), k));
          let tmp_3 = rocq_array::get::<Rc<BigInt>>(uh, k);
          let tmp_4 = mul_2(tmp_2, tmp_3);
          add(acc, tmp_4)
        }
      });
      let tmp_5 = rocq_bigint::zero();
      let m_clone_1 = Clone::clone(m);
      loop_::<Rc<BigInt>>(m_clone_1, callback_2, 0u64, tmp_5)
    }
  });
  let v = build(m, callback_1);
  let callback_3: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new({
    let __anf_capture_215 = n;
    let __anf_capture_217 = xs;
    let __anf_capture_219 = xd;
    move |v221: u64, v222: Rc<Array<bool>>| -> Rc<Array<bool>> {
      let tmp_6 = Clone::clone(&__anf_capture_215);
      let tmp_7 = Rc::clone(&__anf_capture_217);
      let tmp_8 = Rc::clone(&__anf_capture_219);
      adj_step(tmp_6, tmp_7, tmp_8, v221, v222)
    }
  });
  let tmp_9 = rocq_array::make::<bool>(mul_1(n, n), false);
  let adj = loop_::<Rc<Array<bool>>>(L, callback_3, 0u64, tmp_9);
  let adj_clone = Rc::clone(&adj);
  let v_clone = Rc::clone(&v);
  let callback_4: Rc<dyn Fn(u64, Rc<BigInt>) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_273 = n;
    move |i: u64, b: Rc<BigInt>| -> Rc<BigInt> {
      let tmp_10 = faced_z(Clone::clone(&__anf_capture_273), &adj_clone, &v_clone, i);
      min(b, tmp_10)
    }
  });
  let tmp_11 = faced_z_owned(n, adj, v, 0u64);
  let best = loop_::<Rc<BigInt>>(n, callback_4, 1u64, tmp_11);
  conv(best)
}

// Rocq: Timing.timing_implem.timing_impl
// Variant: uncurried
pub fn timing_impl(xt: u64, xu: Rc<Array<f64>>, xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, xf: Rc<Array<f64>>) -> f64 {
  let n = rocq_array::length::<f64>(&xu);
  let L = rocq_array::length::<u64>(&xs);
  let xs_clone = Rc::clone(&xs);
  let xd_clone = Rc::clone(&xd);
  let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
    move |v21: u64, v22: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let tmp = Rc::clone(&xs_clone);
      let tmp_1 = Rc::clone(&xd_clone);
      cnt_step(tmp, tmp_1, v21, v22)
    }
  });
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  let c = loop_::<Rc<Array<u64>>>(L, callback, 0u64, tmp_2);
  let xs_clone_1 = Rc::clone(&xs);
  let xd_clone_1 = Rc::clone(&xd);
  let xf_clone = Rc::clone(&xf);
  let callback_1: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new({
    move |v72: u64, v73: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let tmp_3 = Rc::clone(&xs_clone_1);
      let tmp_4 = Rc::clone(&xd_clone_1);
      let tmp_5 = Rc::clone(&xf_clone);
      out_step(tmp_3, tmp_4, tmp_5, v72, v73)
    }
  });
  let tmp_6 = rocq_array::make::<f64>(n, f64::from_bits(0u64));
  let ou = loop_::<Rc<Array<f64>>>(L, callback_1, 0u64, tmp_6);
  let xs_clone_2 = Rc::clone(&xs);
  let xd_clone_2 = Rc::clone(&xd);
  let xf_clone_1 = Rc::clone(&xf);
  let ou_clone = Rc::clone(&ou);
  let c_clone = Rc::clone(&c);
  let callback_2: Rc<dyn Fn(u64, ((Rc<Array<f64>>, Rc<Array<f64>>), bool)) -> ((Rc<Array<f64>>, Rc<Array<f64>>), bool)> = Rc::new({
    let __anf_capture_129 = n;
    let __anf_capture_131 = L;
    move |v143: u64, v144: ((Rc<Array<f64>>, Rc<Array<f64>>), bool)| -> ((Rc<Array<f64>>, Rc<Array<f64>>), bool) {
      let n = &__anf_capture_129;
      let L = &__anf_capture_131;
      let xs = &xs_clone_2;
      let xd = &xd_clone_2;
      let xf = &xf_clone_1;
      let ou = &ou_clone;
      let c = &c_clone;
      let tmp_7 = tstep(Clone::clone(n), Clone::clone(L), xs, xd, xf, ou, c, v143, v144);
      tmp_7
    }
  });
  let tmp_8 = rocq_array::make::<f64>(n, f64::from_bits(0u64));
  let xu_clone = Rc::clone(&xu);
  let tmp_9 = loop_::<((Rc<Array<f64>>, Rc<Array<f64>>), bool)>(xt, callback_2, 0u64, ((xu_clone, tmp_8), true));
  match tmp_9 {
    (v198, v200) => {
      let p = &v200;
      match v198 {
        (v204, v206) => {
          let e = &v204;
          let v = &v206;
          if *p {
            let xs_clone_3 = Rc::clone(&xs);
            let xd_clone_3 = Rc::clone(&xd);
            let callback_3: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new({
              let __anf_capture_221 = n;
              move |v227: u64, v228: Rc<Array<bool>>| -> Rc<Array<bool>> {
                let tmp_10 = Clone::clone(&__anf_capture_221);
                let tmp_11 = Rc::clone(&xs_clone_3);
                let tmp_12 = Rc::clone(&xd_clone_3);
                adj_step(tmp_10, tmp_11, tmp_12, v227, v228)
              }
            });
            let tmp_13 = rocq_array::make::<bool>(mul_1(n, n), false);
            let adj = loop_::<Rc<Array<bool>>>(L, callback_3, 0u64, tmp_13);
            let adj_clone = Rc::clone(&adj);
            let e_clone = Rc::clone(e);
            let callback_4: Rc<dyn Fn(u64, f64) -> f64> = Rc::new({
              let __anf_capture_278 = n;
              move |i: u64, b: f64| -> f64 {
                let tmp_14 = faced_f(Clone::clone(&__anf_capture_278), &adj_clone, &e_clone, i);
                fmin(b, tmp_14)
              }
            });
            let adj_clone_1 = Rc::clone(&adj);
            let e_clone_1 = Rc::clone(e);
            let tmp_15 = faced_f_owned(n, adj_clone_1, e_clone_1, 0u64);
            let o = loop_::<f64>(n, callback_4, 1u64, tmp_15);
            let nu = mul(of_uint63(add_1(n, 1u64)), __rocq_global_419);
            let adj_clone_2 = Rc::clone(&adj);
            let e_clone_2 = Rc::clone(e);
            let v_clone = Rc::clone(v);
            let callback_5: Rc<dyn Fn(u64) -> f64> = Rc::new({
              let __anf_capture_360 = n;
              move |v370: u64| -> f64 {
                let n = &__anf_capture_360;
                let adj = &adj_clone_2;
                let e = &e_clone_2;
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
const __rocq_global_416: f64 = f64::from_bits(4607182418804211712u64);
const __rocq_global_419: f64 = f64::from_bits(4372995238176751616u64);
const __rocq_global_444: f64 = f64::from_bits(4472074429978902528u64);
const __rocq_global_1401: u64 = 16u64;