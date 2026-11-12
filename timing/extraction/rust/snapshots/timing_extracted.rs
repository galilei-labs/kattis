// Generated from OwnedANF. This printer is not verified.
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

// Rocq: Timing.timing_implem.timing
// Variant: uncurried
pub fn timing() -> Rc<dyn Fn(u64, Rc<Array<f64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<f64>>) -> f64> {
  let v0: fn(u64, Rc<Array<f64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<f64>>) -> f64 = timing_impl;
  let v1: Rc<dyn Fn(u64, Rc<Array<f64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<f64>>) -> f64> = Rc::new(v0);
  v1
}

// Rocq: Timing.timing_implem.timing
pub fn timing_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<f64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<f64>>) -> f64>>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<f64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<f64>>) -> f64>>>> = timing_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<f64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<f64>>) -> f64>>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.BinNums.IntDef.Z.add
// Variant: uncurried
pub fn add(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::add(v0, v1);
  v8
}

// Rocq: Corelib.BinNums.IntDef.Z.opp
pub fn opp(v0: Rc<BigInt>) -> Rc<BigInt> {
  let v5 = rocq_bigint::neg(v0);
  v5
}

// Rocq: Corelib.BinNums.IntDef.Z.sub
// Variant: uncurried
pub fn sub(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::sub(v0, v1);
  v8
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
  match b {
    true => {
      sumbool::left
    },
    false => {
      sumbool::right
    },
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
  let v12 = ltb(i, hi);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add_1(i, 1u64);
      let v24: &Rc<dyn Fn(u64, St) -> St> = &f;
      let v29 = v24(i, s);
      wloop::<St>(hi, f, v23, v29, ())
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
  let v4 = &xs;
  let s = rocq_array::get::<u64>(&v4, j);
  let v8 = &xd;
  let d = rocq_array::get::<u64>(&v8, j);
  match eqb(s, d) {
    true => {
      std::mem::drop(xs);
      std::mem::drop(xd);
      c
    },
    false => {
      std::mem::drop(xs);
      std::mem::drop(xd);
      let v22 = &c;
      let v25 = rocq_array::get::<u64>(&v22, s);
      let c1 = rocq_array::set::<u64>(c, s, add_1(v25, 1u64));
      let v41 = &c1;
      let v44 = rocq_array::get::<u64>(&v41, d);
      rocq_array::set::<u64>(c1, d, add_1(v44, 1u64))
    },
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
  let v5 = &xs;
  let s = rocq_array::get::<u64>(&v5, j);
  let v9 = &xd;
  let d = rocq_array::get::<u64>(&v9, j);
  match eqb(s, d) {
    true => {
      std::mem::drop(xs);
      std::mem::drop(xf);
      std::mem::drop(xd);
      o
    },
    false => {
      std::mem::drop(xs);
      std::mem::drop(xd);
      let v23 = &o;
      let v26 = rocq_array::get::<f64>(&v23, s);
      let v27 = &xf;
      let v30 = rocq_array::get::<f64>(&v27, j);
      std::mem::drop(xf);
      rocq_array::set::<f64>(o, s, add_2(v26, v30))
    },
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
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let v3 = Clone::clone((&(&p).1));
  std::mem::drop(p);
  v3
}

// Rocq: Timing.timing_implem.elink
// Variant: borrowed, uncurried
pub fn elink(xs: &Rc<Array<u64>>, xd: &Rc<Array<u64>>, xf: &Rc<Array<f64>>, v: &Rc<Array<f64>>, e: &Rc<Array<f64>>, j: u64, st: (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>) {
  let j_1 = j;
  let st_1 = st;
  let v9 = xs;
  let s = rocq_array::get::<u64>(&v9, j_1);
  let v13 = xd;
  let d = rocq_array::get::<u64>(&v13, j_1);
  match eqb(s, d) {
    true => {
      st_1
    },
    false => {
      let v28 = xf;
      let v31 = rocq_array::get::<f64>(&v28, j_1);
      let v32 = v;
      let a = abs(mul(v31, rocq_array::get::<f64>(&v32, s)));
      let v46 = Clone::clone(&st_1);
      let ein = fst::<Rc<Array<f64>>, Rc<Array<f64>>>(v46);
      let mac = snd::<Rc<Array<f64>>, Rc<Array<f64>>>(st_1);
      let v54 = &mac;
      let v58 = rocq_array::get::<f64>(&v54, d);
      let mac1 = rocq_array::set::<f64>(mac, d, add_2(v58, a));
      let v71 = &ein;
      let v74 = rocq_array::get::<f64>(&v71, d);
      let v76 = xf;
      let v79 = rocq_array::get::<f64>(&v76, j_1);
      let v80 = e;
      let v100 = rocq_array::set::<f64>(ein, d, add_2(v74, mul(v79, rocq_array::get::<f64>(&v80, s))));
      let v102 = &mac1;
      let v106 = rocq_array::get::<f64>(&v102, s);
      let v117 = rocq_array::set::<f64>(mac1, s, add_2(v106, a));
      (v100, v117)
    },
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
  let v8 = ou;
  add_2(abs(sub_1(f64::from_bits(4607182418800017408u64), rocq_array::get::<f64>(&v8, x_1))), __rocq_global_444)
}

// Rocq: Corelib.Floats.PrimFloat.of_uint63
pub fn of_uint63(v0: u64) -> f64 {
  rocq_float64::of_uint63(v0)
}

// Rocq: Timing.timing_implem.kx
// Variant: borrowed, uncurried
pub fn kx(c: &Rc<Array<u64>>, x: u64) -> f64 {
  let x_1 = x;
  let v7 = c;
  let v10 = rocq_array::get::<u64>(&v7, x_1);
  let v11 = c;
  let v19 = add_1(v10, rocq_array::get::<u64>(&v11, x_1));
  mul(of_uint63(add_1(v19, 3u64)), __rocq_global_419)
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
  let v19 = coef(ou, x_1);
  let v20 = e;
  let v28 = mul(v19, rocq_array::get::<f64>(&v20, x_1));
  let v29 = ein;
  let v37 = add_2(v28, rocq_array::get::<f64>(&v29, x_1));
  let v44 = kx(c, x_1);
  let v48 = v;
  let v54 = abs(rocq_array::get::<f64>(&v48, x_1));
  let v55 = mac;
  let v63 = add_2(v54, rocq_array::get::<f64>(&v55, x_1));
  let v70 = add_2(v63, f64::from_bits(4607182418800017408u64));
  let y = up(add_2(v37, mul(v44, v70)));
  let v86 = Clone::clone(&st_1);
  let v89 = fst::<Rc<Array<f64>>, bool>(v86);
  let v95 = rocq_array::set::<f64>(v89, x_1, y);
  (v95, andb(snd::<Rc<Array<f64>>, bool>(st_1), leb(y, f64::from_bits(4607182418800017408u64))))
}

// Rocq: Timing.timing_implem.ebound
// Variant: uncurried
pub fn ebound(n: u64, L: u64, xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, xf: Rc<Array<f64>>, ou: Rc<Array<f64>>, c: Rc<Array<u64>>, v: Rc<Array<f64>>, e: Rc<Array<f64>>) -> (Rc<Array<f64>>, bool) {
  let v18 = Rc::clone(&v);
  let v21 = Rc::clone(&e);
  let v22 = {
    move |v33: u64, v34: (Rc<Array<f64>>, Rc<Array<f64>>)| -> (Rc<Array<f64>>, Rc<Array<f64>>) {
      let xs = &xs;
      let xd = &xd;
      let xf = &xf;
      let v = &v18;
      let e = &v21;
      let v45 = elink(xs, xd, xf, v, e, v33, v34);
      v45
    }
  };
  let v48: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>)> = Rc::new(v22);
  let v58 = rocq_array::make::<f64>(n, f64::from_bits(0u64));
  let v65 = rocq_array::make::<f64>(n, f64::from_bits(0u64));
  let st = loop_::<(Rc<Array<f64>>, Rc<Array<f64>>)>(L, v48, 0u64, (v58, v65));
  let v84 = Clone::clone(&st);
  let v86 = fst::<Rc<Array<f64>>, Rc<Array<f64>>>(v84);
  let v90 = snd::<Rc<Array<f64>>, Rc<Array<f64>>>(st);
  let v103 = {
    let __anf_capture_108 = v;
    let __anf_capture_110 = e;
    move |v116: u64, v117: (Rc<Array<f64>>, bool)| -> (Rc<Array<f64>>, bool) {
      let ou = &ou;
      let c = &c;
      let v = &__anf_capture_108;
      let e = &__anf_capture_110;
      let v112 = &v86;
      let v114 = &v90;
      let v129 = efort(ou, c, v, e, v112, v114, v116, v117);
      v129
    }
  };
  let v132: Rc<dyn Fn(u64, (Rc<Array<f64>>, bool)) -> (Rc<Array<f64>>, bool)> = Rc::new(v103);
  let v142 = rocq_array::make::<f64>(n, f64::from_bits(0u64));
  loop_::<(Rc<Array<f64>>, bool)>(n, v132, 0u64, (v142, true))
}

// Rocq: Timing.timing_implem.link_f
// Variant: uncurried
pub fn link_f(xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, xf: Rc<Array<f64>>, v: Rc<Array<f64>>, j: u64, w: Rc<Array<f64>>) -> Rc<Array<f64>> {
  let v6 = &xs;
  let s = rocq_array::get::<u64>(&v6, j);
  let v10 = &xd;
  let d = rocq_array::get::<u64>(&v10, j);
  match eqb(s, d) {
    true => {
      std::mem::drop(xs);
      std::mem::drop(xf);
      std::mem::drop(v);
      std::mem::drop(xd);
      w
    },
    false => {
      std::mem::drop(xs);
      std::mem::drop(xd);
      let v24 = &xf;
      let v27 = rocq_array::get::<f64>(&v24, j);
      std::mem::drop(xf);
      let v28 = &v;
      let v31 = rocq_array::get::<f64>(&v28, s);
      std::mem::drop(v);
      let a = mul(v27, v31);
      let v38 = &w;
      let v42 = rocq_array::get::<f64>(&v38, d);
      let w1 = rocq_array::set::<f64>(w, d, add_2(v42, a));
      let v55 = &w1;
      let v59 = rocq_array::get::<f64>(&v55, s);
      rocq_array::set::<f64>(w1, s, sub_1(v59, a))
    },
  }
}

// Rocq: Timing.timing_implem.unit_f
// Variant: uncurried
pub fn unit_f(L: u64, xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, xf: Rc<Array<f64>>, v: Rc<Array<f64>>) -> Rc<Array<f64>> {
  let v14 = Rc::clone(&v);
  let v15 = {
    move |v24: u64, v25: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let v28 = Rc::clone(&xs);
      let v30 = Rc::clone(&xd);
      let v32 = Rc::clone(&xf);
      let v34 = Rc::clone(&v14);
      link_f(v28, v30, v32, v34, v24, v25)
    }
  };
  let v42: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new(v15);
  let v45 = 0u64;
  let v46 = &v;
  let v47 = rocq_array::copy::<f64>(&v46);
  std::mem::drop(v);
  loop_::<Rc<Array<f64>>>(L, v42, v45, v47)
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
          match p {
            true => {
              let v31 = Rc::clone(xs);
              let v34 = Rc::clone(xd);
              let v37 = Rc::clone(xf);
              let v40 = Rc::clone(ou);
              let v43 = Rc::clone(c);
              let v45 = Rc::clone(e);
              let v47 = Rc::clone(v);
              let r = ebound(n_1, L_1, v31, v34, v37, v40, v43, v45, v47);
              let v54 = Rc::clone(xs);
              let v57 = Rc::clone(xd);
              let v60 = Rc::clone(xf);
              let v61 = Rc::clone(e);
              std::mem::drop(st_1);
              let v63 = unit_f(L_1, v54, v57, v60, v61);
              let v66 = Clone::clone(&r);
              let v68 = fst::<Rc<Array<f64>>, bool>(v66);
              ((v63, v68), snd::<Rc<Array<f64>>, bool>(r))
            },
            false => {
              st_1
            },
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
  let v5 = &xs;
  let s = rocq_array::get::<u64>(&v5, l);
  let v9 = &xd;
  let d = rocq_array::get::<u64>(&v9, l);
  match eqb(s, d) {
    true => {
      std::mem::drop(xs);
      std::mem::drop(xd);
      a
    },
    false => {
      std::mem::drop(xs);
      std::mem::drop(xd);
      let v42 = rocq_array::set::<bool>(a, add_1(mul_1(s, n), d), true);
      rocq_array::set::<bool>(v42, add_1(mul_1(d, n), s), true)
    },
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
  match ltb_1(x, b) {
    true => {
      x
    },
    false => {
      b
    },
  }
}

// Rocq: Timing.timing_implem.faced_f
// Variant: uncurried
pub fn faced_f_owned(n: u64, adj: Rc<Array<bool>>, v: Rc<Array<f64>>, i: u64) -> f64 {
  let v13 = Rc::clone(&v);
  let v14 = {
    let __anf_capture_15 = i;
    let __anf_capture_17 = n;
    move |k: u64, acc: f64| -> f64 {
      let i = &__anf_capture_15;
      let n = &__anf_capture_17;
      let adj = &adj;
      let v = &v13;
      let v37 = add_1(mul_1(Clone::clone(i), Clone::clone(n)), k);
      match rocq_array::get::<bool>(&adj, v37) {
        true => {
          let v44 = rocq_array::get::<f64>(&v, k);
          add_2(acc, v44)
        },
        false => {
          acc
        },
      }
    }
  };
  let v57: Rc<dyn Fn(u64, f64) -> f64> = Rc::new(v14);
  let v60 = 0u64;
  let v61 = &v;
  let v64 = rocq_array::get::<f64>(&v61, i);
  std::mem::drop(v);
  loop_::<f64>(n, v57, v60, v64)
}

// Rocq: Timing.timing_implem.faced_f
// Variant: borrowed, uncurried
pub fn faced_f(n: u64, adj: &Rc<Array<bool>>, v: &Rc<Array<f64>>, i: u64) -> f64 {
  let v13 = Rc::clone(adj);
  let v16 = Rc::clone(v);
  let v17 = {
    let __anf_capture_18 = i;
    let __anf_capture_20 = n;
    move |k: u64, acc: f64| -> f64 {
      let i = &__anf_capture_18;
      let n = &__anf_capture_20;
      let adj = &v13;
      let v = &v16;
      let v40 = add_1(mul_1(Clone::clone(i), Clone::clone(n)), k);
      match rocq_array::get::<bool>(&adj, v40) {
        true => {
          let v47 = rocq_array::get::<f64>(&v, k);
          add_2(acc, v47)
        },
        false => {
          acc
        },
      }
    }
  };
  let v60: Rc<dyn Fn(u64, f64) -> f64> = Rc::new(v17);
  let v64 = v;
  loop_::<f64>(n, v60, 0u64, rocq_array::get::<f64>(&v64, i))
}

// Rocq: Timing.timing_implem.gmax
// Variant: uncurried
pub fn gmax(n: u64, g: Rc<dyn Fn(u64) -> f64>) -> f64 {
  let v5 = {
    move |i: u64, m: f64| -> f64 {
      let g = &g;
      let v13 = g(i);
      match ltb_1(m, v13) {
        true => {
          g(i)
        },
        false => {
          m
        },
      }
    }
  };
  let v30: Rc<dyn Fn(u64, f64) -> f64> = Rc::new(v5);
  loop_::<f64>(n, v30, 0u64, f64::from_bits(0u64))
}

// Rocq: Timing.timing_implem.fpair
// Variant: borrowed, uncurried
pub fn fpair(n: u64, adj: &Rc<Array<bool>>, v: &Rc<Array<f64>>, e: &Rc<Array<f64>>, i: u64) -> (f64, f64) {
  let v14 = Rc::clone(adj);
  let v17 = Rc::clone(e);
  let v20 = Rc::clone(v);
  let v21 = {
    let __anf_capture_22 = i;
    let __anf_capture_24 = n;
    move |k: u64, st: (f64, f64)| -> (f64, f64) {
      let i = &__anf_capture_22;
      let n = &__anf_capture_24;
      let adj = &v14;
      let e = &v17;
      let v = &v20;
      let v46 = add_1(mul_1(Clone::clone(i), Clone::clone(n)), k);
      match rocq_array::get::<bool>(&adj, v46) {
        true => {
          let v53 = Clone::clone(&st);
          let v63 = add_2(fst::<f64, f64>(v53), rocq_array::get::<f64>(&e, k));
          let v68 = snd::<f64, f64>(st);
          let v73 = rocq_array::get::<f64>(&v, k);
          (v63, add_2(v68, abs(v73)))
        },
        false => {
          st
        },
      }
    }
  };
  let v94: Rc<dyn Fn(u64, (f64, f64)) -> (f64, f64)> = Rc::new(v21);
  let v98 = e;
  let v101 = rocq_array::get::<f64>(&v98, i);
  let v103 = v;
  loop_::<(f64, f64)>(n, v94, 0u64, (v101, abs(rocq_array::get::<f64>(&v103, i))))
}

// Rocq: Timing.timing_implem.fbound
// Variant: borrowed, uncurried
pub fn fbound(n: u64, adj: &Rc<Array<bool>>, v: &Rc<Array<f64>>, e: &Rc<Array<f64>>, nu: f64, i: u64) -> f64 {
  let n_1 = n;
  let nu_1 = nu;
  let i_1 = i;
  let p = fpair(n_1, adj, v, e, i_1);
  let v25 = Clone::clone(&p);
  let v27 = fst::<f64, f64>(v25);
  let v40 = add_2(snd::<f64, f64>(p), f64::from_bits(4607182418800017408u64));
  up(add_2(v27, mul(nu_1, v40)))
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
  let v8 = rocq_bigint::mul(v0, v1);
  v8
}

// Rocq: Timing.timing_implem.zofi_rec
pub fn zofi_rec_1(i: u64) -> Rc<BigInt> {
  let v9 = zofi_rec(i, ());
  v9
}

// Rocq: Timing.timing_implem.zofi_rec (local: zofi_rec)
// Variant: uncurried, lifted
pub fn zofi_rec(i: u64, _H: ()) -> Rc<BigInt> {
  let v11 = eqb(i, 0u64);
  let v83 = match bdec(v11) {
    sumbool::left => {
      let v16 = rocq_bigint::zero();
      v16
    },
    sumbool::right => {
      let r = zofi_rec(div(i, 2u64), ());
      let v42 = mod_(i, 2u64);
      let v44 = 0u64;
      let bit = match eqb(v42, v44) {
        true => {
          let v52 = rocq_bigint::zero();
          v52
        },
        false => {
          let v55 = rocq_bigint::one();
          let v58 = rocq_bigint::identity(v55);
          v58
        },
      };
      let v64 = rocq_bigint::one();
      let v67 = rocq_bigint::twice(v64);
      let v70 = rocq_bigint::identity(v67);
      let v75 = mul_2(v70, r);
      let v80 = add(v75, bit);
      v80
    },
  };
  v83
}

// Rocq: Timing.timing_implem.zofi
pub fn zofi(i: u64) -> Rc<BigInt> {
  let v5 = zofi_rec_1(i);
  v5
}

// Rocq: Corelib.Floats.PrimFloat.normfr_mantissa
pub fn normfr_mantissa(v0: f64) -> u64 {
  rocq_float64::normfr_mantissa(v0)
}

// Rocq: Timing.timing_implem.fex
pub fn fex(f: f64) -> (Rc<BigInt>, Rc<BigInt>) {
  let v4 = frshiftexp(f);
  match v4 {
    (v6, v8) => {
      let z = &v8;
      let m = zofi(normfr_mantissa(v6));
      let v21 = f64::from_bits(0u64);
      let v27 = match ltb_1(f, v21) {
        true => {
          let v32 = opp(m);
          v32
        },
        false => {
          m
        },
      };
      let v40 = Clone::clone(z);
      let v41 = zofi(v40);
      let v43 = rocq_bigint::one();
      let v46 = rocq_bigint::twice(v43);
      let v49 = rocq_bigint::twice(v46);
      let v52 = rocq_bigint::twice(v49);
      let v55 = rocq_bigint::twice(v52);
      let v58 = rocq_bigint::twice_plus_one(v55);
      let v61 = rocq_bigint::twice_plus_one(v58);
      let v64 = rocq_bigint::twice(v61);
      let v67 = rocq_bigint::twice_plus_one(v64);
      let v70 = rocq_bigint::twice(v67);
      let v73 = rocq_bigint::twice_plus_one(v70);
      let v76 = rocq_bigint::twice(v73);
      let v78 = rocq_bigint::identity(v76);
      let v83 = sub(v41, v78);
      (v27, v83)
    },
  }
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
  let v8 = rocq_bigint::shiftl(v0, v1);
  v8
}

// Rocq: Timing.timing_implem.dlt
// Variant: uncurried
pub fn dlt(x: Rc<BigInt>, a: Rc<BigInt>, y: Rc<BigInt>, b: Rc<BigInt>) -> bool {
  let v7 = Rc::clone(&a);
  let v10 = Rc::clone(&b);
  match leb_1(v7, v10) {
    true => {
      let v20 = sub(b, a);
      let v25 = shiftl(y, v20);
      ltb_2(x, v25)
    },
    false => {
      let v40 = sub(a, b);
      let v46 = shiftl(x, v40);
      ltb_2(v46, y)
    },
  }
}

// Rocq: Timing.timing_implem.fcheck
// Variant: uncurried
pub fn fcheck(B: f64, o: f64) -> bool {
  let v5 = fex(B);
  match v5 {
    (v7, v9) => {
      let eb = &v7;
      let mb = &v9;
      let v16 = fex(o);
      match v16 {
        (v18, v20) => {
          let v25 = rocq_bigint::one();
          let v27 = rocq_bigint::identity(v25);
          let v29 = rocq_bigint::one();
          let v32 = rocq_bigint::twice(v29);
          let v35 = rocq_bigint::twice_plus_one(v32);
          let v38 = rocq_bigint::twice(v35);
          let v41 = rocq_bigint::twice(v38);
          let v43 = rocq_bigint::neg(v41);
          let v45 = Rc::clone(eb);
          let v47 = Rc::clone(mb);
          let v52 = dlt(v45, v47, v27, v43);
          let v56 = rocq_bigint::one();
          let v59 = rocq_bigint::twice(v56);
          let v62 = rocq_bigint::twice(v59);
          let v65 = rocq_bigint::twice(v62);
          let v68 = rocq_bigint::twice(v65);
          let v71 = rocq_bigint::twice(v68);
          let v74 = rocq_bigint::twice(v71);
          let v77 = rocq_bigint::twice(v74);
          let v80 = rocq_bigint::twice(v77);
          let v83 = rocq_bigint::twice(v80);
          let v86 = rocq_bigint::twice(v83);
          let v89 = rocq_bigint::twice(v86);
          let v92 = rocq_bigint::twice(v89);
          let v95 = rocq_bigint::twice(v92);
          let v98 = rocq_bigint::twice(v95);
          let v101 = rocq_bigint::twice(v98);
          let v104 = rocq_bigint::twice(v101);
          let v107 = rocq_bigint::twice(v104);
          let v110 = rocq_bigint::twice(v107);
          let v113 = rocq_bigint::twice(v110);
          let v116 = rocq_bigint::twice_plus_one(v113);
          let v118 = rocq_bigint::identity(v116);
          let v124 = mul_2(v7, v118);
          orb(v52, dlt(v124, v9, v18, v20))
        },
      }
    },
  }
}

// Rocq: Timing.timing_implem.PP
pub fn PP(_v0: ()) -> Rc<BigInt> {
  let v2 = rocq_bigint::one();
  let v5 = rocq_bigint::twice_plus_one(v2);
  let v8 = rocq_bigint::twice(v5);
  let v11 = rocq_bigint::twice(v8);
  let v14 = rocq_bigint::twice(v11);
  let v17 = rocq_bigint::twice(v14);
  let v20 = rocq_bigint::twice(v17);
  let v23 = rocq_bigint::identity(v20);
  v23
}

// Rocq: Timing.timing_implem.fixv
pub fn fixv(f: f64) -> Rc<BigInt> {
  let d = fex(f);
  let v8 = Clone::clone(&d);
  let v10 = fst::<Rc<BigInt>, Rc<BigInt>>(v8);
  let v15 = snd::<Rc<BigInt>, Rc<BigInt>>(d);
  let v21 = PP(());
  let v26 = add(v15, v21);
  let v32 = shiftl(v10, v26);
  v32
}

// Rocq: Timing.timing_implem.link_step
// Variant: uncurried
pub fn link_step(m: u64, xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, xf: Rc<Array<f64>>, l: u64, A: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let v6 = &xs;
  let s = rocq_array::get::<u64>(&v6, l);
  std::mem::drop(xs);
  let v10 = &xd;
  let d = rocq_array::get::<u64>(&v10, l);
  std::mem::drop(xd);
  let v15 = &xf;
  let v18 = rocq_array::get::<f64>(&v15, l);
  std::mem::drop(xf);
  let F = fixv(v18);
  let v33 = add_1(mul_1(d, m), s);
  let v46 = add_1(mul_1(d, m), s);
  let v47 = &A;
  let v51 = rocq_array::get::<Rc<BigInt>>(&v47, v46);
  let v55 = Rc::clone(&F);
  let v56 = add(v51, v55);
  let A1 = rocq_array::set::<Rc<BigInt>>(A, v33, v56);
  let v75 = add_1(mul_1(s, m), s);
  let v88 = add_1(mul_1(s, m), s);
  let v89 = &A1;
  let v93 = rocq_array::get::<Rc<BigInt>>(&v89, v88);
  let v97 = sub(v93, F);
  rocq_array::set::<Rc<BigInt>>(A1, v75, v97)
}

// Rocq: Timing.timing_implem.build
// Variant: uncurried
pub fn build(len: u64, f: Rc<dyn Fn(u64) -> Rc<BigInt>>) -> Rc<Array<Rc<BigInt>>> {
  let v5 = {
    move |k: u64, a: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let f = &f;
      let v12 = f(k);
      rocq_array::set::<Rc<BigInt>>(a, k, v12)
    }
  };
  let v22: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new(v5);
  let v26 = rocq_bigint::zero();
  let v31 = rocq_array::make::<Rc<BigInt>>(len, v26);
  loop_::<Rc<Array<Rc<BigInt>>>>(len, v22, 0u64, v31)
}

// Rocq: Timing.timing_implem.ONE
pub fn ONE(_v0: ()) -> Rc<BigInt> {
  let v3 = rocq_bigint::one();
  let v5 = rocq_bigint::identity(v3);
  let v11 = PP(());
  let v17 = shiftl(v5, v11);
  v17
}

// Rocq: Timing.timing_implem.ident
pub fn ident(m: u64) -> Rc<Array<Rc<BigInt>>> {
  let v7 = mul_1(m, m);
  let v10 = {
    let __anf_capture_11 = m;
    move |k: u64| -> Rc<BigInt> {
      let m = &__anf_capture_11;
      let v20 = div(k, Clone::clone(m));
      let v26 = mod_(k, Clone::clone(m));
      let v45 = match eqb(v20, v26) {
        true => {
          let v39 = ONE(());
          v39
        },
        false => {
          let v42 = rocq_bigint::zero();
          v42
        },
      };
      v45
    }
  };
  let v47: Rc<dyn Fn(u64) -> Rc<BigInt>> = Rc::new(v10);
  build(v7, v47)
}

// Rocq: Timing.timing_implem.amat
// Variant: uncurried
pub fn amat(m: u64, L: u64, xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, xf: Rc<Array<f64>>) -> Rc<Array<Rc<BigInt>>> {
  let v14 = {
    let __anf_capture_15 = m;
    move |v23: u64, v24: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let v27 = Clone::clone(&__anf_capture_15);
      let v29 = Rc::clone(&xs);
      let v31 = Rc::clone(&xd);
      let v33 = Rc::clone(&xf);
      link_step(v27, v29, v31, v33, v23, v24)
    }
  };
  let v41: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new(v14);
  let v48 = ident(m);
  loop_::<Rc<Array<Rc<BigInt>>>>(L, v41, 0u64, v48)
}

// Rocq: Timing.timing_implem.splitb
pub fn splitb(s: u64) -> bool {
  andb(ltb(__rocq_global_1401, s), eqb(mod_(s, 2u64), 0u64))
}

// Rocq: Timing.timing_implem.quad
// Variant: uncurried
pub fn quad(X: Rc<Array<Rc<BigInt>>>, s: u64, h: u64, di: u64, dj: u64) -> Rc<Array<Rc<BigInt>>> {
  let v11 = mul_1(h, h);
  let v22 = {
    let __anf_capture_27 = h;
    move |k: u64| -> Rc<BigInt> {
      let di = &di;
      let s = &s;
      let h = &__anf_capture_27;
      let dj = &dj;
      let X = &X;
      let v42 = div(k, Clone::clone(h));
      let v52 = mul_1(add_1(Clone::clone(di), v42), Clone::clone(s));
      let v59 = mod_(k, Clone::clone(h));
      let v64 = add_1(Clone::clone(dj), v59);
      let v70 = add_1(v52, v64);
      let v73 = rocq_array::get::<Rc<BigInt>>(&X, v70);
      v73
    }
  };
  let v75: Rc<dyn Fn(u64) -> Rc<BigInt>> = Rc::new(v22);
  build(v11, v75)
}

// Rocq: Timing.timing_implem.madd
// Variant: uncurried
pub fn madd(h: u64, A: Rc<Array<Rc<BigInt>>>, B: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let v9 = mul_1(h, h);
  let v14 = {
    move |k: u64| -> Rc<BigInt> {
      let A = &A;
      let B = &B;
      let v23 = rocq_array::get::<Rc<BigInt>>(&A, k);
      let v26 = rocq_array::get::<Rc<BigInt>>(&B, k);
      let v32 = add(v23, v26);
      v32
    }
  };
  let v34: Rc<dyn Fn(u64) -> Rc<BigInt>> = Rc::new(v14);
  build(v9, v34)
}

// Rocq: Timing.timing_implem.msub
// Variant: uncurried
pub fn msub(h: u64, A: Rc<Array<Rc<BigInt>>>, B: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let v9 = mul_1(h, h);
  let v14 = {
    move |k: u64| -> Rc<BigInt> {
      let A = &A;
      let B = &B;
      let v23 = rocq_array::get::<Rc<BigInt>>(&A, k);
      let v26 = rocq_array::get::<Rc<BigInt>>(&B, k);
      let v32 = sub(v23, v26);
      v32
    }
  };
  let v34: Rc<dyn Fn(u64) -> Rc<BigInt>> = Rc::new(v14);
  build(v9, v34)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub_2(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Timing.timing_implem.comb
// Variant: uncurried
pub fn comb(s: u64, h: u64, C11: Rc<Array<Rc<BigInt>>>, C12: Rc<Array<Rc<BigInt>>>, C21: Rc<Array<Rc<BigInt>>>, C22: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let v12 = mul_1(s, s);
  let v25 = {
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
      let v55 = Clone::clone(h);
      let v171 = match ltb(i, v55) {
        true => {
          let v62 = Clone::clone(h);
          let v106 = match ltb(j, v62) {
            true => {
              let v77 = add_1(mul_1(i, Clone::clone(h)), j);
              let v80 = rocq_array::get::<Rc<BigInt>>(&C11, v77);
              v80
            },
            false => {
              let v100 = add_1(mul_1(i, Clone::clone(h)), sub_2(j, Clone::clone(h)));
              let v103 = rocq_array::get::<Rc<BigInt>>(&C12, v100);
              v103
            },
          };
          v106
        },
        false => {
          let v112 = Clone::clone(h);
          let v168 = match ltb(j, v112) {
            true => {
              let v133 = add_1(mul_1(sub_2(i, Clone::clone(h)), Clone::clone(h)), j);
              let v136 = rocq_array::get::<Rc<BigInt>>(&C21, v133);
              v136
            },
            false => {
              let v162 = add_1(mul_1(sub_2(i, Clone::clone(h)), Clone::clone(h)), sub_2(j, Clone::clone(h)));
              let v165 = rocq_array::get::<Rc<BigInt>>(&C22, v162);
              v165
            },
          };
          v168
        },
      };
      v171
    }
  };
  let v173: Rc<dyn Fn(u64) -> Rc<BigInt>> = Rc::new(v25);
  build(v12, v173)
}

// Rocq: Timing.timing_implem.dot
// Variant: borrowed, uncurried
pub fn dot(s: u64, X: &Rc<Array<Rc<BigInt>>>, Y: &Rc<Array<Rc<BigInt>>>, i: u64, j: u64) -> Rc<BigInt> {
  let v13 = Rc::clone(X);
  let v20 = Rc::clone(Y);
  let v21 = {
    let __anf_capture_26 = s;
    move |k: u64, acc: Rc<BigInt>| -> Rc<BigInt> {
      let i = &i;
      let X = &v13;
      let s = &__anf_capture_26;
      let j = &j;
      let Y = &v20;
      let v48 = add_1(mul_1(Clone::clone(i), Clone::clone(s)), k);
      let v50 = rocq_array::get::<Rc<BigInt>>(&X, v48);
      let v63 = add_1(mul_1(k, Clone::clone(s)), Clone::clone(j));
      let v65 = rocq_array::get::<Rc<BigInt>>(&Y, v63);
      let v70 = mul_2(v50, v65);
      let v76 = add(acc, v70);
      v76
    }
  };
  let v78: Rc<dyn Fn(u64, Rc<BigInt>) -> Rc<BigInt>> = Rc::new(v21);
  let v82 = rocq_bigint::zero();
  let v92 = loop_::<Rc<BigInt>>(s, v78, 0u64, v82);
  v92
}

// Rocq: Timing.timing_implem.naive
// Variant: uncurried
pub fn naive(s: u64, X: Rc<Array<Rc<BigInt>>>, Y: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let v9 = mul_1(s, s);
  let v16 = {
    let __anf_capture_17 = s;
    move |k: u64| -> Rc<BigInt> {
      let s = &__anf_capture_17;
      let X = &X;
      let Y = &Y;
      let v29 = div(k, Clone::clone(s));
      let v35 = mod_(k, Clone::clone(s));
      let v46 = dot(Clone::clone(s), X, Y, v29, v35);
      v46
    }
  };
  let v48: Rc<dyn Fn(u64) -> Rc<BigInt>> = Rc::new(v16);
  build(v9, v48)
}

// Rocq: Timing.timing_implem.strass
// Variant: uncurried
pub fn strass_1(s: u64, X: Rc<Array<Rc<BigInt>>>, Y: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  strass(s, X, Y, ())
}

// Rocq: Timing.timing_implem.strass (local: strass)
// Variant: uncurried, lifted
pub fn strass(s: u64, X: Rc<Array<Rc<BigInt>>>, Y: Rc<Array<Rc<BigInt>>>, _H: ()) -> Rc<Array<Rc<BigInt>>> {
  let v9 = splitb(s);
  match bdec(v9) {
    sumbool::left => {
      let h = div(s, 2u64);
      let v23 = {
        let __anf_capture_24 = h;
        move |A: Rc<Array<Rc<BigInt>>>, B: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
          let v32 = Clone::clone(&__anf_capture_24);
          strass(v32, A, B, ())
        }
      };
      let v42: Rc<dyn Fn(Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new(v23);
      let sr: Rc<dyn Fn(Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = v42;
      let v51 = Rc::clone(&X);
      let A11 = quad(v51, s, h, 0u64, 0u64);
      let v66 = Rc::clone(&X);
      let A12 = quad(v66, s, h, 0u64, h);
      let v81 = Rc::clone(&X);
      let A21 = quad(v81, s, h, h, 0u64);
      let A22 = quad(X, s, h, h, h);
      let v110 = Rc::clone(&Y);
      let B11 = quad(v110, s, h, 0u64, 0u64);
      let v125 = Rc::clone(&Y);
      let B12 = quad(v125, s, h, 0u64, h);
      let v140 = Rc::clone(&Y);
      let B21 = quad(v140, s, h, h, 0u64);
      let B22 = quad(Y, s, h, h, h);
      let v167 = Rc::clone(&A11);
      let v170 = Rc::clone(&A22);
      let v171 = madd(h, v167, v170);
      let v177 = Rc::clone(&B11);
      let v180 = Rc::clone(&B22);
      let v181 = madd(h, v177, v180);
      let v182: &Rc<dyn Fn(Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = &sr;
      let M1 = v182(v171, v181);
      let v193 = Rc::clone(&A21);
      let v196 = Rc::clone(&A22);
      let v197 = madd(h, v193, v196);
      let v198: &Rc<dyn Fn(Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = &sr;
      let v203 = Rc::clone(&B11);
      let M2 = v198(v197, v203);
      let v210 = Rc::clone(&B12);
      let v213 = Rc::clone(&B22);
      let v214 = msub(h, v210, v213);
      let v215: &Rc<dyn Fn(Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = &sr;
      let v218 = Rc::clone(&A11);
      let M3 = v215(v218, v214);
      let v227 = Rc::clone(&B21);
      let v230 = Rc::clone(&B11);
      let v231 = msub(h, v227, v230);
      let v232: &Rc<dyn Fn(Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = &sr;
      let v235 = Rc::clone(&A22);
      let M4 = v232(v235, v231);
      let v244 = Rc::clone(&A11);
      let v247 = Rc::clone(&A12);
      let v248 = madd(h, v244, v247);
      let v249: &Rc<dyn Fn(Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = &sr;
      let v254 = Rc::clone(&B22);
      let M5 = v249(v248, v254);
      let v263 = msub(h, A21, A11);
      let v271 = madd(h, B11, B12);
      let v272: &Rc<dyn Fn(Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = &sr;
      let M6 = v272(v263, v271);
      let v285 = msub(h, A12, A22);
      let v293 = madd(h, B21, B22);
      let v294: &Rc<dyn Fn(Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = &sr;
      let M7 = v294(v285, v293);
      std::mem::drop(sr);
      let v308 = Rc::clone(&M1);
      let v311 = Rc::clone(&M4);
      let v312 = madd(h, v308, v311);
      let v319 = Rc::clone(&M5);
      let v320 = msub(h, v312, v319);
      let v327 = madd(h, v320, M7);
      let v333 = Rc::clone(&M3);
      let v336 = madd(h, v333, M5);
      let v342 = Rc::clone(&M2);
      let v345 = madd(h, v342, M4);
      let v355 = msub(h, M1, M2);
      let v362 = madd(h, v355, M3);
      let v369 = madd(h, v362, M6);
      comb(s, h, v327, v336, v345, v369)
    },
    sumbool::right => {
      naive(s, X, Y)
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.shiftr
// Variant: uncurried
pub fn shiftr(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::shiftr(v0, v1);
  v8
}

// Rocq: Timing.timing_implem.mulr
// Variant: uncurried
pub fn mulr(m: u64, X: Rc<Array<Rc<BigInt>>>, Y: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let C = strass_1(m, X, Y);
  let v17 = mul_1(m, m);
  let v20 = {
    move |k: u64| -> Rc<BigInt> {
      let C = &C;
      let v27 = rocq_array::get::<Rc<BigInt>>(&C, k);
      let v33 = PP(());
      let v39 = shiftr(v27, v33);
      v39
    }
  };
  let v41: Rc<dyn Fn(u64) -> Rc<BigInt>> = Rc::new(v20);
  build(v17, v41)
}

// Rocq: Timing.timing_implem.pw
// Variant: uncurried
pub fn pw_1(m: u64, t: u64, R: Rc<option<Rc<Array<Rc<BigInt>>>>>, B: Rc<Array<Rc<BigInt>>>) -> Rc<option<Rc<Array<Rc<BigInt>>>>> {
  pw(m, t, R, B, ())
}

// Rocq: Timing.timing_implem.pw (local: pw)
// Variant: uncurried, lifted
pub fn pw(m: u64, t: u64, R: Rc<option<Rc<Array<Rc<BigInt>>>>>, B: Rc<Array<Rc<BigInt>>>, _H: ()) -> Rc<option<Rc<Array<Rc<BigInt>>>>> {
  let v14 = eqb(t, 0u64);
  match bdec(v14) {
    sumbool::left => {
      std::mem::drop(B);
      R
    },
    sumbool::right => {
      let v28 = mod_(t, 2u64);
      let v30 = 0u64;
      let R_ = match eqb(v28, v30) {
        true => {
          R
        },
        false => {
          let v58 = match &*R {
            option::Some(X) => {
              let v46 = Rc::clone(X);
              std::mem::drop(R);
              let v50 = Rc::clone(&B);
              mulr(m, v46, v50)
            },
            option::None => {
              std::mem::drop(R);
              Rc::clone(&B)
            },
          };
          Rc::new(option::<Rc<Array<Rc<BigInt>>>>::Some(v58))
        },
      };
      let t_ = div(t, 2u64);
      match eqb(t_, 0u64) {
        true => {
          std::mem::drop(B);
          R_
        },
        false => {
          let v90 = Rc::clone(&B);
          let v93 = mulr(m, v90, B);
          pw(m, t_, R_, v93, ())
        },
      }
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.min
// Variant: uncurried
pub fn min(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::min(v0, v1);
  v8
}

// Rocq: Timing.timing_implem.faced_z
// Variant: uncurried
pub fn faced_z_owned(n: u64, adj: Rc<Array<bool>>, v: Rc<Array<Rc<BigInt>>>, i: u64) -> Rc<BigInt> {
  let v5 = &v;
  let v8 = rocq_array::get::<Rc<BigInt>>(&v5, i);
  let v18 = {
    let __anf_capture_19 = i;
    let __anf_capture_21 = n;
    let __anf_capture_25 = v;
    move |k: u64, acc: Rc<BigInt>| -> Rc<BigInt> {
      let i = &__anf_capture_19;
      let n = &__anf_capture_21;
      let adj = &adj;
      let v = &__anf_capture_25;
      let v41 = add_1(mul_1(Clone::clone(i), Clone::clone(n)), k);
      let v59 = match rocq_array::get::<bool>(&adj, v41) {
        true => {
          let v48 = rocq_array::get::<Rc<BigInt>>(&v, k);
          let v54 = add(acc, v48);
          v54
        },
        false => {
          acc
        },
      };
      v59
    }
  };
  let v61: Rc<dyn Fn(u64, Rc<BigInt>) -> Rc<BigInt>> = Rc::new(v18);
  let v65 = rocq_bigint::zero();
  let v74 = loop_::<Rc<BigInt>>(n, v61, 0u64, v65);
  let v80 = add(v8, v74);
  v80
}

// Rocq: Timing.timing_implem.faced_z
// Variant: borrowed, uncurried
pub fn faced_z(n: u64, adj: &Rc<Array<bool>>, v: &Rc<Array<Rc<BigInt>>>, i: u64) -> Rc<BigInt> {
  let v7 = v;
  let v10 = rocq_array::get::<Rc<BigInt>>(&v7, i);
  let v18 = Rc::clone(adj);
  let v21 = Rc::clone(v);
  let v22 = {
    let __anf_capture_23 = i;
    let __anf_capture_25 = n;
    move |k: u64, acc: Rc<BigInt>| -> Rc<BigInt> {
      let i = &__anf_capture_23;
      let n = &__anf_capture_25;
      let adj = &v18;
      let v = &v21;
      let v45 = add_1(mul_1(Clone::clone(i), Clone::clone(n)), k);
      let v63 = match rocq_array::get::<bool>(&adj, v45) {
        true => {
          let v52 = rocq_array::get::<Rc<BigInt>>(&v, k);
          let v58 = add(acc, v52);
          v58
        },
        false => {
          acc
        },
      };
      v63
    }
  };
  let v65: Rc<dyn Fn(u64, Rc<BigInt>) -> Rc<BigInt>> = Rc::new(v22);
  let v69 = rocq_bigint::zero();
  let v78 = loop_::<Rc<BigInt>>(n, v65, 0u64, v69);
  let v84 = add(v10, v78);
  v84
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
  let v3 = Rc::clone(&p);
  match rocq_bigint::positive_tag(v3) {
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
  let v3 = Rc::clone(&z);
  match rocq_bigint::integer_tag(v3) {
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
  let v8 = rocq_bigint::one();
  let v11 = rocq_bigint::twice(v8);
  let v13 = rocq_bigint::identity(v11);
  let v19 = PP(());
  let v24 = mul_2(v13, v19);
  let v26 = rocq_bigint::one();
  let v29 = rocq_bigint::twice_plus_one(v26);
  let v32 = rocq_bigint::twice_plus_one(v29);
  let v35 = rocq_bigint::twice_plus_one(v32);
  let v38 = rocq_bigint::twice(v35);
  let v40 = rocq_bigint::identity(v38);
  let v45 = sub(v24, v40);
  let v51 = shiftr(z, v45);
  div_1(of_uint63(iofz(v51)), of_uint63(1073741824u64))
}

// Rocq: Timing.timing_implem.conv
pub fn conv(z: Rc<BigInt>) -> f64 {
  let v2 = rocq_bigint::zero();
  let v5 = Rc::clone(&z);
  match ltb_2(v5, v2) {
    true => {
      let v16 = opp(z);
      opp_1(cv(v16))
    },
    false => {
      cv(z)
    },
  }
}

// Rocq: Timing.timing_implem.timing_exact
// Variant: uncurried
pub fn timing_exact(xt: u64, xu: Rc<Array<f64>>, xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, xf: Rc<Array<f64>>) -> f64 {
  let v5 = &xu;
  let n = rocq_array::length::<f64>(&v5);
  let v7 = &xs;
  let L = rocq_array::length::<u64>(&v7);
  let m = mul_1(div(add_1(n, 7u64), 8u64), 8u64);
  let v40 = Rc::clone(&xs);
  let v43 = Rc::clone(&xd);
  let A = amat(m, L, v40, v43, xf);
  let v59 = pw_1(m, xt, Rc::new(option::<Rc<Array<Rc<BigInt>>>>::None), A);
  let (v60, v61) = __rocq_reuse::reset(v59, |__payload| Clone::clone(__payload));
  std::mem::drop(v61);
  let Rf = match v60 {
    option::Some(v66) => {
      v66
    },
    option::None => {
      ident(m)
    },
  };
  let v82 = {
    let __anf_capture_83 = n;
    let __anf_capture_85 = xu;
    move |s: u64| -> Rc<BigInt> {
      let n = &__anf_capture_83;
      let xu = &__anf_capture_85;
      let v92 = Clone::clone(n);
      let v108 = match ltb(s, v92) {
        true => {
          let v99 = rocq_array::get::<f64>(&xu, s);
          let v102 = fixv(v99);
          v102
        },
        false => {
          let v105 = rocq_bigint::zero();
          v105
        },
      };
      v108
    }
  };
  let v110: Rc<dyn Fn(u64) -> Rc<BigInt>> = Rc::new(v82);
  let uh = build(m, v110);
  let v124 = {
    let __anf_capture_129 = m;
    move |i: u64| -> Rc<BigInt> {
      let Rf = &Rf;
      let uh = &uh;
      let m = &__anf_capture_129;
      let v136 = Clone::clone(m);
      let v138 = Rc::clone(Rf);
      let v140 = Rc::clone(uh);
      let v141 = {
        move |k: u64, acc: Rc<BigInt>| -> Rc<BigInt> {
          let i = &i;
          let m = &v136;
          let Rf = &v138;
          let uh = &v140;
          let v166 = add_1(mul_1(Clone::clone(i), Clone::clone(m)), k);
          let v168 = rocq_array::get::<Rc<BigInt>>(&Rf, v166);
          let v171 = rocq_array::get::<Rc<BigInt>>(&uh, k);
          let v176 = mul_2(v168, v171);
          let v182 = add(acc, v176);
          v182
        }
      };
      let v184: Rc<dyn Fn(u64, Rc<BigInt>) -> Rc<BigInt>> = Rc::new(v141);
      let v188 = rocq_bigint::zero();
      let v190 = Clone::clone(m);
      let v198 = loop_::<Rc<BigInt>>(v190, v184, 0u64, v188);
      v198
    }
  };
  let v200: Rc<dyn Fn(u64) -> Rc<BigInt>> = Rc::new(v124);
  let v = build(m, v200);
  let v214 = {
    let __anf_capture_215 = n;
    let __anf_capture_217 = xs;
    let __anf_capture_219 = xd;
    move |v221: u64, v222: Rc<Array<bool>>| -> Rc<Array<bool>> {
      let v225 = Clone::clone(&__anf_capture_215);
      let v227 = Rc::clone(&__anf_capture_217);
      let v229 = Rc::clone(&__anf_capture_219);
      adj_step(v225, v227, v229, v221, v222)
    }
  };
  let v237: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new(v214);
  let v253 = rocq_array::make::<bool>(mul_1(n, n), false);
  let adj = loop_::<Rc<Array<bool>>>(L, v237, 0u64, v253);
  let v268 = Rc::clone(&adj);
  let v271 = Rc::clone(&v);
  let v272 = {
    let __anf_capture_273 = n;
    move |i: u64, b: Rc<BigInt>| -> Rc<BigInt> {
      let v289 = faced_z(Clone::clone(&__anf_capture_273), &v268, &v271, i);
      let v295 = min(b, v289);
      v295
    }
  };
  let v297: Rc<dyn Fn(u64, Rc<BigInt>) -> Rc<BigInt>> = Rc::new(v272);
  let v312 = faced_z_owned(n, adj, v, 0u64);
  let best = loop_::<Rc<BigInt>>(n, v297, 1u64, v312);
  conv(best)
}

// Rocq: Timing.timing_implem.timing_impl
// Variant: uncurried
pub fn timing_impl(xt: u64, xu: Rc<Array<f64>>, xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, xf: Rc<Array<f64>>) -> f64 {
  let v5 = &xu;
  let n = rocq_array::length::<f64>(&v5);
  let v7 = &xs;
  let L = rocq_array::length::<u64>(&v7);
  let v12 = Rc::clone(&xs);
  let v15 = Rc::clone(&xd);
  let v16 = {
    move |v21: u64, v22: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let v25 = Rc::clone(&v12);
      let v27 = Rc::clone(&v15);
      cnt_step(v25, v27, v21, v22)
    }
  };
  let v35: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v16);
  let v45 = rocq_array::make::<u64>(n, 0u64);
  let c = loop_::<Rc<Array<u64>>>(L, v35, 0u64, v45);
  let v58 = Rc::clone(&xs);
  let v61 = Rc::clone(&xd);
  let v64 = Rc::clone(&xf);
  let v65 = {
    move |v72: u64, v73: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let v76 = Rc::clone(&v58);
      let v78 = Rc::clone(&v61);
      let v80 = Rc::clone(&v64);
      out_step(v76, v78, v80, v72, v73)
    }
  };
  let v88: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new(v65);
  let v98 = rocq_array::make::<f64>(n, f64::from_bits(0u64));
  let ou = loop_::<Rc<Array<f64>>>(L, v88, 0u64, v98);
  let v115 = Rc::clone(&xs);
  let v118 = Rc::clone(&xd);
  let v121 = Rc::clone(&xf);
  let v124 = Rc::clone(&ou);
  let v127 = Rc::clone(&c);
  let v128 = {
    let __anf_capture_129 = n;
    let __anf_capture_131 = L;
    move |v143: u64, v144: ((Rc<Array<f64>>, Rc<Array<f64>>), bool)| -> ((Rc<Array<f64>>, Rc<Array<f64>>), bool) {
      let n = &__anf_capture_129;
      let L = &__anf_capture_131;
      let xs = &v115;
      let xd = &v118;
      let xf = &v121;
      let ou = &v124;
      let c = &v127;
      let v159 = tstep(Clone::clone(n), Clone::clone(L), xs, xd, xf, ou, c, v143, v144);
      v159
    }
  };
  let v162: Rc<dyn Fn(u64, ((Rc<Array<f64>>, Rc<Array<f64>>), bool)) -> ((Rc<Array<f64>>, Rc<Array<f64>>), bool)> = Rc::new(v128);
  let v172 = rocq_array::make::<f64>(n, f64::from_bits(0u64));
  let v175 = Rc::clone(&xu);
  let v196 = loop_::<((Rc<Array<f64>>, Rc<Array<f64>>), bool)>(xt, v162, 0u64, ((v175, v172), true));
  match v196 {
    (v198, v200) => {
      let p = &v200;
      match v198 {
        (v204, v206) => {
          let e = &v204;
          let v = &v206;
          match p {
            true => {
              let v216 = Rc::clone(&xs);
              let v219 = Rc::clone(&xd);
              let v220 = {
                let __anf_capture_221 = n;
                move |v227: u64, v228: Rc<Array<bool>>| -> Rc<Array<bool>> {
                  let v231 = Clone::clone(&__anf_capture_221);
                  let v233 = Rc::clone(&v216);
                  let v235 = Rc::clone(&v219);
                  adj_step(v231, v233, v235, v227, v228)
                }
              };
              let v243: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new(v220);
              let v259 = rocq_array::make::<bool>(mul_1(n, n), false);
              let adj = loop_::<Rc<Array<bool>>>(L, v243, 0u64, v259);
              let v274 = Rc::clone(&adj);
              let v276 = Rc::clone(e);
              let v277 = {
                let __anf_capture_278 = n;
                move |i: u64, b: f64| -> f64 {
                  let v294 = faced_f(Clone::clone(&__anf_capture_278), &v274, &v276, i);
                  fmin(b, v294)
                }
              };
              let v302: Rc<dyn Fn(u64, f64) -> f64> = Rc::new(v277);
              let v313 = Rc::clone(&adj);
              let v315 = Rc::clone(e);
              let v318 = faced_f_owned(n, v313, v315, 0u64);
              let o = loop_::<f64>(n, v302, 1u64, v318);
              let nu = mul(of_uint63(add_1(n, 1u64)), __rocq_global_419);
              let v352 = Rc::clone(&adj);
              let v354 = Rc::clone(e);
              let v356 = Rc::clone(v);
              let v359 = {
                let __anf_capture_360 = n;
                move |v370: u64| -> f64 {
                  let n = &__anf_capture_360;
                  let adj = &v352;
                  let e = &v354;
                  let v = &v356;
                  let v372 = Clone::clone(n);
                  let v374 = Clone::clone(&nu);
                  fbound(v372, adj, e, v, v374, v370)
                }
              };
              let v384: Rc<dyn Fn(u64) -> f64> = Rc::new(v359);
              let B = gmax(n, v384);
              match fcheck(B, o) {
                true => {
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
                },
                false => {
                  std::mem::drop(adj);
                  std::mem::drop(ou);
                  std::mem::drop(c);
                  std::mem::drop(v206);
                  std::mem::drop(v204);
                  timing_exact(xt, xu, xs, xd, xf)
                },
              }
            },
            false => {
              std::mem::drop(ou);
              std::mem::drop(c);
              std::mem::drop(v206);
              std::mem::drop(v204);
              timing_exact(xt, xu, xs, xd, xf)
            },
          }
        },
      }
    },
  }
}

// Rocq: Timing.timing_implem.timing_impl
pub fn timing_impl_curried(xt: u64) -> Rc<dyn Fn(Rc<Array<f64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<f64>>) -> f64>>>> {
  let v3 = {
    move |xu: Rc<Array<f64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<f64>>) -> f64>>> {
      let xt = &xt;
      let v8 = Clone::clone(xt);
      let v11 = {
        move |xs: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<f64>>) -> f64>> {
          let xt = &v8;
          let xu = &xu;
          let v18 = Clone::clone(xt);
          let v20 = Rc::clone(xu);
          let v23 = {
            move |xd: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<f64>>) -> f64> {
              let xt = &v18;
              let xu = &v20;
              let xs = &xs;
              let v32 = Clone::clone(xt);
              let v34 = Rc::clone(xu);
              let v36 = Rc::clone(xs);
              let v39 = {
                move |xf: Rc<Array<f64>>| -> f64 {
                  let v51 = Clone::clone(&v32);
                  let v53 = Rc::clone(&v34);
                  let v55 = Rc::clone(&v36);
                  let v57 = Rc::clone(&xd);
                  timing_impl(v51, v53, v55, v57, xf)
                }
              };
              let v63: Rc<dyn Fn(Rc<Array<f64>>) -> f64> = Rc::new(v39);
              v63
            }
          };
          let v67: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<f64>>) -> f64>> = Rc::new(v23);
          v67
        }
      };
      let v71: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<f64>>) -> f64>>> = Rc::new(v11);
      v71
    }
  };
  let v75: Rc<dyn Fn(Rc<Array<f64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<f64>>) -> f64>>>> = Rc::new(v3);
  v75
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<f64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<f64>>) -> f64> {
  let v0: Rc<dyn Fn(u64, Rc<Array<f64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<f64>>) -> f64> = __rocq_global_2208.with(Clone::clone);
  v0
}
const __rocq_global_416: f64 = f64::from_bits(4607182418804211712u64);
const __rocq_global_419: f64 = f64::from_bits(4372995238176751616u64);
const __rocq_global_444: f64 = f64::from_bits(4472074429978902528u64);
const __rocq_global_1401: u64 = 16u64;
std::thread_local! { static __rocq_global_2208: Rc<dyn Fn(u64, Rc<Array<f64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<f64>>) -> f64> = timing(); }
std::thread_local! { static __rocq_global_2211: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<f64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<f64>>) -> f64>>>>> = timing_curried(); }