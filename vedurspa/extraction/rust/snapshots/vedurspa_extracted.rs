// Generated from OwnedANF. This printer is not verified.
#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;
#[allow(unused_imports)] use rocq_bigint::BigInt;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

pub struct fitr {
  pub fc0: Rc<BigInt>,
  pub fc1: Rc<BigInt>,
  pub fden: Rc<BigInt>,
}

impl Clone for fitr {
  fn clone(&self) -> Self {
    match self {
      fitr { fc0: __field0, fc1: __field1, fden: __field2 } => fitr { fc0: Clone::clone(__field0), fc1: Clone::clone(__field1), fden: Clone::clone(__field2) },
    }
  }
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub struct sums {
  pub sP: Rc<BigInt>,
  pub sK: Rc<BigInt>,
  pub sKK: Rc<BigInt>,
  pub sY: Rc<BigInt>,
  pub sKY: Rc<BigInt>,
  pub sG: Rc<BigInt>,
}

impl Clone for sums {
  fn clone(&self) -> Self {
    match self {
      sums { sP: __field0, sK: __field1, sKK: __field2, sY: __field3, sKY: __field4, sG: __field5 } => sums { sP: Clone::clone(__field0), sK: Clone::clone(__field1), sKK: Clone::clone(__field2), sY: Clone::clone(__field3), sKY: Clone::clone(__field4), sG: Clone::clone(__field5) },
    }
  }
}

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

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::PositiveTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::NaturalTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::IntegerTag>; };

pub type uint = u64;

pub type Out = (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>);

// Rocq: Corelib.Array.PrimArray.max_length
pub fn max_length() -> u64 {
  4194303u64
}

// Rocq: Vedurspa.vedurspa_implem.vedurspa
// Variant: uncurried
pub fn vedurspa() -> Rc<dyn Fn(Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>, Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>, u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)> {
  let v0: fn(Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>, Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>, u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>) = vedurspa_impl_owned;
  let v1: Rc<dyn Fn(Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>, Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>, u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)> = Rc::new(v0);
  v1
}

// Rocq: Vedurspa.vedurspa_implem.vedurspa
pub fn vedurspa_curried() -> Rc<dyn Fn(Rc<Array<Rc<option<f64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<option<u64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<option<f64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<option<u64>>>>) -> Rc<dyn Fn(u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)>>>>> {
  let v0: fn(Rc<Array<Rc<option<f64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<option<u64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<option<f64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<option<u64>>>>) -> Rc<dyn Fn(u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)>>>> = vedurspa_impl_curried_owned;
  let v1: Rc<dyn Fn(Rc<Array<Rc<option<f64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<option<u64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<option<f64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<option<u64>>>>) -> Rc<dyn Fn(u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)>>>>> = Rc::new(v0);
  v1
}

// Rocq: Vedurspa.vedurspa_implem.sP
pub fn sP(s: Rc<sums>) -> Rc<BigInt> {
  let v3 = Rc::clone((&(&**&s).sP));
  std::mem::drop(s);
  v3
}

// Rocq: Vedurspa.vedurspa_implem.sK
pub fn sK(s: Rc<sums>) -> Rc<BigInt> {
  let v3 = Rc::clone((&(&**&s).sK));
  std::mem::drop(s);
  v3
}

// Rocq: Corelib.BinNums.IntDef.Z.ltb
// Variant: uncurried
pub fn ltb(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::lt(v0, v1)
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

// Rocq: Corelib.BinNums.IntDef.Z.mul
// Variant: uncurried
pub fn mul(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::mul(v0, v1);
  v8
}

// Rocq: Vedurspa.vedurspa_implem.sKK
pub fn sKK(s: Rc<sums>) -> Rc<BigInt> {
  let v3 = Rc::clone((&(&**&s).sKK));
  std::mem::drop(s);
  v3
}

// Rocq: Vedurspa.vedurspa_implem.sKY
pub fn sKY(s: Rc<sums>) -> Rc<BigInt> {
  let v3 = Rc::clone((&(&**&s).sKY));
  std::mem::drop(s);
  v3
}

// Rocq: Vedurspa.vedurspa_implem.sY
pub fn sY(s: Rc<sums>) -> Rc<BigInt> {
  let v3 = Rc::clone((&(&**&s).sY));
  std::mem::drop(s);
  v3
}

// Rocq: Vedurspa.vedurspa_implem.sG
pub fn sG(s: Rc<sums>) -> Rc<BigInt> {
  let v3 = Rc::clone((&(&**&s).sG));
  std::mem::drop(s);
  v3
}

// Rocq: Corelib.BinNums.IntDef.Z.leb
// Variant: uncurried
pub fn leb(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::le(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.shiftl
// Variant: uncurried
pub fn shiftl(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::shiftl(v0, v1);
  v8
}

// Rocq: Vedurspa.vedurspa_implem.fit
// Variant: uncurried
pub fn fit(s: Rc<sums>, sc: Rc<BigInt>) -> Rc<option<Rc<fitr>>> {
  let v5 = Rc::clone(&s);
  let P = sP(v5);
  let v10 = Rc::clone(&s);
  let SK = sK(v10);
  let v14 = rocq_bigint::one();
  let v17 = rocq_bigint::twice(v14);
  let v19 = rocq_bigint::identity(v17);
  let v22 = Rc::clone(&P);
  match ltb(v22, v19) {
    true => {
      std::mem::drop(SK);
      std::mem::drop(P);
      std::mem::drop(s);
      std::mem::drop(sc);
      Rc::new(option::<Rc<fitr>>::None)
    },
    false => {
      let v37 = Rc::clone(&s);
      let v38 = sKK(v37);
      let v41 = Rc::clone(&P);
      let v44 = mul(v41, v38);
      let v48 = Rc::clone(&SK);
      let v51 = Rc::clone(&SK);
      let v52 = mul(v48, v51);
      let D = sub(v44, v52);
      let v63 = Rc::clone(&s);
      let v64 = sKY(v63);
      let v67 = Rc::clone(&P);
      let v70 = mul(v67, v64);
      let v75 = Rc::clone(&s);
      let v76 = sY(v75);
      let v79 = Rc::clone(&SK);
      let v82 = mul(v79, v76);
      let B = sub(v70, v82);
      let v93 = Rc::clone(&s);
      let v95 = sY(v93);
      let v99 = Rc::clone(&D);
      let v100 = mul(v95, v99);
      let v104 = Rc::clone(&B);
      let v107 = mul(v104, SK);
      let n0 = sub(v100, v107);
      let v118 = Rc::clone(&P);
      let n1 = mul(B, v118);
      let den = mul(P, D);
      let v131 = sG(s);
      let e = add(v131, sc);
      let v138 = rocq_bigint::zero();
      let v142 = Rc::clone(&e);
      match leb(v138, v142) {
        true => {
          let v150 = Rc::clone(&e);
          let v151 = shiftl(n0, v150);
          let v157 = shiftl(n1, e);
          let v166 = Rc::new(fitr { fc0: v151, fc1: v157, fden: den });
          Rc::new(option::<Rc<fitr>>::Some(v166))
        },
        false => {
          let v178 = opp(e);
          let v183 = shiftl(den, v178);
          let v192 = Rc::new(fitr { fc0: n0, fc1: n1, fden: v183 });
          Rc::new(option::<Rc<fitr>>::Some(v192))
        },
      }
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb_1(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Vedurspa.vedurspa_implem.bdec
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

// Rocq: Vedurspa.vedurspa_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Vedurspa.vedurspa_implem.wloop (local: wloop)
// Variant: uncurried, lifted
pub fn wloop<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St, _H: ()) -> St {
  let v13 = ltb_1(i, hi);
  match bdec(v13) {
    sumbool::left => {
      let v17: &Rc<dyn Fn(u64, St) -> bool> = &cont;
      let v21 = Clone::clone(&s);
      let v23 = v17(i, v21);
      match v23 {
        true => {
          let v32 = add_1(i, 1u64);
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

// Rocq: Vedurspa.vedurspa_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop_1::<St>(hi, cont, f, i, s)
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

// Rocq: Vedurspa.vedurspa_implem.zofi_rec
pub fn zofi_rec_1(i: u64) -> Rc<BigInt> {
  let v9 = zofi_rec(i, ());
  v9
}

// Rocq: Vedurspa.vedurspa_implem.zofi_rec (local: zofi_rec)
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
      let v75 = mul(v70, r);
      let v80 = add(v75, bit);
      v80
    },
  };
  v83
}

// Rocq: Vedurspa.vedurspa_implem.zofi
pub fn zofi(i: u64) -> Rc<BigInt> {
  let v5 = zofi_rec_1(i);
  v5
}

// Rocq: Corelib.BinNums.IntDef.Z.eqb
// Variant: uncurried
pub fn eqb_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::equal(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.min
// Variant: uncurried
pub fn min(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::min(v0, v1);
  v8
}

// Rocq: Vedurspa.vedurspa_implem.acc_step
// Variant: uncurried
pub fn acc_step<A: Clone + 'static>(conv: Rc<dyn Fn(A) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>>>, x: Rc<Array<A>>, i: u64, s: Rc<sums>) -> Rc<sums> {
  let v4 = &x;
  let v7 = rocq_array::get::<A>(&v4, i);
  let v8: &Rc<dyn Fn(A) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>>> = &conv;
  let v11 = v8(v7);
  let (v12, v13) = __rocq_reuse::reset(v11, |__payload| Clone::clone(__payload));
  std::mem::drop(v13);
  match v12 {
    option::Some(v18) => {
      let d = &v18;
      let v22 = Clone::clone(d);
      let M = fst::<Rc<BigInt>, Rc<BigInt>>(v22);
      let E = snd::<Rc<BigInt>, Rc<BigInt>>(v18);
      let K = zofi(i);
      let v37 = Rc::clone(&s);
      let v38 = sP(v37);
      let v40 = rocq_bigint::one();
      let v42 = rocq_bigint::identity(v40);
      let P = add(v38, v42);
      let v52 = Rc::clone(&s);
      let v54 = sK(v52);
      let v58 = Rc::clone(&K);
      let SK = add(v54, v58);
      let v64 = Rc::clone(&s);
      let v65 = sKK(v64);
      let v69 = Rc::clone(&K);
      let v72 = Rc::clone(&K);
      let v73 = mul(v69, v72);
      let SKK = add(v65, v73);
      let v80 = rocq_bigint::zero();
      let v83 = Rc::clone(&M);
      match eqb_1(v83, v80) {
        true => {
          std::mem::drop(K);
          std::mem::drop(E);
          std::mem::drop(M);
          std::mem::drop(conv);
          std::mem::drop(x);
          let v91 = Rc::clone(&s);
          let v92 = sY(v91);
          let v96 = Rc::clone(&s);
          let v97 = sKY(v96);
          let v101 = sG(s);
          Rc::new(sums { sP: P, sK: SK, sKK: SKK, sY: v92, sKY: v97, sG: v101 })
        },
        false => {
          std::mem::drop(conv);
          std::mem::drop(x);
          let v123 = Rc::clone(&s);
          let v125 = sG(v123);
          let v129 = Rc::clone(&E);
          let g = min(v125, v129);
          let v137 = Rc::clone(&g);
          let v138 = sub(E, v137);
          let Y = shiftl(M, v138);
          let v148 = Rc::clone(&s);
          let v150 = sG(v148);
          let v154 = Rc::clone(&g);
          let sh = sub(v150, v154);
          let v161 = Rc::clone(&s);
          let v163 = sY(v161);
          let v167 = Rc::clone(&sh);
          let v169 = shiftl(v163, v167);
          let v173 = Rc::clone(&Y);
          let v174 = add(v169, v173);
          let v181 = sKY(s);
          let v185 = shiftl(v181, sh);
          let v191 = mul(K, Y);
          let v196 = add(v185, v191);
          Rc::new(sums { sP: P, sK: SK, sKK: SKK, sY: v174, sKY: v196, sG: g })
        },
      }
    },
    option::None => {
      std::mem::drop(conv);
      std::mem::drop(x);
      s
    },
  }
}

// Rocq: Vedurspa.vedurspa_implem.sums0
pub fn sums0(_v0: ()) -> Rc<sums> {
  let v1 = rocq_bigint::zero();
  let v2 = rocq_bigint::zero();
  let v3 = rocq_bigint::zero();
  let v4 = rocq_bigint::zero();
  let v5 = rocq_bigint::zero();
  let v6 = rocq_bigint::zero();
  Rc::new(sums { sP: v1, sK: v2, sKK: v3, sY: v4, sKY: v5, sG: v6 })
}

// Rocq: Vedurspa.vedurspa_implem.col_sums
// Variant: uncurried
pub fn col_sums<A: Clone + 'static>(conv: Rc<dyn Fn(A) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>>>, x: Rc<Array<A>>) -> Rc<sums> {
  let v3 = &x;
  let v4 = rocq_array::length::<A>(&v3);
  let v5 = {
    move |_v6: u64, v7: Rc<sums>| -> bool {
      std::mem::drop(v7);
      true
    }
  };
  let v12: Rc<dyn Fn(u64, Rc<sums>) -> bool> = Rc::new(v5);
  let v13: Rc<dyn Fn(u64, Rc<sums>) -> bool> = v12;
  let v18 = {
    let __anf_capture_21 = x;
    move |v23: u64, v24: Rc<sums>| -> Rc<sums> {
      let v26: Rc<dyn Fn(A) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>>> = Rc::clone(&conv);
      let v29 = Rc::clone(&__anf_capture_21);
      acc_step::<A>(v26, v29, v23, v24)
    }
  };
  let v37: Rc<dyn Fn(u64, Rc<sums>) -> Rc<sums>> = Rc::new(v18);
  loop_::<Rc<sums>>(v4, v13, v37, 0u64, sums0(()))
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

// Rocq: Corelib.Floats.PrimFloat.ltb
// Variant: uncurried
pub fn ltb_2(v0: f64, v1: f64) -> bool {
  rocq_float64::ltb(v0, v1)
}

// Rocq: Vedurspa.vedurspa_implem.fex
pub fn fex(f: f64) -> (Rc<BigInt>, Rc<BigInt>) {
  let v4 = frshiftexp(f);
  match v4 {
    (v6, v8) => {
      let z = &v8;
      let m = zofi(normfr_mantissa(v6));
      let v21 = f64::from_bits(0u64);
      let v27 = match ltb_2(f, v21) {
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

// Rocq: Vedurspa.vedurspa_implem.fconv
pub fn fconv(o: Rc<option<f64>>) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>> {
  let (v1, v2) = __rocq_reuse::reset(o, |__payload| Clone::clone(__payload));
  std::mem::drop(v2);
  match v1 {
    option::Some(v7) => {
      Rc::new(option::<(Rc<BigInt>, Rc<BigInt>)>::Some(fex(v7)))
    },
    option::None => {
      Rc::new(option::<(Rc<BigInt>, Rc<BigInt>)>::None)
    },
  }
}

// Rocq: Vedurspa.vedurspa_implem.iconv
pub fn iconv(o: Rc<option<u64>>) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>> {
  let (v1, v2) = __rocq_reuse::reset(o, |__payload| Clone::clone(__payload));
  std::mem::drop(v2);
  match v1 {
    option::Some(v7) => {
      let v12 = zofi(v7);
      let v13 = rocq_bigint::zero();
      Rc::new(option::<(Rc<BigInt>, Rc<BigInt>)>::Some((v12, v13)))
    },
    option::None => {
      Rc::new(option::<(Rc<BigInt>, Rc<BigInt>)>::None)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb_1(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Corelib.Floats.PrimFloat.mul
// Variant: uncurried
pub fn mul_1(v0: f64, v1: f64) -> f64 {
  rocq_float64::mul(v0, v1)
}

// Rocq: Corelib.Floats.PrimFloat.opp
pub fn opp_1(v0: f64) -> f64 {
  rocq_float64::opp(v0)
}

// Rocq: Corelib.Floats.PrimFloat.of_uint63
pub fn of_uint63(v0: u64) -> f64 {
  rocq_float64::of_uint63(v0)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul_2(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Vedurspa.vedurspa_implem.pos2int
pub fn pos2int_1(p: Rc<BigInt>) -> u64 {
  pos2int(p)
}

// Rocq: Vedurspa.vedurspa_implem.pos2int (local: pos2int)
// Variant: lifted
pub fn pos2int(p: Rc<BigInt>) -> u64 {
  let v3 = Rc::clone(&p);
  match rocq_bigint::positive_tag(v3) {
    rocq_bigint::PositiveTag::Odd => {
      let q = rocq_bigint::positive_tail(p);
      add_1(mul_2(2u64, pos2int(q)), 1u64)
    },
    rocq_bigint::PositiveTag::Even => {
      let q = rocq_bigint::positive_tail(p);
      mul_2(2u64, pos2int(q))
    },
    rocq_bigint::PositiveTag::One => {
      std::mem::drop(p);
      1u64
    },
  }
}

// Rocq: Vedurspa.vedurspa_implem.z2int
pub fn z2int(z: Rc<BigInt>) -> u64 {
  let v3 = Rc::clone(&z);
  match rocq_bigint::integer_tag(v3) {
    rocq_bigint::IntegerTag::Zero => {
      std::mem::drop(z);
      0u64
    },
    rocq_bigint::IntegerTag::Positive => {
      let p = rocq_bigint::integer_magnitude(z);
      pos2int_1(p)
    },
    rocq_bigint::IntegerTag::Negative => {
      let p = rocq_bigint::integer_magnitude(z);
      std::mem::drop(p);
      0u64
    },
  }
}

// Rocq: Vedurspa.vedurspa_implem.fl_of_Z
pub fn fl_of_Z(z: Rc<BigInt>) -> f64 {
  let v2 = rocq_bigint::zero();
  let v5 = Rc::clone(&z);
  match ltb(v5, v2) {
    true => {
      let v17 = opp(z);
      opp_1(of_uint63(z2int(v17)))
    },
    false => {
      of_uint63(z2int(z))
    },
  }
}

// Rocq: Corelib.BinNums.IntDef.Z.max
// Variant: uncurried
pub fn max(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::max(v0, v1);
  v8
}

// Rocq: Vedurspa.vedurspa_implem.clampZ
// Variant: uncurried
pub fn clampZ(lo: Rc<BigInt>, hi: Rc<BigInt>, v: Rc<BigInt>) -> Rc<BigInt> {
  let v9 = min(hi, v);
  let v15 = max(lo, v9);
  v15
}

// Rocq: Corelib.BinNums.IntDef.Z.div
// Variant: uncurried
pub fn div_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::div(v0, v1);
  v8
}

// Rocq: Vedurspa.vedurspa_implem.fc0
pub fn fc0(f: Rc<fitr>) -> Rc<BigInt> {
  let v3 = Rc::clone((&(&**&f).fc0));
  std::mem::drop(f);
  v3
}

// Rocq: Vedurspa.vedurspa_implem.fc1
pub fn fc1(f: Rc<fitr>) -> Rc<BigInt> {
  let v3 = Rc::clone((&(&**&f).fc1));
  std::mem::drop(f);
  v3
}

// Rocq: Vedurspa.vedurspa_implem.fden
pub fn fden(f: Rc<fitr>) -> Rc<BigInt> {
  let v3 = Rc::clone((&(&**&f).fden));
  std::mem::drop(f);
  v3
}

// Rocq: Vedurspa.vedurspa_implem.rnd_at
// Variant: uncurried
pub fn rnd_at(f: Rc<fitr>, T: Rc<BigInt>) -> Rc<BigInt> {
  let v6 = rocq_bigint::one();
  let v9 = rocq_bigint::twice(v6);
  let v11 = rocq_bigint::identity(v9);
  let v16 = Rc::clone(&f);
  let v17 = fc0(v16);
  let v22 = Rc::clone(&f);
  let v24 = fc1(v22);
  let v28 = mul(v24, T);
  let v33 = add(v17, v28);
  let v38 = mul(v11, v33);
  let v42 = Rc::clone(&f);
  let v43 = fden(v42);
  let v48 = add(v38, v43);
  let v51 = rocq_bigint::one();
  let v54 = rocq_bigint::twice(v51);
  let v56 = rocq_bigint::identity(v54);
  let v60 = fden(f);
  let v65 = mul(v56, v60);
  let v71 = div_1(v48, v65);
  v71
}

// Rocq: Corelib.Floats.PrimFloat.div
// Variant: uncurried
pub fn div_2(v0: f64, v1: f64) -> f64 {
  rocq_float64::div(v0, v1)
}

// Rocq: Vedurspa.vedurspa_implem.c20
pub fn c20(_v0: ()) -> f64 {
  div_2(of_uint63(1u64), of_uint63(1048576u64))
}

// Rocq: Vedurspa.vedurspa_implem.fout
// Variant: uncurried
pub fn fout(fo: Rc<option<Rc<fitr>>>, lo: Rc<BigInt>, hi: Rc<BigInt>, T: Rc<BigInt>) -> Rc<option<f64>> {
  let (v4, v5) = __rocq_reuse::reset(fo, |__payload| Clone::clone(__payload));
  std::mem::drop(v5);
  match v4 {
    option::Some(v10) => {
      let v17 = rocq_bigint::one();
      let v20 = rocq_bigint::twice(v17);
      let v23 = rocq_bigint::twice(v20);
      let v26 = rocq_bigint::twice(v23);
      let v29 = rocq_bigint::twice(v26);
      let v32 = rocq_bigint::twice(v29);
      let v35 = rocq_bigint::twice(v32);
      let v38 = rocq_bigint::twice(v35);
      let v41 = rocq_bigint::twice(v38);
      let v44 = rocq_bigint::twice(v41);
      let v47 = rocq_bigint::twice(v44);
      let v50 = rocq_bigint::twice(v47);
      let v53 = rocq_bigint::twice(v50);
      let v56 = rocq_bigint::twice(v53);
      let v59 = rocq_bigint::twice(v56);
      let v62 = rocq_bigint::twice(v59);
      let v65 = rocq_bigint::twice(v62);
      let v68 = rocq_bigint::twice(v65);
      let v71 = rocq_bigint::twice(v68);
      let v74 = rocq_bigint::twice(v71);
      let v77 = rocq_bigint::twice(v74);
      let v79 = rocq_bigint::identity(v77);
      let v84 = mul(lo, v79);
      let v87 = rocq_bigint::one();
      let v90 = rocq_bigint::twice(v87);
      let v93 = rocq_bigint::twice(v90);
      let v96 = rocq_bigint::twice(v93);
      let v99 = rocq_bigint::twice(v96);
      let v102 = rocq_bigint::twice(v99);
      let v105 = rocq_bigint::twice(v102);
      let v108 = rocq_bigint::twice(v105);
      let v111 = rocq_bigint::twice(v108);
      let v114 = rocq_bigint::twice(v111);
      let v117 = rocq_bigint::twice(v114);
      let v120 = rocq_bigint::twice(v117);
      let v123 = rocq_bigint::twice(v120);
      let v126 = rocq_bigint::twice(v123);
      let v129 = rocq_bigint::twice(v126);
      let v132 = rocq_bigint::twice(v129);
      let v135 = rocq_bigint::twice(v132);
      let v138 = rocq_bigint::twice(v135);
      let v141 = rocq_bigint::twice(v138);
      let v144 = rocq_bigint::twice(v141);
      let v147 = rocq_bigint::twice(v144);
      let v149 = rocq_bigint::identity(v147);
      let v154 = mul(hi, v149);
      let v160 = rnd_at(v10, T);
      let v168 = clampZ(v84, v154, v160);
      Rc::new(option::<f64>::Some(mul_1(fl_of_Z(v168), c20(()))))
    },
    option::None => {
      std::mem::drop(lo);
      std::mem::drop(hi);
      std::mem::drop(T);
      Rc::new(option::<f64>::None)
    },
  }
}

// Rocq: Vedurspa.vedurspa_implem.iout
// Variant: uncurried
pub fn iout(fo: Rc<option<Rc<fitr>>>, lo: Rc<BigInt>, hi: Rc<BigInt>, T: Rc<BigInt>) -> Rc<option<u64>> {
  let (v4, v5) = __rocq_reuse::reset(fo, |__payload| Clone::clone(__payload));
  std::mem::drop(v5);
  match v4 {
    option::Some(v10) => {
      let v19 = rnd_at(v10, T);
      let v27 = clampZ(lo, hi, v19);
      Rc::new(option::<u64>::Some(z2int(v27)))
    },
    option::None => {
      std::mem::drop(lo);
      std::mem::drop(hi);
      std::mem::drop(T);
      Rc::new(option::<u64>::None)
    },
  }
}

// Rocq: Vedurspa.vedurspa_implem.out_step
// Variant: borrowed, uncurried
pub fn out_step(ft: &Rc<option<Rc<fitr>>>, fd: &Rc<option<Rc<fitr>>>, fs: &Rc<option<Rc<fitr>>>, fh: &Rc<option<Rc<fitr>>>, nt: &Rc<BigInt>, nd: &Rc<BigInt>, ns: &Rc<BigInt>, nh: &Rc<BigInt>, i: u64, o: (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>) {
  let i_1 = i;
  let o_1 = o;
  match o_1 {
    (v13, v15) => {
      match v13 {
        (v18, v20) => {
          match v18 {
            (v23, v25) => {
              let j = zofi(i_1);
              let v33 = rocq_bigint::one();
              let v36 = rocq_bigint::twice_plus_one(v33);
              let v39 = rocq_bigint::twice(v36);
              let v42 = rocq_bigint::twice(v39);
              let v45 = rocq_bigint::twice_plus_one(v42);
              let v48 = rocq_bigint::twice(v45);
              let v50 = rocq_bigint::neg(v48);
              let v52 = rocq_bigint::one();
              let v55 = rocq_bigint::twice_plus_one(v52);
              let v58 = rocq_bigint::twice(v55);
              let v61 = rocq_bigint::twice(v58);
              let v64 = rocq_bigint::twice_plus_one(v61);
              let v67 = rocq_bigint::twice(v64);
              let v69 = rocq_bigint::identity(v67);
              let v73 = Rc::clone(nt);
              let v76 = Rc::clone(&j);
              let v77 = add(v73, v76);
              let v94 = rocq_array::set::<Rc<option<f64>>>(v23, i_1, fout(Rc::clone(ft), v50, v69, v77));
              let v96 = rocq_bigint::zero();
              let v98 = rocq_bigint::one();
              let v101 = rocq_bigint::twice(v98);
              let v104 = rocq_bigint::twice_plus_one(v101);
              let v107 = rocq_bigint::twice_plus_one(v104);
              let v110 = rocq_bigint::twice(v107);
              let v113 = rocq_bigint::twice_plus_one(v110);
              let v116 = rocq_bigint::twice(v113);
              let v119 = rocq_bigint::twice(v116);
              let v122 = rocq_bigint::twice(v119);
              let v124 = rocq_bigint::identity(v122);
              let v128 = Rc::clone(nd);
              let v131 = Rc::clone(&j);
              let v132 = add(v128, v131);
              let v149 = rocq_array::set::<Rc<option<u64>>>(v25, i_1, iout(Rc::clone(fd), v96, v124, v132));
              let v155 = (v94, v149);
              let v157 = rocq_bigint::zero();
              let v159 = rocq_bigint::one();
              let v162 = rocq_bigint::twice(v159);
              let v165 = rocq_bigint::twice_plus_one(v162);
              let v168 = rocq_bigint::twice(v165);
              let v171 = rocq_bigint::twice(v168);
              let v174 = rocq_bigint::twice(v171);
              let v177 = rocq_bigint::twice(v174);
              let v179 = rocq_bigint::identity(v177);
              let v183 = Rc::clone(ns);
              let v186 = Rc::clone(&j);
              let v187 = add(v183, v186);
              let v204 = rocq_array::set::<Rc<option<f64>>>(v20, i_1, fout(Rc::clone(fs), v157, v179, v187));
              let v209 = (v155, v204);
              let v212 = rocq_bigint::zero();
              let v214 = rocq_bigint::one();
              let v217 = rocq_bigint::twice_plus_one(v214);
              let v220 = rocq_bigint::twice(v217);
              let v223 = rocq_bigint::twice_plus_one(v220);
              let v226 = rocq_bigint::twice_plus_one(v223);
              let v229 = rocq_bigint::twice_plus_one(v226);
              let v232 = rocq_bigint::twice(v229);
              let v234 = rocq_bigint::identity(v232);
              let v238 = Rc::clone(nh);
              let v241 = add(v238, j);
              let v258 = rocq_array::set::<Rc<option<u64>>>(v15, i_1, iout(Rc::clone(fh), v212, v234, v241));
              (v209, v258)
            },
          }
        },
      }
    },
  }
}

// Rocq: Vedurspa.vedurspa_implem.vedurspa_impl
// Variant: uncurried
pub fn vedurspa_impl_owned(xt: Rc<Array<Rc<option<f64>>>>, xd: Rc<Array<Rc<option<u64>>>>, xs: Rc<Array<Rc<option<f64>>>>, xh: Rc<Array<Rc<option<u64>>>>, m: u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>) {
  let v7: fn(Rc<option<f64>>) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>> = fconv;
  let v8: Rc<dyn Fn(Rc<option<f64>>) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>>> = Rc::new(v7);
  let v14 = Rc::clone(&xt);
  let v15 = col_sums::<Rc<option<f64>>>(v8, v14);
  let v17 = rocq_bigint::one();
  let v20 = rocq_bigint::twice(v17);
  let v23 = rocq_bigint::twice_plus_one(v20);
  let v26 = rocq_bigint::twice(v23);
  let v29 = rocq_bigint::twice(v26);
  let v31 = rocq_bigint::identity(v29);
  let ft = fit(v15, v31);
  let v39: fn(Rc<option<u64>>) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>> = iconv;
  let v40: Rc<dyn Fn(Rc<option<u64>>) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>>> = Rc::new(v39);
  let v46 = Rc::clone(&xd);
  let v47 = col_sums::<Rc<option<u64>>>(v40, v46);
  let v48 = rocq_bigint::zero();
  let fd = fit(v47, v48);
  let v56: fn(Rc<option<f64>>) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>> = fconv;
  let v57: Rc<dyn Fn(Rc<option<f64>>) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>>> = Rc::new(v56);
  let v63 = Rc::clone(&xs);
  let v64 = col_sums::<Rc<option<f64>>>(v57, v63);
  let v66 = rocq_bigint::one();
  let v69 = rocq_bigint::twice(v66);
  let v72 = rocq_bigint::twice_plus_one(v69);
  let v75 = rocq_bigint::twice(v72);
  let v78 = rocq_bigint::twice(v75);
  let v80 = rocq_bigint::identity(v78);
  let fs = fit(v64, v80);
  let v88: fn(Rc<option<u64>>) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>> = iconv;
  let v89: Rc<dyn Fn(Rc<option<u64>>) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>>> = Rc::new(v88);
  let v95 = Rc::clone(&xh);
  let v96 = col_sums::<Rc<option<u64>>>(v89, v95);
  let v97 = rocq_bigint::zero();
  let fh = fit(v96, v97);
  let v104 = __rocq_global_774;
  let L = match leb_1(m, v104) {
    true => {
      m
    },
    false => {
      __rocq_global_774
    },
  };
  let v118 = {
    move |_v119: u64, v120: (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)| -> bool {
      std::mem::drop(v120);
      true
    }
  };
  let v125: Rc<dyn Fn(u64, (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)) -> bool> = Rc::new(v118);
  let v126: Rc<dyn Fn(u64, (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)) -> bool> = v125;
  let v128 = &xt;
  let v129 = rocq_array::length::<Rc<option<f64>>>(&v128);
  std::mem::drop(xt);
  let v132 = zofi(v129);
  let v134 = &xd;
  let v135 = rocq_array::length::<Rc<option<u64>>>(&v134);
  std::mem::drop(xd);
  let v138 = zofi(v135);
  let v140 = &xs;
  let v141 = rocq_array::length::<Rc<option<f64>>>(&v140);
  std::mem::drop(xs);
  let v144 = zofi(v141);
  let v146 = &xh;
  let v147 = rocq_array::length::<Rc<option<u64>>>(&v146);
  std::mem::drop(xh);
  let v150 = zofi(v147);
  let v167 = {
    move |v184: u64, v185: (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)| -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>) {
      let ft = &ft;
      let fd = &fd;
      let fs = &fs;
      let fh = &fh;
      let v176 = &v132;
      let v178 = &v138;
      let v180 = &v144;
      let v182 = &v150;
      let v199 = out_step(ft, fd, fs, fh, v176, v178, v180, v182, v184, v185);
      v199
    }
  };
  let v202: Rc<dyn Fn(u64, (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)> = Rc::new(v167);
  let v213 = rocq_array::make::<Rc<option<f64>>>(L, Rc::new(option::<f64>::None));
  let v221 = rocq_array::make::<Rc<option<u64>>>(L, Rc::new(option::<u64>::None));
  let v226 = (v213, v221);
  let v235 = rocq_array::make::<Rc<option<f64>>>(L, Rc::new(option::<f64>::None));
  let v240 = (v226, v235);
  let v249 = rocq_array::make::<Rc<option<u64>>>(L, Rc::new(option::<u64>::None));
  loop_::<(((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)>(L, v126, v202, 0u64, (v240, v249))
}

// Rocq: Vedurspa.vedurspa_implem.vedurspa_impl
// Variant: borrowed, uncurried
pub fn vedurspa_impl(xt: &Rc<Array<Rc<option<f64>>>>, xd: &Rc<Array<Rc<option<u64>>>>, xs: &Rc<Array<Rc<option<f64>>>>, xh: &Rc<Array<Rc<option<u64>>>>, m: u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>) {
  let m_1 = m;
  let v8: fn(Rc<option<f64>>) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>> = fconv;
  let v9: Rc<dyn Fn(Rc<option<f64>>) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>>> = Rc::new(v8);
  let v15 = Rc::clone(xt);
  let v16 = col_sums::<Rc<option<f64>>>(v9, v15);
  let v18 = rocq_bigint::one();
  let v21 = rocq_bigint::twice(v18);
  let v24 = rocq_bigint::twice_plus_one(v21);
  let v27 = rocq_bigint::twice(v24);
  let v30 = rocq_bigint::twice(v27);
  let v32 = rocq_bigint::identity(v30);
  let ft = fit(v16, v32);
  let v40: fn(Rc<option<u64>>) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>> = iconv;
  let v41: Rc<dyn Fn(Rc<option<u64>>) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>>> = Rc::new(v40);
  let v47 = Rc::clone(xd);
  let v48 = col_sums::<Rc<option<u64>>>(v41, v47);
  let v49 = rocq_bigint::zero();
  let fd = fit(v48, v49);
  let v57: fn(Rc<option<f64>>) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>> = fconv;
  let v58: Rc<dyn Fn(Rc<option<f64>>) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>>> = Rc::new(v57);
  let v64 = Rc::clone(xs);
  let v65 = col_sums::<Rc<option<f64>>>(v58, v64);
  let v67 = rocq_bigint::one();
  let v70 = rocq_bigint::twice(v67);
  let v73 = rocq_bigint::twice_plus_one(v70);
  let v76 = rocq_bigint::twice(v73);
  let v79 = rocq_bigint::twice(v76);
  let v81 = rocq_bigint::identity(v79);
  let fs = fit(v65, v81);
  let v89: fn(Rc<option<u64>>) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>> = iconv;
  let v90: Rc<dyn Fn(Rc<option<u64>>) -> Rc<option<(Rc<BigInt>, Rc<BigInt>)>>> = Rc::new(v89);
  let v96 = Rc::clone(xh);
  let v97 = col_sums::<Rc<option<u64>>>(v90, v96);
  let v98 = rocq_bigint::zero();
  let fh = fit(v97, v98);
  let v105 = __rocq_global_774;
  let L = match leb_1(m_1, v105) {
    true => {
      m_1
    },
    false => {
      __rocq_global_774
    },
  };
  let v119 = {
    move |_v120: u64, v121: (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)| -> bool {
      std::mem::drop(v121);
      true
    }
  };
  let v126: Rc<dyn Fn(u64, (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)) -> bool> = Rc::new(v119);
  let v127: Rc<dyn Fn(u64, (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)) -> bool> = v126;
  let v129 = xt;
  let v133 = zofi(rocq_array::length::<Rc<option<f64>>>(&v129));
  let v135 = xd;
  let v139 = zofi(rocq_array::length::<Rc<option<u64>>>(&v135));
  let v141 = xs;
  let v145 = zofi(rocq_array::length::<Rc<option<f64>>>(&v141));
  let v147 = xh;
  let v151 = zofi(rocq_array::length::<Rc<option<u64>>>(&v147));
  let v168 = {
    move |v185: u64, v186: (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)| -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>) {
      let ft = &ft;
      let fd = &fd;
      let fs = &fs;
      let fh = &fh;
      let v177 = &v133;
      let v179 = &v139;
      let v181 = &v145;
      let v183 = &v151;
      let v200 = out_step(ft, fd, fs, fh, v177, v179, v181, v183, v185, v186);
      v200
    }
  };
  let v203: Rc<dyn Fn(u64, (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)> = Rc::new(v168);
  let v214 = rocq_array::make::<Rc<option<f64>>>(L, Rc::new(option::<f64>::None));
  let v222 = rocq_array::make::<Rc<option<u64>>>(L, Rc::new(option::<u64>::None));
  let v227 = (v214, v222);
  let v236 = rocq_array::make::<Rc<option<f64>>>(L, Rc::new(option::<f64>::None));
  let v241 = (v227, v236);
  let v250 = rocq_array::make::<Rc<option<u64>>>(L, Rc::new(option::<u64>::None));
  loop_::<(((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)>(L, v127, v203, 0u64, (v241, v250))
}

// Rocq: Vedurspa.vedurspa_implem.vedurspa_impl
pub fn vedurspa_impl_curried_owned(xt: Rc<Array<Rc<option<f64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<option<u64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<option<f64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<option<u64>>>>) -> Rc<dyn Fn(u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)>>>> {
  let v3 = {
    move |xd: Rc<Array<Rc<option<u64>>>>| -> Rc<dyn Fn(Rc<Array<Rc<option<f64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<option<u64>>>>) -> Rc<dyn Fn(u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)>>> {
      let xt = &xt;
      let v8 = Rc::clone(xt);
      let v11 = {
        move |xs: Rc<Array<Rc<option<f64>>>>| -> Rc<dyn Fn(Rc<Array<Rc<option<u64>>>>) -> Rc<dyn Fn(u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)>> {
          let xt = &v8;
          let xd = &xd;
          let v18 = Rc::clone(xt);
          let v20 = Rc::clone(xd);
          let v23 = {
            move |xh: Rc<Array<Rc<option<u64>>>>| -> Rc<dyn Fn(u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)> {
              let xt = &v18;
              let xd = &v20;
              let xs = &xs;
              let v32 = Rc::clone(xt);
              let v34 = Rc::clone(xd);
              let v36 = Rc::clone(xs);
              let v39 = {
                move |m: u64| -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>) {
                  let xt = &v32;
                  let xd = &v34;
                  let xs = &v36;
                  let xh = &xh;
                  let v56 = vedurspa_impl(xt, xd, xs, xh, m);
                  v56
                }
              };
              let v59: Rc<dyn Fn(u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)> = Rc::new(v39);
              v59
            }
          };
          let v63: Rc<dyn Fn(Rc<Array<Rc<option<u64>>>>) -> Rc<dyn Fn(u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)>> = Rc::new(v23);
          v63
        }
      };
      let v67: Rc<dyn Fn(Rc<Array<Rc<option<f64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<option<u64>>>>) -> Rc<dyn Fn(u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)>>> = Rc::new(v11);
      v67
    }
  };
  let v71: Rc<dyn Fn(Rc<Array<Rc<option<u64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<option<f64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<option<u64>>>>) -> Rc<dyn Fn(u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)>>>> = Rc::new(v3);
  v71
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

pub fn run() -> Rc<dyn Fn(Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>, Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>, u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)> {
  let v0: Rc<dyn Fn(Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>, Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>, u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)> = __rocq_global_1287.with(Clone::clone);
  v0
}
const __rocq_global_774: u64 = 4194303u64;
std::thread_local! { static __rocq_global_1287: Rc<dyn Fn(Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>, Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>, u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)> = vedurspa(); }
std::thread_local! { static __rocq_global_1290: Rc<dyn Fn(Rc<Array<Rc<option<f64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<option<u64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<option<f64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<option<u64>>>>) -> Rc<dyn Fn(u64) -> (((Rc<Array<Rc<option<f64>>>>, Rc<Array<Rc<option<u64>>>>), Rc<Array<Rc<option<f64>>>>), Rc<Array<Rc<option<u64>>>>)>>>>> = vedurspa_curried(); }