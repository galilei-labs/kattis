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

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::PositiveTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::NaturalTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::IntegerTag>; };

pub type DS = ((((Rc<Array<u64>>, Rc<Array<u64>>), u64), Rc<Array<u64>>), u64);

pub type uint = u64;

// Rocq: Tsp.tsp_implem.tsp
// Variant: uncurried
pub fn tsp() -> Rc<dyn Fn(Rc<Array<f64>>, Rc<Array<f64>>) -> Rc<Array<u64>>> {
  let v0: fn(Rc<Array<f64>>, Rc<Array<f64>>) -> Rc<Array<u64>> = tsp_impl;
  let v1: Rc<dyn Fn(Rc<Array<f64>>, Rc<Array<f64>>) -> Rc<Array<u64>>> = Rc::new(v0);
  v1
}

// Rocq: Tsp.tsp_implem.tsp
pub fn tsp_curried() -> Rc<dyn Fn(Rc<Array<f64>>) -> Rc<dyn Fn(Rc<Array<f64>>) -> Rc<Array<u64>>>> {
  let v0: fn(Rc<Array<f64>>) -> Rc<dyn Fn(Rc<Array<f64>>) -> Rc<Array<u64>>> = tsp_impl_curried;
  let v1: Rc<dyn Fn(Rc<Array<f64>>) -> Rc<dyn Fn(Rc<Array<f64>>) -> Rc<Array<u64>>>> = Rc::new(v0);
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

// Rocq: Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z
pub fn to_Z(v0: u64) -> Rc<BigInt> {
  let v5 = rocq_bigint::of_uint63(v0);
  v5
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Tsp.tsp_implem.bdec
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

// Rocq: Tsp.tsp_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Tsp.tsp_implem.wloop (local: wloop)
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

// Rocq: Tsp.tsp_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop_1::<St>(hi, cont, f, i, s)
}

// Rocq: Corelib.BinNums.IntDef.Z.min
// Variant: uncurried
pub fn min(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::min(v0, v1);
  v8
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let v3 = Clone::clone((&(&p).1));
  std::mem::drop(p);
  v3
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

// Rocq: Tsp.tsp_implem.zofi
pub fn zofi(i: u64) -> Rc<BigInt> {
  let v5 = to_Z(i);
  v5
}

// Rocq: Corelib.Floats.PrimFloat.normfr_mantissa
pub fn normfr_mantissa(v0: f64) -> u64 {
  rocq_float64::normfr_mantissa(v0)
}

// Rocq: Corelib.Floats.PrimFloat.ltb
// Variant: uncurried
pub fn ltb_1(v0: f64, v1: f64) -> bool {
  rocq_float64::ltb(v0, v1)
}

// Rocq: Tsp.tsp_implem.fex_raw
pub fn fex_raw(f: f64) -> (Rc<BigInt>, Rc<BigInt>) {
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

// Rocq: Corelib.BinNums.IntDef.Z.eqb
// Variant: uncurried
pub fn eqb_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::equal(v0, v1)
}

// Rocq: Tsp.tsp_implem.fex
pub fn fex(f: f64) -> (Rc<BigInt>, Rc<BigInt>) {
  let v4 = fex_raw(f);
  match v4 {
    (v6, v8) => {
      let e = &v6;
      let v12 = rocq_bigint::zero();
      let v14 = Rc::clone(e);
      match eqb_1(v14, v12) {
        true => {
          std::mem::drop(v8);
          std::mem::drop(v6);
          let v19 = rocq_bigint::zero();
          let v20 = rocq_bigint::zero();
          (v19, v20)
        },
        false => {
          (v6, v8)
        },
      }
    },
  }
}

// Rocq: Tsp.tsp_implem.expo_step
// Variant: uncurried
pub fn expo_step(x: Rc<Array<f64>>, y: Rc<Array<f64>>, i: u64, E: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = &x;
  let v11 = rocq_array::get::<f64>(&v8, i);
  std::mem::drop(x);
  let v17 = snd::<Rc<BigInt>, Rc<BigInt>>(fex(v11));
  let v20 = &y;
  let v23 = rocq_array::get::<f64>(&v20, i);
  std::mem::drop(y);
  let v29 = snd::<Rc<BigInt>, Rc<BigInt>>(fex(v23));
  let v34 = min(v17, v29);
  let v40 = min(E, v34);
  v40
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
}

// Rocq: Corelib.BinNums.IntDef.Z.mul
// Variant: uncurried
pub fn mul(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::mul(v0, v1);
  v8
}

// Rocq: Corelib.BinNums.IntDef.Z.shiftl
// Variant: uncurried
pub fn shiftl(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::shiftl(v0, v1);
  v8
}

// Rocq: Tsp.tsp_implem.dal
// Variant: borrowed, uncurried
pub fn dal(d: (Rc<BigInt>, Rc<BigInt>), e: &Rc<BigInt>) -> Rc<BigInt> {
  let d_1 = d;
  let v6 = Clone::clone(&d_1);
  let v8 = fst::<Rc<BigInt>, Rc<BigInt>>(v6);
  let v14 = snd::<Rc<BigInt>, Rc<BigInt>>(d_1);
  let v18 = Rc::clone(e);
  let v19 = sub(v14, v18);
  let v25 = shiftl(v8, v19);
  v25
}

// Rocq: Tsp.tsp_implem.grid_step
// Variant: borrowed, uncurried
pub fn grid_step(x: &Rc<Array<f64>>, y: &Rc<Array<f64>>, E: &Rc<BigInt>, i: u64, st: (Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>)) -> (Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>) {
  let i_1 = i;
  let st_1 = st;
  let v9 = Clone::clone(&st_1);
  let v11 = fst::<Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>>(v9);
  let v13 = x;
  let v25 = dal(fex(rocq_array::get::<f64>(&v13, i_1)), E);
  let v32 = rocq_array::set::<Rc<BigInt>>(v11, i_1, v25);
  let v36 = snd::<Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>>(st_1);
  let v38 = y;
  let v50 = dal(fex(rocq_array::get::<f64>(&v38, i_1)), E);
  let v57 = rocq_array::set::<Rc<BigInt>>(v36, i_1, v50);
  (v32, v57)
}

// Rocq: Tsp.tsp_implem.Dz
// Variant: uncurried
pub fn Dz_owned(GX: Rc<Array<Rc<BigInt>>>, GY: Rc<Array<Rc<BigInt>>>, a: u64, b: u64) -> Rc<BigInt> {
  let v5 = &GX;
  let v8 = rocq_array::get::<Rc<BigInt>>(&v5, a);
  let v9 = &GX;
  let v12 = rocq_array::get::<Rc<BigInt>>(&v9, b);
  std::mem::drop(GX);
  let dx = sub(v8, v12);
  let v19 = &GY;
  let v22 = rocq_array::get::<Rc<BigInt>>(&v19, a);
  let v23 = &GY;
  let v26 = rocq_array::get::<Rc<BigInt>>(&v23, b);
  std::mem::drop(GY);
  let dy = sub(v22, v26);
  let v36 = Rc::clone(&dx);
  let v39 = mul(v36, dx);
  let v43 = Rc::clone(&dy);
  let v46 = mul(v43, dy);
  let v52 = add(v39, v46);
  v52
}

// Rocq: Tsp.tsp_implem.Dz
// Variant: borrowed, uncurried
pub fn Dz(GX: &Rc<Array<Rc<BigInt>>>, GY: &Rc<Array<Rc<BigInt>>>, a: u64, b: u64) -> Rc<BigInt> {
  let a_1 = a;
  let b_1 = b;
  let v7 = GX;
  let v10 = rocq_array::get::<Rc<BigInt>>(&v7, a_1);
  let v11 = GX;
  let v14 = rocq_array::get::<Rc<BigInt>>(&v11, b_1);
  let dx = sub(v10, v14);
  let v21 = GY;
  let v24 = rocq_array::get::<Rc<BigInt>>(&v21, a_1);
  let v25 = GY;
  let v28 = rocq_array::get::<Rc<BigInt>>(&v25, b_1);
  let dy = sub(v24, v28);
  let v38 = Rc::clone(&dx);
  let v41 = mul(v38, dx);
  let v45 = Rc::clone(&dy);
  let v48 = mul(v45, dy);
  let v54 = add(v41, v48);
  v54
}

// Rocq: Tsp.tsp_implem.key_init
// Variant: uncurried
pub fn key_init(GX: Rc<Array<Rc<BigInt>>>, GY: Rc<Array<Rc<BigInt>>>, w: u64, K: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let v15 = Dz_owned(GX, GY, 0u64, w);
  rocq_array::set::<Rc<BigInt>>(K, w, v15)
}

// Rocq: Corelib.BinNums.IntDef.Z.ltb
// Variant: uncurried
pub fn ltb_2(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::lt(v0, v1)
}

// Rocq: Tsp.tsp_implem.amin_step
// Variant: borrowed, uncurried
pub fn amin_step(n: u64, rk: &Rc<Array<u64>>, K: &Rc<Array<Rc<BigInt>>>, w: u64, b: u64) -> u64 {
  let n_1 = n;
  let w_1 = w;
  let b_1 = b;
  let v9 = rk;
  let v13 = rocq_array::get::<u64>(&v9, w_1);
  match eqb(v13, n_1) {
    true => {
      match eqb(b_1, n_1) {
        true => {
          w_1
        },
        false => {
          let v29 = K;
          let v32 = rocq_array::get::<Rc<BigInt>>(&v29, w_1);
          let v33 = K;
          let v36 = rocq_array::get::<Rc<BigInt>>(&v33, b_1);
          match ltb_2(v32, v36) {
            true => {
              w_1
            },
            false => {
              b_1
            },
          }
        },
      }
    },
    false => {
      b_1
    },
  }
}

// Rocq: Tsp.tsp_implem.relax_step
// Variant: borrowed, uncurried
pub fn relax_step(GX: &Rc<Array<Rc<BigInt>>>, GY: &Rc<Array<Rc<BigInt>>>, n: u64, rk: &Rc<Array<u64>>, v: u64, w: u64, st: (Rc<Array<Rc<BigInt>>>, Rc<Array<u64>>)) -> (Rc<Array<Rc<BigInt>>>, Rc<Array<u64>>) {
  let n_1 = n;
  let v_1 = v;
  let w_1 = w;
  let st_1 = st;
  let v12 = rk;
  let v16 = rocq_array::get::<u64>(&v12, w_1);
  match eqb(v16, n_1) {
    true => {
      let d = Dz(GX, GY, v_1, w_1);
      let v35 = Clone::clone(&st_1);
      let v37 = fst::<Rc<Array<Rc<BigInt>>>, Rc<Array<u64>>>(v35);
      let v38 = &v37;
      let v41 = rocq_array::get::<Rc<BigInt>>(&v38, w_1);
      let v44 = Rc::clone(&d);
      match ltb_2(v44, v41) {
        true => {
          std::mem::drop(v37);
          let v51 = Clone::clone(&st_1);
          let v54 = fst::<Rc<Array<Rc<BigInt>>>, Rc<Array<u64>>>(v51);
          let v60 = rocq_array::set::<Rc<BigInt>>(v54, w_1, d);
          let v65 = snd::<Rc<Array<Rc<BigInt>>>, Rc<Array<u64>>>(st_1);
          let v71 = rocq_array::set::<u64>(v65, w_1, v_1);
          (v60, v71)
        },
        false => {
          std::mem::drop(v37);
          std::mem::drop(d);
          st_1
        },
      }
    },
    false => {
      st_1
    },
  }
}

// Rocq: Tsp.tsp_implem.prim_step
// Variant: borrowed, uncurried
pub fn prim_step(GX: &Rc<Array<Rc<BigInt>>>, GY: &Rc<Array<Rc<BigInt>>>, n: u64, k: u64, st: ((Rc<Array<u64>>, Rc<Array<Rc<BigInt>>>), Rc<Array<u64>>)) -> ((Rc<Array<u64>>, Rc<Array<Rc<BigInt>>>), Rc<Array<u64>>) {
  let k_1 = k;
  let st_1 = st;
  let v11 = Clone::clone(&st_1);
  let rk = fst::<Rc<Array<u64>>, Rc<Array<Rc<BigInt>>>>(fst::<(Rc<Array<u64>>, Rc<Array<Rc<BigInt>>>), Rc<Array<u64>>>(v11));
  let v18 = {
    move |_v19: u64, _v20: u64| -> bool {
      true
    }
  };
  let v25: Rc<dyn Fn(u64, u64) -> bool> = Rc::new(v18);
  let v26: Rc<dyn Fn(u64, u64) -> bool> = v25;
  let v30 = Clone::clone(&st_1);
  let v35 = snd::<Rc<Array<u64>>, Rc<Array<Rc<BigInt>>>>(fst::<(Rc<Array<u64>>, Rc<Array<Rc<BigInt>>>), Rc<Array<u64>>>(v30));
  let v40 = Rc::clone(&rk);
  let v43 = {
    let __anf_capture_44 = n;
    move |v50: u64, v51: u64| -> u64 {
      let v53 = Clone::clone(&__anf_capture_44);
      amin_step(v53, &v40, &v35, v50, v51)
    }
  };
  let v64: Rc<dyn Fn(u64, u64) -> u64> = Rc::new(v43);
  let v = loop_::<u64>(n, v26, v64, 0u64, n);
  let rk_ = rocq_array::set::<u64>(rk, v, k_1);
  let v87 = {
    move |_v88: u64, v89: (Rc<Array<Rc<BigInt>>>, Rc<Array<u64>>)| -> bool {
      std::mem::drop(v89);
      true
    }
  };
  let v94: Rc<dyn Fn(u64, (Rc<Array<Rc<BigInt>>>, Rc<Array<u64>>)) -> bool> = Rc::new(v87);
  let v95: Rc<dyn Fn(u64, (Rc<Array<Rc<BigInt>>>, Rc<Array<u64>>)) -> bool> = v94;
  let v98 = Rc::clone(GX);
  let v101 = Rc::clone(GY);
  let v106 = Rc::clone(&rk_);
  let v109 = {
    let __anf_capture_114 = n;
    let __anf_capture_118 = v;
    move |v120: u64, v121: (Rc<Array<Rc<BigInt>>>, Rc<Array<u64>>)| -> (Rc<Array<Rc<BigInt>>>, Rc<Array<u64>>) {
      let GX = &v98;
      let GY = &v101;
      let n = &__anf_capture_114;
      let rk_ = &v106;
      let v134 = relax_step(GX, GY, Clone::clone(n), rk_, Clone::clone(&__anf_capture_118), v120, v121);
      v134
    }
  };
  let v137: Rc<dyn Fn(u64, (Rc<Array<Rc<BigInt>>>, Rc<Array<u64>>)) -> (Rc<Array<Rc<BigInt>>>, Rc<Array<u64>>)> = Rc::new(v109);
  let v144 = Clone::clone(&st_1);
  let v149 = snd::<Rc<Array<u64>>, Rc<Array<Rc<BigInt>>>>(fst::<(Rc<Array<u64>>, Rc<Array<Rc<BigInt>>>), Rc<Array<u64>>>(v144));
  let v153 = snd::<(Rc<Array<u64>>, Rc<Array<Rc<BigInt>>>), Rc<Array<u64>>>(st_1);
  let KP = loop_::<(Rc<Array<Rc<BigInt>>>, Rc<Array<u64>>)>(n, v95, v137, 0u64, (v149, v153));
  let v173 = Clone::clone(&KP);
  let v175 = fst::<Rc<Array<Rc<BigInt>>>, Rc<Array<u64>>>(v173);
  let v180 = (rk_, v175);
  let v185 = snd::<Rc<Array<Rc<BigInt>>>, Rc<Array<u64>>>(KP);
  (v180, v185)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul_1(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Tsp.tsp_implem.ds_sp
pub fn ds_sp(s: ((((Rc<Array<u64>>, Rc<Array<u64>>), u64), Rc<Array<u64>>), u64)) -> u64 {
  snd::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(fst::<((Rc<Array<u64>>, Rc<Array<u64>>), u64), Rc<Array<u64>>>(fst::<(((Rc<Array<u64>>, Rc<Array<u64>>), u64), Rc<Array<u64>>), u64>(s)))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub_1(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
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

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  match b {
    true => {
      false
    },
    false => {
      true
    },
  }
}

// Rocq: Tsp.tsp_implem.dfs_step
// Variant: borrowed, uncurried
pub fn dfs_step(n: u64, P: &Rc<Array<u64>>, _j: u64, s: ((((Rc<Array<u64>>, Rc<Array<u64>>), u64), Rc<Array<u64>>), u64)) -> ((((Rc<Array<u64>>, Rc<Array<u64>>), u64), Rc<Array<u64>>), u64) {
  let n_1 = n;
  let s_1 = s;
  match s_1 {
    (v7, v9) => {
      match v7 {
        (v12, v14) => {
          match v12 {
            (v17, v19) => {
              match v17 {
                (v22, v24) => {
                  let stk = &v22;
                  let it = &v24;
                  let v36 = sub_1(v19, 1u64);
                  let u = rocq_array::get::<u64>(&it, v36);
                  let c = rocq_array::get::<u64>(&stk, u);
                  match ltb(c, n_1) {
                    true => {
                      let it_ = rocq_array::set::<u64>(v22, u, add_1(c, 1u64));
                      let v66 = P;
                      let v74 = eqb(rocq_array::get::<u64>(&v66, c), u);
                      let v86 = negb(eqb(c, 0u64));
                      match andb(v74, v86) {
                        true => {
                          let v99 = rocq_array::set::<u64>(v24, v19, c);
                          let v118 = ((it_, v99), add_1(v19, 1u64));
                          let v126 = rocq_array::set::<u64>(v14, v9, c);
                          ((v118, v126), add_1(v9, 1u64))
                        },
                        false => {
                          ((((it_, v24), v19), v14), v9)
                        },
                      }
                    },
                    false => {
                      ((((v22, v24), sub_1(v19, 1u64)), v14), v9)
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

// Rocq: Tsp.tsp_implem.ds_out
pub fn ds_out(s: ((((Rc<Array<u64>>, Rc<Array<u64>>), u64), Rc<Array<u64>>), u64)) -> Rc<Array<u64>> {
  snd::<((Rc<Array<u64>>, Rc<Array<u64>>), u64), Rc<Array<u64>>>(fst::<(((Rc<Array<u64>>, Rc<Array<u64>>), u64), Rc<Array<u64>>), u64>(s))
}

// Rocq: Tsp.tsp_implem.tsp_impl
// Variant: uncurried
pub fn tsp_impl(x: Rc<Array<f64>>, y: Rc<Array<f64>>) -> Rc<Array<u64>> {
  let v2 = &x;
  let n = rocq_array::length::<f64>(&v2);
  let v5 = {
    move |_v6: u64, v7: Rc<BigInt>| -> bool {
      std::mem::drop(v7);
      true
    }
  };
  let v12: Rc<dyn Fn(u64, Rc<BigInt>) -> bool> = Rc::new(v5);
  let v13: Rc<dyn Fn(u64, Rc<BigInt>) -> bool> = v12;
  let v16 = Rc::clone(&x);
  let v19 = Rc::clone(&y);
  let v20 = {
    move |v25: u64, v26: Rc<BigInt>| -> Rc<BigInt> {
      let v29 = Rc::clone(&v16);
      let v31 = Rc::clone(&v19);
      let v37 = expo_step(v29, v31, v25, v26);
      v37
    }
  };
  let v39: Rc<dyn Fn(u64, Rc<BigInt>) -> Rc<BigInt>> = Rc::new(v20);
  let v43 = rocq_bigint::zero();
  let E = loop_::<Rc<BigInt>>(n, v13, v39, 0u64, v43);
  let v56 = {
    move |_v57: u64, v58: (Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>)| -> bool {
      std::mem::drop(v58);
      true
    }
  };
  let v63: Rc<dyn Fn(u64, (Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>)) -> bool> = Rc::new(v56);
  let v64: Rc<dyn Fn(u64, (Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>)) -> bool> = v63;
  let v71 = {
    let __anf_capture_72 = x;
    let __anf_capture_74 = y;
    move |v78: u64, v79: (Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>)| -> (Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>) {
      let x = &__anf_capture_72;
      let y = &__anf_capture_74;
      let E = &E;
      let v88 = grid_step(x, y, E, v78, v79);
      v88
    }
  };
  let v91: Rc<dyn Fn(u64, (Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>)) -> (Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>)> = Rc::new(v71);
  let v95 = rocq_bigint::zero();
  let v100 = rocq_array::make::<Rc<BigInt>>(n, v95);
  let v101 = rocq_bigint::zero();
  let v106 = rocq_array::make::<Rc<BigInt>>(n, v101);
  let G = loop_::<(Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>)>(n, v64, v91, 0u64, (v100, v106));
  let v126 = Clone::clone(&G);
  let GX = fst::<Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>>(v126);
  let GY = snd::<Rc<Array<Rc<BigInt>>>, Rc<Array<Rc<BigInt>>>>(G);
  let v134 = {
    move |_v135: u64, v136: Rc<Array<Rc<BigInt>>>| -> bool {
      std::mem::drop(v136);
      true
    }
  };
  let v141: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = Rc::new(v134);
  let v142: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> bool> = v141;
  let v145 = Rc::clone(&GX);
  let v148 = Rc::clone(&GY);
  let v149 = {
    move |v154: u64, v155: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let v158 = Rc::clone(&v145);
      let v160 = Rc::clone(&v148);
      key_init(v158, v160, v154, v155)
    }
  };
  let v168: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new(v149);
  let v172 = rocq_bigint::zero();
  let v177 = rocq_array::make::<Rc<BigInt>>(n, v172);
  let K0 = loop_::<Rc<Array<Rc<BigInt>>>>(n, v142, v168, 0u64, v177);
  let v193 = rocq_array::make::<u64>(n, n);
  let rk0 = rocq_array::set::<u64>(v193, 0u64, 0u64);
  let v206 = {
    move |_v207: u64, v208: ((Rc<Array<u64>>, Rc<Array<Rc<BigInt>>>), Rc<Array<u64>>)| -> bool {
      std::mem::drop(v208);
      true
    }
  };
  let v213: Rc<dyn Fn(u64, ((Rc<Array<u64>>, Rc<Array<Rc<BigInt>>>), Rc<Array<u64>>)) -> bool> = Rc::new(v206);
  let v214: Rc<dyn Fn(u64, ((Rc<Array<u64>>, Rc<Array<Rc<BigInt>>>), Rc<Array<u64>>)) -> bool> = v213;
  let v221 = {
    let __anf_capture_222 = GX;
    let __anf_capture_224 = GY;
    let __anf_capture_226 = n;
    move |v228: u64, v229: ((Rc<Array<u64>>, Rc<Array<Rc<BigInt>>>), Rc<Array<u64>>)| -> ((Rc<Array<u64>>, Rc<Array<Rc<BigInt>>>), Rc<Array<u64>>) {
      let GX = &__anf_capture_222;
      let GY = &__anf_capture_224;
      let v239 = prim_step(GX, GY, Clone::clone(&__anf_capture_226), v228, v229);
      v239
    }
  };
  let v242: Rc<dyn Fn(u64, ((Rc<Array<u64>>, Rc<Array<Rc<BigInt>>>), Rc<Array<u64>>)) -> ((Rc<Array<u64>>, Rc<Array<Rc<BigInt>>>), Rc<Array<u64>>)> = Rc::new(v221);
  let v250 = (rk0, K0);
  let v258 = rocq_array::make::<u64>(n, 0u64);
  let PR = loop_::<((Rc<Array<u64>>, Rc<Array<Rc<BigInt>>>), Rc<Array<u64>>)>(n, v214, v242, 1u64, (v250, v258));
  let v289 = add_1(mul_1(n, n), n);
  let v296 = add_1(v289, 1u64);
  let v297 = {
    move |_v298: u64, s: ((((Rc<Array<u64>>, Rc<Array<u64>>), u64), Rc<Array<u64>>), u64)| -> bool {
      ltb(0u64, ds_sp(s))
    }
  };
  let v314: Rc<dyn Fn(u64, ((((Rc<Array<u64>>, Rc<Array<u64>>), u64), Rc<Array<u64>>), u64)) -> bool> = Rc::new(v297);
  let v315: Rc<dyn Fn(u64, ((((Rc<Array<u64>>, Rc<Array<u64>>), u64), Rc<Array<u64>>), u64)) -> bool> = v314;
  let v319 = snd::<(Rc<Array<u64>>, Rc<Array<Rc<BigInt>>>), Rc<Array<u64>>>(PR);
  let v324 = {
    let __anf_capture_325 = n;
    move |v329: u64, v330: ((((Rc<Array<u64>>, Rc<Array<u64>>), u64), Rc<Array<u64>>), u64)| -> ((((Rc<Array<u64>>, Rc<Array<u64>>), u64), Rc<Array<u64>>), u64) {
      let n = &__anf_capture_325;
      let v327 = &v319;
      let v339 = dfs_step(Clone::clone(n), v327, v329, v330);
      v339
    }
  };
  let v342: Rc<dyn Fn(u64, ((((Rc<Array<u64>>, Rc<Array<u64>>), u64), Rc<Array<u64>>), u64)) -> ((((Rc<Array<u64>>, Rc<Array<u64>>), u64), Rc<Array<u64>>), u64)> = Rc::new(v324);
  let v352 = rocq_array::make::<u64>(n, 0u64);
  let v359 = rocq_array::make::<u64>(n, 0u64);
  let v372 = ((v352, v359), 1u64);
  let v380 = rocq_array::make::<u64>(n, 0u64);
  let s = loop_::<((((Rc<Array<u64>>, Rc<Array<u64>>), u64), Rc<Array<u64>>), u64)>(v296, v315, v342, 0u64, ((v372, v380), 1u64));
  ds_out(s)
}

// Rocq: Tsp.tsp_implem.tsp_impl
pub fn tsp_impl_curried(x: Rc<Array<f64>>) -> Rc<dyn Fn(Rc<Array<f64>>) -> Rc<Array<u64>>> {
  let v3 = {
    move |y: Rc<Array<f64>>| -> Rc<Array<u64>> {
      let v9 = Rc::clone(&x);
      tsp_impl(v9, y)
    }
  };
  let v15: Rc<dyn Fn(Rc<Array<f64>>) -> Rc<Array<u64>>> = Rc::new(v3);
  v15
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

pub fn run() -> Rc<dyn Fn(Rc<Array<f64>>, Rc<Array<f64>>) -> Rc<Array<u64>>> {
  let v0: Rc<dyn Fn(Rc<Array<f64>>, Rc<Array<f64>>) -> Rc<Array<u64>>> = __rocq_global_997.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_997: Rc<dyn Fn(Rc<Array<f64>>, Rc<Array<f64>>) -> Rc<Array<u64>>> = tsp(); }
std::thread_local! { static __rocq_global_1000: Rc<dyn Fn(Rc<Array<f64>>) -> Rc<dyn Fn(Rc<Array<f64>>) -> Rc<Array<u64>>>> = tsp_curried(); }