// Generated from OwnedANF. This printer is not verified.
#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;
#[allow(unused_imports)] use rocq_bigint::BigInt;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub struct sig<A: 'static> {
  pub x: A,
}

impl<A: Clone + 'static> Clone for sig<A> {
  fn clone(&self) -> Self {
    match self {
      sig { x: __field0 } => sig { x: Clone::clone(__field0) },
    }
  }
}

pub enum sumor<A: 'static> {
  inleft(A),
  inright,
}

impl<A: Clone + 'static> Clone for sumor<A> {
  fn clone(&self) -> Self {
    match self {
      sumor::inleft(__field0) => sumor::inleft(Clone::clone(__field0)),
      sumor::inright => sumor::inright,
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

pub struct Q {
  pub Qnum: Rc<BigInt>,
  pub Qden: Rc<BigInt>,
}

impl Clone for Q {
  fn clone(&self) -> Self {
    match self {
      Q { Qnum: __field0, Qden: __field1 } => Q { Qnum: Clone::clone(__field0), Qden: Clone::clone(__field1) },
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

pub type sint = u64;

pub type uint = u64;

pub type SState = ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>);

// Rocq: Roadtimes.roadtimes_implem.INF
pub fn INF() -> u64 {
  1073741824u64
}

// Rocq: Roadtimes.roadtimes_implem.two36
pub fn two36() -> u64 {
  68719476736u64
}

// Rocq: Corelib.Floats.PrimFloat.zero
pub fn zero() -> f64 {
  f64::from_bits(0u64)
}

// Rocq: Roadtimes.roadtimes_implem.roadtimes
// Variant: uncurried
pub fn roadtimes() -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<(f64, f64)>>> {
  let v0: fn(Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<(f64, f64)>> = roadtimes_impl;
  let v1: Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<(f64, f64)>>> = Rc::new(v0);
  v1
}

// Rocq: Roadtimes.roadtimes_implem.roadtimes
pub fn roadtimes_curried() -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<(f64, f64)>>>>>>>> {
  let v0: fn(Rc<Array<Rc<Array<u64>>>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<(f64, f64)>>>>>>> = roadtimes_impl_curried;
  let v1: Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<(f64, f64)>>>>>>>> = Rc::new(v0);
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

// Rocq: Roadtimes.roadtimes_implem.bdec
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

// Rocq: Roadtimes.roadtimes_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Roadtimes.roadtimes_implem.wloop (local: wloop)
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

// Rocq: Roadtimes.roadtimes_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop_1::<St>(hi, cont, f, i, s)
}

// Rocq: Roadtimes.roadtimes_implem.forl
// Variant: uncurried
pub fn forl<St: Clone + 'static>(lo: u64, hi: u64, f: Rc<dyn Fn(u64, St) -> St>, s: St) -> St {
  let v5 = {
    move |_v6: u64, v7: St| -> bool {
      std::mem::drop(v7);
      true
    }
  };
  let v12: Rc<dyn Fn(u64, St) -> bool> = Rc::new(v5);
  loop_::<St>(hi, v12, f, lo, s)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Roadtimes.roadtimes_implem.fill2
// Variant: uncurried
pub fn fill2(n: u64, g: Rc<dyn Fn(u64, u64) -> u64>, A: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v5 = 0u64;
  let v10 = {
    let __anf_capture_13 = n;
    move |i: u64, A: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let g = &g;
      let n = &__anf_capture_13;
      let v19 = 0u64;
      let v21 = Clone::clone(n);
      let v22: Rc<dyn Fn(u64, u64) -> u64> = Rc::clone(g);
      let v26 = {
        move |j: u64, A: Rc<Array<u64>>| -> Rc<Array<u64>> {
          let n = &v21;
          let g = &v22;
          let v46 = add_1(mul(Clone::clone(&i), Clone::clone(n)), j);
          let v51 = g(Clone::clone(&i), j);
          rocq_array::set::<u64>(A, v46, v51)
        }
      };
      let v61: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v26);
      let v66 = Clone::clone(n);
      forl::<Rc<Array<u64>>>(v19, v66, v61, A)
    }
  };
  let v74: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v10);
  forl::<Rc<Array<u64>>>(v5, n, v74, A)
}

// Rocq: Roadtimes.roadtimes_implem.flatten
// Variant: uncurried
pub fn flatten(n: u64, x: Rc<Array<Rc<Array<u64>>>>) -> Rc<Array<u64>> {
  let v5 = {
    move |i: u64, j: u64| -> u64 {
      let x = &x;
      let v11 = Rc::clone(x);
      let v15 = rocq_array::get::<Rc<Array<u64>>>(&v11, i);
      std::mem::drop(v11);
      let v16 = &v15;
      let v19 = rocq_array::get::<u64>(&v16, j);
      std::mem::drop(v15);
      v19
    }
  };
  let v22: Rc<dyn Fn(u64, u64) -> u64> = Rc::new(v5);
  let v36 = rocq_array::make::<u64>(mul(n, n), 0u64);
  fill2(n, v22, v36)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb
// Variant: uncurried
pub fn ltsb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltsb(v0, v1)
}

// Rocq: Roadtimes.roadtimes_implem.isroad
pub fn isroad(e: u64) -> bool {
  ltsb(0u64, e)
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

// Rocq: Roadtimes.roadtimes_implem.fw_cell
// Variant: uncurried
pub fn fw_cell(n: u64, k: u64, i: u64, j: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v7 = Clone::clone(&st);
  let D = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(v7);
  let v12 = Clone::clone(&st);
  let X = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(v12);
  let v27 = add_1(mul(i, n), k);
  let v28 = &D;
  let v31 = rocq_array::get::<u64>(&v28, v27);
  let v43 = add_1(mul(k, n), j);
  let v44 = &D;
  let v47 = rocq_array::get::<u64>(&v44, v43);
  let a = add_1(v31, v47);
  let v65 = add_1(mul(i, n), j);
  let v66 = &D;
  let v69 = rocq_array::get::<u64>(&v66, v65);
  match ltb(a, v69) {
    true => {
      std::mem::drop(st);
      let v94 = rocq_array::set::<u64>(D, add_1(mul(i, n), j), a);
      let v106 = add_1(mul(i, n), j);
      let v118 = add_1(mul(i, n), k);
      let v119 = &X;
      let v122 = rocq_array::get::<u64>(&v119, v118);
      let v129 = rocq_array::set::<u64>(X, v106, v122);
      (v94, v129)
    },
    false => {
      std::mem::drop(X);
      std::mem::drop(D);
      st
    },
  }
}

// Rocq: Roadtimes.roadtimes_implem.fw_iter
// Variant: uncurried
pub fn fw_iter(n: u64, k: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v5 = 0u64;
  let v10 = {
    let __anf_capture_13 = n;
    move |i: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
      let k = &k;
      let n = &__anf_capture_13;
      let v19 = 0u64;
      let v21 = Clone::clone(n);
      let v23 = Clone::clone(k);
      let v26 = {
        move |j: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
          let v37 = Clone::clone(&v21);
          let v39 = Clone::clone(&v23);
          let v41 = Clone::clone(&i);
          fw_cell(v37, v39, v41, j, st)
        }
      };
      let v49: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new(v26);
      let v54 = Clone::clone(n);
      forl::<(Rc<Array<u64>>, Rc<Array<u64>>)>(v19, v54, v49, st)
    }
  };
  let v62: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new(v10);
  forl::<(Rc<Array<u64>>, Rc<Array<u64>>)>(v5, n, v62, st)
}

// Rocq: Roadtimes.roadtimes_implem.fw
// Variant: uncurried
pub fn fw(n: u64, W: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v7 = {
    let __anf_capture_8 = n;
    move |i: u64, j: u64| -> u64 {
      let n = &__anf_capture_8;
      let W = &W;
      match eqb(i, j) {
        true => {
          0u64
        },
        false => {
          let v38 = add_1(mul(i, Clone::clone(n)), j);
          let v41 = rocq_array::get::<u64>(&W, v38);
          match isroad(v41) {
            true => {
              let v57 = add_1(mul(i, Clone::clone(n)), j);
              rocq_array::get::<u64>(&W, v57)
            },
            false => {
              __rocq_global_461
            },
          }
        },
      }
    }
  };
  let v71: Rc<dyn Fn(u64, u64) -> u64> = Rc::new(v7);
  let v85 = rocq_array::make::<u64>(mul(n, n), 0u64);
  let D0 = fill2(n, v71, v85);
  let v94 = {
    move |_i: u64, j: u64| -> u64 {
      j
    }
  };
  let v99: Rc<dyn Fn(u64, u64) -> u64> = Rc::new(v94);
  let v113 = rocq_array::make::<u64>(mul(n, n), 0u64);
  let X0 = fill2(n, v99, v113);
  let v123 = 0u64;
  let v126 = {
    let __anf_capture_127 = n;
    move |k: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
      let v133 = Clone::clone(&__anf_capture_127);
      fw_iter(v133, k, st)
    }
  };
  let v141: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new(v126);
  forl::<(Rc<Array<u64>>, Rc<Array<u64>>)>(v123, n, v141, (D0, X0))
}

// Rocq: Roadtimes.roadtimes_implem.scan_roads
// Variant: uncurried
pub fn scan_roads(n: u64, W: Rc<Array<u64>>) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let v4 = 0u64;
  let v10 = mul(n, n);
  let v13 = {
    move |p: u64, st: ((Rc<Array<u64>>, Rc<Array<u64>>), u64)| -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
      let W = &W;
      let v21 = Clone::clone(&st);
      let I = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(v21));
      let v30 = Clone::clone(&st);
      let P = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(v30));
      let v38 = Clone::clone(&st);
      let e = snd::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(v38);
      let v45 = rocq_array::get::<u64>(&W, p);
      match isroad(v45) {
        true => {
          std::mem::drop(st);
          let v55 = rocq_array::set::<u64>(I, p, e);
          let v62 = rocq_array::set::<u64>(P, e, p);
          ((v55, v62), add_1(e, 1u64))
        },
        false => {
          std::mem::drop(P);
          std::mem::drop(I);
          st
        },
      }
    }
  };
  let v90: Rc<dyn Fn(u64, ((Rc<Array<u64>>, Rc<Array<u64>>), u64)) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64)> = Rc::new(v13);
  let v104 = rocq_array::make::<u64>(mul(n, n), 0u64);
  let v117 = rocq_array::make::<u64>(mul(n, n), 0u64);
  forl::<((Rc<Array<u64>>, Rc<Array<u64>>), u64)>(v4, v10, v90, ((v104, v117), 0u64))
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Roadtimes.roadtimes_implem.guard
// Variant: uncurried
pub fn guard(E: u64, R: u64) -> bool {
  let v31 = andb(leb(1u64, add_1(E, R)), leb(E, 2048u64));
  let v44 = andb(v31, leb(R, 2048u64));
  let v52 = add_1(E, R);
  let v60 = add_1(E, R);
  let v65 = add_1(E, v60);
  andb(v44, leb(mul(v52, add_1(v65, 1u64)), 4194303u64))
}

// Rocq: Stdlib.QArith.QArith_base.inject_Z
pub fn inject_Z(x: Rc<BigInt>) -> Rc<Q> {
  let v1 = rocq_bigint::one();
  Rc::new(Q { Qnum: x, Qden: v1 })
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

// Rocq: Corelib.BinNums.PosDef.Pos.mul
// Variant: uncurried
pub fn mul_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::mul(v0, v1);
  v8
}

// Rocq: Corelib.BinNums.IntDef.Z.mul
// Variant: uncurried
pub fn mul_2(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::mul(v0, v1);
  v8
}

// Rocq: Roadtimes.roadtimes_implem.zofi_rec
pub fn zofi_rec_1(i: u64) -> Rc<BigInt> {
  let v9 = zofi_rec(i, ());
  v9
}

// Rocq: Roadtimes.roadtimes_implem.zofi_rec (local: zofi_rec)
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

// Rocq: Roadtimes.roadtimes_implem.zofi
pub fn zofi(i: u64) -> Rc<BigInt> {
  let v5 = zofi_rec_1(i);
  v5
}

// Rocq: Roadtimes.roadtimes_implem.zofs
pub fn zofs(i: u64) -> Rc<BigInt> {
  let v3 = 4611686018427387904u64;
  let v222 = match ltb(i, v3) {
    true => {
      let v14 = zofi(i);
      v14
    },
    false => {
      let v20 = zofi(i);
      let v22 = rocq_bigint::one();
      let v25 = rocq_bigint::twice(v22);
      let v28 = rocq_bigint::twice(v25);
      let v31 = rocq_bigint::twice(v28);
      let v34 = rocq_bigint::twice(v31);
      let v37 = rocq_bigint::twice(v34);
      let v40 = rocq_bigint::twice(v37);
      let v43 = rocq_bigint::twice(v40);
      let v46 = rocq_bigint::twice(v43);
      let v49 = rocq_bigint::twice(v46);
      let v52 = rocq_bigint::twice(v49);
      let v55 = rocq_bigint::twice(v52);
      let v58 = rocq_bigint::twice(v55);
      let v61 = rocq_bigint::twice(v58);
      let v64 = rocq_bigint::twice(v61);
      let v67 = rocq_bigint::twice(v64);
      let v70 = rocq_bigint::twice(v67);
      let v73 = rocq_bigint::twice(v70);
      let v76 = rocq_bigint::twice(v73);
      let v79 = rocq_bigint::twice(v76);
      let v82 = rocq_bigint::twice(v79);
      let v85 = rocq_bigint::twice(v82);
      let v88 = rocq_bigint::twice(v85);
      let v91 = rocq_bigint::twice(v88);
      let v94 = rocq_bigint::twice(v91);
      let v97 = rocq_bigint::twice(v94);
      let v100 = rocq_bigint::twice(v97);
      let v103 = rocq_bigint::twice(v100);
      let v106 = rocq_bigint::twice(v103);
      let v109 = rocq_bigint::twice(v106);
      let v112 = rocq_bigint::twice(v109);
      let v115 = rocq_bigint::twice(v112);
      let v118 = rocq_bigint::twice(v115);
      let v121 = rocq_bigint::twice(v118);
      let v124 = rocq_bigint::twice(v121);
      let v127 = rocq_bigint::twice(v124);
      let v130 = rocq_bigint::twice(v127);
      let v133 = rocq_bigint::twice(v130);
      let v136 = rocq_bigint::twice(v133);
      let v139 = rocq_bigint::twice(v136);
      let v142 = rocq_bigint::twice(v139);
      let v145 = rocq_bigint::twice(v142);
      let v148 = rocq_bigint::twice(v145);
      let v151 = rocq_bigint::twice(v148);
      let v154 = rocq_bigint::twice(v151);
      let v157 = rocq_bigint::twice(v154);
      let v160 = rocq_bigint::twice(v157);
      let v163 = rocq_bigint::twice(v160);
      let v166 = rocq_bigint::twice(v163);
      let v169 = rocq_bigint::twice(v166);
      let v172 = rocq_bigint::twice(v169);
      let v175 = rocq_bigint::twice(v172);
      let v178 = rocq_bigint::twice(v175);
      let v181 = rocq_bigint::twice(v178);
      let v184 = rocq_bigint::twice(v181);
      let v187 = rocq_bigint::twice(v184);
      let v190 = rocq_bigint::twice(v187);
      let v193 = rocq_bigint::twice(v190);
      let v196 = rocq_bigint::twice(v193);
      let v199 = rocq_bigint::twice(v196);
      let v202 = rocq_bigint::twice(v199);
      let v205 = rocq_bigint::twice(v202);
      let v208 = rocq_bigint::twice(v205);
      let v211 = rocq_bigint::twice(v208);
      let v213 = rocq_bigint::identity(v211);
      let v219 = sub(v20, v213);
      v219
    },
  };
  v222
}

// Rocq: Roadtimes.roadtimes_implem.bound_rows
// Variant: uncurried
pub fn bound_rows(E: u64, w: u64, N: u64, W: Rc<Array<u64>>, P: Rc<Array<u64>>, T: Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>> {
  let v8 = 0u64;
  let v19 = {
    let __anf_capture_24 = E;
    move |e: u64, T: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
      let P = &P;
      let W = &W;
      let E = &__anf_capture_24;
      let w = &w;
      let N = &N;
      let v35 = rocq_array::get::<u64>(&P, e);
      let u = rocq_array::get::<u64>(&W, v35);
      let v49 = add_1(mul(e, Clone::clone(w)), e);
      let v51 = rocq_bigint::one();
      let v53 = rocq_bigint::identity(v51);
      let v54 = rocq_bigint::one();
      let T_1 = rocq_array::set::<Rc<Q>>(T, v49, Rc::new(Q { Qnum: v53, Qden: v54 }));
      let v75 = mul(e, Clone::clone(w));
      let v81 = add_1(Clone::clone(E), e);
      let v86 = add_1(v75, v81);
      let v88 = rocq_bigint::one();
      let v90 = rocq_bigint::identity(v88);
      let v91 = rocq_bigint::one();
      let T_2 = rocq_array::set::<Rc<Q>>(T_1, v86, Rc::new(Q { Qnum: v90, Qden: v91 }));
      let v117 = add_1(mul(e, Clone::clone(w)), Clone::clone(N));
      let v122 = match isroad(u) {
        true => {
          let v128 = zofs(u);
          inject_Z(v128)
        },
        false => {
          let v133 = rocq_bigint::zero();
          let v134 = rocq_bigint::one();
          Rc::new(Q { Qnum: v133, Qden: v134 })
        },
      };
      rocq_array::set::<Rc<Q>>(T_2, v117, v122)
    }
  };
  let v154: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new(v19);
  forl::<Rc<Array<Rc<Q>>>>(v8, E, v154, T)
}

// Rocq: Roadtimes.roadtimes_implem.walk
// Variant: uncurried
pub fn walk_1(n: u64, d: u64, E: u64, D: Rc<Array<u64>>, X: Rc<Array<u64>>, I: Rc<Array<u64>>, cur: u64, cnt: Rc<Array<u64>>) -> Rc<Array<u64>> {
  walk(n, d, E, D, X, I, cur, cnt, ())
}

// Rocq: Roadtimes.roadtimes_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(n: u64, d: u64, E: u64, D: Rc<Array<u64>>, X: Rc<Array<u64>>, I: Rc<Array<u64>>, cur: u64, cnt: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  match eqb(cur, d) {
    true => {
      std::mem::drop(D);
      std::mem::drop(X);
      std::mem::drop(I);
      cnt
    },
    false => {
      let v29 = add_1(mul(cur, n), d);
      let v30 = &X;
      let v = rocq_array::get::<u64>(&v30, v29);
      let v47 = add_1(mul(v, n), d);
      let v48 = &D;
      let v51 = rocq_array::get::<u64>(&v48, v47);
      let v63 = add_1(mul(cur, n), d);
      let v64 = &D;
      let v67 = rocq_array::get::<u64>(&v64, v63);
      let v73 = ltb(v51, v67);
      match bdec(v73) {
        sumbool::left => {
          let v88 = add_1(mul(cur, n), v);
          let v89 = &I;
          let e = rocq_array::get::<u64>(&v89, v88);
          let v99 = match ltb(e, E) {
            true => {
              let v101 = &cnt;
              let v104 = rocq_array::get::<u64>(&v101, e);
              rocq_array::set::<u64>(cnt, e, add_1(v104, 1u64))
            },
            false => {
              cnt
            },
          };
          walk(n, d, E, D, X, I, v, v99, ())
        },
        sumbool::right => {
          std::mem::drop(I);
          std::mem::drop(D);
          std::mem::drop(X);
          cnt
        },
      }
    },
  }
}

// Rocq: Roadtimes.roadtimes_implem.route_cnt
// Variant: uncurried
pub fn route_cnt_owned(n: u64, E: u64, D: Rc<Array<u64>>, X: Rc<Array<u64>>, I: Rc<Array<u64>>, s: u64, d: u64) -> Rc<Array<u64>> {
  let v14 = rocq_array::make::<u64>(E, 0u64);
  walk_1(n, d, E, D, X, I, s, v14)
}

// Rocq: Roadtimes.roadtimes_implem.route_cnt
// Variant: borrowed, uncurried
pub fn route_cnt(n: u64, E: u64, D: &Rc<Array<u64>>, X: &Rc<Array<u64>>, I: &Rc<Array<u64>>, s: u64, d: u64) -> Rc<Array<u64>> {
  let n_1 = n;
  let E_1 = E;
  let s_1 = s;
  let d_1 = d;
  let v18 = rocq_array::make::<u64>(E_1, 0u64);
  let v27 = Rc::clone(D);
  let v30 = Rc::clone(X);
  let v33 = Rc::clone(I);
  walk_1(n_1, d_1, E_1, v27, v30, v33, s_1, v18)
}

// Rocq: Corelib.BinNums.IntDef.Z.ltb
// Variant: uncurried
pub fn ltb_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::lt(v0, v1)
}

// Rocq: Stdlib.ZArith.BinIntDef.Z.abs
pub fn abs(v0: Rc<BigInt>) -> Rc<BigInt> {
  let v5 = rocq_bigint::abs(v0);
  v5
}

// Rocq: Roadtimes.roadtimes_implem.deliv_row
// Variant: uncurried
pub fn deliv_row(n: u64, E: u64, w: u64, N: u64, D: Rc<Array<u64>>, X: Rc<Array<u64>>, I: Rc<Array<u64>>, rs: Rc<Array<u64>>, rd: Rc<Array<u64>>, rt: Rc<Array<u64>>, k: u64, T: Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>> {
  let v12 = &rs;
  let s = rocq_array::get::<u64>(&v12, k);
  std::mem::drop(rs);
  let v16 = &rd;
  let d = rocq_array::get::<u64>(&v16, k);
  std::mem::drop(rd);
  let v27 = Rc::clone(&D);
  let cnt = route_cnt_owned(n, E, v27, X, I, s, d);
  let v39 = &rt;
  let v42 = rocq_array::get::<u64>(&v39, k);
  std::mem::drop(rt);
  let v45 = zofi(v42);
  let v58 = add_1(mul(s, n), d);
  let v59 = &D;
  let v62 = rocq_array::get::<u64>(&v59, v58);
  std::mem::drop(D);
  let v65 = zofi(v62);
  let b = sub(v45, v65);
  let i = add_1(E, k);
  let v79 = 0u64;
  let v86 = Rc::clone(&b);
  let v89 = {
    let __anf_capture_90 = i;
    let __anf_capture_92 = w;
    move |e: u64, T: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
      let i = &__anf_capture_90;
      let w = &__anf_capture_92;
      let b = &v86;
      let cnt = &cnt;
      let v111 = add_1(mul(Clone::clone(i), Clone::clone(w)), e);
      let v114 = rocq_bigint::zero();
      let v116 = Rc::clone(b);
      let v144 = match ltb_1(v116, v114) {
        true => {
          let v126 = rocq_array::get::<u64>(&cnt, e);
          let v129 = zofi(v126);
          let v132 = opp(v129);
          v132
        },
        false => {
          let v138 = rocq_array::get::<u64>(&cnt, e);
          let v141 = zofi(v138);
          v141
        },
      };
      rocq_array::set::<Rc<Q>>(T, v111, inject_Z(v144))
    }
  };
  let v156: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new(v89);
  let T_1 = forl::<Rc<Array<Rc<Q>>>>(v79, E, v156, T);
  let v173 = mul(i, w);
  let v181 = add_1(E, E);
  let v185 = add_1(v181, k);
  let v190 = add_1(v173, v185);
  let v192 = rocq_bigint::one();
  let v194 = rocq_bigint::identity(v192);
  let v195 = rocq_bigint::one();
  let T_2 = rocq_array::set::<Rc<Q>>(T_1, v190, Rc::new(Q { Qnum: v194, Qden: v195 }));
  let v221 = add_1(mul(i, w), N);
  let v227 = abs(b);
  rocq_array::set::<Rc<Q>>(T_2, v221, inject_Z(v227))
}

// Rocq: Roadtimes.roadtimes_implem.build_T
// Variant: uncurried
pub fn build_T(n: u64, E: u64, R: u64, W: Rc<Array<u64>>, D: Rc<Array<u64>>, X: Rc<Array<u64>>, I: Rc<Array<u64>>, P: Rc<Array<u64>>, rs: Rc<Array<u64>>, rd: Rc<Array<u64>>, rt: Rc<Array<u64>>) -> Rc<Array<Rc<Q>>> {
  let m = add_1(E, R);
  let v23 = add_1(E, m);
  let w = add_1(v23, 1u64);
  let N = add_1(E, m);
  let v43 = mul(m, w);
  let v44 = rocq_bigint::zero();
  let v45 = rocq_bigint::one();
  let v57 = rocq_array::make::<Rc<Q>>(v43, Rc::new(Q { Qnum: v44, Qden: v45 }));
  let T = bound_rows(E, w, N, W, P, v57);
  let v73 = 0u64;
  let v94 = {
    let __anf_capture_97 = E;
    let __anf_capture_99 = w;
    let __anf_capture_101 = N;
    move |k: u64, T: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
      let v119 = Clone::clone(&n);
      let v121 = Clone::clone(&__anf_capture_97);
      let v123 = Clone::clone(&__anf_capture_99);
      let v125 = Clone::clone(&__anf_capture_101);
      let v127 = Rc::clone(&D);
      let v129 = Rc::clone(&X);
      let v131 = Rc::clone(&I);
      let v133 = Rc::clone(&rs);
      let v135 = Rc::clone(&rd);
      let v137 = Rc::clone(&rt);
      deliv_row(v119, v121, v123, v125, v127, v129, v131, v133, v135, v137, k, T)
    }
  };
  let v145: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new(v94);
  forl::<Rc<Array<Rc<Q>>>>(v73, R, v145, T)
}

// Rocq: Stdlib.QArith.QArith_base.Qnum
pub fn Qnum_owned(q: Rc<Q>) -> Rc<BigInt> {
  let v3 = Rc::clone((&(&**&q).Qnum));
  std::mem::drop(q);
  v3
}

// Rocq: Stdlib.QArith.QArith_base.Qnum
// Variant: borrowed
pub fn Qnum(q: &Rc<Q>) -> Rc<BigInt> {
  let v1 = q;
  let v4 = Rc::clone((&(&**v1).Qnum));
  v4
}

// Rocq: Stdlib.QArith.QArith_base.Qden
pub fn Qden(q: Rc<Q>) -> Rc<BigInt> {
  let v3 = Rc::clone((&(&**&q).Qden));
  std::mem::drop(q);
  v3
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub_1(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Roadtimes.roadtimes_implem.sT
pub fn sT(st: ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>)) -> Rc<Array<Rc<Q>>> {
  fst::<Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>>(fst::<(Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>>(st))
}

// Rocq: Roadtimes.roadtimes_implem.sO
pub fn sO(st: ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>)) -> Rc<Array<Rc<Q>>> {
  snd::<Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>>(fst::<(Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>>(st))
}

// Rocq: Roadtimes.roadtimes_implem.sB
pub fn sB(st: ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>)) -> Rc<Array<u64>> {
  snd::<(Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>>(st)
}

// Rocq: Roadtimes.roadtimes_implem.cart
// Variant: uncurried
pub fn cart(w: u64, A0: u64, N: u64) -> Rc<Array<Rc<Q>>> {
  let v4 = {
    move |j: u64, c: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
      let v8 = rocq_bigint::one();
      let v10 = rocq_bigint::identity(v8);
      let v11 = rocq_bigint::one();
      rocq_array::set::<Rc<Q>>(c, j, Rc::new(Q { Qnum: v10, Qden: v11 }))
    }
  };
  let v28: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new(v4);
  let v30 = rocq_bigint::zero();
  let v31 = rocq_bigint::one();
  let v43 = rocq_array::make::<Rc<Q>>(w, Rc::new(Q { Qnum: v30, Qden: v31 }));
  forl::<Rc<Array<Rc<Q>>>>(A0, N, v28, v43)
}

// Rocq: Roadtimes.roadtimes_implem.binit
// Variant: uncurried
pub fn binit(m: u64, E0: u64) -> Rc<Array<u64>> {
  let v4 = 0u64;
  let v7 = {
    move |k: u64, B: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let v14 = Clone::clone(&E0);
      let v17 = add_1(v14, k);
      rocq_array::set::<u64>(B, k, v17)
    }
  };
  let v27: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v7);
  let v35 = rocq_array::make::<u64>(m, 0u64);
  forl::<Rc<Array<u64>>>(v4, m, v27, v35)
}

// Rocq: Corelib.BinNums.IntDef.Z.eqb
// Variant: uncurried
pub fn eqb_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::equal(v0, v1)
}

// Rocq: Roadtimes.roadtimes_implem.qzerob
pub fn qzerob_owned(a: Rc<Q>) -> bool {
  let v5 = Qnum_owned(a);
  let v6 = rocq_bigint::zero();
  eqb_1(v5, v6)
}

// Rocq: Roadtimes.roadtimes_implem.qzerob
// Variant: borrowed
pub fn qzerob(a: &Rc<Q>) -> bool {
  let v5 = Qnum(a);
  let v6 = rocq_bigint::zero();
  eqb_1(v5, v6)
}

// Rocq: Corelib.BinNums.IntDef.Z.modulo
// Variant: uncurried
pub fn modulo(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::modulo(v0, v1);
  v8
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
  let v34 = match ltb_1(v5, v9) {
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

// Rocq: StdGalilei.bigint.zgcd
// Variant: uncurried
pub fn zgcd(a: Rc<BigInt>, b: Rc<BigInt>) -> Rc<BigInt> {
  let v6 = abs(a);
  let v10 = abs(b);
  let v16 = zgcd_loop_1(v6, v10);
  v16
}

// Rocq: Corelib.BinNums.IntDef.Z.div
// Variant: uncurried
pub fn div_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::div(v0, v1);
  v8
}

// Rocq: Corelib.BinNums.IntDef.Z.to_pos
pub fn to_pos(v0: Rc<BigInt>) -> Rc<BigInt> {
  let v5 = rocq_bigint::to_positive(v0);
  v5
}

// Rocq: Roadtimes.roadtimes_implem.qred
pub fn qred(q: Rc<Q>) -> Rc<Q> {
  let v4 = Rc::clone(&q);
  let n = Qnum_owned(v4);
  let v10 = Qden(q);
  let d = rocq_bigint::identity(v10);
  let v16 = Rc::clone(&n);
  let v19 = Rc::clone(&d);
  let g = zgcd(v16, v19);
  let v26 = Rc::clone(&g);
  let v27 = div_1(n, v26);
  let v35 = div_1(d, g);
  let v37 = to_pos(v35);
  Rc::new(Q { Qnum: v27, Qden: v37 })
}

// Rocq: Stdlib.QArith.QArith_base.Qplus
// Variant: uncurried
pub fn Qplus(x: Rc<Q>, y: Rc<Q>) -> Rc<Q> {
  let v7 = Rc::clone(&x);
  let v8 = Qnum_owned(v7);
  let v12 = Rc::clone(&y);
  let v14 = Qden(v12);
  let v16 = rocq_bigint::identity(v14);
  let v21 = mul_2(v8, v16);
  let v26 = Rc::clone(&y);
  let v27 = Qnum_owned(v26);
  let v31 = Rc::clone(&x);
  let v33 = Qden(v31);
  let v35 = rocq_bigint::identity(v33);
  let v40 = mul_2(v27, v35);
  let v45 = add(v21, v40);
  let v50 = Qden(x);
  let v54 = Qden(y);
  let v59 = mul_1(v50, v54);
  Rc::new(Q { Qnum: v45, Qden: v59 })
}

// Rocq: Stdlib.QArith.QArith_base.Qopp
pub fn Qopp(x: Rc<Q>) -> Rc<Q> {
  let v5 = Rc::clone(&x);
  let v7 = Qnum_owned(v5);
  let v9 = opp(v7);
  let v13 = Qden(x);
  Rc::new(Q { Qnum: v9, Qden: v13 })
}

// Rocq: Stdlib.QArith.QArith_base.Qminus
// Variant: uncurried
pub fn Qminus(x: Rc<Q>, y: Rc<Q>) -> Rc<Q> {
  Qplus(x, Qopp(y))
}

// Rocq: Roadtimes.roadtimes_implem.qsub
// Variant: uncurried
pub fn qsub(a: Rc<Q>, b: Rc<Q>) -> Rc<Q> {
  qred(Qminus(a, b))
}

// Rocq: Stdlib.QArith.QArith_base.Qmult
// Variant: uncurried
pub fn Qmult(x: Rc<Q>, y: Rc<Q>) -> Rc<Q> {
  let v6 = Rc::clone(&x);
  let v7 = Qnum_owned(v6);
  let v11 = Rc::clone(&y);
  let v12 = Qnum_owned(v11);
  let v17 = mul_2(v7, v12);
  let v22 = Qden(x);
  let v26 = Qden(y);
  let v31 = mul_1(v22, v26);
  Rc::new(Q { Qnum: v17, Qden: v31 })
}

// Rocq: Roadtimes.roadtimes_implem.elim_obj
// Variant: uncurried
pub fn elim_obj(O: Rc<Array<Rc<Q>>>, T: Rc<Array<Rc<Q>>>, w: u64, r: u64, f: Rc<Q>) -> Rc<Array<Rc<Q>>> {
  let v7 = 0u64;
  let v16 = {
    let __anf_capture_19 = w;
    move |j: u64, O: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
      let r = &r;
      let w = &__anf_capture_19;
      let T = &T;
      let f = &f;
      let v39 = add_1(mul(Clone::clone(r), Clone::clone(w)), j);
      let a = rocq_array::get::<Rc<Q>>(&T, v39);
      match qzerob(&a) {
        true => {
          std::mem::drop(a);
          O
        },
        false => {
          let v50 = &O;
          let v53 = rocq_array::get::<Rc<Q>>(&v50, j);
          let v56 = Rc::clone(f);
          rocq_array::set::<Rc<Q>>(O, j, qsub(v53, Qmult(v56, a)))
        },
      }
    }
  };
  let v77: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new(v16);
  forl::<Rc<Array<Rc<Q>>>>(v7, w, v77, O)
}

// Rocq: Roadtimes.roadtimes_implem.canon_obj
// Variant: uncurried
pub fn canon_obj(T: Rc<Array<Rc<Q>>>, B: Rc<Array<u64>>, c: Rc<Array<Rc<Q>>>, w: u64, m: u64) -> Rc<Array<Rc<Q>>> {
  let v7 = 0u64;
  let v12 = Rc::clone(&c);
  let v17 = {
    move |k: u64, O: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
      let B = &B;
      let c = &v12;
      let T = &T;
      let w = &w;
      let v31 = rocq_array::get::<u64>(&B, k);
      let f = rocq_array::get::<Rc<Q>>(&c, v31);
      match qzerob(&f) {
        true => {
          std::mem::drop(f);
          O
        },
        false => {
          let v45 = Rc::clone(T);
          let v47 = Clone::clone(w);
          elim_obj(O, v45, v47, k, f)
        },
      }
    }
  };
  let v58: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new(v17);
  let v60 = &c;
  let v61 = rocq_array::copy::<Rc<Q>>(&v60);
  std::mem::drop(c);
  forl::<Rc<Array<Rc<Q>>>>(v7, m, v58, v61)
}

// Rocq: Roadtimes.roadtimes_implem.st0
// Variant: uncurried
pub fn st0(T0: Rc<Array<Rc<Q>>>, m: u64, E0: u64, A0: u64) -> ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>) {
  let B0 = binit(m, E0);
  let v18 = add_1(E0, m);
  let v38 = cart(add_1(v18, 1u64), A0, add_1(E0, m));
  let v45 = add_1(E0, m);
  let v52 = add_1(v45, 1u64);
  let v55 = Rc::clone(&T0);
  let v58 = Rc::clone(&B0);
  let v65 = canon_obj(v55, v58, v38, v52, m);
  ((T0, v65), B0)
}

// Rocq: Roadtimes.roadtimes_implem.qltb
// Variant: uncurried
pub fn qltb(a: Rc<Q>, b: Rc<Q>) -> bool {
  let v7 = Rc::clone(&a);
  let v8 = Qnum_owned(v7);
  let v12 = Rc::clone(&b);
  let v14 = Qden(v12);
  let v16 = rocq_bigint::identity(v14);
  let v21 = mul_2(v8, v16);
  let v26 = Qnum_owned(b);
  let v31 = Qden(a);
  let v33 = rocq_bigint::identity(v31);
  let v38 = mul_2(v26, v33);
  ltb_1(v21, v38)
}

// Rocq: Roadtimes.roadtimes_implem.enter
// Variant: uncurried
pub fn enter(N: u64, al: Rc<Array<bool>>, O: Rc<Array<Rc<Q>>>) -> Rc<option<u64>> {
  let v4 = {
    move |_v5: u64, st: Rc<option<u64>>| -> bool {
      let (v7, v8) = __rocq_reuse::reset(st, |__payload| Clone::clone(__payload));
      std::mem::drop(v8);
      match v7 {
        option::Some(_v13) => {
          false
        },
        option::None => {
          true
        },
      }
    }
  };
  let v26: Rc<dyn Fn(u64, Rc<option<u64>>) -> bool> = Rc::new(v4);
  let v27: Rc<dyn Fn(u64, Rc<option<u64>>) -> bool> = v26;
  let v32 = {
    move |j: u64, v38: Rc<option<u64>>| -> Rc<option<u64>> {
      let al = &al;
      let O = &O;
      let v42 = rocq_array::get::<bool>(&al, j);
      let v46 = rocq_array::get::<Rc<Q>>(&O, j);
      let v47 = rocq_bigint::zero();
      let v48 = rocq_bigint::one();
      let v60 = qltb(v46, Rc::new(Q { Qnum: v47, Qden: v48 }));
      match andb(v42, v60) {
        true => {
          std::mem::drop(v38);
          Rc::new(option::<u64>::Some(j))
        },
        false => {
          std::mem::drop(v38);
          Rc::new(option::<u64>::None)
        },
      }
    }
  };
  let v82: Rc<dyn Fn(u64, Rc<option<u64>>) -> Rc<option<u64>>> = Rc::new(v32);
  loop_::<Rc<option<u64>>>(N, v27, v82, 0u64, Rc::new(option::<u64>::None))
}

// Rocq: Roadtimes.roadtimes_implem.lc
// Variant: uncurried
pub fn lc(N: u64, E0: u64, p: u64) -> u64 {
  match eqb(p, 0u64) {
    true => {
      N
    },
    false => {
      sub_1(add_1(E0, p), 1u64)
    },
  }
}

// Rocq: Roadtimes.roadtimes_implem.lexless
// Variant: borrowed, uncurried
pub fn lexless(T: &Rc<Array<Rc<Q>>>, w: u64, N: u64, E0: u64, m: u64, k: u64, r: u64, s: u64) -> bool {
  let m_1 = m;
  let s_1 = s;
  let v26 = add_1(mul(k, w), s_1);
  let v27 = T;
  let tks = rocq_array::get::<Rc<Q>>(&v27, v26);
  let v42 = add_1(mul(r, w), s_1);
  let v43 = T;
  let trs = rocq_array::get::<Rc<Q>>(&v43, v42);
  let v55 = add_1(m_1, 1u64);
  let v56 = {
    move |_v57: u64, st: u64| -> bool {
      eqb(st, 0u64)
    }
  };
  let v69: Rc<dyn Fn(u64, u64) -> bool> = Rc::new(v56);
  let v70: Rc<dyn Fn(u64, u64) -> bool> = v69;
  let v85 = Rc::clone(T);
  let v88 = {
    let __anf_capture_93 = k;
    let __anf_capture_97 = r;
    let __anf_capture_99 = w;
    move |p: u64, _v106: u64| -> u64 {
      let N = &N;
      let E0 = &E0;
      let k = &__anf_capture_93;
      let trs = &trs;
      let r = &__anf_capture_97;
      let w = &__anf_capture_99;
      let T = &v85;
      let tks = &tks;
      let c = lc(Clone::clone(N), Clone::clone(E0), p);
      let v128 = add_1(mul(Clone::clone(k), Clone::clone(w)), c);
      let a = Qmult(rocq_array::get::<Rc<Q>>(&T, v128), Rc::clone(trs));
      let v149 = add_1(mul(Clone::clone(r), Clone::clone(w)), c);
      let b = Qmult(rocq_array::get::<Rc<Q>>(&T, v149), Rc::clone(tks));
      let v160 = Rc::clone(&a);
      let v163 = Rc::clone(&b);
      match qltb(v160, v163) {
        true => {
          std::mem::drop(b);
          std::mem::drop(a);
          1u64
        },
        false => {
          match qltb(b, a) {
            true => {
              2u64
            },
            false => {
              0u64
            },
          }
        },
      }
    }
  };
  let v191: Rc<dyn Fn(u64, u64) -> u64> = Rc::new(v88);
  let st = loop_::<u64>(v55, v70, v191, 0u64, 0u64);
  eqb(st, 1u64)
}

// Rocq: Roadtimes.roadtimes_implem.leave
// Variant: uncurried
pub fn leave(T: Rc<Array<Rc<Q>>>, w: u64, N: u64, E0: u64, m: u64, s: u64) -> Rc<option<u64>> {
  let v8 = 0u64;
  let v21 = {
    let __anf_capture_30 = m;
    move |k: u64, best: Rc<option<u64>>| -> Rc<option<u64>> {
      let T = &T;
      let w = &w;
      let N = &N;
      let E0 = &E0;
      let m = &__anf_capture_30;
      let s = &s;
      let v37 = rocq_bigint::zero();
      let v38 = rocq_bigint::one();
      let v45 = Rc::new(Q { Qnum: v37, Qden: v38 });
      let v58 = add_1(mul(k, Clone::clone(w)), Clone::clone(s));
      let v60 = rocq_array::get::<Rc<Q>>(&T, v58);
      match qltb(v45, v60) {
        true => {
          let (v67, v68) = __rocq_reuse::reset(best, |__payload| Clone::clone(__payload));
          match v67 {
            option::Some(v73) => {
              let v76 = Clone::clone(w);
              let v78 = Clone::clone(N);
              let v80 = Clone::clone(E0);
              let v82 = Clone::clone(m);
              let v88 = Clone::clone(s);
              match lexless(T, v76, v78, v80, v82, k, v73, v88) {
                true => {
                  __rocq_reuse::rebuild(v68, option::<u64>::Some(k))
                },
                false => {
                  __rocq_reuse::rebuild(v68, option::<u64>::Some(v73))
                },
              }
            },
            option::None => {
              __rocq_reuse::rebuild(v68, option::<u64>::Some(k))
            },
          }
        },
        false => {
          best
        },
      }
    }
  };
  let v125: Rc<dyn Fn(u64, Rc<option<u64>>) -> Rc<option<u64>>> = Rc::new(v21);
  forl::<Rc<option<u64>>>(v8, m, v125, Rc::new(option::<u64>::None))
}

// Rocq: Roadtimes.roadtimes_implem.qmul
// Variant: uncurried
pub fn qmul(a: Rc<Q>, b: Rc<Q>) -> Rc<Q> {
  qred(Qmult(a, b))
}

// Rocq: Roadtimes.roadtimes_implem.scale_row
// Variant: uncurried
pub fn scale_row(T: Rc<Array<Rc<Q>>>, w: u64, r: u64, inv: Rc<Q>) -> Rc<Array<Rc<Q>>> {
  let v6 = 0u64;
  let v13 = {
    let __anf_capture_16 = w;
    move |j: u64, T: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
      let r = &r;
      let w = &__anf_capture_16;
      let inv = &inv;
      let v33 = add_1(mul(Clone::clone(r), Clone::clone(w)), j);
      let v46 = add_1(mul(Clone::clone(r), Clone::clone(w)), j);
      let v47 = &T;
      let v51 = rocq_array::get::<Rc<Q>>(&v47, v46);
      let v54 = Rc::clone(inv);
      rocq_array::set::<Rc<Q>>(T, v33, qmul(v51, v54))
    }
  };
  let v65: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new(v13);
  forl::<Rc<Array<Rc<Q>>>>(v6, w, v65, T)
}

// Rocq: Stdlib.QArith.QArith_base.Qinv
pub fn Qinv(x: Rc<Q>) -> Rc<Q> {
  let v4 = Rc::clone(&x);
  let v5 = Qnum_owned(v4);
  let v8 = Rc::clone(&v5);
  match rocq_bigint::integer_tag(v8) {
    rocq_bigint::IntegerTag::Zero => {
      std::mem::drop(v5);
      std::mem::drop(x);
      let v11 = rocq_bigint::zero();
      let v12 = rocq_bigint::one();
      Rc::new(Q { Qnum: v11, Qden: v12 })
    },
    rocq_bigint::IntegerTag::Positive => {
      let p = rocq_bigint::integer_magnitude(v5);
      let v29 = Qden(x);
      let v32 = rocq_bigint::identity(v29);
      Rc::new(Q { Qnum: v32, Qden: p })
    },
    rocq_bigint::IntegerTag::Negative => {
      let p = rocq_bigint::integer_magnitude(v5);
      let v48 = Qden(x);
      let v51 = rocq_bigint::neg(v48);
      Rc::new(Q { Qnum: v51, Qden: p })
    },
  }
}

// Rocq: Roadtimes.roadtimes_implem.elim_row
// Variant: uncurried
pub fn elim_row(T: Rc<Array<Rc<Q>>>, w: u64, r: u64, k: u64, f: Rc<Q>) -> Rc<Array<Rc<Q>>> {
  let v7 = 0u64;
  let v16 = {
    let __anf_capture_21 = w;
    move |j: u64, T: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
      let r = &r;
      let k = &k;
      let w = &__anf_capture_21;
      let f = &f;
      let v38 = add_1(mul(Clone::clone(r), Clone::clone(w)), j);
      let v39 = &T;
      let a = rocq_array::get::<Rc<Q>>(&v39, v38);
      match qzerob(&a) {
        true => {
          std::mem::drop(a);
          T
        },
        false => {
          let v61 = add_1(mul(Clone::clone(k), Clone::clone(w)), j);
          let v74 = add_1(mul(Clone::clone(k), Clone::clone(w)), j);
          let v75 = &T;
          let v78 = rocq_array::get::<Rc<Q>>(&v75, v74);
          let v81 = Rc::clone(f);
          rocq_array::set::<Rc<Q>>(T, v61, qsub(v78, Qmult(v81, a)))
        },
      }
    }
  };
  let v102: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new(v16);
  forl::<Rc<Array<Rc<Q>>>>(v7, w, v102, T)
}

// Rocq: Roadtimes.roadtimes_implem.elim_all
// Variant: uncurried
pub fn elim_all(T: Rc<Array<Rc<Q>>>, w: u64, m: u64, r: u64, s: u64) -> Rc<Array<Rc<Q>>> {
  let v7 = 0u64;
  let v14 = {
    move |k: u64, T: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
      let s = &s;
      let w = &w;
      let r = &r;
      let v27 = Clone::clone(r);
      match eqb(k, v27) {
        true => {
          T
        },
        false => {
          let v43 = add_1(mul(k, Clone::clone(w)), Clone::clone(s));
          let v44 = &T;
          let f = rocq_array::get::<Rc<Q>>(&v44, v43);
          match qzerob(&f) {
            true => {
              std::mem::drop(f);
              T
            },
            false => {
              let v59 = Clone::clone(w);
              let v61 = Clone::clone(r);
              elim_row(T, v59, v61, k, f)
            },
          }
        },
      }
    }
  };
  let v75: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new(v14);
  forl::<Rc<Array<Rc<Q>>>>(v7, m, v75, T)
}

// Rocq: Roadtimes.roadtimes_implem.pivot
// Variant: uncurried
pub fn pivot(w: u64, m: u64, st: ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>), r: u64, s: u64) -> ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>) {
  let v7 = Clone::clone(&st);
  let T = sT(v7);
  let v12 = Clone::clone(&st);
  let O = sO(v12);
  let B = sB(st);
  let v32 = add_1(mul(r, w), s);
  let v33 = &T;
  let v37 = rocq_array::get::<Rc<Q>>(&v33, v32);
  let T1 = scale_row(T, w, r, Qinv(v37));
  let T2 = elim_all(T1, w, m, r, s);
  let v62 = &O;
  let v65 = rocq_array::get::<Rc<Q>>(&v62, s);
  let v70 = Rc::clone(&T2);
  let O2 = elim_obj(O, v70, w, r, v65);
  let v82 = (T2, O2);
  let v90 = rocq_array::set::<u64>(B, r, s);
  (v82, v90)
}

// Rocq: Roadtimes.roadtimes_implem.odec
pub fn odec<A: Clone + 'static>(o: Rc<option<A>>) -> Rc<sumor<Rc<sig<A>>>> {
  let (v1, v2) = __rocq_reuse::reset(o, |__payload| match __payload {
    option::Some(__field0) => option::Some(Clone::clone(__field0)),
    option::None => option::None,
  });
  std::mem::drop(v2);
  match v1 {
    option::Some(v7) => {
      let v13 = Rc::new(sig::<A> { x: v7 });
      Rc::new(sumor::<Rc<sig<A>>>::inleft(v13))
    },
    option::None => {
      Rc::new(sumor::<Rc<sig<A>>>::inright)
    },
  }
}

// Rocq: Roadtimes.roadtimes_implem.sloop
// Variant: uncurried
pub fn sloop_1(m: u64, E0: u64, al: Rc<Array<bool>>, st: ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>)) -> ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>) {
  sloop(m, E0, al, st, ())
}

// Rocq: Roadtimes.roadtimes_implem.sloop (local: sloop)
// Variant: uncurried, lifted
pub fn sloop(m: u64, E0: u64, al: Rc<Array<bool>>, st: ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>), _H: ()) -> ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>) {
  let v12 = add_1(E0, m);
  let v15 = Clone::clone(&st);
  let v17 = sO(v15);
  let v22 = Rc::clone(&al);
  let v28 = odec::<u64>(enter(v12, v22, v17));
  let (v29, v30) = __rocq_reuse::reset(v28, |__payload| Clone::clone(__payload));
  std::mem::drop(v30);
  match v29 {
    sumor::inleft(v35) => {
      let (v37, v38) = __rocq_reuse::reset(v35, |__payload| Clone::clone(__payload));
      std::mem::drop(v38);
      match v37 {
        sig { x: v43 } => {
          let v49 = Clone::clone(&st);
          let v51 = sT(v49);
          let v58 = add_1(E0, m);
          let v87 = odec::<u64>(leave(v51, add_1(v58, 1u64), add_1(E0, m), E0, m, v43));
          let (v88, v89) = __rocq_reuse::reset(v87, |__payload| Clone::clone(__payload));
          std::mem::drop(v89);
          match v88 {
            sumor::inleft(v94) => {
              let s0 = &v94;
              match &**s0 {
                sig { x: r } => {
                  let v107 = add_1(E0, m);
                  let v115 = add_1(v107, 1u64);
                  let v120 = st;
                  let v121 = Clone::clone(r);
                  std::mem::drop(v94);
                  let v125 = pivot(v115, m, v120, v121, v43);
                  sloop(m, E0, al, v125, ())
                },
              }
            },
            sumor::inright => {
              std::mem::drop(al);
              st
            },
          }
        },
      }
    },
    sumor::inright => {
      std::mem::drop(al);
      st
    },
  }
}

// Rocq: Roadtimes.roadtimes_implem.phase1
// Variant: uncurried
pub fn phase1(T0: Rc<Array<Rc<Q>>>, m: u64, E0: u64, A0: u64) -> ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>) {
  let v17 = rocq_array::make::<bool>(add_1(E0, m), true);
  let v27 = st0(T0, m, E0, A0);
  sloop_1(m, E0, v17, v27)
}

// Rocq: Roadtimes.roadtimes_implem.al2
// Variant: uncurried
pub fn al2(O1: Rc<Array<Rc<Q>>>, A0: u64, N: u64) -> Rc<Array<bool>> {
  let v5 = 0u64;
  let v10 = {
    move |j: u64, a: Rc<Array<bool>>| -> Rc<Array<bool>> {
      let A0 = &A0;
      let O1 = &O1;
      let v23 = ltb(j, Clone::clone(A0));
      let v28 = rocq_array::get::<Rc<Q>>(&O1, j);
      rocq_array::set::<bool>(a, j, andb(v23, qzerob_owned(v28)))
    }
  };
  let v45: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new(v10);
  let v53 = rocq_array::make::<bool>(N, false);
  forl::<Rc<Array<bool>>>(v5, N, v45, v53)
}

// Rocq: Corelib.Floats.PrimFloat.div
// Variant: uncurried
pub fn div_2(v0: f64, v1: f64) -> f64 {
  rocq_float64::div(v0, v1)
}

// Rocq: Corelib.Floats.PrimFloat.of_uint63
pub fn of_uint63(v0: u64) -> f64 {
  rocq_float64::of_uint63(v0)
}

// Rocq: Roadtimes.roadtimes_implem.iofz_rec
pub fn iofz_rec_1(z: Rc<BigInt>) -> u64 {
  iofz_rec(z, ())
}

// Rocq: Roadtimes.roadtimes_implem.iofz_rec (local: iofz_rec)
// Variant: uncurried, lifted
pub fn iofz_rec(z: Rc<BigInt>, _H: ()) -> u64 {
  let v5 = rocq_bigint::zero();
  let v9 = Rc::clone(&z);
  let v11 = ltb_1(v5, v9);
  match bdec(v11) {
    sumbool::left => {
      let v17 = rocq_bigint::one();
      let v20 = rocq_bigint::twice(v17);
      let v22 = rocq_bigint::identity(v20);
      let v25 = Rc::clone(&z);
      let v28 = div_1(v25, v22);
      let r = iofz_rec(v28, ());
      let v40 = rocq_bigint::one();
      let v43 = rocq_bigint::twice(v40);
      let v45 = rocq_bigint::identity(v43);
      let v50 = modulo(z, v45);
      let v51 = rocq_bigint::zero();
      match eqb_1(v50, v51) {
        true => {
          add_1(r, r)
        },
        false => {
          let v72 = add_1(r, r);
          add_1(v72, 1u64)
        },
      }
    },
    sumbool::right => {
      std::mem::drop(z);
      0u64
    },
  }
}

// Rocq: Roadtimes.roadtimes_implem.iofz
pub fn iofz(z: Rc<BigInt>) -> u64 {
  iofz_rec_1(z)
}

// Rocq: Roadtimes.roadtimes_implem.q2f
pub fn q2f(q: Rc<Q>) -> f64 {
  let v6 = Rc::clone(&q);
  let v7 = Qnum_owned(v6);
  let v9 = rocq_bigint::one();
  let v12 = rocq_bigint::twice(v9);
  let v15 = rocq_bigint::twice(v12);
  let v18 = rocq_bigint::twice(v15);
  let v21 = rocq_bigint::twice(v18);
  let v24 = rocq_bigint::twice(v21);
  let v27 = rocq_bigint::twice(v24);
  let v30 = rocq_bigint::twice(v27);
  let v33 = rocq_bigint::twice(v30);
  let v36 = rocq_bigint::twice(v33);
  let v39 = rocq_bigint::twice(v36);
  let v42 = rocq_bigint::twice(v39);
  let v45 = rocq_bigint::twice(v42);
  let v48 = rocq_bigint::twice(v45);
  let v51 = rocq_bigint::twice(v48);
  let v54 = rocq_bigint::twice(v51);
  let v57 = rocq_bigint::twice(v54);
  let v60 = rocq_bigint::twice(v57);
  let v63 = rocq_bigint::twice(v60);
  let v66 = rocq_bigint::twice(v63);
  let v69 = rocq_bigint::twice(v66);
  let v72 = rocq_bigint::twice(v69);
  let v75 = rocq_bigint::twice(v72);
  let v78 = rocq_bigint::twice(v75);
  let v81 = rocq_bigint::twice(v78);
  let v84 = rocq_bigint::twice(v81);
  let v87 = rocq_bigint::twice(v84);
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
  let v119 = rocq_bigint::identity(v117);
  let v124 = mul_2(v7, v119);
  let v129 = Qden(q);
  let v131 = rocq_bigint::identity(v129);
  let mz = div_1(v124, v131);
  div_2(of_uint63(iofz(mz)), of_uint63(__rocq_global_2268))
}

// Rocq: Roadtimes.roadtimes_implem.dq
// Variant: borrowed, uncurried
pub fn dq(n: u64, D: &Rc<Array<u64>>, s: u64, d: u64) -> Rc<Q> {
  let n_1 = n;
  let s_1 = s;
  let d_1 = d;
  let v20 = add_1(mul(s_1, n_1), d_1);
  let v21 = D;
  let v28 = zofi(rocq_array::get::<u64>(&v21, v20));
  inject_Z(v28)
}

// Rocq: Roadtimes.roadtimes_implem.mk2
// Variant: uncurried
pub fn mk2(st1: ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>), carr: Rc<Array<Rc<Q>>>, w: u64, m: u64) -> ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>) {
  let v6 = Clone::clone(&st1);
  let v8 = sT(v6);
  let v9 = &v8;
  let v10 = rocq_array::copy::<Rc<Q>>(&v9);
  std::mem::drop(v8);
  let v14 = Clone::clone(&st1);
  let v16 = sT(v14);
  let v19 = Clone::clone(&st1);
  let v21 = sB(v19);
  let v32 = canon_obj(v16, v21, carr, w, m);
  let v38 = (v10, v32);
  let v42 = sB(st1);
  let v43 = &v42;
  let v44 = rocq_array::copy::<u64>(&v43);
  std::mem::drop(v42);
  (v38, v44)
}

// Rocq: Roadtimes.roadtimes_implem.phase2
// Variant: uncurried
pub fn phase2(T0: Rc<Array<Rc<Q>>>, m: u64, E0: u64, _A0: u64, st1: ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>), al: Rc<Array<bool>>, carr: Rc<Array<Rc<Q>>>) -> Rc<Q> {
  let v10 = &carr;
  let v11 = rocq_array::length::<Rc<Q>>(&v10);
  let v18 = add_1(E0, m);
  let v30 = eqb(v11, add_1(v18, 1u64));
  let v37 = add_1(E0, m);
  let v38 = &carr;
  let v42 = rocq_array::get::<Rc<Q>>(&v38, v37);
  let v50 = andb(v30, qzerob_owned(v42));
  match bdec(v50) {
    sumbool::left => {
      std::mem::drop(T0);
      let v62 = add_1(E0, m);
      let v78 = mk2(st1, carr, add_1(v62, 1u64), m);
      let st3 = sloop_1(m, E0, al, v78);
      let v92 = sO(st3);
      let v98 = add_1(E0, m);
      let v99 = &v92;
      let v102 = rocq_array::get::<Rc<Q>>(&v99, v98);
      std::mem::drop(v92);
      Qopp(v102)
    },
    sumbool::right => {
      std::mem::drop(T0);
      std::mem::drop(st1);
      std::mem::drop(al);
      std::mem::drop(carr);
      let v108 = rocq_bigint::zero();
      let v109 = rocq_bigint::one();
      Rc::new(Q { Qnum: v108, Qden: v109 })
    },
  }
}

// Rocq: Roadtimes.roadtimes_implem.qcost
// Variant: uncurried
pub fn qcost(E: u64, w: u64, cnt: Rc<Array<u64>>, neg: bool) -> Rc<Array<Rc<Q>>> {
  let v6 = 0u64;
  let v11 = {
    move |e: u64, c: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
      let neg = &neg;
      let cnt = &cnt;
      let v43 = match neg {
        true => {
          let v25 = rocq_array::get::<u64>(&cnt, e);
          let v28 = zofi(v25);
          let v31 = opp(v28);
          v31
        },
        false => {
          let v37 = rocq_array::get::<u64>(&cnt, e);
          let v40 = zofi(v37);
          v40
        },
      };
      rocq_array::set::<Rc<Q>>(c, e, inject_Z(v43))
    }
  };
  let v55: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new(v11);
  let v57 = rocq_bigint::zero();
  let v58 = rocq_bigint::one();
  let v70 = rocq_array::make::<Rc<Q>>(w, Rc::new(Q { Qnum: v57, Qden: v58 }));
  forl::<Rc<Array<Rc<Q>>>>(v6, E, v55, v70)
}

// Rocq: Roadtimes.roadtimes_implem.vq
// Variant: borrowed, uncurried
pub fn vq(n: u64, E: u64, RR: u64, D: &Rc<Array<u64>>, X: &Rc<Array<u64>>, I: &Rc<Array<u64>>, T0: &Rc<Array<Rc<Q>>>, st1: ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>), al: &Rc<Array<bool>>, s: u64, d: u64, neg: bool) -> Rc<Q> {
  let n_1 = n;
  let E_1 = E;
  let RR_1 = RR;
  let st1_1 = st1;
  let s_1 = s;
  let d_1 = d;
  let neg_1 = neg;
  let v25 = add_1(E_1, RR_1);
  let v31 = add_1(E_1, E_1);
  let v40 = add_1(E_1, RR_1);
  let v45 = add_1(E_1, v40);
  let v52 = add_1(v45, 1u64);
  let v68 = route_cnt(n_1, E_1, D, X, I, s_1, d_1);
  let v77 = qcost(E_1, v52, v68, neg_1);
  let v80 = Rc::clone(T0);
  let v91 = Rc::clone(al);
  phase2(v80, v25, E_1, v31, st1_1, v91, v77)
}

// Rocq: Roadtimes.roadtimes_implem.qans
// Variant: borrowed, uncurried
pub fn qans(n: u64, E: u64, RR: u64, D: &Rc<Array<u64>>, X: &Rc<Array<u64>>, I: &Rc<Array<u64>>, T0: &Rc<Array<Rc<Q>>>, st1: ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>), al: &Rc<Array<bool>>, s: u64, d: u64) -> (f64, f64) {
  let n_1 = n;
  let E_1 = E;
  let RR_1 = RR;
  let st1_1 = st1;
  let s_1 = s;
  let d_1 = d;
  let v28 = dq(n_1, D, s_1, d_1);
  let v37 = D;
  let v38 = X;
  let v39 = I;
  let v40 = T0;
  let v42 = Clone::clone(&st1_1);
  (q2f(Qplus(v28, vq(n_1, E_1, RR_1, v37, v38, v39, v40, v42, al, s_1, d_1, false))), q2f(Qminus(dq(n_1, D, s_1, d_1), vq(n_1, E_1, RR_1, D, X, I, T0, st1_1, al, s_1, d_1, true))))
}

// Rocq: Roadtimes.roadtimes_implem.aget
// Variant: borrowed, uncurried
pub fn aget(t: &Rc<Array<u64>>, i: u64) -> u64 {
  let i_1 = i;
  let v3 = t;
  rocq_array::get::<u64>(&v3, i_1)
}

// Rocq: Roadtimes.roadtimes_implem.answers
// Variant: uncurried
pub fn answers(n: u64, E: u64, RR: u64, D: Rc<Array<u64>>, X: Rc<Array<u64>>, I: Rc<Array<u64>>, T0: Rc<Array<Rc<Q>>>, xqs: Rc<Array<u64>>, xqd: Rc<Array<u64>>) -> Rc<Array<(f64, f64)>> {
  let v15 = add_1(E, RR);
  let v21 = add_1(E, E);
  let v24 = Rc::clone(&T0);
  let st1 = phase1(v24, v15, E, v21);
  let v35 = Clone::clone(&st1);
  let v37 = sO(v35);
  let v43 = add_1(E, E);
  let v50 = add_1(E, RR);
  let al = al2(v37, v43, add_1(E, v50));
  let v65 = 0u64;
  let v66 = &xqs;
  let v67 = rocq_array::length::<u64>(&v66);
  let v70 = Rc::clone(&xqs);
  let v91 = {
    let __anf_capture_98 = E;
    let __anf_capture_100 = RR;
    let __anf_capture_108 = T0;
    let __anf_capture_110 = st1;
    move |j: u64, out: Rc<Array<(f64, f64)>>| -> Rc<Array<(f64, f64)>> {
      let xqs = &v70;
      let xqd = &xqd;
      let n = &n;
      let E = &__anf_capture_98;
      let RR = &__anf_capture_100;
      let D = &D;
      let X = &X;
      let I = &I;
      let T0 = &__anf_capture_108;
      let st1 = &__anf_capture_110;
      let al = &al;
      let v120 = aget(xqs, j);
      let v125 = aget(xqd, j);
      let v144 = qans(Clone::clone(n), Clone::clone(E), Clone::clone(RR), D, X, I, T0, Clone::clone(st1), al, v120, v125);
      rocq_array::set::<(f64, f64)>(out, j, v144)
    }
  };
  let v154: Rc<dyn Fn(u64, Rc<Array<(f64, f64)>>) -> Rc<Array<(f64, f64)>>> = Rc::new(v91);
  let v156 = &xqs;
  let v157 = rocq_array::length::<u64>(&v156);
  std::mem::drop(xqs);
  let v170 = rocq_array::make::<(f64, f64)>(v157, (__rocq_global_2601, __rocq_global_2601));
  forl::<Rc<Array<(f64, f64)>>>(v65, v67, v154, v170)
}

// Rocq: Roadtimes.roadtimes_implem.roadtimes_impl
// Variant: uncurried
pub fn roadtimes_impl(xdist: Rc<Array<Rc<Array<u64>>>>, xrs: Rc<Array<u64>>, xrd: Rc<Array<u64>>, xrt: Rc<Array<u64>>, xqs: Rc<Array<u64>>, xqd: Rc<Array<u64>>) -> Rc<Array<(f64, f64)>> {
  let v6 = &xdist;
  let n = rocq_array::length::<Rc<Array<u64>>>(&v6);
  let W = flatten(n, xdist);
  let v19 = Rc::clone(&W);
  let FW = fw(n, v19);
  let v23 = Clone::clone(&FW);
  let D = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(v23);
  let X = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(FW);
  let v35 = Rc::clone(&W);
  let SR = scan_roads(n, v35);
  let v40 = Clone::clone(&SR);
  let I = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(v40));
  let v49 = Clone::clone(&SR);
  let P = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(v49));
  let E = snd::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(SR);
  let v59 = &xrs;
  let RR = rocq_array::length::<u64>(&v59);
  let v68 = guard(E, RR);
  match bdec(v68) {
    sumbool::left => {
      let v83 = Rc::clone(&D);
      let v86 = Rc::clone(&X);
      let v89 = Rc::clone(&I);
      let T0 = build_T(n, E, RR, W, v83, v86, v89, P, xrs, xrd, xrt);
      answers(n, E, RR, D, X, I, T0, xqs, xqd)
    },
    sumbool::right => {
      std::mem::drop(P);
      std::mem::drop(I);
      std::mem::drop(X);
      std::mem::drop(D);
      std::mem::drop(W);
      std::mem::drop(xrs);
      std::mem::drop(xrd);
      std::mem::drop(xrt);
      std::mem::drop(xqd);
      let v121 = &xqs;
      let v122 = rocq_array::length::<u64>(&v121);
      std::mem::drop(xqs);
      rocq_array::make::<(f64, f64)>(v122, (__rocq_global_2601, __rocq_global_2601))
    },
  }
}

// Rocq: Roadtimes.roadtimes_implem.roadtimes_impl
pub fn roadtimes_impl_curried(xdist: Rc<Array<Rc<Array<u64>>>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<(f64, f64)>>>>>>> {
  let v3 = {
    move |xrs: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<(f64, f64)>>>>>> {
      let xdist = &xdist;
      let v8 = Rc::clone(xdist);
      let v11 = {
        move |xrd: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<(f64, f64)>>>>> {
          let xdist = &v8;
          let xrs = &xrs;
          let v18 = Rc::clone(xdist);
          let v20 = Rc::clone(xrs);
          let v23 = {
            move |xrt: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<(f64, f64)>>>> {
              let xdist = &v18;
              let xrs = &v20;
              let xrd = &xrd;
              let v32 = Rc::clone(xdist);
              let v34 = Rc::clone(xrs);
              let v36 = Rc::clone(xrd);
              let v39 = {
                move |xqs: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<(f64, f64)>>> {
                  let xdist = &v32;
                  let xrs = &v34;
                  let xrd = &v36;
                  let xrt = &xrt;
                  let v50 = Rc::clone(xdist);
                  let v52 = Rc::clone(xrs);
                  let v54 = Rc::clone(xrd);
                  let v56 = Rc::clone(xrt);
                  let v59 = {
                    move |xqd: Rc<Array<u64>>| -> Rc<Array<(f64, f64)>> {
                      let v73 = Rc::clone(&v50);
                      let v75 = Rc::clone(&v52);
                      let v77 = Rc::clone(&v54);
                      let v79 = Rc::clone(&v56);
                      let v81 = Rc::clone(&xqs);
                      roadtimes_impl(v73, v75, v77, v79, v81, xqd)
                    }
                  };
                  let v87: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<(f64, f64)>>> = Rc::new(v59);
                  v87
                }
              };
              let v91: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<(f64, f64)>>>> = Rc::new(v39);
              v91
            }
          };
          let v95: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<(f64, f64)>>>>> = Rc::new(v23);
          v95
        }
      };
      let v99: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<(f64, f64)>>>>>> = Rc::new(v11);
      v99
    }
  };
  let v103: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<(f64, f64)>>>>>>> = Rc::new(v3);
  v103
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

pub fn run() -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<(f64, f64)>>> {
  let v0: Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<(f64, f64)>>> = __rocq_global_2726.with(Clone::clone);
  v0
}
const __rocq_global_461: u64 = 1073741824u64;
const __rocq_global_2268: u64 = 68719476736u64;
const __rocq_global_2601: f64 = f64::from_bits(0u64);
std::thread_local! { static __rocq_global_2726: Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<(f64, f64)>>> = roadtimes(); }
std::thread_local! { static __rocq_global_2729: Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<(f64, f64)>>>>>>>> = roadtimes_curried(); }