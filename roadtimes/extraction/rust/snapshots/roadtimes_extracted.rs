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

// Rocq: Roadtimes.roadtimes_implem.bdec
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

// Rocq: Roadtimes.roadtimes_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Roadtimes.roadtimes_implem.wloop (local: wloop)
// Variant: uncurried, lifted
pub fn wloop<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St, _H: ()) -> St {
  let tmp = ltb(i, hi);
  match bdec(tmp) {
    sumbool::left => {
      let cont_ref: &Rc<dyn Fn(u64, St) -> bool> = &cont;
      let s_clone = Clone::clone(&s);
      let tmp_1 = cont_ref(i, s_clone);
      if tmp_1 {
        let tmp_2 = add_1(i, 1u64);
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

// Rocq: Roadtimes.roadtimes_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop_1::<St>(hi, cont, f, i, s)
}

// Rocq: Roadtimes.roadtimes_implem.forl
// Variant: uncurried
pub fn forl<St: Clone + 'static>(lo: u64, hi: u64, f: Rc<dyn Fn(u64, St) -> St>, s: St) -> St {
  let callback: Rc<dyn Fn(u64, St) -> bool> = Rc::new(move |_v6: u64, v7: St| -> bool {
    std::mem::drop(v7);
    true
  });
  loop_::<St>(hi, callback, f, lo, s)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Roadtimes.roadtimes_implem.fill2
// Variant: uncurried
pub fn fill2(n: u64, g: Rc<dyn Fn(u64, u64) -> u64>, A: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let tmp = 0u64;
  let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
    let __anf_capture_13 = n;
    move |i: u64, A: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let g = &g;
      let n = &__anf_capture_13;
      let tmp_1 = 0u64;
      let n_clone = Clone::clone(n);
      let g_clone: Rc<dyn Fn(u64, u64) -> u64> = Rc::clone(g);
      let callback_1: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
        move |j: u64, A: Rc<Array<u64>>| -> Rc<Array<u64>> {
          let n = &n_clone;
          let g = &g_clone;
          let tmp_2 = add_1(mul(Clone::clone(&i), Clone::clone(n)), j);
          let tmp_3 = g(Clone::clone(&i), j);
          rocq_array::set::<u64>(A, tmp_2, tmp_3)
        }
      });
      let n_clone_1 = Clone::clone(n);
      forl::<Rc<Array<u64>>>(tmp_1, n_clone_1, callback_1, A)
    }
  });
  forl::<Rc<Array<u64>>>(tmp, n, callback, A)
}

// Rocq: Roadtimes.roadtimes_implem.flatten
// Variant: uncurried
pub fn flatten(n: u64, x: Rc<Array<Rc<Array<u64>>>>) -> Rc<Array<u64>> {
  let callback: Rc<dyn Fn(u64, u64) -> u64> = Rc::new({
    move |i: u64, j: u64| -> u64 {
      let x = &x;
      let x_clone = Rc::clone(x);
      let tmp = rocq_array::get::<Rc<Array<u64>>>(&x_clone, i);
      std::mem::drop(x_clone);
      let tmp_1 = rocq_array::get::<u64>(&tmp, j);
      std::mem::drop(tmp);
      tmp_1
    }
  });
  let tmp_2 = rocq_array::make::<u64>(mul(n, n), 0u64);
  fill2(n, callback, tmp_2)
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

// Rocq: Roadtimes.roadtimes_implem.fw_cell
// Variant: uncurried
pub fn fw_cell(n: u64, k: u64, i: u64, j: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let st_clone = Clone::clone(&st);
  let D = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(st_clone);
  let st_clone_1 = Clone::clone(&st);
  let X = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(st_clone_1);
  let tmp = rocq_array::get::<u64>(&D, add_1(mul(i, n), k));
  let tmp_1 = rocq_array::get::<u64>(&D, add_1(mul(k, n), j));
  let a = add_1(tmp, tmp_1);
  let tmp_2 = rocq_array::get::<u64>(&D, add_1(mul(i, n), j));
  if ltb(a, tmp_2) {
    std::mem::drop(st);
    let tmp_3 = rocq_array::set::<u64>(D, add_1(mul(i, n), j), a);
    let tmp_4 = add_1(mul(i, n), j);
    let tmp_5 = rocq_array::get::<u64>(&X, add_1(mul(i, n), k));
    let tmp_6 = rocq_array::set::<u64>(X, tmp_4, tmp_5);
    (tmp_3, tmp_6)
  } else {
    std::mem::drop(X);
    std::mem::drop(D);
    st
  }
}

// Rocq: Roadtimes.roadtimes_implem.fw_iter
// Variant: uncurried
pub fn fw_iter(n: u64, k: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = 0u64;
  let callback: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new({
    let __anf_capture_13 = n;
    move |i: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
      let k = &k;
      let n = &__anf_capture_13;
      let tmp_1 = 0u64;
      let n_clone = Clone::clone(n);
      let k_clone = Clone::clone(k);
      let callback_1: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new({
        move |j: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
          let tmp_2 = Clone::clone(&n_clone);
          let tmp_3 = Clone::clone(&k_clone);
          let i_clone = Clone::clone(&i);
          fw_cell(tmp_2, tmp_3, i_clone, j, st)
        }
      });
      let n_clone_1 = Clone::clone(n);
      forl::<(Rc<Array<u64>>, Rc<Array<u64>>)>(tmp_1, n_clone_1, callback_1, st)
    }
  });
  forl::<(Rc<Array<u64>>, Rc<Array<u64>>)>(tmp, n, callback, st)
}

// Rocq: Roadtimes.roadtimes_implem.fw
// Variant: uncurried
pub fn fw(n: u64, W: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let callback: Rc<dyn Fn(u64, u64) -> u64> = Rc::new({
    let __anf_capture_8 = n;
    move |i: u64, j: u64| -> u64 {
      let n = &__anf_capture_8;
      let W = &W;
      if eqb(i, j) {
        0u64
      } else {
        let tmp = rocq_array::get::<u64>(W, add_1(mul(i, Clone::clone(n)), j));
        if isroad(tmp) {
          let tmp_1 = add_1(mul(i, Clone::clone(n)), j);
          rocq_array::get::<u64>(W, tmp_1)
        } else {
          __rocq_global_461
        }
      }
    }
  });
  let tmp_2 = rocq_array::make::<u64>(mul(n, n), 0u64);
  let D0 = fill2(n, callback, tmp_2);
  let callback_1: Rc<dyn Fn(u64, u64) -> u64> = Rc::new(move |_i: u64, j: u64| -> u64 {
    j
  });
  let tmp_3 = rocq_array::make::<u64>(mul(n, n), 0u64);
  let X0 = fill2(n, callback_1, tmp_3);
  let tmp_4 = 0u64;
  let callback_2: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new({
    let __anf_capture_127 = n;
    move |k: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
      let tmp_5 = Clone::clone(&__anf_capture_127);
      fw_iter(tmp_5, k, st)
    }
  });
  forl::<(Rc<Array<u64>>, Rc<Array<u64>>)>(tmp_4, n, callback_2, (D0, X0))
}

// Rocq: Roadtimes.roadtimes_implem.scan_roads
// Variant: uncurried
pub fn scan_roads(n: u64, W: Rc<Array<u64>>) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let tmp = 0u64;
  let tmp_1 = mul(n, n);
  let callback: Rc<dyn Fn(u64, ((Rc<Array<u64>>, Rc<Array<u64>>), u64)) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64)> = Rc::new({
    move |p: u64, st: ((Rc<Array<u64>>, Rc<Array<u64>>), u64)| -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
      let W = &W;
      let st_clone = Clone::clone(&st);
      let I = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(st_clone));
      let st_clone_1 = Clone::clone(&st);
      let P = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(st_clone_1));
      let st_clone_2 = Clone::clone(&st);
      let e = snd::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(st_clone_2);
      let tmp_2 = rocq_array::get::<u64>(W, p);
      if isroad(tmp_2) {
        std::mem::drop(st);
        let tmp_3 = rocq_array::set::<u64>(I, p, e);
        let tmp_4 = rocq_array::set::<u64>(P, e, p);
        ((tmp_3, tmp_4), add_1(e, 1u64))
      } else {
        std::mem::drop(P);
        std::mem::drop(I);
        st
      }
    }
  });
  let tmp_5 = rocq_array::make::<u64>(mul(n, n), 0u64);
  let tmp_6 = rocq_array::make::<u64>(mul(n, n), 0u64);
  forl::<((Rc<Array<u64>>, Rc<Array<u64>>), u64)>(tmp, tmp_1, callback, ((tmp_5, tmp_6), 0u64))
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Roadtimes.roadtimes_implem.guard
// Variant: uncurried
pub fn guard(E: u64, R: u64) -> bool {
  let tmp = andb(leb(1u64, add_1(E, R)), leb(E, 2048u64));
  let tmp_1 = andb(tmp, leb(R, 2048u64));
  let tmp_2 = add_1(E, R);
  let tmp_3 = add_1(E, R);
  let tmp_4 = add_1(E, tmp_3);
  andb(tmp_1, leb(mul(tmp_2, add_1(tmp_4, 1u64)), 4194303u64))
}

// Rocq: Stdlib.QArith.QArith_base.inject_Z
pub fn inject_Z(x: Rc<BigInt>) -> Rc<Q> {
  let tmp = rocq_bigint::one();
  Rc::new(Q { Qnum: x, Qden: tmp })
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
  rocq_bigint::mul(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.mul
// Variant: uncurried
pub fn mul_2(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::mul(v0, v1)
}

// Rocq: Roadtimes.roadtimes_implem.zofi_rec
pub fn zofi_rec_1(i: u64) -> Rc<BigInt> {
  zofi_rec(i, ())
}

// Rocq: Roadtimes.roadtimes_implem.zofi_rec (local: zofi_rec)
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

// Rocq: Roadtimes.roadtimes_implem.zofi
pub fn zofi(i: u64) -> Rc<BigInt> {
  zofi_rec_1(i)
}

// Rocq: Roadtimes.roadtimes_implem.zofs
pub fn zofs(i: u64) -> Rc<BigInt> {
  if ltb(i, 4611686018427387904u64) {
    zofi(i)
  } else {
    let tmp = zofi(i);
    let tmp_1 = rocq_bigint::one();
    let tmp_2 = rocq_bigint::twice(tmp_1);
    let tmp_3 = rocq_bigint::twice(tmp_2);
    let tmp_4 = rocq_bigint::twice(tmp_3);
    let tmp_5 = rocq_bigint::twice(tmp_4);
    let tmp_6 = rocq_bigint::twice(tmp_5);
    let tmp_7 = rocq_bigint::twice(tmp_6);
    let tmp_8 = rocq_bigint::twice(tmp_7);
    let tmp_9 = rocq_bigint::twice(tmp_8);
    let tmp_10 = rocq_bigint::twice(tmp_9);
    let tmp_11 = rocq_bigint::twice(tmp_10);
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
    let tmp_31 = rocq_bigint::twice(tmp_30);
    let tmp_32 = rocq_bigint::twice(tmp_31);
    let tmp_33 = rocq_bigint::twice(tmp_32);
    let tmp_34 = rocq_bigint::twice(tmp_33);
    let tmp_35 = rocq_bigint::twice(tmp_34);
    let tmp_36 = rocq_bigint::twice(tmp_35);
    let tmp_37 = rocq_bigint::twice(tmp_36);
    let tmp_38 = rocq_bigint::twice(tmp_37);
    let tmp_39 = rocq_bigint::twice(tmp_38);
    let tmp_40 = rocq_bigint::twice(tmp_39);
    let tmp_41 = rocq_bigint::twice(tmp_40);
    let tmp_42 = rocq_bigint::twice(tmp_41);
    let tmp_43 = rocq_bigint::twice(tmp_42);
    let tmp_44 = rocq_bigint::twice(tmp_43);
    let tmp_45 = rocq_bigint::twice(tmp_44);
    let tmp_46 = rocq_bigint::twice(tmp_45);
    let tmp_47 = rocq_bigint::twice(tmp_46);
    let tmp_48 = rocq_bigint::twice(tmp_47);
    let tmp_49 = rocq_bigint::twice(tmp_48);
    let tmp_50 = rocq_bigint::twice(tmp_49);
    let tmp_51 = rocq_bigint::twice(tmp_50);
    let tmp_52 = rocq_bigint::twice(tmp_51);
    let tmp_53 = rocq_bigint::twice(tmp_52);
    let tmp_54 = rocq_bigint::twice(tmp_53);
    let tmp_55 = rocq_bigint::twice(tmp_54);
    let tmp_56 = rocq_bigint::twice(tmp_55);
    let tmp_57 = rocq_bigint::twice(tmp_56);
    let tmp_58 = rocq_bigint::twice(tmp_57);
    let tmp_59 = rocq_bigint::twice(tmp_58);
    let tmp_60 = rocq_bigint::twice(tmp_59);
    let tmp_61 = rocq_bigint::twice(tmp_60);
    let tmp_62 = rocq_bigint::twice(tmp_61);
    let tmp_63 = rocq_bigint::twice(tmp_62);
    let tmp_64 = rocq_bigint::twice(tmp_63);
    let tmp_65 = rocq_bigint::identity(tmp_64);
    sub(tmp, tmp_65)
  }
}

// Rocq: Roadtimes.roadtimes_implem.bound_rows
// Variant: uncurried
pub fn bound_rows(E: u64, w: u64, N: u64, W: Rc<Array<u64>>, P: Rc<Array<u64>>, T: Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>> {
  let tmp = 0u64;
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new({
    let __anf_capture_24 = E;
    move |e: u64, T: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
      let P = &P;
      let W = &W;
      let E = &__anf_capture_24;
      let w = &w;
      let N = &N;
      let tmp_1 = rocq_array::get::<u64>(P, e);
      let u = rocq_array::get::<u64>(W, tmp_1);
      let tmp_2 = add_1(mul(e, Clone::clone(w)), e);
      let tmp_3 = rocq_bigint::one();
      let tmp_4 = rocq_bigint::identity(tmp_3);
      let tmp_5 = rocq_bigint::one();
      let T_1 = rocq_array::set::<Rc<Q>>(T, tmp_2, Rc::new(Q { Qnum: tmp_4, Qden: tmp_5 }));
      let tmp_6 = mul(e, Clone::clone(w));
      let tmp_7 = add_1(Clone::clone(E), e);
      let tmp_8 = add_1(tmp_6, tmp_7);
      let tmp_9 = rocq_bigint::one();
      let tmp_10 = rocq_bigint::identity(tmp_9);
      let tmp_11 = rocq_bigint::one();
      let T_2 = rocq_array::set::<Rc<Q>>(T_1, tmp_8, Rc::new(Q { Qnum: tmp_10, Qden: tmp_11 }));
      let tmp_12 = add_1(mul(e, Clone::clone(w)), Clone::clone(N));
      let tmp_13 = if isroad(u) {
        let tmp_14 = zofs(u);
        inject_Z(tmp_14)
      } else {
        let tmp_15 = rocq_bigint::zero();
        let tmp_16 = rocq_bigint::one();
        Rc::new(Q { Qnum: tmp_15, Qden: tmp_16 })
      };
      rocq_array::set::<Rc<Q>>(T_2, tmp_12, tmp_13)
    }
  });
  forl::<Rc<Array<Rc<Q>>>>(tmp, E, callback, T)
}

// Rocq: Roadtimes.roadtimes_implem.walk
// Variant: uncurried
pub fn walk_1(n: u64, d: u64, E: u64, D: Rc<Array<u64>>, X: Rc<Array<u64>>, I: Rc<Array<u64>>, cur: u64, cnt: Rc<Array<u64>>) -> Rc<Array<u64>> {
  walk(n, d, E, D, X, I, cur, cnt, ())
}

// Rocq: Roadtimes.roadtimes_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(n: u64, d: u64, E: u64, D: Rc<Array<u64>>, X: Rc<Array<u64>>, I: Rc<Array<u64>>, cur: u64, cnt: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  if eqb(cur, d) {
    std::mem::drop(D);
    std::mem::drop(X);
    std::mem::drop(I);
    cnt
  } else {
    let v = rocq_array::get::<u64>(&X, add_1(mul(cur, n), d));
    let tmp = rocq_array::get::<u64>(&D, add_1(mul(v, n), d));
    let tmp_1 = rocq_array::get::<u64>(&D, add_1(mul(cur, n), d));
    let tmp_2 = ltb(tmp, tmp_1);
    match bdec(tmp_2) {
      sumbool::left => {
        let e = rocq_array::get::<u64>(&I, add_1(mul(cur, n), v));
        let tmp_3 = if ltb(e, E) {
          let tmp_4 = rocq_array::get::<u64>(&cnt, e);
          rocq_array::set::<u64>(cnt, e, add_1(tmp_4, 1u64))
        } else {
          cnt
        };
        walk(n, d, E, D, X, I, v, tmp_3, ())
      },
      sumbool::right => {
        std::mem::drop(I);
        std::mem::drop(D);
        std::mem::drop(X);
        cnt
      },
    }
  }
}

// Rocq: Roadtimes.roadtimes_implem.route_cnt
// Variant: uncurried
pub fn route_cnt_owned(n: u64, E: u64, D: Rc<Array<u64>>, X: Rc<Array<u64>>, I: Rc<Array<u64>>, s: u64, d: u64) -> Rc<Array<u64>> {
  let tmp = rocq_array::make::<u64>(E, 0u64);
  walk_1(n, d, E, D, X, I, s, tmp)
}

// Rocq: Roadtimes.roadtimes_implem.route_cnt
// Variant: borrowed, uncurried
pub fn route_cnt(n: u64, E: u64, D: &Rc<Array<u64>>, X: &Rc<Array<u64>>, I: &Rc<Array<u64>>, s: u64, d: u64) -> Rc<Array<u64>> {
  let n_1 = n;
  let E_1 = E;
  let s_1 = s;
  let d_1 = d;
  let tmp = rocq_array::make::<u64>(E_1, 0u64);
  let D_clone = Rc::clone(D);
  let X_clone = Rc::clone(X);
  let I_clone = Rc::clone(I);
  walk_1(n_1, d_1, E_1, D_clone, X_clone, I_clone, s_1, tmp)
}

// Rocq: Corelib.BinNums.IntDef.Z.ltb
// Variant: uncurried
pub fn ltb_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::lt(v0, v1)
}

// Rocq: Stdlib.ZArith.BinIntDef.Z.abs
pub fn abs(v0: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::abs(v0)
}

// Rocq: Roadtimes.roadtimes_implem.deliv_row
// Variant: uncurried
pub fn deliv_row(n: u64, E: u64, w: u64, N: u64, D: Rc<Array<u64>>, X: Rc<Array<u64>>, I: Rc<Array<u64>>, rs: Rc<Array<u64>>, rd: Rc<Array<u64>>, rt: Rc<Array<u64>>, k: u64, T: Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>> {
  let s = rocq_array::get::<u64>(&rs, k);
  std::mem::drop(rs);
  let d = rocq_array::get::<u64>(&rd, k);
  std::mem::drop(rd);
  let D_clone = Rc::clone(&D);
  let cnt = route_cnt_owned(n, E, D_clone, X, I, s, d);
  let tmp = rocq_array::get::<u64>(&rt, k);
  std::mem::drop(rt);
  let tmp_1 = zofi(tmp);
  let tmp_2 = rocq_array::get::<u64>(&D, add_1(mul(s, n), d));
  std::mem::drop(D);
  let tmp_3 = zofi(tmp_2);
  let b = sub(tmp_1, tmp_3);
  let i = add_1(E, k);
  let tmp_4 = 0u64;
  let b_clone = Rc::clone(&b);
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new({
    let __anf_capture_90 = i;
    let __anf_capture_92 = w;
    move |e: u64, T: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
      let i = &__anf_capture_90;
      let w = &__anf_capture_92;
      let b = &b_clone;
      let cnt = &cnt;
      let tmp_5 = add_1(mul(Clone::clone(i), Clone::clone(w)), e);
      let tmp_6 = rocq_bigint::zero();
      let b_clone_1 = Rc::clone(b);
      let tmp_7 = if ltb_1(b_clone_1, tmp_6) {
        let tmp_8 = rocq_array::get::<u64>(cnt, e);
        let tmp_9 = zofi(tmp_8);
        opp(tmp_9)
      } else {
        let tmp_10 = rocq_array::get::<u64>(cnt, e);
        zofi(tmp_10)
      };
      rocq_array::set::<Rc<Q>>(T, tmp_5, inject_Z(tmp_7))
    }
  });
  let T_1 = forl::<Rc<Array<Rc<Q>>>>(tmp_4, E, callback, T);
  let tmp_11 = mul(i, w);
  let tmp_12 = add_1(E, E);
  let tmp_13 = add_1(tmp_12, k);
  let tmp_14 = add_1(tmp_11, tmp_13);
  let tmp_15 = rocq_bigint::one();
  let tmp_16 = rocq_bigint::identity(tmp_15);
  let tmp_17 = rocq_bigint::one();
  let T_2 = rocq_array::set::<Rc<Q>>(T_1, tmp_14, Rc::new(Q { Qnum: tmp_16, Qden: tmp_17 }));
  let tmp_18 = add_1(mul(i, w), N);
  let tmp_19 = abs(b);
  rocq_array::set::<Rc<Q>>(T_2, tmp_18, inject_Z(tmp_19))
}

// Rocq: Roadtimes.roadtimes_implem.build_T
// Variant: uncurried
pub fn build_T(n: u64, E: u64, R: u64, W: Rc<Array<u64>>, D: Rc<Array<u64>>, X: Rc<Array<u64>>, I: Rc<Array<u64>>, P: Rc<Array<u64>>, rs: Rc<Array<u64>>, rd: Rc<Array<u64>>, rt: Rc<Array<u64>>) -> Rc<Array<Rc<Q>>> {
  let m = add_1(E, R);
  let tmp = add_1(E, m);
  let w = add_1(tmp, 1u64);
  let N = add_1(E, m);
  let tmp_1 = mul(m, w);
  let tmp_2 = rocq_bigint::zero();
  let tmp_3 = rocq_bigint::one();
  let tmp_4 = rocq_array::make::<Rc<Q>>(tmp_1, Rc::new(Q { Qnum: tmp_2, Qden: tmp_3 }));
  let T = bound_rows(E, w, N, W, P, tmp_4);
  let tmp_5 = 0u64;
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new({
    let __anf_capture_97 = E;
    let __anf_capture_99 = w;
    let __anf_capture_101 = N;
    move |k: u64, T: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
      let n_clone = Clone::clone(&n);
      let tmp_6 = Clone::clone(&__anf_capture_97);
      let tmp_7 = Clone::clone(&__anf_capture_99);
      let tmp_8 = Clone::clone(&__anf_capture_101);
      let D_clone = Rc::clone(&D);
      let X_clone = Rc::clone(&X);
      let I_clone = Rc::clone(&I);
      let rs_clone = Rc::clone(&rs);
      let rd_clone = Rc::clone(&rd);
      let rt_clone = Rc::clone(&rt);
      deliv_row(n_clone, tmp_6, tmp_7, tmp_8, D_clone, X_clone, I_clone, rs_clone, rd_clone, rt_clone, k, T)
    }
  });
  forl::<Rc<Array<Rc<Q>>>>(tmp_5, R, callback, T)
}

// Rocq: Stdlib.QArith.QArith_base.Qnum
pub fn Qnum_owned(q: Rc<Q>) -> Rc<BigInt> {
  let q_Qnum_clone = Rc::clone(&q.Qnum);
  std::mem::drop(q);
  q_Qnum_clone
}

// Rocq: Stdlib.QArith.QArith_base.Qnum
// Variant: borrowed
pub fn Qnum(q: &Rc<Q>) -> Rc<BigInt> {
  let tmp = q;
  Rc::clone(&tmp.Qnum)
}

// Rocq: Stdlib.QArith.QArith_base.Qden
pub fn Qden(q: Rc<Q>) -> Rc<BigInt> {
  let q_Qden_clone = Rc::clone(&q.Qden);
  std::mem::drop(q);
  q_Qden_clone
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
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new(move |j: u64, c: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
    let tmp = rocq_bigint::one();
    let tmp_1 = rocq_bigint::identity(tmp);
    let tmp_2 = rocq_bigint::one();
    rocq_array::set::<Rc<Q>>(c, j, Rc::new(Q { Qnum: tmp_1, Qden: tmp_2 }))
  });
  let tmp_3 = rocq_bigint::zero();
  let tmp_4 = rocq_bigint::one();
  let tmp_5 = rocq_array::make::<Rc<Q>>(w, Rc::new(Q { Qnum: tmp_3, Qden: tmp_4 }));
  forl::<Rc<Array<Rc<Q>>>>(A0, N, callback, tmp_5)
}

// Rocq: Roadtimes.roadtimes_implem.binit
// Variant: uncurried
pub fn binit(m: u64, E0: u64) -> Rc<Array<u64>> {
  let tmp = 0u64;
  let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
    move |k: u64, B: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let E0_clone = Clone::clone(&E0);
      let tmp_1 = add_1(E0_clone, k);
      rocq_array::set::<u64>(B, k, tmp_1)
    }
  });
  let tmp_2 = rocq_array::make::<u64>(m, 0u64);
  forl::<Rc<Array<u64>>>(tmp, m, callback, tmp_2)
}

// Rocq: Corelib.BinNums.IntDef.Z.eqb
// Variant: uncurried
pub fn eqb_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::equal(v0, v1)
}

// Rocq: Roadtimes.roadtimes_implem.qzerob
pub fn qzerob_owned(a: Rc<Q>) -> bool {
  let tmp = Qnum_owned(a);
  let tmp_1 = rocq_bigint::zero();
  eqb_1(tmp, tmp_1)
}

// Rocq: Roadtimes.roadtimes_implem.qzerob
// Variant: borrowed
pub fn qzerob(a: &Rc<Q>) -> bool {
  let tmp = Qnum(a);
  let tmp_1 = rocq_bigint::zero();
  eqb_1(tmp, tmp_1)
}

// Rocq: Corelib.BinNums.IntDef.Z.modulo
// Variant: uncurried
pub fn modulo(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::modulo(v0, v1)
}

// Rocq: StdGalilei.bigint.zgcd_loop
// Variant: uncurried
pub fn zgcd_loop_1(a: Rc<BigInt>, b: Rc<BigInt>) -> Rc<BigInt> {
  zgcd_loop(a, b, ())
}

// Rocq: StdGalilei.bigint.zgcd_loop (local: zgcd_loop)
// Variant: uncurried, lifted
pub fn zgcd_loop(a: Rc<BigInt>, b: Rc<BigInt>, _H: ()) -> Rc<BigInt> {
  let tmp = rocq_bigint::zero();
  let b_clone = Rc::clone(&b);
  if ltb_1(tmp, b_clone) {
    let b_clone_1 = Rc::clone(&b);
    let tmp_1 = modulo(a, b_clone_1);
    zgcd_loop(b, tmp_1, ())
  } else {
    std::mem::drop(b);
    a
  }
}

// Rocq: StdGalilei.bigint.zgcd
// Variant: uncurried
pub fn zgcd(a: Rc<BigInt>, b: Rc<BigInt>) -> Rc<BigInt> {
  let tmp = abs(a);
  let tmp_1 = abs(b);
  zgcd_loop_1(tmp, tmp_1)
}

// Rocq: Corelib.BinNums.IntDef.Z.div
// Variant: uncurried
pub fn div_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::div(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.to_pos
pub fn to_pos(v0: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::to_positive(v0)
}

// Rocq: Roadtimes.roadtimes_implem.qred
pub fn qred(q: Rc<Q>) -> Rc<Q> {
  let q_clone = Rc::clone(&q);
  let n = Qnum_owned(q_clone);
  let tmp = Qden(q);
  let d = rocq_bigint::identity(tmp);
  let n_clone = Rc::clone(&n);
  let d_clone = Rc::clone(&d);
  let g = zgcd(n_clone, d_clone);
  let g_clone = Rc::clone(&g);
  let tmp_1 = div_1(n, g_clone);
  let tmp_2 = div_1(d, g);
  let tmp_3 = to_pos(tmp_2);
  Rc::new(Q { Qnum: tmp_1, Qden: tmp_3 })
}

// Rocq: Stdlib.QArith.QArith_base.Qplus
// Variant: uncurried
pub fn Qplus(x: Rc<Q>, y: Rc<Q>) -> Rc<Q> {
  let x_clone = Rc::clone(&x);
  let tmp = Qnum_owned(x_clone);
  let y_clone = Rc::clone(&y);
  let tmp_1 = Qden(y_clone);
  let tmp_2 = rocq_bigint::identity(tmp_1);
  let tmp_3 = mul_2(tmp, tmp_2);
  let y_clone_1 = Rc::clone(&y);
  let tmp_4 = Qnum_owned(y_clone_1);
  let x_clone_1 = Rc::clone(&x);
  let tmp_5 = Qden(x_clone_1);
  let tmp_6 = rocq_bigint::identity(tmp_5);
  let tmp_7 = mul_2(tmp_4, tmp_6);
  let tmp_8 = add(tmp_3, tmp_7);
  let tmp_9 = Qden(x);
  let tmp_10 = Qden(y);
  let tmp_11 = mul_1(tmp_9, tmp_10);
  Rc::new(Q { Qnum: tmp_8, Qden: tmp_11 })
}

// Rocq: Stdlib.QArith.QArith_base.Qopp
pub fn Qopp(x: Rc<Q>) -> Rc<Q> {
  let x_clone = Rc::clone(&x);
  let tmp = Qnum_owned(x_clone);
  let tmp_1 = opp(tmp);
  let tmp_2 = Qden(x);
  Rc::new(Q { Qnum: tmp_1, Qden: tmp_2 })
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
  let x_clone = Rc::clone(&x);
  let tmp = Qnum_owned(x_clone);
  let y_clone = Rc::clone(&y);
  let tmp_1 = Qnum_owned(y_clone);
  let tmp_2 = mul_2(tmp, tmp_1);
  let tmp_3 = Qden(x);
  let tmp_4 = Qden(y);
  let tmp_5 = mul_1(tmp_3, tmp_4);
  Rc::new(Q { Qnum: tmp_2, Qden: tmp_5 })
}

// Rocq: Roadtimes.roadtimes_implem.elim_obj
// Variant: uncurried
pub fn elim_obj(O: Rc<Array<Rc<Q>>>, T: Rc<Array<Rc<Q>>>, w: u64, r: u64, f: Rc<Q>) -> Rc<Array<Rc<Q>>> {
  let tmp = 0u64;
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new({
    let __anf_capture_19 = w;
    move |j: u64, O: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
      let r = &r;
      let w = &__anf_capture_19;
      let T = &T;
      let f = &f;
      let a = rocq_array::get::<Rc<Q>>(T, add_1(mul(Clone::clone(r), Clone::clone(w)), j));
      if qzerob(&a) {
        std::mem::drop(a);
        O
      } else {
        let tmp_1 = rocq_array::get::<Rc<Q>>(&O, j);
        let f_clone = Rc::clone(f);
        rocq_array::set::<Rc<Q>>(O, j, qsub(tmp_1, Qmult(f_clone, a)))
      }
    }
  });
  forl::<Rc<Array<Rc<Q>>>>(tmp, w, callback, O)
}

// Rocq: Roadtimes.roadtimes_implem.canon_obj
// Variant: uncurried
pub fn canon_obj(T: Rc<Array<Rc<Q>>>, B: Rc<Array<u64>>, c: Rc<Array<Rc<Q>>>, w: u64, m: u64) -> Rc<Array<Rc<Q>>> {
  let tmp = 0u64;
  let c_clone = Rc::clone(&c);
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new({
    move |k: u64, O: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
      let B = &B;
      let c = &c_clone;
      let T = &T;
      let w = &w;
      let f = rocq_array::get::<Rc<Q>>(c, rocq_array::get::<u64>(B, k));
      if qzerob(&f) {
        std::mem::drop(f);
        O
      } else {
        let T_clone = Rc::clone(T);
        let w_clone = Clone::clone(w);
        elim_obj(O, T_clone, w_clone, k, f)
      }
    }
  });
  let tmp_1 = rocq_array::copy::<Rc<Q>>(&c);
  std::mem::drop(c);
  forl::<Rc<Array<Rc<Q>>>>(tmp, m, callback, tmp_1)
}

// Rocq: Roadtimes.roadtimes_implem.st0
// Variant: uncurried
pub fn st0(T0: Rc<Array<Rc<Q>>>, m: u64, E0: u64, A0: u64) -> ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>) {
  let B0 = binit(m, E0);
  let tmp = add_1(E0, m);
  let tmp_1 = cart(add_1(tmp, 1u64), A0, add_1(E0, m));
  let tmp_2 = add_1(E0, m);
  let tmp_3 = add_1(tmp_2, 1u64);
  let T0_clone = Rc::clone(&T0);
  let B0_clone = Rc::clone(&B0);
  let tmp_4 = canon_obj(T0_clone, B0_clone, tmp_1, tmp_3, m);
  ((T0, tmp_4), B0)
}

// Rocq: Roadtimes.roadtimes_implem.qltb
// Variant: uncurried
pub fn qltb(a: Rc<Q>, b: Rc<Q>) -> bool {
  let a_clone = Rc::clone(&a);
  let tmp = Qnum_owned(a_clone);
  let b_clone = Rc::clone(&b);
  let tmp_1 = Qden(b_clone);
  let tmp_2 = rocq_bigint::identity(tmp_1);
  let tmp_3 = mul_2(tmp, tmp_2);
  let tmp_4 = Qnum_owned(b);
  let tmp_5 = Qden(a);
  let tmp_6 = rocq_bigint::identity(tmp_5);
  let tmp_7 = mul_2(tmp_4, tmp_6);
  ltb_1(tmp_3, tmp_7)
}

// Rocq: Roadtimes.roadtimes_implem.enter
// Variant: uncurried
pub fn enter(N: u64, al: Rc<Array<bool>>, O: Rc<Array<Rc<Q>>>) -> Rc<option<u64>> {
  let callback: Rc<dyn Fn(u64, Rc<option<u64>>) -> bool> = Rc::new(move |_v5: u64, st: Rc<option<u64>>| -> bool {
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
  });
  let callback_1: Rc<dyn Fn(u64, Rc<option<u64>>) -> Rc<option<u64>>> = Rc::new({
    move |j: u64, v38: Rc<option<u64>>| -> Rc<option<u64>> {
      let al = &al;
      let O = &O;
      let tmp = rocq_array::get::<bool>(al, j);
      let tmp_1 = rocq_array::get::<Rc<Q>>(O, j);
      let tmp_2 = rocq_bigint::zero();
      let tmp_3 = rocq_bigint::one();
      let tmp_4 = qltb(tmp_1, Rc::new(Q { Qnum: tmp_2, Qden: tmp_3 }));
      if andb(tmp, tmp_4) {
        std::mem::drop(v38);
        Rc::new(option::<u64>::Some(j))
      } else {
        std::mem::drop(v38);
        Rc::new(option::<u64>::None)
      }
    }
  });
  loop_::<Rc<option<u64>>>(N, callback, callback_1, 0u64, Rc::new(option::<u64>::None))
}

// Rocq: Roadtimes.roadtimes_implem.lc
// Variant: uncurried
pub fn lc(N: u64, E0: u64, p: u64) -> u64 {
  if eqb(p, 0u64) {
    N
  } else {
    sub_1(add_1(E0, p), 1u64)
  }
}

// Rocq: Roadtimes.roadtimes_implem.lexless
// Variant: borrowed, uncurried
pub fn lexless(T: &Rc<Array<Rc<Q>>>, w: u64, N: u64, E0: u64, m: u64, k: u64, r: u64, s: u64) -> bool {
  let m_1 = m;
  let s_1 = s;
  let tks = rocq_array::get::<Rc<Q>>(T, add_1(mul(k, w), s_1));
  let trs = rocq_array::get::<Rc<Q>>(T, add_1(mul(r, w), s_1));
  let tmp = add_1(m_1, 1u64);
  let callback: Rc<dyn Fn(u64, u64) -> bool> = Rc::new(move |_v57: u64, st: u64| -> bool {
    eqb(st, 0u64)
  });
  let T_clone = Rc::clone(T);
  let callback_1: Rc<dyn Fn(u64, u64) -> u64> = Rc::new({
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
      let T = &T_clone;
      let tks = &tks;
      let c = lc(Clone::clone(N), Clone::clone(E0), p);
      let a = Qmult(rocq_array::get::<Rc<Q>>(T, add_1(mul(Clone::clone(k), Clone::clone(w)), c)), Rc::clone(trs));
      let b = Qmult(rocq_array::get::<Rc<Q>>(T, add_1(mul(Clone::clone(r), Clone::clone(w)), c)), Rc::clone(tks));
      let a_clone = Rc::clone(&a);
      let b_clone = Rc::clone(&b);
      if qltb(a_clone, b_clone) {
        std::mem::drop(b);
        std::mem::drop(a);
        1u64
      } else {
        if qltb(b, a) {
          2u64
        } else {
          0u64
        }
      }
    }
  });
  let st = loop_::<u64>(tmp, callback, callback_1, 0u64, 0u64);
  eqb(st, 1u64)
}

// Rocq: Roadtimes.roadtimes_implem.leave
// Variant: uncurried
pub fn leave(T: Rc<Array<Rc<Q>>>, w: u64, N: u64, E0: u64, m: u64, s: u64) -> Rc<option<u64>> {
  let tmp = 0u64;
  let callback: Rc<dyn Fn(u64, Rc<option<u64>>) -> Rc<option<u64>>> = Rc::new({
    let __anf_capture_30 = m;
    move |k: u64, best: Rc<option<u64>>| -> Rc<option<u64>> {
      let T = &T;
      let w = &w;
      let N = &N;
      let E0 = &E0;
      let m = &__anf_capture_30;
      let s = &s;
      let tmp_1 = rocq_bigint::zero();
      let tmp_2 = rocq_bigint::one();
      let tmp_3 = Rc::new(Q { Qnum: tmp_1, Qden: tmp_2 });
      let tmp_4 = rocq_array::get::<Rc<Q>>(T, add_1(mul(k, Clone::clone(w)), Clone::clone(s)));
      if qltb(tmp_3, tmp_4) {
        let (v67, v68) = __rocq_reuse::reset(best, |__payload| Clone::clone(__payload));
        match v67 {
          option::Some(v73) => {
            let w_clone = Clone::clone(w);
            let N_clone = Clone::clone(N);
            let E0_clone = Clone::clone(E0);
            let m_clone = Clone::clone(m);
            let s_clone = Clone::clone(s);
            if lexless(T, w_clone, N_clone, E0_clone, m_clone, k, v73, s_clone) {
              __rocq_reuse::rebuild(v68, option::<u64>::Some(k))
            } else {
              __rocq_reuse::rebuild(v68, option::<u64>::Some(v73))
            }
          },
          option::None => {
            __rocq_reuse::rebuild(v68, option::<u64>::Some(k))
          },
        }
      } else {
        best
      }
    }
  });
  forl::<Rc<option<u64>>>(tmp, m, callback, Rc::new(option::<u64>::None))
}

// Rocq: Roadtimes.roadtimes_implem.qmul
// Variant: uncurried
pub fn qmul(a: Rc<Q>, b: Rc<Q>) -> Rc<Q> {
  qred(Qmult(a, b))
}

// Rocq: Roadtimes.roadtimes_implem.scale_row
// Variant: uncurried
pub fn scale_row(T: Rc<Array<Rc<Q>>>, w: u64, r: u64, inv: Rc<Q>) -> Rc<Array<Rc<Q>>> {
  let tmp = 0u64;
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new({
    let __anf_capture_16 = w;
    move |j: u64, T: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
      let r = &r;
      let w = &__anf_capture_16;
      let inv = &inv;
      let tmp_1 = add_1(mul(Clone::clone(r), Clone::clone(w)), j);
      let tmp_2 = rocq_array::get::<Rc<Q>>(&T, add_1(mul(Clone::clone(r), Clone::clone(w)), j));
      let inv_clone = Rc::clone(inv);
      rocq_array::set::<Rc<Q>>(T, tmp_1, qmul(tmp_2, inv_clone))
    }
  });
  forl::<Rc<Array<Rc<Q>>>>(tmp, w, callback, T)
}

// Rocq: Stdlib.QArith.QArith_base.Qinv
pub fn Qinv(x: Rc<Q>) -> Rc<Q> {
  let x_clone = Rc::clone(&x);
  let tmp = Qnum_owned(x_clone);
  let tmp_1 = Rc::clone(&tmp);
  match rocq_bigint::integer_tag(tmp_1) {
    rocq_bigint::IntegerTag::Zero => {
      std::mem::drop(tmp);
      std::mem::drop(x);
      let tmp_2 = rocq_bigint::zero();
      let tmp_3 = rocq_bigint::one();
      Rc::new(Q { Qnum: tmp_2, Qden: tmp_3 })
    },
    rocq_bigint::IntegerTag::Positive => {
      let p = rocq_bigint::integer_magnitude(tmp);
      let tmp_4 = Qden(x);
      let tmp_5 = rocq_bigint::identity(tmp_4);
      Rc::new(Q { Qnum: tmp_5, Qden: p })
    },
    rocq_bigint::IntegerTag::Negative => {
      let p = rocq_bigint::integer_magnitude(tmp);
      let tmp_6 = Qden(x);
      let tmp_7 = rocq_bigint::neg(tmp_6);
      Rc::new(Q { Qnum: tmp_7, Qden: p })
    },
  }
}

// Rocq: Roadtimes.roadtimes_implem.elim_row
// Variant: uncurried
pub fn elim_row(T: Rc<Array<Rc<Q>>>, w: u64, r: u64, k: u64, f: Rc<Q>) -> Rc<Array<Rc<Q>>> {
  let tmp = 0u64;
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new({
    let __anf_capture_21 = w;
    move |j: u64, T: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
      let r = &r;
      let k = &k;
      let w = &__anf_capture_21;
      let f = &f;
      let a = rocq_array::get::<Rc<Q>>(&T, add_1(mul(Clone::clone(r), Clone::clone(w)), j));
      if qzerob(&a) {
        std::mem::drop(a);
        T
      } else {
        let tmp_1 = add_1(mul(Clone::clone(k), Clone::clone(w)), j);
        let tmp_2 = rocq_array::get::<Rc<Q>>(&T, add_1(mul(Clone::clone(k), Clone::clone(w)), j));
        let f_clone = Rc::clone(f);
        rocq_array::set::<Rc<Q>>(T, tmp_1, qsub(tmp_2, Qmult(f_clone, a)))
      }
    }
  });
  forl::<Rc<Array<Rc<Q>>>>(tmp, w, callback, T)
}

// Rocq: Roadtimes.roadtimes_implem.elim_all
// Variant: uncurried
pub fn elim_all(T: Rc<Array<Rc<Q>>>, w: u64, m: u64, r: u64, s: u64) -> Rc<Array<Rc<Q>>> {
  let tmp = 0u64;
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new({
    move |k: u64, T: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
      let s = &s;
      let w = &w;
      let r = &r;
      let r_clone = Clone::clone(r);
      if eqb(k, r_clone) {
        T
      } else {
        let f = rocq_array::get::<Rc<Q>>(&T, add_1(mul(k, Clone::clone(w)), Clone::clone(s)));
        if qzerob(&f) {
          std::mem::drop(f);
          T
        } else {
          let w_clone = Clone::clone(w);
          let r_clone_1 = Clone::clone(r);
          elim_row(T, w_clone, r_clone_1, k, f)
        }
      }
    }
  });
  forl::<Rc<Array<Rc<Q>>>>(tmp, m, callback, T)
}

// Rocq: Roadtimes.roadtimes_implem.pivot
// Variant: uncurried
pub fn pivot(w: u64, m: u64, st: ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>), r: u64, s: u64) -> ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>) {
  let st_clone = Clone::clone(&st);
  let T = sT(st_clone);
  let st_clone_1 = Clone::clone(&st);
  let O = sO(st_clone_1);
  let B = sB(st);
  let tmp = rocq_array::get::<Rc<Q>>(&T, add_1(mul(r, w), s));
  let T1 = scale_row(T, w, r, Qinv(tmp));
  let T2 = elim_all(T1, w, m, r, s);
  let tmp_1 = rocq_array::get::<Rc<Q>>(&O, s);
  let T2_clone = Rc::clone(&T2);
  let O2 = elim_obj(O, T2_clone, w, r, tmp_1);
  let tmp_2 = (T2, O2);
  let tmp_3 = rocq_array::set::<u64>(B, r, s);
  (tmp_2, tmp_3)
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
      let tmp = Rc::new(sig::<A> { x: v7 });
      Rc::new(sumor::<Rc<sig<A>>>::inleft(tmp))
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
  let tmp = add_1(E0, m);
  let st_clone = Clone::clone(&st);
  let tmp_1 = sO(st_clone);
  let al_clone = Rc::clone(&al);
  let tmp_2 = odec::<u64>(enter(tmp, al_clone, tmp_1));
  let (v29, v30) = __rocq_reuse::reset(tmp_2, |__payload| Clone::clone(__payload));
  std::mem::drop(v30);
  match v29 {
    sumor::inleft(v35) => {
      let (v37, v38) = __rocq_reuse::reset(v35, |__payload| Clone::clone(__payload));
      std::mem::drop(v38);
      match v37 {
        sig { x: v43 } => {
          let st_clone_1 = Clone::clone(&st);
          let tmp_3 = sT(st_clone_1);
          let tmp_4 = add_1(E0, m);
          let tmp_5 = odec::<u64>(leave(tmp_3, add_1(tmp_4, 1u64), add_1(E0, m), E0, m, v43));
          let (v88, v89) = __rocq_reuse::reset(tmp_5, |__payload| Clone::clone(__payload));
          std::mem::drop(v89);
          match v88 {
            sumor::inleft(v94) => {
              let s0 = &v94;
              match &**s0 {
                sig { x: r } => {
                  let tmp_6 = add_1(E0, m);
                  let tmp_7 = add_1(tmp_6, 1u64);
                  let tmp_8 = st;
                  let r_clone = Clone::clone(r);
                  std::mem::drop(v94);
                  let tmp_9 = pivot(tmp_7, m, tmp_8, r_clone, v43);
                  sloop(m, E0, al, tmp_9, ())
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
  let tmp = rocq_array::make::<bool>(add_1(E0, m), true);
  let tmp_1 = st0(T0, m, E0, A0);
  sloop_1(m, E0, tmp, tmp_1)
}

// Rocq: Roadtimes.roadtimes_implem.al2
// Variant: uncurried
pub fn al2(O1: Rc<Array<Rc<Q>>>, A0: u64, N: u64) -> Rc<Array<bool>> {
  let tmp = 0u64;
  let callback: Rc<dyn Fn(u64, Rc<Array<bool>>) -> Rc<Array<bool>>> = Rc::new({
    move |j: u64, a: Rc<Array<bool>>| -> Rc<Array<bool>> {
      let A0 = &A0;
      let O1 = &O1;
      let tmp_1 = ltb(j, Clone::clone(A0));
      let tmp_2 = rocq_array::get::<Rc<Q>>(O1, j);
      rocq_array::set::<bool>(a, j, andb(tmp_1, qzerob_owned(tmp_2)))
    }
  });
  let tmp_3 = rocq_array::make::<bool>(N, false);
  forl::<Rc<Array<bool>>>(tmp, N, callback, tmp_3)
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
  let tmp = rocq_bigint::zero();
  let z_clone = Rc::clone(&z);
  let tmp_1 = ltb_1(tmp, z_clone);
  match bdec(tmp_1) {
    sumbool::left => {
      let tmp_2 = rocq_bigint::one();
      let tmp_3 = rocq_bigint::twice(tmp_2);
      let tmp_4 = rocq_bigint::identity(tmp_3);
      let z_clone_1 = Rc::clone(&z);
      let tmp_5 = div_1(z_clone_1, tmp_4);
      let r = iofz_rec(tmp_5, ());
      let tmp_6 = rocq_bigint::one();
      let tmp_7 = rocq_bigint::twice(tmp_6);
      let tmp_8 = rocq_bigint::identity(tmp_7);
      let tmp_9 = modulo(z, tmp_8);
      let tmp_10 = rocq_bigint::zero();
      if eqb_1(tmp_9, tmp_10) {
        add_1(r, r)
      } else {
        let tmp_11 = add_1(r, r);
        add_1(tmp_11, 1u64)
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
  let q_clone = Rc::clone(&q);
  let tmp = Qnum_owned(q_clone);
  let tmp_1 = rocq_bigint::one();
  let tmp_2 = rocq_bigint::twice(tmp_1);
  let tmp_3 = rocq_bigint::twice(tmp_2);
  let tmp_4 = rocq_bigint::twice(tmp_3);
  let tmp_5 = rocq_bigint::twice(tmp_4);
  let tmp_6 = rocq_bigint::twice(tmp_5);
  let tmp_7 = rocq_bigint::twice(tmp_6);
  let tmp_8 = rocq_bigint::twice(tmp_7);
  let tmp_9 = rocq_bigint::twice(tmp_8);
  let tmp_10 = rocq_bigint::twice(tmp_9);
  let tmp_11 = rocq_bigint::twice(tmp_10);
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
  let tmp_31 = rocq_bigint::twice(tmp_30);
  let tmp_32 = rocq_bigint::twice(tmp_31);
  let tmp_33 = rocq_bigint::twice(tmp_32);
  let tmp_34 = rocq_bigint::twice(tmp_33);
  let tmp_35 = rocq_bigint::twice(tmp_34);
  let tmp_36 = rocq_bigint::twice(tmp_35);
  let tmp_37 = rocq_bigint::twice(tmp_36);
  let tmp_38 = rocq_bigint::identity(tmp_37);
  let tmp_39 = mul_2(tmp, tmp_38);
  let tmp_40 = Qden(q);
  let tmp_41 = rocq_bigint::identity(tmp_40);
  let mz = div_1(tmp_39, tmp_41);
  div_2(of_uint63(iofz(mz)), of_uint63(__rocq_global_2268))
}

// Rocq: Roadtimes.roadtimes_implem.dq
// Variant: borrowed, uncurried
pub fn dq(n: u64, D: &Rc<Array<u64>>, s: u64, d: u64) -> Rc<Q> {
  let n_1 = n;
  let s_1 = s;
  let d_1 = d;
  let tmp = zofi(rocq_array::get::<u64>(D, add_1(mul(s_1, n_1), d_1)));
  inject_Z(tmp)
}

// Rocq: Roadtimes.roadtimes_implem.mk2
// Variant: uncurried
pub fn mk2(st1: ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>), carr: Rc<Array<Rc<Q>>>, w: u64, m: u64) -> ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>) {
  let st1_clone = Clone::clone(&st1);
  let tmp = sT(st1_clone);
  let tmp_1 = rocq_array::copy::<Rc<Q>>(&tmp);
  std::mem::drop(tmp);
  let st1_clone_1 = Clone::clone(&st1);
  let tmp_2 = sT(st1_clone_1);
  let st1_clone_2 = Clone::clone(&st1);
  let tmp_3 = sB(st1_clone_2);
  let tmp_4 = canon_obj(tmp_2, tmp_3, carr, w, m);
  let tmp_5 = (tmp_1, tmp_4);
  let tmp_6 = sB(st1);
  let tmp_7 = rocq_array::copy::<u64>(&tmp_6);
  std::mem::drop(tmp_6);
  (tmp_5, tmp_7)
}

// Rocq: Roadtimes.roadtimes_implem.phase2
// Variant: uncurried
pub fn phase2(T0: Rc<Array<Rc<Q>>>, m: u64, E0: u64, _A0: u64, st1: ((Rc<Array<Rc<Q>>>, Rc<Array<Rc<Q>>>), Rc<Array<u64>>), al: Rc<Array<bool>>, carr: Rc<Array<Rc<Q>>>) -> Rc<Q> {
  let tmp = rocq_array::length::<Rc<Q>>(&carr);
  let tmp_1 = add_1(E0, m);
  let tmp_2 = eqb(tmp, add_1(tmp_1, 1u64));
  let tmp_3 = rocq_array::get::<Rc<Q>>(&carr, add_1(E0, m));
  let tmp_4 = andb(tmp_2, qzerob_owned(tmp_3));
  match bdec(tmp_4) {
    sumbool::left => {
      std::mem::drop(T0);
      let tmp_5 = add_1(E0, m);
      let tmp_6 = mk2(st1, carr, add_1(tmp_5, 1u64), m);
      let st3 = sloop_1(m, E0, al, tmp_6);
      let tmp_7 = sO(st3);
      let tmp_8 = rocq_array::get::<Rc<Q>>(&tmp_7, add_1(E0, m));
      std::mem::drop(tmp_7);
      Qopp(tmp_8)
    },
    sumbool::right => {
      std::mem::drop(T0);
      std::mem::drop(st1);
      std::mem::drop(al);
      std::mem::drop(carr);
      let tmp_9 = rocq_bigint::zero();
      let tmp_10 = rocq_bigint::one();
      Rc::new(Q { Qnum: tmp_9, Qden: tmp_10 })
    },
  }
}

// Rocq: Roadtimes.roadtimes_implem.qcost
// Variant: uncurried
pub fn qcost(E: u64, w: u64, cnt: Rc<Array<u64>>, neg: bool) -> Rc<Array<Rc<Q>>> {
  let tmp = 0u64;
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<Q>>>) -> Rc<Array<Rc<Q>>>> = Rc::new({
    move |e: u64, c: Rc<Array<Rc<Q>>>| -> Rc<Array<Rc<Q>>> {
      let neg = &neg;
      let cnt = &cnt;
      let tmp_1 = if *neg {
        let tmp_2 = rocq_array::get::<u64>(cnt, e);
        let tmp_3 = zofi(tmp_2);
        opp(tmp_3)
      } else {
        let tmp_4 = rocq_array::get::<u64>(cnt, e);
        zofi(tmp_4)
      };
      rocq_array::set::<Rc<Q>>(c, e, inject_Z(tmp_1))
    }
  });
  let tmp_5 = rocq_bigint::zero();
  let tmp_6 = rocq_bigint::one();
  let tmp_7 = rocq_array::make::<Rc<Q>>(w, Rc::new(Q { Qnum: tmp_5, Qden: tmp_6 }));
  forl::<Rc<Array<Rc<Q>>>>(tmp, E, callback, tmp_7)
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
  let tmp = add_1(E_1, RR_1);
  let tmp_1 = add_1(E_1, E_1);
  let tmp_2 = add_1(E_1, RR_1);
  let tmp_3 = add_1(E_1, tmp_2);
  let tmp_4 = add_1(tmp_3, 1u64);
  let tmp_5 = route_cnt(n_1, E_1, D, X, I, s_1, d_1);
  let tmp_6 = qcost(E_1, tmp_4, tmp_5, neg_1);
  let T0_clone = Rc::clone(T0);
  let al_clone = Rc::clone(al);
  phase2(T0_clone, tmp, E_1, tmp_1, st1_1, al_clone, tmp_6)
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
  let tmp = dq(n_1, D, s_1, d_1);
  let tmp_1 = D;
  let tmp_2 = X;
  let tmp_3 = I;
  let tmp_4 = T0;
  let st1_clone = Clone::clone(&st1_1);
  (q2f(Qplus(tmp, vq(n_1, E_1, RR_1, tmp_1, tmp_2, tmp_3, tmp_4, st1_clone, al, s_1, d_1, false))), q2f(Qminus(dq(n_1, D, s_1, d_1), vq(n_1, E_1, RR_1, D, X, I, T0, st1_1, al, s_1, d_1, true))))
}

// Rocq: Roadtimes.roadtimes_implem.aget
// Variant: borrowed, uncurried
pub fn aget(t: &Rc<Array<u64>>, i: u64) -> u64 {
  let i_1 = i;
  rocq_array::get::<u64>(t, i_1)
}

// Rocq: Roadtimes.roadtimes_implem.answers
// Variant: uncurried
pub fn answers(n: u64, E: u64, RR: u64, D: Rc<Array<u64>>, X: Rc<Array<u64>>, I: Rc<Array<u64>>, T0: Rc<Array<Rc<Q>>>, xqs: Rc<Array<u64>>, xqd: Rc<Array<u64>>) -> Rc<Array<(f64, f64)>> {
  let tmp = add_1(E, RR);
  let tmp_1 = add_1(E, E);
  let T0_clone = Rc::clone(&T0);
  let st1 = phase1(T0_clone, tmp, E, tmp_1);
  let st1_clone = Clone::clone(&st1);
  let tmp_2 = sO(st1_clone);
  let tmp_3 = add_1(E, E);
  let tmp_4 = add_1(E, RR);
  let al = al2(tmp_2, tmp_3, add_1(E, tmp_4));
  let tmp_5 = 0u64;
  let tmp_6 = rocq_array::length::<u64>(&xqs);
  let xqs_clone = Rc::clone(&xqs);
  let callback: Rc<dyn Fn(u64, Rc<Array<(f64, f64)>>) -> Rc<Array<(f64, f64)>>> = Rc::new({
    let __anf_capture_98 = E;
    let __anf_capture_100 = RR;
    let __anf_capture_108 = T0;
    let __anf_capture_110 = st1;
    move |j: u64, out: Rc<Array<(f64, f64)>>| -> Rc<Array<(f64, f64)>> {
      let xqs = &xqs_clone;
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
      let tmp_7 = aget(xqs, j);
      let tmp_8 = aget(xqd, j);
      let tmp_9 = qans(Clone::clone(n), Clone::clone(E), Clone::clone(RR), D, X, I, T0, Clone::clone(st1), al, tmp_7, tmp_8);
      rocq_array::set::<(f64, f64)>(out, j, tmp_9)
    }
  });
  let tmp_10 = rocq_array::length::<u64>(&xqs);
  std::mem::drop(xqs);
  let tmp_11 = rocq_array::make::<(f64, f64)>(tmp_10, (__rocq_global_2601, __rocq_global_2601));
  forl::<Rc<Array<(f64, f64)>>>(tmp_5, tmp_6, callback, tmp_11)
}

// Rocq: Roadtimes.roadtimes_implem.roadtimes_impl
// Variant: uncurried
pub fn roadtimes_impl(xdist: Rc<Array<Rc<Array<u64>>>>, xrs: Rc<Array<u64>>, xrd: Rc<Array<u64>>, xrt: Rc<Array<u64>>, xqs: Rc<Array<u64>>, xqd: Rc<Array<u64>>) -> Rc<Array<(f64, f64)>> {
  let n = rocq_array::length::<Rc<Array<u64>>>(&xdist);
  let W = flatten(n, xdist);
  let W_clone = Rc::clone(&W);
  let FW = fw(n, W_clone);
  let FW_clone = Clone::clone(&FW);
  let D = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(FW_clone);
  let X = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(FW);
  let W_clone_1 = Rc::clone(&W);
  let SR = scan_roads(n, W_clone_1);
  let SR_clone = Clone::clone(&SR);
  let I = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(SR_clone));
  let SR_clone_1 = Clone::clone(&SR);
  let P = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(SR_clone_1));
  let E = snd::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(SR);
  let RR = rocq_array::length::<u64>(&xrs);
  let tmp = guard(E, RR);
  match bdec(tmp) {
    sumbool::left => {
      let D_clone = Rc::clone(&D);
      let X_clone = Rc::clone(&X);
      let I_clone = Rc::clone(&I);
      let T0 = build_T(n, E, RR, W, D_clone, X_clone, I_clone, P, xrs, xrd, xrt);
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
      let tmp_1 = rocq_array::length::<u64>(&xqs);
      std::mem::drop(xqs);
      rocq_array::make::<(f64, f64)>(tmp_1, (__rocq_global_2601, __rocq_global_2601))
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
const __rocq_global_461: u64 = 1073741824u64;
const __rocq_global_2268: u64 = 68719476736u64;
const __rocq_global_2601: f64 = f64::from_bits(0u64);