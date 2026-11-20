#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};
#[allow(unused_imports)] use rocq_bigint::{self as b, BigInt};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

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

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::PositiveTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::NaturalTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::IntegerTag>; };

pub type sint = Int63;

pub type uint = Int63;

pub type SState = ((Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>);

// Rocq: Roadtimes.roadtimes_implem.INF
pub fn INF() -> Int63 {
  int63!(1073741824)
}

// Rocq: Roadtimes.roadtimes_implem.two36
pub fn two36() -> Int63 {
  int63!(68719476736)
}

// Rocq: Corelib.Floats.PrimFloat.zero
pub fn zero() -> f64 {
  f64::from_bits(0u64)
}

// Rocq: Roadtimes.roadtimes_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Roadtimes.roadtimes_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: Int63, cont: Rc<dyn Fn(Int63, St) -> bool>, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Roadtimes.roadtimes_implem.wloop (local: wloop)
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

// Rocq: Roadtimes.roadtimes_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: Int63, cont: Rc<dyn Fn(Int63, St) -> bool>, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop_1::<St>(hi, cont, f, i, s)
}

// Rocq: Roadtimes.roadtimes_implem.forl
// Variant: uncurried
pub fn forl<St: Clone + 'static>(lo: Int63, hi: Int63, f: Rc<dyn Fn(Int63, St) -> St>, s: St) -> St {
  let callback: Rc<dyn Fn(Int63, St) -> bool> = Rc::new(move |_v6: Int63, v7: St| -> bool {
    std::mem::drop(v7);
    true
  });
  loop_::<St>(hi, callback, f, lo, s)
}

// Rocq: Roadtimes.roadtimes_implem.fill2
// Variant: uncurried
pub fn fill2(n: Int63, g: Rc<dyn Fn(Int63, Int63) -> Int63>, A: Array<Int63>) -> Array<Int63> {
  let tmp = int63!(0);
  let callback: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
    let __anf_capture_13 = n;
    move |i: Int63, A: Array<Int63>| -> Array<Int63> {
      let g = &g;
      let n = &__anf_capture_13;
      let tmp_1 = int63!(0);
      let n_clone = Clone::clone(n);
      let g_clone: Rc<dyn Fn(Int63, Int63) -> Int63> = Rc::clone(g);
      let callback_1: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
        move |j: Int63, A: Array<Int63>| -> Array<Int63> {
          let n = &n_clone;
          let g = &g_clone;
          let tmp_2 = Clone::clone(&i) * Clone::clone(n) + j;
          let tmp_3 = g(Clone::clone(&i), j);
          A.set(tmp_2, tmp_3)
        }
      });
      let n_clone_1 = Clone::clone(n);
      forl::<Array<Int63>>(tmp_1, n_clone_1, callback_1, A)
    }
  });
  forl::<Array<Int63>>(tmp, n, callback, A)
}

// Rocq: Roadtimes.roadtimes_implem.flatten
// Variant: uncurried
pub fn flatten(n: Int63, x: Array<Array<Int63>>) -> Array<Int63> {
  let callback: Rc<dyn Fn(Int63, Int63) -> Int63> = Rc::new({
    move |i: Int63, j: Int63| -> Int63 {
      let x = &x;
      let x_clone = Clone::clone(x);
      let tmp = &x_clone;
      let tmp_1 = tmp.get_cloned(i);
      std::mem::drop(x_clone);
      let tmp_2 = tmp_1.get_cloned(j);
      std::mem::drop(tmp_1);
      tmp_2
    }
  });
  let tmp_3 = n * n;
  fill2(n, callback, Array::<Int63>::make(tmp_3, int63!(0)))
}

// Rocq: Roadtimes.roadtimes_implem.isroad
pub fn isroad(e: Int63) -> bool {
  int63!(0).ltsb(e)
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
pub fn fw_cell(n: Int63, k: Int63, i: Int63, j: Int63, st: (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>) {
  let st_clone = Clone::clone(&st);
  let D = fst::<Array<Int63>, Array<Int63>>(st_clone);
  let st_clone_1 = Clone::clone(&st);
  let X = snd::<Array<Int63>, Array<Int63>>(st_clone_1);
  let tmp = D.get_cloned(i * n + k);
  let tmp_1 = D.get_cloned(k * n + j);
  let a_1 = tmp + tmp_1;
  let tmp_2 = D.get_cloned(i * n + j);
  if a_1 < tmp_2 {
    std::mem::drop(st);
    let tmp_3 = D.set(i * n + j, a_1);
    let tmp_4 = i * n + j;
    let tmp_5 = X.get_cloned(i * n + k);
    (tmp_3, X.set(tmp_4, tmp_5))
  } else {
    std::mem::drop(X);
    std::mem::drop(D);
    st
  }
}

// Rocq: Roadtimes.roadtimes_implem.fw_iter
// Variant: uncurried
pub fn fw_iter(n: Int63, k: Int63, st: (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>) {
  let tmp = int63!(0);
  let callback: Rc<dyn Fn(Int63, (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>)> = Rc::new({
    let __anf_capture_13 = n;
    move |i: Int63, st: (Array<Int63>, Array<Int63>)| -> (Array<Int63>, Array<Int63>) {
      let k = &k;
      let n = &__anf_capture_13;
      let tmp_1 = int63!(0);
      let n_clone = Clone::clone(n);
      let k_clone = Clone::clone(k);
      let callback_1: Rc<dyn Fn(Int63, (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>)> = Rc::new({
        move |j: Int63, st: (Array<Int63>, Array<Int63>)| -> (Array<Int63>, Array<Int63>) {
          let tmp_2 = Clone::clone(&n_clone);
          let tmp_3 = Clone::clone(&k_clone);
          let i_clone = Clone::clone(&i);
          fw_cell(tmp_2, tmp_3, i_clone, j, st)
        }
      });
      let n_clone_1 = Clone::clone(n);
      forl::<(Array<Int63>, Array<Int63>)>(tmp_1, n_clone_1, callback_1, st)
    }
  });
  forl::<(Array<Int63>, Array<Int63>)>(tmp, n, callback, st)
}

// Rocq: Roadtimes.roadtimes_implem.fw
// Variant: uncurried
pub fn fw(n: Int63, W: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  let callback: Rc<dyn Fn(Int63, Int63) -> Int63> = Rc::new({
    let __anf_capture_8 = n;
    move |i: Int63, j: Int63| -> Int63 {
      let n = &__anf_capture_8;
      let W = &W;
      if i == j {
        int63!(0)
      } else {
        let tmp = W.get_cloned(i * Clone::clone(n) + j);
        if isroad(tmp) {
          let tmp_1 = i * Clone::clone(n) + j;
          W.get_cloned(tmp_1)
        } else {
          __rocq_global_461
        }
      }
    }
  });
  let tmp_2 = n * n;
  let D0 = fill2(n, callback, Array::<Int63>::make(tmp_2, int63!(0)));
  let callback_1: Rc<dyn Fn(Int63, Int63) -> Int63> = Rc::new(move |_i: Int63, j: Int63| -> Int63 {
    j
  });
  let tmp_3 = n * n;
  let X0 = fill2(n, callback_1, Array::<Int63>::make(tmp_3, int63!(0)));
  let tmp_4 = int63!(0);
  let callback_2: Rc<dyn Fn(Int63, (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>)> = Rc::new({
    let __anf_capture_127 = n;
    move |k: Int63, st: (Array<Int63>, Array<Int63>)| -> (Array<Int63>, Array<Int63>) {
      let tmp_5 = Clone::clone(&__anf_capture_127);
      fw_iter(tmp_5, k, st)
    }
  });
  forl::<(Array<Int63>, Array<Int63>)>(tmp_4, n, callback_2, (D0, X0))
}

// Rocq: Roadtimes.roadtimes_implem.scan_roads
// Variant: uncurried
pub fn scan_roads(n: Int63, W: Array<Int63>) -> ((Array<Int63>, Array<Int63>), Int63) {
  let tmp = int63!(0);
  let tmp_1 = n * n;
  let callback: Rc<dyn Fn(Int63, ((Array<Int63>, Array<Int63>), Int63)) -> ((Array<Int63>, Array<Int63>), Int63)> = Rc::new({
    move |p: Int63, st: ((Array<Int63>, Array<Int63>), Int63)| -> ((Array<Int63>, Array<Int63>), Int63) {
      let W = &W;
      let st_clone = Clone::clone(&st);
      let I = fst::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), Int63>(st_clone));
      let st_clone_1 = Clone::clone(&st);
      let P = snd::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), Int63>(st_clone_1));
      let st_clone_2 = Clone::clone(&st);
      let e = snd::<(Array<Int63>, Array<Int63>), Int63>(st_clone_2);
      let tmp_2 = W.get_cloned(p);
      if isroad(tmp_2) {
        std::mem::drop(st);
        ((I.set(p, e), P.set(e, p)), e + int63!(1))
      } else {
        std::mem::drop(P);
        std::mem::drop(I);
        st
      }
    }
  });
  forl::<((Array<Int63>, Array<Int63>), Int63)>(tmp, tmp_1, callback, ((Array::<Int63>::make(n * n, int63!(0)), Array::<Int63>::make(n * n, int63!(0))), int63!(0)))
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

// Rocq: Roadtimes.roadtimes_implem.guard
// Variant: uncurried
pub fn guard(E: Int63, R: Int63) -> bool {
  let tmp = andb(int63!(1) <= E + R, E <= int63!(2048));
  let tmp_1 = andb(tmp, R <= int63!(2048));
  let tmp_2 = E + R;
  let tmp_3 = E + R;
  andb(tmp_1, tmp_2 * (E + tmp_3 + int63!(1)) <= int63!(4194303))
}

// Rocq: Stdlib.QArith.QArith_base.inject_Z
pub fn inject_Z(x: Rc<BigInt>) -> Rc<Q> {
  let tmp = b::one();
  Rc::new(Q { Qnum: x, Qden: tmp })
}

// Rocq: Roadtimes.roadtimes_implem.zofi_rec
pub fn zofi_rec_1(i: Int63) -> Rc<BigInt> {
  zofi_rec(i, ())
}

// Rocq: Roadtimes.roadtimes_implem.zofi_rec (local: zofi_rec)
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

// Rocq: Roadtimes.roadtimes_implem.zofi
pub fn zofi(i: Int63) -> Rc<BigInt> {
  zofi_rec_1(i)
}

// Rocq: Roadtimes.roadtimes_implem.zofs
pub fn zofs(i: Int63) -> Rc<BigInt> {
  if i < int63!(4611686018427387904) {
    zofi(i)
  } else {
    let tmp = zofi(i);
    let tmp_1 = b::one();
    let tmp_2 = b::twice(tmp_1);
    let tmp_3 = b::twice(tmp_2);
    let tmp_4 = b::twice(tmp_3);
    let tmp_5 = b::twice(tmp_4);
    let tmp_6 = b::twice(tmp_5);
    let tmp_7 = b::twice(tmp_6);
    let tmp_8 = b::twice(tmp_7);
    let tmp_9 = b::twice(tmp_8);
    let tmp_10 = b::twice(tmp_9);
    let tmp_11 = b::twice(tmp_10);
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
    let tmp_43 = b::twice(tmp_42);
    let tmp_44 = b::twice(tmp_43);
    let tmp_45 = b::twice(tmp_44);
    let tmp_46 = b::twice(tmp_45);
    let tmp_47 = b::twice(tmp_46);
    let tmp_48 = b::twice(tmp_47);
    let tmp_49 = b::twice(tmp_48);
    let tmp_50 = b::twice(tmp_49);
    let tmp_51 = b::twice(tmp_50);
    let tmp_52 = b::twice(tmp_51);
    let tmp_53 = b::twice(tmp_52);
    let tmp_54 = b::twice(tmp_53);
    let tmp_55 = b::twice(tmp_54);
    let tmp_56 = b::twice(tmp_55);
    let tmp_57 = b::twice(tmp_56);
    let tmp_58 = b::twice(tmp_57);
    let tmp_59 = b::twice(tmp_58);
    let tmp_60 = b::twice(tmp_59);
    let tmp_61 = b::twice(tmp_60);
    let tmp_62 = b::twice(tmp_61);
    let tmp_63 = b::twice(tmp_62);
    let tmp_64 = b::twice(tmp_63);
    let tmp_65 = b::identity(tmp_64);
    b::sub(tmp, tmp_65)
  }
}

// Rocq: Roadtimes.roadtimes_implem.bound_rows
// Variant: uncurried
pub fn bound_rows(E: Int63, w: Int63, N: Int63, W: Array<Int63>, P: Array<Int63>, T: Array<Rc<Q>>) -> Array<Rc<Q>> {
  let tmp = int63!(0);
  let callback: Rc<dyn Fn(Int63, Array<Rc<Q>>) -> Array<Rc<Q>>> = Rc::new({
    let __anf_capture_24 = E;
    move |e: Int63, T: Array<Rc<Q>>| -> Array<Rc<Q>> {
      let P = &P;
      let W = &W;
      let E = &__anf_capture_24;
      let w = &w;
      let N = &N;
      let u = W.get_cloned(P.get_cloned(e));
      let tmp_1 = e * Clone::clone(w) + e;
      let tmp_2 = b::one();
      let tmp_3 = b::identity(tmp_2);
      let tmp_4 = b::one();
      let T_1 = T.set(tmp_1, Rc::new(Q { Qnum: tmp_3, Qden: tmp_4 }));
      let tmp_5 = e * Clone::clone(w) + (Clone::clone(E) + e);
      let tmp_6 = b::one();
      let tmp_7 = b::identity(tmp_6);
      let tmp_8 = b::one();
      let T_2 = T_1.set(tmp_5, Rc::new(Q { Qnum: tmp_7, Qden: tmp_8 }));
      let tmp_9 = e * Clone::clone(w) + Clone::clone(N);
      let tmp_10 = if isroad(u) {
        let tmp_11 = zofs(u);
        inject_Z(tmp_11)
      } else {
        let tmp_12 = b::zero();
        let tmp_13 = b::one();
        Rc::new(Q { Qnum: tmp_12, Qden: tmp_13 })
      };
      T_2.set(tmp_9, tmp_10)
    }
  });
  forl::<Array<Rc<Q>>>(tmp, E, callback, T)
}

// Rocq: Roadtimes.roadtimes_implem.walk
// Variant: uncurried
pub fn walk_1(n: Int63, d: Int63, E: Int63, D: Array<Int63>, X: Array<Int63>, I: Array<Int63>, cur: Int63, cnt: Array<Int63>) -> Array<Int63> {
  walk(n, d, E, D, X, I, cur, cnt, ())
}

// Rocq: Roadtimes.roadtimes_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(n: Int63, d: Int63, E: Int63, D: Array<Int63>, X: Array<Int63>, I: Array<Int63>, cur: Int63, cnt: Array<Int63>, _H: ()) -> Array<Int63> {
  if cur == d {
    std::mem::drop(D);
    std::mem::drop(X);
    std::mem::drop(I);
    cnt
  } else {
    let v = X.get_cloned(cur * n + d);
    let tmp = D.get_cloned(v * n + d);
    let tmp_1 = D.get_cloned(cur * n + d);
    let tmp_2 = tmp < tmp_1;
    match bdec(tmp_2) {
      sumbool::left => {
        let e = I.get_cloned(cur * n + v);
        let tmp_3 = if e < E {
          let tmp_4 = cnt.get_cloned(e);
          cnt.set(e, tmp_4 + int63!(1))
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
pub fn route_cnt_owned(n: Int63, E: Int63, D: Array<Int63>, X: Array<Int63>, I: Array<Int63>, s: Int63, d: Int63) -> Array<Int63> {
  let tmp = Array::<Int63>::make(E, int63!(0));
  walk_1(n, d, E, D, X, I, s, tmp)
}

// Rocq: Roadtimes.roadtimes_implem.route_cnt
// Variant: borrowed, uncurried
pub fn route_cnt(n: Int63, E: Int63, D: &Array<Int63>, X: &Array<Int63>, I: &Array<Int63>, s: Int63, d: Int63) -> Array<Int63> {
  let n_1 = n;
  let E_1 = E;
  let s_1 = s;
  let d_1 = d;
  let tmp = Array::<Int63>::make(E_1, int63!(0));
  walk_1(n_1, d_1, E_1, Clone::clone(D), Clone::clone(X), Clone::clone(I), s_1, tmp)
}

// Rocq: Roadtimes.roadtimes_implem.deliv_row
// Variant: uncurried
pub fn deliv_row(n: Int63, E: Int63, w: Int63, N: Int63, D: Array<Int63>, X: Array<Int63>, I: Array<Int63>, rs: Array<Int63>, rd: Array<Int63>, rt: Array<Int63>, k: Int63, T: Array<Rc<Q>>) -> Array<Rc<Q>> {
  let s = rs.get_cloned(k);
  std::mem::drop(rs);
  let d = rd.get_cloned(k);
  std::mem::drop(rd);
  let D_clone = Clone::clone(&D);
  let cnt = route_cnt_owned(n, E, D_clone, X, I, s, d);
  let tmp = rt.get_cloned(k);
  std::mem::drop(rt);
  let tmp_1 = zofi(tmp);
  let tmp_2 = D.get_cloned(s * n + d);
  std::mem::drop(D);
  let tmp_3 = zofi(tmp_2);
  let b_1 = b::sub(tmp_1, tmp_3);
  let i = E + k;
  let tmp_4 = int63!(0);
  let b_clone = Rc::clone(&b_1);
  let callback: Rc<dyn Fn(Int63, Array<Rc<Q>>) -> Array<Rc<Q>>> = Rc::new({
    let __anf_capture_90 = i;
    let __anf_capture_92 = w;
    move |e: Int63, T: Array<Rc<Q>>| -> Array<Rc<Q>> {
      let i = &__anf_capture_90;
      let w = &__anf_capture_92;
      let b_1 = &b_clone;
      let cnt = &cnt;
      let tmp_5 = Clone::clone(i) * Clone::clone(w) + e;
      let tmp_6 = b::zero();
      let b_clone_1 = Rc::clone(b_1);
      let tmp_7 = if b::lt(b_clone_1, tmp_6) {
        let tmp_8 = cnt.get_cloned(e);
        let tmp_9 = zofi(tmp_8);
        b::neg(tmp_9)
      } else {
        let tmp_10 = cnt.get_cloned(e);
        zofi(tmp_10)
      };
      T.set(tmp_5, inject_Z(tmp_7))
    }
  });
  let T_1 = forl::<Array<Rc<Q>>>(tmp_4, E, callback, T);
  let tmp_11 = i * w + (E + E + k);
  let tmp_12 = b::one();
  let tmp_13 = b::identity(tmp_12);
  let tmp_14 = b::one();
  let T_2 = T_1.set(tmp_11, Rc::new(Q { Qnum: tmp_13, Qden: tmp_14 }));
  let tmp_15 = i * w + N;
  let tmp_16 = b::abs(b_1);
  T_2.set(tmp_15, inject_Z(tmp_16))
}

// Rocq: Roadtimes.roadtimes_implem.build_T
// Variant: uncurried
pub fn build_T(n: Int63, E: Int63, R: Int63, W: Array<Int63>, D: Array<Int63>, X: Array<Int63>, I: Array<Int63>, P: Array<Int63>, rs: Array<Int63>, rd: Array<Int63>, rt: Array<Int63>) -> Array<Rc<Q>> {
  let m = E + R;
  let w = E + m + int63!(1);
  let N = E + m;
  let tmp = m * w;
  let tmp_1 = b::zero();
  let tmp_2 = b::one();
  let T = bound_rows(E, w, N, W, P, Array::<Rc<Q>>::make(tmp, Rc::new(Q { Qnum: tmp_1, Qden: tmp_2 })));
  let tmp_3 = int63!(0);
  let callback: Rc<dyn Fn(Int63, Array<Rc<Q>>) -> Array<Rc<Q>>> = Rc::new({
    let __anf_capture_97 = E;
    let __anf_capture_99 = w;
    let __anf_capture_101 = N;
    move |k: Int63, T: Array<Rc<Q>>| -> Array<Rc<Q>> {
      let n_clone = Clone::clone(&n);
      let tmp_4 = Clone::clone(&__anf_capture_97);
      let tmp_5 = Clone::clone(&__anf_capture_99);
      let tmp_6 = Clone::clone(&__anf_capture_101);
      let D_clone = Clone::clone(&D);
      let X_clone = Clone::clone(&X);
      let I_clone = Clone::clone(&I);
      let rs_clone = Clone::clone(&rs);
      let rd_clone = Clone::clone(&rd);
      let rt_clone = Clone::clone(&rt);
      deliv_row(n_clone, tmp_4, tmp_5, tmp_6, D_clone, X_clone, I_clone, rs_clone, rd_clone, rt_clone, k, T)
    }
  });
  forl::<Array<Rc<Q>>>(tmp_3, R, callback, T)
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

// Rocq: Roadtimes.roadtimes_implem.sT
pub fn sT(st: ((Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>)) -> Array<Rc<Q>> {
  fst::<Array<Rc<Q>>, Array<Rc<Q>>>(fst::<(Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>>(st))
}

// Rocq: Roadtimes.roadtimes_implem.sO
pub fn sO(st: ((Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>)) -> Array<Rc<Q>> {
  snd::<Array<Rc<Q>>, Array<Rc<Q>>>(fst::<(Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>>(st))
}

// Rocq: Roadtimes.roadtimes_implem.sB
pub fn sB(st: ((Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>)) -> Array<Int63> {
  snd::<(Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>>(st)
}

// Rocq: Roadtimes.roadtimes_implem.cart
// Variant: uncurried
pub fn cart(w: Int63, A0: Int63, N: Int63) -> Array<Rc<Q>> {
  let callback: Rc<dyn Fn(Int63, Array<Rc<Q>>) -> Array<Rc<Q>>> = Rc::new(move |j: Int63, c: Array<Rc<Q>>| -> Array<Rc<Q>> {
    let tmp = b::one();
    let tmp_1 = b::identity(tmp);
    let tmp_2 = b::one();
    c.set(j, Rc::new(Q { Qnum: tmp_1, Qden: tmp_2 }))
  });
  let tmp_3 = b::zero();
  let tmp_4 = b::one();
  forl::<Array<Rc<Q>>>(A0, N, callback, Array::<Rc<Q>>::make(w, Rc::new(Q { Qnum: tmp_3, Qden: tmp_4 })))
}

// Rocq: Roadtimes.roadtimes_implem.binit
// Variant: uncurried
pub fn binit(m: Int63, E0: Int63) -> Array<Int63> {
  let tmp = int63!(0);
  let callback: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
    move |k: Int63, B: Array<Int63>| -> Array<Int63> {
      let E0_clone = Clone::clone(&E0);
      let tmp_1 = E0_clone + k;
      B.set(k, tmp_1)
    }
  });
  let tmp_2 = Array::<Int63>::make(m, int63!(0));
  forl::<Array<Int63>>(tmp, m, callback, tmp_2)
}

// Rocq: Roadtimes.roadtimes_implem.qzerob
pub fn qzerob_owned(a_1: Rc<Q>) -> bool {
  let tmp = Qnum_owned(a_1);
  let tmp_1 = b::zero();
  b::equal(tmp, tmp_1)
}

// Rocq: Roadtimes.roadtimes_implem.qzerob
// Variant: borrowed
pub fn qzerob(a_1: &Rc<Q>) -> bool {
  let tmp = Qnum(a_1);
  let tmp_1 = b::zero();
  b::equal(tmp, tmp_1)
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

// Rocq: Roadtimes.roadtimes_implem.qred
pub fn qred(q: Rc<Q>) -> Rc<Q> {
  let q_clone = Rc::clone(&q);
  let n = Qnum_owned(q_clone);
  let tmp = Qden(q);
  let d = b::identity(tmp);
  let n_clone = Rc::clone(&n);
  let d_clone = Rc::clone(&d);
  let g = zgcd(n_clone, d_clone);
  let g_clone = Rc::clone(&g);
  let tmp_1 = b::div(n, g_clone);
  let tmp_2 = b::div(d, g);
  let tmp_3 = b::to_positive(tmp_2);
  Rc::new(Q { Qnum: tmp_1, Qden: tmp_3 })
}

// Rocq: Stdlib.QArith.QArith_base.Qplus
// Variant: uncurried
pub fn Qplus(x: Rc<Q>, y: Rc<Q>) -> Rc<Q> {
  let x_clone = Rc::clone(&x);
  let tmp = Qnum_owned(x_clone);
  let y_clone = Rc::clone(&y);
  let tmp_1 = Qden(y_clone);
  let tmp_2 = b::identity(tmp_1);
  let tmp_3 = b::mul(tmp, tmp_2);
  let y_clone_1 = Rc::clone(&y);
  let tmp_4 = Qnum_owned(y_clone_1);
  let x_clone_1 = Rc::clone(&x);
  let tmp_5 = Qden(x_clone_1);
  let tmp_6 = b::identity(tmp_5);
  let tmp_7 = b::mul(tmp_4, tmp_6);
  let tmp_8 = b::add(tmp_3, tmp_7);
  let tmp_9 = Qden(x);
  let tmp_10 = Qden(y);
  let tmp_11 = b::mul(tmp_9, tmp_10);
  Rc::new(Q { Qnum: tmp_8, Qden: tmp_11 })
}

// Rocq: Stdlib.QArith.QArith_base.Qopp
pub fn Qopp(x: Rc<Q>) -> Rc<Q> {
  let x_clone = Rc::clone(&x);
  let tmp = Qnum_owned(x_clone);
  let tmp_1 = b::neg(tmp);
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
pub fn qsub(a_1: Rc<Q>, b_1: Rc<Q>) -> Rc<Q> {
  qred(Qminus(a_1, b_1))
}

// Rocq: Stdlib.QArith.QArith_base.Qmult
// Variant: uncurried
pub fn Qmult(x: Rc<Q>, y: Rc<Q>) -> Rc<Q> {
  let x_clone = Rc::clone(&x);
  let tmp = Qnum_owned(x_clone);
  let y_clone = Rc::clone(&y);
  let tmp_1 = Qnum_owned(y_clone);
  let tmp_2 = b::mul(tmp, tmp_1);
  let tmp_3 = Qden(x);
  let tmp_4 = Qden(y);
  let tmp_5 = b::mul(tmp_3, tmp_4);
  Rc::new(Q { Qnum: tmp_2, Qden: tmp_5 })
}

// Rocq: Roadtimes.roadtimes_implem.elim_obj
// Variant: uncurried
pub fn elim_obj(O: Array<Rc<Q>>, T: Array<Rc<Q>>, w: Int63, r: Int63, f: Rc<Q>) -> Array<Rc<Q>> {
  let tmp = int63!(0);
  let callback: Rc<dyn Fn(Int63, Array<Rc<Q>>) -> Array<Rc<Q>>> = Rc::new({
    let __anf_capture_19 = w;
    move |j: Int63, O: Array<Rc<Q>>| -> Array<Rc<Q>> {
      let r = &r;
      let w = &__anf_capture_19;
      let T = &T;
      let f = &f;
      let a_1 = T.get_cloned(Clone::clone(r) * Clone::clone(w) + j);
      if qzerob(&a_1) {
        std::mem::drop(a_1);
        O
      } else {
        let tmp_1 = O.get_cloned(j);
        let f_clone = Rc::clone(f);
        O.set(j, qsub(tmp_1, Qmult(f_clone, a_1)))
      }
    }
  });
  forl::<Array<Rc<Q>>>(tmp, w, callback, O)
}

// Rocq: Roadtimes.roadtimes_implem.canon_obj
// Variant: uncurried
pub fn canon_obj(T: Array<Rc<Q>>, B: Array<Int63>, c: Array<Rc<Q>>, w: Int63, m: Int63) -> Array<Rc<Q>> {
  let tmp = int63!(0);
  let c_clone = Clone::clone(&c);
  let callback: Rc<dyn Fn(Int63, Array<Rc<Q>>) -> Array<Rc<Q>>> = Rc::new({
    move |k: Int63, O: Array<Rc<Q>>| -> Array<Rc<Q>> {
      let B = &B;
      let c = &c_clone;
      let T = &T;
      let w = &w;
      let f = c.get_cloned(B.get_cloned(k));
      if qzerob(&f) {
        std::mem::drop(f);
        O
      } else {
        let T_clone = Clone::clone(T);
        let w_clone = Clone::clone(w);
        elim_obj(O, T_clone, w_clone, k, f)
      }
    }
  });
  let c_ref = &c;
  let tmp_1 = c_ref.copy();
  std::mem::drop(c);
  forl::<Array<Rc<Q>>>(tmp, m, callback, tmp_1)
}

// Rocq: Roadtimes.roadtimes_implem.st0
// Variant: uncurried
pub fn st0(T0: Array<Rc<Q>>, m: Int63, E0: Int63, A0: Int63) -> ((Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>) {
  let B0 = binit(m, E0);
  let tmp = cart(E0 + m + int63!(1), A0, E0 + m);
  let tmp_1 = E0 + m + int63!(1);
  let T0_clone = Clone::clone(&T0);
  let B0_clone = Clone::clone(&B0);
  ((T0, canon_obj(T0_clone, B0_clone, tmp, tmp_1, m)), B0)
}

// Rocq: Roadtimes.roadtimes_implem.qltb
// Variant: uncurried
pub fn qltb(a_1: Rc<Q>, b_1: Rc<Q>) -> bool {
  let a_clone = Rc::clone(&a_1);
  let tmp = Qnum_owned(a_clone);
  let b_clone = Rc::clone(&b_1);
  let tmp_1 = Qden(b_clone);
  let tmp_2 = b::identity(tmp_1);
  let tmp_3 = b::mul(tmp, tmp_2);
  let tmp_4 = Qnum_owned(b_1);
  let tmp_5 = Qden(a_1);
  let tmp_6 = b::identity(tmp_5);
  let tmp_7 = b::mul(tmp_4, tmp_6);
  b::lt(tmp_3, tmp_7)
}

// Rocq: Roadtimes.roadtimes_implem.enter
// Variant: uncurried
pub fn enter(N: Int63, al: Array<bool>, O: Array<Rc<Q>>) -> Rc<option<Int63>> {
  let callback: Rc<dyn Fn(Int63, Rc<option<Int63>>) -> bool> = Rc::new(move |_v5: Int63, st: Rc<option<Int63>>| -> bool {
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
  let callback_1: Rc<dyn Fn(Int63, Rc<option<Int63>>) -> Rc<option<Int63>>> = Rc::new({
    move |j: Int63, v38: Rc<option<Int63>>| -> Rc<option<Int63>> {
      let al = &al;
      let O = &O;
      let tmp = al.get_cloned(j);
      let tmp_1 = O.get_cloned(j);
      let tmp_2 = b::zero();
      let tmp_3 = b::one();
      let tmp_4 = qltb(tmp_1, Rc::new(Q { Qnum: tmp_2, Qden: tmp_3 }));
      if andb(tmp, tmp_4) {
        std::mem::drop(v38);
        Rc::new(option::<Int63>::Some(j))
      } else {
        std::mem::drop(v38);
        Rc::new(option::<Int63>::None)
      }
    }
  });
  loop_::<Rc<option<Int63>>>(N, callback, callback_1, int63!(0), Rc::new(option::<Int63>::None))
}

// Rocq: Roadtimes.roadtimes_implem.lc
// Variant: uncurried
pub fn lc(N: Int63, E0: Int63, p: Int63) -> Int63 {
  if p == int63!(0) {
    N
  } else {
    E0 + p - int63!(1)
  }
}

// Rocq: Roadtimes.roadtimes_implem.lexless
// Variant: borrowed, uncurried
pub fn lexless(T: &Array<Rc<Q>>, w: Int63, N: Int63, E0: Int63, m: Int63, k: Int63, r: Int63, s: Int63) -> bool {
  let m_1 = m;
  let s_1 = s;
  let tks = T.get_cloned(k * w + s_1);
  let trs = T.get_cloned(r * w + s_1);
  let tmp = m_1 + int63!(1);
  let callback: Rc<dyn Fn(Int63, Int63) -> bool> = Rc::new(move |_v57: Int63, st: Int63| -> bool {
    st == int63!(0)
  });
  let T_clone = Clone::clone(T);
  let callback_1: Rc<dyn Fn(Int63, Int63) -> Int63> = Rc::new({
    let __anf_capture_93 = k;
    let __anf_capture_97 = r;
    let __anf_capture_99 = w;
    move |p: Int63, _v106: Int63| -> Int63 {
      let N = &N;
      let E0 = &E0;
      let k = &__anf_capture_93;
      let trs = &trs;
      let r = &__anf_capture_97;
      let w = &__anf_capture_99;
      let T = &T_clone;
      let tks = &tks;
      let c = lc(Clone::clone(N), Clone::clone(E0), p);
      let a_1 = Qmult(T.get_cloned(Clone::clone(k) * Clone::clone(w) + c), Rc::clone(trs));
      let b_1 = Qmult(T.get_cloned(Clone::clone(r) * Clone::clone(w) + c), Rc::clone(tks));
      let a_clone = Rc::clone(&a_1);
      let b_clone = Rc::clone(&b_1);
      if qltb(a_clone, b_clone) {
        std::mem::drop(b_1);
        std::mem::drop(a_1);
        int63!(1)
      } else {
        if qltb(b_1, a_1) {
          int63!(2)
        } else {
          int63!(0)
        }
      }
    }
  });
  let st = loop_::<Int63>(tmp, callback, callback_1, int63!(0), int63!(0));
  st == int63!(1)
}

// Rocq: Roadtimes.roadtimes_implem.leave
// Variant: uncurried
pub fn leave(T: Array<Rc<Q>>, w: Int63, N: Int63, E0: Int63, m: Int63, s: Int63) -> Rc<option<Int63>> {
  let tmp = int63!(0);
  let callback: Rc<dyn Fn(Int63, Rc<option<Int63>>) -> Rc<option<Int63>>> = Rc::new({
    let __anf_capture_30 = m;
    move |k: Int63, best: Rc<option<Int63>>| -> Rc<option<Int63>> {
      let T = &T;
      let w = &w;
      let N = &N;
      let E0 = &E0;
      let m = &__anf_capture_30;
      let s = &s;
      let tmp_1 = b::zero();
      let tmp_2 = b::one();
      let tmp_3 = Rc::new(Q { Qnum: tmp_1, Qden: tmp_2 });
      let tmp_4 = T.get_cloned(k * Clone::clone(w) + Clone::clone(s));
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
              __rocq_reuse::rebuild(v68, option::<Int63>::Some(k))
            } else {
              __rocq_reuse::rebuild(v68, option::<Int63>::Some(v73))
            }
          },
          option::None => {
            __rocq_reuse::rebuild(v68, option::<Int63>::Some(k))
          },
        }
      } else {
        best
      }
    }
  });
  forl::<Rc<option<Int63>>>(tmp, m, callback, Rc::new(option::<Int63>::None))
}

// Rocq: Roadtimes.roadtimes_implem.qmul
// Variant: uncurried
pub fn qmul(a_1: Rc<Q>, b_1: Rc<Q>) -> Rc<Q> {
  qred(Qmult(a_1, b_1))
}

// Rocq: Roadtimes.roadtimes_implem.scale_row
// Variant: uncurried
pub fn scale_row(T: Array<Rc<Q>>, w: Int63, r: Int63, inv: Rc<Q>) -> Array<Rc<Q>> {
  let tmp = int63!(0);
  let callback: Rc<dyn Fn(Int63, Array<Rc<Q>>) -> Array<Rc<Q>>> = Rc::new({
    let __anf_capture_16 = w;
    move |j: Int63, T: Array<Rc<Q>>| -> Array<Rc<Q>> {
      let r = &r;
      let w = &__anf_capture_16;
      let inv = &inv;
      let tmp_1 = Clone::clone(r) * Clone::clone(w) + j;
      let tmp_2 = T.get_cloned(Clone::clone(r) * Clone::clone(w) + j);
      let inv_clone = Rc::clone(inv);
      T.set(tmp_1, qmul(tmp_2, inv_clone))
    }
  });
  forl::<Array<Rc<Q>>>(tmp, w, callback, T)
}

// Rocq: Stdlib.QArith.QArith_base.Qinv
pub fn Qinv(x: Rc<Q>) -> Rc<Q> {
  let x_clone = Rc::clone(&x);
  let tmp = Qnum_owned(x_clone);
  let tmp_1 = Rc::clone(&tmp);
  match b::integer_tag(tmp_1) {
    b::IntegerTag::Zero => {
      std::mem::drop(tmp);
      std::mem::drop(x);
      let tmp_2 = b::zero();
      let tmp_3 = b::one();
      Rc::new(Q { Qnum: tmp_2, Qden: tmp_3 })
    },
    b::IntegerTag::Positive => {
      let p = b::integer_magnitude(tmp);
      let tmp_4 = Qden(x);
      let tmp_5 = b::identity(tmp_4);
      Rc::new(Q { Qnum: tmp_5, Qden: p })
    },
    b::IntegerTag::Negative => {
      let p = b::integer_magnitude(tmp);
      let tmp_6 = Qden(x);
      let tmp_7 = b::neg(tmp_6);
      Rc::new(Q { Qnum: tmp_7, Qden: p })
    },
  }
}

// Rocq: Roadtimes.roadtimes_implem.elim_row
// Variant: uncurried
pub fn elim_row(T: Array<Rc<Q>>, w: Int63, r: Int63, k: Int63, f: Rc<Q>) -> Array<Rc<Q>> {
  let tmp = int63!(0);
  let callback: Rc<dyn Fn(Int63, Array<Rc<Q>>) -> Array<Rc<Q>>> = Rc::new({
    let __anf_capture_21 = w;
    move |j: Int63, T: Array<Rc<Q>>| -> Array<Rc<Q>> {
      let r = &r;
      let k = &k;
      let w = &__anf_capture_21;
      let f = &f;
      let a_1 = T.get_cloned(Clone::clone(r) * Clone::clone(w) + j);
      if qzerob(&a_1) {
        std::mem::drop(a_1);
        T
      } else {
        let tmp_1 = Clone::clone(k) * Clone::clone(w) + j;
        let tmp_2 = T.get_cloned(Clone::clone(k) * Clone::clone(w) + j);
        let f_clone = Rc::clone(f);
        T.set(tmp_1, qsub(tmp_2, Qmult(f_clone, a_1)))
      }
    }
  });
  forl::<Array<Rc<Q>>>(tmp, w, callback, T)
}

// Rocq: Roadtimes.roadtimes_implem.elim_all
// Variant: uncurried
pub fn elim_all(T: Array<Rc<Q>>, w: Int63, m: Int63, r: Int63, s: Int63) -> Array<Rc<Q>> {
  let tmp = int63!(0);
  let callback: Rc<dyn Fn(Int63, Array<Rc<Q>>) -> Array<Rc<Q>>> = Rc::new({
    move |k: Int63, T: Array<Rc<Q>>| -> Array<Rc<Q>> {
      let s = &s;
      let w = &w;
      let r = &r;
      let r_clone = Clone::clone(r);
      if k == r_clone {
        T
      } else {
        let f = T.get_cloned(k * Clone::clone(w) + Clone::clone(s));
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
  forl::<Array<Rc<Q>>>(tmp, m, callback, T)
}

// Rocq: Roadtimes.roadtimes_implem.pivot
// Variant: uncurried
pub fn pivot(w: Int63, m: Int63, st: ((Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>), r: Int63, s: Int63) -> ((Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>) {
  let st_clone = Clone::clone(&st);
  let T = sT(st_clone);
  let st_clone_1 = Clone::clone(&st);
  let O = sO(st_clone_1);
  let B = sB(st);
  let tmp = T.get_cloned(r * w + s);
  let T1 = scale_row(T, w, r, Qinv(tmp));
  let T2 = elim_all(T1, w, m, r, s);
  let tmp_1 = O.get_cloned(s);
  let T2_clone = Clone::clone(&T2);
  let O2 = elim_obj(O, T2_clone, w, r, tmp_1);
  ((T2, O2), B.set(r, s))
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
pub fn sloop_1(m: Int63, E0: Int63, al: Array<bool>, st: ((Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>)) -> ((Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>) {
  sloop(m, E0, al, st, ())
}

// Rocq: Roadtimes.roadtimes_implem.sloop (local: sloop)
// Variant: uncurried, lifted
pub fn sloop(m: Int63, E0: Int63, al: Array<bool>, st: ((Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>), _H: ()) -> ((Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>) {
  let tmp = E0 + m;
  let st_clone = Clone::clone(&st);
  let tmp_1 = sO(st_clone);
  let al_clone = Clone::clone(&al);
  let tmp_2 = odec::<Int63>(enter(tmp, al_clone, tmp_1));
  let (v29, v30) = __rocq_reuse::reset(tmp_2, |__payload| Clone::clone(__payload));
  std::mem::drop(v30);
  match v29 {
    sumor::inleft(v35) => {
      let (v37, v38) = __rocq_reuse::reset(v35, |__payload| Clone::clone(__payload));
      std::mem::drop(v38);
      match v37 {
        sig { x: v43 } => {
          let st_clone_1 = Clone::clone(&st);
          let tmp_3 = odec::<Int63>(leave(sT(st_clone_1), E0 + m + int63!(1), E0 + m, E0, m, v43));
          let (v88, v89) = __rocq_reuse::reset(tmp_3, |__payload| Clone::clone(__payload));
          std::mem::drop(v89);
          match v88 {
            sumor::inleft(v94) => {
              let s0 = &v94;
              match &**s0 {
                sig { x: r } => {
                  let tmp_4 = E0 + m + int63!(1);
                  let tmp_5 = st;
                  let r_clone = Clone::clone(r);
                  std::mem::drop(v94);
                  let tmp_6 = pivot(tmp_4, m, tmp_5, r_clone, v43);
                  sloop(m, E0, al, tmp_6, ())
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
pub fn phase1(T0: Array<Rc<Q>>, m: Int63, E0: Int63, A0: Int63) -> ((Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>) {
  let tmp = Array::<bool>::make(E0 + m, true);
  let tmp_1 = st0(T0, m, E0, A0);
  sloop_1(m, E0, tmp, tmp_1)
}

// Rocq: Roadtimes.roadtimes_implem.al2
// Variant: uncurried
pub fn al2(O1: Array<Rc<Q>>, A0: Int63, N: Int63) -> Array<bool> {
  let tmp = int63!(0);
  let callback: Rc<dyn Fn(Int63, Array<bool>) -> Array<bool>> = Rc::new({
    move |j: Int63, a_1: Array<bool>| -> Array<bool> {
      let A0 = &A0;
      let O1 = &O1;
      let tmp_1 = j < Clone::clone(A0);
      let tmp_2 = O1.get_cloned(j);
      a_1.set(j, andb(tmp_1, qzerob_owned(tmp_2)))
    }
  });
  let tmp_3 = Array::<bool>::make(N, false);
  forl::<Array<bool>>(tmp, N, callback, tmp_3)
}

// Rocq: Roadtimes.roadtimes_implem.iofz_rec
pub fn iofz_rec_1(z: Rc<BigInt>) -> Int63 {
  iofz_rec(z, ())
}

// Rocq: Roadtimes.roadtimes_implem.iofz_rec (local: iofz_rec)
// Variant: uncurried, lifted
pub fn iofz_rec(z: Rc<BigInt>, _H: ()) -> Int63 {
  let tmp = b::zero();
  let z_clone = Rc::clone(&z);
  let tmp_1 = b::lt(tmp, z_clone);
  match bdec(tmp_1) {
    sumbool::left => {
      let tmp_2 = b::one();
      let tmp_3 = b::twice(tmp_2);
      let tmp_4 = b::identity(tmp_3);
      let z_clone_1 = Rc::clone(&z);
      let tmp_5 = b::div(z_clone_1, tmp_4);
      let r = iofz_rec(tmp_5, ());
      let tmp_6 = b::one();
      let tmp_7 = b::twice(tmp_6);
      let tmp_8 = b::identity(tmp_7);
      let tmp_9 = b::modulo(z, tmp_8);
      let tmp_10 = b::zero();
      if b::equal(tmp_9, tmp_10) {
        r + r
      } else {
        r + r + int63!(1)
      }
    },
    sumbool::right => {
      std::mem::drop(z);
      int63!(0)
    },
  }
}

// Rocq: Roadtimes.roadtimes_implem.iofz
pub fn iofz(z: Rc<BigInt>) -> Int63 {
  iofz_rec_1(z)
}

// Rocq: Roadtimes.roadtimes_implem.q2f
pub fn q2f(q: Rc<Q>) -> f64 {
  let q_clone = Rc::clone(&q);
  let tmp = Qnum_owned(q_clone);
  let tmp_1 = b::one();
  let tmp_2 = b::twice(tmp_1);
  let tmp_3 = b::twice(tmp_2);
  let tmp_4 = b::twice(tmp_3);
  let tmp_5 = b::twice(tmp_4);
  let tmp_6 = b::twice(tmp_5);
  let tmp_7 = b::twice(tmp_6);
  let tmp_8 = b::twice(tmp_7);
  let tmp_9 = b::twice(tmp_8);
  let tmp_10 = b::twice(tmp_9);
  let tmp_11 = b::twice(tmp_10);
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
  let tmp_31 = b::twice(tmp_30);
  let tmp_32 = b::twice(tmp_31);
  let tmp_33 = b::twice(tmp_32);
  let tmp_34 = b::twice(tmp_33);
  let tmp_35 = b::twice(tmp_34);
  let tmp_36 = b::twice(tmp_35);
  let tmp_37 = b::twice(tmp_36);
  let tmp_38 = b::identity(tmp_37);
  let tmp_39 = b::mul(tmp, tmp_38);
  let tmp_40 = Qden(q);
  let tmp_41 = b::identity(tmp_40);
  let mz = b::div(tmp_39, tmp_41);
  rocq_float64::div(rocq_float64::of_uint63(iofz(mz)), rocq_float64::of_uint63(__rocq_global_2268))
}

// Rocq: Roadtimes.roadtimes_implem.dq
// Variant: borrowed, uncurried
pub fn dq(n: Int63, D: &Array<Int63>, s: Int63, d: Int63) -> Rc<Q> {
  let n_1 = n;
  let s_1 = s;
  let d_1 = d;
  let tmp = zofi(D.get_cloned(s_1 * n_1 + d_1));
  inject_Z(tmp)
}

// Rocq: Roadtimes.roadtimes_implem.mk2
// Variant: uncurried
pub fn mk2(st1: ((Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>), carr: Array<Rc<Q>>, w: Int63, m: Int63) -> ((Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>) {
  let st1_clone = Clone::clone(&st1);
  let tmp = sT(st1_clone);
  let tmp_1 = &tmp;
  let tmp_2 = tmp_1.copy();
  std::mem::drop(tmp);
  let st1_clone_1 = Clone::clone(&st1);
  let tmp_3 = sT(st1_clone_1);
  let st1_clone_2 = Clone::clone(&st1);
  let tmp_4 = (tmp_2, canon_obj(tmp_3, sB(st1_clone_2), carr, w, m));
  let tmp_5 = sB(st1);
  let tmp_6 = &tmp_5;
  let tmp_7 = tmp_6.copy();
  std::mem::drop(tmp_5);
  (tmp_4, tmp_7)
}

// Rocq: Roadtimes.roadtimes_implem.phase2
// Variant: uncurried
pub fn phase2(T0: Array<Rc<Q>>, m: Int63, E0: Int63, _A0: Int63, st1: ((Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>), al: Array<bool>, carr: Array<Rc<Q>>) -> Rc<Q> {
  let tmp = carr.length();
  let tmp_1 = tmp == E0 + m + int63!(1);
  let tmp_2 = carr.get_cloned(E0 + m);
  let tmp_3 = andb(tmp_1, qzerob_owned(tmp_2));
  match bdec(tmp_3) {
    sumbool::left => {
      std::mem::drop(T0);
      let tmp_4 = mk2(st1, carr, E0 + m + int63!(1), m);
      let st3 = sloop_1(m, E0, al, tmp_4);
      let tmp_5 = sO(st3);
      let tmp_6 = tmp_5.get_cloned(E0 + m);
      std::mem::drop(tmp_5);
      Qopp(tmp_6)
    },
    sumbool::right => {
      std::mem::drop(T0);
      std::mem::drop(st1);
      std::mem::drop(al);
      std::mem::drop(carr);
      let tmp_7 = b::zero();
      let tmp_8 = b::one();
      Rc::new(Q { Qnum: tmp_7, Qden: tmp_8 })
    },
  }
}

// Rocq: Roadtimes.roadtimes_implem.qcost
// Variant: uncurried
pub fn qcost(E: Int63, w: Int63, cnt: Array<Int63>, neg: bool) -> Array<Rc<Q>> {
  let tmp = int63!(0);
  let callback: Rc<dyn Fn(Int63, Array<Rc<Q>>) -> Array<Rc<Q>>> = Rc::new({
    move |e: Int63, c: Array<Rc<Q>>| -> Array<Rc<Q>> {
      let neg = &neg;
      let cnt = &cnt;
      let tmp_1 = if *neg {
        let tmp_2 = cnt.get_cloned(e);
        let tmp_3 = zofi(tmp_2);
        b::neg(tmp_3)
      } else {
        let tmp_4 = cnt.get_cloned(e);
        zofi(tmp_4)
      };
      c.set(e, inject_Z(tmp_1))
    }
  });
  let tmp_5 = b::zero();
  let tmp_6 = b::one();
  forl::<Array<Rc<Q>>>(tmp, E, callback, Array::<Rc<Q>>::make(w, Rc::new(Q { Qnum: tmp_5, Qden: tmp_6 })))
}

// Rocq: Roadtimes.roadtimes_implem.vq
// Variant: borrowed, uncurried
pub fn vq(n: Int63, E: Int63, RR: Int63, D: &Array<Int63>, X: &Array<Int63>, I: &Array<Int63>, T0: &Array<Rc<Q>>, st1: ((Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>), al: &Array<bool>, s: Int63, d: Int63, neg: bool) -> Rc<Q> {
  let n_1 = n;
  let E_1 = E;
  let RR_1 = RR;
  let st1_1 = st1;
  let s_1 = s;
  let d_1 = d;
  let neg_1 = neg;
  let tmp = E_1 + RR_1;
  let tmp_1 = E_1 + E_1;
  let tmp_2 = E_1 + RR_1;
  let tmp_3 = E_1 + tmp_2 + int63!(1);
  let tmp_4 = route_cnt(n_1, E_1, D, X, I, s_1, d_1);
  let tmp_5 = qcost(E_1, tmp_3, tmp_4, neg_1);
  phase2(Clone::clone(T0), tmp, E_1, tmp_1, st1_1, Clone::clone(al), tmp_5)
}

// Rocq: Roadtimes.roadtimes_implem.qans
// Variant: borrowed, uncurried
pub fn qans(n: Int63, E: Int63, RR: Int63, D: &Array<Int63>, X: &Array<Int63>, I: &Array<Int63>, T0: &Array<Rc<Q>>, st1: ((Array<Rc<Q>>, Array<Rc<Q>>), Array<Int63>), al: &Array<bool>, s: Int63, d: Int63) -> (f64, f64) {
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
pub fn aget(t: &Array<Int63>, i: Int63) -> Int63 {
  let i_1 = i;
  t.get_cloned(i_1)
}

// Rocq: Roadtimes.roadtimes_implem.answers
// Variant: uncurried
pub fn answers(n: Int63, E: Int63, RR: Int63, D: Array<Int63>, X: Array<Int63>, I: Array<Int63>, T0: Array<Rc<Q>>, xqs: Array<Int63>, xqd: Array<Int63>) -> Array<(f64, f64)> {
  let tmp = E + RR;
  let tmp_1 = E + E;
  let T0_clone = Clone::clone(&T0);
  let st1 = phase1(T0_clone, tmp, E, tmp_1);
  let st1_clone = Clone::clone(&st1);
  let tmp_2 = sO(st1_clone);
  let tmp_3 = E + E;
  let tmp_4 = E + RR;
  let al = al2(tmp_2, tmp_3, E + tmp_4);
  let tmp_5 = int63!(0);
  let tmp_6 = xqs.length();
  let xqs_clone = Clone::clone(&xqs);
  let callback: Rc<dyn Fn(Int63, Array<(f64, f64)>) -> Array<(f64, f64)>> = Rc::new({
    let __anf_capture_98 = E;
    let __anf_capture_100 = RR;
    let __anf_capture_108 = T0;
    let __anf_capture_110 = st1;
    move |j: Int63, out: Array<(f64, f64)>| -> Array<(f64, f64)> {
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
      out.set(j, tmp_9)
    }
  });
  let tmp_10 = xqs.length();
  std::mem::drop(xqs);
  forl::<Array<(f64, f64)>>(tmp_5, tmp_6, callback, Array::<(f64, f64)>::make(tmp_10, (__rocq_global_2601, __rocq_global_2601)))
}

// Rocq: Roadtimes.roadtimes_implem.roadtimes_impl
// Variant: uncurried
pub fn roadtimes_impl(xdist: Array<Array<Int63>>, xrs: Array<Int63>, xrd: Array<Int63>, xrt: Array<Int63>, xqs: Array<Int63>, xqd: Array<Int63>) -> Array<(f64, f64)> {
  let n = xdist.length();
  let W = flatten(n, xdist);
  let W_clone = Clone::clone(&W);
  let FW = fw(n, W_clone);
  let FW_clone = Clone::clone(&FW);
  let D = fst::<Array<Int63>, Array<Int63>>(FW_clone);
  let X = snd::<Array<Int63>, Array<Int63>>(FW);
  let W_clone_1 = Clone::clone(&W);
  let SR = scan_roads(n, W_clone_1);
  let SR_clone = Clone::clone(&SR);
  let I = fst::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), Int63>(SR_clone));
  let SR_clone_1 = Clone::clone(&SR);
  let P = snd::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), Int63>(SR_clone_1));
  let E = snd::<(Array<Int63>, Array<Int63>), Int63>(SR);
  let RR = xrs.length();
  let tmp = guard(E, RR);
  match bdec(tmp) {
    sumbool::left => {
      let D_clone = Clone::clone(&D);
      let X_clone = Clone::clone(&X);
      let I_clone = Clone::clone(&I);
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
      let tmp_1 = xqs.length();
      std::mem::drop(xqs);
      Array::<(f64, f64)>::make(tmp_1, (__rocq_global_2601, __rocq_global_2601))
    },
  }
}
const __rocq_global_461: Int63 = int63!(1073741824);
const __rocq_global_2268: Int63 = int63!(68719476736);
const __rocq_global_2601: f64 = f64::from_bits(0u64);