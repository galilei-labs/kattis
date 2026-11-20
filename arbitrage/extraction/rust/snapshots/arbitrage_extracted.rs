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

pub struct tabs {
  pub tPR: Array<bool>,
  pub tMA: Array<f64>,
  pub tEX: Array<Int63>,
  pub tCN: Array<Int63>,
  pub tVT: Array<Int63>,
}

impl Clone for tabs {
  fn clone(&self) -> Self {
    match self {
      tabs { tPR: __field0, tMA: __field1, tEX: __field2, tCN: __field3, tVT: __field4 } => tabs { tPR: Clone::clone(__field0), tMA: Clone::clone(__field1), tEX: Clone::clone(__field2), tCN: Clone::clone(__field3), tVT: Clone::clone(__field4) },
    }
  }
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::PositiveTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::NaturalTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::IntegerTag>; };

pub type uint = Int63;

// Rocq: Arbitrage.arbitrage_implem.BIAS
pub fn BIAS() -> Int63 {
  int63!(1073741824)
}

// Rocq: Arbitrage.arbitrage_implem.cap
pub fn cap() -> Int63 {
  int63!(1048576)
}

// Rocq: Arbitrage.arbitrage_implem.f_one
pub fn f_one(_v0: ()) -> f64 {
  rocq_float64::of_uint63(int63!(1))
}

// Rocq: Arbitrage.arbitrage_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Arbitrage.arbitrage_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: Int63, cont: Rc<dyn Fn(Int63, St) -> bool>, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Arbitrage.arbitrage_implem.wloop (local: wloop)
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

// Rocq: Arbitrage.arbitrage_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: Int63, cont: Rc<dyn Fn(Int63, St) -> bool>, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop_1::<St>(hi, cont, f, i, s)
}

// Rocq: Arbitrage.arbitrage_implem.f_two
pub fn f_two(_v0: ()) -> f64 {
  rocq_float64::of_uint63(int63!(2))
}

// Rocq: Arbitrage.arbitrage_implem.ratecell
// Variant: uncurried
pub fn ratecell(a_1: Int63, b_1: Int63) -> ((f64, Int63), Int63) {
  let ha = a_1.head0();
  let hb = b_1.head0();
  let num = if ha < hb {
    b_1 << hb - ha
  } else {
    b_1
  };
  let den = if ha < hb {
    a_1
  } else {
    a_1 << ha - hb
  };
  let r = rocq_float64::div(rocq_float64::of_uint63(num), rocq_float64::of_uint63(den));
  let e = __rocq_global_359 + ha - hb;
  let tmp = f_one(());
  if rocq_float64::ltb(r, tmp) {
    ((rocq_float64::mul(r, f_two(())), e - int63!(1)), int63!(2))
  } else {
    ((r, e), int63!(2))
  }
}

// Rocq: Arbitrage.arbitrage_implem.tPR
pub fn tPR(t: Rc<tabs>) -> Array<bool> {
  let t_tPR_clone = Clone::clone(&t.tPR);
  std::mem::drop(t);
  t_tPR_clone
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

// Rocq: Arbitrage.arbitrage_implem.f_c1
pub fn f_c1(_v0: ()) -> f64 {
  rocq_float64::of_uint63(int63!(1048577))
}

// Rocq: Arbitrage.arbitrage_implem.f_c0
pub fn f_c0(_v0: ()) -> f64 {
  rocq_float64::of_uint63(int63!(1048576))
}

// Rocq: Arbitrage.arbitrage_implem.fcmp
// Variant: uncurried
pub fn fcmp(m1: f64, e1: Int63, n1: Int63, m2: f64, e2: Int63, n2: Int63) -> Rc<option<bool>> {
  let tmp = __rocq_global_467 < n1;
  let tmp_1 = __rocq_global_467 < n2;
  if orb(tmp, tmp_1) {
    Rc::new(option::<bool>::None)
  } else {
    let tmp_2 = e2 + int63!(2);
    if tmp_2 <= e1 {
      Rc::new(option::<bool>::Some(true))
    } else {
      let tmp_3 = e1 + int63!(2);
      if tmp_3 <= e2 {
        Rc::new(option::<bool>::Some(false))
      } else {
        let x = if e2 < e1 {
          rocq_float64::mul(m1, f_two(()))
        } else {
          m1
        };
        let y = if e1 < e2 {
          rocq_float64::mul(m2, f_two(()))
        } else {
          m2
        };
        let tmp_4 = rocq_float64::mul(y, f_c1(()));
        let tmp_5 = rocq_float64::mul(x, f_c0(()));
        if rocq_float64::ltb(tmp_4, tmp_5) {
          Rc::new(option::<bool>::Some(true))
        } else {
          let tmp_6 = rocq_float64::mul(x, f_c1(()));
          let tmp_7 = rocq_float64::mul(y, f_c0(()));
          if rocq_float64::ltb(tmp_6, tmp_7) {
            Rc::new(option::<bool>::Some(false))
          } else {
            Rc::new(option::<bool>::None)
          }
        }
      }
    }
  }
}

// Rocq: Arbitrage.arbitrage_implem.tMA
pub fn tMA(t: Rc<tabs>) -> Array<f64> {
  let t_tMA_clone = Clone::clone(&t.tMA);
  std::mem::drop(t);
  t_tMA_clone
}

// Rocq: Arbitrage.arbitrage_implem.tEX
pub fn tEX(t: Rc<tabs>) -> Array<Int63> {
  let t_tEX_clone = Clone::clone(&t.tEX);
  std::mem::drop(t);
  t_tEX_clone
}

// Rocq: Arbitrage.arbitrage_implem.tCN
pub fn tCN(t: Rc<tabs>) -> Array<Int63> {
  let t_tCN_clone = Clone::clone(&t.tCN);
  std::mem::drop(t);
  t_tCN_clone
}

// Rocq: Arbitrage.arbitrage_implem.zofi_rec
pub fn zofi_rec_1(i: Int63) -> Rc<BigInt> {
  zofi_rec(i, ())
}

// Rocq: Arbitrage.arbitrage_implem.zofi_rec (local: zofi_rec)
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

// Rocq: Arbitrage.arbitrage_implem.zofi
pub fn zofi(i: Int63) -> Rc<BigInt> {
  zofi_rec_1(i)
}

// Rocq: Arbitrage.arbitrage_implem.primes
pub fn primes(_v0: ()) -> Array<Int63> {
  Array::<Int63>::make(int63!(25), int63!(0)).set(int63!(0), int63!(2)).set(int63!(1), int63!(3)).set(int63!(2), int63!(5)).set(int63!(3), int63!(7)).set(int63!(4), int63!(11)).set(int63!(5), int63!(13)).set(int63!(6), int63!(17)).set(int63!(7), int63!(19)).set(int63!(8), int63!(23)).set(int63!(9), int63!(29)).set(int63!(10), int63!(31)).set(int63!(11), int63!(37)).set(int63!(12), int63!(41)).set(int63!(13), int63!(43)).set(int63!(14), int63!(47)).set(int63!(15), int63!(53)).set(int63!(16), int63!(59)).set(int63!(17), int63!(61)).set(int63!(18), int63!(67)).set(int63!(19), int63!(71)).set(int63!(20), int63!(73)).set(int63!(21), int63!(79)).set(int63!(22), int63!(83)).set(int63!(23), int63!(89)).set(int63!(24), int63!(97))
}

// Rocq: Arbitrage.arbitrage_implem.ex_step
// Variant: borrowed, uncurried
pub fn ex_step(dv: &Rc<dyn Fn(Int63) -> Int63>, t: Int63, s: ((bool, Rc<BigInt>), Rc<BigInt>)) -> ((bool, Rc<BigInt>), Rc<BigInt>) {
  let t_1 = t;
  let s_1 = s;
  match &s_1 {
    (Q, p) => {
      match Q {
        (_P, nz) => {
          let d = dv(t_1);
          if int63!(0).ltsb(d) {
            let tmp = primes(());
            let tmp_1 = tmp.get_cloned(t_1);
            std::mem::drop(tmp);
            let tmp_2 = zofi(tmp_1);
            let tmp_3 = zofi(d);
            let tmp_4 = b::pow(tmp_2, tmp_3);
            let nz_clone = Rc::clone(nz);
            let tmp_5 = b::mul(nz_clone, tmp_4);
            let tmp_6 = (true, tmp_5);
            let p_clone = Rc::clone(p);
            std::mem::drop(s_1);
            (tmp_6, p_clone)
          } else {
            if d.ltsb(int63!(0)) {
              let nz_clone_1 = Rc::clone(nz);
              let tmp_7 = (true, nz_clone_1);
              let tmp_8 = primes(());
              let tmp_9 = tmp_8.get_cloned(t_1);
              std::mem::drop(tmp_8);
              let tmp_10 = zofi(tmp_9);
              let tmp_11 = zofi(int63!(0) - d);
              let tmp_12 = b::pow(tmp_10, tmp_11);
              let p_clone_1 = Rc::clone(p);
              std::mem::drop(s_1);
              let tmp_13 = b::mul(p_clone_1, tmp_12);
              (tmp_7, tmp_13)
            } else {
              s_1
            }
          }
        },
      }
    },
  }
}

// Rocq: Arbitrage.arbitrage_implem.exact_gt
pub fn exact_gt(dv: Rc<dyn Fn(Int63) -> Int63>) -> bool {
  let tmp = int63!(25);
  let callback: Rc<dyn Fn(Int63, ((bool, Rc<BigInt>), Rc<BigInt>)) -> bool> = Rc::new(move |_v5: Int63, v6: ((bool, Rc<BigInt>), Rc<BigInt>)| -> bool {
    std::mem::drop(v6);
    true
  });
  let dv_clone: Rc<dyn Fn(Int63) -> Int63> = Rc::clone(&dv);
  let callback_1: Rc<dyn Fn(Int63, ((bool, Rc<BigInt>), Rc<BigInt>)) -> ((bool, Rc<BigInt>), Rc<BigInt>)> = Rc::new({
    move |v19: Int63, v20: ((bool, Rc<BigInt>), Rc<BigInt>)| -> ((bool, Rc<BigInt>), Rc<BigInt>) {
      let dv = &dv_clone;
      let tmp_1 = ex_step(dv, v19, v20);
      tmp_1
    }
  });
  let tmp_2 = b::one();
  let tmp_3 = b::identity(tmp_2);
  let tmp_4 = (false, tmp_3);
  let tmp_5 = b::one();
  let tmp_6 = b::identity(tmp_5);
  let tmp_7 = loop_::<((bool, Rc<BigInt>), Rc<BigInt>)>(tmp, callback, callback_1, int63!(0), (tmp_4, tmp_6));
  match tmp_7 {
    (v68, v70) => {
      match v68 {
        (v73, v75) => {
          if v73 {
            std::mem::drop(dv);
            b::lt(v70, v75)
          } else {
            std::mem::drop(dv);
            std::mem::drop(v75);
            std::mem::drop(v70);
            false
          }
        },
      }
    },
  }
}

// Rocq: Arbitrage.arbitrage_implem.dvd1
// Variant: uncurried
pub fn dvd1(n: Int63, x: Int63) -> Int63 {
  let tmp = n % x;
  if tmp == int63!(0) {
    int63!(1)
  } else {
    int63!(0)
  }
}

// Rocq: Arbitrage.arbitrage_implem.mlt
// Variant: uncurried
pub fn mlt(n: Int63, p: Int63) -> Int63 {
  let p2 = p * p;
  let p3 = p2 * p;
  let p4 = p3 * p;
  let p5 = p4 * p;
  let p6 = p5 * p;
  dvd1(n, p) + dvd1(n, p2) + dvd1(n, p3) + dvd1(n, p4) + dvd1(n, p5) + dvd1(n, p6)
}

// Rocq: Arbitrage.arbitrage_implem.tVT
pub fn tVT_owned(t: Rc<tabs>) -> Array<Int63> {
  let t_tVT_clone = Clone::clone(&t.tVT);
  std::mem::drop(t);
  t_tVT_clone
}

// Rocq: Arbitrage.arbitrage_implem.tVT
// Variant: borrowed
pub fn tVT(t: &Rc<tabs>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tVT)
}

// Rocq: Arbitrage.arbitrage_implem.wr_head
// Variant: uncurried
pub fn wr_head(T: Rc<tabs>, q: Int63, m: f64, e: Int63, n: Int63, V: Array<Int63>) -> Rc<tabs> {
  let T_clone = Rc::clone(&T);
  let tmp = tPR(T_clone).set(q, true);
  let T_clone_1 = Rc::clone(&T);
  let tmp_1 = tMA(T_clone_1).set(q, m);
  let T_clone_2 = Rc::clone(&T);
  Rc::new(tabs { tPR: tmp, tMA: tmp_1, tEX: tEX(T_clone_2).set(q, e), tCN: tCN(T).set(q, n), tVT: V })
}

// Rocq: Arbitrage.arbitrage_implem.vset
// Variant: uncurried
pub fn vset(bd: Int63, a_1: Int63, b_1: Int63, V: Array<Int63>) -> Array<Int63> {
  let tmp = int63!(25);
  let callback: Rc<dyn Fn(Int63, Array<Int63>) -> bool> = Rc::new(move |_v8: Int63, v9: Array<Int63>| -> bool {
    std::mem::drop(v9);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
    move |t: Int63, W: Array<Int63>| -> Array<Int63> {
      let bd = &bd;
      let b_1 = &b_1;
      let a_1 = &a_1;
      let tmp_1 = Clone::clone(bd) + t;
      let tmp_2 = primes(());
      let tmp_3 = tmp_2.get_cloned(t);
      std::mem::drop(tmp_2);
      let tmp_4 = mlt(Clone::clone(b_1), tmp_3);
      let tmp_5 = primes(());
      let tmp_6 = tmp_5.get_cloned(t);
      std::mem::drop(tmp_5);
      let a_clone = Clone::clone(a_1);
      W.set(tmp_1, tmp_4 - mlt(a_clone, tmp_6))
    }
  });
  loop_::<Array<Int63>>(tmp, callback, callback_1, int63!(0), V)
}

// Rocq: Arbitrage.arbitrage_implem.init_step
// Variant: uncurried
pub fn init_step(c: Int63, xs: Array<Int63>, xd: Array<Int63>, xa: Array<Int63>, xb: Array<Int63>, r: Int63, T: Rc<tabs>) -> Rc<tabs> {
  let u = xs.get_cloned(r);
  let v = xd.get_cloned(r);
  let a_1 = xa.get_cloned(r);
  let b_1 = xb.get_cloned(r);
  let q = u * c + v;
  let tmp = ratecell(a_1, b_1);
  match tmp {
    (v42, v44) => {
      let p = &v44;
      match v42 {
        (v48, v50) => {
          let e = &v48;
          let m = &v50;
          let T_clone = Rc::clone(&T);
          let tmp_1 = tPR(T_clone);
          let tmp_2 = tmp_1.get_cloned(q);
          let better = if tmp_2 {
            let T_clone_1 = Rc::clone(&T);
            let tmp_3 = tMA(T_clone_1);
            let tmp_4 = tmp_3.get_cloned(q);
            let T_clone_2 = Rc::clone(&T);
            let tmp_5 = tEX(T_clone_2);
            let tmp_6 = tmp_5.get_cloned(q);
            let T_clone_3 = Rc::clone(&T);
            let tmp_7 = tCN(T_clone_3);
            let tmp_8 = tmp_7.get_cloned(q);
            let tmp_9 = fcmp(v48, v50, v44, tmp_4, tmp_6, tmp_8);
            let (v105, v106) = __rocq_reuse::reset(tmp_9, |__payload| Clone::clone(__payload));
            std::mem::drop(v106);
            match v105 {
              option::Some(v111) => {
                std::mem::drop(tmp_7);
                std::mem::drop(tmp_5);
                std::mem::drop(tmp_3);
                v111
              },
              option::None => {
                std::mem::drop(tmp_7);
                std::mem::drop(tmp_5);
                std::mem::drop(tmp_3);
                let T_clone_4 = Rc::clone(&T);
                let callback: Rc<dyn Fn(Int63) -> Int63> = Rc::new({
                  let __anf_capture_126 = b_1;
                  let __anf_capture_128 = a_1;
                  let __anf_capture_132 = q;
                  move |t: Int63| -> Int63 {
                    let b_1 = &__anf_capture_126;
                    let a_1 = &__anf_capture_128;
                    let T = &T_clone_4;
                    let q = &__anf_capture_132;
                    let tmp_10 = primes(());
                    let tmp_11 = tmp_10.get_cloned(t);
                    std::mem::drop(tmp_10);
                    let tmp_12 = mlt(Clone::clone(b_1), tmp_11);
                    let tmp_13 = primes(());
                    let tmp_14 = tmp_13.get_cloned(t);
                    std::mem::drop(tmp_13);
                    let tmp_15 = tmp_12 - mlt(Clone::clone(a_1), tmp_14);
                    let tmp_16 = tVT(T);
                    let q_clone = Clone::clone(q);
                    let tmp_17 = tmp_16.get_cloned(int63!(25) * q_clone + t);
                    std::mem::drop(tmp_16);
                    tmp_15 - tmp_17
                  }
                });
                exact_gt(callback)
              },
            }
          } else {
            true
          };
          if better {
            std::mem::drop(xs);
            std::mem::drop(xd);
            std::mem::drop(xa);
            std::mem::drop(tmp_1);
            std::mem::drop(xb);
            let tmp_18 = int63!(25) * q;
            let T_clone_5 = Rc::clone(&T);
            let tmp_19 = vset(tmp_18, a_1, b_1, tVT_owned(T_clone_5));
            let e_clone = Clone::clone(e);
            let m_clone = Clone::clone(m);
            let p_clone = Clone::clone(p);
            wr_head(T, q, e_clone, m_clone, p_clone, tmp_19)
          } else {
            std::mem::drop(xs);
            std::mem::drop(xd);
            std::mem::drop(xa);
            std::mem::drop(tmp_1);
            std::mem::drop(xb);
            T
          }
        },
      }
    },
  }
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b_1: bool) -> bool {
  if b_1 {
    false
  } else {
    true
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Arbitrage.arbitrage_implem.mulcell
// Variant: uncurried
pub fn mulcell(m1: f64, e1: Int63, n1: Int63, m2: f64, e2: Int63, n2: Int63) -> ((f64, Int63), Int63) {
  let p = rocq_float64::mul(m1, m2);
  let n = n1 + n2 + int63!(2);
  let tmp = __rocq_global_467;
  let n_ = if tmp < n {
    __rocq_global_467 + int63!(1)
  } else {
    n
  };
  let tmp_1 = f_two(());
  if rocq_float64::leb(tmp_1, p) {
    ((rocq_float64::div(p, f_two(())), e1 + e2 - __rocq_global_359 + int63!(1)), n_)
  } else {
    ((p, e1 + e2 - __rocq_global_359), n_)
  }
}

// Rocq: Arbitrage.arbitrage_implem.vadd
// Variant: uncurried
pub fn vadd(bd: Int63, b1: Int63, b2: Int63, V: Array<Int63>) -> Array<Int63> {
  let tmp = int63!(25);
  let callback: Rc<dyn Fn(Int63, Array<Int63>) -> bool> = Rc::new(move |_v8: Int63, v9: Array<Int63>| -> bool {
    std::mem::drop(v9);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
    move |t: Int63, W: Array<Int63>| -> Array<Int63> {
      let bd = &bd;
      let b1 = &b1;
      let b2 = &b2;
      let tmp_1 = Clone::clone(bd) + t;
      let tmp_2 = W.get_cloned(Clone::clone(b1) + t);
      let b2_clone = Clone::clone(b2);
      let tmp_3 = W.get_cloned(b2_clone + t);
      W.set(tmp_1, tmp_2 + tmp_3)
    }
  });
  loop_::<Array<Int63>>(tmp, callback, callback_1, int63!(0), V)
}

// Rocq: Arbitrage.arbitrage_implem.fw_j
// Variant: uncurried
pub fn fw_j(c: Int63, k: Int63, i: Int63, j: Int63, s: (Rc<tabs>, bool)) -> (Rc<tabs>, bool) {
  let s_clone = Clone::clone(&s);
  let T = fst::<Rc<tabs>, bool>(s_clone);
  if j == k {
    std::mem::drop(T);
    s
  } else {
    let qkj = k * c + j;
    let T_clone = Rc::clone(&T);
    let tmp = tPR(T_clone);
    let tmp_1 = tmp.get_cloned(qkj);
    if tmp_1 {
      let qik = i * c + k;
      let qij = i * c + j;
      let T_clone_1 = Rc::clone(&T);
      let tmp_2 = tMA(T_clone_1);
      let tmp_3 = tmp_2.get_cloned(qik);
      let T_clone_2 = Rc::clone(&T);
      let tmp_4 = tEX(T_clone_2);
      let tmp_5 = tmp_4.get_cloned(qik);
      let T_clone_3 = Rc::clone(&T);
      let tmp_6 = tCN(T_clone_3);
      let tmp_7 = tmp_6.get_cloned(qik);
      let T_clone_4 = Rc::clone(&T);
      let tmp_8 = tMA(T_clone_4);
      let tmp_9 = tmp_8.get_cloned(qkj);
      let T_clone_5 = Rc::clone(&T);
      let tmp_10 = tEX(T_clone_5);
      let tmp_11 = tmp_10.get_cloned(qkj);
      let T_clone_6 = Rc::clone(&T);
      let tmp_12 = tCN(T_clone_6);
      let tmp_13 = tmp_12.get_cloned(qkj);
      let tmp_14 = mulcell(tmp_3, tmp_5, tmp_7, tmp_9, tmp_11, tmp_13);
      match tmp_14 {
        (v134, v136) => {
          let p = &v136;
          match v134 {
            (v140, v142) => {
              let e = &v140;
              let m = &v142;
              let bik = int63!(25) * qik;
              let bkj = int63!(25) * qkj;
              let bij = int63!(25) * qij;
              let ex = if i == j {
                let tmp_15 = fcmp(v140, v142, v136, f_one(()), __rocq_global_359, int63!(0));
                let (v200, v201) = __rocq_reuse::reset(tmp_15, |__payload| Clone::clone(__payload));
                std::mem::drop(v201);
                match v200 {
                  option::Some(v206) => {
                    v206
                  },
                  option::None => {
                    let T_clone_7 = Rc::clone(&T);
                    let callback: Rc<dyn Fn(Int63) -> Int63> = Rc::new({
                      let __anf_capture_219 = bik;
                      let __anf_capture_223 = bkj;
                      move |t: Int63| -> Int63 {
                        let bik = &__anf_capture_219;
                        let T = &T_clone_7;
                        let bkj = &__anf_capture_223;
                        let tmp_16 = tVT(T);
                        let tmp_17 = tmp_16.get_cloned(Clone::clone(bik) + t);
                        std::mem::drop(tmp_16);
                        let tmp_18 = tVT(T);
                        let bkj_clone = Clone::clone(bkj);
                        let tmp_19 = tmp_18.get_cloned(bkj_clone + t);
                        std::mem::drop(tmp_18);
                        tmp_17 + tmp_19
                      }
                    });
                    exact_gt(callback)
                  },
                }
              } else {
                false
              };
              if ex {
                std::mem::drop(tmp_12);
                std::mem::drop(tmp_10);
                std::mem::drop(tmp_8);
                std::mem::drop(tmp_4);
                std::mem::drop(tmp_2);
                std::mem::drop(s);
                std::mem::drop(tmp_6);
                std::mem::drop(tmp);
                (T, true)
              } else {
                let T_clone_8 = Rc::clone(&T);
                let tmp_20 = tPR(T_clone_8);
                let tmp_21 = tmp_20.get_cloned(qij);
                let better = if tmp_21 {
                  let T_clone_9 = Rc::clone(&T);
                  let tmp_22 = tMA(T_clone_9);
                  let tmp_23 = tmp_22.get_cloned(qij);
                  let T_clone_10 = Rc::clone(&T);
                  let tmp_24 = tEX(T_clone_10);
                  let tmp_25 = tmp_24.get_cloned(qij);
                  let T_clone_11 = Rc::clone(&T);
                  let tmp_26 = tCN(T_clone_11);
                  let tmp_27 = tmp_26.get_cloned(qij);
                  let tmp_28 = fcmp(Clone::clone(e), Clone::clone(m), Clone::clone(p), tmp_23, tmp_25, tmp_27);
                  let (v337, v338) = __rocq_reuse::reset(tmp_28, |__payload| Clone::clone(__payload));
                  std::mem::drop(v338);
                  match v337 {
                    option::Some(v343) => {
                      std::mem::drop(tmp_26);
                      std::mem::drop(tmp_24);
                      std::mem::drop(tmp_22);
                      v343
                    },
                    option::None => {
                      std::mem::drop(tmp_26);
                      std::mem::drop(tmp_24);
                      std::mem::drop(tmp_22);
                      let T_clone_12 = Rc::clone(&T);
                      let callback_1: Rc<dyn Fn(Int63) -> Int63> = Rc::new({
                        let __anf_capture_358 = bik;
                        let __anf_capture_360 = bkj;
                        let __anf_capture_364 = bij;
                        move |t: Int63| -> Int63 {
                          let bik = &__anf_capture_358;
                          let bkj = &__anf_capture_360;
                          let T = &T_clone_12;
                          let bij = &__anf_capture_364;
                          let tmp_29 = tVT(T);
                          let tmp_30 = tmp_29.get_cloned(Clone::clone(bik) + t);
                          std::mem::drop(tmp_29);
                          let tmp_31 = tVT(T);
                          let tmp_32 = tmp_31.get_cloned(Clone::clone(bkj) + t);
                          std::mem::drop(tmp_31);
                          let tmp_33 = tmp_30 + tmp_32;
                          let tmp_34 = tVT(T);
                          let bij_clone = Clone::clone(bij);
                          let tmp_35 = tmp_34.get_cloned(bij_clone + t);
                          std::mem::drop(tmp_34);
                          tmp_33 - tmp_35
                        }
                      });
                      exact_gt(callback_1)
                    },
                  }
                } else {
                  true
                };
                if better {
                  std::mem::drop(tmp_20);
                  std::mem::drop(tmp_12);
                  std::mem::drop(tmp_10);
                  std::mem::drop(tmp_8);
                  std::mem::drop(tmp_4);
                  std::mem::drop(tmp_2);
                  std::mem::drop(s);
                  std::mem::drop(tmp_6);
                  std::mem::drop(tmp);
                  let T_clone_13 = Rc::clone(&T);
                  let tmp_36 = vadd(bij, bik, bkj, tVT_owned(T_clone_13));
                  let e_clone = Clone::clone(e);
                  let m_clone = Clone::clone(m);
                  let p_clone = Clone::clone(p);
                  (wr_head(T, qij, e_clone, m_clone, p_clone, tmp_36), false)
                } else {
                  std::mem::drop(tmp_20);
                  std::mem::drop(tmp_12);
                  std::mem::drop(tmp_10);
                  std::mem::drop(tmp_8);
                  std::mem::drop(tmp_4);
                  std::mem::drop(tmp_2);
                  std::mem::drop(tmp_6);
                  std::mem::drop(T);
                  std::mem::drop(tmp);
                  s
                }
              }
            },
          }
        },
      }
    } else {
      std::mem::drop(T);
      std::mem::drop(tmp);
      s
    }
  }
}

// Rocq: Arbitrage.arbitrage_implem.fw_i
// Variant: uncurried
pub fn fw_i(c: Int63, k: Int63, i: Int63, s: (Rc<tabs>, bool)) -> (Rc<tabs>, bool) {
  if i == k {
    s
  } else {
    let s_clone = Clone::clone(&s);
    let tmp = tPR(fst::<Rc<tabs>, bool>(s_clone));
    let tmp_1 = tmp.get_cloned(i * c + k);
    if tmp_1 {
      std::mem::drop(tmp);
      let callback: Rc<dyn Fn(Int63, (Rc<tabs>, bool)) -> bool> = Rc::new(move |_v41: Int63, s: (Rc<tabs>, bool)| -> bool {
        negb(snd::<Rc<tabs>, bool>(s))
      });
      let callback_1: Rc<dyn Fn(Int63, (Rc<tabs>, bool)) -> (Rc<tabs>, bool)> = Rc::new({
        let __anf_capture_62 = c;
        let __anf_capture_64 = k;
        let __anf_capture_66 = i;
        move |v68: Int63, v69: (Rc<tabs>, bool)| -> (Rc<tabs>, bool) {
          let tmp_2 = Clone::clone(&__anf_capture_62);
          let tmp_3 = Clone::clone(&__anf_capture_64);
          let tmp_4 = Clone::clone(&__anf_capture_66);
          fw_j(tmp_2, tmp_3, tmp_4, v68, v69)
        }
      });
      loop_::<(Rc<tabs>, bool)>(c, callback, callback_1, int63!(0), s)
    } else {
      std::mem::drop(tmp);
      s
    }
  }
}

// Rocq: Arbitrage.arbitrage_implem.fw_k
// Variant: uncurried
pub fn fw_k(c: Int63, k: Int63, s: (Rc<tabs>, bool)) -> (Rc<tabs>, bool) {
  let callback: Rc<dyn Fn(Int63, (Rc<tabs>, bool)) -> bool> = Rc::new(move |_v5: Int63, s: (Rc<tabs>, bool)| -> bool {
    negb(snd::<Rc<tabs>, bool>(s))
  });
  let callback_1: Rc<dyn Fn(Int63, (Rc<tabs>, bool)) -> (Rc<tabs>, bool)> = Rc::new({
    let __anf_capture_24 = c;
    move |v28: Int63, v29: (Rc<tabs>, bool)| -> (Rc<tabs>, bool) {
      let tmp = Clone::clone(&__anf_capture_24);
      let k_clone = Clone::clone(&k);
      fw_i(tmp, k_clone, v28, v29)
    }
  });
  loop_::<(Rc<tabs>, bool)>(c, callback, callback_1, int63!(0), s)
}

// Rocq: Arbitrage.arbitrage_implem.arbitrage_impl
// Variant: uncurried
pub fn arbitrage_impl(c: Int63, xs: Array<Int63>, xd: Array<Int63>, xa: Array<Int63>, xb: Array<Int63>) -> bool {
  let cc = c * c;
  let T0 = Rc::new(tabs { tPR: Array::<bool>::make(cc, false), tMA: Array::<f64>::make(cc, f_one(())), tEX: Array::<Int63>::make(cc, int63!(0)), tCN: Array::<Int63>::make(cc, int63!(0)), tVT: Array::<Int63>::make(int63!(25) * cc, int63!(0)) });
  let tmp = xs.length();
  let callback: Rc<dyn Fn(Int63, Rc<tabs>) -> bool> = Rc::new(move |_v75: Int63, v76: Rc<tabs>| -> bool {
    std::mem::drop(v76);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Rc<tabs>) -> Rc<tabs>> = Rc::new({
    let __anf_capture_94 = c;
    let __anf_capture_96 = xs;
    move |v104: Int63, v105: Rc<tabs>| -> Rc<tabs> {
      let tmp_1 = Clone::clone(&__anf_capture_94);
      let tmp_2 = Clone::clone(&__anf_capture_96);
      let xd_clone = Clone::clone(&xd);
      let xa_clone = Clone::clone(&xa);
      let xb_clone = Clone::clone(&xb);
      init_step(tmp_1, tmp_2, xd_clone, xa_clone, xb_clone, v104, v105)
    }
  });
  let T1 = loop_::<Rc<tabs>>(tmp, callback, callback_1, int63!(0), T0);
  let callback_2: Rc<dyn Fn(Int63, (Rc<tabs>, bool)) -> bool> = Rc::new(move |_v142: Int63, s: (Rc<tabs>, bool)| -> bool {
    negb(snd::<Rc<tabs>, bool>(s))
  });
  let callback_3: Rc<dyn Fn(Int63, (Rc<tabs>, bool)) -> (Rc<tabs>, bool)> = Rc::new({
    let __anf_capture_159 = c;
    move |v161: Int63, v162: (Rc<tabs>, bool)| -> (Rc<tabs>, bool) {
      let tmp_3 = Clone::clone(&__anf_capture_159);
      fw_k(tmp_3, v161, v162)
    }
  });
  snd::<Rc<tabs>, bool>(loop_::<(Rc<tabs>, bool)>(c, callback_2, callback_3, int63!(0), (T1, false)))
}
const __rocq_global_359: Int63 = int63!(1073741824);
const __rocq_global_467: Int63 = int63!(1048576);