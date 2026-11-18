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

pub struct tabs {
  pub tPR: Rc<Array<bool>>,
  pub tMA: Rc<Array<f64>>,
  pub tEX: Rc<Array<u64>>,
  pub tCN: Rc<Array<u64>>,
  pub tVT: Rc<Array<u64>>,
}

impl Clone for tabs {
  fn clone(&self) -> Self {
    match self {
      tabs { tPR: __field0, tMA: __field1, tEX: __field2, tCN: __field3, tVT: __field4 } => tabs { tPR: Clone::clone(__field0), tMA: Clone::clone(__field1), tEX: Clone::clone(__field2), tCN: Clone::clone(__field3), tVT: Clone::clone(__field4) },
    }
  }
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::PositiveTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::NaturalTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::IntegerTag>; };

pub type uint = u64;

// Rocq: Arbitrage.arbitrage_implem.BIAS
pub fn BIAS() -> u64 {
  1073741824u64
}

// Rocq: Arbitrage.arbitrage_implem.cap
pub fn cap() -> u64 {
  1048576u64
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Corelib.Floats.PrimFloat.of_uint63
pub fn of_uint63(v0: u64) -> f64 {
  rocq_float64::of_uint63(v0)
}

// Rocq: Arbitrage.arbitrage_implem.f_one
pub fn f_one(_v0: ()) -> f64 {
  of_uint63(1u64)
}

// Rocq: Corelib.BinNums.IntDef.Z.add
// Variant: uncurried
pub fn add(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::add(v0, v1)
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

// Rocq: Arbitrage.arbitrage_implem.bdec
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

// Rocq: Arbitrage.arbitrage_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Arbitrage.arbitrage_implem.wloop (local: wloop)
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

// Rocq: Arbitrage.arbitrage_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop_1::<St>(hi, cont, f, i, s)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.head0
pub fn head0(v0: u64) -> u64 {
  rocq_int63::head0(v0)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsl
// Variant: uncurried
pub fn lsl(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsl(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Floats.PrimFloat.div
// Variant: uncurried
pub fn div(v0: f64, v1: f64) -> f64 {
  rocq_float64::div(v0, v1)
}

// Rocq: Corelib.Floats.PrimFloat.ltb
// Variant: uncurried
pub fn ltb_1(v0: f64, v1: f64) -> bool {
  rocq_float64::ltb(v0, v1)
}

// Rocq: Corelib.Floats.PrimFloat.mul
// Variant: uncurried
pub fn mul_1(v0: f64, v1: f64) -> f64 {
  rocq_float64::mul(v0, v1)
}

// Rocq: Arbitrage.arbitrage_implem.f_two
pub fn f_two(_v0: ()) -> f64 {
  of_uint63(2u64)
}

// Rocq: Arbitrage.arbitrage_implem.ratecell
// Variant: uncurried
pub fn ratecell(a: u64, b: u64) -> ((f64, u64), u64) {
  let ha = head0(a);
  let hb = head0(b);
  let num = if ltb(ha, hb) {
    lsl(b, sub(hb, ha))
  } else {
    b
  };
  let den = if ltb(ha, hb) {
    a
  } else {
    lsl(a, sub(ha, hb))
  };
  let r = div(of_uint63(num), of_uint63(den));
  let e = sub(add_1(__rocq_global_359, ha), hb);
  let tmp = f_one(());
  if ltb_1(r, tmp) {
    ((mul_1(r, f_two(())), sub(e, 1u64)), 2u64)
  } else {
    ((r, e), 2u64)
  }
}

// Rocq: Arbitrage.arbitrage_implem.tPR
pub fn tPR(t: Rc<tabs>) -> Rc<Array<bool>> {
  let t_tPR_clone = Rc::clone(&t.tPR);
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Arbitrage.arbitrage_implem.f_c1
pub fn f_c1(_v0: ()) -> f64 {
  of_uint63(1048577u64)
}

// Rocq: Arbitrage.arbitrage_implem.f_c0
pub fn f_c0(_v0: ()) -> f64 {
  of_uint63(1048576u64)
}

// Rocq: Arbitrage.arbitrage_implem.fcmp
// Variant: uncurried
pub fn fcmp(m1: f64, e1: u64, n1: u64, m2: f64, e2: u64, n2: u64) -> Rc<option<bool>> {
  let tmp = ltb(__rocq_global_467, n1);
  let tmp_1 = ltb(__rocq_global_467, n2);
  if orb(tmp, tmp_1) {
    Rc::new(option::<bool>::None)
  } else {
    let tmp_2 = add_1(e2, 2u64);
    if leb(tmp_2, e1) {
      Rc::new(option::<bool>::Some(true))
    } else {
      let tmp_3 = add_1(e1, 2u64);
      if leb(tmp_3, e2) {
        Rc::new(option::<bool>::Some(false))
      } else {
        let x = if ltb(e2, e1) {
          mul_1(m1, f_two(()))
        } else {
          m1
        };
        let y = if ltb(e1, e2) {
          mul_1(m2, f_two(()))
        } else {
          m2
        };
        let tmp_4 = mul_1(y, f_c1(()));
        let tmp_5 = mul_1(x, f_c0(()));
        if ltb_1(tmp_4, tmp_5) {
          Rc::new(option::<bool>::Some(true))
        } else {
          let tmp_6 = mul_1(x, f_c1(()));
          let tmp_7 = mul_1(y, f_c0(()));
          if ltb_1(tmp_6, tmp_7) {
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
pub fn tMA(t: Rc<tabs>) -> Rc<Array<f64>> {
  let t_tMA_clone = Rc::clone(&t.tMA);
  std::mem::drop(t);
  t_tMA_clone
}

// Rocq: Arbitrage.arbitrage_implem.tEX
pub fn tEX(t: Rc<tabs>) -> Rc<Array<u64>> {
  let t_tEX_clone = Rc::clone(&t.tEX);
  std::mem::drop(t);
  t_tEX_clone
}

// Rocq: Arbitrage.arbitrage_implem.tCN
pub fn tCN(t: Rc<tabs>) -> Rc<Array<u64>> {
  let t_tCN_clone = Rc::clone(&t.tCN);
  std::mem::drop(t);
  t_tCN_clone
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb
// Variant: uncurried
pub fn ltsb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltsb(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.mul
// Variant: uncurried
pub fn mul_2(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::mul(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.pow
// Variant: uncurried
pub fn pow(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::pow(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div_1(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Arbitrage.arbitrage_implem.zofi_rec
pub fn zofi_rec_1(i: u64) -> Rc<BigInt> {
  zofi_rec(i, ())
}

// Rocq: Arbitrage.arbitrage_implem.zofi_rec (local: zofi_rec)
// Variant: uncurried, lifted
pub fn zofi_rec(i: u64, _H: ()) -> Rc<BigInt> {
  let tmp = eqb(i, 0u64);
  match bdec(tmp) {
    sumbool::left => {
      rocq_bigint::zero()
    },
    sumbool::right => {
      let r = zofi_rec(div_1(i, 2u64), ());
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

// Rocq: Arbitrage.arbitrage_implem.zofi
pub fn zofi(i: u64) -> Rc<BigInt> {
  zofi_rec_1(i)
}

// Rocq: Arbitrage.arbitrage_implem.primes
pub fn primes(_v0: ()) -> Rc<Array<u64>> {
  let tmp = rocq_array::make::<u64>(25u64, 0u64);
  let tmp_1 = rocq_array::set::<u64>(tmp, 0u64, 2u64);
  let tmp_2 = rocq_array::set::<u64>(tmp_1, 1u64, 3u64);
  let tmp_3 = rocq_array::set::<u64>(tmp_2, 2u64, 5u64);
  let tmp_4 = rocq_array::set::<u64>(tmp_3, 3u64, 7u64);
  let tmp_5 = rocq_array::set::<u64>(tmp_4, 4u64, 11u64);
  let tmp_6 = rocq_array::set::<u64>(tmp_5, 5u64, 13u64);
  let tmp_7 = rocq_array::set::<u64>(tmp_6, 6u64, 17u64);
  let tmp_8 = rocq_array::set::<u64>(tmp_7, 7u64, 19u64);
  let tmp_9 = rocq_array::set::<u64>(tmp_8, 8u64, 23u64);
  let tmp_10 = rocq_array::set::<u64>(tmp_9, 9u64, 29u64);
  let tmp_11 = rocq_array::set::<u64>(tmp_10, 10u64, 31u64);
  let tmp_12 = rocq_array::set::<u64>(tmp_11, 11u64, 37u64);
  let tmp_13 = rocq_array::set::<u64>(tmp_12, 12u64, 41u64);
  let tmp_14 = rocq_array::set::<u64>(tmp_13, 13u64, 43u64);
  let tmp_15 = rocq_array::set::<u64>(tmp_14, 14u64, 47u64);
  let tmp_16 = rocq_array::set::<u64>(tmp_15, 15u64, 53u64);
  let tmp_17 = rocq_array::set::<u64>(tmp_16, 16u64, 59u64);
  let tmp_18 = rocq_array::set::<u64>(tmp_17, 17u64, 61u64);
  let tmp_19 = rocq_array::set::<u64>(tmp_18, 18u64, 67u64);
  let tmp_20 = rocq_array::set::<u64>(tmp_19, 19u64, 71u64);
  let tmp_21 = rocq_array::set::<u64>(tmp_20, 20u64, 73u64);
  let tmp_22 = rocq_array::set::<u64>(tmp_21, 21u64, 79u64);
  let tmp_23 = rocq_array::set::<u64>(tmp_22, 22u64, 83u64);
  let tmp_24 = rocq_array::set::<u64>(tmp_23, 23u64, 89u64);
  rocq_array::set::<u64>(tmp_24, 24u64, 97u64)
}

// Rocq: Arbitrage.arbitrage_implem.ex_step
// Variant: borrowed, uncurried
pub fn ex_step(dv: &Rc<dyn Fn(u64) -> u64>, t: u64, s: ((bool, Rc<BigInt>), Rc<BigInt>)) -> ((bool, Rc<BigInt>), Rc<BigInt>) {
  let t_1 = t;
  let s_1 = s;
  match &s_1 {
    (Q, p) => {
      match Q {
        (_P, nz) => {
          let d = dv(t_1);
          if ltsb(0u64, d) {
            let tmp = primes(());
            let tmp_1 = rocq_array::get::<u64>(&tmp, t_1);
            std::mem::drop(tmp);
            let tmp_2 = zofi(tmp_1);
            let tmp_3 = zofi(d);
            let tmp_4 = pow(tmp_2, tmp_3);
            let nz_clone = Rc::clone(nz);
            let tmp_5 = mul_2(nz_clone, tmp_4);
            let tmp_6 = (true, tmp_5);
            let p_clone = Rc::clone(p);
            std::mem::drop(s_1);
            (tmp_6, p_clone)
          } else {
            if ltsb(d, 0u64) {
              let nz_clone_1 = Rc::clone(nz);
              let tmp_7 = (true, nz_clone_1);
              let tmp_8 = primes(());
              let tmp_9 = rocq_array::get::<u64>(&tmp_8, t_1);
              std::mem::drop(tmp_8);
              let tmp_10 = zofi(tmp_9);
              let tmp_11 = zofi(sub(0u64, d));
              let tmp_12 = pow(tmp_10, tmp_11);
              let p_clone_1 = Rc::clone(p);
              std::mem::drop(s_1);
              let tmp_13 = mul_2(p_clone_1, tmp_12);
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

// Rocq: Corelib.BinNums.IntDef.Z.ltb
// Variant: uncurried
pub fn ltb_2(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::lt(v0, v1)
}

// Rocq: Arbitrage.arbitrage_implem.exact_gt
pub fn exact_gt(dv: Rc<dyn Fn(u64) -> u64>) -> bool {
  let tmp = 25u64;
  let callback: Rc<dyn Fn(u64, ((bool, Rc<BigInt>), Rc<BigInt>)) -> bool> = Rc::new(move |_v5: u64, v6: ((bool, Rc<BigInt>), Rc<BigInt>)| -> bool {
    std::mem::drop(v6);
    true
  });
  let dv_clone: Rc<dyn Fn(u64) -> u64> = Rc::clone(&dv);
  let callback_1: Rc<dyn Fn(u64, ((bool, Rc<BigInt>), Rc<BigInt>)) -> ((bool, Rc<BigInt>), Rc<BigInt>)> = Rc::new({
    move |v19: u64, v20: ((bool, Rc<BigInt>), Rc<BigInt>)| -> ((bool, Rc<BigInt>), Rc<BigInt>) {
      let dv = &dv_clone;
      let tmp_1 = ex_step(dv, v19, v20);
      tmp_1
    }
  });
  let tmp_2 = rocq_bigint::one();
  let tmp_3 = rocq_bigint::identity(tmp_2);
  let tmp_4 = (false, tmp_3);
  let tmp_5 = rocq_bigint::one();
  let tmp_6 = rocq_bigint::identity(tmp_5);
  let tmp_7 = loop_::<((bool, Rc<BigInt>), Rc<BigInt>)>(tmp, callback, callback_1, 0u64, (tmp_4, tmp_6));
  match tmp_7 {
    (v68, v70) => {
      match v68 {
        (v73, v75) => {
          if v73 {
            std::mem::drop(dv);
            ltb_2(v70, v75)
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
pub fn dvd1(n: u64, x: u64) -> u64 {
  let tmp = mod_(n, x);
  if eqb(tmp, 0u64) {
    1u64
  } else {
    0u64
  }
}

// Rocq: Arbitrage.arbitrage_implem.mlt
// Variant: uncurried
pub fn mlt(n: u64, p: u64) -> u64 {
  let p2 = mul(p, p);
  let p3 = mul(p2, p);
  let p4 = mul(p3, p);
  let p5 = mul(p4, p);
  let p6 = mul(p5, p);
  let tmp = add_1(dvd1(n, p), dvd1(n, p2));
  let tmp_1 = add_1(tmp, dvd1(n, p3));
  let tmp_2 = add_1(tmp_1, dvd1(n, p4));
  let tmp_3 = add_1(tmp_2, dvd1(n, p5));
  add_1(tmp_3, dvd1(n, p6))
}

// Rocq: Arbitrage.arbitrage_implem.tVT
pub fn tVT_owned(t: Rc<tabs>) -> Rc<Array<u64>> {
  let t_tVT_clone = Rc::clone(&t.tVT);
  std::mem::drop(t);
  t_tVT_clone
}

// Rocq: Arbitrage.arbitrage_implem.tVT
// Variant: borrowed
pub fn tVT(t: &Rc<tabs>) -> Rc<Array<u64>> {
  let tmp = t;
  Rc::clone(&tmp.tVT)
}

// Rocq: Arbitrage.arbitrage_implem.wr_head
// Variant: uncurried
pub fn wr_head(T: Rc<tabs>, q: u64, m: f64, e: u64, n: u64, V: Rc<Array<u64>>) -> Rc<tabs> {
  let T_clone = Rc::clone(&T);
  let tmp = tPR(T_clone);
  let tmp_1 = rocq_array::set::<bool>(tmp, q, true);
  let T_clone_1 = Rc::clone(&T);
  let tmp_2 = tMA(T_clone_1);
  let tmp_3 = rocq_array::set::<f64>(tmp_2, q, m);
  let T_clone_2 = Rc::clone(&T);
  let tmp_4 = tEX(T_clone_2);
  let tmp_5 = rocq_array::set::<u64>(tmp_4, q, e);
  let tmp_6 = tCN(T);
  let tmp_7 = rocq_array::set::<u64>(tmp_6, q, n);
  Rc::new(tabs { tPR: tmp_1, tMA: tmp_3, tEX: tmp_5, tCN: tmp_7, tVT: V })
}

// Rocq: Arbitrage.arbitrage_implem.vset
// Variant: uncurried
pub fn vset(bd: u64, a: u64, b: u64, V: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let tmp = 25u64;
  let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(move |_v8: u64, v9: Rc<Array<u64>>| -> bool {
    std::mem::drop(v9);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
    move |t: u64, W: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let bd = &bd;
      let b = &b;
      let a = &a;
      let tmp_1 = add_1(Clone::clone(bd), t);
      let tmp_2 = primes(());
      let tmp_3 = rocq_array::get::<u64>(&tmp_2, t);
      std::mem::drop(tmp_2);
      let tmp_4 = mlt(Clone::clone(b), tmp_3);
      let tmp_5 = primes(());
      let tmp_6 = rocq_array::get::<u64>(&tmp_5, t);
      std::mem::drop(tmp_5);
      let a_clone = Clone::clone(a);
      rocq_array::set::<u64>(W, tmp_1, sub(tmp_4, mlt(a_clone, tmp_6)))
    }
  });
  loop_::<Rc<Array<u64>>>(tmp, callback, callback_1, 0u64, V)
}

// Rocq: Arbitrage.arbitrage_implem.init_step
// Variant: uncurried
pub fn init_step(c: u64, xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, r: u64, T: Rc<tabs>) -> Rc<tabs> {
  let u = rocq_array::get::<u64>(&xs, r);
  let v = rocq_array::get::<u64>(&xd, r);
  let a = rocq_array::get::<u64>(&xa, r);
  let b = rocq_array::get::<u64>(&xb, r);
  let q = add_1(mul(u, c), v);
  let tmp = ratecell(a, b);
  match tmp {
    (v42, v44) => {
      let p = &v44;
      match v42 {
        (v48, v50) => {
          let e = &v48;
          let m = &v50;
          let T_clone = Rc::clone(&T);
          let tmp_1 = tPR(T_clone);
          let tmp_2 = rocq_array::get::<bool>(&tmp_1, q);
          let better = if tmp_2 {
            let T_clone_1 = Rc::clone(&T);
            let tmp_3 = tMA(T_clone_1);
            let tmp_4 = rocq_array::get::<f64>(&tmp_3, q);
            let T_clone_2 = Rc::clone(&T);
            let tmp_5 = tEX(T_clone_2);
            let tmp_6 = rocq_array::get::<u64>(&tmp_5, q);
            let T_clone_3 = Rc::clone(&T);
            let tmp_7 = tCN(T_clone_3);
            let tmp_8 = rocq_array::get::<u64>(&tmp_7, q);
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
                let callback: Rc<dyn Fn(u64) -> u64> = Rc::new({
                  let __anf_capture_126 = b;
                  let __anf_capture_128 = a;
                  let __anf_capture_132 = q;
                  move |t: u64| -> u64 {
                    let b = &__anf_capture_126;
                    let a = &__anf_capture_128;
                    let T = &T_clone_4;
                    let q = &__anf_capture_132;
                    let tmp_10 = primes(());
                    let tmp_11 = rocq_array::get::<u64>(&tmp_10, t);
                    std::mem::drop(tmp_10);
                    let tmp_12 = mlt(Clone::clone(b), tmp_11);
                    let tmp_13 = primes(());
                    let tmp_14 = rocq_array::get::<u64>(&tmp_13, t);
                    std::mem::drop(tmp_13);
                    let tmp_15 = sub(tmp_12, mlt(Clone::clone(a), tmp_14));
                    let tmp_16 = tVT(T);
                    let q_clone = Clone::clone(q);
                    let tmp_17 = rocq_array::get::<u64>(&tmp_16, add_1(mul(25u64, q_clone), t));
                    std::mem::drop(tmp_16);
                    sub(tmp_15, tmp_17)
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
            let tmp_18 = mul(25u64, q);
            let T_clone_5 = Rc::clone(&T);
            let tmp_19 = tVT_owned(T_clone_5);
            let tmp_20 = vset(tmp_18, a, b, tmp_19);
            let e_clone = Clone::clone(e);
            let m_clone = Clone::clone(m);
            let p_clone = Clone::clone(p);
            wr_head(T, q, e_clone, m_clone, p_clone, tmp_20)
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
pub fn negb(b: bool) -> bool {
  if b {
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

// Rocq: Corelib.Floats.PrimFloat.leb
// Variant: uncurried
pub fn leb_1(v0: f64, v1: f64) -> bool {
  rocq_float64::leb(v0, v1)
}

// Rocq: Arbitrage.arbitrage_implem.mulcell
// Variant: uncurried
pub fn mulcell(m1: f64, e1: u64, n1: u64, m2: f64, e2: u64, n2: u64) -> ((f64, u64), u64) {
  let p = mul_1(m1, m2);
  let tmp = add_1(n1, n2);
  let n = add_1(tmp, 2u64);
  let tmp_1 = __rocq_global_467;
  let n_ = if ltb(tmp_1, n) {
    add_1(__rocq_global_467, 1u64)
  } else {
    n
  };
  let tmp_2 = f_two(());
  if leb_1(tmp_2, p) {
    let tmp_3 = div(p, f_two(()));
    let tmp_4 = add_1(e1, e2);
    ((tmp_3, add_1(sub(tmp_4, __rocq_global_359), 1u64)), n_)
  } else {
    ((p, sub(add_1(e1, e2), __rocq_global_359)), n_)
  }
}

// Rocq: Arbitrage.arbitrage_implem.vadd
// Variant: uncurried
pub fn vadd(bd: u64, b1: u64, b2: u64, V: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let tmp = 25u64;
  let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(move |_v8: u64, v9: Rc<Array<u64>>| -> bool {
    std::mem::drop(v9);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
    move |t: u64, W: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let bd = &bd;
      let b1 = &b1;
      let b2 = &b2;
      let tmp_1 = add_1(Clone::clone(bd), t);
      let tmp_2 = rocq_array::get::<u64>(&W, add_1(Clone::clone(b1), t));
      let b2_clone = Clone::clone(b2);
      let tmp_3 = rocq_array::get::<u64>(&W, add_1(b2_clone, t));
      rocq_array::set::<u64>(W, tmp_1, add_1(tmp_2, tmp_3))
    }
  });
  loop_::<Rc<Array<u64>>>(tmp, callback, callback_1, 0u64, V)
}

// Rocq: Arbitrage.arbitrage_implem.fw_j
// Variant: uncurried
pub fn fw_j(c: u64, k: u64, i: u64, j: u64, s: (Rc<tabs>, bool)) -> (Rc<tabs>, bool) {
  let s_clone = Clone::clone(&s);
  let T = fst::<Rc<tabs>, bool>(s_clone);
  if eqb(j, k) {
    std::mem::drop(T);
    s
  } else {
    let qkj = add_1(mul(k, c), j);
    let T_clone = Rc::clone(&T);
    let tmp = tPR(T_clone);
    let tmp_1 = rocq_array::get::<bool>(&tmp, qkj);
    if tmp_1 {
      let qik = add_1(mul(i, c), k);
      let qij = add_1(mul(i, c), j);
      let T_clone_1 = Rc::clone(&T);
      let tmp_2 = tMA(T_clone_1);
      let tmp_3 = rocq_array::get::<f64>(&tmp_2, qik);
      let T_clone_2 = Rc::clone(&T);
      let tmp_4 = tEX(T_clone_2);
      let tmp_5 = rocq_array::get::<u64>(&tmp_4, qik);
      let T_clone_3 = Rc::clone(&T);
      let tmp_6 = tCN(T_clone_3);
      let tmp_7 = rocq_array::get::<u64>(&tmp_6, qik);
      let T_clone_4 = Rc::clone(&T);
      let tmp_8 = tMA(T_clone_4);
      let tmp_9 = rocq_array::get::<f64>(&tmp_8, qkj);
      let T_clone_5 = Rc::clone(&T);
      let tmp_10 = tEX(T_clone_5);
      let tmp_11 = rocq_array::get::<u64>(&tmp_10, qkj);
      let T_clone_6 = Rc::clone(&T);
      let tmp_12 = tCN(T_clone_6);
      let tmp_13 = rocq_array::get::<u64>(&tmp_12, qkj);
      let tmp_14 = mulcell(tmp_3, tmp_5, tmp_7, tmp_9, tmp_11, tmp_13);
      match tmp_14 {
        (v134, v136) => {
          let p = &v136;
          match v134 {
            (v140, v142) => {
              let e = &v140;
              let m = &v142;
              let bik = mul(25u64, qik);
              let bkj = mul(25u64, qkj);
              let bij = mul(25u64, qij);
              let ex = if eqb(i, j) {
                let tmp_15 = fcmp(v140, v142, v136, f_one(()), __rocq_global_359, 0u64);
                let (v200, v201) = __rocq_reuse::reset(tmp_15, |__payload| Clone::clone(__payload));
                std::mem::drop(v201);
                match v200 {
                  option::Some(v206) => {
                    v206
                  },
                  option::None => {
                    let T_clone_7 = Rc::clone(&T);
                    let callback: Rc<dyn Fn(u64) -> u64> = Rc::new({
                      let __anf_capture_219 = bik;
                      let __anf_capture_223 = bkj;
                      move |t: u64| -> u64 {
                        let bik = &__anf_capture_219;
                        let T = &T_clone_7;
                        let bkj = &__anf_capture_223;
                        let tmp_16 = tVT(T);
                        let tmp_17 = rocq_array::get::<u64>(&tmp_16, add_1(Clone::clone(bik), t));
                        std::mem::drop(tmp_16);
                        let tmp_18 = tVT(T);
                        let bkj_clone = Clone::clone(bkj);
                        let tmp_19 = rocq_array::get::<u64>(&tmp_18, add_1(bkj_clone, t));
                        std::mem::drop(tmp_18);
                        add_1(tmp_17, tmp_19)
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
                let tmp_21 = rocq_array::get::<bool>(&tmp_20, qij);
                let better = if tmp_21 {
                  let T_clone_9 = Rc::clone(&T);
                  let tmp_22 = tMA(T_clone_9);
                  let tmp_23 = rocq_array::get::<f64>(&tmp_22, qij);
                  let T_clone_10 = Rc::clone(&T);
                  let tmp_24 = tEX(T_clone_10);
                  let tmp_25 = rocq_array::get::<u64>(&tmp_24, qij);
                  let T_clone_11 = Rc::clone(&T);
                  let tmp_26 = tCN(T_clone_11);
                  let tmp_27 = rocq_array::get::<u64>(&tmp_26, qij);
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
                      let callback_1: Rc<dyn Fn(u64) -> u64> = Rc::new({
                        let __anf_capture_358 = bik;
                        let __anf_capture_360 = bkj;
                        let __anf_capture_364 = bij;
                        move |t: u64| -> u64 {
                          let bik = &__anf_capture_358;
                          let bkj = &__anf_capture_360;
                          let T = &T_clone_12;
                          let bij = &__anf_capture_364;
                          let tmp_29 = tVT(T);
                          let tmp_30 = rocq_array::get::<u64>(&tmp_29, add_1(Clone::clone(bik), t));
                          std::mem::drop(tmp_29);
                          let tmp_31 = tVT(T);
                          let tmp_32 = rocq_array::get::<u64>(&tmp_31, add_1(Clone::clone(bkj), t));
                          std::mem::drop(tmp_31);
                          let tmp_33 = add_1(tmp_30, tmp_32);
                          let tmp_34 = tVT(T);
                          let bij_clone = Clone::clone(bij);
                          let tmp_35 = rocq_array::get::<u64>(&tmp_34, add_1(bij_clone, t));
                          std::mem::drop(tmp_34);
                          sub(tmp_33, tmp_35)
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
                  let tmp_36 = tVT_owned(T_clone_13);
                  let tmp_37 = vadd(bij, bik, bkj, tmp_36);
                  let e_clone = Clone::clone(e);
                  let m_clone = Clone::clone(m);
                  let p_clone = Clone::clone(p);
                  (wr_head(T, qij, e_clone, m_clone, p_clone, tmp_37), false)
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
pub fn fw_i(c: u64, k: u64, i: u64, s: (Rc<tabs>, bool)) -> (Rc<tabs>, bool) {
  if eqb(i, k) {
    s
  } else {
    let s_clone = Clone::clone(&s);
    let tmp = tPR(fst::<Rc<tabs>, bool>(s_clone));
    let tmp_1 = rocq_array::get::<bool>(&tmp, add_1(mul(i, c), k));
    if tmp_1 {
      std::mem::drop(tmp);
      let callback: Rc<dyn Fn(u64, (Rc<tabs>, bool)) -> bool> = Rc::new(move |_v41: u64, s: (Rc<tabs>, bool)| -> bool {
        negb(snd::<Rc<tabs>, bool>(s))
      });
      let callback_1: Rc<dyn Fn(u64, (Rc<tabs>, bool)) -> (Rc<tabs>, bool)> = Rc::new({
        let __anf_capture_62 = c;
        let __anf_capture_64 = k;
        let __anf_capture_66 = i;
        move |v68: u64, v69: (Rc<tabs>, bool)| -> (Rc<tabs>, bool) {
          let tmp_2 = Clone::clone(&__anf_capture_62);
          let tmp_3 = Clone::clone(&__anf_capture_64);
          let tmp_4 = Clone::clone(&__anf_capture_66);
          fw_j(tmp_2, tmp_3, tmp_4, v68, v69)
        }
      });
      loop_::<(Rc<tabs>, bool)>(c, callback, callback_1, 0u64, s)
    } else {
      std::mem::drop(tmp);
      s
    }
  }
}

// Rocq: Arbitrage.arbitrage_implem.fw_k
// Variant: uncurried
pub fn fw_k(c: u64, k: u64, s: (Rc<tabs>, bool)) -> (Rc<tabs>, bool) {
  let callback: Rc<dyn Fn(u64, (Rc<tabs>, bool)) -> bool> = Rc::new(move |_v5: u64, s: (Rc<tabs>, bool)| -> bool {
    negb(snd::<Rc<tabs>, bool>(s))
  });
  let callback_1: Rc<dyn Fn(u64, (Rc<tabs>, bool)) -> (Rc<tabs>, bool)> = Rc::new({
    let __anf_capture_24 = c;
    move |v28: u64, v29: (Rc<tabs>, bool)| -> (Rc<tabs>, bool) {
      let tmp = Clone::clone(&__anf_capture_24);
      let k_clone = Clone::clone(&k);
      fw_i(tmp, k_clone, v28, v29)
    }
  });
  loop_::<(Rc<tabs>, bool)>(c, callback, callback_1, 0u64, s)
}

// Rocq: Arbitrage.arbitrage_implem.arbitrage_impl
// Variant: uncurried
pub fn arbitrage_impl(c: u64, xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, xa: Rc<Array<u64>>, xb: Rc<Array<u64>>) -> bool {
  let cc = mul(c, c);
  let tmp = rocq_array::make::<bool>(cc, false);
  let tmp_1 = rocq_array::make::<f64>(cc, f_one(()));
  let tmp_2 = rocq_array::make::<u64>(cc, 0u64);
  let tmp_3 = rocq_array::make::<u64>(cc, 0u64);
  let tmp_4 = rocq_array::make::<u64>(mul(25u64, cc), 0u64);
  let T0 = Rc::new(tabs { tPR: tmp, tMA: tmp_1, tEX: tmp_2, tCN: tmp_3, tVT: tmp_4 });
  let tmp_5 = rocq_array::length::<u64>(&xs);
  let callback: Rc<dyn Fn(u64, Rc<tabs>) -> bool> = Rc::new(move |_v75: u64, v76: Rc<tabs>| -> bool {
    std::mem::drop(v76);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<tabs>) -> Rc<tabs>> = Rc::new({
    let __anf_capture_94 = c;
    let __anf_capture_96 = xs;
    move |v104: u64, v105: Rc<tabs>| -> Rc<tabs> {
      let tmp_6 = Clone::clone(&__anf_capture_94);
      let tmp_7 = Rc::clone(&__anf_capture_96);
      let xd_clone = Rc::clone(&xd);
      let xa_clone = Rc::clone(&xa);
      let xb_clone = Rc::clone(&xb);
      init_step(tmp_6, tmp_7, xd_clone, xa_clone, xb_clone, v104, v105)
    }
  });
  let T1 = loop_::<Rc<tabs>>(tmp_5, callback, callback_1, 0u64, T0);
  let callback_2: Rc<dyn Fn(u64, (Rc<tabs>, bool)) -> bool> = Rc::new(move |_v142: u64, s: (Rc<tabs>, bool)| -> bool {
    negb(snd::<Rc<tabs>, bool>(s))
  });
  let callback_3: Rc<dyn Fn(u64, (Rc<tabs>, bool)) -> (Rc<tabs>, bool)> = Rc::new({
    let __anf_capture_159 = c;
    move |v161: u64, v162: (Rc<tabs>, bool)| -> (Rc<tabs>, bool) {
      let tmp_8 = Clone::clone(&__anf_capture_159);
      fw_k(tmp_8, v161, v162)
    }
  });
  snd::<Rc<tabs>, bool>(loop_::<(Rc<tabs>, bool)>(c, callback_2, callback_3, 0u64, (T1, false)))
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
const __rocq_global_359: u64 = 1073741824u64;
const __rocq_global_467: u64 = 1048576u64;