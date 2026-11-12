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

// Rocq: Arbitrage.arbitrage_implem.arbitrage
// Variant: uncurried
pub fn arbitrage() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> bool> {
  let v0: fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> bool = arbitrage_impl;
  let v1: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> bool> = Rc::new(v0);
  v1
}

// Rocq: Arbitrage.arbitrage_implem.arbitrage
pub fn arbitrage_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>>> = arbitrage_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>>>> = Rc::new(v0);
  v1
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
  let v8 = rocq_bigint::add(v0, v1);
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

// Rocq: Arbitrage.arbitrage_implem.bdec
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

// Rocq: Arbitrage.arbitrage_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Arbitrage.arbitrage_implem.wloop (local: wloop)
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
  let num = match ltb(ha, hb) {
    true => {
      lsl(b, sub(hb, ha))
    },
    false => {
      b
    },
  };
  let den = match ltb(ha, hb) {
    true => {
      a
    },
    false => {
      lsl(a, sub(ha, hb))
    },
  };
  let r = div(of_uint63(num), of_uint63(den));
  let e = sub(add_1(__rocq_global_359, ha), hb);
  let v91 = f_one(());
  match ltb_1(r, v91) {
    true => {
      ((mul_1(r, f_two(())), sub(e, 1u64)), 2u64)
    },
    false => {
      ((r, e), 2u64)
    },
  }
}

// Rocq: Arbitrage.arbitrage_implem.tPR
pub fn tPR(t: Rc<tabs>) -> Rc<Array<bool>> {
  let v3 = Rc::clone((&(&**&t).tPR));
  std::mem::drop(t);
  v3
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
  let v13 = ltb(__rocq_global_467, n1);
  let v20 = ltb(__rocq_global_467, n2);
  match orb(v13, v20) {
    true => {
      Rc::new(option::<bool>::None)
    },
    false => {
      let v41 = add_1(e2, 2u64);
      match leb(v41, e1) {
        true => {
          Rc::new(option::<bool>::Some(true))
        },
        false => {
          let v65 = add_1(e1, 2u64);
          match leb(v65, e2) {
            true => {
              Rc::new(option::<bool>::Some(false))
            },
            false => {
              let x = match ltb(e2, e1) {
                true => {
                  mul_1(m1, f_two(()))
                },
                false => {
                  m1
                },
              };
              let y = match ltb(e1, e2) {
                true => {
                  mul_1(m2, f_two(()))
                },
                false => {
                  m2
                },
              };
              let v140 = mul_1(y, f_c1(()));
              let v152 = mul_1(x, f_c0(()));
              match ltb_1(v140, v152) {
                true => {
                  Rc::new(option::<bool>::Some(true))
                },
                false => {
                  let v180 = mul_1(x, f_c1(()));
                  let v192 = mul_1(y, f_c0(()));
                  match ltb_1(v180, v192) {
                    true => {
                      Rc::new(option::<bool>::Some(false))
                    },
                    false => {
                      Rc::new(option::<bool>::None)
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

// Rocq: Arbitrage.arbitrage_implem.tMA
pub fn tMA(t: Rc<tabs>) -> Rc<Array<f64>> {
  let v3 = Rc::clone((&(&**&t).tMA));
  std::mem::drop(t);
  v3
}

// Rocq: Arbitrage.arbitrage_implem.tEX
pub fn tEX(t: Rc<tabs>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tEX));
  std::mem::drop(t);
  v3
}

// Rocq: Arbitrage.arbitrage_implem.tCN
pub fn tCN(t: Rc<tabs>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tCN));
  std::mem::drop(t);
  v3
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb
// Variant: uncurried
pub fn ltsb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltsb(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.mul
// Variant: uncurried
pub fn mul_2(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::mul(v0, v1);
  v8
}

// Rocq: Corelib.BinNums.IntDef.Z.pow
// Variant: uncurried
pub fn pow(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::pow(v0, v1);
  v8
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
  let v9 = zofi_rec(i, ());
  v9
}

// Rocq: Arbitrage.arbitrage_implem.zofi_rec (local: zofi_rec)
// Variant: uncurried, lifted
pub fn zofi_rec(i: u64, _H: ()) -> Rc<BigInt> {
  let v11 = eqb(i, 0u64);
  let v83 = match bdec(v11) {
    sumbool::left => {
      let v16 = rocq_bigint::zero();
      v16
    },
    sumbool::right => {
      let r = zofi_rec(div_1(i, 2u64), ());
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

// Rocq: Arbitrage.arbitrage_implem.zofi
pub fn zofi(i: u64) -> Rc<BigInt> {
  let v5 = zofi_rec_1(i);
  v5
}

// Rocq: Arbitrage.arbitrage_implem.primes
pub fn primes(_v0: ()) -> Rc<Array<u64>> {
  let v9 = rocq_array::make::<u64>(25u64, 0u64);
  let v20 = rocq_array::set::<u64>(v9, 0u64, 2u64);
  let v31 = rocq_array::set::<u64>(v20, 1u64, 3u64);
  let v42 = rocq_array::set::<u64>(v31, 2u64, 5u64);
  let v53 = rocq_array::set::<u64>(v42, 3u64, 7u64);
  let v64 = rocq_array::set::<u64>(v53, 4u64, 11u64);
  let v75 = rocq_array::set::<u64>(v64, 5u64, 13u64);
  let v86 = rocq_array::set::<u64>(v75, 6u64, 17u64);
  let v97 = rocq_array::set::<u64>(v86, 7u64, 19u64);
  let v108 = rocq_array::set::<u64>(v97, 8u64, 23u64);
  let v119 = rocq_array::set::<u64>(v108, 9u64, 29u64);
  let v130 = rocq_array::set::<u64>(v119, 10u64, 31u64);
  let v141 = rocq_array::set::<u64>(v130, 11u64, 37u64);
  let v152 = rocq_array::set::<u64>(v141, 12u64, 41u64);
  let v163 = rocq_array::set::<u64>(v152, 13u64, 43u64);
  let v174 = rocq_array::set::<u64>(v163, 14u64, 47u64);
  let v185 = rocq_array::set::<u64>(v174, 15u64, 53u64);
  let v196 = rocq_array::set::<u64>(v185, 16u64, 59u64);
  let v207 = rocq_array::set::<u64>(v196, 17u64, 61u64);
  let v218 = rocq_array::set::<u64>(v207, 18u64, 67u64);
  let v229 = rocq_array::set::<u64>(v218, 19u64, 71u64);
  let v240 = rocq_array::set::<u64>(v229, 20u64, 73u64);
  let v251 = rocq_array::set::<u64>(v240, 21u64, 79u64);
  let v262 = rocq_array::set::<u64>(v251, 22u64, 83u64);
  let v273 = rocq_array::set::<u64>(v262, 23u64, 89u64);
  rocq_array::set::<u64>(v273, 24u64, 97u64)
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
          match ltsb(0u64, d) {
            true => {
              let v39 = primes(());
              let v40 = &v39;
              let v43 = rocq_array::get::<u64>(&v40, t_1);
              std::mem::drop(v39);
              let v46 = zofi(v43);
              let v50 = zofi(d);
              let v55 = pow(v46, v50);
              let v57 = Rc::clone(nz);
              let v60 = mul_2(v57, v55);
              let v68 = (true, v60);
              let v69 = Rc::clone(p);
              std::mem::drop(s_1);
              (v68, v69)
            },
            false => {
              match ltsb(d, 0u64) {
                true => {
                  let v89 = Rc::clone(nz);
                  let v91 = (true, v89);
                  let v100 = primes(());
                  let v101 = &v100;
                  let v104 = rocq_array::get::<u64>(&v101, t_1);
                  std::mem::drop(v100);
                  let v107 = zofi(v104);
                  let v119 = zofi(sub(0u64, d));
                  let v124 = pow(v107, v119);
                  let v125 = Rc::clone(p);
                  std::mem::drop(s_1);
                  let v129 = mul_2(v125, v124);
                  (v91, v129)
                },
                false => {
                  s_1
                },
              }
            },
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
  let v3 = 25u64;
  let v4 = {
    move |_v5: u64, v6: ((bool, Rc<BigInt>), Rc<BigInt>)| -> bool {
      std::mem::drop(v6);
      true
    }
  };
  let v11: Rc<dyn Fn(u64, ((bool, Rc<BigInt>), Rc<BigInt>)) -> bool> = Rc::new(v4);
  let v12: Rc<dyn Fn(u64, ((bool, Rc<BigInt>), Rc<BigInt>)) -> bool> = v11;
  let v14: Rc<dyn Fn(u64) -> u64> = Rc::clone(&dv);
  let v16 = {
    move |v19: u64, v20: ((bool, Rc<BigInt>), Rc<BigInt>)| -> ((bool, Rc<BigInt>), Rc<BigInt>) {
      let dv = &v14;
      let v27 = ex_step(dv, v19, v20);
      v27
    }
  };
  let v30: Rc<dyn Fn(u64, ((bool, Rc<BigInt>), Rc<BigInt>)) -> ((bool, Rc<BigInt>), Rc<BigInt>)> = Rc::new(v16);
  let v37 = rocq_bigint::one();
  let v39 = rocq_bigint::identity(v37);
  let v44 = (false, v39);
  let v47 = rocq_bigint::one();
  let v49 = rocq_bigint::identity(v47);
  let v66 = loop_::<((bool, Rc<BigInt>), Rc<BigInt>)>(v3, v12, v30, 0u64, (v44, v49));
  match v66 {
    (v68, v70) => {
      match v68 {
        (v73, v75) => {
          match v73 {
            true => {
              std::mem::drop(dv);
              ltb_2(v70, v75)
            },
            false => {
              std::mem::drop(dv);
              std::mem::drop(v75);
              std::mem::drop(v70);
              false
            },
          }
        },
      }
    },
  }
}

// Rocq: Arbitrage.arbitrage_implem.dvd1
// Variant: uncurried
pub fn dvd1(n: u64, x: u64) -> u64 {
  let v8 = mod_(n, x);
  match eqb(v8, 0u64) {
    true => {
      1u64
    },
    false => {
      0u64
    },
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
  let v53 = add_1(dvd1(n, p), dvd1(n, p2));
  let v64 = add_1(v53, dvd1(n, p3));
  let v75 = add_1(v64, dvd1(n, p4));
  let v86 = add_1(v75, dvd1(n, p5));
  add_1(v86, dvd1(n, p6))
}

// Rocq: Arbitrage.arbitrage_implem.tVT
pub fn tVT_owned(t: Rc<tabs>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tVT));
  std::mem::drop(t);
  v3
}

// Rocq: Arbitrage.arbitrage_implem.tVT
// Variant: borrowed
pub fn tVT(t: &Rc<tabs>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tVT))
}

// Rocq: Arbitrage.arbitrage_implem.wr_head
// Variant: uncurried
pub fn wr_head(T: Rc<tabs>, q: u64, m: f64, e: u64, n: u64, V: Rc<Array<u64>>) -> Rc<tabs> {
  let v9 = Rc::clone(&T);
  let v10 = tPR(v9);
  let v19 = rocq_array::set::<bool>(v10, q, true);
  let v23 = Rc::clone(&T);
  let v25 = tMA(v23);
  let v31 = rocq_array::set::<f64>(v25, q, m);
  let v35 = Rc::clone(&T);
  let v37 = tEX(v35);
  let v43 = rocq_array::set::<u64>(v37, q, e);
  let v48 = tCN(T);
  let v54 = rocq_array::set::<u64>(v48, q, n);
  Rc::new(tabs { tPR: v19, tMA: v31, tEX: v43, tCN: v54, tVT: V })
}

// Rocq: Arbitrage.arbitrage_implem.vset
// Variant: uncurried
pub fn vset(bd: u64, a: u64, b: u64, V: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v6 = 25u64;
  let v7 = {
    move |_v8: u64, v9: Rc<Array<u64>>| -> bool {
      std::mem::drop(v9);
      true
    }
  };
  let v14: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(v7);
  let v15: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = v14;
  let v22 = {
    move |t: u64, W: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let bd = &bd;
      let b = &b;
      let a = &a;
      let v36 = add_1(Clone::clone(bd), t);
      let v44 = primes(());
      let v45 = &v44;
      let v48 = rocq_array::get::<u64>(&v45, t);
      std::mem::drop(v44);
      let v53 = mlt(Clone::clone(b), v48);
      let v60 = primes(());
      let v61 = &v60;
      let v64 = rocq_array::get::<u64>(&v61, t);
      std::mem::drop(v60);
      let v66 = Clone::clone(a);
      rocq_array::set::<u64>(W, v36, sub(v53, mlt(v66, v64)))
    }
  };
  let v84: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v22);
  loop_::<Rc<Array<u64>>>(v6, v15, v84, 0u64, V)
}

// Rocq: Arbitrage.arbitrage_implem.init_step
// Variant: uncurried
pub fn init_step(c: u64, xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, r: u64, T: Rc<tabs>) -> Rc<tabs> {
  let v7 = &xs;
  let u = rocq_array::get::<u64>(&v7, r);
  let v11 = &xd;
  let v = rocq_array::get::<u64>(&v11, r);
  let v15 = &xa;
  let a = rocq_array::get::<u64>(&v15, r);
  let v19 = &xb;
  let b = rocq_array::get::<u64>(&v19, r);
  let q = add_1(mul(u, c), v);
  let v40 = ratecell(a, b);
  match v40 {
    (v42, v44) => {
      let p = &v44;
      match v42 {
        (v48, v50) => {
          let e = &v48;
          let m = &v50;
          let v57 = Rc::clone(&T);
          let v58 = tPR(v57);
          let v59 = &v58;
          let v62 = rocq_array::get::<bool>(&v59, q);
          let better = match v62 {
            true => {
              let v68 = Rc::clone(&T);
              let v69 = tMA(v68);
              let v70 = &v69;
              let v73 = rocq_array::get::<f64>(&v70, q);
              let v77 = Rc::clone(&T);
              let v78 = tEX(v77);
              let v79 = &v78;
              let v82 = rocq_array::get::<u64>(&v79, q);
              let v86 = Rc::clone(&T);
              let v87 = tCN(v86);
              let v88 = &v87;
              let v91 = rocq_array::get::<u64>(&v88, q);
              let v104 = fcmp(v48, v50, v44, v73, v82, v91);
              let (v105, v106) = __rocq_reuse::reset(v104, |__payload| Clone::clone(__payload));
              std::mem::drop(v106);
              match v105 {
                option::Some(v111) => {
                  std::mem::drop(v87);
                  std::mem::drop(v78);
                  std::mem::drop(v69);
                  v111
                },
                option::None => {
                  std::mem::drop(v87);
                  std::mem::drop(v78);
                  std::mem::drop(v69);
                  let v122 = Rc::clone(&T);
                  let v125 = {
                    let __anf_capture_126 = b;
                    let __anf_capture_128 = a;
                    let __anf_capture_132 = q;
                    move |t: u64| -> u64 {
                      let b = &__anf_capture_126;
                      let a = &__anf_capture_128;
                      let T = &v122;
                      let q = &__anf_capture_132;
                      let v143 = primes(());
                      let v144 = &v143;
                      let v147 = rocq_array::get::<u64>(&v144, t);
                      std::mem::drop(v143);
                      let v152 = mlt(Clone::clone(b), v147);
                      let v159 = primes(());
                      let v160 = &v159;
                      let v163 = rocq_array::get::<u64>(&v160, t);
                      std::mem::drop(v159);
                      let v173 = sub(v152, mlt(Clone::clone(a), v163));
                      let v176 = tVT(T);
                      let v184 = Clone::clone(q);
                      let v190 = add_1(mul(25u64, v184), t);
                      let v191 = &v176;
                      let v194 = rocq_array::get::<u64>(&v191, v190);
                      std::mem::drop(v176);
                      sub(v173, v194)
                    }
                  };
                  let v202: Rc<dyn Fn(u64) -> u64> = Rc::new(v125);
                  exact_gt(v202)
                },
              }
            },
            false => {
              true
            },
          };
          match better {
            true => {
              std::mem::drop(xs);
              std::mem::drop(xd);
              std::mem::drop(xa);
              std::mem::drop(v58);
              std::mem::drop(xb);
              let v227 = mul(25u64, q);
              let v231 = Rc::clone(&T);
              let v232 = tVT_owned(v231);
              let v241 = vset(v227, a, b, v232);
              let v247 = Clone::clone(e);
              let v249 = Clone::clone(m);
              let v251 = Clone::clone(p);
              wr_head(T, q, v247, v249, v251, v241)
            },
            false => {
              std::mem::drop(xs);
              std::mem::drop(xd);
              std::mem::drop(xa);
              std::mem::drop(v58);
              std::mem::drop(xb);
              T
            },
          }
        },
      }
    },
  }
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let v3 = Clone::clone((&(&p).1));
  std::mem::drop(p);
  v3
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

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
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
  let v18 = add_1(n1, n2);
  let n = add_1(v18, 2u64);
  let v28 = __rocq_global_467;
  let n_ = match ltb(v28, n) {
    true => {
      add_1(__rocq_global_467, 1u64)
    },
    false => {
      n
    },
  };
  let v55 = f_two(());
  match leb_1(v55, p) {
    true => {
      let v72 = div(p, f_two(()));
      let v80 = add_1(e1, e2);
      ((v72, add_1(sub(v80, __rocq_global_359), 1u64)), n_)
    },
    false => {
      ((p, sub(add_1(e1, e2), __rocq_global_359)), n_)
    },
  }
}

// Rocq: Arbitrage.arbitrage_implem.vadd
// Variant: uncurried
pub fn vadd(bd: u64, b1: u64, b2: u64, V: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v6 = 25u64;
  let v7 = {
    move |_v8: u64, v9: Rc<Array<u64>>| -> bool {
      std::mem::drop(v9);
      true
    }
  };
  let v14: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(v7);
  let v15: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = v14;
  let v22 = {
    move |t: u64, W: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let bd = &bd;
      let b1 = &b1;
      let b2 = &b2;
      let v36 = add_1(Clone::clone(bd), t);
      let v43 = add_1(Clone::clone(b1), t);
      let v44 = &W;
      let v47 = rocq_array::get::<u64>(&v44, v43);
      let v50 = Clone::clone(b2);
      let v53 = add_1(v50, t);
      let v54 = &W;
      let v57 = rocq_array::get::<u64>(&v54, v53);
      rocq_array::set::<u64>(W, v36, add_1(v47, v57))
    }
  };
  let v72: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v22);
  loop_::<Rc<Array<u64>>>(v6, v15, v72, 0u64, V)
}

// Rocq: Arbitrage.arbitrage_implem.fw_j
// Variant: uncurried
pub fn fw_j(c: u64, k: u64, i: u64, j: u64, s: (Rc<tabs>, bool)) -> (Rc<tabs>, bool) {
  let v7 = Clone::clone(&s);
  let T = fst::<Rc<tabs>, bool>(v7);
  match eqb(j, k) {
    true => {
      std::mem::drop(T);
      s
    },
    false => {
      let qkj = add_1(mul(k, c), j);
      let v34 = Rc::clone(&T);
      let v35 = tPR(v34);
      let v36 = &v35;
      let v39 = rocq_array::get::<bool>(&v36, qkj);
      match v39 {
        true => {
          let qik = add_1(mul(i, c), k);
          let qij = add_1(mul(i, c), j);
          let v69 = Rc::clone(&T);
          let v70 = tMA(v69);
          let v71 = &v70;
          let v74 = rocq_array::get::<f64>(&v71, qik);
          let v78 = Rc::clone(&T);
          let v79 = tEX(v78);
          let v80 = &v79;
          let v83 = rocq_array::get::<u64>(&v80, qik);
          let v87 = Rc::clone(&T);
          let v88 = tCN(v87);
          let v89 = &v88;
          let v92 = rocq_array::get::<u64>(&v89, qik);
          let v96 = Rc::clone(&T);
          let v97 = tMA(v96);
          let v98 = &v97;
          let v101 = rocq_array::get::<f64>(&v98, qkj);
          let v105 = Rc::clone(&T);
          let v106 = tEX(v105);
          let v107 = &v106;
          let v110 = rocq_array::get::<u64>(&v107, qkj);
          let v114 = Rc::clone(&T);
          let v115 = tCN(v114);
          let v116 = &v115;
          let v119 = rocq_array::get::<u64>(&v116, qkj);
          let v132 = mulcell(v74, v83, v92, v101, v110, v119);
          match v132 {
            (v134, v136) => {
              let p = &v136;
              match v134 {
                (v140, v142) => {
                  let e = &v140;
                  let m = &v142;
                  let bik = mul(25u64, qik);
                  let bkj = mul(25u64, qkj);
                  let bij = mul(25u64, qij);
                  let ex = match eqb(i, j) {
                    true => {
                      let v199 = fcmp(v140, v142, v136, f_one(()), __rocq_global_359, 0u64);
                      let (v200, v201) = __rocq_reuse::reset(v199, |__payload| Clone::clone(__payload));
                      std::mem::drop(v201);
                      match v200 {
                        option::Some(v206) => {
                          v206
                        },
                        option::None => {
                          let v215 = Rc::clone(&T);
                          let v218 = {
                            let __anf_capture_219 = bik;
                            let __anf_capture_223 = bkj;
                            move |t: u64| -> u64 {
                              let bik = &__anf_capture_219;
                              let T = &v215;
                              let bkj = &__anf_capture_223;
                              let v229 = tVT(T);
                              let v235 = add_1(Clone::clone(bik), t);
                              let v236 = &v229;
                              let v239 = rocq_array::get::<u64>(&v236, v235);
                              std::mem::drop(v229);
                              let v242 = tVT(T);
                              let v245 = Clone::clone(bkj);
                              let v248 = add_1(v245, t);
                              let v249 = &v242;
                              let v252 = rocq_array::get::<u64>(&v249, v248);
                              std::mem::drop(v242);
                              add_1(v239, v252)
                            }
                          };
                          let v260: Rc<dyn Fn(u64) -> u64> = Rc::new(v218);
                          exact_gt(v260)
                        },
                      }
                    },
                    false => {
                      false
                    },
                  };
                  match ex {
                    true => {
                      std::mem::drop(v115);
                      std::mem::drop(v106);
                      std::mem::drop(v97);
                      std::mem::drop(v79);
                      std::mem::drop(v70);
                      std::mem::drop(s);
                      std::mem::drop(v88);
                      std::mem::drop(v35);
                      (T, true)
                    },
                    false => {
                      let v289 = Rc::clone(&T);
                      let v290 = tPR(v289);
                      let v291 = &v290;
                      let v294 = rocq_array::get::<bool>(&v291, qij);
                      let better = match v294 {
                        true => {
                          let v300 = Rc::clone(&T);
                          let v301 = tMA(v300);
                          let v302 = &v301;
                          let v305 = rocq_array::get::<f64>(&v302, qij);
                          let v309 = Rc::clone(&T);
                          let v310 = tEX(v309);
                          let v311 = &v310;
                          let v314 = rocq_array::get::<u64>(&v311, qij);
                          let v318 = Rc::clone(&T);
                          let v319 = tCN(v318);
                          let v320 = &v319;
                          let v323 = rocq_array::get::<u64>(&v320, qij);
                          let v336 = fcmp(Clone::clone(e), Clone::clone(m), Clone::clone(p), v305, v314, v323);
                          let (v337, v338) = __rocq_reuse::reset(v336, |__payload| Clone::clone(__payload));
                          std::mem::drop(v338);
                          match v337 {
                            option::Some(v343) => {
                              std::mem::drop(v319);
                              std::mem::drop(v310);
                              std::mem::drop(v301);
                              v343
                            },
                            option::None => {
                              std::mem::drop(v319);
                              std::mem::drop(v310);
                              std::mem::drop(v301);
                              let v354 = Rc::clone(&T);
                              let v357 = {
                                let __anf_capture_358 = bik;
                                let __anf_capture_360 = bkj;
                                let __anf_capture_364 = bij;
                                move |t: u64| -> u64 {
                                  let bik = &__anf_capture_358;
                                  let bkj = &__anf_capture_360;
                                  let T = &v354;
                                  let bij = &__anf_capture_364;
                                  let v371 = tVT(T);
                                  let v377 = add_1(Clone::clone(bik), t);
                                  let v378 = &v371;
                                  let v381 = rocq_array::get::<u64>(&v378, v377);
                                  std::mem::drop(v371);
                                  let v384 = tVT(T);
                                  let v390 = add_1(Clone::clone(bkj), t);
                                  let v391 = &v384;
                                  let v394 = rocq_array::get::<u64>(&v391, v390);
                                  std::mem::drop(v384);
                                  let v399 = add_1(v381, v394);
                                  let v402 = tVT(T);
                                  let v405 = Clone::clone(bij);
                                  let v408 = add_1(v405, t);
                                  let v409 = &v402;
                                  let v412 = rocq_array::get::<u64>(&v409, v408);
                                  std::mem::drop(v402);
                                  sub(v399, v412)
                                }
                              };
                              let v420: Rc<dyn Fn(u64) -> u64> = Rc::new(v357);
                              exact_gt(v420)
                            },
                          }
                        },
                        false => {
                          true
                        },
                      };
                      match better {
                        true => {
                          std::mem::drop(v290);
                          std::mem::drop(v115);
                          std::mem::drop(v106);
                          std::mem::drop(v97);
                          std::mem::drop(v79);
                          std::mem::drop(v70);
                          std::mem::drop(s);
                          std::mem::drop(v88);
                          std::mem::drop(v35);
                          let v441 = Rc::clone(&T);
                          let v442 = tVT_owned(v441);
                          let v451 = vadd(bij, bik, bkj, v442);
                          let v457 = Clone::clone(e);
                          let v459 = Clone::clone(m);
                          let v461 = Clone::clone(p);
                          (wr_head(T, qij, v457, v459, v461, v451), false)
                        },
                        false => {
                          std::mem::drop(v290);
                          std::mem::drop(v115);
                          std::mem::drop(v106);
                          std::mem::drop(v97);
                          std::mem::drop(v79);
                          std::mem::drop(v70);
                          std::mem::drop(v88);
                          std::mem::drop(T);
                          std::mem::drop(v35);
                          s
                        },
                      }
                    },
                  }
                },
              }
            },
          }
        },
        false => {
          std::mem::drop(T);
          std::mem::drop(v35);
          s
        },
      }
    },
  }
}

// Rocq: Arbitrage.arbitrage_implem.fw_i
// Variant: uncurried
pub fn fw_i(c: u64, k: u64, i: u64, s: (Rc<tabs>, bool)) -> (Rc<tabs>, bool) {
  match eqb(i, k) {
    true => {
      s
    },
    false => {
      let v16 = Clone::clone(&s);
      let v21 = tPR(fst::<Rc<tabs>, bool>(v16));
      let v33 = add_1(mul(i, c), k);
      let v34 = &v21;
      let v37 = rocq_array::get::<bool>(&v34, v33);
      match v37 {
        true => {
          std::mem::drop(v21);
          let v40 = {
            move |_v41: u64, s: (Rc<tabs>, bool)| -> bool {
              negb(snd::<Rc<tabs>, bool>(s))
            }
          };
          let v53: Rc<dyn Fn(u64, (Rc<tabs>, bool)) -> bool> = Rc::new(v40);
          let v54: Rc<dyn Fn(u64, (Rc<tabs>, bool)) -> bool> = v53;
          let v61 = {
            let __anf_capture_62 = c;
            let __anf_capture_64 = k;
            let __anf_capture_66 = i;
            move |v68: u64, v69: (Rc<tabs>, bool)| -> (Rc<tabs>, bool) {
              let v72 = Clone::clone(&__anf_capture_62);
              let v74 = Clone::clone(&__anf_capture_64);
              let v76 = Clone::clone(&__anf_capture_66);
              fw_j(v72, v74, v76, v68, v69)
            }
          };
          let v84: Rc<dyn Fn(u64, (Rc<tabs>, bool)) -> (Rc<tabs>, bool)> = Rc::new(v61);
          loop_::<(Rc<tabs>, bool)>(c, v54, v84, 0u64, s)
        },
        false => {
          std::mem::drop(v21);
          s
        },
      }
    },
  }
}

// Rocq: Arbitrage.arbitrage_implem.fw_k
// Variant: uncurried
pub fn fw_k(c: u64, k: u64, s: (Rc<tabs>, bool)) -> (Rc<tabs>, bool) {
  let v4 = {
    move |_v5: u64, s: (Rc<tabs>, bool)| -> bool {
      negb(snd::<Rc<tabs>, bool>(s))
    }
  };
  let v17: Rc<dyn Fn(u64, (Rc<tabs>, bool)) -> bool> = Rc::new(v4);
  let v18: Rc<dyn Fn(u64, (Rc<tabs>, bool)) -> bool> = v17;
  let v23 = {
    let __anf_capture_24 = c;
    move |v28: u64, v29: (Rc<tabs>, bool)| -> (Rc<tabs>, bool) {
      let v32 = Clone::clone(&__anf_capture_24);
      let v34 = Clone::clone(&k);
      fw_i(v32, v34, v28, v29)
    }
  };
  let v42: Rc<dyn Fn(u64, (Rc<tabs>, bool)) -> (Rc<tabs>, bool)> = Rc::new(v23);
  loop_::<(Rc<tabs>, bool)>(c, v18, v42, 0u64, s)
}

// Rocq: Arbitrage.arbitrage_implem.arbitrage_impl
// Variant: uncurried
pub fn arbitrage_impl(c: u64, xs: Rc<Array<u64>>, xd: Rc<Array<u64>>, xa: Rc<Array<u64>>, xb: Rc<Array<u64>>) -> bool {
  let cc = mul(c, c);
  let v17 = rocq_array::make::<bool>(cc, false);
  let v28 = rocq_array::make::<f64>(cc, f_one(()));
  let v35 = rocq_array::make::<u64>(cc, 0u64);
  let v42 = rocq_array::make::<u64>(cc, 0u64);
  let v57 = rocq_array::make::<u64>(mul(25u64, cc), 0u64);
  let T0 = Rc::new(tabs { tPR: v17, tMA: v28, tEX: v35, tCN: v42, tVT: v57 });
  let v72 = &xs;
  let v73 = rocq_array::length::<u64>(&v72);
  let v74 = {
    move |_v75: u64, v76: Rc<tabs>| -> bool {
      std::mem::drop(v76);
      true
    }
  };
  let v81: Rc<dyn Fn(u64, Rc<tabs>) -> bool> = Rc::new(v74);
  let v82: Rc<dyn Fn(u64, Rc<tabs>) -> bool> = v81;
  let v93 = {
    let __anf_capture_94 = c;
    let __anf_capture_96 = xs;
    move |v104: u64, v105: Rc<tabs>| -> Rc<tabs> {
      let v108 = Clone::clone(&__anf_capture_94);
      let v110 = Rc::clone(&__anf_capture_96);
      let v112 = Rc::clone(&xd);
      let v114 = Rc::clone(&xa);
      let v116 = Rc::clone(&xb);
      init_step(v108, v110, v112, v114, v116, v104, v105)
    }
  };
  let v124: Rc<dyn Fn(u64, Rc<tabs>) -> Rc<tabs>> = Rc::new(v93);
  let T1 = loop_::<Rc<tabs>>(v73, v82, v124, 0u64, T0);
  let v141 = {
    move |_v142: u64, s: (Rc<tabs>, bool)| -> bool {
      negb(snd::<Rc<tabs>, bool>(s))
    }
  };
  let v154: Rc<dyn Fn(u64, (Rc<tabs>, bool)) -> bool> = Rc::new(v141);
  let v155: Rc<dyn Fn(u64, (Rc<tabs>, bool)) -> bool> = v154;
  let v158 = {
    let __anf_capture_159 = c;
    move |v161: u64, v162: (Rc<tabs>, bool)| -> (Rc<tabs>, bool) {
      let v165 = Clone::clone(&__anf_capture_159);
      fw_k(v165, v161, v162)
    }
  };
  let v173: Rc<dyn Fn(u64, (Rc<tabs>, bool)) -> (Rc<tabs>, bool)> = Rc::new(v158);
  snd::<Rc<tabs>, bool>(loop_::<(Rc<tabs>, bool)>(c, v155, v173, 0u64, (T1, false)))
}

// Rocq: Arbitrage.arbitrage_implem.arbitrage_impl
pub fn arbitrage_impl_curried(c: u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>>> {
  let v3 = {
    move |xs: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>> {
      let c = &c;
      let v8 = Clone::clone(c);
      let v11 = {
        move |xd: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>> {
          let c = &v8;
          let xs = &xs;
          let v18 = Clone::clone(c);
          let v20 = Rc::clone(xs);
          let v23 = {
            move |xa: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> bool> {
              let c = &v18;
              let xs = &v20;
              let xd = &xd;
              let v32 = Clone::clone(c);
              let v34 = Rc::clone(xs);
              let v36 = Rc::clone(xd);
              let v39 = {
                move |xb: Rc<Array<u64>>| -> bool {
                  let v51 = Clone::clone(&v32);
                  let v53 = Rc::clone(&v34);
                  let v55 = Rc::clone(&v36);
                  let v57 = Rc::clone(&xa);
                  arbitrage_impl(v51, v53, v55, v57, xb)
                }
              };
              let v63: Rc<dyn Fn(Rc<Array<u64>>) -> bool> = Rc::new(v39);
              v63
            }
          };
          let v67: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>> = Rc::new(v23);
          v67
        }
      };
      let v71: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>> = Rc::new(v11);
      v71
    }
  };
  let v75: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>>> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> bool> {
  let v0: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> bool> = __rocq_global_1555.with(Clone::clone);
  v0
}
const __rocq_global_359: u64 = 1073741824u64;
const __rocq_global_467: u64 = 1048576u64;
std::thread_local! { static __rocq_global_1555: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> bool> = arbitrage(); }
std::thread_local! { static __rocq_global_1558: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>>>>> = arbitrage_curried(); }