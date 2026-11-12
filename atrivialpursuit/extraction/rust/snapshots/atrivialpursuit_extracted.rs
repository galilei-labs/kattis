// Generated from OwnedANF. This printer is not verified.
#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

#[derive(Clone, Copy)]
pub enum bres {
  BFound,
  BComp,
  BFail,
}

#[derive(Clone, Copy)]
pub enum cres {
  CPrime,
  CComp,
  CFail,
}

#[derive(Clone, Copy)]
pub enum kind {
  KPrime,
  KSquare,
  KSemi,
}

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = u64;

// Rocq: Atrivialpursuit.atrivialpursuit_implem.LIM
pub fn LIM() -> u64 {
  1000000u64
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.MODP
pub fn MODP() -> u64 {
  1000000007u64
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.T12
pub fn T12() -> u64 {
  1000000000000u64
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.ALIM
pub fn ALIM() -> u64 {
  1000u64
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.RHOC
pub fn RHOC() -> u64 {
  40u64
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.atrivialpursuit
// Variant: uncurried
pub fn atrivialpursuit() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> {
  let v0: fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> u64 = atp_impl;
  let v1: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> = Rc::new(v0);
  v1
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.atrivialpursuit
pub fn atrivialpursuit_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> = atp_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.land
// Variant: uncurried
pub fn land(v0: u64, v1: u64) -> u64 {
  rocq_int63::land(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsr
// Variant: uncurried
pub fn lsr(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsr(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.bdec
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
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
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

// Rocq: Atrivialpursuit.atrivialpursuit_implem.mark_loop
// Variant: uncurried
pub fn mark_loop_1(m: Rc<Array<bool>>, i: u64, j: u64) -> Rc<Array<bool>> {
  mark_loop(m, i, j, (), ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.mark_loop (local: mark_loop)
// Variant: uncurried, lifted
pub fn mark_loop(m: Rc<Array<bool>>, i: u64, j: u64, _Hi: (), _H: ()) -> Rc<Array<bool>> {
  let v13 = ltb(j, __rocq_global_43);
  match bdec(v13) {
    sumbool::left => {
      let v25 = rocq_array::set::<bool>(m, j, true);
      let v31 = add(j, i);
      mark_loop(v25, i, v31, (), ())
    },
    sumbool::right => {
      m
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.sieve_loop
// Variant: uncurried
pub fn sieve_loop_1(m: Rc<Array<bool>>, pr: Rc<Array<u64>>, np: u64, i: u64) -> (Rc<Array<u64>>, u64) {
  sieve_loop(m, pr, np, i, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.sieve_loop (local: sieve_loop)
// Variant: uncurried, lifted
pub fn sieve_loop(m: Rc<Array<bool>>, pr: Rc<Array<u64>>, np: u64, i: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let v13 = ltb(i, __rocq_global_43);
  match bdec(v13) {
    sumbool::left => {
      let v17 = &m;
      let v20 = rocq_array::get::<bool>(&v17, i);
      match v20 {
        true => {
          sieve_loop(m, pr, np, add(i, 1u64), ())
        },
        false => {
          let v68 = andb(ltb(0u64, i), ltb(i, __rocq_global_43));
          match bdec(v68) {
            sumbool::left => {
              let v78 = add(i, i);
              let v85 = mark_loop_1(m, i, v78);
              let v92 = rocq_array::set::<u64>(pr, np, i);
              sieve_loop(v85, v92, add(np, 1u64), add(i, 1u64), ())
            },
            sumbool::right => {
              std::mem::drop(m);
              (pr, np)
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(m);
      (pr, np)
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.sieve
pub fn sieve(_v0: ()) -> (Rc<Array<u64>>, u64) {
  let v9 = rocq_array::make::<bool>(__rocq_global_43, false);
  let v17 = rocq_array::make::<u64>(__rocq_global_43, 0u64);
  sieve_loop_1(v9, v17, 0u64, 2u64)
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.divfull
// Variant: uncurried
pub fn divfull_1(x: u64, c: u64, k: u64) -> (u64, u64) {
  divfull(x, c, k, (), ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.divfull (local: divfull)
// Variant: uncurried, lifted
pub fn divfull(x: u64, c: u64, k: u64, _Hx: (), _H: ()) -> (u64, u64) {
  let v14 = ltb(0u64, c);
  match bdec(v14) {
    sumbool::left => {
      let v24 = mod_(c, x);
      match eqb(v24, 0u64) {
        true => {
          let v38 = div(c, x);
          divfull(x, v38, add(k, 1u64), (), ())
        },
        false => {
          (c, k)
        },
      }
    },
    sumbool::right => {
      (c, k)
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.divpass
// Variant: uncurried
pub fn divpass_1(x: u64, a: Rc<Array<u64>>, n: u64, j: u64, e: u64) -> (Rc<Array<u64>>, u64) {
  divpass(x, (), a, n, j, e, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.divpass (local: divpass)
// Variant: uncurried, lifted
pub fn divpass(x: u64, _Hx: (), a: Rc<Array<u64>>, n: u64, j: u64, e: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let v14 = ltb(j, n);
  match bdec(v14) {
    sumbool::left => {
      let v18 = &a;
      let c = rocq_array::get::<u64>(&v18, j);
      let v28 = mod_(c, x);
      match eqb(v28, 0u64) {
        true => {
          let ck = divfull_1(x, c, 0u64);
          let v51 = Clone::clone(&ck);
          let v60 = rocq_array::set::<u64>(a, j, fst::<u64, u64>(v51));
          divpass(x, (), v60, n, add(j, 1u64), add(e, snd::<u64, u64>(ck)), ())
        },
        false => {
          divpass(x, (), a, n, add(j, 1u64), e, ())
        },
      }
    },
    sumbool::right => {
      (a, e)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mulc$rust_low$uncurry$0
// Variant: uncurried
pub fn mulc_rust_low_uncurry_0(v0: u64, v1: u64) -> u64 {
  rocq_int63::mulc_low(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mulc$rust_high$uncurry$0
// Variant: uncurried
pub fn mulc_rust_high_uncurry_0(v0: u64, v1: u64) -> u64 {
  rocq_int63::mulc_high(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mulc
// Variant: uncurried
pub fn mulc(x: u64, x_1: u64) -> (u64, u64) {
  (mulc_rust_high_uncurry_0(x, x_1), mulc_rust_low_uncurry_0(x, x_1))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.diveucl_21$rust_remainder$uncurry$0
// Variant: uncurried
pub fn diveucl_21_rust_remainder_uncurry_0(v0: u64, v1: u64, v2: u64) -> u64 {
  rocq_int63::diveucl_21_remainder(v0, v1, v2)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.diveucl_21$rust_quotient$uncurry$0
// Variant: uncurried
pub fn diveucl_21_rust_quotient_uncurry_0(v0: u64, v1: u64, v2: u64) -> u64 {
  rocq_int63::diveucl_21_quotient(v0, v1, v2)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.diveucl_21
// Variant: uncurried
pub fn diveucl_21(x: u64, x_1: u64, x_2: u64) -> (u64, u64) {
  (diveucl_21_rust_quotient_uncurry_0(x, x_1, x_2), diveucl_21_rust_remainder_uncurry_0(x, x_1, x_2))
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.mulmod
// Variant: uncurried
pub fn mulmod(a: u64, b: u64, n: u64) -> u64 {
  let v8 = mulc(a, b);
  match v8 {
    (v10, v12) => {
      snd::<u64, u64>(diveucl_21(v10, v12, n))
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.step_acc
// Variant: uncurried
pub fn step_acc(acc: u64, eg: u64, el: u64, f: Rc<dyn Fn(u64) -> u64>) -> u64 {
  match eqb(eg, el) {
    true => {
      std::mem::drop(f);
      acc
    },
    false => {
      match ltb(el, eg) {
        true => {
          std::mem::drop(f);
          0u64
        },
        false => {
          let v30 = sub(el, eg);
          let v31: &Rc<dyn Fn(u64) -> u64> = &f;
          let v34 = v31(v30);
          std::mem::drop(f);
          mulmod(acc, v34, __rocq_global_525)
        },
      }
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.pow_loop
// Variant: uncurried
pub fn pow_loop_1(b: u64, e: u64, r: u64, n: u64) -> u64 {
  pow_loop(b, e, r, n, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.pow_loop (local: pow_loop)
// Variant: uncurried, lifted
pub fn pow_loop(b: u64, e: u64, r: u64, n: u64, _H: ()) -> u64 {
  let v14 = ltb(0u64, e);
  match bdec(v14) {
    sumbool::left => {
      let v25 = mulmod(b, b, n);
      let v33 = lsr(e, 1u64);
      let v42 = land(e, 1u64);
      let v44 = 1u64;
      let v50 = match eqb(v42, v44) {
        true => {
          mulmod(r, b, n)
        },
        false => {
          r
        },
      };
      pow_loop(v25, v33, v50, n, ())
    },
    sumbool::right => {
      r
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.powmod
// Variant: uncurried
pub fn powmod(b: u64, e: u64, n: u64) -> u64 {
  pow_loop_1(mod_(b, n), e, mod_(1u64, n), n)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.fmod
// Variant: uncurried
pub fn fmod(e: u64, P: u64) -> u64 {
  let a = powmod(add(e, 1u64), P, __rocq_global_525);
  let b = powmod(e, P, __rocq_global_525);
  let c = powmod(sub(e, 1u64), P, __rocq_global_525);
  let v68 = add(a, mul(2u64, sub(__rocq_global_525, b)));
  mod_(add(v68, c), __rocq_global_525)
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.ph1
// Variant: uncurried
pub fn ph1_1(pr: Rc<Array<u64>>, np: u64, k: u64, aG: Rc<Array<u64>>, aL: Rc<Array<u64>>, nG: u64, nL: u64, P: u64, acc: u64) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  ph1(pr, np, k, aG, aL, nG, nL, P, acc, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.ph1 (local: ph1)
// Variant: uncurried, lifted
pub fn ph1(pr: Rc<Array<u64>>, np: u64, k: u64, aG: Rc<Array<u64>>, aL: Rc<Array<u64>>, nG: u64, nL: u64, P: u64, acc: u64, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let v17 = ltb(k, np);
  match bdec(v17) {
    sumbool::left => {
      let v21 = &pr;
      let p = rocq_array::get::<u64>(&v21, k);
      let v34 = ltb(1u64, p);
      match bdec(v34) {
        sumbool::left => {
          let rG = divpass_1(p, aG, nG, 0u64, 0u64);
          let rL = divpass_1(p, aL, nL, 0u64, 0u64);
          let v77 = add(k, 1u64);
          let v80 = Clone::clone(&rG);
          let v82 = fst::<Rc<Array<u64>>, u64>(v80);
          let v85 = Clone::clone(&rL);
          let v87 = fst::<Rc<Array<u64>>, u64>(v85);
          let v92 = snd::<Rc<Array<u64>>, u64>(rG);
          let v96 = snd::<Rc<Array<u64>>, u64>(rL);
          let v99 = {
            let __anf_capture_100 = P;
            move |e: u64| -> u64 {
              let v107 = Clone::clone(&__anf_capture_100);
              fmod(e, v107)
            }
          };
          let v111: Rc<dyn Fn(u64) -> u64> = Rc::new(v99);
          ph1(pr, np, v77, v82, v87, nG, nL, P, step_acc(acc, v92, v96, v111), ())
        },
        sumbool::right => {
          std::mem::drop(pr);
          ((aG, aL), acc)
        },
      }
    },
    sumbool::right => {
      std::mem::drop(pr);
      ((aG, aL), acc)
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.sel_get
// Variant: uncurried
pub fn sel_get(sel: bool, aG: Rc<Array<u64>>, aL: Rc<Array<u64>>, i: u64) -> u64 {
  match sel {
    true => {
      std::mem::drop(aG);
      let v5 = &aL;
      let v8 = rocq_array::get::<u64>(&v5, i);
      std::mem::drop(aL);
      v8
    },
    false => {
      std::mem::drop(aL);
      let v11 = &aG;
      let v14 = rocq_array::get::<u64>(&v11, i);
      std::mem::drop(aG);
      v14
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.gcd_loop
// Variant: uncurried
pub fn gcd_loop_1(a: u64, b: u64) -> u64 {
  gcd_loop(a, b, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.gcd_loop (local: gcd_loop)
// Variant: uncurried, lifted
pub fn gcd_loop(a: u64, b: u64, _H: ()) -> u64 {
  let v12 = ltb(0u64, b);
  match bdec(v12) {
    sumbool::left => {
      let v21 = mod_(a, b);
      gcd_loop(b, v21, ())
    },
    sumbool::right => {
      a
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.igcd
// Variant: uncurried
pub fn igcd(a: u64, b: u64) -> u64 {
  gcd_loop_1(a, b)
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.refine
// Variant: uncurried
pub fn refine_1(a: Rc<Array<u64>>, n: u64, j: u64, x: u64) -> u64 {
  refine(a, n, j, x, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.refine (local: refine)
// Variant: uncurried, lifted
pub fn refine(a: Rc<Array<u64>>, n: u64, j: u64, x: u64, _H: ()) -> u64 {
  let v12 = ltb(j, n);
  match bdec(v12) {
    sumbool::left => {
      let v17 = &a;
      let v20 = rocq_array::get::<u64>(&v17, j);
      let d = igcd(x, v20);
      let v33 = add(j, 1u64);
      let v42 = ltb(1u64, d);
      let v48 = ltb(d, x);
      let v54 = match andb(v42, v48) {
        true => {
          d
        },
        false => {
          x
        },
      };
      refine(a, n, v33, v54, ())
    },
    sumbool::right => {
      std::mem::drop(a);
      x
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.isq_loop
// Variant: uncurried
pub fn isq_loop_1(x: u64, s: u64, w: u64) -> u64 {
  isq_loop(x, s, w, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.isq_loop (local: isq_loop)
// Variant: uncurried, lifted
pub fn isq_loop(x: u64, s: u64, w: u64, _H: ()) -> u64 {
  let v13 = ltb(1u64, w);
  match bdec(v13) {
    sumbool::left => {
      let b = lsr(w, 1u64);
      let t = add(s, b);
      let v38 = mul(t, t);
      match leb(v38, x) {
        true => {
          isq_loop(x, t, sub(w, b), ())
        },
        false => {
          isq_loop(x, s, b, ())
        },
      }
    },
    sumbool::right => {
      s
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.isqrt
pub fn isqrt(x: u64) -> u64 {
  isq_loop_1(x, 0u64, 2147483648u64)
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

// Rocq: Atrivialpursuit.atrivialpursuit_implem.strip2
// Variant: uncurried
pub fn strip2_1(d: u64, s: u64) -> (u64, u64) {
  strip2(d, s, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.strip2 (local: strip2)
// Variant: uncurried, lifted
pub fn strip2(d: u64, s: u64, _H: ()) -> (u64, u64) {
  let v34 = andb(ltb(0u64, d), eqb(land(d, 1u64), 0u64));
  match bdec(v34) {
    sumbool::left => {
      strip2(lsr(d, 1u64), add(s, 1u64), ())
    },
    sumbool::right => {
      (d, s)
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.mr_loop
// Variant: uncurried
pub fn mr_loop_1(n: u64, y: u64, i: u64, s: u64) -> bool {
  mr_loop(n, y, i, s, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.mr_loop (local: mr_loop)
// Variant: uncurried, lifted
pub fn mr_loop(n: u64, y: u64, i: u64, s: u64, _H: ()) -> bool {
  let v12 = ltb(i, s);
  match bdec(v12) {
    sumbool::left => {
      let v24 = sub(n, 1u64);
      match eqb(y, v24) {
        true => {
          false
        },
        false => {
          let y_ = mulmod(y, y, n);
          match eqb(y_, 1u64) {
            true => {
              true
            },
            false => {
              mr_loop(n, y_, add(i, 1u64), s, ())
            },
          }
        },
      }
    },
    sumbool::right => {
      true
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.mr_base
// Variant: uncurried
pub fn mr_base(n: u64, a: u64) -> bool {
  let v17 = strip2_1(sub(n, 1u64), 0u64);
  match v17 {
    (v19, v21) => {
      let y = powmod(a, v19, n);
      match eqb(y, 1u64) {
        true => {
          false
        },
        false => {
          mr_loop_1(n, y, 0u64, v21)
        },
      }
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.mr_comp
pub fn mr_comp(n: u64) -> bool {
  let v32 = orb(mr_base(n, 2u64), mr_base(n, 3u64));
  let v45 = orb(v32, mr_base(n, 5u64));
  let v58 = orb(v45, mr_base(n, 7u64));
  let v71 = orb(v58, mr_base(n, 11u64));
  let v84 = orb(v71, mr_base(n, 13u64));
  let v97 = orb(v84, mr_base(n, 17u64));
  let v110 = orb(v97, mr_base(n, 19u64));
  let v123 = orb(v110, mr_base(n, 23u64));
  let v136 = orb(v123, mr_base(n, 29u64));
  let v149 = orb(v136, mr_base(n, 31u64));
  orb(v149, mr_base(n, 37u64))
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

// Rocq: Atrivialpursuit.atrivialpursuit_implem.find_base
// Variant: uncurried
pub fn find_base_1(n: u64, m: u64, q: u64, a: u64) -> bres {
  find_base(n, m, q, a, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.find_base (local: find_base)
// Variant: uncurried, lifted
pub fn find_base(n: u64, m: u64, q: u64, a: u64, _H: ()) -> bres {
  let v13 = ltb(a, __rocq_global_1183);
  match bdec(v13) {
    sumbool::left => {
      let v34 = eqb(powmod(a, m, n), 1u64);
      match negb(v34) {
        true => {
          bres::BComp
        },
        false => {
          let u = powmod(a, div(m, q), n);
          let g = igcd(mod_(sub(add(u, n), 1u64), n), n);
          match eqb(g, 1u64) {
            true => {
              bres::BFound
            },
            false => {
              match ltb(g, n) {
                true => {
                  bres::BComp
                },
                false => {
                  find_base(n, m, q, add(a, 1u64), ())
                },
              }
            },
          }
        },
      }
    },
    sumbool::right => {
      bres::BFail
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.td_cert
// Variant: borrowed, uncurried
pub fn td_cert_1(pr: &Rc<Array<u64>>, np: u64, k: u64, n: u64, m: u64, F: u64, R: u64) -> ((bres, u64), u64) {
  let np_1 = np;
  let k_1 = k;
  let n_1 = n;
  let m_1 = m;
  let F_1 = F;
  let R_1 = R;
  td_cert(pr, np_1, k_1, n_1, m_1, F_1, R_1, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.td_cert (local: td_cert)
// Variant: borrowed, uncurried, lifted
pub fn td_cert(pr: &Rc<Array<u64>>, np: u64, k: u64, n: u64, m: u64, F: u64, R: u64, _H: ()) -> ((bres, u64), u64) {
  let np_1 = np;
  let k_1 = k;
  let n_1 = n;
  let m_1 = m;
  let F_1 = F;
  let R_1 = R;
  let v21 = ltb(k_1, np_1);
  match bdec(v21) {
    sumbool::left => {
      let v32 = div(n_1, F_1);
      match ltb(v32, F_1) {
        true => {
          ((bres::BFound, F_1), R_1)
        },
        false => {
          let v54 = pr;
          let q = rocq_array::get::<u64>(&v54, k_1);
          let v64 = mod_(R_1, q);
          match eqb(v64, 0u64) {
            true => {
              let v82 = ltb(1u64, q);
              match bdec(v82) {
                sumbool::left => {
                  let Rk = divfull_1(q, R_1, 0u64);
                  match find_base_1(n_1, m_1, q, 2u64) {
                    bres::BFound => {
                      let v116 = add(k_1, 1u64);
                      let v121 = Clone::clone(&Rk);
                      td_cert(pr, np_1, v116, n_1, m_1, mul(F_1, div(R_1, fst::<u64, u64>(v121))), fst::<u64, u64>(Rk), ())
                    },
                    bres::BComp => {
                      std::mem::drop(Rk);
                      ((bres::BComp, F_1), R_1)
                    },
                    bres::BFail => {
                      std::mem::drop(Rk);
                      ((bres::BFail, F_1), R_1)
                    },
                  }
                },
                sumbool::right => {
                  ((bres::BFail, F_1), R_1)
                },
              }
            },
            false => {
              td_cert(pr, np_1, add(k_1, 1u64), n_1, m_1, F_1, R_1, ())
            },
          }
        },
      }
    },
    sumbool::right => {
      ((bres::BFound, F_1), R_1)
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.base_res
pub fn base_res(b: bres) -> cres {
  match b {
    bres::BFound => {
      cres::CPrime
    },
    bres::BComp => {
      cres::CComp
    },
    bres::BFail => {
      cres::CFail
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.rho_loop
// Variant: uncurried
pub fn rho_loop_1(n: u64, c: u64, x: u64, y: u64, q: u64, j: u64, r: u64, b: u64, budget: u64) -> u64 {
  rho_loop(n, c, x, y, q, j, r, b, budget, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.rho_loop (local: rho_loop)
// Variant: uncurried, lifted
pub fn rho_loop(n: u64, c: u64, x: u64, y: u64, q: u64, j: u64, r: u64, b: u64, budget: u64, _H: ()) -> u64 {
  let v19 = ltb(0u64, budget);
  match bdec(v19) {
    sumbool::left => {
      let y_ = mod_(add(mulmod(y, y, n), c), n);
      let diff = match ltb(x, y_) {
        true => {
          sub(y_, x)
        },
        false => {
          sub(x, y_)
        },
      };
      let q_ = mulmod(q, diff, n);
      let b_ = add(b, 1u64);
      let v85 = 128u64;
      let g = match eqb(b_, v85) {
        true => {
          igcd(q_, n)
        },
        false => {
          1u64
        },
      };
      let v114 = eqb(g, 1u64);
      match negb(v114) {
        true => {
          g
        },
        false => {
          let v122 = 128u64;
          let b__ = match eqb(b_, v122) {
            true => {
              0u64
            },
            false => {
              b_
            },
          };
          let j_ = add(j, 1u64);
          match eqb(j_, r) {
            true => {
              rho_loop(n, c, y_, y_, q_, 0u64, add(r, r), b__, sub(budget, 1u64), ())
            },
            false => {
              rho_loop(n, c, x, y_, q_, j_, r, b__, sub(budget, 1u64), ())
            },
          }
        },
      }
    },
    sumbool::right => {
      1u64
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.rho_try
// Variant: uncurried
pub fn rho_try_1(n: u64, c: u64) -> u64 {
  rho_try(n, c, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.rho_try (local: rho_try)
// Variant: uncurried, lifted
pub fn rho_try(n: u64, c: u64, _H: ()) -> u64 {
  let v11 = ltb(c, __rocq_global_1389);
  match bdec(v11) {
    sumbool::left => {
      let g = rho_loop_1(n, c, 2u64, 2u64, 1u64, 0u64, 1u64, 0u64, 1048576u64);
      let v69 = andb(ltb(1u64, g), ltb(g, n));
      let v83 = eqb(mod_(n, g), 0u64);
      match andb(v69, v83) {
        true => {
          g
        },
        false => {
          rho_try(n, add(c, 1u64), ())
        },
      }
    },
    sumbool::right => {
      0u64
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.certify
// Variant: borrowed, uncurried
pub fn certify_1(pr: &Rc<Array<u64>>, np: u64, n: u64) -> cres {
  let np_1 = np;
  let n_1 = n;
  certify(pr, np_1, n_1, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.certify (local: certify)
// Variant: borrowed, uncurried, lifted
pub fn certify(pr: &Rc<Array<u64>>, np: u64, n: u64, _H: ()) -> cres {
  let np_1 = np;
  let n_1 = n;
  let m = sub(n_1, 1u64);
  let v33 = td_cert_1(pr, np_1, 0u64, n_1, m, 1u64, m);
  match v33 {
    (v35, v37) => {
      match v35 {
        (v40, v42) => {
          match v40 {
            bres::BFound => {
              let v52 = div(n_1, v42);
              match ltb(v52, v42) {
                true => {
                  cres::CPrime
                },
                false => {
                  match leb(v37, 1u64) {
                    true => {
                      cres::CFail
                    },
                    false => {
                      match leb(v37, __rocq_global_921) {
                        true => {
                          base_res(find_base_1(n_1, m, v37, 2u64))
                        },
                        false => {
                          match mr_comp(v37) {
                            true => {
                              let g = rho_try_1(v37, 1u64);
                              let v134 = andb(ltb(1u64, g), ltb(g, v37));
                              let v148 = eqb(mod_(v37, g), 0u64);
                              match andb(v134, v148) {
                                true => {
                                  match find_base_1(n_1, m, g, 2u64) {
                                    bres::BFound => {
                                      let F_ = mul(v42, g);
                                      let v181 = div(n_1, F_);
                                      match ltb(v181, F_) {
                                        true => {
                                          cres::CPrime
                                        },
                                        false => {
                                          base_res(find_base_1(n_1, m, div(v37, g), 2u64))
                                        },
                                      }
                                    },
                                    bres::BComp => {
                                      cres::CComp
                                    },
                                    bres::BFail => {
                                      cres::CFail
                                    },
                                  }
                                },
                                false => {
                                  cres::CFail
                                },
                              }
                            },
                            false => {
                              let v243 = ltb(v37, n_1);
                              match bdec(v243) {
                                sumbool::left => {
                                  match certify(pr, np_1, v37, ()) {
                                    cres::CPrime => {
                                      base_res(find_base_1(n_1, m, v37, 2u64))
                                    },
                                    cres::CComp => {
                                      cres::CFail
                                    },
                                    cres::CFail => {
                                      cres::CFail
                                    },
                                  }
                                },
                                sumbool::right => {
                                  cres::CFail
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
            },
            bres::BComp => {
              cres::CComp
            },
            bres::BFail => {
              cres::CFail
            },
          }
        },
      }
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.td_loop
// Variant: uncurried
pub fn td_loop_1(n: u64, d: u64) -> bool {
  td_loop(n, d, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.td_loop (local: td_loop)
// Variant: uncurried, lifted
pub fn td_loop(n: u64, d: u64, _H: ()) -> bool {
  let v10 = ltb(d, n);
  match bdec(v10) {
    sumbool::left => {
      let v21 = mul(d, d);
      match leb(v21, n) {
        true => {
          let v33 = mod_(n, d);
          match eqb(v33, 0u64) {
            true => {
              false
            },
            false => {
              td_loop(n, add(d, 1u64), ())
            },
          }
        },
        false => {
          true
        },
      }
    },
    sumbool::right => {
      true
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.classify
// Variant: borrowed, uncurried
pub fn classify(pr: &Rc<Array<u64>>, np: u64, x: u64) -> kind {
  let np_1 = np;
  let x_1 = x;
  match leb(x_1, __rocq_global_921) {
    true => {
      kind::KPrime
    },
    false => {
      let s = isqrt(x_1);
      let v28 = mul(s, s);
      match eqb(v28, x_1) {
        true => {
          kind::KSquare
        },
        false => {
          match mr_comp(x_1) {
            true => {
              kind::KSemi
            },
            false => {
              match certify_1(pr, np_1, x_1) {
                cres::CPrime => {
                  kind::KPrime
                },
                cres::CComp => {
                  kind::KSemi
                },
                cres::CFail => {
                  match td_loop_1(x_1, 2u64) {
                    true => {
                      kind::KPrime
                    },
                    false => {
                      kind::KSemi
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

// Rocq: Atrivialpursuit.atrivialpursuit_implem.contrib
// Variant: borrowed, uncurried
pub fn contrib(pr: &Rc<Array<u64>>, np: u64, x: u64, e: u64, P: u64) -> u64 {
  let np_1 = np;
  let x_1 = x;
  let e_1 = e;
  let P_1 = P;
  match classify(pr, np_1, x_1) {
    kind::KPrime => {
      fmod(e_1, P_1)
    },
    kind::KSquare => {
      fmod(add(e_1, e_1), P_1)
    },
    kind::KSemi => {
      let f = fmod(e_1, P_1);
      mulmod(f, f, __rocq_global_525)
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.peel
// Variant: uncurried
pub fn peel_1(pr: Rc<Array<u64>>, np: u64, aG: Rc<Array<u64>>, aL: Rc<Array<u64>>, nG: u64, nL: u64, sel: bool, i: u64, P: u64, acc: u64) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  peel(pr, np, aG, aL, nG, nL, sel, i, P, acc, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.peel (local: peel)
// Variant: uncurried, lifted
pub fn peel(pr: Rc<Array<u64>>, np: u64, aG: Rc<Array<u64>>, aL: Rc<Array<u64>>, nG: u64, nL: u64, sel: bool, i: u64, P: u64, acc: u64, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let v16 = Rc::clone(&aG);
  let v19 = Rc::clone(&aL);
  let c = sel_get(sel, v16, v19, i);
  let v32 = ltb(1u64, c);
  match bdec(v32) {
    sumbool::left => {
      let v44 = Rc::clone(&aG);
      let v51 = refine_1(v44, nG, 0u64, c);
      let v54 = Rc::clone(&aL);
      let x = refine_1(v54, nL, 0u64, v51);
      let v71 = ltb(1u64, x);
      match bdec(v71) {
        sumbool::left => {
          let rG = divpass_1(x, aG, nG, 0u64, 0u64);
          let rL = divpass_1(x, aL, nL, 0u64, 0u64);
          let v110 = Clone::clone(&rG);
          let v112 = snd::<Rc<Array<u64>>, u64>(v110);
          let v115 = Clone::clone(&rL);
          let v117 = snd::<Rc<Array<u64>>, u64>(v115);
          let v120 = Rc::clone(&pr);
          let v127 = {
            let __anf_capture_130 = np;
            let __anf_capture_132 = x;
            let __anf_capture_134 = P;
            move |e: u64| -> u64 {
              let pr = &v120;
              let v138 = Clone::clone(&__anf_capture_130);
              let v140 = Clone::clone(&__anf_capture_132);
              let v144 = Clone::clone(&__anf_capture_134);
              contrib(pr, v138, v140, e, v144)
            }
          };
          let v150: Rc<dyn Fn(u64) -> u64> = Rc::new(v127);
          let acc_ = step_acc(acc, v112, v117, v150);
          let v166 = Clone::clone(&rG);
          let v168 = fst::<Rc<Array<u64>>, u64>(v166);
          let v171 = Clone::clone(&rL);
          let v173 = fst::<Rc<Array<u64>>, u64>(v171);
          let v188 = ltb(sel_get(sel, v168, v173, i), c);
          match bdec(v188) {
            sumbool::left => {
              let v195 = fst::<Rc<Array<u64>>, u64>(rG);
              let v199 = fst::<Rc<Array<u64>>, u64>(rL);
              peel(pr, np, v195, v199, nG, nL, sel, i, P, acc_, ())
            },
            sumbool::right => {
              std::mem::drop(pr);
              let v231 = fst::<Rc<Array<u64>>, u64>(rG);
              let v235 = fst::<Rc<Array<u64>>, u64>(rL);
              ((v231, v235), acc_)
            },
          }
        },
        sumbool::right => {
          std::mem::drop(pr);
          ((aG, aL), acc)
        },
      }
    },
    sumbool::right => {
      std::mem::drop(pr);
      ((aG, aL), acc)
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.ph2
// Variant: uncurried
pub fn ph2_1(pr: Rc<Array<u64>>, np: u64, aG: Rc<Array<u64>>, aL: Rc<Array<u64>>, nG: u64, nL: u64, sel: bool, n: u64, i: u64, P: u64, acc: u64) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  ph2(pr, np, aG, aL, nG, nL, sel, n, i, P, acc, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.ph2 (local: ph2)
// Variant: uncurried, lifted
pub fn ph2(pr: Rc<Array<u64>>, np: u64, aG: Rc<Array<u64>>, aL: Rc<Array<u64>>, nG: u64, nL: u64, sel: bool, n: u64, i: u64, P: u64, acc: u64, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let v19 = ltb(i, n);
  match bdec(v19) {
    sumbool::left => {
      let v26 = Rc::clone(&pr);
      let r = peel_1(v26, np, aG, aL, nG, nL, sel, i, P, acc);
      let v49 = Clone::clone(&r);
      let v54 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(v49));
      let v58 = Clone::clone(&r);
      let v63 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(v58));
      ph2(pr, np, v54, v63, nG, nL, sel, n, add(i, 1u64), P, snd::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r), ())
    },
    sumbool::right => {
      std::mem::drop(pr);
      ((aG, aL), acc)
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.atp_impl
// Variant: uncurried
pub fn atp_impl(p: u64, x: Rc<Array<u64>>, y: Rc<Array<u64>>) -> u64 {
  let s = sieve(());
  let v11 = Clone::clone(&s);
  let pr = fst::<Rc<Array<u64>>, u64>(v11);
  let np = snd::<Rc<Array<u64>>, u64>(s);
  let v18 = &x;
  let nG = rocq_array::length::<u64>(&v18);
  let v20 = &y;
  let nL = rocq_array::length::<u64>(&v20);
  let v24 = 0u64;
  let v25 = &x;
  let v26 = rocq_array::copy::<u64>(&v25);
  std::mem::drop(x);
  let v27 = &y;
  let v28 = rocq_array::copy::<u64>(&v27);
  std::mem::drop(y);
  let v33 = Rc::clone(&pr);
  let r1 = ph1_1(v33, np, v24, v26, v28, nG, nL, p, 1u64);
  let v55 = Clone::clone(&r1);
  let v60 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(v55));
  let v64 = Clone::clone(&r1);
  let v69 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(v64));
  let v77 = snd::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r1);
  let v80 = Rc::clone(&pr);
  let r2 = ph2_1(v80, np, v60, v69, nG, nL, false, nG, 0u64, p, v77);
  let v106 = Clone::clone(&r2);
  let v111 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(v106));
  let v115 = Clone::clone(&r2);
  let v120 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(v115));
  let r3 = ph2_1(pr, np, v111, v120, nG, nL, true, nL, 0u64, p, snd::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r2));
  snd::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r3)
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.atp_impl
pub fn atp_impl_curried(p: u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> {
  let v3 = {
    move |x: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> u64> {
      let p = &p;
      let v8 = Clone::clone(p);
      let v11 = {
        move |y: Rc<Array<u64>>| -> u64 {
          let v19 = Clone::clone(&v8);
          let v21 = Rc::clone(&x);
          atp_impl(v19, v21, y)
        }
      };
      let v27: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = Rc::new(v11);
      v27
    }
  };
  let v31: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> = Rc::new(v3);
  v31
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> {
  let v0: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> = __rocq_global_2109.with(Clone::clone);
  v0
}
const __rocq_global_43: u64 = 1000000u64;
const __rocq_global_525: u64 = 1000000007u64;
const __rocq_global_921: u64 = 1000000000000u64;
const __rocq_global_1183: u64 = 1000u64;
const __rocq_global_1389: u64 = 40u64;
std::thread_local! { static __rocq_global_2109: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> = atrivialpursuit(); }
std::thread_local! { static __rocq_global_2112: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>> = atrivialpursuit_curried(); }