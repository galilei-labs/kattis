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
  if b {
    sumbool::left
  } else {
    sumbool::right
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
  if b1 {
    b2
  } else {
    false
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
  let tmp = ltb(j, __rocq_global_43);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::set::<bool>(m, j, true);
      let tmp_2 = add(j, i);
      mark_loop(tmp_1, i, tmp_2, (), ())
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
  let tmp = ltb(i, __rocq_global_43);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<bool>(&m, i);
      if tmp_1 {
        sieve_loop(m, pr, np, add(i, 1u64), ())
      } else {
        let tmp_2 = andb(ltb(0u64, i), ltb(i, __rocq_global_43));
        match bdec(tmp_2) {
          sumbool::left => {
            let tmp_3 = add(i, i);
            let tmp_4 = mark_loop_1(m, i, tmp_3);
            let tmp_5 = rocq_array::set::<u64>(pr, np, i);
            sieve_loop(tmp_4, tmp_5, add(np, 1u64), add(i, 1u64), ())
          },
          sumbool::right => {
            std::mem::drop(m);
            (pr, np)
          },
        }
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
  let tmp = rocq_array::make::<bool>(__rocq_global_43, false);
  let tmp_1 = rocq_array::make::<u64>(__rocq_global_43, 0u64);
  sieve_loop_1(tmp, tmp_1, 0u64, 2u64)
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
  let tmp = ltb(0u64, c);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = mod_(c, x);
      if eqb(tmp_1, 0u64) {
        let tmp_2 = div(c, x);
        divfull(x, tmp_2, add(k, 1u64), (), ())
      } else {
        (c, k)
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
  let tmp = ltb(j, n);
  match bdec(tmp) {
    sumbool::left => {
      let c = rocq_array::get::<u64>(&a, j);
      let tmp_1 = mod_(c, x);
      if eqb(tmp_1, 0u64) {
        let ck = divfull_1(x, c, 0u64);
        let ck_clone = Clone::clone(&ck);
        let tmp_2 = rocq_array::set::<u64>(a, j, fst::<u64, u64>(ck_clone));
        divpass(x, (), tmp_2, n, add(j, 1u64), add(e, snd::<u64, u64>(ck)), ())
      } else {
        divpass(x, (), a, n, add(j, 1u64), e, ())
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
  let tmp = mulc(a, b);
  match tmp {
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
  if eqb(eg, el) {
    std::mem::drop(f);
    acc
  } else {
    if ltb(el, eg) {
      std::mem::drop(f);
      0u64
    } else {
      let tmp = sub(el, eg);
      let f_ref: &Rc<dyn Fn(u64) -> u64> = &f;
      let tmp_1 = f_ref(tmp);
      std::mem::drop(f);
      mulmod(acc, tmp_1, __rocq_global_525)
    }
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
  let tmp = ltb(0u64, e);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = mulmod(b, b, n);
      let tmp_2 = lsr(e, 1u64);
      let tmp_3 = land(e, 1u64);
      let tmp_4 = 1u64;
      let tmp_5 = if eqb(tmp_3, tmp_4) {
        mulmod(r, b, n)
      } else {
        r
      };
      pow_loop(tmp_1, tmp_2, tmp_5, n, ())
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
  let tmp = add(a, mul(2u64, sub(__rocq_global_525, b)));
  mod_(add(tmp, c), __rocq_global_525)
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.ph1
// Variant: uncurried
pub fn ph1_1(pr: Rc<Array<u64>>, np: u64, k: u64, aG: Rc<Array<u64>>, aL: Rc<Array<u64>>, nG: u64, nL: u64, P: u64, acc: u64) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  ph1(pr, np, k, aG, aL, nG, nL, P, acc, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.ph1 (local: ph1)
// Variant: uncurried, lifted
pub fn ph1(pr: Rc<Array<u64>>, np: u64, k: u64, aG: Rc<Array<u64>>, aL: Rc<Array<u64>>, nG: u64, nL: u64, P: u64, acc: u64, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let tmp = ltb(k, np);
  match bdec(tmp) {
    sumbool::left => {
      let p = rocq_array::get::<u64>(&pr, k);
      let tmp_1 = ltb(1u64, p);
      match bdec(tmp_1) {
        sumbool::left => {
          let rG = divpass_1(p, aG, nG, 0u64, 0u64);
          let rL = divpass_1(p, aL, nL, 0u64, 0u64);
          let tmp_2 = add(k, 1u64);
          let rG_clone = Clone::clone(&rG);
          let tmp_3 = fst::<Rc<Array<u64>>, u64>(rG_clone);
          let rL_clone = Clone::clone(&rL);
          let tmp_4 = fst::<Rc<Array<u64>>, u64>(rL_clone);
          let tmp_5 = snd::<Rc<Array<u64>>, u64>(rG);
          let tmp_6 = snd::<Rc<Array<u64>>, u64>(rL);
          let callback: Rc<dyn Fn(u64) -> u64> = Rc::new({
            let __anf_capture_100 = P;
            move |e: u64| -> u64 {
              let tmp_7 = Clone::clone(&__anf_capture_100);
              fmod(e, tmp_7)
            }
          });
          ph1(pr, np, tmp_2, tmp_3, tmp_4, nG, nL, P, step_acc(acc, tmp_5, tmp_6, callback), ())
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
  if sel {
    std::mem::drop(aG);
    let tmp = rocq_array::get::<u64>(&aL, i);
    std::mem::drop(aL);
    tmp
  } else {
    std::mem::drop(aL);
    let tmp_1 = rocq_array::get::<u64>(&aG, i);
    std::mem::drop(aG);
    tmp_1
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
  let tmp = ltb(0u64, b);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = mod_(a, b);
      gcd_loop(b, tmp_1, ())
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
  let tmp = ltb(j, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&a, j);
      let d = igcd(x, tmp_1);
      let tmp_2 = add(j, 1u64);
      let tmp_3 = ltb(1u64, d);
      let tmp_4 = ltb(d, x);
      let tmp_5 = if andb(tmp_3, tmp_4) {
        d
      } else {
        x
      };
      refine(a, n, tmp_2, tmp_5, ())
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
  let tmp = ltb(1u64, w);
  match bdec(tmp) {
    sumbool::left => {
      let b = lsr(w, 1u64);
      let t = add(s, b);
      let tmp_1 = mul(t, t);
      if leb(tmp_1, x) {
        isq_loop(x, t, sub(w, b), ())
      } else {
        isq_loop(x, s, b, ())
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
  if b1 {
    true
  } else {
    b2
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
  let tmp = andb(ltb(0u64, d), eqb(land(d, 1u64), 0u64));
  match bdec(tmp) {
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
  let tmp = ltb(i, s);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = sub(n, 1u64);
      if eqb(y, tmp_1) {
        false
      } else {
        let y_ = mulmod(y, y, n);
        if eqb(y_, 1u64) {
          true
        } else {
          mr_loop(n, y_, add(i, 1u64), s, ())
        }
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
  let tmp = strip2_1(sub(n, 1u64), 0u64);
  match tmp {
    (v19, v21) => {
      let y = powmod(a, v19, n);
      if eqb(y, 1u64) {
        false
      } else {
        mr_loop_1(n, y, 0u64, v21)
      }
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.mr_comp
pub fn mr_comp(n: u64) -> bool {
  let tmp = orb(mr_base(n, 2u64), mr_base(n, 3u64));
  let tmp_1 = orb(tmp, mr_base(n, 5u64));
  let tmp_2 = orb(tmp_1, mr_base(n, 7u64));
  let tmp_3 = orb(tmp_2, mr_base(n, 11u64));
  let tmp_4 = orb(tmp_3, mr_base(n, 13u64));
  let tmp_5 = orb(tmp_4, mr_base(n, 17u64));
  let tmp_6 = orb(tmp_5, mr_base(n, 19u64));
  let tmp_7 = orb(tmp_6, mr_base(n, 23u64));
  let tmp_8 = orb(tmp_7, mr_base(n, 29u64));
  let tmp_9 = orb(tmp_8, mr_base(n, 31u64));
  orb(tmp_9, mr_base(n, 37u64))
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  if b {
    false
  } else {
    true
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
  let tmp = ltb(a, __rocq_global_1183);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = eqb(powmod(a, m, n), 1u64);
      if negb(tmp_1) {
        bres::BComp
      } else {
        let u = powmod(a, div(m, q), n);
        let g = igcd(mod_(sub(add(u, n), 1u64), n), n);
        if eqb(g, 1u64) {
          bres::BFound
        } else {
          if ltb(g, n) {
            bres::BComp
          } else {
            find_base(n, m, q, add(a, 1u64), ())
          }
        }
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
  let tmp = ltb(k_1, np_1);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = div(n_1, F_1);
      if ltb(tmp_1, F_1) {
        ((bres::BFound, F_1), R_1)
      } else {
        let q = rocq_array::get::<u64>(pr, k_1);
        let tmp_2 = mod_(R_1, q);
        if eqb(tmp_2, 0u64) {
          let tmp_3 = ltb(1u64, q);
          match bdec(tmp_3) {
            sumbool::left => {
              let Rk = divfull_1(q, R_1, 0u64);
              match find_base_1(n_1, m_1, q, 2u64) {
                bres::BFound => {
                  let tmp_4 = add(k_1, 1u64);
                  let Rk_clone = Clone::clone(&Rk);
                  td_cert(pr, np_1, tmp_4, n_1, m_1, mul(F_1, div(R_1, fst::<u64, u64>(Rk_clone))), fst::<u64, u64>(Rk), ())
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
        } else {
          td_cert(pr, np_1, add(k_1, 1u64), n_1, m_1, F_1, R_1, ())
        }
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
  let tmp = ltb(0u64, budget);
  match bdec(tmp) {
    sumbool::left => {
      let y_ = mod_(add(mulmod(y, y, n), c), n);
      let diff = if ltb(x, y_) {
        sub(y_, x)
      } else {
        sub(x, y_)
      };
      let q_ = mulmod(q, diff, n);
      let b_ = add(b, 1u64);
      let tmp_1 = 128u64;
      let g = if eqb(b_, tmp_1) {
        igcd(q_, n)
      } else {
        1u64
      };
      let tmp_2 = eqb(g, 1u64);
      if negb(tmp_2) {
        g
      } else {
        let tmp_3 = 128u64;
        let b__ = if eqb(b_, tmp_3) {
          0u64
        } else {
          b_
        };
        let j_ = add(j, 1u64);
        if eqb(j_, r) {
          rho_loop(n, c, y_, y_, q_, 0u64, add(r, r), b__, sub(budget, 1u64), ())
        } else {
          rho_loop(n, c, x, y_, q_, j_, r, b__, sub(budget, 1u64), ())
        }
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
  let tmp = ltb(c, __rocq_global_1389);
  match bdec(tmp) {
    sumbool::left => {
      let g = rho_loop_1(n, c, 2u64, 2u64, 1u64, 0u64, 1u64, 0u64, 1048576u64);
      let tmp_1 = andb(ltb(1u64, g), ltb(g, n));
      let tmp_2 = eqb(mod_(n, g), 0u64);
      if andb(tmp_1, tmp_2) {
        g
      } else {
        rho_try(n, add(c, 1u64), ())
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
  let tmp = td_cert_1(pr, np_1, 0u64, n_1, m, 1u64, m);
  match tmp {
    (v35, v37) => {
      match v35 {
        (v40, v42) => {
          match v40 {
            bres::BFound => {
              let tmp_1 = div(n_1, v42);
              if ltb(tmp_1, v42) {
                cres::CPrime
              } else {
                if leb(v37, 1u64) {
                  cres::CFail
                } else {
                  if leb(v37, __rocq_global_921) {
                    base_res(find_base_1(n_1, m, v37, 2u64))
                  } else {
                    if mr_comp(v37) {
                      let g = rho_try_1(v37, 1u64);
                      let tmp_2 = andb(ltb(1u64, g), ltb(g, v37));
                      let tmp_3 = eqb(mod_(v37, g), 0u64);
                      if andb(tmp_2, tmp_3) {
                        match find_base_1(n_1, m, g, 2u64) {
                          bres::BFound => {
                            let F_ = mul(v42, g);
                            let tmp_4 = div(n_1, F_);
                            if ltb(tmp_4, F_) {
                              cres::CPrime
                            } else {
                              base_res(find_base_1(n_1, m, div(v37, g), 2u64))
                            }
                          },
                          bres::BComp => {
                            cres::CComp
                          },
                          bres::BFail => {
                            cres::CFail
                          },
                        }
                      } else {
                        cres::CFail
                      }
                    } else {
                      let tmp_5 = ltb(v37, n_1);
                      match bdec(tmp_5) {
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
                    }
                  }
                }
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
  let tmp = ltb(d, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = mul(d, d);
      if leb(tmp_1, n) {
        let tmp_2 = mod_(n, d);
        if eqb(tmp_2, 0u64) {
          false
        } else {
          td_loop(n, add(d, 1u64), ())
        }
      } else {
        true
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
  if leb(x_1, __rocq_global_921) {
    kind::KPrime
  } else {
    let s = isqrt(x_1);
    let tmp = mul(s, s);
    if eqb(tmp, x_1) {
      kind::KSquare
    } else {
      if mr_comp(x_1) {
        kind::KSemi
      } else {
        match certify_1(pr, np_1, x_1) {
          cres::CPrime => {
            kind::KPrime
          },
          cres::CComp => {
            kind::KSemi
          },
          cres::CFail => {
            if td_loop_1(x_1, 2u64) {
              kind::KPrime
            } else {
              kind::KSemi
            }
          },
        }
      }
    }
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
  let aG_clone = Rc::clone(&aG);
  let aL_clone = Rc::clone(&aL);
  let c = sel_get(sel, aG_clone, aL_clone, i);
  let tmp = ltb(1u64, c);
  match bdec(tmp) {
    sumbool::left => {
      let aG_clone_1 = Rc::clone(&aG);
      let tmp_1 = refine_1(aG_clone_1, nG, 0u64, c);
      let aL_clone_1 = Rc::clone(&aL);
      let x = refine_1(aL_clone_1, nL, 0u64, tmp_1);
      let tmp_2 = ltb(1u64, x);
      match bdec(tmp_2) {
        sumbool::left => {
          let rG = divpass_1(x, aG, nG, 0u64, 0u64);
          let rL = divpass_1(x, aL, nL, 0u64, 0u64);
          let rG_clone = Clone::clone(&rG);
          let tmp_3 = snd::<Rc<Array<u64>>, u64>(rG_clone);
          let rL_clone = Clone::clone(&rL);
          let tmp_4 = snd::<Rc<Array<u64>>, u64>(rL_clone);
          let pr_clone = Rc::clone(&pr);
          let callback: Rc<dyn Fn(u64) -> u64> = Rc::new({
            let __anf_capture_130 = np;
            let __anf_capture_132 = x;
            let __anf_capture_134 = P;
            move |e: u64| -> u64 {
              let pr = &pr_clone;
              let tmp_5 = Clone::clone(&__anf_capture_130);
              let tmp_6 = Clone::clone(&__anf_capture_132);
              let tmp_7 = Clone::clone(&__anf_capture_134);
              contrib(pr, tmp_5, tmp_6, e, tmp_7)
            }
          });
          let acc_ = step_acc(acc, tmp_3, tmp_4, callback);
          let rG_clone_1 = Clone::clone(&rG);
          let tmp_8 = fst::<Rc<Array<u64>>, u64>(rG_clone_1);
          let rL_clone_1 = Clone::clone(&rL);
          let tmp_9 = fst::<Rc<Array<u64>>, u64>(rL_clone_1);
          let tmp_10 = ltb(sel_get(sel, tmp_8, tmp_9, i), c);
          match bdec(tmp_10) {
            sumbool::left => {
              let tmp_11 = fst::<Rc<Array<u64>>, u64>(rG);
              let tmp_12 = fst::<Rc<Array<u64>>, u64>(rL);
              peel(pr, np, tmp_11, tmp_12, nG, nL, sel, i, P, acc_, ())
            },
            sumbool::right => {
              std::mem::drop(pr);
              let tmp_13 = fst::<Rc<Array<u64>>, u64>(rG);
              let tmp_14 = fst::<Rc<Array<u64>>, u64>(rL);
              ((tmp_13, tmp_14), acc_)
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
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let pr_clone = Rc::clone(&pr);
      let r = peel_1(pr_clone, np, aG, aL, nG, nL, sel, i, P, acc);
      let r_clone = Clone::clone(&r);
      let tmp_1 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r_clone));
      let r_clone_1 = Clone::clone(&r);
      let tmp_2 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r_clone_1));
      ph2(pr, np, tmp_1, tmp_2, nG, nL, sel, n, add(i, 1u64), P, snd::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r), ())
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
  let s_clone = Clone::clone(&s);
  let pr = fst::<Rc<Array<u64>>, u64>(s_clone);
  let np = snd::<Rc<Array<u64>>, u64>(s);
  let nG = rocq_array::length::<u64>(&x);
  let nL = rocq_array::length::<u64>(&y);
  let tmp = 0u64;
  let tmp_1 = rocq_array::copy::<u64>(&x);
  std::mem::drop(x);
  let tmp_2 = rocq_array::copy::<u64>(&y);
  std::mem::drop(y);
  let pr_clone = Rc::clone(&pr);
  let r1 = ph1_1(pr_clone, np, tmp, tmp_1, tmp_2, nG, nL, p, 1u64);
  let r1_clone = Clone::clone(&r1);
  let tmp_3 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r1_clone));
  let r1_clone_1 = Clone::clone(&r1);
  let tmp_4 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r1_clone_1));
  let tmp_5 = snd::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r1);
  let pr_clone_1 = Rc::clone(&pr);
  let r2 = ph2_1(pr_clone_1, np, tmp_3, tmp_4, nG, nL, false, nG, 0u64, p, tmp_5);
  let r2_clone = Clone::clone(&r2);
  let tmp_6 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r2_clone));
  let r2_clone_1 = Clone::clone(&r2);
  let tmp_7 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r2_clone_1));
  let r3 = ph2_1(pr, np, tmp_6, tmp_7, nG, nL, true, nL, 0u64, p, snd::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r2));
  snd::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r3)
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
const __rocq_global_43: u64 = 1000000u64;
const __rocq_global_525: u64 = 1000000007u64;
const __rocq_global_921: u64 = 1000000000000u64;
const __rocq_global_1183: u64 = 1000u64;
const __rocq_global_1389: u64 = 40u64;