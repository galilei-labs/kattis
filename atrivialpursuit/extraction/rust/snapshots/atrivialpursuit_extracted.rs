#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

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

pub type uint = Int63;

// Rocq: Atrivialpursuit.atrivialpursuit_implem.LIM
pub fn LIM() -> Int63 {
  int63!(1000000)
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.MODP
pub fn MODP() -> Int63 {
  int63!(1000000007)
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.T12
pub fn T12() -> Int63 {
  int63!(1000000000000)
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.ALIM
pub fn ALIM() -> Int63 {
  int63!(1000)
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.RHOC
pub fn RHOC() -> Int63 {
  int63!(40)
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
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
pub fn mark_loop_1(m: Array<bool>, i: Int63, j: Int63) -> Array<bool> {
  mark_loop(m, i, j, (), ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.mark_loop (local: mark_loop)
// Variant: uncurried, lifted
pub fn mark_loop(m: Array<bool>, i: Int63, j: Int63, _Hi: (), _H: ()) -> Array<bool> {
  let tmp = j < __rocq_global_43;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = m.set(j, true);
      let tmp_2 = j + i;
      mark_loop(tmp_1, i, tmp_2, (), ())
    },
    sumbool::right => {
      m
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.sieve_loop
// Variant: uncurried
pub fn sieve_loop_1(m: Array<bool>, pr: Array<Int63>, np: Int63, i: Int63) -> (Array<Int63>, Int63) {
  sieve_loop(m, pr, np, i, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.sieve_loop (local: sieve_loop)
// Variant: uncurried, lifted
pub fn sieve_loop(m: Array<bool>, pr: Array<Int63>, np: Int63, i: Int63, _H: ()) -> (Array<Int63>, Int63) {
  let tmp = i < __rocq_global_43;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = m.get_cloned(i);
      if tmp_1 {
        sieve_loop(m, pr, np, i + int63!(1), ())
      } else {
        let tmp_2 = andb(int63!(0) < i, i < __rocq_global_43);
        match bdec(tmp_2) {
          sumbool::left => {
            let tmp_3 = i + i;
            sieve_loop(mark_loop_1(m, i, tmp_3), pr.set(np, i), np + int63!(1), i + int63!(1), ())
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
pub fn sieve(_v0: ()) -> (Array<Int63>, Int63) {
  sieve_loop_1(Array::<bool>::make(__rocq_global_43, false), Array::<Int63>::make(__rocq_global_43, int63!(0)), int63!(0), int63!(2))
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

// Rocq: Atrivialpursuit.atrivialpursuit_implem.divfull
// Variant: uncurried
pub fn divfull_1(x: Int63, c: Int63, k: Int63) -> (Int63, Int63) {
  divfull(x, c, k, (), ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.divfull (local: divfull)
// Variant: uncurried, lifted
pub fn divfull(x: Int63, c: Int63, k: Int63, _Hx: (), _H: ()) -> (Int63, Int63) {
  let tmp = int63!(0) < c;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = c % x;
      if tmp_1 == int63!(0) {
        let tmp_2 = c / x;
        divfull(x, tmp_2, k + int63!(1), (), ())
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
pub fn divpass_1(x: Int63, a_1: Array<Int63>, n: Int63, j: Int63, e: Int63) -> (Array<Int63>, Int63) {
  divpass(x, (), a_1, n, j, e, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.divpass (local: divpass)
// Variant: uncurried, lifted
pub fn divpass(x: Int63, _Hx: (), a_1: Array<Int63>, n: Int63, j: Int63, e: Int63, _H: ()) -> (Array<Int63>, Int63) {
  let tmp = j < n;
  match bdec(tmp) {
    sumbool::left => {
      let c = a_1.get_cloned(j);
      let tmp_1 = c % x;
      if tmp_1 == int63!(0) {
        let ck = divfull_1(x, c, int63!(0));
        let ck_clone = Clone::clone(&ck);
        divpass(x, (), a_1.set(j, fst::<Int63, Int63>(ck_clone)), n, j + int63!(1), e + snd::<Int63, Int63>(ck), ())
      } else {
        divpass(x, (), a_1, n, j + int63!(1), e, ())
      }
    },
    sumbool::right => {
      (a_1, e)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mulc
// Variant: uncurried
pub fn mulc(x: Int63, x_1: Int63) -> (Int63, Int63) {
  (x.mulc_high(x_1), x.mulc_low(x_1))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.diveucl_21
// Variant: uncurried
pub fn diveucl_21(x: Int63, x_1: Int63, x_2: Int63) -> (Int63, Int63) {
  (x.diveucl_21_quotient(x_1, x_2), x.diveucl_21_remainder(x_1, x_2))
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.mulmod
// Variant: uncurried
pub fn mulmod(a_1: Int63, b_1: Int63, n: Int63) -> Int63 {
  let tmp = mulc(a_1, b_1);
  match tmp {
    (v10, v12) => {
      snd::<Int63, Int63>(diveucl_21(v10, v12, n))
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.step_acc
// Variant: uncurried
pub fn step_acc(acc: Int63, eg: Int63, el: Int63, f: Rc<dyn Fn(Int63) -> Int63>) -> Int63 {
  if eg == el {
    std::mem::drop(f);
    acc
  } else {
    if el < eg {
      std::mem::drop(f);
      int63!(0)
    } else {
      let tmp = el - eg;
      let f_ref: &Rc<dyn Fn(Int63) -> Int63> = &f;
      let tmp_1 = f_ref(tmp);
      std::mem::drop(f);
      mulmod(acc, tmp_1, __rocq_global_525)
    }
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.pow_loop
// Variant: uncurried
pub fn pow_loop_1(b_1: Int63, e: Int63, r: Int63, n: Int63) -> Int63 {
  pow_loop(b_1, e, r, n, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.pow_loop (local: pow_loop)
// Variant: uncurried, lifted
pub fn pow_loop(b_1: Int63, e: Int63, r: Int63, n: Int63, _H: ()) -> Int63 {
  let tmp = int63!(0) < e;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = mulmod(b_1, b_1, n);
      let tmp_2 = e >> int63!(1);
      let tmp_3 = e & int63!(1);
      let tmp_4 = int63!(1);
      let tmp_5 = if tmp_3 == tmp_4 {
        mulmod(r, b_1, n)
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
pub fn powmod(b_1: Int63, e: Int63, n: Int63) -> Int63 {
  pow_loop_1(b_1 % n, e, int63!(1) % n, n)
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.fmod
// Variant: uncurried
pub fn fmod(e: Int63, P: Int63) -> Int63 {
  let a_1 = powmod(e + int63!(1), P, __rocq_global_525);
  let b_1 = powmod(e, P, __rocq_global_525);
  let c = powmod(e - int63!(1), P, __rocq_global_525);
  (a_1 + int63!(2) * (__rocq_global_525 - b_1) + c) % __rocq_global_525
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.ph1
// Variant: uncurried
pub fn ph1_1(pr: Array<Int63>, np: Int63, k: Int63, aG: Array<Int63>, aL: Array<Int63>, nG: Int63, nL: Int63, P: Int63, acc: Int63) -> ((Array<Int63>, Array<Int63>), Int63) {
  ph1(pr, np, k, aG, aL, nG, nL, P, acc, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.ph1 (local: ph1)
// Variant: uncurried, lifted
pub fn ph1(pr: Array<Int63>, np: Int63, k: Int63, aG: Array<Int63>, aL: Array<Int63>, nG: Int63, nL: Int63, P: Int63, acc: Int63, _H: ()) -> ((Array<Int63>, Array<Int63>), Int63) {
  let tmp = k < np;
  match bdec(tmp) {
    sumbool::left => {
      let p = pr.get_cloned(k);
      let tmp_1 = int63!(1) < p;
      match bdec(tmp_1) {
        sumbool::left => {
          let rG = divpass_1(p, aG, nG, int63!(0), int63!(0));
          let rL = divpass_1(p, aL, nL, int63!(0), int63!(0));
          let tmp_2 = k + int63!(1);
          let rG_clone = Clone::clone(&rG);
          let tmp_3 = fst::<Array<Int63>, Int63>(rG_clone);
          let rL_clone = Clone::clone(&rL);
          let tmp_4 = fst::<Array<Int63>, Int63>(rL_clone);
          let tmp_5 = snd::<Array<Int63>, Int63>(rG);
          let tmp_6 = snd::<Array<Int63>, Int63>(rL);
          let callback: Rc<dyn Fn(Int63) -> Int63> = Rc::new({
            let __anf_capture_100 = P;
            move |e: Int63| -> Int63 {
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
pub fn sel_get(sel: bool, aG: Array<Int63>, aL: Array<Int63>, i: Int63) -> Int63 {
  if sel {
    std::mem::drop(aG);
    let tmp = aL.get_cloned(i);
    std::mem::drop(aL);
    tmp
  } else {
    std::mem::drop(aL);
    let tmp_1 = aG.get_cloned(i);
    std::mem::drop(aG);
    tmp_1
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.gcd_loop
// Variant: uncurried
pub fn gcd_loop_1(a_1: Int63, b_1: Int63) -> Int63 {
  gcd_loop(a_1, b_1, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.gcd_loop (local: gcd_loop)
// Variant: uncurried, lifted
pub fn gcd_loop(a_1: Int63, b_1: Int63, _H: ()) -> Int63 {
  let tmp = int63!(0) < b_1;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = a_1 % b_1;
      gcd_loop(b_1, tmp_1, ())
    },
    sumbool::right => {
      a_1
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.igcd
// Variant: uncurried
pub fn igcd(a_1: Int63, b_1: Int63) -> Int63 {
  gcd_loop_1(a_1, b_1)
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.refine
// Variant: uncurried
pub fn refine_1(a_1: Array<Int63>, n: Int63, j: Int63, x: Int63) -> Int63 {
  refine(a_1, n, j, x, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.refine (local: refine)
// Variant: uncurried, lifted
pub fn refine(a_1: Array<Int63>, n: Int63, j: Int63, x: Int63, _H: ()) -> Int63 {
  let tmp = j < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = a_1.get_cloned(j);
      let d = igcd(x, tmp_1);
      let tmp_2 = j + int63!(1);
      let tmp_3 = int63!(1) < d;
      let tmp_4 = d < x;
      let tmp_5 = if andb(tmp_3, tmp_4) {
        d
      } else {
        x
      };
      refine(a_1, n, tmp_2, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(a_1);
      x
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.isq_loop
// Variant: uncurried
pub fn isq_loop_1(x: Int63, s: Int63, w: Int63) -> Int63 {
  isq_loop(x, s, w, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.isq_loop (local: isq_loop)
// Variant: uncurried, lifted
pub fn isq_loop(x: Int63, s: Int63, w: Int63, _H: ()) -> Int63 {
  let tmp = int63!(1) < w;
  match bdec(tmp) {
    sumbool::left => {
      let b_1 = w >> int63!(1);
      let t = s + b_1;
      let tmp_1 = t * t;
      if tmp_1 <= x {
        isq_loop(x, t, w - b_1, ())
      } else {
        isq_loop(x, s, b_1, ())
      }
    },
    sumbool::right => {
      s
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.isqrt
pub fn isqrt(x: Int63) -> Int63 {
  isq_loop_1(x, int63!(0), int63!(2147483648))
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
pub fn strip2_1(d: Int63, s: Int63) -> (Int63, Int63) {
  strip2(d, s, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.strip2 (local: strip2)
// Variant: uncurried, lifted
pub fn strip2(d: Int63, s: Int63, _H: ()) -> (Int63, Int63) {
  let tmp = andb(int63!(0) < d, d & int63!(1) == int63!(0));
  match bdec(tmp) {
    sumbool::left => {
      strip2(d >> int63!(1), s + int63!(1), ())
    },
    sumbool::right => {
      (d, s)
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.mr_loop
// Variant: uncurried
pub fn mr_loop_1(n: Int63, y: Int63, i: Int63, s: Int63) -> bool {
  mr_loop(n, y, i, s, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.mr_loop (local: mr_loop)
// Variant: uncurried, lifted
pub fn mr_loop(n: Int63, y: Int63, i: Int63, s: Int63, _H: ()) -> bool {
  let tmp = i < s;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = n - int63!(1);
      if y == tmp_1 {
        false
      } else {
        let y_ = mulmod(y, y, n);
        if y_ == int63!(1) {
          true
        } else {
          mr_loop(n, y_, i + int63!(1), s, ())
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
pub fn mr_base(n: Int63, a_1: Int63) -> bool {
  let tmp = strip2_1(n - int63!(1), int63!(0));
  match tmp {
    (v19, v21) => {
      let y = powmod(a_1, v19, n);
      if y == int63!(1) {
        false
      } else {
        mr_loop_1(n, y, int63!(0), v21)
      }
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.mr_comp
pub fn mr_comp(n: Int63) -> bool {
  let tmp = orb(mr_base(n, int63!(2)), mr_base(n, int63!(3)));
  let tmp_1 = orb(tmp, mr_base(n, int63!(5)));
  let tmp_2 = orb(tmp_1, mr_base(n, int63!(7)));
  let tmp_3 = orb(tmp_2, mr_base(n, int63!(11)));
  let tmp_4 = orb(tmp_3, mr_base(n, int63!(13)));
  let tmp_5 = orb(tmp_4, mr_base(n, int63!(17)));
  let tmp_6 = orb(tmp_5, mr_base(n, int63!(19)));
  let tmp_7 = orb(tmp_6, mr_base(n, int63!(23)));
  let tmp_8 = orb(tmp_7, mr_base(n, int63!(29)));
  let tmp_9 = orb(tmp_8, mr_base(n, int63!(31)));
  orb(tmp_9, mr_base(n, int63!(37)))
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b_1: bool) -> bool {
  if b_1 {
    false
  } else {
    true
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.find_base
// Variant: uncurried
pub fn find_base_1(n: Int63, m: Int63, q: Int63, a_1: Int63) -> bres {
  find_base(n, m, q, a_1, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.find_base (local: find_base)
// Variant: uncurried, lifted
pub fn find_base(n: Int63, m: Int63, q: Int63, a_1: Int63, _H: ()) -> bres {
  let tmp = a_1 < __rocq_global_1183;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = powmod(a_1, m, n) == int63!(1);
      if negb(tmp_1) {
        bres::BComp
      } else {
        let u = powmod(a_1, m / q, n);
        let g = igcd((u + n - int63!(1)) % n, n);
        if g == int63!(1) {
          bres::BFound
        } else {
          if g < n {
            bres::BComp
          } else {
            find_base(n, m, q, a_1 + int63!(1), ())
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
pub fn td_cert_1(pr: &Array<Int63>, np: Int63, k: Int63, n: Int63, m: Int63, F: Int63, R: Int63) -> ((bres, Int63), Int63) {
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
pub fn td_cert(pr: &Array<Int63>, np: Int63, k: Int63, n: Int63, m: Int63, F: Int63, R: Int63, _H: ()) -> ((bres, Int63), Int63) {
  let np_1 = np;
  let k_1 = k;
  let n_1 = n;
  let m_1 = m;
  let F_1 = F;
  let R_1 = R;
  let tmp = k_1 < np_1;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = n_1 / F_1;
      if tmp_1 < F_1 {
        ((bres::BFound, F_1), R_1)
      } else {
        let q = pr.get_cloned(k_1);
        let tmp_2 = R_1 % q;
        if tmp_2 == int63!(0) {
          let tmp_3 = int63!(1) < q;
          match bdec(tmp_3) {
            sumbool::left => {
              let Rk = divfull_1(q, R_1, int63!(0));
              match find_base_1(n_1, m_1, q, int63!(2)) {
                bres::BFound => {
                  let tmp_4 = k_1 + int63!(1);
                  let Rk_clone = Clone::clone(&Rk);
                  td_cert(pr, np_1, tmp_4, n_1, m_1, F_1 * (R_1 / fst::<Int63, Int63>(Rk_clone)), fst::<Int63, Int63>(Rk), ())
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
          td_cert(pr, np_1, k_1 + int63!(1), n_1, m_1, F_1, R_1, ())
        }
      }
    },
    sumbool::right => {
      ((bres::BFound, F_1), R_1)
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.base_res
pub fn base_res(b_1: bres) -> cres {
  match b_1 {
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
pub fn rho_loop_1(n: Int63, c: Int63, x: Int63, y: Int63, q: Int63, j: Int63, r: Int63, b_1: Int63, budget: Int63) -> Int63 {
  rho_loop(n, c, x, y, q, j, r, b_1, budget, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.rho_loop (local: rho_loop)
// Variant: uncurried, lifted
pub fn rho_loop(n: Int63, c: Int63, x: Int63, y: Int63, q: Int63, j: Int63, r: Int63, b_1: Int63, budget: Int63, _H: ()) -> Int63 {
  let tmp = int63!(0) < budget;
  match bdec(tmp) {
    sumbool::left => {
      let y_ = (mulmod(y, y, n) + c) % n;
      let diff = if x < y_ {
        y_ - x
      } else {
        x - y_
      };
      let q_ = mulmod(q, diff, n);
      let b_ = b_1 + int63!(1);
      let tmp_1 = int63!(128);
      let g = if b_ == tmp_1 {
        igcd(q_, n)
      } else {
        int63!(1)
      };
      let tmp_2 = g == int63!(1);
      if negb(tmp_2) {
        g
      } else {
        let tmp_3 = int63!(128);
        let b__ = if b_ == tmp_3 {
          int63!(0)
        } else {
          b_
        };
        let j_ = j + int63!(1);
        if j_ == r {
          rho_loop(n, c, y_, y_, q_, int63!(0), r + r, b__, budget - int63!(1), ())
        } else {
          rho_loop(n, c, x, y_, q_, j_, r, b__, budget - int63!(1), ())
        }
      }
    },
    sumbool::right => {
      int63!(1)
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.rho_try
// Variant: uncurried
pub fn rho_try_1(n: Int63, c: Int63) -> Int63 {
  rho_try(n, c, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.rho_try (local: rho_try)
// Variant: uncurried, lifted
pub fn rho_try(n: Int63, c: Int63, _H: ()) -> Int63 {
  let tmp = c < __rocq_global_1389;
  match bdec(tmp) {
    sumbool::left => {
      let g = rho_loop_1(n, c, int63!(2), int63!(2), int63!(1), int63!(0), int63!(1), int63!(0), int63!(1048576));
      let tmp_1 = andb(int63!(1) < g, g < n);
      let tmp_2 = n % g == int63!(0);
      if andb(tmp_1, tmp_2) {
        g
      } else {
        rho_try(n, c + int63!(1), ())
      }
    },
    sumbool::right => {
      int63!(0)
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.certify
// Variant: borrowed, uncurried
pub fn certify_1(pr: &Array<Int63>, np: Int63, n: Int63) -> cres {
  let np_1 = np;
  let n_1 = n;
  certify(pr, np_1, n_1, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.certify (local: certify)
// Variant: borrowed, uncurried, lifted
pub fn certify(pr: &Array<Int63>, np: Int63, n: Int63, _H: ()) -> cres {
  let np_1 = np;
  let n_1 = n;
  let m = n_1 - int63!(1);
  let tmp = td_cert_1(pr, np_1, int63!(0), n_1, m, int63!(1), m);
  match tmp {
    (v35, v37) => {
      match v35 {
        (v40, v42) => {
          match v40 {
            bres::BFound => {
              let tmp_1 = n_1 / v42;
              if tmp_1 < v42 {
                cres::CPrime
              } else {
                if v37 <= int63!(1) {
                  cres::CFail
                } else {
                  if v37 <= __rocq_global_921 {
                    base_res(find_base_1(n_1, m, v37, int63!(2)))
                  } else {
                    if mr_comp(v37) {
                      let g = rho_try_1(v37, int63!(1));
                      let tmp_2 = andb(int63!(1) < g, g < v37);
                      let tmp_3 = v37 % g == int63!(0);
                      if andb(tmp_2, tmp_3) {
                        match find_base_1(n_1, m, g, int63!(2)) {
                          bres::BFound => {
                            let F_ = v42 * g;
                            let tmp_4 = n_1 / F_;
                            if tmp_4 < F_ {
                              cres::CPrime
                            } else {
                              base_res(find_base_1(n_1, m, v37 / g, int63!(2)))
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
                      let tmp_5 = v37 < n_1;
                      match bdec(tmp_5) {
                        sumbool::left => {
                          match certify(pr, np_1, v37, ()) {
                            cres::CPrime => {
                              base_res(find_base_1(n_1, m, v37, int63!(2)))
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
pub fn td_loop_1(n: Int63, d: Int63) -> bool {
  td_loop(n, d, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.td_loop (local: td_loop)
// Variant: uncurried, lifted
pub fn td_loop(n: Int63, d: Int63, _H: ()) -> bool {
  let tmp = d < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = d * d;
      if tmp_1 <= n {
        let tmp_2 = n % d;
        if tmp_2 == int63!(0) {
          false
        } else {
          td_loop(n, d + int63!(1), ())
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
pub fn classify(pr: &Array<Int63>, np: Int63, x: Int63) -> kind {
  let np_1 = np;
  let x_1 = x;
  if x_1 <= __rocq_global_921 {
    kind::KPrime
  } else {
    let s = isqrt(x_1);
    let tmp = s * s;
    if tmp == x_1 {
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
            if td_loop_1(x_1, int63!(2)) {
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
pub fn contrib(pr: &Array<Int63>, np: Int63, x: Int63, e: Int63, P: Int63) -> Int63 {
  let np_1 = np;
  let x_1 = x;
  let e_1 = e;
  let P_1 = P;
  match classify(pr, np_1, x_1) {
    kind::KPrime => {
      fmod(e_1, P_1)
    },
    kind::KSquare => {
      fmod(e_1 + e_1, P_1)
    },
    kind::KSemi => {
      let f = fmod(e_1, P_1);
      mulmod(f, f, __rocq_global_525)
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.peel
// Variant: uncurried
pub fn peel_1(pr: Array<Int63>, np: Int63, aG: Array<Int63>, aL: Array<Int63>, nG: Int63, nL: Int63, sel: bool, i: Int63, P: Int63, acc: Int63) -> ((Array<Int63>, Array<Int63>), Int63) {
  peel(pr, np, aG, aL, nG, nL, sel, i, P, acc, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.peel (local: peel)
// Variant: uncurried, lifted
pub fn peel(pr: Array<Int63>, np: Int63, aG: Array<Int63>, aL: Array<Int63>, nG: Int63, nL: Int63, sel: bool, i: Int63, P: Int63, acc: Int63, _H: ()) -> ((Array<Int63>, Array<Int63>), Int63) {
  let aG_clone = Clone::clone(&aG);
  let aL_clone = Clone::clone(&aL);
  let c = sel_get(sel, aG_clone, aL_clone, i);
  let tmp = int63!(1) < c;
  match bdec(tmp) {
    sumbool::left => {
      let aG_clone_1 = Clone::clone(&aG);
      let tmp_1 = refine_1(aG_clone_1, nG, int63!(0), c);
      let aL_clone_1 = Clone::clone(&aL);
      let x = refine_1(aL_clone_1, nL, int63!(0), tmp_1);
      let tmp_2 = int63!(1) < x;
      match bdec(tmp_2) {
        sumbool::left => {
          let rG = divpass_1(x, aG, nG, int63!(0), int63!(0));
          let rL = divpass_1(x, aL, nL, int63!(0), int63!(0));
          let rG_clone = Clone::clone(&rG);
          let tmp_3 = snd::<Array<Int63>, Int63>(rG_clone);
          let rL_clone = Clone::clone(&rL);
          let tmp_4 = snd::<Array<Int63>, Int63>(rL_clone);
          let pr_clone = Clone::clone(&pr);
          let callback: Rc<dyn Fn(Int63) -> Int63> = Rc::new({
            let __anf_capture_130 = np;
            let __anf_capture_132 = x;
            let __anf_capture_134 = P;
            move |e: Int63| -> Int63 {
              let pr = &pr_clone;
              let tmp_5 = Clone::clone(&__anf_capture_130);
              let tmp_6 = Clone::clone(&__anf_capture_132);
              let tmp_7 = Clone::clone(&__anf_capture_134);
              contrib(pr, tmp_5, tmp_6, e, tmp_7)
            }
          });
          let acc_ = step_acc(acc, tmp_3, tmp_4, callback);
          let rG_clone_1 = Clone::clone(&rG);
          let tmp_8 = fst::<Array<Int63>, Int63>(rG_clone_1);
          let rL_clone_1 = Clone::clone(&rL);
          let tmp_9 = sel_get(sel, tmp_8, fst::<Array<Int63>, Int63>(rL_clone_1), i) < c;
          match bdec(tmp_9) {
            sumbool::left => {
              peel(pr, np, fst::<Array<Int63>, Int63>(rG), fst::<Array<Int63>, Int63>(rL), nG, nL, sel, i, P, acc_, ())
            },
            sumbool::right => {
              std::mem::drop(pr);
              ((fst::<Array<Int63>, Int63>(rG), fst::<Array<Int63>, Int63>(rL)), acc_)
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
pub fn ph2_1(pr: Array<Int63>, np: Int63, aG: Array<Int63>, aL: Array<Int63>, nG: Int63, nL: Int63, sel: bool, n: Int63, i: Int63, P: Int63, acc: Int63) -> ((Array<Int63>, Array<Int63>), Int63) {
  ph2(pr, np, aG, aL, nG, nL, sel, n, i, P, acc, ())
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.ph2 (local: ph2)
// Variant: uncurried, lifted
pub fn ph2(pr: Array<Int63>, np: Int63, aG: Array<Int63>, aL: Array<Int63>, nG: Int63, nL: Int63, sel: bool, n: Int63, i: Int63, P: Int63, acc: Int63, _H: ()) -> ((Array<Int63>, Array<Int63>), Int63) {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let pr_clone = Clone::clone(&pr);
      let r = peel_1(pr_clone, np, aG, aL, nG, nL, sel, i, P, acc);
      let r_clone = Clone::clone(&r);
      let tmp_1 = fst::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), Int63>(r_clone));
      let r_clone_1 = Clone::clone(&r);
      ph2(pr, np, tmp_1, snd::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), Int63>(r_clone_1)), nG, nL, sel, n, i + int63!(1), P, snd::<(Array<Int63>, Array<Int63>), Int63>(r), ())
    },
    sumbool::right => {
      std::mem::drop(pr);
      ((aG, aL), acc)
    },
  }
}

// Rocq: Atrivialpursuit.atrivialpursuit_implem.atp_impl
// Variant: uncurried
pub fn atp_impl(p: Int63, x: Array<Int63>, y: Array<Int63>) -> Int63 {
  let s = sieve(());
  let s_clone = Clone::clone(&s);
  let pr = fst::<Array<Int63>, Int63>(s_clone);
  let np = snd::<Array<Int63>, Int63>(s);
  let nG = x.length();
  let nL = y.length();
  let tmp = int63!(0);
  let x_ref = &x;
  let tmp_1 = x_ref.copy();
  std::mem::drop(x);
  let y_ref = &y;
  let tmp_2 = y_ref.copy();
  std::mem::drop(y);
  let pr_clone = Clone::clone(&pr);
  let r1 = ph1_1(pr_clone, np, tmp, tmp_1, tmp_2, nG, nL, p, int63!(1));
  let r1_clone = Clone::clone(&r1);
  let tmp_3 = fst::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), Int63>(r1_clone));
  let r1_clone_1 = Clone::clone(&r1);
  let tmp_4 = snd::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), Int63>(r1_clone_1));
  let tmp_5 = snd::<(Array<Int63>, Array<Int63>), Int63>(r1);
  let pr_clone_1 = Clone::clone(&pr);
  let r2 = ph2_1(pr_clone_1, np, tmp_3, tmp_4, nG, nL, false, nG, int63!(0), p, tmp_5);
  let r2_clone = Clone::clone(&r2);
  let tmp_6 = fst::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), Int63>(r2_clone));
  let r2_clone_1 = Clone::clone(&r2);
  let r3 = ph2_1(pr, np, tmp_6, snd::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), Int63>(r2_clone_1)), nG, nL, true, nL, int63!(0), p, snd::<(Array<Int63>, Array<Int63>), Int63>(r2));
  snd::<(Array<Int63>, Array<Int63>), Int63>(r3)
}
const __rocq_global_43: Int63 = int63!(1000000);
const __rocq_global_525: Int63 = int63!(1000000007);
const __rocq_global_921: Int63 = int63!(1000000000000);
const __rocq_global_1183: Int63 = int63!(1000);
const __rocq_global_1389: Int63 = int63!(40);