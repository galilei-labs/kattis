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

pub type uint = u64;

pub type sint = u64;

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.valid
// Variant: uncurried
pub fn valid() -> Rc<dyn Fn(u64, Rc<Array<Rc<Array<u64>>>>) -> bool> {
  let v0: fn(u64, Rc<Array<Rc<Array<u64>>>>) -> bool = valid_impl;
  let v1: Rc<dyn Fn(u64, Rc<Array<Rc<Array<u64>>>>) -> bool> = Rc::new(v0);
  v1
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.valid
pub fn valid_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> bool>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> bool> = valid_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> bool>> = Rc::new(v0);
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

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.bdec
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

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.loop
// Variant: uncurried
pub fn loop__1<S: Clone + 'static>(f: Rc<dyn Fn(u64, S) -> S>, hi: u64, i: u64, s: S) -> S {
  loop_::<S>((), f, hi, i, s, ())
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.loop (local: loop)
// Variant: uncurried, lifted
pub fn loop_<S: Clone + 'static>(_S_1: (), f: Rc<dyn Fn(u64, S) -> S>, hi: u64, i: u64, s: S, _H: ()) -> S {
  let v13 = ltb(i, hi);
  match bdec(v13) {
    sumbool::left => {
      let v26 = add_1(i, 1u64);
      let v27: &Rc<dyn Fn(u64, S) -> S> = &f;
      let v32 = v27(i, s);
      loop_::<S>((), f, hi, v26, v32, ())
    },
    sumbool::right => {
      std::mem::drop(f);
      s
    },
  }
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.for_
// Variant: uncurried
pub fn for_<S: Clone + 'static>(lo: u64, hi: u64, s: S, f: Rc<dyn Fn(u64, S) -> S>) -> S {
  loop__1::<S>(f, hi, lo, s)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Corelib.BinNums.IntDef.Z.mul
// Variant: uncurried
pub fn mul_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::mul(v0, v1);
  v8
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

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.uconv
pub fn uconv_1(x: u64) -> Rc<BigInt> {
  let v9 = uconv(x, ());
  v9
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.uconv (local: uconv)
// Variant: uncurried, lifted
pub fn uconv(x: u64, _H: ()) -> Rc<BigInt> {
  let v11 = eqb(x, 0u64);
  let v83 = match bdec(v11) {
    sumbool::left => {
      let v16 = rocq_bigint::zero();
      v16
    },
    sumbool::right => {
      let v21 = rocq_bigint::one();
      let v24 = rocq_bigint::twice(v21);
      let v26 = rocq_bigint::identity(v24);
      let v42 = uconv(div(x, 2u64), ());
      let v47 = mul_1(v26, v42);
      let v56 = mod_(x, 2u64);
      let v58 = 0u64;
      let v64 = match eqb(v56, v58) {
        true => {
          let v66 = rocq_bigint::zero();
          v66
        },
        false => {
          let v69 = rocq_bigint::one();
          let v72 = rocq_bigint::identity(v69);
          v72
        },
      };
      let v80 = add(v47, v64);
      v80
    },
  };
  v83
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub_1(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.sconv
pub fn sconv(x: u64) -> Rc<BigInt> {
  let v3 = 4611686018427387904u64;
  let v35 = match ltb(x, v3) {
    true => {
      let v14 = uconv_1(x);
      v14
    },
    false => {
      let v29 = uconv_1(sub_1(0u64, x));
      let v32 = opp(v29);
      v32
    },
  };
  v35
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.ztab
// Variant: uncurried
pub fn ztab(n: u64, m: u64, xe: Rc<Array<Rc<Array<u64>>>>) -> Rc<Array<Rc<BigInt>>> {
  let v5 = 0u64;
  let v11 = mul(n, m);
  let v12 = rocq_bigint::zero();
  let v17 = rocq_array::make::<Rc<BigInt>>(v11, v12);
  let v22 = {
    let __anf_capture_25 = m;
    move |i: u64, T: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let xe = &xe;
      let m = &__anf_capture_25;
      let v30 = Rc::clone(xe);
      let row = rocq_array::get::<Rc<Array<u64>>>(&v30, i);
      std::mem::drop(v30);
      let v37 = 0u64;
      let v41 = Clone::clone(m);
      let v44 = {
        let __anf_capture_45 = i;
        move |j: u64, T: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
          let i = &__anf_capture_45;
          let m = &v41;
          let row = &row;
          let v64 = add_1(mul(Clone::clone(i), Clone::clone(m)), j);
          let v69 = rocq_array::get::<u64>(&row, j);
          let v71 = sconv(v69);
          rocq_array::set::<Rc<BigInt>>(T, v64, v71)
        }
      };
      let v81: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new(v44);
      let v86 = Clone::clone(m);
      for_::<Rc<Array<Rc<BigInt>>>>(v37, v86, T, v81)
    }
  };
  let v94: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new(v22);
  for_::<Rc<Array<Rc<BigInt>>>>(v5, n, v17, v94)
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

// Rocq: Corelib.BinNums.IntDef.Z.eqb
// Variant: uncurried
pub fn eqb_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::equal(v0, v1)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.find_piv
// Variant: uncurried
pub fn find_piv(n: u64, m: u64, c: u64, T: Rc<Array<Rc<BigInt>>>, U: Rc<Array<bool>>) -> u64 {
  let v7 = 0u64;
  let v18 = {
    let __anf_capture_19 = n;
    move |i: u64, r: u64| -> u64 {
      let n = &__anf_capture_19;
      let U = &U;
      let m = &m;
      let c = &c;
      let T = &T;
      let v35 = Clone::clone(n);
      match eqb(r, v35) {
        true => {
          match rocq_array::get::<bool>(&U, i) {
            true => {
              r
            },
            false => {
              let v57 = add_1(mul(i, Clone::clone(m)), Clone::clone(c));
              let v59 = rocq_array::get::<Rc<BigInt>>(&T, v57);
              let v60 = rocq_bigint::zero();
              match eqb_1(v59, v60) {
                true => {
                  r
                },
                false => {
                  i
                },
              }
            },
          }
        },
        false => {
          r
        },
      }
    }
  };
  let v82: Rc<dyn Fn(u64, u64) -> u64> = Rc::new(v18);
  for_::<u64>(v7, n, n, v82)
}

// Rocq: Corelib.BinNums.IntDef.Z.ltb
// Variant: uncurried
pub fn ltb_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::lt(v0, v1)
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

// Rocq: Stdlib.ZArith.BinIntDef.Z.abs
pub fn abs(v0: Rc<BigInt>) -> Rc<BigInt> {
  let v5 = rocq_bigint::abs(v0);
  v5
}

// Rocq: StdGalilei.bigint.zgcd
// Variant: uncurried
pub fn zgcd(a: Rc<BigInt>, b: Rc<BigInt>) -> Rc<BigInt> {
  let v6 = abs(a);
  let v10 = abs(b);
  let v16 = zgcd_loop_1(v6, v10);
  v16
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.row_gcd
// Variant: uncurried
pub fn row_gcd(m: u64, i: u64, T: Rc<Array<Rc<BigInt>>>) -> Rc<BigInt> {
  let v5 = 0u64;
  let v6 = rocq_bigint::zero();
  let v13 = {
    let __anf_capture_16 = m;
    move |j: u64, g: Rc<BigInt>| -> Rc<BigInt> {
      let i = &i;
      let m = &__anf_capture_16;
      let T = &T;
      let v35 = add_1(mul(Clone::clone(i), Clone::clone(m)), j);
      let v37 = rocq_array::get::<Rc<BigInt>>(&T, v35);
      let v43 = zgcd(g, v37);
      v43
    }
  };
  let v45: Rc<dyn Fn(u64, Rc<BigInt>) -> Rc<BigInt>> = Rc::new(v13);
  let v56 = for_::<Rc<BigInt>>(v5, m, v6, v45);
  v56
}

// Rocq: Corelib.BinNums.IntDef.Z.div
// Variant: uncurried
pub fn div_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  let v8 = rocq_bigint::div(v0, v1);
  v8
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.div_row
// Variant: uncurried
pub fn div_row(m: u64, i: u64, g: Rc<BigInt>, T: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let v6 = 0u64;
  let v13 = {
    let __anf_capture_16 = m;
    move |j: u64, T: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let i = &i;
      let m = &__anf_capture_16;
      let g = &g;
      let v33 = add_1(mul(Clone::clone(i), Clone::clone(m)), j);
      let v46 = add_1(mul(Clone::clone(i), Clone::clone(m)), j);
      let v47 = &T;
      let v51 = rocq_array::get::<Rc<BigInt>>(&v47, v46);
      let v54 = Rc::clone(g);
      let v55 = div_1(v51, v54);
      rocq_array::set::<Rc<BigInt>>(T, v33, v55)
    }
  };
  let v65: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new(v13);
  for_::<Rc<Array<Rc<BigInt>>>>(v6, m, T, v65)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.norm_row
// Variant: uncurried
pub fn norm_row(m: u64, i: u64, T: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let v10 = Rc::clone(&T);
  let g = row_gcd(m, i, v10);
  let v14 = rocq_bigint::one();
  let v17 = rocq_bigint::identity(v14);
  let v21 = Rc::clone(&g);
  match ltb_1(v17, v21) {
    true => {
      div_row(m, i, g, T)
    },
    false => {
      std::mem::drop(g);
      T
    },
  }
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.upd_row
// Variant: uncurried
pub fn upd_row(m: u64, i: u64, s: u64, p: Rc<BigInt>, f: Rc<BigInt>, T: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let v8 = 0u64;
  let v19 = {
    let __anf_capture_26 = m;
    move |j: u64, T: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let i = &i;
      let p = &p;
      let s = &s;
      let m = &__anf_capture_26;
      let f = &f;
      let v43 = add_1(mul(Clone::clone(i), Clone::clone(m)), j);
      let v57 = add_1(mul(Clone::clone(i), Clone::clone(m)), j);
      let v58 = &T;
      let v61 = rocq_array::get::<Rc<BigInt>>(&v58, v57);
      let v63 = Rc::clone(p);
      let v66 = mul_1(v63, v61);
      let v79 = add_1(mul(Clone::clone(s), Clone::clone(m)), j);
      let v80 = &T;
      let v83 = rocq_array::get::<Rc<BigInt>>(&v80, v79);
      let v85 = Rc::clone(f);
      let v88 = mul_1(v85, v83);
      let v93 = sub(v66, v88);
      rocq_array::set::<Rc<BigInt>>(T, v43, v93)
    }
  };
  let v103: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new(v19);
  for_::<Rc<Array<Rc<BigInt>>>>(v8, m, T, v103)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.elim_rows
// Variant: uncurried
pub fn elim_rows(n: u64, m: u64, s: u64, c: u64, T: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let v16 = add_1(mul(s, m), c);
  let v17 = &T;
  let p = rocq_array::get::<Rc<BigInt>>(&v17, v16);
  let v23 = 0u64;
  let v32 = {
    let __anf_capture_33 = c;
    let __anf_capture_35 = s;
    let __anf_capture_39 = m;
    move |i: u64, T: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let c = &__anf_capture_33;
      let s = &__anf_capture_35;
      let p = &p;
      let m = &__anf_capture_39;
      let v47 = Clone::clone(s);
      match eqb(i, v47) {
        true => {
          T
        },
        false => {
          let v63 = add_1(mul(i, Clone::clone(m)), Clone::clone(c));
          let v64 = &T;
          let f = rocq_array::get::<Rc<BigInt>>(&v64, v63);
          let v69 = rocq_bigint::zero();
          let v72 = Rc::clone(&f);
          match eqb_1(v72, v69) {
            true => {
              std::mem::drop(f);
              T
            },
            false => {
              let v82 = Clone::clone(m);
              let v86 = Clone::clone(s);
              let v88 = Rc::clone(p);
              let v93 = upd_row(v82, i, v86, v88, f, T);
              let v95 = Clone::clone(m);
              norm_row(v95, i, v93)
            },
          }
        },
      }
    }
  };
  let v109: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new(v32);
  for_::<Rc<Array<Rc<BigInt>>>>(v23, n, T, v109)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.col_step
// Variant: uncurried
pub fn col_step(n: u64, m: u64, c: u64, st: (Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>)) -> (Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>) {
  let v6 = Clone::clone(&st);
  let T = fst::<Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>>(v6);
  let v11 = Clone::clone(&st);
  let U = snd::<Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>>(v11);
  let v23 = Rc::clone(&T);
  let v26 = Rc::clone(&U);
  let s = find_piv(n, m, c, v23, v26);
  match eqb(s, n) {
    true => {
      std::mem::drop(U);
      std::mem::drop(T);
      st
    },
    false => {
      std::mem::drop(st);
      let v48 = elim_rows(n, m, s, c, T);
      let v57 = rocq_array::set::<bool>(U, s, true);
      (v48, v57)
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

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.count_nz
// Variant: borrowed, uncurried
pub fn count_nz(m: u64, i: u64, T: &Rc<Array<Rc<BigInt>>>) -> u64 {
  let v7 = 0u64;
  let v9 = 0u64;
  let v16 = Rc::clone(T);
  let v17 = {
    let __anf_capture_20 = m;
    move |j: u64, k: u64| -> u64 {
      let i = &i;
      let m = &__anf_capture_20;
      let T = &v16;
      let v39 = add_1(mul(Clone::clone(i), Clone::clone(m)), j);
      let v41 = rocq_array::get::<Rc<BigInt>>(&T, v39);
      let v42 = rocq_bigint::zero();
      match eqb_1(v41, v42) {
        true => {
          k
        },
        false => {
          add_1(k, 1u64)
        },
      }
    }
  };
  let v64: Rc<dyn Fn(u64, u64) -> u64> = Rc::new(v17);
  for_::<u64>(v7, m, v9, v64)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.valid_impl
// Variant: uncurried
pub fn valid_impl(xm: u64, xe: Rc<Array<Rc<Array<u64>>>>) -> bool {
  let v2 = &xe;
  let n = rocq_array::length::<Rc<Array<u64>>>(&v2);
  let v6 = 0u64;
  let v14 = ztab(n, xm, xe);
  let v21 = rocq_array::make::<bool>(n, false);
  let v27 = (v14, v21);
  let v32 = {
    let __anf_capture_33 = n;
    let __anf_capture_35 = xm;
    move |v37: u64, v38: (Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>)| -> (Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>) {
      let v41 = Clone::clone(&__anf_capture_33);
      let v43 = Clone::clone(&__anf_capture_35);
      col_step(v41, v43, v37, v38)
    }
  };
  let v51: Rc<dyn Fn(u64, (Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>)) -> (Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>)> = Rc::new(v32);
  let st = for_::<(Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>)>(v6, xm, v27, v51);
  let T = fst::<Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>>(st);
  let v68 = 0u64;
  let v70 = true;
  let v75 = {
    let __anf_capture_76 = xm;
    move |i: u64, b: bool| -> bool {
      let xm = &__anf_capture_76;
      let T = &T;
      match b {
        true => {
          let v91 = count_nz(Clone::clone(xm), i, T);
          negb(eqb(v91, 1u64))
        },
        false => {
          false
        },
      }
    }
  };
  let v111: Rc<dyn Fn(u64, bool) -> bool> = Rc::new(v75);
  for_::<bool>(v68, n, v70, v111)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.valid_impl
pub fn valid_impl_curried(xm: u64) -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> bool> {
  let v3 = {
    move |xe: Rc<Array<Rc<Array<u64>>>>| -> bool {
      let v9 = Clone::clone(&xm);
      valid_impl(v9, xe)
    }
  };
  let v15: Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> bool> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<Rc<Array<u64>>>>) -> bool> {
  let v0: Rc<dyn Fn(u64, Rc<Array<Rc<Array<u64>>>>) -> bool> = __rocq_global_884.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_884: Rc<dyn Fn(u64, Rc<Array<Rc<Array<u64>>>>) -> bool> = valid(); }
std::thread_local! { static __rocq_global_887: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> bool>> = valid_curried(); }