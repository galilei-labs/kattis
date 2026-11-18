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

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.bdec
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

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.loop
// Variant: uncurried
pub fn loop__1<S: Clone + 'static>(f: Rc<dyn Fn(u64, S) -> S>, hi: u64, i: u64, s: S) -> S {
  loop_::<S>((), f, hi, i, s, ())
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.loop (local: loop)
// Variant: uncurried, lifted
pub fn loop_<S: Clone + 'static>(_S_1: (), f: Rc<dyn Fn(u64, S) -> S>, hi: u64, i: u64, s: S, _H: ()) -> S {
  let tmp = ltb(i, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add_1(i, 1u64);
      let f_ref: &Rc<dyn Fn(u64, S) -> S> = &f;
      let tmp_2 = f_ref(i, s);
      loop_::<S>((), f, hi, tmp_1, tmp_2, ())
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
  rocq_bigint::mul(v0, v1)
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
  uconv(x, ())
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.uconv (local: uconv)
// Variant: uncurried, lifted
pub fn uconv(x: u64, _H: ()) -> Rc<BigInt> {
  let tmp = eqb(x, 0u64);
  match bdec(tmp) {
    sumbool::left => {
      rocq_bigint::zero()
    },
    sumbool::right => {
      let tmp_1 = rocq_bigint::one();
      let tmp_2 = rocq_bigint::twice(tmp_1);
      let tmp_3 = rocq_bigint::identity(tmp_2);
      let tmp_4 = uconv(div(x, 2u64), ());
      let tmp_5 = mul_1(tmp_3, tmp_4);
      let tmp_6 = mod_(x, 2u64);
      let tmp_7 = 0u64;
      let tmp_8 = if eqb(tmp_6, tmp_7) {
        rocq_bigint::zero()
      } else {
        let tmp_9 = rocq_bigint::one();
        rocq_bigint::identity(tmp_9)
      };
      add(tmp_5, tmp_8)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub_1(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.sconv
pub fn sconv(x: u64) -> Rc<BigInt> {
  if ltb(x, 4611686018427387904u64) {
    uconv_1(x)
  } else {
    let tmp = uconv_1(sub_1(0u64, x));
    opp(tmp)
  }
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.ztab
// Variant: uncurried
pub fn ztab(n: u64, m: u64, xe: Rc<Array<Rc<Array<u64>>>>) -> Rc<Array<Rc<BigInt>>> {
  let tmp = 0u64;
  let tmp_1 = mul(n, m);
  let tmp_2 = rocq_bigint::zero();
  let tmp_3 = rocq_array::make::<Rc<BigInt>>(tmp_1, tmp_2);
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new({
    let __anf_capture_25 = m;
    move |i: u64, T: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let xe = &xe;
      let m = &__anf_capture_25;
      let xe_clone = Rc::clone(xe);
      let row = rocq_array::get::<Rc<Array<u64>>>(&xe_clone, i);
      std::mem::drop(xe_clone);
      let tmp_4 = 0u64;
      let m_clone = Clone::clone(m);
      let callback_1: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new({
        let __anf_capture_45 = i;
        move |j: u64, T: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
          let i = &__anf_capture_45;
          let m = &m_clone;
          let row = &row;
          let tmp_5 = add_1(mul(Clone::clone(i), Clone::clone(m)), j);
          let tmp_6 = rocq_array::get::<u64>(row, j);
          let tmp_7 = sconv(tmp_6);
          rocq_array::set::<Rc<BigInt>>(T, tmp_5, tmp_7)
        }
      });
      let m_clone_1 = Clone::clone(m);
      for_::<Rc<Array<Rc<BigInt>>>>(tmp_4, m_clone_1, T, callback_1)
    }
  });
  for_::<Rc<Array<Rc<BigInt>>>>(tmp, n, tmp_3, callback)
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

// Rocq: Corelib.BinNums.IntDef.Z.eqb
// Variant: uncurried
pub fn eqb_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::equal(v0, v1)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.find_piv
// Variant: uncurried
pub fn find_piv(n: u64, m: u64, c: u64, T: Rc<Array<Rc<BigInt>>>, U: Rc<Array<bool>>) -> u64 {
  let tmp = 0u64;
  let callback: Rc<dyn Fn(u64, u64) -> u64> = Rc::new({
    let __anf_capture_19 = n;
    move |i: u64, r: u64| -> u64 {
      let n = &__anf_capture_19;
      let U = &U;
      let m = &m;
      let c = &c;
      let T = &T;
      let n_clone = Clone::clone(n);
      if eqb(r, n_clone) {
        if rocq_array::get::<bool>(U, i) {
          r
        } else {
          let tmp_1 = rocq_array::get::<Rc<BigInt>>(T, add_1(mul(i, Clone::clone(m)), Clone::clone(c)));
          let tmp_2 = rocq_bigint::zero();
          if eqb_1(tmp_1, tmp_2) {
            r
          } else {
            i
          }
        }
      } else {
        r
      }
    }
  });
  for_::<u64>(tmp, n, n, callback)
}

// Rocq: Corelib.BinNums.IntDef.Z.ltb
// Variant: uncurried
pub fn ltb_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> bool {
  rocq_bigint::lt(v0, v1)
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

// Rocq: Stdlib.ZArith.BinIntDef.Z.abs
pub fn abs(v0: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::abs(v0)
}

// Rocq: StdGalilei.bigint.zgcd
// Variant: uncurried
pub fn zgcd(a: Rc<BigInt>, b: Rc<BigInt>) -> Rc<BigInt> {
  let tmp = abs(a);
  let tmp_1 = abs(b);
  zgcd_loop_1(tmp, tmp_1)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.row_gcd
// Variant: uncurried
pub fn row_gcd(m: u64, i: u64, T: Rc<Array<Rc<BigInt>>>) -> Rc<BigInt> {
  let tmp = 0u64;
  let tmp_1 = rocq_bigint::zero();
  let callback: Rc<dyn Fn(u64, Rc<BigInt>) -> Rc<BigInt>> = Rc::new({
    let __anf_capture_16 = m;
    move |j: u64, g: Rc<BigInt>| -> Rc<BigInt> {
      let i = &i;
      let m = &__anf_capture_16;
      let tmp_2 = rocq_array::get::<Rc<BigInt>>(&T, add_1(mul(Clone::clone(i), Clone::clone(m)), j));
      zgcd(g, tmp_2)
    }
  });
  for_::<Rc<BigInt>>(tmp, m, tmp_1, callback)
}

// Rocq: Corelib.BinNums.IntDef.Z.div
// Variant: uncurried
pub fn div_1(v0: Rc<BigInt>, v1: Rc<BigInt>) -> Rc<BigInt> {
  rocq_bigint::div(v0, v1)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.div_row
// Variant: uncurried
pub fn div_row(m: u64, i: u64, g: Rc<BigInt>, T: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let tmp = 0u64;
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new({
    let __anf_capture_16 = m;
    move |j: u64, T: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let i = &i;
      let m = &__anf_capture_16;
      let g = &g;
      let tmp_1 = add_1(mul(Clone::clone(i), Clone::clone(m)), j);
      let tmp_2 = rocq_array::get::<Rc<BigInt>>(&T, add_1(mul(Clone::clone(i), Clone::clone(m)), j));
      let g_clone = Rc::clone(g);
      let tmp_3 = div_1(tmp_2, g_clone);
      rocq_array::set::<Rc<BigInt>>(T, tmp_1, tmp_3)
    }
  });
  for_::<Rc<Array<Rc<BigInt>>>>(tmp, m, T, callback)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.norm_row
// Variant: uncurried
pub fn norm_row(m: u64, i: u64, T: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let T_clone = Rc::clone(&T);
  let g = row_gcd(m, i, T_clone);
  let tmp = rocq_bigint::one();
  let tmp_1 = rocq_bigint::identity(tmp);
  let g_clone = Rc::clone(&g);
  if ltb_1(tmp_1, g_clone) {
    div_row(m, i, g, T)
  } else {
    std::mem::drop(g);
    T
  }
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.upd_row
// Variant: uncurried
pub fn upd_row(m: u64, i: u64, s: u64, p: Rc<BigInt>, f: Rc<BigInt>, T: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let tmp = 0u64;
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new({
    let __anf_capture_26 = m;
    move |j: u64, T: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let i = &i;
      let p = &p;
      let s = &s;
      let m = &__anf_capture_26;
      let f = &f;
      let tmp_1 = add_1(mul(Clone::clone(i), Clone::clone(m)), j);
      let tmp_2 = rocq_array::get::<Rc<BigInt>>(&T, add_1(mul(Clone::clone(i), Clone::clone(m)), j));
      let p_clone = Rc::clone(p);
      let tmp_3 = mul_1(p_clone, tmp_2);
      let tmp_4 = rocq_array::get::<Rc<BigInt>>(&T, add_1(mul(Clone::clone(s), Clone::clone(m)), j));
      let f_clone = Rc::clone(f);
      let tmp_5 = mul_1(f_clone, tmp_4);
      let tmp_6 = sub(tmp_3, tmp_5);
      rocq_array::set::<Rc<BigInt>>(T, tmp_1, tmp_6)
    }
  });
  for_::<Rc<Array<Rc<BigInt>>>>(tmp, m, T, callback)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.elim_rows
// Variant: uncurried
pub fn elim_rows(n: u64, m: u64, s: u64, c: u64, T: Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>> {
  let p = rocq_array::get::<Rc<BigInt>>(&T, add_1(mul(s, m), c));
  let tmp = 0u64;
  let callback: Rc<dyn Fn(u64, Rc<Array<Rc<BigInt>>>) -> Rc<Array<Rc<BigInt>>>> = Rc::new({
    let __anf_capture_33 = c;
    let __anf_capture_35 = s;
    let __anf_capture_39 = m;
    move |i: u64, T: Rc<Array<Rc<BigInt>>>| -> Rc<Array<Rc<BigInt>>> {
      let c = &__anf_capture_33;
      let s = &__anf_capture_35;
      let p = &p;
      let m = &__anf_capture_39;
      let s_clone = Clone::clone(s);
      if eqb(i, s_clone) {
        T
      } else {
        let f = rocq_array::get::<Rc<BigInt>>(&T, add_1(mul(i, Clone::clone(m)), Clone::clone(c)));
        let tmp_1 = rocq_bigint::zero();
        let f_clone = Rc::clone(&f);
        if eqb_1(f_clone, tmp_1) {
          std::mem::drop(f);
          T
        } else {
          let m_clone = Clone::clone(m);
          let s_clone_1 = Clone::clone(s);
          let p_clone = Rc::clone(p);
          let tmp_2 = upd_row(m_clone, i, s_clone_1, p_clone, f, T);
          let m_clone_1 = Clone::clone(m);
          norm_row(m_clone_1, i, tmp_2)
        }
      }
    }
  });
  for_::<Rc<Array<Rc<BigInt>>>>(tmp, n, T, callback)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.col_step
// Variant: uncurried
pub fn col_step(n: u64, m: u64, c: u64, st: (Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>)) -> (Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>) {
  let st_clone = Clone::clone(&st);
  let T = fst::<Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>>(st_clone);
  let st_clone_1 = Clone::clone(&st);
  let U = snd::<Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>>(st_clone_1);
  let T_clone = Rc::clone(&T);
  let U_clone = Rc::clone(&U);
  let s = find_piv(n, m, c, T_clone, U_clone);
  if eqb(s, n) {
    std::mem::drop(U);
    std::mem::drop(T);
    st
  } else {
    std::mem::drop(st);
    let tmp = elim_rows(n, m, s, c, T);
    let tmp_1 = rocq_array::set::<bool>(U, s, true);
    (tmp, tmp_1)
  }
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  if b {
    false
  } else {
    true
  }
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.count_nz
// Variant: borrowed, uncurried
pub fn count_nz(m: u64, i: u64, T: &Rc<Array<Rc<BigInt>>>) -> u64 {
  let tmp = 0u64;
  let tmp_1 = 0u64;
  let T_clone = Rc::clone(T);
  let callback: Rc<dyn Fn(u64, u64) -> u64> = Rc::new({
    let __anf_capture_20 = m;
    move |j: u64, k: u64| -> u64 {
      let i = &i;
      let m = &__anf_capture_20;
      let T = &T_clone;
      let tmp_2 = rocq_array::get::<Rc<BigInt>>(T, add_1(mul(Clone::clone(i), Clone::clone(m)), j));
      let tmp_3 = rocq_bigint::zero();
      if eqb_1(tmp_2, tmp_3) {
        k
      } else {
        add_1(k, 1u64)
      }
    }
  });
  for_::<u64>(tmp, m, tmp_1, callback)
}

// Rocq: Dimensionalanalysis.dimensionalanalysis_implem.valid_impl
// Variant: uncurried
pub fn valid_impl(xm: u64, xe: Rc<Array<Rc<Array<u64>>>>) -> bool {
  let n = rocq_array::length::<Rc<Array<u64>>>(&xe);
  let tmp = 0u64;
  let tmp_1 = ztab(n, xm, xe);
  let tmp_2 = rocq_array::make::<bool>(n, false);
  let tmp_3 = (tmp_1, tmp_2);
  let callback: Rc<dyn Fn(u64, (Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>)) -> (Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>)> = Rc::new({
    let __anf_capture_33 = n;
    let __anf_capture_35 = xm;
    move |v37: u64, v38: (Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>)| -> (Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>) {
      let tmp_4 = Clone::clone(&__anf_capture_33);
      let tmp_5 = Clone::clone(&__anf_capture_35);
      col_step(tmp_4, tmp_5, v37, v38)
    }
  });
  let st = for_::<(Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>)>(tmp, xm, tmp_3, callback);
  let T = fst::<Rc<Array<Rc<BigInt>>>, Rc<Array<bool>>>(st);
  let tmp_6 = 0u64;
  let tmp_7 = true;
  let callback_1: Rc<dyn Fn(u64, bool) -> bool> = Rc::new({
    let __anf_capture_76 = xm;
    move |i: u64, b: bool| -> bool {
      let xm = &__anf_capture_76;
      let T = &T;
      if b {
        let tmp_8 = count_nz(Clone::clone(xm), i, T);
        negb(eqb(tmp_8, 1u64))
      } else {
        false
      }
    }
  });
  for_::<bool>(tmp_6, n, tmp_7, callback_1)
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
