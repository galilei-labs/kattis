#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

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

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = u64;

// Rocq: Addemup.addemup_implem.K
pub fn K() -> u64 {
  131072u64
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
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

// Rocq: Addemup.addemup_implem.bdec
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

// Rocq: Addemup.addemup_implem.rotd
pub fn rotd(d: u64) -> Rc<option<u64>> {
  if eqb(d, 0u64) {
    Rc::new(option::<u64>::Some(0u64))
  } else {
    if eqb(d, 1u64) {
      Rc::new(option::<u64>::Some(1u64))
    } else {
      if eqb(d, 2u64) {
        Rc::new(option::<u64>::Some(2u64))
      } else {
        if eqb(d, 5u64) {
          Rc::new(option::<u64>::Some(5u64))
        } else {
          if eqb(d, 6u64) {
            Rc::new(option::<u64>::Some(9u64))
          } else {
            if eqb(d, 8u64) {
              Rc::new(option::<u64>::Some(8u64))
            } else {
              if eqb(d, 9u64) {
                Rc::new(option::<u64>::Some(6u64))
              } else {
                Rc::new(option::<u64>::None)
              }
            }
          }
        }
      }
    }
  }
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

// Rocq: Addemup.addemup_implem.rloop
// Variant: uncurried
pub fn rloop_1(x: u64, r: u64) -> Rc<option<u64>> {
  rloop(x, r, ())
}

// Rocq: Addemup.addemup_implem.rloop (local: rloop)
// Variant: uncurried, lifted
pub fn rloop(x: u64, r: u64, _H: ()) -> Rc<option<u64>> {
  let tmp = ltb(0u64, x);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rotd(mod_(x, 10u64));
      let (v28, v29) = __rocq_reuse::reset(tmp_1, |__payload| Clone::clone(__payload));
      match v28 {
        option::Some(v34) => {
          std::mem::drop(v29);
          rloop(div(x, 10u64), add(mul(r, 10u64), v34), ())
        },
        option::None => {
          __rocq_reuse::rebuild(v29, option::<u64>::None)
        },
      }
    },
    sumbool::right => {
      Rc::new(option::<u64>::Some(r))
    },
  }
}

// Rocq: Addemup.addemup_implem.alt
pub fn alt(c: u64) -> u64 {
  let tmp = rloop_1(c, 0u64);
  let (v9, v10) = __rocq_reuse::reset(tmp, |__payload| Clone::clone(__payload));
  std::mem::drop(v10);
  match v9 {
    option::Some(v15) => {
      v15
    },
    option::None => {
      c
    },
  }
}

// Rocq: Addemup.addemup_implem.build
// Variant: uncurried
pub fn build_1(y: Rc<Array<u64>>, T: Rc<Array<u64>>, n: u64, i: u64) -> Rc<Array<u64>> {
  build(y, T, n, i, ())
}

// Rocq: Addemup.addemup_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(y: Rc<Array<u64>>, T: Rc<Array<u64>>, n: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let c = rocq_array::get::<u64>(&y, i);
      let tmp_1 = rocq_array::set::<u64>(T, mul(2u64, i), add(mul(c, __rocq_global_68), i));
      let tmp_2 = rocq_array::set::<u64>(tmp_1, add(mul(2u64, i), 1u64), add(mul(alt(c), __rocq_global_68), i));
      build(y, tmp_2, n, add(i, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(y);
      T
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Addemup.addemup_implem.merge_loop
// Variant: uncurried
pub fn merge_loop_1(src: Rc<Array<u64>>, dst: Rc<Array<u64>>, i: u64, mid: u64, j: u64, hi: u64, k: u64) -> Rc<Array<u64>> {
  merge_loop(src, dst, i, mid, j, hi, k, ())
}

// Rocq: Addemup.addemup_implem.merge_loop (local: merge_loop)
// Variant: uncurried, lifted
pub fn merge_loop(src: Rc<Array<u64>>, dst: Rc<Array<u64>>, i: u64, mid: u64, j: u64, hi: u64, k: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, hi);
  match bdec(tmp) {
    sumbool::left => {
      if ltb(i, mid) {
        if ltb(j, hi) {
          let tmp_1 = rocq_array::get::<u64>(&src, i);
          let tmp_2 = rocq_array::get::<u64>(&src, j);
          if leb(tmp_1, tmp_2) {
            let tmp_3 = rocq_array::get::<u64>(&src, i);
            let tmp_4 = rocq_array::set::<u64>(dst, k, tmp_3);
            merge_loop(src, tmp_4, add(i, 1u64), mid, j, hi, add(k, 1u64), ())
          } else {
            let tmp_5 = rocq_array::get::<u64>(&src, j);
            let tmp_6 = rocq_array::set::<u64>(dst, k, tmp_5);
            merge_loop(src, tmp_6, i, mid, add(j, 1u64), hi, add(k, 1u64), ())
          }
        } else {
          let tmp_7 = rocq_array::get::<u64>(&src, i);
          let tmp_8 = rocq_array::set::<u64>(dst, k, tmp_7);
          merge_loop(src, tmp_8, add(i, 1u64), mid, j, hi, add(k, 1u64), ())
        }
      } else {
        let tmp_9 = rocq_array::get::<u64>(&src, j);
        let tmp_10 = rocq_array::set::<u64>(dst, k, tmp_9);
        merge_loop(src, tmp_10, i, mid, add(j, 1u64), hi, add(k, 1u64), ())
      }
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Addemup.addemup_implem.copy_loop
// Variant: uncurried
pub fn copy_loop_1(src: Rc<Array<u64>>, dst: Rc<Array<u64>>, hi: u64, k: u64) -> Rc<Array<u64>> {
  copy_loop(src, dst, hi, k, ())
}

// Rocq: Addemup.addemup_implem.copy_loop (local: copy_loop)
// Variant: uncurried, lifted
pub fn copy_loop(src: Rc<Array<u64>>, dst: Rc<Array<u64>>, hi: u64, k: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&src, k);
      let tmp_2 = rocq_array::set::<u64>(dst, k, tmp_1);
      copy_loop(src, tmp_2, hi, add(k, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Addemup.addemup_implem.msort
// Variant: uncurried
pub fn msort_1(a: Rc<Array<u64>>, b: Rc<Array<u64>>, lo: u64, hi: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  msort(a, b, lo, hi, ())
}

// Rocq: Addemup.addemup_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(a: Rc<Array<u64>>, b: Rc<Array<u64>>, lo: u64, hi: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(lo, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = ltb(1u64, sub(hi, lo));
      match bdec(tmp_1) {
        sumbool::left => {
          let tmp_2 = sub(hi, lo);
          let mid = add(lo, div(tmp_2, 2u64));
          let tmp_3 = msort(a, b, lo, mid, ());
          match &tmp_3 {
            (b1, a1) => {
              let tmp_4 = ();
              let b1_clone = Rc::clone(b1);
              let a1_clone = Rc::clone(a1);
              std::mem::drop(tmp_3);
              let tmp_5 = msort(b1_clone, a1_clone, mid, hi, tmp_4);
              match tmp_5 {
                (v90, v92) => {
                  let b2 = &v90;
                  let b2_clone = Rc::clone(b2);
                  let b3 = merge_loop_1(b2_clone, v92, lo, mid, mid, hi, lo);
                  let b3_clone = Rc::clone(&b3);
                  let tmp_6 = copy_loop_1(b3_clone, v90, hi, lo);
                  (tmp_6, b3)
                },
              }
            },
          }
        },
        sumbool::right => {
          (a, b)
        },
      }
    },
    sumbool::right => {
      (a, b)
    },
  }
}

// Rocq: Addemup.addemup_implem.lbloop
// Variant: uncurried
pub fn lbloop_1(S: Rc<Array<u64>>, x: u64, lo: u64, hi: u64) -> u64 {
  lbloop(S, x, lo, hi, ())
}

// Rocq: Addemup.addemup_implem.lbloop (local: lbloop)
// Variant: uncurried, lifted
pub fn lbloop(S: Rc<Array<u64>>, x: u64, lo: u64, hi: u64, _H: ()) -> u64 {
  let tmp = ltb(lo, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = sub(hi, lo);
      let tmp_2 = rocq_array::get::<u64>(&S, add(lo, div(tmp_1, 2u64)));
      if ltb(tmp_2, x) {
        let tmp_3 = sub(hi, lo);
        let tmp_4 = add(lo, div(tmp_3, 2u64));
        lbloop(S, x, add(tmp_4, 1u64), hi, ())
      } else {
        let tmp_5 = sub(hi, lo);
        let tmp_6 = add(lo, div(tmp_5, 2u64));
        lbloop(S, x, lo, tmp_6, ())
      }
    },
    sumbool::right => {
      std::mem::drop(S);
      lo
    },
  }
}

// Rocq: Addemup.addemup_implem.inrange
// Variant: uncurried
pub fn inrange(S: Rc<Array<u64>>, m: u64, lo: u64, hi: u64) -> bool {
  let S_clone = Rc::clone(&S);
  let p = lbloop_1(S_clone, lo, 0u64, m);
  if ltb(p, m) {
    let tmp = rocq_array::get::<u64>(&S, p);
    std::mem::drop(S);
    ltb(tmp, hi)
  } else {
    std::mem::drop(S);
    false
  }
}

// Rocq: Addemup.addemup_implem.found
// Variant: uncurried
pub fn found(S: Rc<Array<u64>>, m: u64, w: u64, i: u64) -> bool {
  let tmp = mul(w, __rocq_global_68);
  let tmp_1 = add(mul(w, __rocq_global_68), i);
  let S_clone = Rc::clone(&S);
  if inrange(S_clone, m, tmp, tmp_1) {
    std::mem::drop(S);
    true
  } else {
    let tmp_2 = add(mul(w, __rocq_global_68), i);
    inrange(S, m, add(tmp_2, 1u64), mul(add(w, 1u64), __rocq_global_68))
  }
}

// Rocq: Addemup.addemup_implem.okv
// Variant: uncurried
pub fn okv(S: Rc<Array<u64>>, m: u64, s: u64, v: u64, i: u64) -> bool {
  if leb(v, s) {
    found(S, m, sub(s, v), i)
  } else {
    std::mem::drop(S);
    false
  }
}

// Rocq: Addemup.addemup_implem.scan
// Variant: uncurried
pub fn scan_1(y: Rc<Array<u64>>, S: Rc<Array<u64>>, s: u64, m: u64, n: u64, i: u64) -> bool {
  scan(y, S, s, m, n, i, ())
}

// Rocq: Addemup.addemup_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(y: Rc<Array<u64>>, S: Rc<Array<u64>>, s: u64, m: u64, n: u64, i: u64, _H: ()) -> bool {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let c = rocq_array::get::<u64>(&y, i);
      let S_clone = Rc::clone(&S);
      if okv(S_clone, m, s, c, i) {
        std::mem::drop(y);
        std::mem::drop(S);
        true
      } else {
        let tmp_1 = alt(c);
        let S_clone_1 = Rc::clone(&S);
        if okv(S_clone_1, m, s, tmp_1, i) {
          std::mem::drop(y);
          std::mem::drop(S);
          true
        } else {
          scan(y, S, s, m, n, add(i, 1u64), ())
        }
      }
    },
    sumbool::right => {
      std::mem::drop(y);
      std::mem::drop(S);
      false
    },
  }
}

// Rocq: Addemup.addemup_implem.addemup_impl
// Variant: uncurried
pub fn addemup_impl(s: u64, y: Rc<Array<u64>>) -> bool {
  let n = rocq_array::length::<u64>(&y);
  let m = mul(2u64, n);
  let tmp = rocq_array::make::<u64>(m, 0u64);
  let y_clone = Rc::clone(&y);
  let T = build_1(y_clone, tmp, n, 0u64);
  let tmp_1 = rocq_array::make::<u64>(m, 0u64);
  let S = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(msort_1(T, tmp_1, 0u64, m));
  scan_1(y, S, s, m, n, 0u64)
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
const __rocq_global_68: u64 = 131072u64;