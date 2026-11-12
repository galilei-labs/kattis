// Generated from OwnedANF. This printer is not verified.
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

// Rocq: Addemup.addemup_implem.addemup
// Variant: uncurried
pub fn addemup() -> Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> {
  let v0: fn(u64, Rc<Array<u64>>) -> bool = addemup_impl;
  let v1: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(v0);
  v1
}

// Rocq: Addemup.addemup_implem.addemup
pub fn addemup_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool> = addemup_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>> = Rc::new(v0);
  v1
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

// Rocq: Addemup.addemup_implem.rotd
pub fn rotd(d: u64) -> Rc<option<u64>> {
  match eqb(d, 0u64) {
    true => {
      Rc::new(option::<u64>::Some(0u64))
    },
    false => {
      match eqb(d, 1u64) {
        true => {
          Rc::new(option::<u64>::Some(1u64))
        },
        false => {
          match eqb(d, 2u64) {
            true => {
              Rc::new(option::<u64>::Some(2u64))
            },
            false => {
              match eqb(d, 5u64) {
                true => {
                  Rc::new(option::<u64>::Some(5u64))
                },
                false => {
                  match eqb(d, 6u64) {
                    true => {
                      Rc::new(option::<u64>::Some(9u64))
                    },
                    false => {
                      match eqb(d, 8u64) {
                        true => {
                          Rc::new(option::<u64>::Some(8u64))
                        },
                        false => {
                          match eqb(d, 9u64) {
                            true => {
                              Rc::new(option::<u64>::Some(6u64))
                            },
                            false => {
                              Rc::new(option::<u64>::None)
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
      }
    },
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
  let v12 = ltb(0u64, x);
  match bdec(v12) {
    sumbool::left => {
      let v27 = rotd(mod_(x, 10u64));
      let (v28, v29) = __rocq_reuse::reset(v27, |__payload| Clone::clone(__payload));
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
  let v8 = rloop_1(c, 0u64);
  let (v9, v10) = __rocq_reuse::reset(v8, |__payload| Clone::clone(__payload));
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
  let v12 = ltb(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v16 = &y;
      let c = rocq_array::get::<u64>(&v16, i);
      let v47 = rocq_array::set::<u64>(T, mul(2u64, i), add(mul(c, __rocq_global_68), i));
      let v87 = rocq_array::set::<u64>(v47, add(mul(2u64, i), 1u64), add(mul(alt(c), __rocq_global_68), i));
      build(y, v87, n, add(i, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(y);
      T
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
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
  let v15 = ltb(k, hi);
  match bdec(v15) {
    sumbool::left => {
      match ltb(i, mid) {
        true => {
          match ltb(j, hi) {
            true => {
              let v34 = &src;
              let v37 = rocq_array::get::<u64>(&v34, i);
              let v38 = &src;
              let v41 = rocq_array::get::<u64>(&v38, j);
              match leb(v37, v41) {
                true => {
                  let v48 = &src;
                  let v51 = rocq_array::get::<u64>(&v48, i);
                  let v58 = rocq_array::set::<u64>(dst, k, v51);
                  merge_loop(src, v58, add(i, 1u64), mid, j, hi, add(k, 1u64), ())
                },
                false => {
                  let v97 = &src;
                  let v100 = rocq_array::get::<u64>(&v97, j);
                  let v107 = rocq_array::set::<u64>(dst, k, v100);
                  merge_loop(src, v107, i, mid, add(j, 1u64), hi, add(k, 1u64), ())
                },
              }
            },
            false => {
              let v149 = &src;
              let v152 = rocq_array::get::<u64>(&v149, i);
              let v159 = rocq_array::set::<u64>(dst, k, v152);
              merge_loop(src, v159, add(i, 1u64), mid, j, hi, add(k, 1u64), ())
            },
          }
        },
        false => {
          let v201 = &src;
          let v204 = rocq_array::get::<u64>(&v201, j);
          let v211 = rocq_array::set::<u64>(dst, k, v204);
          merge_loop(src, v211, i, mid, add(j, 1u64), hi, add(k, 1u64), ())
        },
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
  let v12 = ltb(k, hi);
  match bdec(v12) {
    sumbool::left => {
      let v16 = &src;
      let v19 = rocq_array::get::<u64>(&v16, k);
      let v26 = rocq_array::set::<u64>(dst, k, v19);
      copy_loop(src, v26, hi, add(k, 1u64), ())
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
  let v12 = ltb(lo, hi);
  match bdec(v12) {
    sumbool::left => {
      let v31 = ltb(1u64, sub(hi, lo));
      match bdec(v31) {
        sumbool::left => {
          let v42 = sub(hi, lo);
          let mid = add(lo, div(v42, 2u64));
          let v68 = msort(a, b, lo, mid, ());
          match &v68 {
            (b1, a1) => {
              let v76 = ();
              let v79 = Rc::clone(b1);
              let v80 = Rc::clone(a1);
              std::mem::drop(v68);
              let v88 = msort(v79, v80, mid, hi, v76);
              match v88 {
                (v90, v92) => {
                  let b2 = &v90;
                  let v97 = Rc::clone(b2);
                  let b3 = merge_loop_1(v97, v92, lo, mid, mid, hi, lo);
                  let v114 = Rc::clone(&b3);
                  let v122 = copy_loop_1(v114, v90, hi, lo);
                  (v122, b3)
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
  let v12 = ltb(lo, hi);
  match bdec(v12) {
    sumbool::left => {
      let v24 = sub(hi, lo);
      let v36 = add(lo, div(v24, 2u64));
      let v37 = &S;
      let v41 = rocq_array::get::<u64>(&v37, v36);
      match ltb(v41, x) {
        true => {
          let v55 = sub(hi, lo);
          let v67 = add(lo, div(v55, 2u64));
          lbloop(S, x, add(v67, 1u64), hi, ())
        },
        false => {
          let v98 = sub(hi, lo);
          let v110 = add(lo, div(v98, 2u64));
          lbloop(S, x, lo, v110, ())
        },
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
  let v9 = Rc::clone(&S);
  let p = lbloop_1(v9, lo, 0u64, m);
  match ltb(p, m) {
    true => {
      let v25 = &S;
      let v28 = rocq_array::get::<u64>(&v25, p);
      std::mem::drop(S);
      ltb(v28, hi)
    },
    false => {
      std::mem::drop(S);
      false
    },
  }
}

// Rocq: Addemup.addemup_implem.found
// Variant: uncurried
pub fn found(S: Rc<Array<u64>>, m: u64, w: u64, i: u64) -> bool {
  let v11 = mul(w, __rocq_global_68);
  let v24 = add(mul(w, __rocq_global_68), i);
  let v27 = Rc::clone(&S);
  match inrange(v27, m, v11, v24) {
    true => {
      std::mem::drop(S);
      true
    },
    false => {
      let v54 = add(mul(w, __rocq_global_68), i);
      inrange(S, m, add(v54, 1u64), mul(add(w, 1u64), __rocq_global_68))
    },
  }
}

// Rocq: Addemup.addemup_implem.okv
// Variant: uncurried
pub fn okv(S: Rc<Array<u64>>, m: u64, s: u64, v: u64, i: u64) -> bool {
  match leb(v, s) {
    true => {
      found(S, m, sub(s, v), i)
    },
    false => {
      std::mem::drop(S);
      false
    },
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
  let v14 = ltb(i, n);
  match bdec(v14) {
    sumbool::left => {
      let v18 = &y;
      let c = rocq_array::get::<u64>(&v18, i);
      let v25 = Rc::clone(&S);
      match okv(v25, m, s, c, i) {
        true => {
          std::mem::drop(y);
          std::mem::drop(S);
          true
        },
        false => {
          let v44 = alt(c);
          let v47 = Rc::clone(&S);
          match okv(v47, m, s, v44, i) {
            true => {
              std::mem::drop(y);
              std::mem::drop(S);
              true
            },
            false => {
              scan(y, S, s, m, n, add(i, 1u64), ())
            },
          }
        },
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
  let v2 = &y;
  let n = rocq_array::length::<u64>(&v2);
  let m = mul(2u64, n);
  let v19 = rocq_array::make::<u64>(m, 0u64);
  let v24 = Rc::clone(&y);
  let T = build_1(v24, v19, n, 0u64);
  let v40 = rocq_array::make::<u64>(m, 0u64);
  let S = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(msort_1(T, v40, 0u64, m));
  scan_1(y, S, s, m, n, 0u64)
}

// Rocq: Addemup.addemup_implem.addemup_impl
pub fn addemup_impl_curried(s: u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool> {
  let v3 = {
    move |y: Rc<Array<u64>>| -> bool {
      let v9 = Clone::clone(&s);
      addemup_impl(v9, y)
    }
  };
  let v15: Rc<dyn Fn(Rc<Array<u64>>) -> bool> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> {
  let v0: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = __rocq_global_785.with(Clone::clone);
  v0
}
const __rocq_global_68: u64 = 131072u64;
std::thread_local! { static __rocq_global_785: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = addemup(); }
std::thread_local! { static __rocq_global_788: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> bool>> = addemup_curried(); }