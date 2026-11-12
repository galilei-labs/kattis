// Generated from OwnedANF. This printer is not verified.
#[allow(unused_imports)] use std::rc::Rc;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = u64;

// Rocq: Remainderreminder.remainderreminder_implem.remainderreminder
// Variant: uncurried
pub fn remainderreminder() -> Rc<dyn Fn(u64, u64, u64, u64, u64, u64, u64) -> u64> {
  let v0: fn(u64, u64, u64, u64, u64, u64, u64) -> u64 = rr_impl;
  let v1: Rc<dyn Fn(u64, u64, u64, u64, u64, u64, u64) -> u64> = Rc::new(v0);
  v1
}

// Rocq: Remainderreminder.remainderreminder_implem.remainderreminder
pub fn remainderreminder_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>>>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>>>>> = rr_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>>>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
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

// Rocq: Remainderreminder.remainderreminder_implem.bdec
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

// Rocq: Remainderreminder.remainderreminder_implem.upd
// Variant: uncurried
pub fn upd(t: ((u64, u64), u64), v: u64) -> ((u64, u64), u64) {
  match &t {
    (t3, p) => {
      match t3 {
        (t2, t1) => {
          let v15 = Clone::clone(t2);
          match ltb(v15, v) {
            true => {
              let v27 = (v, Clone::clone(t2));
              let v28 = Clone::clone(t1);
              std::mem::drop(t);
              (v27, v28)
            },
            false => {
              let v38 = Clone::clone(t2);
              match eqb(v, v38) {
                true => {
                  t
                },
                false => {
                  let v45 = Clone::clone(t1);
                  match ltb(v45, v) {
                    true => {
                      let v57 = (Clone::clone(t2), v);
                      let v58 = Clone::clone(t1);
                      std::mem::drop(t);
                      (v57, v58)
                    },
                    false => {
                      let v68 = Clone::clone(t1);
                      match eqb(v, v68) {
                        true => {
                          t
                        },
                        false => {
                          let v75 = Clone::clone(p);
                          match ltb(v75, v) {
                            true => {
                              let v81 = Clone::clone(t2);
                              let v82 = Clone::clone(t1);
                              std::mem::drop(t);
                              ((v81, v82), v)
                            },
                            false => {
                              t
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Remainderreminder.remainderreminder_implem.vol
// Variant: uncurried
pub fn vol(a: u64, b: u64, x: u64) -> u64 {
  let v13 = mul(2u64, x);
  let v23 = mul(x, sub(a, v13));
  let v32 = mul(2u64, x);
  mul(v23, sub(b, v32))
}

// Rocq: Remainderreminder.remainderreminder_implem.scan
// Variant: uncurried
pub fn scan_1(a: u64, b: u64, m: u64, x: u64, t: ((u64, u64), u64)) -> ((u64, u64), u64) {
  scan(a, b, m, x, t, ())
}

// Rocq: Remainderreminder.remainderreminder_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(a: u64, b: u64, m: u64, x: u64, t: ((u64, u64), u64), _H: ()) -> ((u64, u64), u64) {
  let v13 = ltb(x, m);
  match bdec(v13) {
    sumbool::left => {
      let v24 = add(x, 1u64);
      let v33 = vol(a, b, x);
      scan(a, b, m, v24, upd(t, v33), ())
    },
    sumbool::right => {
      t
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Remainderreminder.remainderreminder_implem.egcd
// Variant: uncurried
pub fn egcd_1(m: u64, r0: u64, s0: u64, r1: u64, s1: u64) -> (u64, u64) {
  egcd(m, r0, s0, r1, s1, ())
}

// Rocq: Remainderreminder.remainderreminder_implem.egcd (local: egcd)
// Variant: uncurried, lifted
pub fn egcd(m: u64, r0: u64, s0: u64, r1: u64, s1: u64, _H: ()) -> (u64, u64) {
  let v15 = eqb(r1, 0u64);
  match bdec(v15) {
    sumbool::left => {
      (r0, s0)
    },
    sumbool::right => {
      let v32 = mod_(r0, r1);
      let v40 = add(s0, m);
      let v55 = mod_(div(r0, r1), m);
      let v64 = mod_(mul(v55, s1), m);
      let v74 = mod_(sub(v40, v64), m);
      egcd(m, r1, s1, v32, v74, ())
    },
  }
}

// Rocq: Remainderreminder.remainderreminder_implem.merge
// Variant: uncurried
pub fn merge(r1: u64, m1: u64, r2: u64, m2: u64) -> (u64, u64) {
  let v12 = mod_(1u64, m2);
  let v25 = egcd_1(m2, m1, v12, m2, 0u64);
  match v25 {
    (v27, v29) => {
      let v38 = add(r2, m2);
      let v44 = mod_(r1, m2);
      let dd = mod_(sub(v38, v44), m2);
      let v61 = mod_(dd, v27);
      match eqb(v61, 0u64) {
        true => {
          let m2_ = div(m2, v27);
          let v91 = mul(div(dd, v27), v29);
          (add(r1, mul(m1, mod_(v91, m2_))), mul(m1, m2_))
        },
        false => {
          (0u64, 0u64)
        },
      }
    },
  }
}

// Rocq: Remainderreminder.remainderreminder_implem.lift
// Variant: uncurried
pub fn lift(f: u64, r: u64, l: u64) -> u64 {
  let v11 = add(r, l);
  let v17 = mod_(f, l);
  add(f, mod_(sub(v11, v17), l))
}

// Rocq: Remainderreminder.remainderreminder_implem.rr_impl
// Variant: uncurried
pub fn rr_impl(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, _g: u64) -> u64 {
  let m = div(add(a, 1u64), 2u64);
  let v54 = scan_1(a, b, m, 1u64, ((0u64, 0u64), 0u64));
  match v54 {
    (v56, v58) => {
      match v56 {
        (v61, v63) => {
          let v74 = merge(c, v61, d, v63);
          match &v74 {
            (l12, r12) => {
              let v83 = Clone::clone(l12);
              let v84 = Clone::clone(r12);
              std::mem::drop(v74);
              let v90 = merge(v83, v84, e, v58);
              match v90 {
                (v92, v94) => {
                  lift(f, v92, v94)
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Remainderreminder.remainderreminder_implem.rr_impl
pub fn rr_impl_curried(a: u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>>>>> {
  let v3 = {
    move |b: u64| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>>>> {
      let a = &a;
      let v8 = Clone::clone(a);
      let v11 = {
        move |c: u64| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>>> {
          let a = &v8;
          let b = &b;
          let v18 = Clone::clone(a);
          let v20 = Clone::clone(b);
          let v23 = {
            move |d: u64| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>> {
              let a = &v18;
              let b = &v20;
              let c = &c;
              let v32 = Clone::clone(a);
              let v34 = Clone::clone(b);
              let v36 = Clone::clone(c);
              let v39 = {
                move |e: u64| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>> {
                  let a = &v32;
                  let b = &v34;
                  let c = &v36;
                  let d = &d;
                  let v50 = Clone::clone(a);
                  let v52 = Clone::clone(b);
                  let v54 = Clone::clone(c);
                  let v56 = Clone::clone(d);
                  let v59 = {
                    move |f: u64| -> Rc<dyn Fn(u64) -> u64> {
                      let a = &v50;
                      let b = &v52;
                      let c = &v54;
                      let d = &v56;
                      let e = &e;
                      let v72 = Clone::clone(a);
                      let v74 = Clone::clone(b);
                      let v76 = Clone::clone(c);
                      let v78 = Clone::clone(d);
                      let v80 = Clone::clone(e);
                      let v83 = {
                        move |g: u64| -> u64 {
                          let v99 = Clone::clone(&v72);
                          let v101 = Clone::clone(&v74);
                          let v103 = Clone::clone(&v76);
                          let v105 = Clone::clone(&v78);
                          let v107 = Clone::clone(&v80);
                          let v109 = Clone::clone(&f);
                          rr_impl(v99, v101, v103, v105, v107, v109, g)
                        }
                      };
                      let v115: Rc<dyn Fn(u64) -> u64> = Rc::new(v83);
                      v115
                    }
                  };
                  let v119: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>> = Rc::new(v59);
                  v119
                }
              };
              let v123: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>> = Rc::new(v39);
              v123
            }
          };
          let v127: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>>> = Rc::new(v23);
          v127
        }
      };
      let v131: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>>>> = Rc::new(v11);
      v131
    }
  };
  let v135: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>>>>> = Rc::new(v3);
  v135
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

pub fn run() -> Rc<dyn Fn(u64, u64, u64, u64, u64, u64, u64) -> u64> {
  let v0: Rc<dyn Fn(u64, u64, u64, u64, u64, u64, u64) -> u64> = __rocq_global_419.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_419: Rc<dyn Fn(u64, u64, u64, u64, u64, u64, u64) -> u64> = remainderreminder(); }
std::thread_local! { static __rocq_global_422: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>>>>>> = remainderreminder_curried(); }