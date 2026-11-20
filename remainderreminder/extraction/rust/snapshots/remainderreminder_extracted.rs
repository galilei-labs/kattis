#[allow(unused_imports)] use std::rc::Rc;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = u64;

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
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Remainderreminder.remainderreminder_implem.upd
// Variant: uncurried
pub fn upd(t: ((u64, u64), u64), v: u64) -> ((u64, u64), u64) {
  match &t {
    (t3, p) => {
      match t3 {
        (t2, t1) => {
          let t2_clone = Clone::clone(t2);
          if ltb(t2_clone, v) {
            let tmp = (v, Clone::clone(t2));
            let t1_clone = Clone::clone(t1);
            std::mem::drop(t);
            (tmp, t1_clone)
          } else {
            let t2_clone_1 = Clone::clone(t2);
            if eqb(v, t2_clone_1) {
              t
            } else {
              let t1_clone_1 = Clone::clone(t1);
              if ltb(t1_clone_1, v) {
                let tmp_1 = (Clone::clone(t2), v);
                let t1_clone_2 = Clone::clone(t1);
                std::mem::drop(t);
                (tmp_1, t1_clone_2)
              } else {
                let t1_clone_3 = Clone::clone(t1);
                if eqb(v, t1_clone_3) {
                  t
                } else {
                  let p_clone = Clone::clone(p);
                  if ltb(p_clone, v) {
                    let t2_clone_2 = Clone::clone(t2);
                    let t1_clone_4 = Clone::clone(t1);
                    std::mem::drop(t);
                    ((t2_clone_2, t1_clone_4), v)
                  } else {
                    t
                  }
                }
              }
            }
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
  let tmp = mul(2u64, x);
  let tmp_1 = mul(x, sub(a, tmp));
  let tmp_2 = mul(2u64, x);
  mul(tmp_1, sub(b, tmp_2))
}

// Rocq: Remainderreminder.remainderreminder_implem.scan
// Variant: uncurried
pub fn scan_1(a: u64, b: u64, m: u64, x: u64, t: ((u64, u64), u64)) -> ((u64, u64), u64) {
  scan(a, b, m, x, t, ())
}

// Rocq: Remainderreminder.remainderreminder_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(a: u64, b: u64, m: u64, x: u64, t: ((u64, u64), u64), _H: ()) -> ((u64, u64), u64) {
  let tmp = ltb(x, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(x, 1u64);
      let tmp_2 = vol(a, b, x);
      scan(a, b, m, tmp_1, upd(t, tmp_2), ())
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
  let tmp = eqb(r1, 0u64);
  match bdec(tmp) {
    sumbool::left => {
      (r0, s0)
    },
    sumbool::right => {
      let tmp_1 = mod_(r0, r1);
      let tmp_2 = add(s0, m);
      let tmp_3 = mod_(div(r0, r1), m);
      let tmp_4 = mod_(mul(tmp_3, s1), m);
      let tmp_5 = mod_(sub(tmp_2, tmp_4), m);
      egcd(m, r1, s1, tmp_1, tmp_5, ())
    },
  }
}

// Rocq: Remainderreminder.remainderreminder_implem.merge
// Variant: uncurried
pub fn merge(r1: u64, m1: u64, r2: u64, m2: u64) -> (u64, u64) {
  let tmp = mod_(1u64, m2);
  let tmp_1 = egcd_1(m2, m1, tmp, m2, 0u64);
  match tmp_1 {
    (v27, v29) => {
      let tmp_2 = add(r2, m2);
      let tmp_3 = mod_(r1, m2);
      let dd = mod_(sub(tmp_2, tmp_3), m2);
      let tmp_4 = mod_(dd, v27);
      if eqb(tmp_4, 0u64) {
        let m2_ = div(m2, v27);
        let tmp_5 = mul(div(dd, v27), v29);
        (add(r1, mul(m1, mod_(tmp_5, m2_))), mul(m1, m2_))
      } else {
        (0u64, 0u64)
      }
    },
  }
}

// Rocq: Remainderreminder.remainderreminder_implem.lift
// Variant: uncurried
pub fn lift(f: u64, r: u64, l: u64) -> u64 {
  let tmp = add(r, l);
  let tmp_1 = mod_(f, l);
  add(f, mod_(sub(tmp, tmp_1), l))
}

// Rocq: Remainderreminder.remainderreminder_implem.rr_impl
// Variant: uncurried
pub fn rr_impl(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, _g: u64) -> u64 {
  let m = div(add(a, 1u64), 2u64);
  let tmp = scan_1(a, b, m, 1u64, ((0u64, 0u64), 0u64));
  match tmp {
    (v56, v58) => {
      match v56 {
        (v61, v63) => {
          let tmp_1 = merge(c, v61, d, v63);
          match &tmp_1 {
            (l12, r12) => {
              let l12_clone = Clone::clone(l12);
              let r12_clone = Clone::clone(r12);
              std::mem::drop(tmp_1);
              let tmp_2 = merge(l12_clone, r12_clone, e, v58);
              match tmp_2 {
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
