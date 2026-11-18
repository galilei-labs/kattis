#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<std::cmp::Ordering>; };

pub type uint = u64;

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

// Rocq: Committeeassignment.committeeassignment_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Strings.PrimString.compare
// Variant: uncurried
pub fn compare(v0: Rc<rocq_string::RocqString>, v1: Rc<rocq_string::RocqString>) -> std::cmp::Ordering {
  let tmp = rocq_string::compare(&v0, &v1);
  std::mem::drop(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Committeeassignment.committeeassignment_implem.midp
// Variant: uncurried
pub fn midp(lo: u64, hi: u64) -> u64 {
  let tmp = sub(hi, lo);
  add(lo, div(tmp, 2u64))
}

// Rocq: Committeeassignment.committeeassignment_implem.lb
// Variant: uncurried
pub fn lb_1(K: Rc<Array<Rc<rocq_string::RocqString>>>, s: Rc<rocq_string::RocqString>, lo: u64, hi: u64) -> u64 {
  lb(K, s, lo, hi, ())
}

// Rocq: Committeeassignment.committeeassignment_implem.lb (local: lb)
// Variant: uncurried, lifted
pub fn lb(K: Rc<Array<Rc<rocq_string::RocqString>>>, s: Rc<rocq_string::RocqString>, lo: u64, hi: u64, _H: ()) -> u64 {
  let tmp = ltb(lo, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<Rc<rocq_string::RocqString>>(&K, midp(lo, hi));
      let s_clone = Rc::clone(&s);
      match compare(tmp_1, s_clone) {
        std::cmp::Ordering::Equal => {
          let tmp_2 = midp(lo, hi);
          lb(K, s, lo, tmp_2, ())
        },
        std::cmp::Ordering::Less => {
          lb(K, s, add(midp(lo, hi), 1u64), hi, ())
        },
        std::cmp::Ordering::Greater => {
          let tmp_3 = midp(lo, hi);
          lb(K, s, lo, tmp_3, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(K);
      std::mem::drop(s);
      lo
    },
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.look
// Variant: uncurried
pub fn look(K: Rc<Array<Rc<rocq_string::RocqString>>>, p: u64, s: Rc<rocq_string::RocqString>) -> u64 {
  lb_1(K, s, 0u64, p)
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

// Rocq: Committeeassignment.committeeassignment_implem.is_eq
pub fn is_eq(c: std::cmp::Ordering) -> bool {
  match c {
    std::cmp::Ordering::Equal => {
      true
    },
    std::cmp::Ordering::Less => {
      false
    },
    std::cmp::Ordering::Greater => {
      false
    },
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.shift
// Variant: uncurried
pub fn shift_1(K: Rc<Array<Rc<rocq_string::RocqString>>>, t: u64, j: u64) -> Rc<Array<Rc<rocq_string::RocqString>>> {
  shift(K, t, j, ())
}

// Rocq: Committeeassignment.committeeassignment_implem.shift (local: shift)
// Variant: uncurried, lifted
pub fn shift(K: Rc<Array<Rc<rocq_string::RocqString>>>, t: u64, j: u64, _H: ()) -> Rc<Array<Rc<rocq_string::RocqString>>> {
  let tmp = ltb(t, j);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<Rc<rocq_string::RocqString>>(&K, sub(j, 1u64));
      let tmp_2 = rocq_array::set::<Rc<rocq_string::RocqString>>(K, j, tmp_1);
      shift(tmp_2, t, sub(j, 1u64), ())
    },
    sumbool::right => {
      K
    },
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.insert
// Variant: uncurried
pub fn insert(K: Rc<Array<Rc<rocq_string::RocqString>>>, p: u64, s: Rc<rocq_string::RocqString>) -> (Rc<Array<Rc<rocq_string::RocqString>>>, u64) {
  let K_clone = Rc::clone(&K);
  let s_clone = Rc::clone(&s);
  let t = look(K_clone, p, s_clone);
  let tmp = ltb(t, p);
  let tmp_1 = rocq_array::get::<Rc<rocq_string::RocqString>>(&K, t);
  let s_clone_1 = Rc::clone(&s);
  let tmp_2 = is_eq(compare(tmp_1, s_clone_1));
  if andb(tmp, tmp_2) {
    std::mem::drop(s);
    (K, p)
  } else {
    let tmp_3 = shift_1(K, t, p);
    let tmp_4 = rocq_array::set::<Rc<rocq_string::RocqString>>(tmp_3, t, s);
    (tmp_4, add(p, 1u64))
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.build
// Variant: uncurried
pub fn build_1(y: Rc<Array<Rc<rocq_string::RocqString>>>, z: Rc<Array<Rc<rocq_string::RocqString>>>, m: u64, i: u64, K: Rc<Array<Rc<rocq_string::RocqString>>>, p: u64) -> (Rc<Array<Rc<rocq_string::RocqString>>>, u64) {
  build(y, z, m, i, K, p, ())
}

// Rocq: Committeeassignment.committeeassignment_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(y: Rc<Array<Rc<rocq_string::RocqString>>>, z: Rc<Array<Rc<rocq_string::RocqString>>>, m: u64, i: u64, K: Rc<Array<Rc<rocq_string::RocqString>>>, p: u64, _H: ()) -> (Rc<Array<Rc<rocq_string::RocqString>>>, u64) {
  let tmp = ltb(i, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<Rc<rocq_string::RocqString>>(&y, i);
      let tmp_2 = insert(K, p, tmp_1);
      match &tmp_2 {
        (p1, K1) => {
          let tmp_3 = rocq_array::get::<Rc<rocq_string::RocqString>>(&z, i);
          let p1_clone = Rc::clone(p1);
          let K1_clone = Clone::clone(K1);
          std::mem::drop(tmp_2);
          let tmp_4 = insert(p1_clone, K1_clone, tmp_3);
          match tmp_4 {
            (v49, v51) => {
              build(y, z, m, add(i, 1u64), v49, v51, ())
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(y);
      std::mem::drop(z);
      (K, p)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Committeeassignment.committeeassignment_implem.fill
// Variant: uncurried
pub fn fill_1(y: Rc<Array<Rc<rocq_string::RocqString>>>, z: Rc<Array<Rc<rocq_string::RocqString>>>, K: Rc<Array<Rc<rocq_string::RocqString>>>, p: u64, m: u64, i: u64, tbl: Rc<Array<bool>>) -> Rc<Array<bool>> {
  fill(y, z, K, p, m, i, tbl, ())
}

// Rocq: Committeeassignment.committeeassignment_implem.fill (local: fill)
// Variant: uncurried, lifted
pub fn fill(y: Rc<Array<Rc<rocq_string::RocqString>>>, z: Rc<Array<Rc<rocq_string::RocqString>>>, K: Rc<Array<Rc<rocq_string::RocqString>>>, p: u64, m: u64, i: u64, tbl: Rc<Array<bool>>, _H: ()) -> Rc<Array<bool>> {
  let tmp = ltb(i, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<Rc<rocq_string::RocqString>>(&y, i);
      let K_clone = Rc::clone(&K);
      let u = look(K_clone, p, tmp_1);
      let tmp_2 = rocq_array::get::<Rc<rocq_string::RocqString>>(&z, i);
      let K_clone_1 = Rc::clone(&K);
      let v = look(K_clone_1, p, tmp_2);
      let tmp_3 = add(i, 1u64);
      let tmp_4 = rocq_array::set::<bool>(tbl, add(mul(u, p), v), true);
      let tmp_5 = rocq_array::set::<bool>(tmp_4, add(mul(v, p), u), true);
      fill(y, z, K, p, m, tmp_3, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(y);
      std::mem::drop(z);
      std::mem::drop(K);
      tbl
    },
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.lim
// Variant: uncurried
pub fn lim(used: u64, k: u64) -> u64 {
  if ltb(used, k) {
    add(used, 1u64)
  } else {
    k
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.okc
// Variant: uncurried
pub fn okc_1(tbl: Rc<Array<bool>>, p: u64, v: u64, c: u64, col: Rc<Array<u64>>, u: u64) -> bool {
  okc(tbl, p, v, c, col, u, ())
}

// Rocq: Committeeassignment.committeeassignment_implem.okc (local: okc)
// Variant: uncurried, lifted
pub fn okc(tbl: Rc<Array<bool>>, p: u64, v: u64, c: u64, col: Rc<Array<u64>>, u: u64, _H: ()) -> bool {
  let tmp = ltb(u, v);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<bool>(&tbl, add(mul(u, p), v));
      let tmp_2 = rocq_array::get::<u64>(&col, u);
      let tmp_3 = eqb(tmp_2, c);
      if andb(tmp_1, tmp_3) {
        std::mem::drop(col);
        std::mem::drop(tbl);
        false
      } else {
        okc(tbl, p, v, c, col, add(u, 1u64), ())
      }
    },
    sumbool::right => {
      std::mem::drop(tbl);
      std::mem::drop(col);
      true
    },
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.bump
// Variant: uncurried
pub fn bump(used: u64, c: u64) -> u64 {
  let tmp = add(c, 1u64);
  if ltb(used, tmp) {
    add(c, 1u64)
  } else {
    used
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.srch
// Variant: uncurried
pub fn srch_1(tbl: Rc<Array<bool>>, p: u64, k: u64, v: u64, c: u64, used: u64, col: Rc<Array<u64>>) -> (bool, Rc<Array<u64>>) {
  srch(tbl, p, k, v, c, used, col, ())
}

// Rocq: Committeeassignment.committeeassignment_implem.srch (local: srch)
// Variant: uncurried, lifted
pub fn srch(tbl: Rc<Array<bool>>, p: u64, k: u64, v: u64, c: u64, used: u64, col: Rc<Array<u64>>, _H: ()) -> (bool, Rc<Array<u64>>) {
  let tmp = ltb(v, p);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = ltb(c, lim(used, k));
      match bdec(tmp_1) {
        sumbool::left => {
          let tbl_clone = Rc::clone(&tbl);
          let col_clone = Rc::clone(&col);
          if okc_1(tbl_clone, p, v, c, col_clone, 0u64) {
            let tmp_2 = add(v, 1u64);
            let tmp_3 = bump(used, c);
            let tmp_4 = rocq_array::set::<u64>(col, v, c);
            let tbl_clone_1 = Rc::clone(&tbl);
            let tmp_5 = srch(tbl_clone_1, p, k, tmp_2, 0u64, tmp_3, tmp_4, ());
            match tmp_5 {
              (v100, v102) => {
                if v100 {
                  std::mem::drop(tbl);
                  (true, v102)
                } else {
                  srch(tbl, p, k, v, add(c, 1u64), used, v102, ())
                }
              },
            }
          } else {
            srch(tbl, p, k, v, add(c, 1u64), used, col, ())
          }
        },
        sumbool::right => {
          std::mem::drop(tbl);
          (false, col)
        },
      }
    },
    sumbool::right => {
      std::mem::drop(tbl);
      (true, col)
    },
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.deepen
// Variant: uncurried
pub fn deepen_1(tbl: Rc<Array<bool>>, p: u64, P: u64, k: u64, col: Rc<Array<u64>>) -> u64 {
  deepen(tbl, p, P, k, col, ())
}

// Rocq: Committeeassignment.committeeassignment_implem.deepen (local: deepen)
// Variant: uncurried, lifted
pub fn deepen(tbl: Rc<Array<bool>>, p: u64, P: u64, k: u64, col: Rc<Array<u64>>, _H: ()) -> u64 {
  let tmp = ltb(k, P);
  match bdec(tmp) {
    sumbool::left => {
      let tbl_clone = Rc::clone(&tbl);
      let tmp_1 = srch_1(tbl_clone, p, k, 0u64, 0u64, 0u64, col);
      match tmp_1 {
        (v41, v43) => {
          if v41 {
            std::mem::drop(tbl);
            std::mem::drop(v43);
            k
          } else {
            deepen(tbl, p, P, add(k, 1u64), v43, ())
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(tbl);
      std::mem::drop(col);
      P
    },
  }
}

// Rocq: Committeeassignment.committeeassignment_implem.committees_impl
// Variant: uncurried
pub fn committees_impl(_n: u64, y: Rc<Array<Rc<rocq_string::RocqString>>>, z: Rc<Array<Rc<rocq_string::RocqString>>>) -> u64 {
  let m = rocq_array::length::<Rc<rocq_string::RocqString>>(&y);
  let tmp = add(m, m);
  let tmp_1 = rocq_string::RocqString::from_bytes(vec![]);
  let tmp_2 = Rc::new(tmp_1);
  let tmp_3 = rocq_array::make::<Rc<rocq_string::RocqString>>(tmp, tmp_2);
  let y_clone = Rc::clone(&y);
  let z_clone = Rc::clone(&z);
  let tmp_4 = build_1(y_clone, z_clone, m, 0u64, tmp_3, 0u64);
  match tmp_4 {
    (v40, v42) => {
      let K = &v42;
      let tmp_5 = rocq_array::make::<bool>(mul(v42, v42), false);
      let tbl = fill_1(y, z, v40, v42, m, 0u64, tmp_5);
      let tmp_6 = 1u64;
      let P = if ltb(v42, tmp_6) {
        1u64
      } else {
        v42
      };
      let tmp_7 = rocq_array::make::<u64>(P, 0u64);
      let K_clone = Clone::clone(K);
      deepen_1(tbl, K_clone, P, 1u64, tmp_7)
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
