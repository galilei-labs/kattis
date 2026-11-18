#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
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

// Rocq: Numbersetshard.numbersetshard_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Numbersetshard.numbersetshard_implem.mark
// Variant: uncurried
pub fn mark_1(c: Rc<Array<bool>>, i: u64, cnt: u64, t: u64, j: u64) -> Rc<Array<bool>> {
  mark(c, i, cnt, t, j, ())
}

// Rocq: Numbersetshard.numbersetshard_implem.mark (local: mark)
// Variant: uncurried, lifted
pub fn mark(c: Rc<Array<bool>>, i: u64, cnt: u64, t: u64, j: u64, _H: ()) -> Rc<Array<bool>> {
  let tmp = ltb(t, cnt);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::set::<bool>(c, j, true);
      let tmp_2 = add(t, 1u64);
      let tmp_3 = add(j, i);
      mark(tmp_1, i, cnt, tmp_2, tmp_3, ())
    },
    sumbool::right => {
      c
    },
  }
}

// Rocq: Numbersetshard.numbersetshard_implem.mark_from
// Variant: uncurried
pub fn mark_from(c: Rc<Array<bool>>, w: u64, i: u64) -> Rc<Array<bool>> {
  let s = mul(i, i);
  let cnt = add(div(sub(w, s), i), 1u64);
  mark_1(c, i, cnt, 0u64, s)
}

// Rocq: Numbersetshard.numbersetshard_implem.sieve
// Variant: uncurried
pub fn sieve_1(c: Rc<Array<bool>>, w: u64, n: u64, i: u64) -> Rc<Array<bool>> {
  sieve(c, w, n, i, ())
}

// Rocq: Numbersetshard.numbersetshard_implem.sieve (local: sieve)
// Variant: uncurried, lifted
pub fn sieve(c: Rc<Array<bool>>, w: u64, n: u64, i: u64, _H: ()) -> Rc<Array<bool>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = mul(i, i);
      if leb(tmp_1, w) {
        let c_ref = &c;
        let tmp_2 = i;
        let tmp_3 = Clone::clone(&(c_ref)[tmp_2]);
        let c_ = if tmp_3 {
          c
        } else {
          mark_from(c, w, i)
        };
        sieve(c_, w, n, add(i, 1u64), ())
      } else {
        c
      }
    },
    sumbool::right => {
      c
    },
  }
}

// Rocq: Numbersetshard.numbersetshard_implem.iota
// Variant: uncurried
pub fn iota_1(par: Rc<Array<u64>>, n: u64, i: u64) -> Rc<Array<u64>> {
  iota(par, n, i, ())
}

// Rocq: Numbersetshard.numbersetshard_implem.iota (local: iota)
// Variant: uncurried, lifted
pub fn iota(par: Rc<Array<u64>>, n: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::set::<u64>(par, i, i);
      iota(tmp_1, n, add(i, 1u64), ())
    },
    sumbool::right => {
      par
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Numbersetshard.numbersetshard_implem.first_off
// Variant: uncurried
pub fn first_off(a: u64, q: u64) -> u64 {
  let tmp = mod_(a, q);
  mod_(sub(q, tmp), q)
}

// Rocq: Numbersetshard.numbersetshard_implem.find
// Variant: uncurried
pub fn find_1(par: Rc<Array<u64>>, rk: Rc<Array<u64>>, x: u64) -> (u64, Rc<Array<u64>>) {
  find(par, rk, x, ())
}

// Rocq: Numbersetshard.numbersetshard_implem.find (local: find)
// Variant: uncurried, lifted
pub fn find(par: Rc<Array<u64>>, rk: Rc<Array<u64>>, x: u64, _H: ()) -> (u64, Rc<Array<u64>>) {
  let par_ref = &par;
  let tmp = x;
  let y = Clone::clone(&(par_ref)[tmp]);
  if eqb(y, x) {
    std::mem::drop(rk);
    (x, par)
  } else {
    let par_ref_1 = &par;
    let tmp_1 = y;
    let z = Clone::clone(&(par_ref_1)[tmp_1]);
    let rk_ref = &rk;
    let tmp_2 = x;
    let tmp_3 = Clone::clone(&(rk_ref)[tmp_2]);
    let rk_ref_1 = &rk;
    let tmp_4 = z;
    let tmp_5 = Clone::clone(&(rk_ref_1)[tmp_4]);
    let tmp_6 = ltb(tmp_3, tmp_5);
    match bdec(tmp_6) {
      sumbool::left => {
        let tmp_7 = rocq_array::set::<u64>(par, x, z);
        find(tmp_7, rk, z, ())
      },
      sumbool::right => {
        std::mem::drop(rk);
        (x, par)
      },
    }
  }
}

// Rocq: Numbersetshard.numbersetshard_implem.union
// Variant: uncurried
pub fn union(par: Rc<Array<u64>>, rk: Rc<Array<u64>>, u: u64, v: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let rk_clone = Rc::clone(&rk);
  let tmp = find_1(par, rk_clone, u);
  match tmp {
    (v14, v16) => {
      let rk_clone_1 = Rc::clone(&rk);
      let tmp_1 = find_1(v16, rk_clone_1, v);
      match tmp_1 {
        (v28, v30) => {
          if eqb(v14, v28) {
            (v30, rk)
          } else {
            let rk_ref = &rk;
            let tmp_2 = v14;
            let ku = Clone::clone(&(rk_ref)[tmp_2]);
            let rk_ref_1 = &rk;
            let tmp_3 = v28;
            let kv = Clone::clone(&(rk_ref_1)[tmp_3]);
            if ltb(ku, kv) {
              let tmp_4 = rocq_array::set::<u64>(v30, v14, v28);
              (tmp_4, rk)
            } else {
              if ltb(kv, ku) {
                let tmp_5 = rocq_array::set::<u64>(v30, v28, v14);
                (tmp_5, rk)
              } else {
                let tmp_6 = rocq_array::set::<u64>(v30, v14, v28);
                let tmp_7 = rocq_array::set::<u64>(rk, v28, add(kv, 1u64));
                (tmp_6, tmp_7)
              }
            }
          }
        },
      }
    },
  }
}

// Rocq: Numbersetshard.numbersetshard_implem.ulink
// Variant: uncurried
pub fn ulink_1(par: Rc<Array<u64>>, rk: Rc<Array<u64>>, q: u64, cnt: u64, t: u64, o: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  ulink(par, rk, q, cnt, t, o, ())
}

// Rocq: Numbersetshard.numbersetshard_implem.ulink (local: ulink)
// Variant: uncurried, lifted
pub fn ulink(par: Rc<Array<u64>>, rk: Rc<Array<u64>>, q: u64, cnt: u64, t: u64, o: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(t, cnt);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(o, q);
      let tmp_2 = union(par, rk, o, tmp_1);
      match tmp_2 {
        (v35, v37) => {
          let tmp_3 = add(t, 1u64);
          let tmp_4 = add(o, q);
          ulink(v35, v37, q, cnt, tmp_3, tmp_4, ())
        },
      }
    },
    sumbool::right => {
      (par, rk)
    },
  }
}

// Rocq: Numbersetshard.numbersetshard_implem.uprimes
// Variant: uncurried
pub fn uprimes_1(c: Rc<Array<bool>>, a: u64, w: u64, n: u64, par: Rc<Array<u64>>, rk: Rc<Array<u64>>, q: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  uprimes(c, a, w, n, par, rk, q, ())
}

// Rocq: Numbersetshard.numbersetshard_implem.uprimes (local: uprimes)
// Variant: uncurried, lifted
pub fn uprimes(c: Rc<Array<bool>>, a: u64, w: u64, n: u64, par: Rc<Array<u64>>, rk: Rc<Array<u64>>, q: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(q, n);
  match bdec(tmp) {
    sumbool::left => {
      let c_ref = &c;
      let tmp_1 = q;
      let tmp_2 = Clone::clone(&(c_ref)[tmp_1]);
      let tmp_3 = if tmp_2 {
        (par, rk)
      } else {
        let o0 = first_off(a, q);
        let tmp_4 = div(sub(w, o0), q);
        ulink_1(par, rk, q, tmp_4, 0u64, o0)
      };
      match tmp_3 {
        (v70, v72) => {
          uprimes(c, a, w, n, v70, v72, add(q, 1u64), ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(c);
      (par, rk)
    },
  }
}

// Rocq: Numbersetshard.numbersetshard_implem.count
// Variant: uncurried
pub fn count_1(par: Rc<Array<u64>>, n: u64, o: u64, acc: u64) -> u64 {
  count(par, n, o, acc, ())
}

// Rocq: Numbersetshard.numbersetshard_implem.count (local: count)
// Variant: uncurried, lifted
pub fn count(par: Rc<Array<u64>>, n: u64, o: u64, acc: u64, _H: ()) -> u64 {
  let tmp = ltb(o, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(o, 1u64);
      let par_ref = &par;
      let tmp_2 = o;
      let tmp_3 = Clone::clone(&(par_ref)[tmp_2]);
      let tmp_4 = if eqb(tmp_3, o) {
        add(acc, 1u64)
      } else {
        acc
      };
      count(par, n, tmp_1, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(par);
      acc
    },
  }
}

// Rocq: Numbersetshard.numbersetshard_implem.numbersets_impl
// Variant: uncurried
pub fn numbersets_impl(x: u64, y: u64, z: u64) -> u64 {
  let w = sub(y, x);
  let n = add(w, 1u64);
  let tmp = rocq_array::make::<bool>(n, false);
  let c = sieve_1(tmp, w, n, 2u64);
  let tmp_1 = rocq_array::make::<u64>(n, 0u64);
  let par0 = iota_1(tmp_1, n, 0u64);
  let rk0 = rocq_array::make::<u64>(n, 0u64);
  let tmp_2 = uprimes_1(c, x, w, n, par0, rk0, z);
  match tmp_2 {
    (v77, v79) => {
      std::mem::drop(v79);
      count_1(v77, n, 0u64, 0u64)
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
