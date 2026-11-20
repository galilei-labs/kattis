#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type buffer = (Rc<Array<u64>>, Rc<Array<u64>>);

pub type char63 = u64;

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: Rc<rocq_string::RocqString>) -> u64 {
  let tmp = rocq_string::length(&v0);
  std::mem::drop(v0);
  tmp
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Stringmatching.stringmatching_implem.bmake
pub fn bmake(n: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let tmp_1 = 4194303u64;
  let tmp_2 = if ltb(tmp_1, n) {
    sub(n, 4194303u64)
  } else {
    0u64
  };
  let tmp_3 = rocq_array::make::<u64>(tmp_2, 0u64);
  (tmp, tmp_3)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
}

// Rocq: Stringmatching.stringmatching_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let tmp = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Stringmatching.stringmatching_implem.fall
// Variant: uncurried
pub fn fall_1(xp: Rc<rocq_string::RocqString>, tbl: Rc<Array<u64>>, c: u64, q: u64) -> u64 {
  fall(xp, tbl, c, q, ())
}

// Rocq: Stringmatching.stringmatching_implem.fall (local: fall)
// Variant: uncurried, lifted
pub fn fall(xp: Rc<rocq_string::RocqString>, tbl: Rc<Array<u64>>, c: u64, q: u64, _H: ()) -> u64 {
  let xp_clone = Rc::clone(&xp);
  let tmp = get(xp_clone, q);
  if eqb(tmp, c) {
    std::mem::drop(xp);
    std::mem::drop(tbl);
    add(q, 1u64)
  } else {
    let tmp_1 = ltb(0u64, q);
    match bdec(tmp_1) {
      sumbool::left => {
        let q_ = rocq_array::get::<u64>(&tbl, sub(q, 1u64));
        let tmp_2 = ltb(q_, q);
        match bdec(tmp_2) {
          sumbool::left => {
            fall(xp, tbl, c, q_, ())
          },
          sumbool::right => {
            std::mem::drop(xp);
            std::mem::drop(tbl);
            0u64
          },
        }
      },
      sumbool::right => {
        std::mem::drop(xp);
        std::mem::drop(tbl);
        0u64
      },
    }
  }
}

// Rocq: Stringmatching.stringmatching_implem.build
// Variant: uncurried
pub fn build_1(xp: Rc<rocq_string::RocqString>, m: u64, tbl: Rc<Array<u64>>, i: u64, q: u64) -> Rc<Array<u64>> {
  build(xp, m, tbl, i, q, ())
}

// Rocq: Stringmatching.stringmatching_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(xp: Rc<rocq_string::RocqString>, m: u64, tbl: Rc<Array<u64>>, i: u64, q: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, m);
  match bdec(tmp) {
    sumbool::left => {
      let xp_clone = Rc::clone(&xp);
      let tmp_1 = get(xp_clone, i);
      let xp_clone_1 = Rc::clone(&xp);
      let tbl_clone = Rc::clone(&tbl);
      let r = fall_1(xp_clone_1, tbl_clone, tmp_1, q);
      let tmp_2 = rocq_array::set::<u64>(tbl, i, r);
      build(xp, m, tmp_2, add(i, 1u64), r, ())
    },
    sumbool::right => {
      std::mem::drop(xp);
      tbl
    },
  }
}

// Rocq: Stringmatching.stringmatching_implem.alen
pub fn alen_owned(a: Rc<Array<u64>>) -> u64 {
  let tmp = rocq_array::length::<u64>(&a);
  std::mem::drop(a);
  tmp
}

// Rocq: Stringmatching.stringmatching_implem.alen
// Variant: borrowed
pub fn alen(a: &Rc<Array<u64>>) -> u64 {
  rocq_array::length::<u64>(a)
}

// Rocq: Stringmatching.stringmatching_implem.bset
// Variant: uncurried
pub fn bset(t: (Rc<Array<u64>>, Rc<Array<u64>>), i: u64, v: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  match t {
    (v4, v6) => {
      let b = &v4;
      let tmp = alen(b);
      if ltb(i, tmp) {
        let tmp_1 = rocq_array::set::<u64>(v4, i, v);
        (tmp_1, v6)
      } else {
        let tmp_2 = alen(b);
        let tmp_3 = rocq_array::set::<u64>(v6, sub(i, tmp_2), v);
        (v4, tmp_3)
      }
    },
  }
}

// Rocq: Stringmatching.stringmatching_implem.bget
// Variant: uncurried
pub fn bget(t: (Rc<Array<u64>>, Rc<Array<u64>>), i: u64) -> u64 {
  match t {
    (v3, v5) => {
      let b = &v3;
      let a = &v5;
      let tmp = alen(b);
      if ltb(i, tmp) {
        std::mem::drop(v5);
        let tmp_1 = rocq_array::get::<u64>(b, i);
        std::mem::drop(v3);
        tmp_1
      } else {
        let tmp_2 = rocq_array::get::<u64>(a, sub(i, alen_owned(v3)));
        std::mem::drop(v5);
        tmp_2
      }
    },
  }
}

// Rocq: Stringmatching.stringmatching_implem.copy
// Variant: uncurried
pub fn copy_1(buf: (Rc<Array<u64>>, Rc<Array<u64>>), res: (Rc<Array<u64>>, Rc<Array<u64>>), c: u64, k: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  copy(buf, res, c, k, ())
}

// Rocq: Stringmatching.stringmatching_implem.copy (local: copy)
// Variant: uncurried, lifted
pub fn copy(buf: (Rc<Array<u64>>, Rc<Array<u64>>), res: (Rc<Array<u64>>, Rc<Array<u64>>), c: u64, k: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(k, c);
  match bdec(tmp) {
    sumbool::left => {
      let buf_clone = Clone::clone(&buf);
      let tmp_1 = bget(buf_clone, k);
      copy(buf, bset(res, k, tmp_1), c, add(k, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(buf);
      res
    },
  }
}

// Rocq: Stringmatching.stringmatching_implem.scan
// Variant: uncurried
pub fn scan_1(xp: Rc<rocq_string::RocqString>, xt: Rc<rocq_string::RocqString>, tbl: Rc<Array<u64>>, m: u64, n: u64, buf: (Rc<Array<u64>>, Rc<Array<u64>>), i: u64, q: u64, cnt: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  scan(xp, xt, tbl, m, n, buf, i, q, cnt, ())
}

// Rocq: Stringmatching.stringmatching_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(xp: Rc<rocq_string::RocqString>, xt: Rc<rocq_string::RocqString>, tbl: Rc<Array<u64>>, m: u64, n: u64, buf: (Rc<Array<u64>>, Rc<Array<u64>>), i: u64, q: u64, cnt: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let xt_clone = Rc::clone(&xt);
      let tmp_1 = get(xt_clone, i);
      let xp_clone = Rc::clone(&xp);
      let tbl_clone = Rc::clone(&tbl);
      let r = fall_1(xp_clone, tbl_clone, tmp_1, q);
      if eqb(r, m) {
        let tmp_2 = bset(buf, cnt, sub(add(i, 1u64), m));
        let tmp_3 = add(i, 1u64);
        let tmp_4 = rocq_array::get::<u64>(&tbl, sub(m, 1u64));
        scan(xp, xt, tbl, m, n, tmp_2, tmp_3, tmp_4, add(cnt, 1u64), ())
      } else {
        scan(xp, xt, tbl, m, n, buf, add(i, 1u64), r, cnt, ())
      }
    },
    sumbool::right => {
      std::mem::drop(xp);
      std::mem::drop(xt);
      std::mem::drop(tbl);
      copy_1(buf, bmake(cnt), cnt, 0u64)
    },
  }
}

// Rocq: Stringmatching.stringmatching_implem.find_all_impl
// Variant: uncurried
pub fn find_all_impl(xp: Rc<rocq_string::RocqString>, xt: Rc<rocq_string::RocqString>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let xp_clone = Rc::clone(&xp);
  let m = length(xp_clone);
  let xt_clone = Rc::clone(&xt);
  let n = length(xt_clone);
  if ltb(n, m) {
    std::mem::drop(xp);
    std::mem::drop(xt);
    bmake(0u64)
  } else {
    let tmp = rocq_array::make::<u64>(m, 0u64);
    let xp_clone_1 = Rc::clone(&xp);
    let tbl = build_1(xp_clone_1, m, tmp, 1u64, 0u64);
    let tmp_1 = sub(n, m);
    scan_1(xp, xt, tbl, m, n, bmake(add(tmp_1, 1u64)), 0u64, 0u64, 0u64)
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
