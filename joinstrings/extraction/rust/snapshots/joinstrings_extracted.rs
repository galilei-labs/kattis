#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

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

// Rocq: Joinstrings.joinstrings_implem.bdec
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

// Rocq: Joinstrings.joinstrings_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(n: u64, k: u64, tl: Rc<Array<u64>>) -> Rc<Array<u64>> {
  init_loop(n, k, tl, ())
}

// Rocq: Joinstrings.joinstrings_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(n: u64, k: u64, tl: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(k, 1u64);
      let tmp_2 = rocq_array::set::<u64>(tl, k, k);
      init_loop(n, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      tl
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Joinstrings.joinstrings_implem.ops_loop
// Variant: uncurried
pub fn ops_loop_1(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, m: u64, k: u64, nx: Rc<Array<u64>>, tl: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  ops_loop(xa, xb, m, k, nx, tl, ())
}

// Rocq: Joinstrings.joinstrings_implem.ops_loop (local: ops_loop)
// Variant: uncurried, lifted
pub fn ops_loop(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, m: u64, k: u64, nx: Rc<Array<u64>>, tl: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(k, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&xa, k);
      let x = sub(tmp_1, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&xb, k);
      let y = sub(tmp_2, 1u64);
      let ty = rocq_array::get::<u64>(&tl, y);
      let tx = rocq_array::get::<u64>(&tl, x);
      let tmp_3 = add(k, 1u64);
      let tmp_4 = rocq_array::set::<u64>(nx, tx, y);
      let tmp_5 = rocq_array::set::<u64>(tl, x, ty);
      ops_loop(xa, xb, m, tmp_3, tmp_4, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(xa);
      std::mem::drop(xb);
      (nx, tl)
    },
  }
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

// Rocq: Joinstrings.joinstrings_implem.root_of
// Variant: uncurried
pub fn root_of(xa: Rc<Array<u64>>, m: u64) -> u64 {
  if eqb(m, 0u64) {
    std::mem::drop(xa);
    0u64
  } else {
    let tmp = rocq_array::get::<u64>(&xa, sub(m, 1u64));
    std::mem::drop(xa);
    sub(tmp, 1u64)
  }
}

// Rocq: Joinstrings.joinstrings_implem.walk
// Variant: uncurried
pub fn walk_1(nx: Rc<Array<u64>>, t: u64, n: u64, cur: u64, i: u64, ord: Rc<Array<u64>>) -> (Rc<Array<u64>>, u64) {
  walk(nx, t, n, cur, i, ord, ())
}

// Rocq: Joinstrings.joinstrings_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(nx: Rc<Array<u64>>, t: u64, n: u64, cur: u64, i: u64, ord: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, u64) {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      if eqb(cur, t) {
        std::mem::drop(nx);
        let tmp_1 = rocq_array::set::<u64>(ord, i, cur);
        (tmp_1, add(i, 1u64))
      } else {
        let tmp_2 = rocq_array::get::<u64>(&nx, cur);
        let tmp_3 = add(i, 1u64);
        let tmp_4 = rocq_array::set::<u64>(ord, i, cur);
        walk(nx, t, n, tmp_2, tmp_3, tmp_4, ())
      }
    },
    sumbool::right => {
      std::mem::drop(nx);
      (ord, i)
    },
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

// Rocq: Joinstrings.joinstrings_implem.split_ok
// Variant: uncurried
pub fn split_ok(lo: u64, hi: u64) -> bool {
  andb(ltb(lo, hi), ltb(1u64, sub(hi, lo)))
}

// Rocq: Corelib.Strings.PrimString.cat
// Variant: uncurried
pub fn cat(v0: Rc<rocq_string::RocqString>, v1: Rc<rocq_string::RocqString>) -> Rc<rocq_string::RocqString> {
  let tmp = rocq_string::cat(&v0, &v1);
  std::mem::drop(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Joinstrings.joinstrings_implem.mid_of
// Variant: uncurried
pub fn mid_of(lo: u64, hi: u64) -> u64 {
  let tmp = sub(hi, lo);
  add(lo, div(tmp, 2u64))
}

// Rocq: Joinstrings.joinstrings_implem.build
// Variant: uncurried
pub fn build_1(xs: Rc<Array<Rc<rocq_string::RocqString>>>, ord: Rc<Array<u64>>, lo: u64, hi: u64) -> Rc<rocq_string::RocqString> {
  let tmp = build(xs, ord, lo, hi, ());
  tmp
}

// Rocq: Joinstrings.joinstrings_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(xs: Rc<Array<Rc<rocq_string::RocqString>>>, ord: Rc<Array<u64>>, lo: u64, hi: u64, _H: ()) -> Rc<rocq_string::RocqString> {
  let tmp = split_ok(lo, hi);
  let tmp_1 = match bdec(tmp) {
    sumbool::left => {
      let tmp_2 = mid_of(lo, hi);
      let xs_clone = Rc::clone(&xs);
      let ord_clone = Rc::clone(&ord);
      let tmp_3 = build(xs_clone, ord_clone, lo, tmp_2, ());
      let tmp_4 = build(xs, ord, mid_of(lo, hi), hi, ());
      let tmp_5 = cat(tmp_3, tmp_4);
      tmp_5
    },
    sumbool::right => {
      let tmp_6 = rocq_array::get::<u64>(&ord, lo);
      std::mem::drop(ord);
      let tmp_7 = rocq_array::get::<Rc<rocq_string::RocqString>>(&xs, tmp_6);
      std::mem::drop(xs);
      tmp_7
    },
  };
  tmp_1
}

// Rocq: Joinstrings.joinstrings_implem.joinstrings_impl
// Variant: uncurried
pub fn joinstrings_impl(xs: Rc<Array<Rc<rocq_string::RocqString>>>, xa: Rc<Array<u64>>, xb: Rc<Array<u64>>) -> Rc<rocq_string::RocqString> {
  let n = rocq_array::length::<Rc<rocq_string::RocqString>>(&xs);
  let m = rocq_array::length::<u64>(&xa);
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let tl0 = init_loop_1(n, 0u64, tmp);
  let tmp_1 = rocq_array::make::<u64>(n, 0u64);
  let xa_clone = Rc::clone(&xa);
  let nt = ops_loop_1(xa_clone, xb, m, 0u64, tmp_1, tl0);
  let nt_clone = Clone::clone(&nt);
  let nx = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(nt_clone);
  let tl = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(nt);
  let r = root_of(xa, m);
  let tmp_2 = rocq_array::get::<u64>(&tl, r);
  std::mem::drop(tl);
  let tmp_3 = rocq_array::make::<u64>(n, 0u64);
  let oc = walk_1(nx, tmp_2, n, r, 0u64, tmp_3);
  let oc_clone = Clone::clone(&oc);
  let tmp_4 = fst::<Rc<Array<u64>>, u64>(oc_clone);
  let tmp_5 = build_1(xs, tmp_4, 0u64, snd::<Rc<Array<u64>>, u64>(oc));
  tmp_5
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
