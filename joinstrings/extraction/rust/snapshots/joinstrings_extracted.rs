// Generated from OwnedANF. This printer is not verified.
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

// Rocq: Joinstrings.joinstrings_implem.joinstrings
// Variant: uncurried
pub fn joinstrings() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<rocq_string::RocqString>> {
  let v0: fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<rocq_string::RocqString> = joinstrings_impl;
  let v1: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<rocq_string::RocqString>> = Rc::new(v0);
  v1
}

// Rocq: Joinstrings.joinstrings_implem.joinstrings
pub fn joinstrings_curried() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<rocq_string::RocqString>>>> {
  let v0: fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<rocq_string::RocqString>>> = joinstrings_impl_curried;
  let v1: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<rocq_string::RocqString>>>> = Rc::new(v0);
  v1
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

// Rocq: Joinstrings.joinstrings_implem.bdec
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

// Rocq: Joinstrings.joinstrings_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(n: u64, k: u64, tl: Rc<Array<u64>>) -> Rc<Array<u64>> {
  init_loop(n, k, tl, ())
}

// Rocq: Joinstrings.joinstrings_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(n: u64, k: u64, tl: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v11 = ltb(k, n);
  match bdec(v11) {
    sumbool::left => {
      let v22 = add(k, 1u64);
      let v29 = rocq_array::set::<u64>(tl, k, k);
      init_loop(n, v22, v29, ())
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
  let v14 = ltb(k, m);
  match bdec(v14) {
    sumbool::left => {
      let v19 = &xa;
      let v22 = rocq_array::get::<u64>(&v19, k);
      let x = sub(v22, 1u64);
      let v31 = &xb;
      let v34 = rocq_array::get::<u64>(&v31, k);
      let y = sub(v34, 1u64);
      let v42 = &tl;
      let ty = rocq_array::get::<u64>(&v42, y);
      let v46 = &tl;
      let tx = rocq_array::get::<u64>(&v46, x);
      let v57 = add(k, 1u64);
      let v64 = rocq_array::set::<u64>(nx, tx, y);
      let v71 = rocq_array::set::<u64>(tl, x, ty);
      ops_loop(xa, xb, m, v57, v64, v71, ())
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

// Rocq: Joinstrings.joinstrings_implem.root_of
// Variant: uncurried
pub fn root_of(xa: Rc<Array<u64>>, m: u64) -> u64 {
  match eqb(m, 0u64) {
    true => {
      std::mem::drop(xa);
      0u64
    },
    false => {
      let v23 = sub(m, 1u64);
      let v24 = &xa;
      let v27 = rocq_array::get::<u64>(&v24, v23);
      std::mem::drop(xa);
      sub(v27, 1u64)
    },
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
  let v14 = ltb(i, n);
  match bdec(v14) {
    sumbool::left => {
      match eqb(cur, t) {
        true => {
          std::mem::drop(nx);
          let v31 = rocq_array::set::<u64>(ord, i, cur);
          (v31, add(i, 1u64))
        },
        false => {
          let v48 = &nx;
          let v51 = rocq_array::get::<u64>(&v48, cur);
          let v59 = add(i, 1u64);
          let v66 = rocq_array::set::<u64>(ord, i, cur);
          walk(nx, t, n, v51, v59, v66, ())
        },
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
  match b1 {
    true => {
      b2
    },
    false => {
      false
    },
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
  let v4 = rocq_string::cat(&v0, &v1);
  std::mem::drop(v1);
  std::mem::drop(v0);
  v4
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Joinstrings.joinstrings_implem.mid_of
// Variant: uncurried
pub fn mid_of(lo: u64, hi: u64) -> u64 {
  let v9 = sub(hi, lo);
  add(lo, div(v9, 2u64))
}

// Rocq: Joinstrings.joinstrings_implem.build
// Variant: uncurried
pub fn build_1(xs: Rc<Array<Rc<rocq_string::RocqString>>>, ord: Rc<Array<u64>>, lo: u64, hi: u64) -> Rc<rocq_string::RocqString> {
  let v18 = build(xs, ord, lo, hi, ());
  v18
}

// Rocq: Joinstrings.joinstrings_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(xs: Rc<Array<Rc<rocq_string::RocqString>>>, ord: Rc<Array<u64>>, lo: u64, hi: u64, _H: ()) -> Rc<rocq_string::RocqString> {
  let v12 = split_ok(lo, hi);
  let v77 = match bdec(v12) {
    sumbool::left => {
      let v22 = mid_of(lo, hi);
      let v28 = Rc::clone(&xs);
      let v31 = Rc::clone(&ord);
      let v38 = build(v28, v31, lo, v22, ());
      let v58 = build(xs, ord, mid_of(lo, hi), hi, ());
      let v64 = cat(v38, v58);
      v64
    },
    sumbool::right => {
      let v66 = &ord;
      let v69 = rocq_array::get::<u64>(&v66, lo);
      std::mem::drop(ord);
      let v70 = &xs;
      let v73 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v70, v69);
      std::mem::drop(xs);
      v73
    },
  };
  v77
}

// Rocq: Joinstrings.joinstrings_implem.joinstrings_impl
// Variant: uncurried
pub fn joinstrings_impl(xs: Rc<Array<Rc<rocq_string::RocqString>>>, xa: Rc<Array<u64>>, xb: Rc<Array<u64>>) -> Rc<rocq_string::RocqString> {
  let v3 = &xs;
  let n = rocq_array::length::<Rc<rocq_string::RocqString>>(&v3);
  let v5 = &xa;
  let m = rocq_array::length::<u64>(&v5);
  let v16 = rocq_array::make::<u64>(n, 0u64);
  let tl0 = init_loop_1(n, 0u64, v16);
  let v33 = rocq_array::make::<u64>(n, 0u64);
  let v36 = Rc::clone(&xa);
  let nt = ops_loop_1(v36, xb, m, 0u64, v33, tl0);
  let v50 = Clone::clone(&nt);
  let nx = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(v50);
  let tl = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(nt);
  let r = root_of(xa, m);
  let v64 = &tl;
  let v67 = rocq_array::get::<u64>(&v64, r);
  std::mem::drop(tl);
  let v76 = rocq_array::make::<u64>(n, 0u64);
  let oc = walk_1(nx, v67, n, r, 0u64, v76);
  let v93 = Clone::clone(&oc);
  let v95 = fst::<Rc<Array<u64>>, u64>(v93);
  let v111 = build_1(xs, v95, 0u64, snd::<Rc<Array<u64>>, u64>(oc));
  v111
}

// Rocq: Joinstrings.joinstrings_implem.joinstrings_impl
pub fn joinstrings_impl_curried(xs: Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<rocq_string::RocqString>>> {
  let v3 = {
    move |xa: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<rocq_string::RocqString>> {
      let xs = &xs;
      let v8 = Rc::clone(xs);
      let v11 = {
        move |xb: Rc<Array<u64>>| -> Rc<rocq_string::RocqString> {
          let v19 = Rc::clone(&v8);
          let v21 = Rc::clone(&xa);
          let v25 = joinstrings_impl(v19, v21, xb);
          v25
        }
      };
      let v27: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<rocq_string::RocqString>> = Rc::new(v11);
      v27
    }
  };
  let v31: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<rocq_string::RocqString>>> = Rc::new(v3);
  v31
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

pub fn run() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<rocq_string::RocqString>> {
  let v0: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<rocq_string::RocqString>> = __rocq_global_438.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_438: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<rocq_string::RocqString>> = joinstrings(); }
std::thread_local! { static __rocq_global_441: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<rocq_string::RocqString>>>> = joinstrings_curried(); }