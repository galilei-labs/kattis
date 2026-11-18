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

// Rocq: Knapsack2.knapsack2_implem.inf
pub fn inf() -> u64 {
  9223372036854775807u64
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

// Rocq: Knapsack2.knapsack2_implem.bdec
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

// Rocq: Knapsack2.knapsack2_implem.min_loop
// Variant: uncurried
pub fn min_loop_1(g: Rc<Array<u64>>, n: u64, i: u64, best: u64) -> u64 {
  min_loop(g, n, i, best, ())
}

// Rocq: Knapsack2.knapsack2_implem.min_loop (local: min_loop)
// Variant: uncurried, lifted
pub fn min_loop(g: Rc<Array<u64>>, n: u64, i: u64, best: u64, _H: ()) -> u64 {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&g, i);
      let tmp_3 = if ltb(tmp_2, best) {
        rocq_array::get::<u64>(&g, i)
      } else {
        best
      };
      min_loop(g, n, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(g);
      best
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Knapsack2.knapsack2_implem.gcd_loop
// Variant: uncurried
pub fn gcd_loop_1(u: u64, v: u64) -> u64 {
  gcd_loop(u, v, ())
}

// Rocq: Knapsack2.knapsack2_implem.gcd_loop (local: gcd_loop)
// Variant: uncurried, lifted
pub fn gcd_loop(u: u64, v: u64, _H: ()) -> u64 {
  let tmp = eqb(v, 0u64);
  match bdec(tmp) {
    sumbool::left => {
      u
    },
    sumbool::right => {
      let tmp_1 = mod_(u, v);
      gcd_loop(v, tmp_1, ())
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Knapsack2.knapsack2_implem.nxt
// Variant: uncurried
pub fn nxt(m: u64, a_: u64, x: u64) -> u64 {
  let y = add(x, a_);
  if ltb(y, m) {
    y
  } else {
    sub(y, m)
  }
}

// Rocq: Knapsack2.knapsack2_implem.scan
// Variant: uncurried
pub fn scan_1(A: Rc<Array<u64>>, m: u64, a_: u64, L: u64, j: u64, x: u64, p: u64) -> u64 {
  scan(A, m, a_, L, j, x, p, ())
}

// Rocq: Knapsack2.knapsack2_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(A: Rc<Array<u64>>, m: u64, a_: u64, L: u64, j: u64, x: u64, p: u64, _H: ()) -> u64 {
  let tmp = ltb(j, L);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(j, 1u64);
      let tmp_2 = nxt(m, a_, x);
      let tmp_3 = rocq_array::get::<u64>(&A, x);
      let tmp_4 = rocq_array::get::<u64>(&A, p);
      let tmp_5 = if ltb(tmp_3, tmp_4) {
        x
      } else {
        p
      };
      scan(A, m, a_, L, tmp_1, tmp_2, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(A);
      p
    },
  }
}

// Rocq: Knapsack2.knapsack2_implem.relax
// Variant: uncurried
pub fn relax_1(m: u64, a: u64, a_: u64, L1: u64, j: u64, x: u64, cur: u64, A: Rc<Array<u64>>) -> Rc<Array<u64>> {
  relax(m, a, a_, L1, j, x, cur, A, ())
}

// Rocq: Knapsack2.knapsack2_implem.relax (local: relax)
// Variant: uncurried, lifted
pub fn relax(m: u64, a: u64, a_: u64, L1: u64, j: u64, x: u64, cur: u64, A: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(j, L1);
  match bdec(tmp) {
    sumbool::left => {
      let y = nxt(m, a_, x);
      let c = add(cur, a);
      let v = rocq_array::get::<u64>(&A, y);
      if ltb(c, v) {
        let tmp_1 = add(j, 1u64);
        let tmp_2 = rocq_array::set::<u64>(A, y, c);
        relax(m, a, a_, L1, tmp_1, y, c, tmp_2, ())
      } else {
        relax(m, a, a_, L1, add(j, 1u64), y, v, A, ())
      }
    },
    sumbool::right => {
      A
    },
  }
}

// Rocq: Knapsack2.knapsack2_implem.classes
// Variant: uncurried
pub fn classes_1(m: u64, a: u64, a_: u64, d: u64, L: u64, c: u64, A: Rc<Array<u64>>) -> Rc<Array<u64>> {
  classes(m, a, a_, d, L, c, A, ())
}

// Rocq: Knapsack2.knapsack2_implem.classes (local: classes)
// Variant: uncurried, lifted
pub fn classes(m: u64, a: u64, a_: u64, d: u64, L: u64, c: u64, A: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(c, d);
  match bdec(tmp) {
    sumbool::left => {
      let A_clone = Rc::clone(&A);
      let p = scan_1(A_clone, m, a_, L, 0u64, c, c);
      let v = rocq_array::get::<u64>(&A, p);
      let tmp_1 = add(c, 1u64);
      let tmp_2 = __rocq_global_249;
      let tmp_3 = if eqb(v, tmp_2) {
        A
      } else {
        relax_1(m, a, a_, sub(L, 1u64), 0u64, p, v, A)
      };
      classes(m, a, a_, d, L, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      A
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Knapsack2.knapsack2_implem.item
// Variant: uncurried
pub fn item(m: u64, a: u64, A: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let a_ = mod_(a, m);
  let d = gcd_loop_1(m, a_);
  let tmp = div(m, d);
  classes_1(m, a, a_, d, tmp, 0u64, A)
}

// Rocq: Knapsack2.knapsack2_implem.items
// Variant: uncurried
pub fn items_1(g: Rc<Array<u64>>, n: u64, m: u64, i: u64, A: Rc<Array<u64>>) -> Rc<Array<u64>> {
  items(g, n, m, i, A, ())
}

// Rocq: Knapsack2.knapsack2_implem.items (local: items)
// Variant: uncurried, lifted
pub fn items(g: Rc<Array<u64>>, n: u64, m: u64, i: u64, A: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&g, i);
      let tmp_3 = item(m, tmp_2, A);
      items(g, n, m, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(g);
      A
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Knapsack2.knapsack2_implem.fillable_core
// Variant: uncurried
pub fn fillable_core(k: u64, g: Rc<Array<u64>>) -> bool {
  let n = rocq_array::length::<u64>(&g);
  let tmp = rocq_array::get::<u64>(&g, 0u64);
  let g_clone = Rc::clone(&g);
  let m = min_loop_1(g_clone, n, 1u64, tmp);
  let tmp_1 = rocq_array::make::<u64>(m, __rocq_global_249);
  let tmp_2 = rocq_array::set::<u64>(tmp_1, 0u64, 0u64);
  let A = items_1(g, n, m, 0u64, tmp_2);
  let tmp_3 = rocq_array::get::<u64>(&A, mod_(k, m));
  std::mem::drop(A);
  leb(tmp_3, k)
}

// Rocq: Knapsack2.knapsack2_implem.fillable_impl
// Variant: uncurried
pub fn fillable_impl(k: u64, g: Rc<Array<u64>>) -> bool {
  fillable_core(k, g)
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
const __rocq_global_249: u64 = 9223372036854775807u64;