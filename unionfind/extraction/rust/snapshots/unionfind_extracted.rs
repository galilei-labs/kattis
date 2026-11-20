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

// Rocq: Unionfind.unionfind_implem.bdec
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

// Rocq: Unionfind.unionfind_implem.count_queries
// Variant: uncurried
pub fn count_queries_1(xu: Rc<Array<bool>>, q: u64, k: u64, c: u64) -> u64 {
  count_queries(xu, q, k, c, ())
}

// Rocq: Unionfind.unionfind_implem.count_queries (local: count_queries)
// Variant: uncurried, lifted
pub fn count_queries(xu: Rc<Array<bool>>, q: u64, k: u64, c: u64, _H: ()) -> u64 {
  let tmp = ltb(k, q);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(k, 1u64);
      let tmp_2 = rocq_array::get::<bool>(&xu, k);
      let tmp_3 = if tmp_2 {
        c
      } else {
        add(c, 1u64)
      };
      count_queries(xu, q, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(xu);
      c
    },
  }
}

// Rocq: Unionfind.unionfind_implem.pack_queries
// Variant: uncurried
pub fn pack_queries_1(xu: Rc<Array<bool>>, raw: Rc<Array<bool>>, q: u64, k: u64, c: u64, out: Rc<Array<bool>>) -> Rc<Array<bool>> {
  pack_queries(xu, raw, q, k, c, out, ())
}

// Rocq: Unionfind.unionfind_implem.pack_queries (local: pack_queries)
// Variant: uncurried, lifted
pub fn pack_queries(xu: Rc<Array<bool>>, raw: Rc<Array<bool>>, q: u64, k: u64, c: u64, out: Rc<Array<bool>>, _H: ()) -> Rc<Array<bool>> {
  let tmp = ltb(k, q);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<bool>(&xu, k);
      if tmp_1 {
        pack_queries(xu, raw, q, add(k, 1u64), c, out, ())
      } else {
        let tmp_2 = add(k, 1u64);
        let tmp_3 = add(c, 1u64);
        let tmp_4 = rocq_array::get::<bool>(&raw, k);
        let tmp_5 = rocq_array::set::<bool>(out, c, tmp_4);
        pack_queries(xu, raw, q, tmp_2, tmp_3, tmp_5, ())
      }
    },
    sumbool::right => {
      std::mem::drop(xu);
      std::mem::drop(raw);
      out
    },
  }
}

// Rocq: Unionfind.unionfind_implem.compact_queries
// Variant: uncurried
pub fn compact_queries(xu: Rc<Array<bool>>, raw: Rc<Array<bool>>) -> Rc<Array<bool>> {
  let q = rocq_array::length::<bool>(&xu);
  let xu_clone = Rc::clone(&xu);
  let count = count_queries_1(xu_clone, q, 0u64, 0u64);
  let tmp = rocq_array::make::<bool>(count, false);
  pack_queries_1(xu, raw, q, 0u64, 0u64, tmp)
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

// Rocq: Unionfind.unionfind_implem.find
// Variant: uncurried
pub fn find_1(par: Rc<Array<u64>>, x: u64) -> (u64, Rc<Array<u64>>) {
  find(par, x, ())
}

// Rocq: Unionfind.unionfind_implem.find (local: find)
// Variant: uncurried, lifted
pub fn find(par: Rc<Array<u64>>, x: u64, _H: ()) -> (u64, Rc<Array<u64>>) {
  let p = rocq_array::get::<u64>(&par, x);
  let tmp = eqb(p, x);
  match bdec(tmp) {
    sumbool::left => {
      (x, par)
    },
    sumbool::right => {
      let rp = find(par, p, ());
      let rp_clone = Clone::clone(&rp);
      let tmp_1 = fst::<u64, Rc<Array<u64>>>(rp_clone);
      let rp_clone_1 = Clone::clone(&rp);
      let tmp_2 = snd::<u64, Rc<Array<u64>>>(rp_clone_1);
      let tmp_3 = rocq_array::set::<u64>(tmp_2, x, fst::<u64, Rc<Array<u64>>>(rp));
      (tmp_1, tmp_3)
    },
  }
}

// Rocq: Unionfind.unionfind_implem.link
// Variant: uncurried
pub fn link(par: Rc<Array<u64>>, rk: Rc<Array<u64>>, ra: u64, rb: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  if eqb(ra, rb) {
    (par, rk)
  } else {
    let ka = rocq_array::get::<u64>(&rk, ra);
    let kb = rocq_array::get::<u64>(&rk, rb);
    if ltb(ka, kb) {
      let tmp = rocq_array::set::<u64>(par, ra, rb);
      (tmp, rk)
    } else {
      if ltb(kb, ka) {
        let tmp_1 = rocq_array::set::<u64>(par, rb, ra);
        (tmp_1, rk)
      } else {
        let tmp_2 = rocq_array::set::<u64>(par, ra, rb);
        let tmp_3 = rocq_array::set::<u64>(rk, rb, add(kb, 1u64));
        (tmp_2, tmp_3)
      }
    }
  }
}

// Rocq: Unionfind.unionfind_implem.scan
// Variant: uncurried
pub fn scan_1(xu: Rc<Array<bool>>, xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, q: u64, k: u64, par: Rc<Array<u64>>, rk: Rc<Array<u64>>, out: Rc<Array<bool>>) -> Rc<Array<bool>> {
  scan(xu, xa, xb, q, k, par, rk, out, (), ())
}

// Rocq: Unionfind.unionfind_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(xu: Rc<Array<bool>>, xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, q: u64, k: u64, par: Rc<Array<u64>>, rk: Rc<Array<u64>>, out: Rc<Array<bool>>, _W: (), _H: ()) -> Rc<Array<bool>> {
  let tmp = ltb(k, q);
  match bdec(tmp) {
    sumbool::left => {
      let a = rocq_array::get::<u64>(&xa, k);
      let b = rocq_array::get::<u64>(&xb, k);
      let fa = find_1(par, a);
      let fa_clone = Clone::clone(&fa);
      let tmp_1 = snd::<u64, Rc<Array<u64>>>(fa_clone);
      let fb = find_1(tmp_1, b);
      let tmp_2 = rocq_array::get::<bool>(&xu, k);
      if tmp_2 {
        let fb_clone = Clone::clone(&fb);
        let tmp_3 = snd::<u64, Rc<Array<u64>>>(fb_clone);
        let l = link(tmp_3, rk, fst::<u64, Rc<Array<u64>>>(fa), fst::<u64, Rc<Array<u64>>>(fb));
        let tmp_4 = add(k, 1u64);
        let l_clone = Clone::clone(&l);
        let tmp_5 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(l_clone);
        let tmp_6 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(l);
        scan(xu, xa, xb, q, tmp_4, tmp_5, tmp_6, out, (), ())
      } else {
        let tmp_7 = add(k, 1u64);
        let fb_clone_1 = Clone::clone(&fb);
        let tmp_8 = snd::<u64, Rc<Array<u64>>>(fb_clone_1);
        let tmp_9 = rocq_array::set::<bool>(out, k, eqb(fst::<u64, Rc<Array<u64>>>(fa), fst::<u64, Rc<Array<u64>>>(fb)));
        scan(xu, xa, xb, q, tmp_7, tmp_8, rk, tmp_9, (), ())
      }
    },
    sumbool::right => {
      std::mem::drop(xu);
      std::mem::drop(xa);
      std::mem::drop(xb);
      std::mem::drop(par);
      std::mem::drop(rk);
      out
    },
  }
}

// Rocq: Unionfind.unionfind_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(n: u64, i: u64, p: Rc<Array<u64>>) -> Rc<Array<u64>> {
  init_loop(n, i, p, ())
}

// Rocq: Unionfind.unionfind_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(n: u64, i: u64, p: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::set::<u64>(p, i, i);
      init_loop(n, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      p
    },
  }
}

// Rocq: Unionfind.unionfind_implem.init_par
pub fn init_par(n: u64) -> Rc<Array<u64>> {
  let tmp = rocq_array::make::<u64>(n, 0u64);
  init_loop_1(n, 0u64, tmp)
}

// Rocq: Unionfind.unionfind_implem.run_ops_raw
// Variant: uncurried
pub fn run_ops_raw(xn: u64, xu: Rc<Array<bool>>, xa: Rc<Array<u64>>, xb: Rc<Array<u64>>) -> Rc<Array<bool>> {
  let q = rocq_array::length::<bool>(&xu);
  let tmp = init_par(xn);
  let tmp_1 = rocq_array::make::<u64>(xn, 0u64);
  let tmp_2 = rocq_array::make::<bool>(q, false);
  scan_1(xu, xa, xb, q, 0u64, tmp, tmp_1, tmp_2)
}

// Rocq: Unionfind.unionfind_implem.run_ops_impl
// Variant: uncurried
pub fn run_ops_impl(xn: u64, xu: Rc<Array<bool>>, xa: Rc<Array<u64>>, xb: Rc<Array<u64>>) -> Rc<Array<bool>> {
  let xu_clone = Rc::clone(&xu);
  let tmp = run_ops_raw(xn, xu_clone, xa, xb);
  compact_queries(xu, tmp)
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
