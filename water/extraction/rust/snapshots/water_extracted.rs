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

// Rocq: Water.water_implem.big
pub fn big() -> u64 {
  4611686018427387903u64
}

// Rocq: Water.water_implem.budget
pub fn budget() -> u64 {
  1099511627776u64
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

// Rocq: Water.water_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Water.water_implem.add_pipe
// Variant: uncurried
pub fn add_pipe(m: u64, r: Rc<Array<u64>>, a: u64, b: u64, c: u64) -> Rc<Array<u64>> {
  let i1 = add(mul(a, m), b);
  let tmp = rocq_array::get::<u64>(&r, i1);
  let r1 = rocq_array::set::<u64>(r, i1, add(tmp, c));
  let i2 = add(mul(b, m), a);
  let tmp_1 = rocq_array::get::<u64>(&r1, i2);
  rocq_array::set::<u64>(r1, i2, add(tmp_1, c))
}

// Rocq: Water.water_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(pa: Rc<Array<u64>>, pb: Rc<Array<u64>>, pc: Rc<Array<u64>>, m: u64, p: u64, j: u64, r: Rc<Array<u64>>) -> Rc<Array<u64>> {
  init_loop(pa, pb, pc, m, p, j, r, ())
}

// Rocq: Water.water_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(pa: Rc<Array<u64>>, pb: Rc<Array<u64>>, pc: Rc<Array<u64>>, m: u64, p: u64, j: u64, r: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(j, p);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(j, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&pa, j);
      let tmp_3 = rocq_array::get::<u64>(&pb, j);
      let tmp_4 = rocq_array::get::<u64>(&pc, j);
      let tmp_5 = add_pipe(m, r, tmp_2, tmp_3, tmp_4);
      init_loop(pa, pb, pc, m, p, tmp_1, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(pa);
      std::mem::drop(pb);
      std::mem::drop(pc);
      r
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

// Rocq: Water.water_implem.scan
// Variant: uncurried
pub fn scan_1(r: Rc<Array<u64>>, m: u64, u: u64, bu: u64, v: u64, par: Rc<Array<u64>>, bott: Rc<Array<u64>>, q: Rc<Array<u64>>, tail: u64) -> (((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64) {
  scan(r, m, u, bu, v, par, bott, q, tail, ())
}

// Rocq: Water.water_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(r: Rc<Array<u64>>, m: u64, u: u64, bu: u64, v: u64, par: Rc<Array<u64>>, bott: Rc<Array<u64>>, q: Rc<Array<u64>>, tail: u64, _H: ()) -> (((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64) {
  let tmp = ltb(v, m);
  match bdec(tmp) {
    sumbool::left => {
      let x = rocq_array::get::<u64>(&r, add(mul(u, m), v));
      let tmp_1 = rocq_array::get::<u64>(&par, v);
      let tmp_2 = eqb(tmp_1, 0u64);
      let tmp_3 = ltb(0u64, x);
      if andb(tmp_2, tmp_3) {
        let tmp_4 = add(v, 1u64);
        let tmp_5 = rocq_array::set::<u64>(par, v, u);
        let tmp_6 = if ltb(bu, x) {
          bu
        } else {
          x
        };
        let tmp_7 = rocq_array::set::<u64>(bott, v, tmp_6);
        let tmp_8 = rocq_array::set::<u64>(q, tail, v);
        scan(r, m, u, bu, tmp_4, tmp_5, tmp_7, tmp_8, add(tail, 1u64), ())
      } else {
        scan(r, m, u, bu, add(v, 1u64), par, bott, q, tail, ())
      }
    },
    sumbool::right => {
      std::mem::drop(r);
      (((par, bott), q), tail)
    },
  }
}

// Rocq: Water.water_implem.bfs_loop
// Variant: uncurried
pub fn bfs_loop_1(r: Rc<Array<u64>>, m: u64, head: u64, par: Rc<Array<u64>>, bott: Rc<Array<u64>>, q: Rc<Array<u64>>, tail: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  bfs_loop(r, m, head, par, bott, q, tail, ())
}

// Rocq: Water.water_implem.bfs_loop (local: bfs_loop)
// Variant: uncurried, lifted
pub fn bfs_loop(r: Rc<Array<u64>>, m: u64, head: u64, par: Rc<Array<u64>>, bott: Rc<Array<u64>>, q: Rc<Array<u64>>, tail: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(head, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = ltb(head, tail);
      let tmp_2 = rocq_array::get::<u64>(&par, 2u64);
      let tmp_3 = eqb(tmp_2, 0u64);
      if andb(tmp_1, tmp_3) {
        let u = rocq_array::get::<u64>(&q, head);
        let tmp_4 = rocq_array::get::<u64>(&bott, u);
        let r_clone = Rc::clone(&r);
        let tmp_5 = scan_1(r_clone, m, u, tmp_4, 1u64, par, bott, q, tail);
        match tmp_5 {
          (v78, v80) => {
            match v78 {
              (v83, v85) => {
                match v83 {
                  (v88, v90) => {
                    bfs_loop(r, m, add(head, 1u64), v88, v90, v85, v80, ())
                  },
                }
              },
            }
          },
        }
      } else {
        std::mem::drop(r);
        std::mem::drop(q);
        (par, bott)
      }
    },
    sumbool::right => {
      std::mem::drop(r);
      std::mem::drop(q);
      (par, bott)
    },
  }
}

// Rocq: Water.water_implem.bfs
// Variant: uncurried
pub fn bfs(r: Rc<Array<u64>>, m: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = rocq_array::make::<u64>(m, 0u64);
  let tmp_1 = rocq_array::set::<u64>(tmp, 1u64, 1u64);
  let tmp_2 = rocq_array::make::<u64>(m, 0u64);
  let tmp_3 = rocq_array::set::<u64>(tmp_2, 1u64, __rocq_global_376);
  let tmp_4 = rocq_array::make::<u64>(m, 0u64);
  let tmp_5 = rocq_array::set::<u64>(tmp_4, 0u64, 1u64);
  bfs_loop_1(r, m, 0u64, tmp_1, tmp_3, tmp_5, 1u64)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Water.water_implem.walk
// Variant: uncurried
pub fn walk_1(par: Rc<Array<u64>>, m: u64, d: u64, r: Rc<Array<u64>>, cur: u64, i: u64) -> Rc<Array<u64>> {
  walk(par, m, d, r, cur, i, ())
}

// Rocq: Water.water_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(par: Rc<Array<u64>>, m: u64, d: u64, r: Rc<Array<u64>>, cur: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, m);
  match bdec(tmp) {
    sumbool::left => {
      if eqb(cur, 1u64) {
        std::mem::drop(par);
        r
      } else {
        let u = rocq_array::get::<u64>(&par, cur);
        let i1 = add(mul(u, m), cur);
        let tmp_1 = rocq_array::get::<u64>(&r, i1);
        let r1 = rocq_array::set::<u64>(r, i1, sub(tmp_1, d));
        let i2 = add(mul(cur, m), u);
        let tmp_2 = rocq_array::get::<u64>(&r1, i2);
        let r2 = rocq_array::set::<u64>(r1, i2, add(tmp_2, d));
        walk(par, m, d, r2, u, add(i, 1u64), ())
      }
    },
    sumbool::right => {
      std::mem::drop(par);
      r
    },
  }
}

// Rocq: Water.water_implem.augment
// Variant: uncurried
pub fn augment_1(m: u64, B: u64, r: Rc<Array<u64>>, val: u64, i: u64) -> (Rc<Array<u64>>, u64) {
  augment(m, B, r, val, i, ())
}

// Rocq: Water.water_implem.augment (local: augment)
// Variant: uncurried, lifted
pub fn augment(m: u64, B: u64, r: Rc<Array<u64>>, val: u64, i: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let tmp = ltb(i, B);
  match bdec(tmp) {
    sumbool::left => {
      let r_clone = Rc::clone(&r);
      let tmp_1 = bfs(r_clone, m);
      match tmp_1 {
        (v25, v27) => {
          let bott = &v25;
          let par = &v27;
          let tmp_2 = rocq_array::get::<u64>(bott, 2u64);
          if eqb(tmp_2, 0u64) {
            std::mem::drop(v25);
            std::mem::drop(v27);
            (r, val)
          } else {
            let d = rocq_array::get::<u64>(par, 2u64);
            std::mem::drop(v27);
            let tmp_3 = walk_1(v25, m, d, r, 2u64, 0u64);
            augment(m, B, tmp_3, add(val, d), add(i, 1u64), ())
          }
        },
      }
    },
    sumbool::right => {
      (r, val)
    },
  }
}

// Rocq: Water.water_implem.imp_loop
// Variant: uncurried
pub fn imp_loop_1(ia: Rc<Array<u64>>, ib: Rc<Array<u64>>, ic: Rc<Array<u64>>, m: u64, k: u64, t: u64, r: Rc<Array<u64>>, val: u64, out: Rc<Array<u64>>) -> Rc<Array<u64>> {
  imp_loop(ia, ib, ic, m, k, t, r, val, out, ())
}

// Rocq: Water.water_implem.imp_loop (local: imp_loop)
// Variant: uncurried, lifted
pub fn imp_loop(ia: Rc<Array<u64>>, ib: Rc<Array<u64>>, ic: Rc<Array<u64>>, m: u64, k: u64, t: u64, r: Rc<Array<u64>>, val: u64, out: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(t, k);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&ia, t);
      let tmp_2 = rocq_array::get::<u64>(&ib, t);
      let tmp_3 = rocq_array::get::<u64>(&ic, t);
      let r1 = add_pipe(m, r, tmp_1, tmp_2, tmp_3);
      let tmp_4 = augment_1(m, __rocq_global_569, r1, val, 0u64);
      match tmp_4 {
        (v61, v63) => {
          let tmp_5 = add(t, 1u64);
          let tmp_6 = rocq_array::set::<u64>(out, add(t, 1u64), v63);
          imp_loop(ia, ib, ic, m, k, tmp_5, v61, v63, tmp_6, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(ia);
      std::mem::drop(ib);
      std::mem::drop(ic);
      std::mem::drop(r);
      out
    },
  }
}

// Rocq: Water.water_implem.water_impl
// Variant: uncurried
pub fn water_impl(n: u64, pa: Rc<Array<u64>>, pb: Rc<Array<u64>>, pc: Rc<Array<u64>>, ia: Rc<Array<u64>>, ib: Rc<Array<u64>>, ic: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let m = add(n, 1u64);
  let p = rocq_array::length::<u64>(&pa);
  let tmp = rocq_array::make::<u64>(mul(m, m), 0u64);
  let r = init_loop_1(pa, pb, pc, m, p, 0u64, tmp);
  let tmp_1 = augment_1(m, __rocq_global_569, r, 0u64, 0u64);
  match tmp_1 {
    (v66, v68) => {
      let k = rocq_array::length::<u64>(&ia);
      let tmp_2 = rocq_array::make::<u64>(add(k, 1u64), 0u64);
      let tmp_3 = rocq_array::set::<u64>(tmp_2, 0u64, v68);
      imp_loop_1(ia, ib, ic, m, k, 0u64, v66, v68, tmp_3)
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
const __rocq_global_376: u64 = 4611686018427387903u64;
const __rocq_global_569: u64 = 1099511627776u64;