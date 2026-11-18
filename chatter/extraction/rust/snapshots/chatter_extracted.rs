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

// Rocq: Chatter.chatter_implem.bdec
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

// Rocq: Chatter.chatter_implem.init
// Variant: uncurried
pub fn init_1(n: u64, i: u64, rep: Rc<Array<u64>>, tl: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  init(n, i, rep, tl, ())
}

// Rocq: Chatter.chatter_implem.init (local: init)
// Variant: uncurried, lifted
pub fn init(n: u64, i: u64, rep: Rc<Array<u64>>, tl: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::set::<u64>(rep, i, i);
      let tmp_3 = rocq_array::set::<u64>(tl, i, i);
      init(n, tmp_1, tmp_2, tmp_3, ())
    },
    sumbool::right => {
      (rep, tl)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Chatter.chatter_implem.nx
// Variant: uncurried
pub fn nx(a: u64, b: u64, c: u64, r: u64) -> u64 {
  mod_(add(mul(r, a), b), c)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Chatter.chatter_implem.redraw
// Variant: uncurried
pub fn redraw_1(n: u64, a: u64, b: u64, c: u64, r: u64, bud: u64) -> ((u64, u64), u64) {
  redraw(n, a, b, c, r, bud, ())
}

// Rocq: Chatter.chatter_implem.redraw (local: redraw)
// Variant: uncurried, lifted
pub fn redraw(n: u64, a: u64, b: u64, c: u64, r: u64, bud: u64, _H: ()) -> ((u64, u64), u64) {
  let tmp = ltb(0u64, bud);
  match bdec(tmp) {
    sumbool::left => {
      let r1 = nx(a, b, c, r);
      let r2 = nx(a, b, c, r1);
      let x = mod_(r1, n);
      let y = mod_(r2, n);
      if eqb(x, y) {
        redraw(n, a, b, c, r2, sub(bud, 1u64), ())
      } else {
        ((r2, x), y)
      }
    },
    sumbool::right => {
      ((r, 0u64), 0u64)
    },
  }
}

// Rocq: Chatter.chatter_implem.relabel
// Variant: uncurried
pub fn relabel_1(nxt: Rc<Array<u64>>, big: u64, q: u64, cnt: u64, rep: Rc<Array<u64>>) -> Rc<Array<u64>> {
  relabel(nxt, big, q, cnt, rep, ())
}

// Rocq: Chatter.chatter_implem.relabel (local: relabel)
// Variant: uncurried, lifted
pub fn relabel(nxt: Rc<Array<u64>>, big: u64, q: u64, cnt: u64, rep: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(0u64, cnt);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&nxt, q);
      let tmp_2 = sub(cnt, 1u64);
      let tmp_3 = rocq_array::set::<u64>(rep, q, big);
      relabel(nxt, big, tmp_1, tmp_2, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(nxt);
      rep
    },
  }
}

// Rocq: Chatter.chatter_implem.merge
// Variant: uncurried
pub fn merge(big: u64, small: u64, rep: Rc<Array<u64>>, nxt: Rc<Array<u64>>, tl: Rc<Array<u64>>, sz: Rc<Array<u64>>) -> (((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<u64>>) {
  let tmp = rocq_array::get::<u64>(&sz, small);
  let nxt_clone = Rc::clone(&nxt);
  let rep_ = relabel_1(nxt_clone, big, small, tmp, rep);
  let tmp_1 = rocq_array::get::<u64>(&tl, big);
  let nxt_ = rocq_array::set::<u64>(nxt, tmp_1, small);
  let tmp_2 = rocq_array::get::<u64>(&tl, small);
  let tl_ = rocq_array::set::<u64>(tl, big, tmp_2);
  let tmp_3 = rocq_array::get::<u64>(&sz, big);
  let tmp_4 = rocq_array::get::<u64>(&sz, small);
  let sz_ = rocq_array::set::<u64>(sz, big, add(tmp_3, tmp_4));
  (((rep_, nxt_), tl_), sz_)
}

// Rocq: Chatter.chatter_implem.union
// Variant: uncurried
pub fn union(x: u64, y: u64, rep: Rc<Array<u64>>, nxt: Rc<Array<u64>>, tl: Rc<Array<u64>>, sz: Rc<Array<u64>>) -> (((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<u64>>) {
  let px = rocq_array::get::<u64>(&rep, x);
  let py = rocq_array::get::<u64>(&rep, y);
  if eqb(px, py) {
    (((rep, nxt), tl), sz)
  } else {
    let tmp = rocq_array::get::<u64>(&sz, py);
    let tmp_1 = rocq_array::get::<u64>(&sz, px);
    if ltb(tmp, tmp_1) {
      merge(px, py, rep, nxt, tl, sz)
    } else {
      merge(py, px, rep, nxt, tl, sz)
    }
  }
}

// Rocq: Chatter.chatter_implem.sim
// Variant: uncurried
pub fn sim_1(n: u64, a: u64, b: u64, c: u64, r: u64, k: u64, rep: Rc<Array<u64>>, nxt: Rc<Array<u64>>, tl: Rc<Array<u64>>, sz: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  sim(n, a, b, c, r, k, rep, nxt, tl, sz, ())
}

// Rocq: Chatter.chatter_implem.sim (local: sim)
// Variant: uncurried, lifted
pub fn sim(n: u64, a: u64, b: u64, c: u64, r: u64, k: u64, rep: Rc<Array<u64>>, nxt: Rc<Array<u64>>, tl: Rc<Array<u64>>, sz: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(0u64, k);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(c, 1u64);
      let tmp_2 = redraw_1(n, a, b, c, r, tmp_1);
      match tmp_2 {
        (v47, v49) => {
          match v47 {
            (v52, v54) => {
              let tmp_3 = union(v54, v49, rep, nxt, tl, sz);
              match tmp_3 {
                (v71, v73) => {
                  match v71 {
                    (v76, v78) => {
                      match v76 {
                        (v81, v83) => {
                          sim(n, a, b, c, v52, sub(k, 1u64), v81, v83, v78, v73, ())
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
    sumbool::right => {
      std::mem::drop(nxt);
      std::mem::drop(tl);
      (rep, sz)
    },
  }
}

// Rocq: Chatter.chatter_implem.tally
// Variant: uncurried
pub fn tally_1(n: u64, i: u64, rep: Rc<Array<u64>>, sz: Rc<Array<u64>>, seen: Rc<Array<u64>>, cnt: Rc<Array<u64>>, g: u64) -> (u64, Rc<Array<u64>>) {
  tally(n, i, rep, sz, seen, cnt, g, ())
}

// Rocq: Chatter.chatter_implem.tally (local: tally)
// Variant: uncurried, lifted
pub fn tally(n: u64, i: u64, rep: Rc<Array<u64>>, sz: Rc<Array<u64>>, seen: Rc<Array<u64>>, cnt: Rc<Array<u64>>, g: u64, _H: ()) -> (u64, Rc<Array<u64>>) {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let ro = rocq_array::get::<u64>(&rep, i);
      let tmp_1 = rocq_array::get::<u64>(&seen, ro);
      if eqb(tmp_1, 0u64) {
        let s = rocq_array::get::<u64>(&sz, ro);
        let tmp_2 = add(i, 1u64);
        let tmp_3 = rocq_array::set::<u64>(seen, ro, 1u64);
        let tmp_4 = rocq_array::get::<u64>(&cnt, s);
        let tmp_5 = rocq_array::set::<u64>(cnt, s, add(tmp_4, 1u64));
        tally(n, tmp_2, rep, sz, tmp_3, tmp_5, add(g, 1u64), ())
      } else {
        tally(n, add(i, 1u64), rep, sz, seen, cnt, g, ())
      }
    },
    sumbool::right => {
      std::mem::drop(rep);
      std::mem::drop(sz);
      std::mem::drop(seen);
      (g, cnt)
    },
  }
}

// Rocq: Chatter.chatter_implem.countd
// Variant: uncurried
pub fn countd_1(n: u64, i: u64, cnt: Rc<Array<u64>>, d: u64) -> u64 {
  countd(n, i, cnt, d, ())
}

// Rocq: Chatter.chatter_implem.countd (local: countd)
// Variant: uncurried, lifted
pub fn countd(n: u64, i: u64, cnt: Rc<Array<u64>>, d: u64, _H: ()) -> u64 {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = 0u64;
      let tmp_3 = rocq_array::get::<u64>(&cnt, sub(n, i));
      let tmp_4 = if ltb(tmp_2, tmp_3) {
        add(d, 1u64)
      } else {
        d
      };
      countd(n, tmp_1, cnt, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(cnt);
      d
    },
  }
}

// Rocq: Chatter.chatter_implem.fill
// Variant: uncurried
pub fn fill_1(n: u64, i: u64, j: u64, cnt: Rc<Array<u64>>, out: Rc<Array<(u64, u64)>>) -> Rc<Array<(u64, u64)>> {
  fill(n, i, j, cnt, out, ())
}

// Rocq: Chatter.chatter_implem.fill (local: fill)
// Variant: uncurried, lifted
pub fn fill(n: u64, i: u64, j: u64, cnt: Rc<Array<u64>>, out: Rc<Array<(u64, u64)>>, _H: ()) -> Rc<Array<(u64, u64)>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let s = sub(n, i);
      let v = rocq_array::get::<u64>(&cnt, s);
      if ltb(0u64, v) {
        let tmp_1 = add(i, 1u64);
        let tmp_2 = add(j, 1u64);
        let tmp_3 = rocq_array::set::<(u64, u64)>(out, j, (s, v));
        fill(n, tmp_1, tmp_2, cnt, tmp_3, ())
      } else {
        fill(n, add(i, 1u64), j, cnt, out, ())
      }
    },
    sumbool::right => {
      std::mem::drop(cnt);
      out
    },
  }
}

// Rocq: Chatter.chatter_implem.chatter_impl
// Variant: uncurried
pub fn chatter_impl(n: u64, r: u64, a: u64, b: u64, c: u64) -> (u64, Rc<Array<(u64, u64)>>) {
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let tmp_1 = rocq_array::make::<u64>(n, 0u64);
  let tmp_2 = init_1(n, 0u64, tmp, tmp_1);
  match tmp_2 {
    (v32, v34) => {
      let tmp_3 = rocq_array::make::<u64>(n, 0u64);
      let tmp_4 = rocq_array::make::<u64>(n, 1u64);
      let tmp_5 = sim_1(n, a, b, c, r, n, v32, tmp_3, v34, tmp_4);
      match &tmp_5 {
        (sz, rep) => {
          let tmp_6 = 0u64;
          let tmp_7 = rocq_array::make::<u64>(n, 0u64);
          let tmp_8 = rocq_array::make::<u64>(add(n, 1u64), 0u64);
          let tmp_9 = 0u64;
          let sz_clone = Rc::clone(sz);
          let rep_clone = Rc::clone(rep);
          std::mem::drop(tmp_5);
          let tmp_10 = tally_1(n, tmp_6, sz_clone, rep_clone, tmp_7, tmp_8, tmp_9);
          match tmp_10 {
            (v121, v123) => {
              let g = &v123;
              let g_clone = Rc::clone(g);
              let d = countd_1(n, 0u64, g_clone, 0u64);
              let tmp_11 = rocq_array::make::<(u64, u64)>(d, (0u64, 0u64));
              let tmp_12 = fill_1(n, 0u64, 0u64, v123, tmp_11);
              (v121, tmp_12)
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
