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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsr
// Variant: uncurried
pub fn lsr(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsr(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Kingpinescape.kingpinescape_implem.bdec
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

// Rocq: Kingpinescape.kingpinescape_implem.cnt_loop
// Variant: uncurried
pub fn cnt_loop_1(col: Rc<Array<u64>>, m: u64, i: u64, deg: Rc<Array<u64>>) -> Rc<Array<u64>> {
  cnt_loop(col, m, i, deg, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.cnt_loop (local: cnt_loop)
// Variant: uncurried, lifted
pub fn cnt_loop(col: Rc<Array<u64>>, m: u64, i: u64, deg: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, m);
  match bdec(tmp) {
    sumbool::left => {
      let v = rocq_array::get::<u64>(&col, i);
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&deg, v);
      let tmp_3 = rocq_array::set::<u64>(deg, v, add(tmp_2, 1u64));
      cnt_loop(col, m, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(col);
      deg
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.pre_loop
// Variant: uncurried
pub fn pre_loop_1(deg: Rc<Array<u64>>, n: u64, i: u64, acc: u64, pos: Rc<Array<u64>>) -> Rc<Array<u64>> {
  pre_loop(deg, n, i, acc, pos, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.pre_loop (local: pre_loop)
// Variant: uncurried, lifted
pub fn pre_loop(deg: Rc<Array<u64>>, n: u64, i: u64, acc: u64, pos: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&deg, i);
      let tmp_3 = add(acc, tmp_2);
      let tmp_4 = rocq_array::set::<u64>(pos, i, acc);
      pre_loop(deg, n, tmp_1, tmp_3, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(deg);
      pos
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(col: Rc<Array<u64>>, base: u64, m: u64, i: u64, pos: Rc<Array<u64>>, adj: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  fill_loop(col, base, m, i, pos, adj, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(col: Rc<Array<u64>>, base: u64, m: u64, i: u64, pos: Rc<Array<u64>>, adj: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(i, m);
  match bdec(tmp) {
    sumbool::left => {
      let v = rocq_array::get::<u64>(&col, i);
      let p = rocq_array::get::<u64>(&pos, v);
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::set::<u64>(pos, v, add(p, 1u64));
      let tmp_3 = rocq_array::set::<u64>(adj, p, add(base, i));
      fill_loop(col, base, m, tmp_1, tmp_2, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(col);
      (pos, adj)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Kingpinescape.kingpinescape_implem.root_loop
// Variant: uncurried
pub fn root_loop_1(deg: Rc<Array<u64>>, n: u64, i: u64) -> u64 {
  root_loop(deg, n, i, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.root_loop (local: root_loop)
// Variant: uncurried, lifted
pub fn root_loop(deg: Rc<Array<u64>>, n: u64, i: u64, _H: ()) -> u64 {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&deg, i);
      if leb(2u64, tmp_1) {
        std::mem::drop(deg);
        i
      } else {
        root_loop(deg, n, add(i, 1u64), ())
      }
    },
    sumbool::right => {
      std::mem::drop(deg);
      0u64
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.other
// Variant: uncurried
pub fn other(ea: Rc<Array<u64>>, eb: Rc<Array<u64>>, m: u64, hh: u64) -> u64 {
  if ltb(hh, m) {
    std::mem::drop(ea);
    let tmp = rocq_array::get::<u64>(&eb, hh);
    std::mem::drop(eb);
    tmp
  } else {
    std::mem::drop(eb);
    let tmp_1 = rocq_array::get::<u64>(&ea, sub(hh, m));
    std::mem::drop(ea);
    tmp_1
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.nb_loop
// Variant: uncurried
pub fn nb_loop_1(ea: Rc<Array<u64>>, eb: Rc<Array<u64>>, adj: Rc<Array<u64>>, m: u64, e: u64, s: u64, mark: Rc<Array<u64>>, stk: Rc<Array<u64>>, sp: u64) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  nb_loop(ea, eb, adj, m, e, s, mark, stk, sp, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.nb_loop (local: nb_loop)
// Variant: uncurried, lifted
pub fn nb_loop(ea: Rc<Array<u64>>, eb: Rc<Array<u64>>, adj: Rc<Array<u64>>, m: u64, e: u64, s: u64, mark: Rc<Array<u64>>, stk: Rc<Array<u64>>, sp: u64, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let tmp = ltb(s, e);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&adj, s);
      let ea_clone = Rc::clone(&ea);
      let eb_clone = Rc::clone(&eb);
      let w = other(ea_clone, eb_clone, m, tmp_1);
      let tmp_2 = rocq_array::get::<u64>(&mark, w);
      if eqb(tmp_2, 0u64) {
        let tmp_3 = add(s, 1u64);
        let tmp_4 = rocq_array::set::<u64>(mark, w, 1u64);
        let tmp_5 = rocq_array::set::<u64>(stk, sp, w);
        nb_loop(ea, eb, adj, m, e, tmp_3, tmp_4, tmp_5, add(sp, 1u64), ())
      } else {
        nb_loop(ea, eb, adj, m, e, add(s, 1u64), mark, stk, sp, ())
      }
    },
    sumbool::right => {
      std::mem::drop(ea);
      std::mem::drop(eb);
      std::mem::drop(adj);
      ((mark, stk), sp)
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.dfs_loop
// Variant: uncurried
pub fn dfs_loop_1(ea: Rc<Array<u64>>, eb: Rc<Array<u64>>, adj: Rc<Array<u64>>, deg: Rc<Array<u64>>, pos: Rc<Array<u64>>, n: u64, m: u64, t: u64, mark: Rc<Array<u64>>, stk: Rc<Array<u64>>, sp: u64, lv: Rc<Array<u64>>, L: u64) -> (Rc<Array<u64>>, u64) {
  dfs_loop(ea, eb, adj, deg, pos, n, m, t, mark, stk, sp, lv, L, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.dfs_loop (local: dfs_loop)
// Variant: uncurried, lifted
pub fn dfs_loop(ea: Rc<Array<u64>>, eb: Rc<Array<u64>>, adj: Rc<Array<u64>>, deg: Rc<Array<u64>>, pos: Rc<Array<u64>>, n: u64, m: u64, t: u64, mark: Rc<Array<u64>>, stk: Rc<Array<u64>>, sp: u64, lv: Rc<Array<u64>>, L: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let tmp = ltb(t, n);
  match bdec(tmp) {
    sumbool::left => {
      if ltb(0u64, sp) {
        let v = rocq_array::get::<u64>(&stk, sub(sp, 1u64));
        let dv = rocq_array::get::<u64>(&deg, v);
        let e = rocq_array::get::<u64>(&pos, v);
        let tmp_1 = 1u64;
        let lv_ = if eqb(dv, tmp_1) {
          rocq_array::set::<u64>(lv, L, v)
        } else {
          lv
        };
        let tmp_2 = 1u64;
        let L_ = if eqb(dv, tmp_2) {
          add(L, 1u64)
        } else {
          L
        };
        let tmp_3 = sub(e, dv);
        let tmp_4 = sub(sp, 1u64);
        let ea_clone = Rc::clone(&ea);
        let eb_clone = Rc::clone(&eb);
        let adj_clone = Rc::clone(&adj);
        let tmp_5 = nb_loop_1(ea_clone, eb_clone, adj_clone, m, e, tmp_3, mark, stk, tmp_4);
        match tmp_5 {
          (v135, v137) => {
            match v135 {
              (v140, v142) => {
                dfs_loop(ea, eb, adj, deg, pos, n, m, add(t, 1u64), v140, v142, v137, lv_, L_, ())
              },
            }
          },
        }
      } else {
        std::mem::drop(ea);
        std::mem::drop(eb);
        std::mem::drop(adj);
        std::mem::drop(deg);
        std::mem::drop(pos);
        std::mem::drop(mark);
        std::mem::drop(stk);
        (lv, L)
      }
    },
    sumbool::right => {
      std::mem::drop(ea);
      std::mem::drop(eb);
      std::mem::drop(adj);
      std::mem::drop(deg);
      std::mem::drop(pos);
      std::mem::drop(mark);
      std::mem::drop(stk);
      (lv, L)
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.out_loop
// Variant: uncurried
pub fn out_loop_1(lv: Rc<Array<u64>>, a: u64, c: u64, i: u64, xs: Rc<Array<u64>>, ys: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  out_loop(lv, a, c, i, xs, ys, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.out_loop (local: out_loop)
// Variant: uncurried, lifted
pub fn out_loop(lv: Rc<Array<u64>>, a: u64, c: u64, i: u64, xs: Rc<Array<u64>>, ys: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(i, c);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&lv, i);
      let tmp_3 = rocq_array::set::<u64>(xs, i, tmp_2);
      let tmp_4 = rocq_array::get::<u64>(&lv, add(i, a));
      let tmp_5 = rocq_array::set::<u64>(ys, i, tmp_4);
      out_loop(lv, a, c, tmp_1, tmp_3, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(lv);
      (xs, ys)
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.kingpin_impl
// Variant: uncurried
pub fn kingpin_impl(n: u64, _h: u64, ea: Rc<Array<u64>>, eb: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let m = sub(n, 1u64);
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let ea_clone = Rc::clone(&ea);
  let deg0 = cnt_loop_1(ea_clone, m, 0u64, tmp);
  let eb_clone = Rc::clone(&eb);
  let deg = cnt_loop_1(eb_clone, m, 0u64, deg0);
  let tmp_1 = rocq_array::make::<u64>(n, 0u64);
  let deg_clone = Rc::clone(&deg);
  let pos0 = pre_loop_1(deg_clone, n, 0u64, 0u64, tmp_1);
  let tmp_2 = rocq_array::make::<u64>(add(m, m), 0u64);
  let ea_clone_1 = Rc::clone(&ea);
  let tmp_3 = fill_loop_1(ea_clone_1, 0u64, m, 0u64, pos0, tmp_2);
  match tmp_3 {
    (v102, v104) => {
      let eb_clone_1 = Rc::clone(&eb);
      let tmp_4 = fill_loop_1(eb_clone_1, m, m, 0u64, v102, v104);
      match &tmp_4 {
        (adj, pos) => {
          let deg_clone_1 = Rc::clone(&deg);
          let r = root_loop_1(deg_clone_1, n, 0u64);
          let tmp_5 = rocq_array::make::<u64>(n, 0u64);
          let mark = rocq_array::set::<u64>(tmp_5, r, 1u64);
          let tmp_6 = rocq_array::make::<u64>(n, 0u64);
          let stk = rocq_array::set::<u64>(tmp_6, 0u64, r);
          let tmp_7 = 0u64;
          let tmp_8 = 1u64;
          let tmp_9 = rocq_array::make::<u64>(n, 0u64);
          let tmp_10 = 0u64;
          let pos_clone = Rc::clone(pos);
          let adj_clone = Rc::clone(adj);
          std::mem::drop(tmp_4);
          let tmp_11 = dfs_loop_1(ea, eb, pos_clone, deg, adj_clone, n, m, tmp_7, mark, stk, tmp_8, tmp_9, tmp_10);
          match tmp_11 {
            (v214, v216) => {
              let a = lsr(v216, 1u64);
              let c = sub(v216, a);
              let tmp_12 = rocq_array::make::<u64>(c, 0u64);
              let tmp_13 = rocq_array::make::<u64>(c, 0u64);
              out_loop_1(v214, a, c, 0u64, tmp_12, tmp_13)
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
