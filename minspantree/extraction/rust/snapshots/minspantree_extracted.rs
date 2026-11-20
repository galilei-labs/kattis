#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

pub enum option<A: 'static> {
  Some(A),
  None,
}

impl<A: Clone + 'static> Clone for option<A> {
  fn clone(&self) -> Self {
    match self {
      option::Some(__field0) => option::Some(Clone::clone(__field0)),
      option::None => option::None,
    }
  }
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = u64;

pub type sint = u64;

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

// Rocq: Minspantree.minspantree_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Minspantree.minspantree_implem.find
// Variant: uncurried
pub fn find_1(par: Rc<Array<u64>>, rk: Rc<Array<u64>>, v: u64) -> u64 {
  find(par, rk, v, ())
}

// Rocq: Minspantree.minspantree_implem.find (local: find)
// Variant: uncurried, lifted
pub fn find(par: Rc<Array<u64>>, rk: Rc<Array<u64>>, v: u64, _H: ()) -> u64 {
  let u = rocq_array::get::<u64>(&par, v);
  if eqb(u, v) {
    std::mem::drop(rk);
    std::mem::drop(par);
    v
  } else {
    let tmp = rocq_array::get::<u64>(&rk, v);
    let tmp_1 = rocq_array::get::<u64>(&rk, u);
    let tmp_2 = ltb(tmp, tmp_1);
    match bdec(tmp_2) {
      sumbool::left => {
        find(par, rk, u, ())
      },
      sumbool::right => {
        std::mem::drop(rk);
        std::mem::drop(par);
        v
      },
    }
  }
}

// Rocq: Minspantree.minspantree_implem.findr
// Variant: uncurried
pub fn findr(par: Rc<Array<u64>>, rk: Rc<Array<u64>>, v: u64) -> u64 {
  find_1(par, rk, v)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Minspantree.minspantree_implem.scan
// Variant: uncurried
pub fn scan_1(n: u64, us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, ord: Rc<Array<u64>>, m: u64, q: u64, par: Rc<Array<u64>>, rk: Rc<Array<u64>>, out: Rc<Array<u64>>, cnt: u64, cost: u64) -> Rc<option<(u64, Rc<Array<u64>>)>> {
  scan(n, us, vs, ws, ord, m, q, par, rk, out, cnt, cost, ())
}

// Rocq: Minspantree.minspantree_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(n: u64, us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, ord: Rc<Array<u64>>, m: u64, q: u64, par: Rc<Array<u64>>, rk: Rc<Array<u64>>, out: Rc<Array<u64>>, cnt: u64, cost: u64, _H: ()) -> Rc<option<(u64, Rc<Array<u64>>)>> {
  let tmp = ltb(q, m);
  match bdec(tmp) {
    sumbool::left => {
      let e = rocq_array::get::<u64>(&ord, q);
      let tmp_1 = rocq_array::get::<u64>(&us, e);
      let par_clone = Rc::clone(&par);
      let rk_clone = Rc::clone(&rk);
      let a = findr(par_clone, rk_clone, tmp_1);
      let tmp_2 = rocq_array::get::<u64>(&vs, e);
      let par_clone_1 = Rc::clone(&par);
      let rk_clone_1 = Rc::clone(&rk);
      let b = findr(par_clone_1, rk_clone_1, tmp_2);
      if eqb(a, b) {
        scan(n, us, vs, ws, ord, m, add(q, 1u64), par, rk, out, cnt, cost, ())
      } else {
        let ra = rocq_array::get::<u64>(&rk, a);
        let rb = rocq_array::get::<u64>(&rk, b);
        if ltb(ra, rb) {
          let tmp_3 = add(q, 1u64);
          let tmp_4 = rocq_array::set::<u64>(par, a, b);
          let tmp_5 = rocq_array::set::<u64>(out, cnt, e);
          let tmp_6 = add(cnt, 1u64);
          let tmp_7 = rocq_array::get::<u64>(&ws, e);
          scan(n, us, vs, ws, ord, m, tmp_3, tmp_4, rk, tmp_5, tmp_6, add(cost, tmp_7), ())
        } else {
          if ltb(rb, ra) {
            let tmp_8 = add(q, 1u64);
            let tmp_9 = rocq_array::set::<u64>(par, b, a);
            let tmp_10 = rocq_array::set::<u64>(out, cnt, e);
            let tmp_11 = add(cnt, 1u64);
            let tmp_12 = rocq_array::get::<u64>(&ws, e);
            scan(n, us, vs, ws, ord, m, tmp_8, tmp_9, rk, tmp_10, tmp_11, add(cost, tmp_12), ())
          } else {
            let tmp_13 = add(q, 1u64);
            let tmp_14 = rocq_array::set::<u64>(par, a, b);
            let tmp_15 = rocq_array::set::<u64>(rk, b, add(rb, 1u64));
            let tmp_16 = rocq_array::set::<u64>(out, cnt, e);
            let tmp_17 = add(cnt, 1u64);
            let tmp_18 = rocq_array::get::<u64>(&ws, e);
            scan(n, us, vs, ws, ord, m, tmp_13, tmp_14, tmp_15, tmp_16, tmp_17, add(cost, tmp_18), ())
          }
        }
      }
    },
    sumbool::right => {
      let tmp_19 = sub(n, 1u64);
      if eqb(cnt, tmp_19) {
        std::mem::drop(us);
        std::mem::drop(vs);
        std::mem::drop(ws);
        std::mem::drop(ord);
        std::mem::drop(par);
        std::mem::drop(rk);
        Rc::new(option::<(u64, Rc<Array<u64>>)>::Some((cost, out)))
      } else {
        std::mem::drop(us);
        std::mem::drop(vs);
        std::mem::drop(ws);
        std::mem::drop(ord);
        std::mem::drop(par);
        std::mem::drop(rk);
        std::mem::drop(out);
        Rc::new(option::<(u64, Rc<Array<u64>>)>::None)
      }
    },
  }
}

// Rocq: Minspantree.minspantree_implem.step_end
// Variant: uncurried
pub fn step_end(m: u64, w: u64, x: u64) -> u64 {
  let tmp = sub(m, x);
  if ltb(w, tmp) {
    add(x, w)
  } else {
    m
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lesb
// Variant: uncurried
pub fn lesb(v0: u64, v1: u64) -> bool {
  rocq_int63::lesb(v0, v1)
}

// Rocq: Minspantree.minspantree_implem.merge_loop
// Variant: uncurried
pub fn merge_loop_1(ws: Rc<Array<u64>>, src: Rc<Array<u64>>, iend: u64, jend: u64, kend: u64, i: u64, j: u64, k: u64, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  merge_loop(ws, src, iend, jend, kend, i, j, k, dst, ())
}

// Rocq: Minspantree.minspantree_implem.merge_loop (local: merge_loop)
// Variant: uncurried, lifted
pub fn merge_loop(ws: Rc<Array<u64>>, src: Rc<Array<u64>>, iend: u64, jend: u64, kend: u64, i: u64, j: u64, k: u64, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, kend);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = if ltb(i, iend) {
        if ltb(j, jend) {
          let tmp_2 = rocq_array::get::<u64>(&src, i);
          let tmp_3 = rocq_array::get::<u64>(&ws, tmp_2);
          let tmp_4 = rocq_array::get::<u64>(&src, j);
          let tmp_5 = rocq_array::get::<u64>(&ws, tmp_4);
          lesb(tmp_3, tmp_5)
        } else {
          true
        }
      } else {
        false
      };
      if tmp_1 {
        let tmp_6 = add(i, 1u64);
        let tmp_7 = add(k, 1u64);
        let tmp_8 = rocq_array::get::<u64>(&src, i);
        let tmp_9 = rocq_array::set::<u64>(dst, k, tmp_8);
        merge_loop(ws, src, iend, jend, kend, tmp_6, j, tmp_7, tmp_9, ())
      } else {
        let tmp_10 = add(j, 1u64);
        let tmp_11 = add(k, 1u64);
        let tmp_12 = rocq_array::get::<u64>(&src, j);
        let tmp_13 = rocq_array::set::<u64>(dst, k, tmp_12);
        merge_loop(ws, src, iend, jend, kend, i, tmp_10, tmp_11, tmp_13, ())
      }
    },
    sumbool::right => {
      std::mem::drop(ws);
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Minspantree.minspantree_implem.pass_loop
// Variant: uncurried
pub fn pass_loop_1(ws: Rc<Array<u64>>, src: Rc<Array<u64>>, m: u64, w: u64, lo: u64, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  pass_loop(ws, src, m, w, lo, dst, ())
}

// Rocq: Minspantree.minspantree_implem.pass_loop (local: pass_loop)
// Variant: uncurried, lifted
pub fn pass_loop(ws: Rc<Array<u64>>, src: Rc<Array<u64>>, m: u64, w: u64, lo: u64, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(lo, m);
  match bdec(tmp) {
    sumbool::left => {
      let mid = step_end(m, w, lo);
      let hi = step_end(m, w, mid);
      let tmp_1 = ltb(lo, hi);
      match bdec(tmp_1) {
        sumbool::left => {
          let ws_clone = Rc::clone(&ws);
          let src_clone = Rc::clone(&src);
          let tmp_2 = merge_loop_1(ws_clone, src_clone, mid, hi, hi, lo, mid, lo, dst);
          pass_loop(ws, src, m, w, hi, tmp_2, ())
        },
        sumbool::right => {
          std::mem::drop(ws);
          std::mem::drop(src);
          dst
        },
      }
    },
    sumbool::right => {
      std::mem::drop(ws);
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Minspantree.minspantree_implem.sort_loop
// Variant: uncurried
pub fn sort_loop_1(ws: Rc<Array<u64>>, m: u64, w: u64, src: Rc<Array<u64>>, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  sort_loop(ws, m, w, src, dst, ())
}

// Rocq: Minspantree.minspantree_implem.sort_loop (local: sort_loop)
// Variant: uncurried, lifted
pub fn sort_loop(ws: Rc<Array<u64>>, m: u64, w: u64, src: Rc<Array<u64>>, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(w, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(w, w);
      let tmp_2 = ltb(w, tmp_1);
      match bdec(tmp_2) {
        sumbool::left => {
          let tmp_3 = add(w, w);
          let ws_clone = Rc::clone(&ws);
          let src_clone = Rc::clone(&src);
          let tmp_4 = pass_loop_1(ws_clone, src_clone, m, w, 0u64, dst);
          sort_loop(ws, m, tmp_3, tmp_4, src, ())
        },
        sumbool::right => {
          std::mem::drop(ws);
          std::mem::drop(dst);
          src
        },
      }
    },
    sumbool::right => {
      std::mem::drop(ws);
      std::mem::drop(dst);
      src
    },
  }
}

// Rocq: Minspantree.minspantree_implem.iota_loop
// Variant: uncurried
pub fn iota_loop_1(m: u64, i: u64, a: Rc<Array<u64>>) -> Rc<Array<u64>> {
  iota_loop(m, i, a, ())
}

// Rocq: Minspantree.minspantree_implem.iota_loop (local: iota_loop)
// Variant: uncurried, lifted
pub fn iota_loop(m: u64, i: u64, a: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::set::<u64>(a, i, i);
      iota_loop(m, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      a
    },
  }
}

// Rocq: Minspantree.minspantree_implem.iota
pub fn iota(m: u64) -> Rc<Array<u64>> {
  let tmp = rocq_array::make::<u64>(m, 0u64);
  iota_loop_1(m, 0u64, tmp)
}

// Rocq: Minspantree.minspantree_implem.sort_edges
// Variant: uncurried
pub fn sort_edges(ws: Rc<Array<u64>>, m: u64) -> Rc<Array<u64>> {
  let tmp = iota(m);
  let tmp_1 = rocq_array::make::<u64>(m, 0u64);
  sort_loop_1(ws, m, 1u64, tmp, tmp_1)
}

// Rocq: Minspantree.minspantree_implem.mst_impl
// Variant: uncurried
pub fn mst_impl(n: u64, us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>) -> Rc<option<(u64, Rc<Array<u64>>)>> {
  let m = rocq_array::length::<u64>(&us);
  let ws_clone = Rc::clone(&ws);
  let tmp = sort_edges(ws_clone, m);
  let tmp_1 = iota(n);
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  let tmp_3 = rocq_array::make::<u64>(sub(n, 1u64), 0u64);
  scan_1(n, us, vs, ws, tmp, m, 0u64, tmp_1, tmp_2, tmp_3, 0u64, 0u64)
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
