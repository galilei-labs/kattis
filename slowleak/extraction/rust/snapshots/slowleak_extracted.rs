#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

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

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = u64;

// Rocq: Slowleak.slowleak_implem.INF
pub fn INF() -> u64 {
  2305843009213693952u64
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

// Rocq: Slowleak.slowleak_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Slowleak.slowleak_implem.diag_loop
// Variant: uncurried
pub fn diag_loop_1(n: u64, i: u64, T: Rc<Array<u64>>) -> Rc<Array<u64>> {
  diag_loop(n, i, T, ())
}

// Rocq: Slowleak.slowleak_implem.diag_loop (local: diag_loop)
// Variant: uncurried, lifted
pub fn diag_loop(n: u64, i: u64, T: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::set::<u64>(T, add(mul(i, n), i), 0u64);
      diag_loop(n, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Slowleak.slowleak_implem.setmin
// Variant: uncurried
pub fn setmin(T: Rc<Array<u64>>, p: u64, s: u64) -> Rc<Array<u64>> {
  let tmp = rocq_array::get::<u64>(&T, p);
  if ltb(s, tmp) {
    rocq_array::set::<u64>(T, p, s)
  } else {
    T
  }
}

// Rocq: Slowleak.slowleak_implem.edge_loop
// Variant: uncurried
pub fn edge_loop_1(n: u64, xi: Rc<Array<u64>>, xj: Rc<Array<u64>>, xk: Rc<Array<u64>>, m: u64, e: u64, T: Rc<Array<u64>>) -> Rc<Array<u64>> {
  edge_loop(n, xi, xj, xk, m, e, T, ())
}

// Rocq: Slowleak.slowleak_implem.edge_loop (local: edge_loop)
// Variant: uncurried, lifted
pub fn edge_loop(n: u64, xi: Rc<Array<u64>>, xj: Rc<Array<u64>>, xk: Rc<Array<u64>>, m: u64, e: u64, T: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(e, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&xi, e);
      let u = sub(tmp_1, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&xj, e);
      let v = sub(tmp_2, 1u64);
      let k = rocq_array::get::<u64>(&xk, e);
      let tmp_3 = add(e, 1u64);
      let tmp_4 = setmin(T, add(mul(u, n), v), k);
      let tmp_5 = setmin(tmp_4, add(mul(v, n), u), k);
      edge_loop(n, xi, xj, xk, m, tmp_3, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(xi);
      std::mem::drop(xj);
      std::mem::drop(xk);
      T
    },
  }
}

// Rocq: Slowleak.slowleak_implem.fw_j
// Variant: uncurried
pub fn fw_j_1(n: u64, rowi: u64, rowk: u64, aik: u64, j: u64, T: Rc<Array<u64>>) -> Rc<Array<u64>> {
  fw_j(n, rowi, rowk, aik, j, T, ())
}

// Rocq: Slowleak.slowleak_implem.fw_j (local: fw_j)
// Variant: uncurried, lifted
pub fn fw_j(n: u64, rowi: u64, rowk: u64, aik: u64, j: u64, T: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(j, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(j, 1u64);
      let tmp_2 = add(rowi, j);
      let tmp_3 = rocq_array::get::<u64>(&T, add(rowk, j));
      let tmp_4 = setmin(T, tmp_2, add(aik, tmp_3));
      fw_j(n, rowi, rowk, aik, tmp_1, tmp_4, ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Slowleak.slowleak_implem.fw_i
// Variant: uncurried
pub fn fw_i_1(n: u64, k: u64, rowk: u64, i: u64, T: Rc<Array<u64>>) -> Rc<Array<u64>> {
  fw_i(n, k, rowk, i, T, ())
}

// Rocq: Slowleak.slowleak_implem.fw_i (local: fw_i)
// Variant: uncurried, lifted
pub fn fw_i(n: u64, k: u64, rowk: u64, i: u64, T: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let rowi = mul(i, n);
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&T, add(rowi, k));
      let tmp_3 = fw_j_1(n, rowi, rowk, tmp_2, 0u64, T);
      fw_i(n, k, rowk, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Slowleak.slowleak_implem.fw_k
// Variant: uncurried
pub fn fw_k_1(n: u64, k: u64, T: Rc<Array<u64>>) -> Rc<Array<u64>> {
  fw_k(n, k, T, ())
}

// Rocq: Slowleak.slowleak_implem.fw_k (local: fw_k)
// Variant: uncurried, lifted
pub fn fw_k(n: u64, k: u64, T: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(k, 1u64);
      let tmp_2 = mul(k, n);
      let tmp_3 = fw_i_1(n, k, tmp_2, 0u64, T);
      fw_k(n, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Slowleak.slowleak_implem.vx_loop
// Variant: uncurried
pub fn vx_loop_1(xs: Rc<Array<u64>>, t: u64, i: u64, V: Rc<Array<u64>>) -> Rc<Array<u64>> {
  vx_loop(xs, t, i, V, ())
}

// Rocq: Slowleak.slowleak_implem.vx_loop (local: vx_loop)
// Variant: uncurried, lifted
pub fn vx_loop(xs: Rc<Array<u64>>, t: u64, i: u64, V: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, t);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = add(i, 1u64);
      let tmp_3 = rocq_array::get::<u64>(&xs, i);
      let tmp_4 = rocq_array::set::<u64>(V, tmp_2, sub(tmp_3, 1u64));
      vx_loop(xs, t, tmp_1, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(xs);
      V
    },
  }
}

// Rocq: Slowleak.slowleak_implem.sel_loop
// Variant: uncurried
pub fn sel_loop_1(M: u64, vis: Rc<Array<bool>>, dist: Rc<Array<u64>>, i: u64, b: u64, bv: u64) -> u64 {
  sel_loop(M, vis, dist, i, b, bv, ())
}

// Rocq: Slowleak.slowleak_implem.sel_loop (local: sel_loop)
// Variant: uncurried, lifted
pub fn sel_loop(M: u64, vis: Rc<Array<bool>>, dist: Rc<Array<u64>>, i: u64, b: u64, bv: u64, _H: ()) -> u64 {
  let tmp = ltb(i, M);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<bool>(&vis, i);
      if tmp_1 {
        sel_loop(M, vis, dist, add(i, 1u64), b, bv, ())
      } else {
        let di = rocq_array::get::<u64>(&dist, i);
        if ltb(di, bv) {
          sel_loop(M, vis, dist, add(i, 1u64), i, di, ())
        } else {
          sel_loop(M, vis, dist, add(i, 1u64), b, bv, ())
        }
      }
    },
    sumbool::right => {
      std::mem::drop(vis);
      std::mem::drop(dist);
      b
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Slowleak.slowleak_implem.rel_loop
// Variant: uncurried
pub fn rel_loop_1(M: u64, V: Rc<Array<u64>>, T: Rc<Array<u64>>, vis: Rc<Array<bool>>, d: u64, ru: u64, du: u64, b: u64, dist: Rc<Array<u64>>) -> Rc<Array<u64>> {
  rel_loop(M, V, T, vis, d, ru, du, b, dist, ())
}

// Rocq: Slowleak.slowleak_implem.rel_loop (local: rel_loop)
// Variant: uncurried, lifted
pub fn rel_loop(M: u64, V: Rc<Array<u64>>, T: Rc<Array<u64>>, vis: Rc<Array<bool>>, d: u64, ru: u64, du: u64, b: u64, dist: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(b, M);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<bool>(&vis, b);
      let dist_ = if tmp_1 {
        dist
      } else {
        let tmp_2 = rocq_array::get::<u64>(&V, b);
        let w = rocq_array::get::<u64>(&T, add(ru, tmp_2));
        if leb(w, d) {
          setmin(dist, b, add(du, w))
        } else {
          dist
        }
      };
      rel_loop(M, V, T, vis, d, ru, du, add(b, 1u64), dist_, ())
    },
    sumbool::right => {
      std::mem::drop(V);
      std::mem::drop(T);
      std::mem::drop(vis);
      dist
    },
  }
}

// Rocq: Slowleak.slowleak_implem.dij_loop
// Variant: uncurried
pub fn dij_loop_1(n: u64, M: u64, tgt: u64, V: Rc<Array<u64>>, T: Rc<Array<u64>>, d: u64, r: u64, vis: Rc<Array<bool>>, dist: Rc<Array<u64>>) -> Rc<option<u64>> {
  dij_loop(n, M, tgt, V, T, d, r, vis, dist, ())
}

// Rocq: Slowleak.slowleak_implem.dij_loop (local: dij_loop)
// Variant: uncurried, lifted
pub fn dij_loop(n: u64, M: u64, tgt: u64, V: Rc<Array<u64>>, T: Rc<Array<u64>>, d: u64, r: u64, vis: Rc<Array<bool>>, dist: Rc<Array<u64>>, _H: ()) -> Rc<option<u64>> {
  let tmp = ltb(0u64, r);
  match bdec(tmp) {
    sumbool::left => {
      let vis_clone = Rc::clone(&vis);
      let dist_clone = Rc::clone(&dist);
      let u = sel_loop_1(M, vis_clone, dist_clone, 0u64, M, __rocq_global_110);
      if eqb(u, M) {
        std::mem::drop(V);
        std::mem::drop(T);
        std::mem::drop(vis);
        std::mem::drop(dist);
        Rc::new(option::<u64>::None)
      } else {
        if eqb(u, tgt) {
          std::mem::drop(V);
          std::mem::drop(T);
          std::mem::drop(vis);
          let tmp_1 = rocq_array::get::<u64>(&dist, u);
          std::mem::drop(dist);
          Rc::new(option::<u64>::Some(tmp_1))
        } else {
          let vis_ = rocq_array::set::<bool>(vis, u, true);
          let tmp_2 = rocq_array::get::<u64>(&V, u);
          let tmp_3 = mul(tmp_2, n);
          let tmp_4 = rocq_array::get::<u64>(&dist, u);
          let V_clone = Rc::clone(&V);
          let T_clone = Rc::clone(&T);
          let vis__clone = Rc::clone(&vis_);
          let dist_ = rel_loop_1(M, V_clone, T_clone, vis__clone, d, tmp_3, tmp_4, 0u64, dist);
          dij_loop(n, M, tgt, V, T, d, sub(r, 1u64), vis_, dist_, ())
        }
      }
    },
    sumbool::right => {
      std::mem::drop(V);
      std::mem::drop(T);
      std::mem::drop(vis);
      std::mem::drop(dist);
      Rc::new(option::<u64>::None)
    },
  }
}

// Rocq: Slowleak.slowleak_implem.slowleak_impl
// Variant: uncurried
pub fn slowleak_impl(x: u64, y: u64, xs: Rc<Array<u64>>, xi: Rc<Array<u64>>, xj: Rc<Array<u64>>, xk: Rc<Array<u64>>) -> Rc<option<u64>> {
  let tmp = rocq_array::make::<u64>(mul(x, x), __rocq_global_110);
  let T0 = diag_loop_1(x, 0u64, tmp);
  let m = rocq_array::length::<u64>(&xi);
  let T1 = edge_loop_1(x, xi, xj, xk, m, 0u64, T0);
  let T = fw_k_1(x, 0u64, T1);
  let t = rocq_array::length::<u64>(&xs);
  let M = add(t, 2u64);
  let tmp_1 = rocq_array::make::<u64>(M, 0u64);
  let tmp_2 = rocq_array::set::<u64>(tmp_1, add(t, 1u64), sub(x, 1u64));
  let V = vx_loop_1(xs, t, 0u64, tmp_2);
  let tmp_3 = add(t, 1u64);
  let tmp_4 = rocq_array::make::<bool>(M, false);
  let tmp_5 = rocq_array::make::<u64>(M, __rocq_global_110);
  let tmp_6 = rocq_array::set::<u64>(tmp_5, 0u64, 0u64);
  dij_loop_1(x, M, tmp_3, V, T, y, M, tmp_4, tmp_6)
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
const __rocq_global_110: u64 = 2305843009213693952u64;