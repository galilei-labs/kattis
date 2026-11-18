#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub enum answer<D: 'static> {
  Dist { distance: D },
  Impossible,
  MinusInfinity,
}

impl<D: Clone + 'static> Clone for answer<D> {
  fn clone(&self) -> Self {
    match self {
      answer::Dist { distance: __field0 } => answer::Dist { distance: Clone::clone(__field0) },
      answer::Impossible => answer::Impossible,
      answer::MinusInfinity => answer::MinusInfinity,
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

pub type sint = u64;

// Rocq: Shortestpath3.shortestpath3_implem.INF
pub fn INF() -> u64 {
  4611686018427387903u64
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

// Rocq: Shortestpath3.shortestpath3_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb
// Variant: uncurried
pub fn ltsb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltsb(v0, v1)
}

// Rocq: Shortestpath3.shortestpath3_implem.relax
// Variant: uncurried
pub fn relax(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, j: u64, d: Rc<Array<u64>>, ch: bool) -> (Rc<Array<u64>>, bool) {
  let tmp = rocq_array::get::<u64>(&us, j);
  let du = rocq_array::get::<u64>(&d, tmp);
  if eqb(du, __rocq_global_7) {
    std::mem::drop(vs);
    std::mem::drop(ws);
    std::mem::drop(us);
    (d, ch)
  } else {
    let v = rocq_array::get::<u64>(&vs, j);
    let tmp_1 = rocq_array::get::<u64>(&ws, j);
    let nd = add(du, tmp_1);
    let tmp_2 = rocq_array::get::<u64>(&d, v);
    if ltsb(nd, tmp_2) {
      std::mem::drop(vs);
      std::mem::drop(ws);
      std::mem::drop(us);
      let tmp_3 = rocq_array::set::<u64>(d, v, nd);
      (tmp_3, true)
    } else {
      std::mem::drop(vs);
      std::mem::drop(ws);
      std::mem::drop(us);
      (d, ch)
    }
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.edges_loop
// Variant: uncurried
pub fn edges_loop_1(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, m: u64, j: u64, d: Rc<Array<u64>>, ch: bool) -> (Rc<Array<u64>>, bool) {
  edges_loop(us, vs, ws, m, j, d, ch, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.edges_loop (local: edges_loop)
// Variant: uncurried, lifted
pub fn edges_loop(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, m: u64, j: u64, d: Rc<Array<u64>>, ch: bool, _H: ()) -> (Rc<Array<u64>>, bool) {
  let tmp = ltb(j, m);
  match bdec(tmp) {
    sumbool::left => {
      let us_clone = Rc::clone(&us);
      let vs_clone = Rc::clone(&vs);
      let ws_clone = Rc::clone(&ws);
      let tmp_1 = relax(us_clone, vs_clone, ws_clone, j, d, ch);
      match tmp_1 {
        (v37, v39) => {
          edges_loop(us, vs, ws, m, add(j, 1u64), v37, v39, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(us);
      std::mem::drop(vs);
      std::mem::drop(ws);
      (d, ch)
    },
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.rounds_loop
// Variant: uncurried
pub fn rounds_loop_1(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, m: u64, R: u64, k: u64, d: Rc<Array<u64>>) -> Rc<Array<u64>> {
  rounds_loop(us, vs, ws, m, R, k, d, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.rounds_loop (local: rounds_loop)
// Variant: uncurried, lifted
pub fn rounds_loop(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, m: u64, R: u64, k: u64, d: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, R);
  match bdec(tmp) {
    sumbool::left => {
      let us_clone = Rc::clone(&us);
      let vs_clone = Rc::clone(&vs);
      let ws_clone = Rc::clone(&ws);
      let tmp_1 = edges_loop_1(us_clone, vs_clone, ws_clone, m, 0u64, d, false);
      match tmp_1 {
        (v43, v45) => {
          if v45 {
            rounds_loop(us, vs, ws, m, R, add(k, 1u64), v43, ())
          } else {
            std::mem::drop(us);
            std::mem::drop(vs);
            std::mem::drop(ws);
            v43
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(us);
      std::mem::drop(vs);
      std::mem::drop(ws);
      d
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
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

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  if b {
    false
  } else {
    true
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.seed_loop
// Variant: uncurried
pub fn seed_loop_1(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, d: Rc<Array<u64>>, m: u64, j: u64, mk: Rc<Array<u64>>, q: Rc<Array<u64>>, tl: u64) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  seed_loop(us, vs, ws, d, m, j, mk, q, tl, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.seed_loop (local: seed_loop)
// Variant: uncurried, lifted
pub fn seed_loop(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, d: Rc<Array<u64>>, m: u64, j: u64, mk: Rc<Array<u64>>, q: Rc<Array<u64>>, tl: u64, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let tmp = ltb(j, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&us, j);
      let du = rocq_array::get::<u64>(&d, tmp_1);
      let v = rocq_array::get::<u64>(&vs, j);
      let tmp_2 = negb(eqb(du, __rocq_global_7));
      let tmp_3 = rocq_array::get::<u64>(&ws, j);
      let tmp_4 = add(du, tmp_3);
      let tmp_5 = rocq_array::get::<u64>(&d, v);
      let tmp_6 = andb(tmp_2, ltsb(tmp_4, tmp_5));
      let tmp_7 = rocq_array::get::<u64>(&mk, v);
      let tmp_8 = eqb(tmp_7, 0u64);
      if andb(tmp_6, tmp_8) {
        let tmp_9 = add(j, 1u64);
        let tmp_10 = rocq_array::set::<u64>(mk, v, 1u64);
        let tmp_11 = rocq_array::set::<u64>(q, tl, v);
        seed_loop(us, vs, ws, d, m, tmp_9, tmp_10, tmp_11, add(tl, 1u64), ())
      } else {
        seed_loop(us, vs, ws, d, m, add(j, 1u64), mk, q, tl, ())
      }
    },
    sumbool::right => {
      std::mem::drop(us);
      std::mem::drop(vs);
      std::mem::drop(ws);
      std::mem::drop(d);
      ((mk, q), tl)
    },
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.build_loop
// Variant: uncurried
pub fn build_loop_1(us: Rc<Array<u64>>, m: u64, j: u64, hd: Rc<Array<u64>>, nx: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  build_loop(us, m, j, hd, nx, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.build_loop (local: build_loop)
// Variant: uncurried, lifted
pub fn build_loop(us: Rc<Array<u64>>, m: u64, j: u64, hd: Rc<Array<u64>>, nx: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(j, m);
  match bdec(tmp) {
    sumbool::left => {
      let u = rocq_array::get::<u64>(&us, j);
      let h = rocq_array::get::<u64>(&hd, u);
      let tmp_1 = add(j, 1u64);
      let tmp_2 = rocq_array::set::<u64>(hd, u, add(j, 1u64));
      let tmp_3 = rocq_array::set::<u64>(nx, j, h);
      build_loop(us, m, tmp_1, tmp_2, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(us);
      (hd, nx)
    },
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.adj_loop
// Variant: uncurried
pub fn adj_loop_1(vs: Rc<Array<u64>>, nx: Rc<Array<u64>>, e: u64, mk: Rc<Array<u64>>, q: Rc<Array<u64>>, tl: u64) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  adj_loop(vs, nx, e, mk, q, tl, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.adj_loop (local: adj_loop)
// Variant: uncurried, lifted
pub fn adj_loop(vs: Rc<Array<u64>>, nx: Rc<Array<u64>>, e: u64, mk: Rc<Array<u64>>, q: Rc<Array<u64>>, tl: u64, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let tmp = ltb(0u64, e);
  match bdec(tmp) {
    sumbool::left => {
      let j = sub(e, 1u64);
      let v = rocq_array::get::<u64>(&vs, j);
      let e_ = rocq_array::get::<u64>(&nx, j);
      let tmp_1 = ltb(e_, e);
      match bdec(tmp_1) {
        sumbool::left => {
          let tmp_2 = rocq_array::get::<u64>(&mk, v);
          if eqb(tmp_2, 0u64) {
            let tmp_3 = rocq_array::set::<u64>(mk, v, 1u64);
            let tmp_4 = rocq_array::set::<u64>(q, tl, v);
            adj_loop(vs, nx, e_, tmp_3, tmp_4, add(tl, 1u64), ())
          } else {
            adj_loop(vs, nx, e_, mk, q, tl, ())
          }
        },
        sumbool::right => {
          std::mem::drop(vs);
          std::mem::drop(nx);
          ((mk, q), tl)
        },
      }
    },
    sumbool::right => {
      std::mem::drop(vs);
      std::mem::drop(nx);
      ((mk, q), tl)
    },
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.bfs_loop
// Variant: uncurried
pub fn bfs_loop_1(vs: Rc<Array<u64>>, hd: Rc<Array<u64>>, nx: Rc<Array<u64>>, n: u64, h: u64, mk: Rc<Array<u64>>, q: Rc<Array<u64>>, tl: u64) -> Rc<Array<u64>> {
  bfs_loop(vs, hd, nx, n, h, mk, q, tl, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.bfs_loop (local: bfs_loop)
// Variant: uncurried, lifted
pub fn bfs_loop(vs: Rc<Array<u64>>, hd: Rc<Array<u64>>, nx: Rc<Array<u64>>, n: u64, h: u64, mk: Rc<Array<u64>>, q: Rc<Array<u64>>, tl: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(h, tl);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = ltb(h, n);
      match bdec(tmp_1) {
        sumbool::left => {
          let x = rocq_array::get::<u64>(&q, h);
          let tmp_2 = rocq_array::get::<u64>(&hd, x);
          let vs_clone = Rc::clone(&vs);
          let nx_clone = Rc::clone(&nx);
          let tmp_3 = adj_loop_1(vs_clone, nx_clone, tmp_2, mk, q, tl);
          match tmp_3 {
            (v56, v58) => {
              match v56 {
                (v61, v63) => {
                  bfs_loop(vs, hd, nx, n, add(h, 1u64), v61, v63, v58, ())
                },
              }
            },
          }
        },
        sumbool::right => {
          std::mem::drop(vs);
          std::mem::drop(hd);
          std::mem::drop(nx);
          std::mem::drop(q);
          mk
        },
      }
    },
    sumbool::right => {
      std::mem::drop(vs);
      std::mem::drop(hd);
      std::mem::drop(nx);
      std::mem::drop(q);
      mk
    },
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.answer_of
// Variant: uncurried
pub fn answer_of(d: Rc<Array<u64>>, mk: Rc<Array<u64>>, t: u64) -> Rc<answer<u64>> {
  let x = rocq_array::get::<u64>(&d, t);
  if eqb(x, __rocq_global_7) {
    std::mem::drop(mk);
    std::mem::drop(d);
    Rc::new(answer::<u64>::Impossible)
  } else {
    let tmp = rocq_array::get::<u64>(&mk, t);
    if eqb(tmp, 0u64) {
      std::mem::drop(mk);
      std::mem::drop(d);
      Rc::new(answer::<u64>::Dist { distance: x })
    } else {
      std::mem::drop(mk);
      std::mem::drop(d);
      Rc::new(answer::<u64>::MinusInfinity)
    }
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.ans_loop
// Variant: uncurried
pub fn ans_loop_1(d: Rc<Array<u64>>, mk: Rc<Array<u64>>, qs: Rc<Array<u64>>, Q: u64, i: u64, out: Rc<Array<Rc<answer<u64>>>>) -> Rc<Array<Rc<answer<u64>>>> {
  ans_loop(d, mk, qs, Q, i, out, ())
}

// Rocq: Shortestpath3.shortestpath3_implem.ans_loop (local: ans_loop)
// Variant: uncurried, lifted
pub fn ans_loop(d: Rc<Array<u64>>, mk: Rc<Array<u64>>, qs: Rc<Array<u64>>, Q: u64, i: u64, out: Rc<Array<Rc<answer<u64>>>>, _H: ()) -> Rc<Array<Rc<answer<u64>>>> {
  let tmp = ltb(i, Q);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&qs, i);
      let d_clone = Rc::clone(&d);
      let mk_clone = Rc::clone(&mk);
      let a = answer_of(d_clone, mk_clone, tmp_1);
      let tmp_2 = add(i, 1u64);
      let tmp_3 = rocq_array::set::<Rc<answer<u64>>>(out, i, a);
      ans_loop(d, mk, qs, Q, tmp_2, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(d);
      std::mem::drop(mk);
      std::mem::drop(qs);
      out
    },
  }
}

// Rocq: Shortestpath3.shortestpath3_implem.shortestpath3_impl
// Variant: uncurried
pub fn shortestpath3_impl(n: u64, s: u64, us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, qs: Rc<Array<u64>>) -> Rc<Array<Rc<answer<u64>>>> {
  let m = rocq_array::length::<u64>(&us);
  let tmp = rocq_array::make::<u64>(n, __rocq_global_7);
  let d0 = rocq_array::set::<u64>(tmp, s, 0u64);
  let tmp_1 = sub(n, 1u64);
  let us_clone = Rc::clone(&us);
  let vs_clone = Rc::clone(&vs);
  let ws_clone = Rc::clone(&ws);
  let d = rounds_loop_1(us_clone, vs_clone, ws_clone, m, tmp_1, 0u64, d0);
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  let tmp_3 = rocq_array::make::<u64>(n, 0u64);
  let us_clone_1 = Rc::clone(&us);
  let vs_clone_1 = Rc::clone(&vs);
  let d_clone = Rc::clone(&d);
  let tmp_4 = seed_loop_1(us_clone_1, vs_clone_1, ws, d_clone, m, 0u64, tmp_2, tmp_3, 0u64);
  match tmp_4 {
    (v94, v96) => {
      match v94 {
        (v99, v101) => {
          let tmp_5 = rocq_array::make::<u64>(n, 0u64);
          let tmp_6 = rocq_array::make::<u64>(m, 0u64);
          let tmp_7 = build_loop_1(us, m, 0u64, tmp_5, tmp_6);
          match tmp_7 {
            (v132, v134) => {
              let mk_ = bfs_loop_1(vs, v132, v134, n, 0u64, v99, v101, v96);
              let Q = rocq_array::length::<u64>(&qs);
              let tmp_8 = rocq_array::make::<Rc<answer<u64>>>(Q, Rc::new(answer::<u64>::Impossible));
              ans_loop_1(d, mk_, qs, Q, 0u64, tmp_8)
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
const __rocq_global_7: u64 = 4611686018427387903u64;