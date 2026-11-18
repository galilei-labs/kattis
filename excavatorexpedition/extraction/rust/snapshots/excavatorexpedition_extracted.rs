#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type char63 = u64;

pub type uint = u64;

pub type sint = u64;

// Rocq: Excavatorexpedition.excavatorexpedition_implem.NEG
pub fn NEG() -> u64 {
  4611686018427387904u64
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.MONE
pub fn MONE() -> u64 {
  9223372036854775807u64
}

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: Rc<rocq_string::RocqString>) -> u64 {
  let tmp = rocq_string::length(&v0);
  std::mem::drop(v0);
  tmp
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

// Rocq: Excavatorexpedition.excavatorexpedition_implem.bdec
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

// Rocq: Excavatorexpedition.excavatorexpedition_implem.cnt_loop
// Variant: uncurried
pub fn cnt_loop_1(xsrc: Rc<Array<u64>>, E: u64, k: u64, c: Rc<Array<u64>>) -> Rc<Array<u64>> {
  cnt_loop(xsrc, E, k, c, ())
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.cnt_loop (local: cnt_loop)
// Variant: uncurried, lifted
pub fn cnt_loop(xsrc: Rc<Array<u64>>, E: u64, k: u64, c: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, E);
  match bdec(tmp) {
    sumbool::left => {
      let u = rocq_array::get::<u64>(&xsrc, k);
      let tmp_1 = add(k, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&c, u);
      let tmp_3 = rocq_array::set::<u64>(c, u, add(tmp_2, 1u64));
      cnt_loop(xsrc, E, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(xsrc);
      c
    },
  }
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.pre_loop
// Variant: uncurried
pub fn pre_loop_1(V: u64, i: u64, c: Rc<Array<u64>>) -> Rc<Array<u64>> {
  pre_loop(V, i, c, ())
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.pre_loop (local: pre_loop)
// Variant: uncurried, lifted
pub fn pre_loop(V: u64, i: u64, c: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, V);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = add(i, 1u64);
      let tmp_3 = rocq_array::get::<u64>(&c, add(i, 1u64));
      let tmp_4 = rocq_array::get::<u64>(&c, i);
      let tmp_5 = rocq_array::set::<u64>(c, tmp_2, add(tmp_3, tmp_4));
      pre_loop(V, tmp_1, tmp_5, ())
    },
    sumbool::right => {
      c
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.rfill_loop
// Variant: uncurried
pub fn rfill_loop_1(xsrc: Rc<Array<u64>>, xdst: Rc<Array<u64>>, k: u64, c: Rc<Array<u64>>, adj: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  rfill_loop(xsrc, xdst, k, c, adj, ())
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.rfill_loop (local: rfill_loop)
// Variant: uncurried, lifted
pub fn rfill_loop(xsrc: Rc<Array<u64>>, xdst: Rc<Array<u64>>, k: u64, c: Rc<Array<u64>>, adj: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(0u64, k);
  match bdec(tmp) {
    sumbool::left => {
      let k1 = sub(k, 1u64);
      let u = rocq_array::get::<u64>(&xsrc, k1);
      let tmp_1 = rocq_array::get::<u64>(&c, u);
      let p = sub(tmp_1, 1u64);
      let tmp_2 = rocq_array::set::<u64>(c, u, p);
      let tmp_3 = rocq_array::get::<u64>(&xdst, k1);
      let tmp_4 = rocq_array::set::<u64>(adj, p, tmp_3);
      rfill_loop(xsrc, xdst, k1, tmp_2, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(xsrc);
      std::mem::drop(xdst);
      (c, adj)
    },
  }
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.ind_loop
// Variant: uncurried
pub fn ind_loop_1(adj: Rc<Array<u64>>, E: u64, j: u64, d: Rc<Array<u64>>) -> Rc<Array<u64>> {
  ind_loop(adj, E, j, d, ())
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.ind_loop (local: ind_loop)
// Variant: uncurried, lifted
pub fn ind_loop(adj: Rc<Array<u64>>, E: u64, j: u64, d: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(j, E);
  match bdec(tmp) {
    sumbool::left => {
      let v = rocq_array::get::<u64>(&adj, j);
      let tmp_1 = add(j, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&d, v);
      let tmp_3 = rocq_array::set::<u64>(d, v, add(tmp_2, 1u64));
      ind_loop(adj, E, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(adj);
      d
    },
  }
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.q0_loop
// Variant: uncurried
pub fn q0_loop_1(V: u64, x: u64, d: Rc<Array<u64>>, q: Rc<Array<u64>>, t: u64) -> (Rc<Array<u64>>, u64) {
  q0_loop(V, x, d, q, t, ())
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.q0_loop (local: q0_loop)
// Variant: uncurried, lifted
pub fn q0_loop(V: u64, x: u64, d: Rc<Array<u64>>, q: Rc<Array<u64>>, t: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let tmp = ltb(x, V);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&d, x);
      if eqb(tmp_1, 0u64) {
        let tmp_2 = add(x, 1u64);
        let tmp_3 = rocq_array::set::<u64>(q, t, x);
        q0_loop(V, tmp_2, d, tmp_3, add(t, 1u64), ())
      } else {
        q0_loop(V, add(x, 1u64), d, q, t, ())
      }
    },
    sumbool::right => {
      std::mem::drop(d);
      (q, t)
    },
  }
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let tmp = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.wt
// Variant: uncurried
pub fn wt(xs: Rc<rocq_string::RocqString>, V: u64, v: u64) -> u64 {
  if eqb(v, 0u64) {
    std::mem::drop(xs);
    0u64
  } else {
    let tmp = sub(V, 1u64);
    if eqb(v, tmp) {
      std::mem::drop(xs);
      0u64
    } else {
      let c = get(xs, v);
      if eqb(c, 88u64) {
        1u64
      } else {
        if eqb(c, 46u64) {
          __rocq_global_365
        } else {
          0u64
        }
      }
    }
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb
// Variant: uncurried
pub fn ltsb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltsb(v0, v1)
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.relax1
// Variant: uncurried
pub fn relax1(xs: Rc<rocq_string::RocqString>, V: u64, du: u64, v: u64, dist: Rc<Array<u64>>) -> Rc<Array<u64>> {
  if eqb(du, __rocq_global_349) {
    std::mem::drop(xs);
    dist
  } else {
    let cand = add(du, wt(xs, V, v));
    let tmp = rocq_array::get::<u64>(&dist, v);
    if ltsb(tmp, cand) {
      rocq_array::set::<u64>(dist, v, cand)
    } else {
      dist
    }
  }
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.relax_loop
// Variant: uncurried
pub fn relax_loop_1(xs: Rc<rocq_string::RocqString>, V: u64, adj: Rc<Array<u64>>, du: u64, hi: u64, j: u64, d: Rc<Array<u64>>, dist: Rc<Array<u64>>, q: Rc<Array<u64>>, t: u64) -> (((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64) {
  relax_loop(xs, V, adj, du, hi, j, d, dist, q, t, ())
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.relax_loop (local: relax_loop)
// Variant: uncurried, lifted
pub fn relax_loop(xs: Rc<rocq_string::RocqString>, V: u64, adj: Rc<Array<u64>>, du: u64, hi: u64, j: u64, d: Rc<Array<u64>>, dist: Rc<Array<u64>>, q: Rc<Array<u64>>, t: u64, _H: ()) -> (((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64) {
  let tmp = ltb(j, hi);
  match bdec(tmp) {
    sumbool::left => {
      let v = rocq_array::get::<u64>(&adj, j);
      let xs_clone = Rc::clone(&xs);
      let dist_ = relax1(xs_clone, V, du, v, dist);
      let tmp_1 = rocq_array::get::<u64>(&d, v);
      let e = sub(tmp_1, 1u64);
      if eqb(e, 0u64) {
        let tmp_2 = add(j, 1u64);
        let tmp_3 = rocq_array::set::<u64>(d, v, e);
        let tmp_4 = rocq_array::set::<u64>(q, t, v);
        relax_loop(xs, V, adj, du, hi, tmp_2, tmp_3, dist_, tmp_4, add(t, 1u64), ())
      } else {
        let tmp_5 = add(j, 1u64);
        let tmp_6 = rocq_array::set::<u64>(d, v, e);
        relax_loop(xs, V, adj, du, hi, tmp_5, tmp_6, dist_, q, t, ())
      }
    },
    sumbool::right => {
      std::mem::drop(xs);
      std::mem::drop(adj);
      (((d, dist), q), t)
    },
  }
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.kahn_loop
// Variant: uncurried
pub fn kahn_loop_1(xs: Rc<rocq_string::RocqString>, V: u64, off: Rc<Array<u64>>, adj: Rc<Array<u64>>, h: u64, d: Rc<Array<u64>>, dist: Rc<Array<u64>>, q: Rc<Array<u64>>, t: u64) -> Rc<Array<u64>> {
  kahn_loop(xs, V, off, adj, h, d, dist, q, t, ())
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.kahn_loop (local: kahn_loop)
// Variant: uncurried, lifted
pub fn kahn_loop(xs: Rc<rocq_string::RocqString>, V: u64, off: Rc<Array<u64>>, adj: Rc<Array<u64>>, h: u64, d: Rc<Array<u64>>, dist: Rc<Array<u64>>, q: Rc<Array<u64>>, t: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(h, t);
  match bdec(tmp) {
    sumbool::left => {
      let u = rocq_array::get::<u64>(&q, h);
      let lo = rocq_array::get::<u64>(&off, u);
      let tmp_1 = rocq_array::get::<u64>(&dist, u);
      let tmp_2 = rocq_array::get::<u64>(&off, add(u, 1u64));
      let xs_clone = Rc::clone(&xs);
      let adj_clone = Rc::clone(&adj);
      let tmp_3 = relax_loop_1(xs_clone, V, adj_clone, tmp_1, tmp_2, lo, d, dist, q, t);
      match tmp_3 {
        (v70, v72) => {
          match v70 {
            (v75, v77) => {
              match v75 {
                (v80, v82) => {
                  kahn_loop(xs, V, off, adj, add(h, 1u64), v80, v82, v77, v72, ())
                },
              }
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(xs);
      std::mem::drop(off);
      std::mem::drop(adj);
      std::mem::drop(d);
      std::mem::drop(q);
      dist
    },
  }
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.excavator_impl
// Variant: uncurried
pub fn excavator_impl(xs: Rc<rocq_string::RocqString>, xsrc: Rc<Array<u64>>, xdst: Rc<Array<u64>>) -> u64 {
  let xs_clone = Rc::clone(&xs);
  let V = length(xs_clone);
  let E = rocq_array::length::<u64>(&xsrc);
  let tmp = rocq_array::make::<u64>(add(V, 1u64), 0u64);
  let xsrc_clone = Rc::clone(&xsrc);
  let c = cnt_loop_1(xsrc_clone, E, 0u64, tmp);
  let c_1 = pre_loop_1(V, 0u64, c);
  let tmp_1 = rocq_array::make::<u64>(E, 0u64);
  let tmp_2 = rfill_loop_1(xsrc, xdst, E, c_1, tmp_1);
  match tmp_2 {
    (v68, v70) => {
      let off = &v70;
      let tmp_3 = rocq_array::make::<u64>(V, 0u64);
      let off_clone = Rc::clone(off);
      let d = ind_loop_1(off_clone, E, 0u64, tmp_3);
      let tmp_4 = rocq_array::make::<u64>(V, 0u64);
      let d_clone = Rc::clone(&d);
      let tmp_5 = q0_loop_1(V, 0u64, d_clone, tmp_4, 0u64);
      match tmp_5 {
        (v117, v119) => {
          let tmp_6 = rocq_array::make::<u64>(V, __rocq_global_349);
          let dist = rocq_array::set::<u64>(tmp_6, 0u64, 0u64);
          let dist_1 = kahn_loop_1(xs, V, v68, v70, 0u64, d, dist, v117, v119);
          let tmp_7 = rocq_array::get::<u64>(&dist_1, sub(V, 1u64));
          std::mem::drop(dist_1);
          tmp_7
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
const __rocq_global_349: u64 = 4611686018427387904u64;
const __rocq_global_365: u64 = 9223372036854775807u64;