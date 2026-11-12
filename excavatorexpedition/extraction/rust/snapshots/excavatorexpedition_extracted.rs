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

// Rocq: Excavatorexpedition.excavatorexpedition_implem.excavator
// Variant: uncurried
pub fn excavator() -> Rc<dyn Fn(Rc<rocq_string::RocqString>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> {
  let v0: fn(Rc<rocq_string::RocqString>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64 = excavator_impl;
  let v1: Rc<dyn Fn(Rc<rocq_string::RocqString>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> = Rc::new(v0);
  v1
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.excavator
pub fn excavator_curried() -> Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>> {
  let v0: fn(Rc<rocq_string::RocqString>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> = excavator_impl_curried;
  let v1: Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: Rc<rocq_string::RocqString>) -> u64 {
  let v2 = rocq_string::length(&v0);
  std::mem::drop(v0);
  v2
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

// Rocq: Excavatorexpedition.excavatorexpedition_implem.cnt_loop
// Variant: uncurried
pub fn cnt_loop_1(xsrc: Rc<Array<u64>>, E: u64, k: u64, c: Rc<Array<u64>>) -> Rc<Array<u64>> {
  cnt_loop(xsrc, E, k, c, ())
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.cnt_loop (local: cnt_loop)
// Variant: uncurried, lifted
pub fn cnt_loop(xsrc: Rc<Array<u64>>, E: u64, k: u64, c: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(k, E);
  match bdec(v12) {
    sumbool::left => {
      let v16 = &xsrc;
      let u = rocq_array::get::<u64>(&v16, k);
      let v27 = add(k, 1u64);
      let v29 = &c;
      let v32 = rocq_array::get::<u64>(&v29, u);
      let v46 = rocq_array::set::<u64>(c, u, add(v32, 1u64));
      cnt_loop(xsrc, E, v27, v46, ())
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
  let v11 = ltb(i, V);
  match bdec(v11) {
    sumbool::left => {
      let v22 = add(i, 1u64);
      let v30 = add(i, 1u64);
      let v39 = add(i, 1u64);
      let v40 = &c;
      let v43 = rocq_array::get::<u64>(&v40, v39);
      let v44 = &c;
      let v47 = rocq_array::get::<u64>(&v44, i);
      let v59 = rocq_array::set::<u64>(c, v30, add(v43, v47));
      pre_loop(V, v22, v59, ())
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
  let v15 = ltb(0u64, k);
  match bdec(v15) {
    sumbool::left => {
      let k1 = sub(k, 1u64);
      let v27 = &xsrc;
      let u = rocq_array::get::<u64>(&v27, k1);
      let v32 = &c;
      let v35 = rocq_array::get::<u64>(&v32, u);
      let p = sub(v35, 1u64);
      let v49 = rocq_array::set::<u64>(c, u, p);
      let v50 = &xdst;
      let v53 = rocq_array::get::<u64>(&v50, k1);
      let v60 = rocq_array::set::<u64>(adj, p, v53);
      rfill_loop(xsrc, xdst, k1, v49, v60, ())
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
  let v12 = ltb(j, E);
  match bdec(v12) {
    sumbool::left => {
      let v16 = &adj;
      let v = rocq_array::get::<u64>(&v16, j);
      let v27 = add(j, 1u64);
      let v29 = &d;
      let v32 = rocq_array::get::<u64>(&v29, v);
      let v46 = rocq_array::set::<u64>(d, v, add(v32, 1u64));
      ind_loop(adj, E, v27, v46, ())
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
  let v13 = ltb(x, V);
  match bdec(v13) {
    sumbool::left => {
      let v18 = &d;
      let v21 = rocq_array::get::<u64>(&v18, x);
      match eqb(v21, 0u64) {
        true => {
          let v37 = add(x, 1u64);
          let v44 = rocq_array::set::<u64>(q, t, x);
          q0_loop(V, v37, d, v44, add(t, 1u64), ())
        },
        false => {
          q0_loop(V, add(x, 1u64), d, q, t, ())
        },
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
  let v5 = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  v5
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.wt
// Variant: uncurried
pub fn wt(xs: Rc<rocq_string::RocqString>, V: u64, v: u64) -> u64 {
  match eqb(v, 0u64) {
    true => {
      std::mem::drop(xs);
      0u64
    },
    false => {
      let v24 = sub(V, 1u64);
      match eqb(v, v24) {
        true => {
          std::mem::drop(xs);
          0u64
        },
        false => {
          let c = get(xs, v);
          match eqb(c, 88u64) {
            true => {
              1u64
            },
            false => {
              match eqb(c, 46u64) {
                true => {
                  __rocq_global_365
                },
                false => {
                  0u64
                },
              }
            },
          }
        },
      }
    },
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
  match eqb(du, __rocq_global_349) {
    true => {
      std::mem::drop(xs);
      dist
    },
    false => {
      let cand = add(du, wt(xs, V, v));
      let v30 = &dist;
      let v34 = rocq_array::get::<u64>(&v30, v);
      match ltsb(v34, cand) {
        true => {
          rocq_array::set::<u64>(dist, v, cand)
        },
        false => {
          dist
        },
      }
    },
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
  let v18 = ltb(j, hi);
  match bdec(v18) {
    sumbool::left => {
      let v22 = &adj;
      let v = rocq_array::get::<u64>(&v22, j);
      let v29 = Rc::clone(&xs);
      let dist_ = relax1(v29, V, du, v, dist);
      let v40 = &d;
      let v43 = rocq_array::get::<u64>(&v40, v);
      let e = sub(v43, 1u64);
      match eqb(e, 0u64) {
        true => {
          let v67 = add(j, 1u64);
          let v74 = rocq_array::set::<u64>(d, v, e);
          let v81 = rocq_array::set::<u64>(q, t, v);
          relax_loop(xs, V, adj, du, hi, v67, v74, dist_, v81, add(t, 1u64), ())
        },
        false => {
          let v125 = add(j, 1u64);
          let v132 = rocq_array::set::<u64>(d, v, e);
          relax_loop(xs, V, adj, du, hi, v125, v132, dist_, q, t, ())
        },
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
  let v17 = ltb(h, t);
  match bdec(v17) {
    sumbool::left => {
      let v21 = &q;
      let u = rocq_array::get::<u64>(&v21, h);
      let v25 = &off;
      let lo = rocq_array::get::<u64>(&v25, u);
      let v30 = &dist;
      let v33 = rocq_array::get::<u64>(&v30, u);
      let v41 = add(u, 1u64);
      let v42 = &off;
      let v45 = rocq_array::get::<u64>(&v42, v41);
      let v48 = Rc::clone(&xs);
      let v53 = Rc::clone(&adj);
      let v68 = relax_loop_1(v48, V, v53, v33, v45, lo, d, dist, q, t);
      match v68 {
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
  let v6 = Rc::clone(&xs);
  let V = length(v6);
  let v8 = &xsrc;
  let E = rocq_array::length::<u64>(&v8);
  let v27 = rocq_array::make::<u64>(add(V, 1u64), 0u64);
  let v30 = Rc::clone(&xsrc);
  let c = cnt_loop_1(v30, E, 0u64, v27);
  let c_1 = pre_loop_1(V, 0u64, c);
  let v55 = rocq_array::make::<u64>(E, 0u64);
  let v66 = rfill_loop_1(xsrc, xdst, E, c_1, v55);
  match v66 {
    (v68, v70) => {
      let off = &v70;
      let v82 = rocq_array::make::<u64>(V, 0u64);
      let v84 = Rc::clone(off);
      let d = ind_loop_1(v84, E, 0u64, v82);
      let v101 = rocq_array::make::<u64>(V, 0u64);
      let v110 = Rc::clone(&d);
      let v115 = q0_loop_1(V, 0u64, v110, v101, 0u64);
      match v115 {
        (v117, v119) => {
          let v126 = rocq_array::make::<u64>(V, __rocq_global_349);
          let dist = rocq_array::set::<u64>(v126, 0u64, 0u64);
          let dist_1 = kahn_loop_1(xs, V, v68, v70, 0u64, d, dist, v117, v119);
          let v167 = sub(V, 1u64);
          let v168 = &dist_1;
          let v171 = rocq_array::get::<u64>(&v168, v167);
          std::mem::drop(dist_1);
          v171
        },
      }
    },
  }
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.excavator_impl
pub fn excavator_impl_curried(xs: Rc<rocq_string::RocqString>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> {
  let v3 = {
    move |xsrc: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> u64> {
      let xs = &xs;
      let v8 = Rc::clone(xs);
      let v11 = {
        move |xdst: Rc<Array<u64>>| -> u64 {
          let v19 = Rc::clone(&v8);
          let v21 = Rc::clone(&xsrc);
          excavator_impl(v19, v21, xdst)
        }
      };
      let v27: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = Rc::new(v11);
      v27
    }
  };
  let v31: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(Rc<rocq_string::RocqString>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> {
  let v0: Rc<dyn Fn(Rc<rocq_string::RocqString>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> = __rocq_global_706.with(Clone::clone);
  v0
}
const __rocq_global_349: u64 = 4611686018427387904u64;
const __rocq_global_365: u64 = 9223372036854775807u64;
std::thread_local! { static __rocq_global_706: Rc<dyn Fn(Rc<rocq_string::RocqString>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> = excavator(); }
std::thread_local! { static __rocq_global_709: Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>> = excavator_curried(); }