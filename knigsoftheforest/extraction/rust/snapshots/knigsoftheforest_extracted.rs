// Generated from OwnedANF. This printer is not verified.
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

// Rocq: Knigsoftheforest.knigsoftheforest_implem.knigsoftheforest
// Variant: uncurried
pub fn knigsoftheforest() -> Rc<dyn Fn(u64, u64, u64, u64, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<option<u64>>> {
  let v0: fn(u64, u64, u64, u64, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<option<u64>> = knigs_impl;
  let v1: Rc<dyn Fn(u64, u64, u64, u64, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<option<u64>>> = Rc::new(v0);
  v1
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.knigsoftheforest
pub fn knigsoftheforest_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>>>> = knigs_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>>>>> = Rc::new(v0);
  v1
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

// Rocq: Knigsoftheforest.knigsoftheforest_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.sift_up
// Variant: uncurried
pub fn sift_up_1(h: Rc<Array<u64>>, i: u64) -> Rc<Array<u64>> {
  sift_up(h, i, ())
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.sift_up (local: sift_up)
// Variant: uncurried, lifted
pub fn sift_up(h: Rc<Array<u64>>, i: u64, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(0u64, i);
  match bdec(v12) {
    sumbool::left => {
      let q = div(sub(i, 1u64), 2u64);
      let v32 = &h;
      let vi = rocq_array::get::<u64>(&v32, i);
      let v36 = &h;
      let vq = rocq_array::get::<u64>(&v36, q);
      let v47 = ltb(vq, vi);
      match bdec(v47) {
        sumbool::left => {
          let v58 = rocq_array::set::<u64>(h, i, vq);
          let v64 = rocq_array::set::<u64>(v58, q, vi);
          sift_up(v64, q, ())
        },
        sumbool::right => {
          h
        },
      }
    },
    sumbool::right => {
      h
    },
  }
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.insert
// Variant: uncurried
pub fn insert(h: Rc<Array<u64>>, s: u64, v: u64) -> Rc<Array<u64>> {
  let v11 = rocq_array::set::<u64>(h, s, v);
  sift_up_1(v11, s)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.step
// Variant: uncurried
pub fn step(st: ((Rc<Array<u64>>, u64), Rc<Array<u64>>), yr: u64, sv: u64) -> ((Rc<Array<u64>>, u64), Rc<Array<u64>>) {
  match st {
    (v4, v6) => {
      match v4 {
        (v9, v11) => {
          match eqb(yr, 2011u64) {
            true => {
              let v29 = insert(v9, v11, sv);
              ((v29, add(v11, 1u64)), v6)
            },
            false => {
              let v56 = (v9, v11);
              let v72 = rocq_array::set::<u64>(v6, sub(yr, 2011u64), sv);
              (v56, v72)
            },
          }
        },
      }
    },
  }
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.fill
// Variant: uncurried
pub fn fill_1(ys: Rc<Array<u64>>, ps: Rc<Array<u64>>, m: u64, i: u64, st: ((Rc<Array<u64>>, u64), Rc<Array<u64>>)) -> ((Rc<Array<u64>>, u64), Rc<Array<u64>>) {
  fill(ys, ps, m, i, st, ())
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.fill (local: fill)
// Variant: uncurried, lifted
pub fn fill(ys: Rc<Array<u64>>, ps: Rc<Array<u64>>, m: u64, i: u64, st: ((Rc<Array<u64>>, u64), Rc<Array<u64>>), _H: ()) -> ((Rc<Array<u64>>, u64), Rc<Array<u64>>) {
  let v13 = ltb(i, m);
  match bdec(v13) {
    sumbool::left => {
      let v24 = add(i, 1u64);
      let v26 = &ys;
      let v29 = rocq_array::get::<u64>(&v26, i);
      let v30 = &ps;
      let v33 = rocq_array::get::<u64>(&v30, i);
      fill(ys, ps, m, v24, step(st, v29, v33), ())
    },
    sumbool::right => {
      std::mem::drop(ys);
      std::mem::drop(ps);
      st
    },
  }
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.pick
// Variant: uncurried
pub fn pick(h: Rc<Array<u64>>, s: u64, l: u64) -> u64 {
  let v12 = add(l, 1u64);
  match ltb(v12, s) {
    true => {
      let v19 = &h;
      let v22 = rocq_array::get::<u64>(&v19, l);
      let v30 = add(l, 1u64);
      let v31 = &h;
      let v34 = rocq_array::get::<u64>(&v31, v30);
      match ltb(v22, v34) {
        true => {
          std::mem::drop(h);
          add(l, 1u64)
        },
        false => {
          std::mem::drop(h);
          l
        },
      }
    },
    false => {
      std::mem::drop(h);
      l
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.sift_down
// Variant: uncurried
pub fn sift_down_1(h: Rc<Array<u64>>, s: u64, i: u64) -> Rc<Array<u64>> {
  sift_down(h, s, i, ())
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.sift_down (local: sift_down)
// Variant: uncurried, lifted
pub fn sift_down(h: Rc<Array<u64>>, s: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let v19 = ltb(i, div(s, 2u64));
  match bdec(v19) {
    sumbool::left => {
      let v39 = add(mul(2u64, i), 1u64);
      let v42 = Rc::clone(&h);
      let c = pick(v42, s, v39);
      let v48 = &h;
      let vi = rocq_array::get::<u64>(&v48, i);
      let v52 = &h;
      let vc = rocq_array::get::<u64>(&v52, c);
      let v63 = ltb(vi, vc);
      match bdec(v63) {
        sumbool::left => {
          let v74 = rocq_array::set::<u64>(h, i, vc);
          let v80 = rocq_array::set::<u64>(v74, c, vi);
          sift_down(v80, s, c, ())
        },
        sumbool::right => {
          h
        },
      }
    },
    sumbool::right => {
      h
    },
  }
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.extract
// Variant: uncurried
pub fn extract(h: Rc<Array<u64>>, s: u64) -> Rc<Array<u64>> {
  let s1 = sub(s, 1u64);
  let v13 = &h;
  let v16 = rocq_array::get::<u64>(&v13, s1);
  let v23 = rocq_array::set::<u64>(h, 0u64, v16);
  sift_down_1(v23, s1, 0u64)
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.sim
// Variant: uncurried
pub fn sim_1(t: Rc<Array<u64>>, h: Rc<Array<u64>>, n: u64, p: u64, s: u64, d: u64) -> Rc<option<u64>> {
  sim(t, h, n, p, s, d, ())
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.sim (local: sim)
// Variant: uncurried, lifted
pub fn sim(t: Rc<Array<u64>>, h: Rc<Array<u64>>, n: u64, p: u64, s: u64, d: u64, _H: ()) -> Rc<option<u64>> {
  let v14 = ltb(d, n);
  match bdec(v14) {
    sumbool::left => {
      match eqb(s, 0u64) {
        true => {
          std::mem::drop(t);
          std::mem::drop(h);
          Rc::new(option::<u64>::None)
        },
        false => {
          let v33 = 0u64;
          let v34 = &h;
          let top = rocq_array::get::<u64>(&v34, v33);
          match eqb(top, p) {
            true => {
              std::mem::drop(t);
              std::mem::drop(h);
              Rc::new(option::<u64>::Some(add(2011u64, d)))
            },
            false => {
              let v69 = add(d, 1u64);
              match ltb(v69, n) {
                true => {
                  let v81 = extract(h, s);
                  let v89 = sub(s, 1u64);
                  let v97 = add(d, 1u64);
                  let v98 = &t;
                  let v101 = rocq_array::get::<u64>(&v98, v97);
                  let v108 = insert(v81, v89, v101);
                  sim(t, v108, n, p, s, add(d, 1u64), ())
                },
                false => {
                  std::mem::drop(t);
                  std::mem::drop(h);
                  Rc::new(option::<u64>::None)
                },
              }
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(t);
      std::mem::drop(h);
      Rc::new(option::<u64>::None)
    },
  }
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.knigs_impl
// Variant: uncurried
pub fn knigs_impl(_k: u64, n: u64, y: u64, p: u64, ys: Rc<Array<u64>>, ps: Rc<Array<u64>>) -> Rc<option<u64>> {
  let v6 = &ys;
  let m = rocq_array::length::<u64>(&v6);
  let v23 = rocq_array::make::<u64>(add(m, 1u64), 0u64);
  let v30 = (v23, 0u64);
  let v38 = rocq_array::make::<u64>(n, 0u64);
  let st0 = step((v30, v38), y, p);
  let v65 = fill_1(ys, ps, m, 0u64, st0);
  match v65 {
    (v67, v69) => {
      match v67 {
        (v72, v74) => {
          sim_1(v69, v72, n, p, v74, 0u64)
        },
      }
    },
  }
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.knigs_impl
pub fn knigs_impl_curried(k: u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>>>> {
  let v3 = {
    move |n: u64| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>>> {
      let k = &k;
      let v8 = Clone::clone(k);
      let v11 = {
        move |y: u64| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>> {
          let k = &v8;
          let n = &n;
          let v18 = Clone::clone(k);
          let v20 = Clone::clone(n);
          let v23 = {
            move |p: u64| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>> {
              let k = &v18;
              let n = &v20;
              let y = &y;
              let v32 = Clone::clone(k);
              let v34 = Clone::clone(n);
              let v36 = Clone::clone(y);
              let v39 = {
                move |ys: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>> {
                  let k = &v32;
                  let n = &v34;
                  let y = &v36;
                  let p = &p;
                  let v50 = Clone::clone(k);
                  let v52 = Clone::clone(n);
                  let v54 = Clone::clone(y);
                  let v56 = Clone::clone(p);
                  let v59 = {
                    move |ps: Rc<Array<u64>>| -> Rc<option<u64>> {
                      let v73 = Clone::clone(&v50);
                      let v75 = Clone::clone(&v52);
                      let v77 = Clone::clone(&v54);
                      let v79 = Clone::clone(&v56);
                      let v81 = Rc::clone(&ys);
                      knigs_impl(v73, v75, v77, v79, v81, ps)
                    }
                  };
                  let v87: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>> = Rc::new(v59);
                  v87
                }
              };
              let v91: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>> = Rc::new(v39);
              v91
            }
          };
          let v95: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>> = Rc::new(v23);
          v95
        }
      };
      let v99: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>>> = Rc::new(v11);
      v99
    }
  };
  let v103: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>>>> = Rc::new(v3);
  v103
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

pub fn run() -> Rc<dyn Fn(u64, u64, u64, u64, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<option<u64>>> {
  let v0: Rc<dyn Fn(u64, u64, u64, u64, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<option<u64>>> = __rocq_global_484.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_484: Rc<dyn Fn(u64, u64, u64, u64, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<option<u64>>> = knigsoftheforest(); }
std::thread_local! { static __rocq_global_487: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>>>>> = knigsoftheforest_curried(); }