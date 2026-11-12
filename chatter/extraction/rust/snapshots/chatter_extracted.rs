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

pub type uint = u64;

// Rocq: Chatter.chatter_implem.chatter
// Variant: uncurried
pub fn chatter() -> Rc<dyn Fn(u64, u64, u64, u64, u64) -> (u64, Rc<Array<(u64, u64)>>)> {
  let v0: fn(u64, u64, u64, u64, u64) -> (u64, Rc<Array<(u64, u64)>>) = chatter_impl;
  let v1: Rc<dyn Fn(u64, u64, u64, u64, u64) -> (u64, Rc<Array<(u64, u64)>>)> = Rc::new(v0);
  v1
}

// Rocq: Chatter.chatter_implem.chatter
pub fn chatter_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, Rc<Array<(u64, u64)>>)>>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, Rc<Array<(u64, u64)>>)>>>> = chatter_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, Rc<Array<(u64, u64)>>)>>>>> = Rc::new(v0);
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

// Rocq: Chatter.chatter_implem.bdec
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

// Rocq: Chatter.chatter_implem.init
// Variant: uncurried
pub fn init_1(n: u64, i: u64, rep: Rc<Array<u64>>, tl: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  init(n, i, rep, tl, ())
}

// Rocq: Chatter.chatter_implem.init (local: init)
// Variant: uncurried, lifted
pub fn init(n: u64, i: u64, rep: Rc<Array<u64>>, tl: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v12 = ltb(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v30 = rocq_array::set::<u64>(rep, i, i);
      let v37 = rocq_array::set::<u64>(tl, i, i);
      init(n, v23, v30, v37, ())
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
  let v16 = ltb(0u64, bud);
  match bdec(v16) {
    sumbool::left => {
      let r1 = nx(a, b, c, r);
      let r2 = nx(a, b, c, r1);
      let x = mod_(r1, n);
      let y = mod_(r2, n);
      match eqb(x, y) {
        true => {
          redraw(n, a, b, c, r2, sub(bud, 1u64), ())
        },
        false => {
          ((r2, x), y)
        },
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
  let v15 = ltb(0u64, cnt);
  match bdec(v15) {
    sumbool::left => {
      let v19 = &nxt;
      let v22 = rocq_array::get::<u64>(&v19, q);
      let v30 = sub(cnt, 1u64);
      let v37 = rocq_array::set::<u64>(rep, q, big);
      relabel(nxt, big, v22, v30, v37, ())
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
  let v7 = &sz;
  let v10 = rocq_array::get::<u64>(&v7, small);
  let v13 = Rc::clone(&nxt);
  let rep_ = relabel_1(v13, big, small, v10, rep);
  let v23 = &tl;
  let v26 = rocq_array::get::<u64>(&v23, big);
  let nxt_ = rocq_array::set::<u64>(nxt, v26, small);
  let v34 = &tl;
  let v37 = rocq_array::get::<u64>(&v34, small);
  let tl_ = rocq_array::set::<u64>(tl, big, v37);
  let v46 = &sz;
  let v49 = rocq_array::get::<u64>(&v46, big);
  let v50 = &sz;
  let v53 = rocq_array::get::<u64>(&v50, small);
  let sz_ = rocq_array::set::<u64>(sz, big, add(v49, v53));
  (((rep_, nxt_), tl_), sz_)
}

// Rocq: Chatter.chatter_implem.union
// Variant: uncurried
pub fn union(x: u64, y: u64, rep: Rc<Array<u64>>, nxt: Rc<Array<u64>>, tl: Rc<Array<u64>>, sz: Rc<Array<u64>>) -> (((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<u64>>) {
  let v6 = &rep;
  let px = rocq_array::get::<u64>(&v6, x);
  let v10 = &rep;
  let py = rocq_array::get::<u64>(&v10, y);
  match eqb(px, py) {
    true => {
      (((rep, nxt), tl), sz)
    },
    false => {
      let v42 = &sz;
      let v45 = rocq_array::get::<u64>(&v42, py);
      let v46 = &sz;
      let v49 = rocq_array::get::<u64>(&v46, px);
      match ltb(v45, v49) {
        true => {
          merge(px, py, rep, nxt, tl, sz)
        },
        false => {
          merge(py, px, rep, nxt, tl, sz)
        },
      }
    },
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
  let v20 = ltb(0u64, k);
  match bdec(v20) {
    sumbool::left => {
      let v32 = add(c, 1u64);
      let v45 = redraw_1(n, a, b, c, r, v32);
      match v45 {
        (v47, v49) => {
          match v47 {
            (v52, v54) => {
              let v69 = union(v54, v49, rep, nxt, tl, sz);
              match v69 {
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
  let v15 = ltb(i, n);
  match bdec(v15) {
    sumbool::left => {
      let v19 = &rep;
      let ro = rocq_array::get::<u64>(&v19, i);
      let v24 = &seen;
      let v27 = rocq_array::get::<u64>(&v24, ro);
      match eqb(v27, 0u64) {
        true => {
          let v36 = &sz;
          let s = rocq_array::get::<u64>(&v36, ro);
          let v47 = add(i, 1u64);
          let v56 = rocq_array::set::<u64>(seen, ro, 1u64);
          let v58 = &cnt;
          let v61 = rocq_array::get::<u64>(&v58, s);
          let v75 = rocq_array::set::<u64>(cnt, s, add(v61, 1u64));
          tally(n, v47, rep, sz, v56, v75, add(g, 1u64), ())
        },
        false => {
          tally(n, add(i, 1u64), rep, sz, seen, cnt, g, ())
        },
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
  let v12 = ltb(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v26 = 0u64;
      let v32 = sub(n, i);
      let v33 = &cnt;
      let v36 = rocq_array::get::<u64>(&v33, v32);
      let v42 = match ltb(v26, v36) {
        true => {
          add(d, 1u64)
        },
        false => {
          d
        },
      };
      countd(n, v23, cnt, v42, ())
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
  let v13 = ltb(i, n);
  match bdec(v13) {
    sumbool::left => {
      let s = sub(n, i);
      let v23 = &cnt;
      let v = rocq_array::get::<u64>(&v23, s);
      match ltb(0u64, v) {
        true => {
          let v43 = add(i, 1u64);
          let v51 = add(j, 1u64);
          let v64 = rocq_array::set::<(u64, u64)>(out, j, (s, v));
          fill(n, v43, v51, cnt, v64, ())
        },
        false => {
          fill(n, add(i, 1u64), j, cnt, out, ())
        },
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
  let v14 = rocq_array::make::<u64>(n, 0u64);
  let v21 = rocq_array::make::<u64>(n, 0u64);
  let v30 = init_1(n, 0u64, v14, v21);
  match v30 {
    (v32, v34) => {
      let v43 = rocq_array::make::<u64>(n, 0u64);
      let v50 = rocq_array::make::<u64>(n, 1u64);
      let v71 = sim_1(n, a, b, c, r, n, v32, v43, v34, v50);
      match &v71 {
        (sz, rep) => {
          let v80 = 0u64;
          let v87 = rocq_array::make::<u64>(n, 0u64);
          let v102 = rocq_array::make::<u64>(add(n, 1u64), 0u64);
          let v104 = 0u64;
          let v110 = Rc::clone(sz);
          let v111 = Rc::clone(rep);
          std::mem::drop(v71);
          let v119 = tally_1(n, v80, v110, v111, v87, v102, v104);
          match v119 {
            (v121, v123) => {
              let g = &v123;
              let v136 = Rc::clone(g);
              let d = countd_1(n, 0u64, v136, 0u64);
              let v159 = rocq_array::make::<(u64, u64)>(d, (0u64, 0u64));
              let v170 = fill_1(n, 0u64, 0u64, v123, v159);
              (v121, v170)
            },
          }
        },
      }
    },
  }
}

// Rocq: Chatter.chatter_implem.chatter_impl
pub fn chatter_impl_curried(n: u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, Rc<Array<(u64, u64)>>)>>>> {
  let v3 = {
    move |r: u64| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, Rc<Array<(u64, u64)>>)>>> {
      let n = &n;
      let v8 = Clone::clone(n);
      let v11 = {
        move |a: u64| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, Rc<Array<(u64, u64)>>)>> {
          let n = &v8;
          let r = &r;
          let v18 = Clone::clone(n);
          let v20 = Clone::clone(r);
          let v23 = {
            move |b: u64| -> Rc<dyn Fn(u64) -> (u64, Rc<Array<(u64, u64)>>)> {
              let n = &v18;
              let r = &v20;
              let a = &a;
              let v32 = Clone::clone(n);
              let v34 = Clone::clone(r);
              let v36 = Clone::clone(a);
              let v39 = {
                move |c: u64| -> (u64, Rc<Array<(u64, u64)>>) {
                  let v51 = Clone::clone(&v32);
                  let v53 = Clone::clone(&v34);
                  let v55 = Clone::clone(&v36);
                  let v57 = Clone::clone(&b);
                  chatter_impl(v51, v53, v55, v57, c)
                }
              };
              let v63: Rc<dyn Fn(u64) -> (u64, Rc<Array<(u64, u64)>>)> = Rc::new(v39);
              v63
            }
          };
          let v67: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, Rc<Array<(u64, u64)>>)>> = Rc::new(v23);
          v67
        }
      };
      let v71: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, Rc<Array<(u64, u64)>>)>>> = Rc::new(v11);
      v71
    }
  };
  let v75: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, Rc<Array<(u64, u64)>>)>>>> = Rc::new(v3);
  v75
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

pub fn run() -> Rc<dyn Fn(u64, u64, u64, u64, u64) -> (u64, Rc<Array<(u64, u64)>>)> {
  let v0: Rc<dyn Fn(u64, u64, u64, u64, u64) -> (u64, Rc<Array<(u64, u64)>>)> = __rocq_global_739.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_739: Rc<dyn Fn(u64, u64, u64, u64, u64) -> (u64, Rc<Array<(u64, u64)>>)> = chatter(); }
std::thread_local! { static __rocq_global_742: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, Rc<Array<(u64, u64)>>)>>>>> = chatter_curried(); }