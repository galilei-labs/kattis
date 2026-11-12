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

pub enum tree {
  Leaf,
  Node(Rc<tree>, u64, Rc<tree>, u64, u64),
}

impl Clone for tree {
  fn clone(&self) -> Self {
    match self {
      tree::Leaf => tree::Leaf,
      tree::Node(__field0, __field1, __field2, __field3, __field4) => tree::Node(Clone::clone(__field0), Clone::clone(__field1), Clone::clone(__field2), Clone::clone(__field3), Clone::clone(__field4)),
    }
  }
}

pub type uint = u64;

// Rocq: Gcpc.gcpc_implem.K0
pub fn K0() -> u64 {
  2305825417027649536u64
}

// Rocq: Gcpc.gcpc_implem.KD
pub fn KD() -> u64 {
  17592186044416u64
}

// Rocq: Gcpc.gcpc_implem.KE
pub fn KE() -> u64 {
  131072u64
}

// Rocq: Gcpc.gcpc_implem.gcpc
// Variant: uncurried
pub fn gcpc() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>> = gcpc_impl;
  let v1: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v0);
  v1
}

// Rocq: Gcpc.gcpc_implem.gcpc
pub fn gcpc_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> = gcpc_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Gcpc.gcpc_implem.bdec
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

// Rocq: Gcpc.gcpc_implem.size
// Variant: borrowed
pub fn size(t: &Rc<tree>) -> u64 {
  let v1 = t;
  match &**v1 {
    tree::Leaf => {
      0u64
    },
    tree::Node(_i0, _s, _t1, i, _t0) => {
      Clone::clone(i)
    },
  }
}

// Rocq: Gcpc.gcpc_implem.height
pub fn height_owned(t: Rc<tree>) -> u64 {
  let (v1, v2) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v2);
  match v1 {
    tree::Leaf => {
      0u64
    },
    tree::Node(v15, _v17, v19, _v21, v23) => {
      std::mem::drop(v15);
      std::mem::drop(v19);
      v23
    },
  }
}

// Rocq: Gcpc.gcpc_implem.height
// Variant: borrowed
pub fn height(t: &Rc<tree>) -> u64 {
  let v1 = t;
  match &**v1 {
    tree::Leaf => {
      0u64
    },
    tree::Node(_h, _i0, _t1, _i, t0) => {
      Clone::clone(t0)
    },
  }
}

// Rocq: Gcpc.gcpc_implem.mk
// Variant: uncurried
pub fn mk(l: Rc<tree>, k: u64, r: Rc<tree>) -> Rc<tree> {
  let v17 = add(size(&l), size(&r));
  let v24 = add(v17, 1u64);
  let v29 = height(&l);
  let v33 = height(&r);
  let v39 = match ltb(v29, v33) {
    true => {
      let v44 = Rc::clone(&r);
      add(height_owned(v44), 1u64)
    },
    false => {
      let v59 = Rc::clone(&l);
      add(height_owned(v59), 1u64)
    },
  };
  Rc::new(tree::Node(l, k, r, v24, v39))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Gcpc.gcpc_implem.bal
// Variant: uncurried
pub fn bal(l: Rc<tree>, k: u64, r: Rc<tree>) -> Rc<tree> {
  let hl = height(&l);
  let hr = height(&r);
  let v20 = add(hr, 2u64);
  match ltb(v20, hl) {
    true => {
      match &*l {
        tree::Leaf => {
          mk(l, k, r)
        },
        tree::Node(i0, i, lr, _lk, _ll) => {
          let v51 = height(lr);
          let v54 = height(i0);
          match leb(v51, v54) {
            true => {
              let v69 = mk(Rc::clone(lr), k, r);
              let v71 = Rc::clone(i0);
              let v72 = Clone::clone(i);
              std::mem::drop(l);
              mk(v71, v72, v69)
            },
            false => {
              match &**lr {
                tree::Leaf => {
                  mk(l, k, r)
                },
                tree::Node(i0_1, i_1, lrr, _lrk, _lrl) => {
                  let v108 = mk(Rc::clone(i0), Clone::clone(i), Rc::clone(i0_1));
                  let v116 = mk(Rc::clone(lrr), k, r);
                  let v119 = Clone::clone(i_1);
                  std::mem::drop(l);
                  mk(v108, v119, v116)
                },
              }
            },
          }
        },
      }
    },
    false => {
      let v144 = add(hl, 2u64);
      match ltb(v144, hr) {
        true => {
          match &*r {
            tree::Leaf => {
              mk(l, k, r)
            },
            tree::Node(i0, i, rr, _rk, _rl) => {
              let v175 = height(i0);
              let v178 = height(rr);
              match leb(v175, v178) {
                true => {
                  let v194 = mk(l, k, Rc::clone(i0));
                  let v197 = Clone::clone(i);
                  let v198 = Rc::clone(rr);
                  std::mem::drop(r);
                  mk(v194, v197, v198)
                },
                false => {
                  match &**i0 {
                    tree::Leaf => {
                      mk(l, k, r)
                    },
                    tree::Node(i0_1, i_1, rlr, _rlk, _rll) => {
                      let v232 = mk(l, k, Rc::clone(i0_1));
                      let v240 = mk(Rc::clone(rlr), Clone::clone(i), Rc::clone(rr));
                      let v243 = Clone::clone(i_1);
                      std::mem::drop(r);
                      mk(v232, v243, v240)
                    },
                  }
                },
              }
            },
          }
        },
        false => {
          mk(l, k, r)
        },
      }
    },
  }
}

// Rocq: Gcpc.gcpc_implem.insert
// Variant: uncurried
pub fn insert_1(x: u64, t: Rc<tree>) -> Rc<tree> {
  insert(x, t)
}

// Rocq: Gcpc.gcpc_implem.insert (local: insert)
// Variant: uncurried, lifted
pub fn insert(x: u64, t: Rc<tree>) -> Rc<tree> {
  match &*t {
    tree::Leaf => {
      std::mem::drop(t);
      mk(Rc::new(tree::Leaf), x, Rc::new(tree::Leaf))
    },
    tree::Node(i0, i, r, _k, _l) => {
      let v34 = Clone::clone(i);
      match ltb(x, v34) {
        true => {
          let v44 = insert(x, Rc::clone(i0));
          let v47 = Clone::clone(i);
          let v48 = Rc::clone(r);
          std::mem::drop(t);
          bal(v44, v47, v48)
        },
        false => {
          let v55 = Clone::clone(i);
          match ltb(v55, x) {
            true => {
              let v66 = insert(x, Rc::clone(r));
              let v68 = Rc::clone(i0);
              let v69 = Clone::clone(i);
              std::mem::drop(t);
              bal(v68, v69, v66)
            },
            false => {
              t
            },
          }
        },
      }
    },
  }
}

// Rocq: Gcpc.gcpc_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(n1: u64, k: u64, keys: Rc<Array<u64>>, T: Rc<tree>) -> (Rc<Array<u64>>, Rc<tree>) {
  init_loop(n1, k, keys, T, ())
}

// Rocq: Gcpc.gcpc_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(n1: u64, k: u64, keys: Rc<Array<u64>>, T: Rc<tree>, _H: ()) -> (Rc<Array<u64>>, Rc<tree>) {
  let v12 = ltb(k, n1);
  match bdec(v12) {
    sumbool::left => {
      let key = add(__rocq_global_36, k);
      let v30 = add(k, 1u64);
      let v37 = rocq_array::set::<u64>(keys, k, key);
      init_loop(n1, v30, v37, insert_1(key, T), ())
    },
    sumbool::right => {
      (keys, T)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Gcpc.gcpc_implem.remove_min
// Variant: uncurried
pub fn remove_min_1(l: Rc<tree>, k: u64, r: Rc<tree>) -> (u64, Rc<tree>) {
  remove_min(l, k, r)
}

// Rocq: Gcpc.gcpc_implem.remove_min (local: remove_min)
// Variant: uncurried, lifted
pub fn remove_min(l: Rc<tree>, k: u64, r: Rc<tree>) -> (u64, Rc<tree>) {
  match &*l {
    tree::Leaf => {
      std::mem::drop(l);
      (k, r)
    },
    tree::Node(i0, i, lr, _lk, _ll) => {
      let v25 = Rc::clone(i0);
      let v27 = Clone::clone(i);
      let v28 = Rc::clone(lr);
      std::mem::drop(l);
      let v30 = remove_min(v25, v27, v28);
      match v30 {
        (v32, v34) => {
          (v32, bal(v34, k, r))
        },
      }
    },
  }
}

// Rocq: Gcpc.gcpc_implem.merge
// Variant: uncurried
pub fn merge(l: Rc<tree>, r: Rc<tree>) -> Rc<tree> {
  match &*l {
    tree::Leaf => {
      std::mem::drop(l);
      r
    },
    tree::Node(_i1, _i0, _t0, _i, _t) => {
      match &*r {
        tree::Leaf => {
          std::mem::drop(r);
          l
        },
        tree::Node(i3, i2, rr, _rk, _rl) => {
          let v32 = Rc::clone(i3);
          let v34 = Clone::clone(i2);
          let v35 = Rc::clone(rr);
          std::mem::drop(r);
          let v37 = remove_min_1(v32, v34, v35);
          match v37 {
            (v39, v41) => {
              bal(l, v39, v41)
            },
          }
        },
      }
    },
  }
}

// Rocq: Gcpc.gcpc_implem.delete
// Variant: uncurried
pub fn delete_1(x: u64, t: Rc<tree>) -> Rc<tree> {
  delete(x, t)
}

// Rocq: Gcpc.gcpc_implem.delete (local: delete)
// Variant: uncurried, lifted
pub fn delete(x: u64, t: Rc<tree>) -> Rc<tree> {
  let (v2, v3) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  match v2 {
    tree::Leaf => {
      __rocq_reuse::rebuild(v3, tree::Leaf)
    },
    tree::Node(v17, v19, v21, _v23, _v25) => {
      std::mem::drop(v3);
      match ltb(x, v19) {
        true => {
          bal(delete(x, v17), v19, v21)
        },
        false => {
          match ltb(v19, x) {
            true => {
              bal(v17, v19, delete(x, v21))
            },
            false => {
              merge(v17, v21)
            },
          }
        },
      }
    },
  }
}

// Rocq: Gcpc.gcpc_implem.count_lt
// Variant: borrowed, uncurried
pub fn count_lt_1(q: u64, t: &Rc<tree>) -> u64 {
  let q_1 = q;
  count_lt(q_1, t)
}

// Rocq: Gcpc.gcpc_implem.count_lt (local: count_lt)
// Variant: borrowed, uncurried, lifted
pub fn count_lt(q: u64, t: &Rc<tree>) -> u64 {
  let q_1 = q;
  let v3 = t;
  match &**v3 {
    tree::Leaf => {
      0u64
    },
    tree::Node(i0, i, r, _k, _l) => {
      let v21 = Clone::clone(i);
      match ltb(v21, q_1) {
        true => {
          let v37 = add(size(i0), 1u64);
          let v42 = count_lt(q_1, r);
          add(v37, v42)
        },
        false => {
          count_lt(q_1, i0)
        },
      }
    },
  }
}

// Rocq: Gcpc.gcpc_implem.ev_loop
// Variant: uncurried
pub fn ev_loop_1(xt: Rc<Array<u64>>, xp: Rc<Array<u64>>, m: u64, j: u64, keys: Rc<Array<u64>>, T: Rc<tree>, out: Rc<Array<u64>>) -> Rc<Array<u64>> {
  ev_loop(xt, xp, m, j, keys, T, out, ())
}

// Rocq: Gcpc.gcpc_implem.ev_loop (local: ev_loop)
// Variant: uncurried, lifted
pub fn ev_loop(xt: Rc<Array<u64>>, xp: Rc<Array<u64>>, m: u64, j: u64, keys: Rc<Array<u64>>, T: Rc<tree>, out: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v15 = ltb(j, m);
  match bdec(v15) {
    sumbool::left => {
      let v19 = &xt;
      let a = rocq_array::get::<u64>(&v19, j);
      let v23 = &keys;
      let old = rocq_array::get::<u64>(&v23, a);
      let v34 = sub(old, __rocq_global_317);
      let v36 = &xp;
      let v39 = rocq_array::get::<u64>(&v36, j);
      let new = add(v34, mul(v39, __rocq_global_334));
      let keys_ = rocq_array::set::<u64>(keys, a, new);
      let T_ = insert_1(new, delete_1(old, T));
      let v73 = 1u64;
      let v74 = &keys_;
      let v77 = rocq_array::get::<u64>(&v74, v73);
      let v90 = count_lt_1(sub(v77, 1u64), &T_);
      let ans = add(v90, 1u64);
      let v105 = add(j, 1u64);
      let v112 = rocq_array::set::<u64>(out, j, ans);
      ev_loop(xt, xp, m, v105, keys_, T_, v112, ())
    },
    sumbool::right => {
      std::mem::drop(xt);
      std::mem::drop(xp);
      std::mem::drop(keys);
      std::mem::drop(T);
      out
    },
  }
}

// Rocq: Gcpc.gcpc_implem.gcpc_impl
// Variant: uncurried
pub fn gcpc_impl(n: u64, xt: Rc<Array<u64>>, xp: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v3 = &xt;
  let m = rocq_array::length::<u64>(&v3);
  let n1 = add(n, 1u64);
  let v22 = rocq_array::make::<u64>(n1, 0u64);
  let v34 = init_loop_1(n1, 1u64, v22, Rc::new(tree::Leaf));
  match v34 {
    (v36, v38) => {
      let v49 = rocq_array::make::<u64>(m, 0u64);
      ev_loop_1(xt, xp, m, 0u64, v36, v38, v49)
    },
  }
}

// Rocq: Gcpc.gcpc_implem.gcpc_impl
pub fn gcpc_impl_curried(n: u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> {
  let v3 = {
    move |xt: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> {
      let n = &n;
      let v8 = Clone::clone(n);
      let v11 = {
        move |xp: Rc<Array<u64>>| -> Rc<Array<u64>> {
          let v19 = Clone::clone(&v8);
          let v21 = Rc::clone(&xt);
          gcpc_impl(v19, v21, xp)
        }
      };
      let v27: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v11);
      v27
    }
  };
  let v31: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = __rocq_global_618.with(Clone::clone);
  v0
}
const __rocq_global_36: u64 = 2305825417027649536u64;
const __rocq_global_317: u64 = 17592186044416u64;
const __rocq_global_334: u64 = 131072u64;
std::thread_local! { static __rocq_global_618: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = gcpc(); }
std::thread_local! { static __rocq_global_621: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>> = gcpc_curried(); }