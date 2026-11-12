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

// Rocq: Unionfind.unionfind_implem.run_ops
// Variant: uncurried
pub fn run_ops() -> Rc<dyn Fn(u64, Rc<Array<bool>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<bool>>> {
  let v0: fn(u64, Rc<Array<bool>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<bool>> = run_ops_impl;
  let v1: Rc<dyn Fn(u64, Rc<Array<bool>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<bool>>> = Rc::new(v0);
  v1
}

// Rocq: Unionfind.unionfind_implem.run_ops
pub fn run_ops_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<bool>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<bool>>>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<bool>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<bool>>>>> = run_ops_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<bool>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<bool>>>>>> = Rc::new(v0);
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

// Rocq: Unionfind.unionfind_implem.bdec
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

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let v3 = Clone::clone((&(&p).1));
  std::mem::drop(p);
  v3
}

// Rocq: Unionfind.unionfind_implem.find
// Variant: uncurried
pub fn find_1(par: Rc<Array<u64>>, x: u64) -> (u64, Rc<Array<u64>>) {
  find(par, x, ())
}

// Rocq: Unionfind.unionfind_implem.find (local: find)
// Variant: uncurried, lifted
pub fn find(par: Rc<Array<u64>>, x: u64, _H: ()) -> (u64, Rc<Array<u64>>) {
  let v3 = &par;
  let p = rocq_array::get::<u64>(&v3, x);
  let v14 = eqb(p, x);
  match bdec(v14) {
    sumbool::left => {
      (x, par)
    },
    sumbool::right => {
      let rp = find(par, p, ());
      let v38 = Clone::clone(&rp);
      let v40 = fst::<u64, Rc<Array<u64>>>(v38);
      let v43 = Clone::clone(&rp);
      let v45 = snd::<u64, Rc<Array<u64>>>(v43);
      let v56 = rocq_array::set::<u64>(v45, x, fst::<u64, Rc<Array<u64>>>(rp));
      (v40, v56)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Unionfind.unionfind_implem.link
// Variant: uncurried
pub fn link(par: Rc<Array<u64>>, rk: Rc<Array<u64>>, ra: u64, rb: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  match eqb(ra, rb) {
    true => {
      (par, rk)
    },
    false => {
      let v19 = &rk;
      let ka = rocq_array::get::<u64>(&v19, ra);
      let v23 = &rk;
      let kb = rocq_array::get::<u64>(&v23, rb);
      match ltb(ka, kb) {
        true => {
          let v41 = rocq_array::set::<u64>(par, ra, rb);
          (v41, rk)
        },
        false => {
          match ltb(kb, ka) {
            true => {
              let v63 = rocq_array::set::<u64>(par, rb, ra);
              (v63, rk)
            },
            false => {
              let v77 = rocq_array::set::<u64>(par, ra, rb);
              let v92 = rocq_array::set::<u64>(rk, rb, add(kb, 1u64));
              (v77, v92)
            },
          }
        },
      }
    },
  }
}

// Rocq: Unionfind.unionfind_implem.scan
// Variant: uncurried
pub fn scan_1(xu: Rc<Array<bool>>, xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, q: u64, k: u64, par: Rc<Array<u64>>, rk: Rc<Array<u64>>, out: Rc<Array<bool>>) -> Rc<Array<bool>> {
  scan(xu, xa, xb, q, k, par, rk, out, (), ())
}

// Rocq: Unionfind.unionfind_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(xu: Rc<Array<bool>>, xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, q: u64, k: u64, par: Rc<Array<u64>>, rk: Rc<Array<u64>>, out: Rc<Array<bool>>, _W: (), _H: ()) -> Rc<Array<bool>> {
  let v17 = ltb(k, q);
  match bdec(v17) {
    sumbool::left => {
      let v21 = &xa;
      let a = rocq_array::get::<u64>(&v21, k);
      let v25 = &xb;
      let b = rocq_array::get::<u64>(&v25, k);
      let fa = find_1(par, a);
      let v38 = Clone::clone(&fa);
      let v41 = snd::<u64, Rc<Array<u64>>>(v38);
      let fb = find_1(v41, b);
      let v46 = &xu;
      let v49 = rocq_array::get::<bool>(&v46, k);
      match v49 {
        true => {
          let v54 = Clone::clone(&fb);
          let v56 = snd::<u64, Rc<Array<u64>>>(v54);
          let l = link(v56, rk, fst::<u64, Rc<Array<u64>>>(fa), fst::<u64, Rc<Array<u64>>>(fb));
          let v81 = add(k, 1u64);
          let v84 = Clone::clone(&l);
          let v86 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(v84);
          let v90 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(l);
          scan(xu, xa, xb, q, v81, v86, v90, out, (), ())
        },
        false => {
          let v126 = add(k, 1u64);
          let v129 = Clone::clone(&fb);
          let v131 = snd::<u64, Rc<Array<u64>>>(v129);
          let v152 = rocq_array::set::<bool>(out, k, eqb(fst::<u64, Rc<Array<u64>>>(fa), fst::<u64, Rc<Array<u64>>>(fb)));
          scan(xu, xa, xb, q, v126, v131, rk, v152, (), ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(xu);
      std::mem::drop(xa);
      std::mem::drop(xb);
      std::mem::drop(par);
      std::mem::drop(rk);
      out
    },
  }
}

// Rocq: Unionfind.unionfind_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(n: u64, i: u64, p: Rc<Array<u64>>) -> Rc<Array<u64>> {
  init_loop(n, i, p, ())
}

// Rocq: Unionfind.unionfind_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(n: u64, i: u64, p: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v11 = ltb(i, n);
  match bdec(v11) {
    sumbool::left => {
      let v22 = add(i, 1u64);
      let v29 = rocq_array::set::<u64>(p, i, i);
      init_loop(n, v22, v29, ())
    },
    sumbool::right => {
      p
    },
  }
}

// Rocq: Unionfind.unionfind_implem.init_par
pub fn init_par(n: u64) -> Rc<Array<u64>> {
  let v10 = rocq_array::make::<u64>(n, 0u64);
  init_loop_1(n, 0u64, v10)
}

// Rocq: Unionfind.unionfind_implem.run_ops_impl
// Variant: uncurried
pub fn run_ops_impl(xn: u64, xu: Rc<Array<bool>>, xa: Rc<Array<u64>>, xb: Rc<Array<u64>>) -> Rc<Array<bool>> {
  let v4 = &xu;
  let q = rocq_array::length::<bool>(&v4);
  let v12 = init_par(xn);
  let v19 = rocq_array::make::<u64>(xn, 0u64);
  let v26 = rocq_array::make::<bool>(q, false);
  scan_1(xu, xa, xb, q, 0u64, v12, v19, v26)
}

// Rocq: Unionfind.unionfind_implem.run_ops_impl
pub fn run_ops_impl_curried(xn: u64) -> Rc<dyn Fn(Rc<Array<bool>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<bool>>>>> {
  let v3 = {
    move |xu: Rc<Array<bool>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<bool>>>> {
      let xn = &xn;
      let v8 = Clone::clone(xn);
      let v11 = {
        move |xa: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<bool>>> {
          let xn = &v8;
          let xu = &xu;
          let v18 = Clone::clone(xn);
          let v20 = Rc::clone(xu);
          let v23 = {
            move |xb: Rc<Array<u64>>| -> Rc<Array<bool>> {
              let v33 = Clone::clone(&v18);
              let v35 = Rc::clone(&v20);
              let v37 = Rc::clone(&xa);
              run_ops_impl(v33, v35, v37, xb)
            }
          };
          let v43: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<bool>>> = Rc::new(v23);
          v43
        }
      };
      let v47: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<bool>>>> = Rc::new(v11);
      v47
    }
  };
  let v51: Rc<dyn Fn(Rc<Array<bool>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<bool>>>>> = Rc::new(v3);
  v51
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<bool>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<bool>>> {
  let v0: Rc<dyn Fn(u64, Rc<Array<bool>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<bool>>> = __rocq_global_321.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_321: Rc<dyn Fn(u64, Rc<Array<bool>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<bool>>> = run_ops(); }
std::thread_local! { static __rocq_global_324: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<bool>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<bool>>>>>> = run_ops_curried(); }