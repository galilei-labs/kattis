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

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::PositiveTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::NaturalTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::IntegerTag>; };

pub type uint = u64;

// Rocq: Magicsequence.magicsequence_implem.mask
pub fn mask() -> u64 {
  65535u64
}

// Rocq: Magicsequence.magicsequence_implem.K
pub fn K() -> u64 {
  65536u64
}

// Rocq: Magicsequence.magicsequence_implem.magic
// Variant: uncurried
pub fn magic() -> Rc<dyn Fn(u64, u64, u64, u64, u64, u64) -> u64> {
  let v0: fn(u64, u64, u64, u64, u64, u64) -> u64 = magic_impl;
  let v1: Rc<dyn Fn(u64, u64, u64, u64, u64, u64) -> u64> = Rc::new(v0);
  v1
}

// Rocq: Magicsequence.magicsequence_implem.magic
pub fn magic_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>>>> = magic_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.land
// Variant: uncurried
pub fn land(v0: u64, v1: u64) -> u64 {
  rocq_int63::land(v0, v1)
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

// Rocq: Magicsequence.magicsequence_implem.bdec
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

// Rocq: Magicsequence.magicsequence_implem.gen_loop
// Variant: uncurried
pub fn gen_loop_1(a: u64, b: u64, c: u64, n: u64, i: u64, t: u64, m: u64, arr: Rc<Array<u64>>, lo: Rc<Array<u64>>, hi: Rc<Array<u64>>) -> (((Rc<Array<u64>>, u64), Rc<Array<u64>>), Rc<Array<u64>>) {
  gen_loop(a, b, c, n, i, t, m, arr, lo, hi, ())
}

// Rocq: Magicsequence.magicsequence_implem.gen_loop (local: gen_loop)
// Variant: uncurried, lifted
pub fn gen_loop(a: u64, b: u64, c: u64, n: u64, i: u64, t: u64, m: u64, arr: Rc<Array<u64>>, lo: Rc<Array<u64>>, hi: Rc<Array<u64>>, _H: ()) -> (((Rc<Array<u64>>, u64), Rc<Array<u64>>), Rc<Array<u64>>) {
  let v18 = ltb(i, n);
  match bdec(v18) {
    sumbool::left => {
      let dl = land(t, __rocq_global_60);
      let dh = land(lsr(t, 16u64), __rocq_global_60);
      let v44 = &lo;
      let v46 = dl;
      let kl = Clone::clone(&(v44)[v46]);
      let v48 = &hi;
      let v50 = dh;
      let kh = Clone::clone(&(v48)[v50]);
      let v59 = add(i, 1u64);
      let v77 = mod_(add(mul(t, b), a), c);
      let v84 = match ltb(m, t) {
        true => {
          t
        },
        false => {
          m
        },
      };
      let v96 = rocq_array::set::<u64>(arr, i, t);
      let v111 = rocq_array::set::<u64>(lo, dl, add(kl, 1u64));
      let v126 = rocq_array::set::<u64>(hi, dh, add(kh, 1u64));
      gen_loop(a, b, c, n, v59, v77, v84, v96, v111, v126, ())
    },
    sumbool::right => {
      (((arr, m), lo), hi)
    },
  }
}

// Rocq: Magicsequence.magicsequence_implem.prefix_loop
// Variant: uncurried
pub fn prefix_loop_1(e: u64, acc: u64, cnt: Rc<Array<u64>>) -> Rc<Array<u64>> {
  prefix_loop(e, acc, cnt, ())
}

// Rocq: Magicsequence.magicsequence_implem.prefix_loop (local: prefix_loop)
// Variant: uncurried, lifted
pub fn prefix_loop(e: u64, acc: u64, cnt: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(e, __rocq_global_223);
  match bdec(v12) {
    sumbool::left => {
      let v16 = &cnt;
      let v18 = e;
      let k = Clone::clone(&(v16)[v18]);
      let v27 = add(e, 1u64);
      let v33 = add(acc, k);
      let v40 = rocq_array::set::<u64>(cnt, e, acc);
      prefix_loop(v27, v33, v40, ())
    },
    sumbool::right => {
      cnt
    },
  }
}

// Rocq: Magicsequence.magicsequence_implem.place_loop
// Variant: uncurried
pub fn place_loop_1(s: u64, n: u64, src: Rc<Array<u64>>, i: u64, cnt: Rc<Array<u64>>, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  place_loop(s, n, src, i, cnt, dst, ())
}

// Rocq: Magicsequence.magicsequence_implem.place_loop (local: place_loop)
// Variant: uncurried, lifted
pub fn place_loop(s: u64, n: u64, src: Rc<Array<u64>>, i: u64, cnt: Rc<Array<u64>>, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v14 = ltb(i, n);
  match bdec(v14) {
    sumbool::left => {
      let v18 = &src;
      let v20 = i;
      let e = Clone::clone(&(v18)[v20]);
      let d = land(lsr(e, s), __rocq_global_60);
      let v35 = &cnt;
      let v37 = d;
      let p = Clone::clone(&(v35)[v37]);
      let v46 = add(i, 1u64);
      let v61 = rocq_array::set::<u64>(cnt, d, add(p, 1u64));
      let v68 = rocq_array::set::<u64>(dst, p, e);
      place_loop(s, n, src, v46, v61, v68, ())
    },
    sumbool::right => {
      std::mem::drop(src);
      std::mem::drop(cnt);
      dst
    },
  }
}

// Rocq: Magicsequence.magicsequence_implem.pass
// Variant: uncurried
pub fn pass(s: u64, n: u64, src: Rc<Array<u64>>, cnt: Rc<Array<u64>>, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let cnt_1 = prefix_loop_1(0u64, 0u64, cnt);
  place_loop_1(s, n, src, 0u64, cnt_1, dst)
}

// Rocq: Magicsequence.magicsequence_implem.hash_loop
// Variant: uncurried
pub fn hash_loop_1(x: u64, y: u64, n: u64, i: u64, v: u64, r: Rc<Array<u64>>) -> u64 {
  hash_loop(x, y, n, i, v, r, ())
}

// Rocq: Magicsequence.magicsequence_implem.hash_loop (local: hash_loop)
// Variant: uncurried, lifted
pub fn hash_loop(x: u64, y: u64, n: u64, i: u64, v: u64, r: Rc<Array<u64>>, _H: ()) -> u64 {
  let v14 = ltb(i, n);
  match bdec(v14) {
    sumbool::left => {
      let v25 = add(i, 1u64);
      let v33 = mul(v, x);
      let v34 = &r;
      let v36 = i;
      let v37 = Clone::clone(&(v34)[v36]);
      let v47 = mod_(add(v33, v37), y);
      hash_loop(x, y, n, v25, v47, r, ())
    },
    sumbool::right => {
      std::mem::drop(r);
      v
    },
  }
}

// Rocq: Magicsequence.magicsequence_implem.magic_impl
// Variant: uncurried
pub fn magic_impl(n: u64, a: u64, b: u64, c: u64, x: u64, y: u64) -> u64 {
  let v17 = rocq_array::make::<u64>(n, 0u64);
  let v25 = rocq_array::make::<u64>(__rocq_global_223, 0u64);
  let v33 = rocq_array::make::<u64>(__rocq_global_223, 0u64);
  let v54 = gen_loop_1(a, b, c, n, 0u64, a, 0u64, v17, v25, v33);
  match v54 {
    (v56, v58) => {
      match v56 {
        (v61, v63) => {
          match v61 {
            (v66, v68) => {
              let m = &v66;
              let v80 = rocq_array::make::<u64>(n, 0u64);
              let v86 = Rc::clone(m);
              let r1 = pass(0u64, n, v86, v63, v80);
              let v93 = __rocq_global_223;
              let r = match ltb(v68, v93) {
                true => {
                  std::mem::drop(v66);
                  std::mem::drop(v58);
                  r1
                },
                false => {
                  pass(16u64, n, r1, v58, v66)
                },
              };
              hash_loop_1(x, y, n, 0u64, 0u64, r)
            },
          }
        },
      }
    },
  }
}

// Rocq: Magicsequence.magicsequence_implem.magic_impl
pub fn magic_impl_curried(n: u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>>>> {
  let v3 = {
    move |a: u64| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>>> {
      let n = &n;
      let v8 = Clone::clone(n);
      let v11 = {
        move |b: u64| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>> {
          let n = &v8;
          let a = &a;
          let v18 = Clone::clone(n);
          let v20 = Clone::clone(a);
          let v23 = {
            move |c: u64| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>> {
              let n = &v18;
              let a = &v20;
              let b = &b;
              let v32 = Clone::clone(n);
              let v34 = Clone::clone(a);
              let v36 = Clone::clone(b);
              let v39 = {
                move |x: u64| -> Rc<dyn Fn(u64) -> u64> {
                  let n = &v32;
                  let a = &v34;
                  let b = &v36;
                  let c = &c;
                  let v50 = Clone::clone(n);
                  let v52 = Clone::clone(a);
                  let v54 = Clone::clone(b);
                  let v56 = Clone::clone(c);
                  let v59 = {
                    move |y: u64| -> u64 {
                      let v73 = Clone::clone(&v50);
                      let v75 = Clone::clone(&v52);
                      let v77 = Clone::clone(&v54);
                      let v79 = Clone::clone(&v56);
                      let v81 = Clone::clone(&x);
                      magic_impl(v73, v75, v77, v79, v81, y)
                    }
                  };
                  let v87: Rc<dyn Fn(u64) -> u64> = Rc::new(v59);
                  v87
                }
              };
              let v91: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>> = Rc::new(v39);
              v91
            }
          };
          let v95: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>> = Rc::new(v23);
          v95
        }
      };
      let v99: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>>> = Rc::new(v11);
      v99
    }
  };
  let v103: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>>>> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(u64, u64, u64, u64, u64, u64) -> u64> {
  let v0: Rc<dyn Fn(u64, u64, u64, u64, u64, u64) -> u64> = __rocq_global_483.with(Clone::clone);
  v0
}
const __rocq_global_60: u64 = 65535u64;
const __rocq_global_223: u64 = 65536u64;
std::thread_local! { static __rocq_global_483: Rc<dyn Fn(u64, u64, u64, u64, u64, u64) -> u64> = magic(); }
std::thread_local! { static __rocq_global_486: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>>>>> = magic_curried(); }