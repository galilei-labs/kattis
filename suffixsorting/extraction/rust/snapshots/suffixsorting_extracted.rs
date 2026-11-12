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

pub type char63 = u64;

pub type uint = u64;

// Rocq: Suffixsorting.suffixsorting_implem.suffix_array
pub fn suffix_array() -> Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<Array<u64>>> {
  let v0: fn(Rc<rocq_string::RocqString>) -> Rc<Array<u64>> = suffix_array_impl;
  let v1: Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<Array<u64>>> = Rc::new(v0);
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

// Rocq: Suffixsorting.suffixsorting_implem.bdec
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

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let v5 = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  v5
}

// Rocq: Suffixsorting.suffixsorting_implem.init_rank
// Variant: uncurried
pub fn init_rank_1(x: Rc<rocq_string::RocqString>, n: u64, i: u64, r: Rc<Array<u64>>) -> Rc<Array<u64>> {
  init_rank(x, n, i, r, ())
}

// Rocq: Suffixsorting.suffixsorting_implem.init_rank (local: init_rank)
// Variant: uncurried, lifted
pub fn init_rank(x: Rc<rocq_string::RocqString>, n: u64, i: u64, r: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v28 = Rc::clone(&x);
      let v31 = get(v28, i);
      let v45 = rocq_array::set::<u64>(r, i, add(v31, 1u64));
      init_rank(x, n, v23, v45, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      r
    },
  }
}

// Rocq: Suffixsorting.suffixsorting_implem.init_id
// Variant: uncurried
pub fn init_id_1(n: u64, i: u64, sa: Rc<Array<u64>>) -> Rc<Array<u64>> {
  init_id(n, i, sa, ())
}

// Rocq: Suffixsorting.suffixsorting_implem.init_id (local: init_id)
// Variant: uncurried, lifted
pub fn init_id(n: u64, i: u64, sa: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v11 = ltb(i, n);
  match bdec(v11) {
    sumbool::left => {
      let v22 = add(i, 1u64);
      let v29 = rocq_array::set::<u64>(sa, i, i);
      init_id(n, v22, v29, ())
    },
    sumbool::right => {
      sa
    },
  }
}

// Rocq: Suffixsorting.suffixsorting_implem.cbound
pub fn cbound(n: u64) -> u64 {
  match ltb(n, 256u64) {
    true => {
      257u64
    },
    false => {
      add(n, 1u64)
    },
  }
}

// Rocq: Suffixsorting.suffixsorting_implem.count_loop
// Variant: uncurried
pub fn count_loop_1(r: Rc<Array<u64>>, n: u64, k: u64, src: Rc<Array<u64>>, i: u64, cnt: Rc<Array<u64>>) -> Rc<Array<u64>> {
  count_loop(r, n, k, src, i, cnt, ())
}

// Rocq: Suffixsorting.suffixsorting_implem.count_loop (local: count_loop)
// Variant: uncurried, lifted
pub fn count_loop(r: Rc<Array<u64>>, n: u64, k: u64, src: Rc<Array<u64>>, i: u64, cnt: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v14 = ltb(i, n);
  match bdec(v14) {
    sumbool::left => {
      let v18 = &src;
      let v20 = i;
      let x = Clone::clone(&(v18)[v20]);
      let v29 = add(x, k);
      let v = match ltb(v29, n) {
        true => {
          let v40 = add(x, k);
          let v41 = &r;
          let v43 = v40;
          Clone::clone(&(v41)[v43])
        },
        false => {
          0u64
        },
      };
      let v59 = add(i, 1u64);
      let v61 = &cnt;
      let v63 = v;
      let v64 = Clone::clone(&(v61)[v63]);
      let v78 = rocq_array::set::<u64>(cnt, v, add(v64, 1u64));
      count_loop(r, n, k, src, v59, v78, ())
    },
    sumbool::right => {
      std::mem::drop(r);
      std::mem::drop(src);
      cnt
    },
  }
}

// Rocq: Suffixsorting.suffixsorting_implem.prefix_loop
// Variant: uncurried
pub fn prefix_loop_1(B: u64, v: u64, acc: u64, cnt: Rc<Array<u64>>) -> Rc<Array<u64>> {
  prefix_loop(B, v, acc, cnt, ())
}

// Rocq: Suffixsorting.suffixsorting_implem.prefix_loop (local: prefix_loop)
// Variant: uncurried, lifted
pub fn prefix_loop(B: u64, v: u64, acc: u64, cnt: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(v, B);
  match bdec(v12) {
    sumbool::left => {
      let v16 = &cnt;
      let v18 = v;
      let c = Clone::clone(&(v16)[v18]);
      let v27 = add(v, 1u64);
      let v33 = add(acc, c);
      let v40 = rocq_array::set::<u64>(cnt, v, acc);
      prefix_loop(B, v27, v33, v40, ())
    },
    sumbool::right => {
      cnt
    },
  }
}

// Rocq: Suffixsorting.suffixsorting_implem.place_loop
// Variant: uncurried
pub fn place_loop_1(r: Rc<Array<u64>>, n: u64, k: u64, src: Rc<Array<u64>>, i: u64, cnt: Rc<Array<u64>>, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  place_loop(r, n, k, src, i, cnt, dst, ())
}

// Rocq: Suffixsorting.suffixsorting_implem.place_loop (local: place_loop)
// Variant: uncurried, lifted
pub fn place_loop(r: Rc<Array<u64>>, n: u64, k: u64, src: Rc<Array<u64>>, i: u64, cnt: Rc<Array<u64>>, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v15 = ltb(i, n);
  match bdec(v15) {
    sumbool::left => {
      let v19 = &src;
      let v21 = i;
      let x = Clone::clone(&(v19)[v21]);
      let v30 = add(x, k);
      let v = match ltb(v30, n) {
        true => {
          let v41 = add(x, k);
          let v42 = &r;
          let v44 = v41;
          Clone::clone(&(v42)[v44])
        },
        false => {
          0u64
        },
      };
      let v53 = &cnt;
      let v55 = v;
      let p = Clone::clone(&(v53)[v55]);
      let v64 = add(i, 1u64);
      let v79 = rocq_array::set::<u64>(cnt, v, add(p, 1u64));
      let v86 = rocq_array::set::<u64>(dst, p, x);
      place_loop(r, n, k, src, v64, v79, v86, ())
    },
    sumbool::right => {
      std::mem::drop(r);
      std::mem::drop(src);
      std::mem::drop(cnt);
      dst
    },
  }
}

// Rocq: Suffixsorting.suffixsorting_implem.csort
// Variant: uncurried
pub fn csort(r: Rc<Array<u64>>, n: u64, k: u64, src: Rc<Array<u64>>, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let B = cbound(n);
  let v18 = rocq_array::make::<u64>(B, 0u64);
  let v21 = Rc::clone(&r);
  let v28 = Rc::clone(&src);
  let c0 = count_loop_1(v21, n, k, v28, 0u64, v18);
  let c1 = prefix_loop_1(B, 0u64, 0u64, c0);
  place_loop_1(r, n, k, src, 0u64, c1, dst)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Suffixsorting.suffixsorting_implem.skey
// Variant: uncurried
pub fn skey(r: Rc<Array<u64>>, n: u64, k: u64, x: u64) -> u64 {
  let v11 = add(x, k);
  match ltb(v11, n) {
    true => {
      let v22 = add(x, k);
      let v23 = &r;
      let v25 = v22;
      let v26 = Clone::clone(&(v23)[v25]);
      std::mem::drop(r);
      v26
    },
    false => {
      std::mem::drop(r);
      0u64
    },
  }
}

// Rocq: Suffixsorting.suffixsorting_implem.rank_loop
// Variant: uncurried
pub fn rank_loop_1(r: Rc<Array<u64>>, n: u64, k: u64, sa: Rc<Array<u64>>, t: u64, cur: u64, nr: Rc<Array<u64>>) -> (Rc<Array<u64>>, u64) {
  rank_loop(r, n, k, sa, t, cur, nr, ())
}

// Rocq: Suffixsorting.suffixsorting_implem.rank_loop (local: rank_loop)
// Variant: uncurried, lifted
pub fn rank_loop(r: Rc<Array<u64>>, n: u64, k: u64, sa: Rc<Array<u64>>, t: u64, cur: u64, nr: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, u64) {
  let v15 = ltb(t, n);
  match bdec(v15) {
    sumbool::left => {
      let v26 = sub(t, 1u64);
      let v27 = &sa;
      let v29 = v26;
      let a = Clone::clone(&(v27)[v29]);
      let v31 = &sa;
      let v33 = t;
      let b = Clone::clone(&(v31)[v33]);
      let v36 = &r;
      let v38 = a;
      let v39 = Clone::clone(&(v36)[v38]);
      let v40 = &r;
      let v42 = b;
      let v43 = Clone::clone(&(v40)[v42]);
      let v49 = match eqb(v39, v43) {
        true => {
          let v54 = Rc::clone(&r);
          let v61 = skey(v54, n, k, a);
          let v65 = Rc::clone(&r);
          eqb(v61, skey(v65, n, k, b))
        },
        false => {
          false
        },
      };
      let c = match v49 {
        true => {
          cur
        },
        false => {
          add(cur, 1u64)
        },
      };
      let v106 = add(t, 1u64);
      let v113 = rocq_array::set::<u64>(nr, b, c);
      rank_loop(r, n, k, sa, v106, c, v113, ())
    },
    sumbool::right => {
      std::mem::drop(r);
      std::mem::drop(sa);
      (nr, cur)
    },
  }
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let v3 = Clone::clone((&(&p).1));
  std::mem::drop(p);
  v3
}

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  match b1 {
    true => {
      b2
    },
    false => {
      false
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
}

// Rocq: Suffixsorting.suffixsorting_implem.rounds
// Variant: uncurried
pub fn rounds_1(n: u64, k: u64, r: Rc<Array<u64>>, nr: Rc<Array<u64>>, sa: Rc<Array<u64>>, tmp: Rc<Array<u64>>) -> Rc<Array<u64>> {
  rounds(n, k, r, nr, sa, tmp, ())
}

// Rocq: Suffixsorting.suffixsorting_implem.rounds (local: rounds)
// Variant: uncurried, lifted
pub fn rounds(n: u64, k: u64, r: Rc<Array<u64>>, nr: Rc<Array<u64>>, sa: Rc<Array<u64>>, tmp: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v10 = Rc::clone(&r);
  let v17 = Rc::clone(&sa);
  let tmp1 = csort(v10, n, k, v17, tmp);
  let v26 = Rc::clone(&r);
  let v33 = Rc::clone(&tmp1);
  let sa1 = csort(v26, n, 0u64, v33, sa);
  let v44 = &sa1;
  let v46 = 0u64;
  let v47 = Clone::clone(&(v44)[v46]);
  let v56 = rocq_array::set::<u64>(nr, v47, 1u64);
  let v59 = Rc::clone(&r);
  let v66 = Rc::clone(&sa1);
  let q = rank_loop_1(v59, n, k, v66, 1u64, 1u64, v56);
  let v77 = Clone::clone(&q);
  let v80 = snd::<Rc<Array<u64>>, u64>(v77);
  match eqb(v80, n) {
    true => {
      std::mem::drop(q);
      std::mem::drop(tmp1);
      std::mem::drop(r);
      sa1
    },
    false => {
      let v96 = add(k, k);
      let v119 = andb(ltb(k, v96), ltb(add(k, k), n));
      match bdec(v119) {
        sumbool::left => {
          let v128 = add(k, k);
          let v132 = fst::<Rc<Array<u64>>, u64>(q);
          rounds(n, v128, v132, r, sa1, tmp1, ())
        },
        sumbool::right => {
          std::mem::drop(q);
          std::mem::drop(tmp1);
          std::mem::drop(r);
          sa1
        },
      }
    },
  }
}

// Rocq: Suffixsorting.suffixsorting_implem.suffix_array_impl
pub fn suffix_array_impl(x: Rc<rocq_string::RocqString>) -> Rc<Array<u64>> {
  let v4 = Rc::clone(&x);
  let n = length(v4);
  let v15 = rocq_array::make::<u64>(n, 0u64);
  let r = init_rank_1(x, n, 0u64, v15);
  let v34 = rocq_array::make::<u64>(n, 0u64);
  let sa = init_id_1(n, 0u64, v34);
  let v51 = rocq_array::make::<u64>(n, 0u64);
  let v58 = rocq_array::make::<u64>(n, 0u64);
  rounds_1(n, 1u64, r, v51, sa, v58)
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

pub fn run() -> Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<Array<u64>>> {
  let v0: Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<Array<u64>>> = __rocq_global_656.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_656: Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<Array<u64>>> = suffix_array(); }