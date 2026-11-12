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

pub type char63 = u64;

// Rocq: Helpfulcurrents.helpfulcurrents_implem.P
pub fn P() -> u64 {
  1000003u64
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.helpfulcurrents
// Variant: uncurried
pub fn helpfulcurrents() -> Rc<dyn Fn(u64, u64, u64, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<u64>>> {
  let v0: fn(u64, u64, u64, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<u64>> = helpfulcurrents_impl;
  let v1: Rc<dyn Fn(u64, u64, u64, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<u64>>> = Rc::new(v0);
  v1
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.helpfulcurrents
pub fn helpfulcurrents_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<u64>>>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<u64>>>>> = helpfulcurrents_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<u64>>>>>> = Rc::new(v0);
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

// Rocq: Helpfulcurrents.helpfulcurrents_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let v5 = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  v5
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  match b {
    true => {
      false
    },
    false => {
      true
    },
  }
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.addm
// Variant: uncurried
pub fn addm(a: u64, b: u64) -> u64 {
  let s = add(a, b);
  match ltb(s, __rocq_global_93) {
    true => {
      s
    },
    false => {
      sub(s, __rocq_global_93)
    },
  }
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.orf
// Variant: uncurried
pub fn orf(a: u64, b: u64) -> u64 {
  match eqb(a, 0u64) {
    true => {
      b
    },
    false => {
      a
    },
  }
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.pass1
// Variant: uncurried
pub fn pass1_1(s: Rc<rocq_string::RocqString>, sb: Rc<rocq_string::RocqString>, Ym: u64, Xm: u64, xim: u64, y: u64, x: u64, wv: u64, wf: u64, cv: Rc<Array<u64>>, cf: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  pass1(s, sb, Ym, Xm, xim, y, x, wv, wf, cv, cf, ())
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.pass1 (local: pass1)
// Variant: uncurried, lifted
pub fn pass1(s: Rc<rocq_string::RocqString>, sb: Rc<rocq_string::RocqString>, Ym: u64, Xm: u64, xim: u64, y: u64, x: u64, wv: u64, wf: u64, cv: Rc<Array<u64>>, cf: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v19 = ltb(x, Xm);
  match bdec(v19) {
    sumbool::left => {
      let v26 = Rc::clone(&s);
      let c = get(v26, x);
      let st = andb(eqb(add(y, 1u64), Ym), eqb(x, xim));
      let sv = match st {
        true => {
          1u64
        },
        false => {
          0u64
        },
      };
      let v81 = ltb(add(y, 1u64), Ym);
      let v87 = Rc::clone(&sb);
      let v105 = andb(v81, negb(eqb(get(v87, x), 64u64)));
      let north = andb(v105, negb(eqb(c, 35u64)));
      let nv = match &north {
        true => {
          let v125 = &cv;
          rocq_array::get::<u64>(&v125, x)
        },
        false => {
          0u64
        },
      };
      let nf = match &north {
        true => {
          let v138 = &cf;
          rocq_array::get::<u64>(&v138, x)
        },
        false => {
          0u64
        },
      };
      let v156 = addm(sv, nv);
      let av = addm(v156, wv);
      let v168 = orf(sv, nf);
      let af = orf(v168, wf);
      let w = eqb(c, 62u64);
      let v188 = add(x, 1u64);
      let v190 = match &w {
        true => {
          av
        },
        false => {
          0u64
        },
      };
      let v199 = match &w {
        true => {
          af
        },
        false => {
          0u64
        },
      };
      let v213 = rocq_array::set::<u64>(cv, x, av);
      let v220 = rocq_array::set::<u64>(cf, x, af);
      pass1(s, sb, Ym, Xm, xim, y, v188, v190, v199, v213, v220, ())
    },
    sumbool::right => {
      std::mem::drop(s);
      std::mem::drop(sb);
      (cv, cf)
    },
  }
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.pass2
// Variant: uncurried
pub fn pass2_1(s: Rc<rocq_string::RocqString>, x: u64, ev: u64, ef: u64, cv: Rc<Array<u64>>, cf: Rc<Array<u64>>, av: u64, af: u64) -> ((Rc<Array<u64>>, Rc<Array<u64>>), (u64, u64)) {
  pass2(s, x, ev, ef, cv, cf, av, af, ())
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.pass2 (local: pass2)
// Variant: uncurried, lifted
pub fn pass2(s: Rc<rocq_string::RocqString>, x: u64, ev: u64, ef: u64, cv: Rc<Array<u64>>, cf: Rc<Array<u64>>, av: u64, af: u64, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), (u64, u64)) {
  let v18 = ltb(0u64, x);
  match bdec(v18) {
    sumbool::left => {
      let x_ = sub(x, 1u64);
      let v33 = Rc::clone(&s);
      let c = get(v33, x_);
      let v38 = &cv;
      let v42 = rocq_array::get::<u64>(&v38, x_);
      let bv = addm(v42, ev);
      let v48 = &cf;
      let v52 = rocq_array::get::<u64>(&v48, x_);
      let bf = orf(v52, ef);
      let e = eqb(c, 60u64);
      let k = eqb(c, 64u64);
      let v74 = match &e {
        true => {
          bv
        },
        false => {
          0u64
        },
      };
      let v83 = match &e {
        true => {
          bf
        },
        false => {
          0u64
        },
      };
      let v97 = rocq_array::set::<u64>(cv, x_, bv);
      let v104 = rocq_array::set::<u64>(cf, x_, bf);
      let v106 = match &k {
        true => {
          bv
        },
        false => {
          av
        },
      };
      let v113 = match &k {
        true => {
          bf
        },
        false => {
          af
        },
      };
      pass2(s, x_, v74, v83, v97, v104, v106, v113, ())
    },
    sumbool::right => {
      std::mem::drop(s);
      ((cv, cf), (av, af))
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

// Rocq: Helpfulcurrents.helpfulcurrents_implem.rows
// Variant: uncurried
pub fn rows_1(m: Rc<Array<Rc<rocq_string::RocqString>>>, Ym: u64, Xm: u64, xim: u64, k: u64, cv: Rc<Array<u64>>, cf: Rc<Array<u64>>, av: u64, af: u64) -> (u64, u64) {
  rows(m, Ym, Xm, xim, k, cv, cf, av, af, ())
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.rows (local: rows)
// Variant: uncurried, lifted
pub fn rows(m: Rc<Array<Rc<rocq_string::RocqString>>>, Ym: u64, Xm: u64, xim: u64, k: u64, cv: Rc<Array<u64>>, cf: Rc<Array<u64>>, av: u64, af: u64, _H: ()) -> (u64, u64) {
  let v19 = ltb(0u64, k);
  match bdec(v19) {
    sumbool::left => {
      let y = sub(k, 1u64);
      let v31 = &m;
      let s = rocq_array::get::<Rc<rocq_string::RocqString>>(&v31, y);
      let v36 = &m;
      let v39 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v36, k);
      let v48 = Rc::clone(&s);
      let r1 = pass1_1(v48, v39, Ym, Xm, xim, y, 0u64, 0u64, 0u64, cv, cf);
      let v77 = Clone::clone(&r1);
      let v79 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(v77);
      let v83 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(r1);
      let r2 = pass2_1(s, Xm, 0u64, 0u64, v79, v83, av, af);
      let v104 = Clone::clone(&r2);
      let v109 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), (u64, u64)>(v104));
      let v113 = Clone::clone(&r2);
      let v118 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), (u64, u64)>(v113));
      let v122 = Clone::clone(&r2);
      rows(m, Ym, Xm, xim, y, v109, v118, fst::<u64, u64>(snd::<(Rc<Array<u64>>, Rc<Array<u64>>), (u64, u64)>(v122)), snd::<u64, u64>(snd::<(Rc<Array<u64>>, Rc<Array<u64>>), (u64, u64)>(r2)), ())
    },
    sumbool::right => {
      std::mem::drop(m);
      std::mem::drop(cv);
      std::mem::drop(cf);
      (av, af)
    },
  }
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.helpfulcurrents_impl
// Variant: uncurried
pub fn helpfulcurrents_impl(Ym: u64, Xm: u64, xim: u64, m: Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<u64>> {
  let v11 = rocq_array::make::<u64>(Xm, 0u64);
  let v18 = rocq_array::make::<u64>(Xm, 0u64);
  let r = rows_1(m, Ym, Xm, xim, Ym, v11, v18, 0u64, 0u64);
  let v45 = Clone::clone(&r);
  let v47 = snd::<u64, u64>(v45);
  match eqb(v47, 0u64) {
    true => {
      std::mem::drop(r);
      Rc::new(option::<u64>::None)
    },
    false => {
      Rc::new(option::<u64>::Some(fst::<u64, u64>(r)))
    },
  }
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.helpfulcurrents_impl
pub fn helpfulcurrents_impl_curried(Ym: u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<u64>>>>> {
  let v3 = {
    move |Xm: u64| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<u64>>>> {
      let Ym = &Ym;
      let v8 = Clone::clone(Ym);
      let v11 = {
        move |xim: u64| -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<u64>>> {
          let Ym = &v8;
          let Xm = &Xm;
          let v18 = Clone::clone(Ym);
          let v20 = Clone::clone(Xm);
          let v23 = {
            move |m: Rc<Array<Rc<rocq_string::RocqString>>>| -> Rc<option<u64>> {
              let v33 = Clone::clone(&v18);
              let v35 = Clone::clone(&v20);
              let v37 = Clone::clone(&xim);
              helpfulcurrents_impl(v33, v35, v37, m)
            }
          };
          let v43: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<u64>>> = Rc::new(v23);
          v43
        }
      };
      let v47: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<u64>>>> = Rc::new(v11);
      v47
    }
  };
  let v51: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<u64>>>>> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(u64, u64, u64, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<u64>>> {
  let v0: Rc<dyn Fn(u64, u64, u64, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<u64>>> = __rocq_global_516.with(Clone::clone);
  v0
}
const __rocq_global_93: u64 = 1000003u64;
std::thread_local! { static __rocq_global_516: Rc<dyn Fn(u64, u64, u64, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<u64>>> = helpfulcurrents(); }
std::thread_local! { static __rocq_global_519: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<u64>>>>>> = helpfulcurrents_curried(); }