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
  if b {
    sumbool::left
  } else {
    sumbool::right
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
  let tmp = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  tmp
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  if b {
    false
  } else {
    true
  }
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.addm
// Variant: uncurried
pub fn addm(a: u64, b: u64) -> u64 {
  let s = add(a, b);
  if ltb(s, __rocq_global_93) {
    s
  } else {
    sub(s, __rocq_global_93)
  }
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.orf
// Variant: uncurried
pub fn orf(a: u64, b: u64) -> u64 {
  if eqb(a, 0u64) {
    b
  } else {
    a
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
  let tmp = ltb(x, Xm);
  match bdec(tmp) {
    sumbool::left => {
      let s_clone = Rc::clone(&s);
      let c = get(s_clone, x);
      let st = andb(eqb(add(y, 1u64), Ym), eqb(x, xim));
      let sv = if st {
        1u64
      } else {
        0u64
      };
      let tmp_1 = ltb(add(y, 1u64), Ym);
      let sb_clone = Rc::clone(&sb);
      let tmp_2 = andb(tmp_1, negb(eqb(get(sb_clone, x), 64u64)));
      let north = andb(tmp_2, negb(eqb(c, 35u64)));
      let nv = if north {
        rocq_array::get::<u64>(&cv, x)
      } else {
        0u64
      };
      let nf = if north {
        rocq_array::get::<u64>(&cf, x)
      } else {
        0u64
      };
      let tmp_3 = addm(sv, nv);
      let av = addm(tmp_3, wv);
      let tmp_4 = orf(sv, nf);
      let af = orf(tmp_4, wf);
      let w = eqb(c, 62u64);
      let tmp_5 = add(x, 1u64);
      let tmp_6 = if w {
        av
      } else {
        0u64
      };
      let tmp_7 = if w {
        af
      } else {
        0u64
      };
      let tmp_8 = rocq_array::set::<u64>(cv, x, av);
      let tmp_9 = rocq_array::set::<u64>(cf, x, af);
      pass1(s, sb, Ym, Xm, xim, y, tmp_5, tmp_6, tmp_7, tmp_8, tmp_9, ())
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
  let tmp = ltb(0u64, x);
  match bdec(tmp) {
    sumbool::left => {
      let x_ = sub(x, 1u64);
      let s_clone = Rc::clone(&s);
      let c = get(s_clone, x_);
      let tmp_1 = rocq_array::get::<u64>(&cv, x_);
      let bv = addm(tmp_1, ev);
      let tmp_2 = rocq_array::get::<u64>(&cf, x_);
      let bf = orf(tmp_2, ef);
      let e = eqb(c, 60u64);
      let k = eqb(c, 64u64);
      let tmp_3 = if e {
        bv
      } else {
        0u64
      };
      let tmp_4 = if e {
        bf
      } else {
        0u64
      };
      let tmp_5 = rocq_array::set::<u64>(cv, x_, bv);
      let tmp_6 = rocq_array::set::<u64>(cf, x_, bf);
      let tmp_7 = if k {
        bv
      } else {
        av
      };
      let tmp_8 = if k {
        bf
      } else {
        af
      };
      pass2(s, x_, tmp_3, tmp_4, tmp_5, tmp_6, tmp_7, tmp_8, ())
    },
    sumbool::right => {
      std::mem::drop(s);
      ((cv, cf), (av, af))
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.pass2r
// Variant: uncurried
pub fn pass2r(s: Rc<rocq_string::RocqString>, Xm: u64, r1: (Rc<Array<u64>>, Rc<Array<u64>>), av: u64, af: u64) -> ((Rc<Array<u64>>, Rc<Array<u64>>), (u64, u64)) {
  let r1_clone = Clone::clone(&r1);
  let tmp = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(r1_clone);
  let tmp_1 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(r1);
  pass2_1(s, Xm, 0u64, 0u64, tmp, tmp_1, av, af)
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.rows
// Variant: uncurried
pub fn rows_1(m: Rc<Array<Rc<rocq_string::RocqString>>>, Ym: u64, Xm: u64, xim: u64, k: u64, cv: Rc<Array<u64>>, cf: Rc<Array<u64>>, av: u64, af: u64) -> (u64, u64) {
  rows(m, Ym, Xm, xim, k, cv, cf, av, af, ())
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.rows (local: rows)
// Variant: uncurried, lifted
pub fn rows(m: Rc<Array<Rc<rocq_string::RocqString>>>, Ym: u64, Xm: u64, xim: u64, k: u64, cv: Rc<Array<u64>>, cf: Rc<Array<u64>>, av: u64, af: u64, _H: ()) -> (u64, u64) {
  let tmp = ltb(0u64, k);
  match bdec(tmp) {
    sumbool::left => {
      let y = sub(k, 1u64);
      let s = rocq_array::get::<Rc<rocq_string::RocqString>>(&m, y);
      let tmp_1 = rocq_array::get::<Rc<rocq_string::RocqString>>(&m, k);
      let s_clone = Rc::clone(&s);
      let r1 = pass1_1(s_clone, tmp_1, Ym, Xm, xim, y, 0u64, 0u64, 0u64, cv, cf);
      let r2 = pass2r(s, Xm, r1, av, af);
      let r2_clone = Clone::clone(&r2);
      let tmp_2 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), (u64, u64)>(r2_clone));
      let r2_clone_1 = Clone::clone(&r2);
      let tmp_3 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), (u64, u64)>(r2_clone_1));
      let r2_clone_2 = Clone::clone(&r2);
      rows(m, Ym, Xm, xim, y, tmp_2, tmp_3, fst::<u64, u64>(snd::<(Rc<Array<u64>>, Rc<Array<u64>>), (u64, u64)>(r2_clone_2)), snd::<u64, u64>(snd::<(Rc<Array<u64>>, Rc<Array<u64>>), (u64, u64)>(r2)), ())
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
  let tmp = rocq_array::make::<u64>(Xm, 0u64);
  let tmp_1 = rocq_array::make::<u64>(Xm, 0u64);
  let r = rows_1(m, Ym, Xm, xim, Ym, tmp, tmp_1, 0u64, 0u64);
  let r_clone = Clone::clone(&r);
  let tmp_2 = snd::<u64, u64>(r_clone);
  if eqb(tmp_2, 0u64) {
    std::mem::drop(r);
    Rc::new(option::<u64>::None)
  } else {
    Rc::new(option::<u64>::Some(fst::<u64, u64>(r)))
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
const __rocq_global_93: u64 = 1000003u64;