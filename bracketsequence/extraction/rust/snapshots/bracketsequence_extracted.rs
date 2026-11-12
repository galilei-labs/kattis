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

pub enum token<A: 'static> {
  Open,
  Close,
  Num(A),
}

impl<A: Clone + 'static> Clone for token<A> {
  fn clone(&self) -> Self {
    match self {
      token::Open => token::Open,
      token::Close => token::Close,
      token::Num(__field0) => token::Num(Clone::clone(__field0)),
    }
  }
}

pub type uint = u64;

// Rocq: Bracketsequence.bracketsequence_implem.Mi
pub fn Mi() -> u64 {
  1000000007u64
}

// Rocq: Bracketsequence.bracketsequence_implem.bracketsequence
pub fn bracketsequence() -> Rc<dyn Fn(Rc<Array<Rc<token<u64>>>>) -> u64> {
  let v0: fn(Rc<Array<Rc<token<u64>>>>) -> u64 = bracketsequence_impl;
  let v1: Rc<dyn Fn(Rc<Array<Rc<token<u64>>>>) -> u64> = Rc::new(v0);
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

// Rocq: Bracketsequence.bracketsequence_implem.bdec
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

// Rocq: Bracketsequence.bracketsequence_implem.idm
pub fn idm(add_1: bool) -> u64 {
  match add_1 {
    true => {
      0u64
    },
    false => {
      1u64
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
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

// Rocq: Bracketsequence.bracketsequence_implem.opm
// Variant: uncurried
pub fn opm(add_1: bool, a: u64, v: u64) -> u64 {
  match add_1 {
    true => {
      mod_(add(a, v), __rocq_global_92)
    },
    false => {
      mod_(mul(a, v), __rocq_global_92)
    },
  }
}

// Rocq: Bracketsequence.bracketsequence_implem.loop
// Variant: uncurried
pub fn loop__1(x: Rc<Array<Rc<token<u64>>>>, n: u64, i: u64, d: u64, add_1: bool, stk: Rc<Array<u64>>) -> u64 {
  loop_(x, n, i, d, add_1, stk, ())
}

// Rocq: Bracketsequence.bracketsequence_implem.loop (local: loop)
// Variant: uncurried, lifted
pub fn loop_(x: Rc<Array<Rc<token<u64>>>>, n: u64, i: u64, d: u64, add_1: bool, stk: Rc<Array<u64>>, _H: ()) -> u64 {
  let v14 = ltb(i, n);
  match bdec(v14) {
    sumbool::left => {
      let v18 = &x;
      let v21 = rocq_array::get::<Rc<token<u64>>>(&v18, i);
      let (v22, v23) = __rocq_reuse::reset(v21, |__payload| Clone::clone(__payload));
      std::mem::drop(v23);
      match v22 {
        token::Open => {
          let v35 = add(i, 1u64);
          let v43 = add(d, 1u64);
          let v47 = negb(add_1);
          let v70 = rocq_array::set::<u64>(stk, add(d, 1u64), idm(negb(add_1)));
          loop_(x, n, v35, v43, v47, v70, ())
        },
        token::Close => {
          match eqb(d, 0u64) {
            true => {
              loop_(x, n, add(i, 1u64), d, add_1, stk, ())
            },
            false => {
              let v135 = add(i, 1u64);
              let v143 = sub(d, 1u64);
              let v147 = negb(add_1);
              let v155 = sub(d, 1u64);
              let v160 = negb(add_1);
              let v168 = sub(d, 1u64);
              let v169 = &stk;
              let v172 = rocq_array::get::<u64>(&v169, v168);
              let v173 = &stk;
              let v176 = rocq_array::get::<u64>(&v173, d);
              let v190 = rocq_array::set::<u64>(stk, v155, opm(v160, v172, v176));
              loop_(x, n, v135, v143, v147, v190, ())
            },
          }
        },
        token::Num(v214) => {
          let v223 = add(i, 1u64);
          let v225 = &stk;
          let v228 = rocq_array::get::<u64>(&v225, d);
          let v242 = rocq_array::set::<u64>(stk, d, opm(add_1, v228, v214));
          loop_(x, n, v223, d, add_1, v242, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      let v266 = &stk;
      let v269 = rocq_array::get::<u64>(&v266, d);
      std::mem::drop(stk);
      v269
    },
  }
}

// Rocq: Bracketsequence.bracketsequence_implem.bracketsequence_impl
pub fn bracketsequence_impl(x: Rc<Array<Rc<token<u64>>>>) -> u64 {
  let v1 = &x;
  let n = rocq_array::length::<Rc<token<u64>>>(&v1);
  let v24 = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  loop__1(x, n, 0u64, 0u64, true, v24)
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

pub fn run() -> Rc<dyn Fn(Rc<Array<Rc<token<u64>>>>) -> u64> {
  let v0: Rc<dyn Fn(Rc<Array<Rc<token<u64>>>>) -> u64> = __rocq_global_261.with(Clone::clone);
  v0
}
const __rocq_global_92: u64 = 1000000007u64;
std::thread_local! { static __rocq_global_261: Rc<dyn Fn(Rc<Array<Rc<token<u64>>>>) -> u64> = bracketsequence(); }