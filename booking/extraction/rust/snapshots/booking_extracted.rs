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

pub struct datetime<A: 'static> {
  pub year: A,
  pub month: A,
  pub day: A,
  pub hour: A,
  pub minute: A,
}

impl<A: Clone + 'static> Clone for datetime<A> {
  fn clone(&self) -> Self {
    match self {
      datetime { year: __field0, month: __field1, day: __field2, hour: __field3, minute: __field4 } => datetime { year: Clone::clone(__field0), month: Clone::clone(__field1), day: Clone::clone(__field2), hour: Clone::clone(__field3), minute: Clone::clone(__field4) },
    }
  }
}

pub type uint = u64;

// Rocq: Booking.booking_implem.min_rooms
// Variant: uncurried
pub fn min_rooms() -> Rc<dyn Fn(u64, Rc<Array<Rc<datetime<u64>>>>, Rc<Array<Rc<datetime<u64>>>>) -> u64> {
  let v0: fn(u64, Rc<Array<Rc<datetime<u64>>>>, Rc<Array<Rc<datetime<u64>>>>) -> u64 = min_rooms_impl;
  let v1: Rc<dyn Fn(u64, Rc<Array<Rc<datetime<u64>>>>, Rc<Array<Rc<datetime<u64>>>>) -> u64> = Rc::new(v0);
  v1
}

// Rocq: Booking.booking_implem.min_rooms
pub fn min_rooms_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<datetime<u64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<datetime<u64>>>>) -> u64>>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<datetime<u64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<datetime<u64>>>>) -> u64>> = min_rooms_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<datetime<u64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<datetime<u64>>>>) -> u64>>> = Rc::new(v0);
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

// Rocq: Booking.booking_implem.bdec
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

// Rocq: Booking.spec.Prelude.year
// Variant: borrowed
pub fn year<A: Clone + 'static>(d: &Rc<datetime<A>>) -> A {
  let v1 = d;
  Clone::clone((&(&**v1).year))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Booking.booking_implem.days_before_year
pub fn days_before_year(y: u64) -> u64 {
  let v11 = mul(365u64, y);
  let v20 = add(y, 3u64);
  let v53 = sub(add(v11, div(v20, 4u64)), div(add(y, 99u64), 100u64));
  let v62 = add(y, 399u64);
  add(v53, div(v62, 400u64))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Corelib.Init.Datatypes.orb
// Variant: uncurried
pub fn orb(b1: bool, b2: bool) -> bool {
  match b1 {
    true => {
      true
    },
    false => {
      b2
    },
  }
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
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

// Rocq: Booking.booking_implem.leapb
pub fn leapb(y: u64) -> bool {
  orb(andb(eqb(mod_(y, 4u64), 0u64), negb(eqb(mod_(y, 100u64), 0u64))), eqb(mod_(y, 400u64), 0u64))
}

// Rocq: Booking.booking_implem.days_before_month
// Variant: uncurried
pub fn days_before_month(y: u64, m: u64) -> u64 {
  let v26 = div(sub(mul(367u64, m), 362u64), 12u64);
  let v29 = 2u64;
  let v35 = match leb(m, v29) {
    true => {
      0u64
    },
    false => {
      match leapb(y) {
        true => {
          1u64
        },
        false => {
          2u64
        },
      }
    },
  };
  sub(v26, v35)
}

// Rocq: Booking.spec.Prelude.month
// Variant: borrowed
pub fn month<A: Clone + 'static>(d: &Rc<datetime<A>>) -> A {
  let v1 = d;
  Clone::clone((&(&**v1).month))
}

// Rocq: Booking.spec.Prelude.day
// Variant: borrowed
pub fn day<A: Clone + 'static>(d: &Rc<datetime<A>>) -> A {
  let v1 = d;
  Clone::clone((&(&**v1).day))
}

// Rocq: Booking.spec.Prelude.hour
// Variant: borrowed
pub fn hour<A: Clone + 'static>(d: &Rc<datetime<A>>) -> A {
  let v1 = d;
  Clone::clone((&(&**v1).hour))
}

// Rocq: Booking.spec.Prelude.minute
pub fn minute<A: Clone + 'static>(d: Rc<datetime<A>>) -> A {
  let v3 = Clone::clone((&(&**&d).minute));
  std::mem::drop(d);
  v3
}

// Rocq: Booking.booking_implem.mach_minutes
pub fn mach_minutes(t: Rc<datetime<u64>>) -> u64 {
  let y = year::<u64>(&t);
  let v10 = days_before_year(y);
  let v15 = month::<u64>(&t);
  let v25 = add(v10, days_before_month(y, v15));
  let v30 = day::<u64>(&t);
  let days = add(v25, sub(v30, 1u64));
  let v53 = mul(days, 24u64);
  let v57 = hour::<u64>(&t);
  let v62 = add(v53, v57);
  add(mul(v62, 60u64), minute::<u64>(t))
}

// Rocq: Booking.booking_implem.key_al
// Variant: uncurried
pub fn key_al(ma: u64, r: u64, i: u64) -> u64 {
  match eqb(ma, r) {
    true => {
      let v26 = add(mul(ma, 20000u64), 5000u64);
      add(v26, mul(2u64, i))
    },
    false => {
      let v59 = add(mul(ma, 20000u64), 15000u64);
      add(v59, i)
    },
  }
}

// Rocq: Booking.booking_implem.key_rh
// Variant: uncurried
pub fn key_rh(ma: u64, r: u64, i: u64) -> u64 {
  match eqb(ma, r) {
    true => {
      let v26 = add(mul(ma, 20000u64), 5001u64);
      add(v26, mul(2u64, i))
    },
    false => {
      add(mul(r, 20000u64), i)
    },
  }
}

// Rocq: Booking.booking_implem.fill
// Variant: uncurried
pub fn fill_1(xa: Rc<Array<Rc<datetime<u64>>>>, xd: Rc<Array<Rc<datetime<u64>>>>, c: u64, n: u64, k: u64, A: Rc<Array<u64>>, R: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  fill(xa, xd, c, n, k, A, R, ())
}

// Rocq: Booking.booking_implem.fill (local: fill)
// Variant: uncurried, lifted
pub fn fill(xa: Rc<Array<Rc<datetime<u64>>>>, xd: Rc<Array<Rc<datetime<u64>>>>, c: u64, n: u64, k: u64, A: Rc<Array<u64>>, R: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v15 = ltb(k, n);
  match bdec(v15) {
    sumbool::left => {
      let v20 = &xa;
      let v24 = rocq_array::get::<Rc<datetime<u64>>>(&v20, k);
      let ma = mach_minutes(v24);
      let v29 = &xd;
      let v33 = rocq_array::get::<Rc<datetime<u64>>>(&v29, k);
      let r = add(mach_minutes(v33), c);
      let v48 = add(k, 1u64);
      let v56 = key_al(ma, r, k);
      let v63 = rocq_array::set::<u64>(A, k, v56);
      let v71 = key_rh(ma, r, k);
      let v78 = rocq_array::set::<u64>(R, k, v71);
      fill(xa, xd, c, n, v48, v63, v78, ())
    },
    sumbool::right => {
      std::mem::drop(xa);
      std::mem::drop(xd);
      (A, R)
    },
  }
}

// Rocq: Booking.booking_implem.swap
// Variant: uncurried
pub fn swap(a: Rc<Array<u64>>, i: u64, j: u64) -> Rc<Array<u64>> {
  let v3 = &a;
  let x = rocq_array::get::<u64>(&v3, i);
  let v7 = &a;
  let y = rocq_array::get::<u64>(&v7, j);
  let v18 = rocq_array::set::<u64>(a, i, y);
  rocq_array::set::<u64>(v18, j, x)
}

// Rocq: Booking.booking_implem.part_loop
// Variant: uncurried
pub fn part_loop_1(a: Rc<Array<u64>>, p: u64, hi1: u64, i: u64, j: u64) -> (Rc<Array<u64>>, u64) {
  part_loop(a, p, hi1, i, j, ())
}

// Rocq: Booking.booking_implem.part_loop (local: part_loop)
// Variant: uncurried, lifted
pub fn part_loop(a: Rc<Array<u64>>, p: u64, hi1: u64, i: u64, j: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let v13 = ltb(j, hi1);
  match bdec(v13) {
    sumbool::left => {
      let v18 = &a;
      let v22 = rocq_array::get::<u64>(&v18, j);
      match ltb(v22, p) {
        true => {
          let v35 = swap(a, i, j);
          part_loop(v35, p, hi1, add(i, 1u64), add(j, 1u64), ())
        },
        false => {
          part_loop(a, p, hi1, i, add(j, 1u64), ())
        },
      }
    },
    sumbool::right => {
      (a, i)
    },
  }
}

// Rocq: Booking.booking_implem.partition
// Variant: uncurried
pub fn partition(a: Rc<Array<u64>>, lo: u64, hi: u64) -> (Rc<Array<u64>>, u64) {
  let v10 = sub(hi, lo);
  let mid = add(lo, div(v10, 2u64));
  let hi1 = sub(hi, 1u64);
  let a1 = swap(a, mid, hi1);
  let v39 = &a1;
  let p = rocq_array::get::<u64>(&v39, hi1);
  let v54 = part_loop_1(a1, p, hi1, lo, lo);
  match v54 {
    (v56, v58) => {
      let v68 = swap(v56, v58, hi1);
      (v68, v58)
    },
  }
}

// Rocq: Booking.booking_implem.qsort
// Variant: uncurried
pub fn qsort_1(a: Rc<Array<u64>>, lo: u64, hi: u64) -> Rc<Array<u64>> {
  qsort(a, lo, hi, ())
}

// Rocq: Booking.booking_implem.qsort (local: qsort)
// Variant: uncurried, lifted
pub fn qsort(a: Rc<Array<u64>>, lo: u64, hi: u64, _H: ()) -> Rc<Array<u64>> {
  let v19 = ltb(add(lo, 1u64), hi);
  match bdec(v19) {
    sumbool::left => {
      let v30 = partition(a, lo, hi);
      match v30 {
        (v32, v34) => {
          let v55 = andb(leb(lo, v34), ltb(v34, hi));
          match bdec(v55) {
            sumbool::left => {
              let a2 = qsort(v32, lo, v34, ());
              qsort(a2, add(v34, 1u64), hi, ())
            },
            sumbool::right => {
              v32
            },
          }
        },
      }
    },
    sumbool::right => {
      a
    },
  }
}

// Rocq: Booking.booking_implem.sort_all
pub fn sort_all(a: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v4 = &a;
  let v5 = rocq_array::length::<u64>(&v4);
  qsort_1(a, 0u64, v5)
}

// Rocq: Booking.booking_implem.sweep
// Variant: uncurried
pub fn sweep_1(A: Rc<Array<u64>>, R: Rc<Array<u64>>, n: u64, p: u64, q: u64, best: u64) -> u64 {
  sweep(A, R, n, p, q, best, ())
}

// Rocq: Booking.booking_implem.sweep (local: sweep)
// Variant: uncurried, lifted
pub fn sweep(A: Rc<Array<u64>>, R: Rc<Array<u64>>, n: u64, p: u64, q: u64, best: u64, _H: ()) -> u64 {
  let v14 = ltb(p, n);
  match bdec(v14) {
    sumbool::left => {
      let v25 = ltb(q, n);
      let v27 = &R;
      let v30 = rocq_array::get::<u64>(&v27, q);
      let v31 = &A;
      let v34 = rocq_array::get::<u64>(&v31, p);
      let v45 = andb(v25, leb(v30, v34));
      match bdec(v45) {
        sumbool::left => {
          sweep(A, R, n, p, add(q, 1u64), best, ())
        },
        sumbool::right => {
          let v84 = add(p, 1u64);
          let v91 = add(best, q);
          let v99 = add(p, 1u64);
          let v105 = match ltb(v91, v99) {
            true => {
              sub(add(p, 1u64), q)
            },
            false => {
              best
            },
          };
          sweep(A, R, n, v84, q, v105, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(A);
      std::mem::drop(R);
      best
    },
  }
}

// Rocq: Booking.booking_implem.min_rooms_impl
// Variant: uncurried
pub fn min_rooms_impl(c: u64, xa: Rc<Array<Rc<datetime<u64>>>>, xd: Rc<Array<Rc<datetime<u64>>>>) -> u64 {
  let v3 = &xa;
  let n = rocq_array::length::<Rc<datetime<u64>>>(&v3);
  let v14 = rocq_array::make::<u64>(n, 0u64);
  let v21 = rocq_array::make::<u64>(n, 0u64);
  let v36 = fill_1(xa, xd, c, n, 0u64, v14, v21);
  match v36 {
    (v38, v40) => {
      let A_ = sort_all(v38);
      let R_ = sort_all(v40);
      sweep_1(A_, R_, n, 0u64, 0u64, 0u64)
    },
  }
}

// Rocq: Booking.booking_implem.min_rooms_impl
pub fn min_rooms_impl_curried(c: u64) -> Rc<dyn Fn(Rc<Array<Rc<datetime<u64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<datetime<u64>>>>) -> u64>> {
  let v3 = {
    move |xa: Rc<Array<Rc<datetime<u64>>>>| -> Rc<dyn Fn(Rc<Array<Rc<datetime<u64>>>>) -> u64> {
      let c = &c;
      let v8 = Clone::clone(c);
      let v11 = {
        move |xd: Rc<Array<Rc<datetime<u64>>>>| -> u64 {
          let v19 = Clone::clone(&v8);
          let v21 = Rc::clone(&xa);
          min_rooms_impl(v19, v21, xd)
        }
      };
      let v27: Rc<dyn Fn(Rc<Array<Rc<datetime<u64>>>>) -> u64> = Rc::new(v11);
      v27
    }
  };
  let v31: Rc<dyn Fn(Rc<Array<Rc<datetime<u64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<datetime<u64>>>>) -> u64>> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<Rc<datetime<u64>>>>, Rc<Array<Rc<datetime<u64>>>>) -> u64> {
  let v0: Rc<dyn Fn(u64, Rc<Array<Rc<datetime<u64>>>>, Rc<Array<Rc<datetime<u64>>>>) -> u64> = __rocq_global_722.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_722: Rc<dyn Fn(u64, Rc<Array<Rc<datetime<u64>>>>, Rc<Array<Rc<datetime<u64>>>>) -> u64> = min_rooms(); }
std::thread_local! { static __rocq_global_725: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<datetime<u64>>>>) -> Rc<dyn Fn(Rc<Array<Rc<datetime<u64>>>>) -> u64>>> = min_rooms_curried(); }