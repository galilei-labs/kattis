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
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Booking.spec.Prelude.year
// Variant: borrowed
pub fn year<A: Clone + 'static>(d: &Rc<datetime<A>>) -> A {
  let tmp = d;
  Clone::clone(&tmp.year)
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
  let tmp = mul(365u64, y);
  let tmp_1 = add(y, 3u64);
  let tmp_2 = sub(add(tmp, div(tmp_1, 4u64)), div(add(y, 99u64), 100u64));
  let tmp_3 = add(y, 399u64);
  add(tmp_2, div(tmp_3, 400u64))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Corelib.Init.Datatypes.orb
// Variant: uncurried
pub fn orb(b1: bool, b2: bool) -> bool {
  if b1 {
    true
  } else {
    b2
  }
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  if b {
    false
  } else {
    true
  }
}

// Rocq: Booking.booking_implem.leapb
pub fn leapb(y: u64) -> bool {
  orb(andb(eqb(mod_(y, 4u64), 0u64), negb(eqb(mod_(y, 100u64), 0u64))), eqb(mod_(y, 400u64), 0u64))
}

// Rocq: Booking.booking_implem.days_before_month
// Variant: uncurried
pub fn days_before_month(y: u64, m: u64) -> u64 {
  let tmp = div(sub(mul(367u64, m), 362u64), 12u64);
  let tmp_1 = 2u64;
  let tmp_2 = if leb(m, tmp_1) {
    0u64
  } else {
    if leapb(y) {
      1u64
    } else {
      2u64
    }
  };
  sub(tmp, tmp_2)
}

// Rocq: Booking.spec.Prelude.month
// Variant: borrowed
pub fn month<A: Clone + 'static>(d: &Rc<datetime<A>>) -> A {
  let tmp = d;
  Clone::clone(&tmp.month)
}

// Rocq: Booking.spec.Prelude.day
// Variant: borrowed
pub fn day<A: Clone + 'static>(d: &Rc<datetime<A>>) -> A {
  let tmp = d;
  Clone::clone(&tmp.day)
}

// Rocq: Booking.spec.Prelude.hour
// Variant: borrowed
pub fn hour<A: Clone + 'static>(d: &Rc<datetime<A>>) -> A {
  let tmp = d;
  Clone::clone(&tmp.hour)
}

// Rocq: Booking.spec.Prelude.minute
pub fn minute<A: Clone + 'static>(d: Rc<datetime<A>>) -> A {
  let d_minute_clone = Clone::clone(&d.minute);
  std::mem::drop(d);
  d_minute_clone
}

// Rocq: Booking.booking_implem.mach_minutes
pub fn mach_minutes(t: Rc<datetime<u64>>) -> u64 {
  let y = year::<u64>(&t);
  let tmp = days_before_year(y);
  let tmp_1 = month::<u64>(&t);
  let tmp_2 = add(tmp, days_before_month(y, tmp_1));
  let tmp_3 = day::<u64>(&t);
  let days = add(tmp_2, sub(tmp_3, 1u64));
  let tmp_4 = mul(days, 24u64);
  let tmp_5 = hour::<u64>(&t);
  let tmp_6 = add(tmp_4, tmp_5);
  add(mul(tmp_6, 60u64), minute::<u64>(t))
}

// Rocq: Booking.booking_implem.key_al
// Variant: uncurried
pub fn key_al(ma: u64, r: u64, i: u64) -> u64 {
  if eqb(ma, r) {
    let tmp = add(mul(ma, 20000u64), 5000u64);
    add(tmp, mul(2u64, i))
  } else {
    let tmp_1 = add(mul(ma, 20000u64), 15000u64);
    add(tmp_1, i)
  }
}

// Rocq: Booking.booking_implem.key_rh
// Variant: uncurried
pub fn key_rh(ma: u64, r: u64, i: u64) -> u64 {
  if eqb(ma, r) {
    let tmp = add(mul(ma, 20000u64), 5001u64);
    add(tmp, mul(2u64, i))
  } else {
    add(mul(r, 20000u64), i)
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
  let tmp = ltb(k, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<Rc<datetime<u64>>>(&xa, k);
      let ma = mach_minutes(tmp_1);
      let tmp_2 = rocq_array::get::<Rc<datetime<u64>>>(&xd, k);
      let r = add(mach_minutes(tmp_2), c);
      let tmp_3 = add(k, 1u64);
      let tmp_4 = key_al(ma, r, k);
      let tmp_5 = rocq_array::set::<u64>(A, k, tmp_4);
      let tmp_6 = key_rh(ma, r, k);
      let tmp_7 = rocq_array::set::<u64>(R, k, tmp_6);
      fill(xa, xd, c, n, tmp_3, tmp_5, tmp_7, ())
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
  let x = rocq_array::get::<u64>(&a, i);
  let y = rocq_array::get::<u64>(&a, j);
  let tmp = rocq_array::set::<u64>(a, i, y);
  rocq_array::set::<u64>(tmp, j, x)
}

// Rocq: Booking.booking_implem.part_loop
// Variant: uncurried
pub fn part_loop_1(a: Rc<Array<u64>>, p: u64, hi1: u64, i: u64, j: u64) -> (Rc<Array<u64>>, u64) {
  part_loop(a, p, hi1, i, j, ())
}

// Rocq: Booking.booking_implem.part_loop (local: part_loop)
// Variant: uncurried, lifted
pub fn part_loop(a: Rc<Array<u64>>, p: u64, hi1: u64, i: u64, j: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let tmp = ltb(j, hi1);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&a, j);
      if ltb(tmp_1, p) {
        let tmp_2 = swap(a, i, j);
        part_loop(tmp_2, p, hi1, add(i, 1u64), add(j, 1u64), ())
      } else {
        part_loop(a, p, hi1, i, add(j, 1u64), ())
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
  let tmp = sub(hi, lo);
  let mid = add(lo, div(tmp, 2u64));
  let hi1 = sub(hi, 1u64);
  let a1 = swap(a, mid, hi1);
  let p = rocq_array::get::<u64>(&a1, hi1);
  let tmp_1 = part_loop_1(a1, p, hi1, lo, lo);
  match tmp_1 {
    (v56, v58) => {
      let tmp_2 = swap(v56, v58, hi1);
      (tmp_2, v58)
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
  let tmp = ltb(add(lo, 1u64), hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = partition(a, lo, hi);
      match tmp_1 {
        (v32, v34) => {
          let tmp_2 = andb(leb(lo, v34), ltb(v34, hi));
          match bdec(tmp_2) {
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
  let tmp = rocq_array::length::<u64>(&a);
  qsort_1(a, 0u64, tmp)
}

// Rocq: Booking.booking_implem.sweep
// Variant: uncurried
pub fn sweep_1(A: Rc<Array<u64>>, R: Rc<Array<u64>>, n: u64, p: u64, q: u64, best: u64) -> u64 {
  sweep(A, R, n, p, q, best, ())
}

// Rocq: Booking.booking_implem.sweep (local: sweep)
// Variant: uncurried, lifted
pub fn sweep(A: Rc<Array<u64>>, R: Rc<Array<u64>>, n: u64, p: u64, q: u64, best: u64, _H: ()) -> u64 {
  let tmp = ltb(p, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = ltb(q, n);
      let tmp_2 = rocq_array::get::<u64>(&R, q);
      let tmp_3 = rocq_array::get::<u64>(&A, p);
      let tmp_4 = andb(tmp_1, leb(tmp_2, tmp_3));
      match bdec(tmp_4) {
        sumbool::left => {
          sweep(A, R, n, p, add(q, 1u64), best, ())
        },
        sumbool::right => {
          let tmp_5 = add(p, 1u64);
          let tmp_6 = add(best, q);
          let tmp_7 = add(p, 1u64);
          let tmp_8 = if ltb(tmp_6, tmp_7) {
            sub(add(p, 1u64), q)
          } else {
            best
          };
          sweep(A, R, n, tmp_5, q, tmp_8, ())
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
  let n = rocq_array::length::<Rc<datetime<u64>>>(&xa);
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let tmp_1 = rocq_array::make::<u64>(n, 0u64);
  let tmp_2 = fill_1(xa, xd, c, n, 0u64, tmp, tmp_1);
  match tmp_2 {
    (v38, v40) => {
      let A_ = sort_all(v38);
      let R_ = sort_all(v40);
      sweep_1(A_, R_, n, 0u64, 0u64, 0u64)
    },
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
