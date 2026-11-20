#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

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

pub type uint = Int63;

// Rocq: Booking.booking_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
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

// Rocq: Booking.booking_implem.days_before_year
pub fn days_before_year(y: Int63) -> Int63 {
  int63!(365) * y + (y + int63!(3)) / int63!(4) - (y + int63!(99)) / int63!(100) + (y + int63!(399)) / int63!(400)
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

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b_1: bool) -> bool {
  if b_1 {
    false
  } else {
    true
  }
}

// Rocq: Booking.booking_implem.leapb
pub fn leapb(y: Int63) -> bool {
  orb(andb(y % int63!(4) == int63!(0), negb(y % int63!(100) == int63!(0))), y % int63!(400) == int63!(0))
}

// Rocq: Booking.booking_implem.days_before_month
// Variant: uncurried
pub fn days_before_month(y: Int63, m: Int63) -> Int63 {
  let tmp = (int63!(367) * m - int63!(362)) / int63!(12);
  let tmp_1 = int63!(2);
  let tmp_2 = if m <= tmp_1 {
    int63!(0)
  } else {
    if leapb(y) {
      int63!(1)
    } else {
      int63!(2)
    }
  };
  tmp - tmp_2
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
pub fn mach_minutes(t: Rc<datetime<Int63>>) -> Int63 {
  let y = year::<Int63>(&t);
  let tmp = days_before_year(y);
  let tmp_1 = month::<Int63>(&t);
  let tmp_2 = tmp + days_before_month(y, tmp_1);
  let tmp_3 = day::<Int63>(&t);
  let days = tmp_2 + (tmp_3 - int63!(1));
  let tmp_4 = days * int63!(24);
  let tmp_5 = hour::<Int63>(&t);
  (tmp_4 + tmp_5) * int63!(60) + minute::<Int63>(t)
}

// Rocq: Booking.booking_implem.key_al
// Variant: uncurried
pub fn key_al(ma: Int63, r: Int63, i: Int63) -> Int63 {
  if ma == r {
    ma * int63!(20000) + int63!(5000) + int63!(2) * i
  } else {
    ma * int63!(20000) + int63!(15000) + i
  }
}

// Rocq: Booking.booking_implem.key_rh
// Variant: uncurried
pub fn key_rh(ma: Int63, r: Int63, i: Int63) -> Int63 {
  if ma == r {
    ma * int63!(20000) + int63!(5001) + int63!(2) * i
  } else {
    r * int63!(20000) + i
  }
}

// Rocq: Booking.booking_implem.fill
// Variant: uncurried
pub fn fill_1(xa: Array<Rc<datetime<Int63>>>, xd: Array<Rc<datetime<Int63>>>, c: Int63, n: Int63, k: Int63, A: Array<Int63>, R: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  fill(xa, xd, c, n, k, A, R, ())
}

// Rocq: Booking.booking_implem.fill (local: fill)
// Variant: uncurried, lifted
pub fn fill(xa: Array<Rc<datetime<Int63>>>, xd: Array<Rc<datetime<Int63>>>, c: Int63, n: Int63, k: Int63, A: Array<Int63>, R: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = k < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = xa.get_cloned(k);
      let ma = mach_minutes(tmp_1);
      let tmp_2 = xd.get_cloned(k);
      let r = mach_minutes(tmp_2) + c;
      let tmp_3 = k + int63!(1);
      let tmp_4 = key_al(ma, r, k);
      let tmp_5 = A.set(k, tmp_4);
      let tmp_6 = key_rh(ma, r, k);
      fill(xa, xd, c, n, tmp_3, tmp_5, R.set(k, tmp_6), ())
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
pub fn swap(a_1: Array<Int63>, i: Int63, j: Int63) -> Array<Int63> {
  let x = a_1.get_cloned(i);
  let y = a_1.get_cloned(j);
  a_1.set(i, y).set(j, x)
}

// Rocq: Booking.booking_implem.part_loop
// Variant: uncurried
pub fn part_loop_1(a_1: Array<Int63>, p: Int63, hi1: Int63, i: Int63, j: Int63) -> (Array<Int63>, Int63) {
  part_loop(a_1, p, hi1, i, j, ())
}

// Rocq: Booking.booking_implem.part_loop (local: part_loop)
// Variant: uncurried, lifted
pub fn part_loop(a_1: Array<Int63>, p: Int63, hi1: Int63, i: Int63, j: Int63, _H: ()) -> (Array<Int63>, Int63) {
  let tmp = j < hi1;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = a_1.get_cloned(j);
      if tmp_1 < p {
        part_loop(swap(a_1, i, j), p, hi1, i + int63!(1), j + int63!(1), ())
      } else {
        part_loop(a_1, p, hi1, i, j + int63!(1), ())
      }
    },
    sumbool::right => {
      (a_1, i)
    },
  }
}

// Rocq: Booking.booking_implem.partition
// Variant: uncurried
pub fn partition(a_1: Array<Int63>, lo: Int63, hi: Int63) -> (Array<Int63>, Int63) {
  let tmp = hi - lo;
  let mid = lo + tmp / int63!(2);
  let hi1 = hi - int63!(1);
  let a1 = swap(a_1, mid, hi1);
  let p = a1.get_cloned(hi1);
  let tmp_1 = part_loop_1(a1, p, hi1, lo, lo);
  match tmp_1 {
    (v56, v58) => {
      (swap(v56, v58, hi1), v58)
    },
  }
}

// Rocq: Booking.booking_implem.qsort
// Variant: uncurried
pub fn qsort_1(a_1: Array<Int63>, lo: Int63, hi: Int63) -> Array<Int63> {
  qsort(a_1, lo, hi, ())
}

// Rocq: Booking.booking_implem.qsort (local: qsort)
// Variant: uncurried, lifted
pub fn qsort(a_1: Array<Int63>, lo: Int63, hi: Int63, _H: ()) -> Array<Int63> {
  let tmp = lo + int63!(1) < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = partition(a_1, lo, hi);
      match tmp_1 {
        (v32, v34) => {
          let tmp_2 = andb(lo <= v34, v34 < hi);
          match bdec(tmp_2) {
            sumbool::left => {
              let a2 = qsort(v32, lo, v34, ());
              qsort(a2, v34 + int63!(1), hi, ())
            },
            sumbool::right => {
              v32
            },
          }
        },
      }
    },
    sumbool::right => {
      a_1
    },
  }
}

// Rocq: Booking.booking_implem.sort_all
pub fn sort_all(a_1: Array<Int63>) -> Array<Int63> {
  let tmp = a_1.length();
  qsort_1(a_1, int63!(0), tmp)
}

// Rocq: Booking.booking_implem.sweep
// Variant: uncurried
pub fn sweep_1(A: Array<Int63>, R: Array<Int63>, n: Int63, p: Int63, q: Int63, best: Int63) -> Int63 {
  sweep(A, R, n, p, q, best, ())
}

// Rocq: Booking.booking_implem.sweep (local: sweep)
// Variant: uncurried, lifted
pub fn sweep(A: Array<Int63>, R: Array<Int63>, n: Int63, p: Int63, q: Int63, best: Int63, _H: ()) -> Int63 {
  let tmp = p < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = q < n;
      let tmp_2 = R.get_cloned(q);
      let tmp_3 = A.get_cloned(p);
      let tmp_4 = andb(tmp_1, tmp_2 <= tmp_3);
      match bdec(tmp_4) {
        sumbool::left => {
          sweep(A, R, n, p, q + int63!(1), best, ())
        },
        sumbool::right => {
          let tmp_5 = p + int63!(1);
          let tmp_6 = best + q;
          let tmp_7 = p + int63!(1);
          let tmp_8 = if tmp_6 < tmp_7 {
            p + int63!(1) - q
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
pub fn min_rooms_impl(c: Int63, xa: Array<Rc<datetime<Int63>>>, xd: Array<Rc<datetime<Int63>>>) -> Int63 {
  let n = xa.length();
  let tmp = Array::<Int63>::make(n, int63!(0));
  let tmp_1 = Array::<Int63>::make(n, int63!(0));
  let tmp_2 = fill_1(xa, xd, c, n, int63!(0), tmp, tmp_1);
  match tmp_2 {
    (v38, v40) => {
      let A_ = sort_all(v38);
      let R_ = sort_all(v40);
      sweep_1(A_, R_, n, int63!(0), int63!(0), int63!(0))
    },
  }
}
