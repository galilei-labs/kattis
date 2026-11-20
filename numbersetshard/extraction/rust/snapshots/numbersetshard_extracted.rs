#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};
#[allow(unused_imports)] use rocq_bigint as b;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::PositiveTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::NaturalTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::IntegerTag>; };

pub type uint = Int63;

// Rocq: Numbersetshard.numbersetshard_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Numbersetshard.numbersetshard_implem.mark
// Variant: uncurried
pub fn mark_1(c: Array<bool>, i: Int63, cnt: Int63, t: Int63, j: Int63) -> Array<bool> {
  mark(c, i, cnt, t, j, ())
}

// Rocq: Numbersetshard.numbersetshard_implem.mark (local: mark)
// Variant: uncurried, lifted
pub fn mark(c: Array<bool>, i: Int63, cnt: Int63, t: Int63, j: Int63, _H: ()) -> Array<bool> {
  let tmp = t < cnt;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = c.set(j, true);
      let tmp_2 = t + int63!(1);
      let tmp_3 = j + i;
      mark(tmp_1, i, cnt, tmp_2, tmp_3, ())
    },
    sumbool::right => {
      c
    },
  }
}

// Rocq: Numbersetshard.numbersetshard_implem.mark_from
// Variant: uncurried
pub fn mark_from(c: Array<bool>, w: Int63, i: Int63) -> Array<bool> {
  let s = i * i;
  let cnt = (w - s) / i + int63!(1);
  mark_1(c, i, cnt, int63!(0), s)
}

// Rocq: Numbersetshard.numbersetshard_implem.sieve
// Variant: uncurried
pub fn sieve_1(c: Array<bool>, w: Int63, n: Int63, i: Int63) -> Array<bool> {
  sieve(c, w, n, i, ())
}

// Rocq: Numbersetshard.numbersetshard_implem.sieve (local: sieve)
// Variant: uncurried, lifted
pub fn sieve(c: Array<bool>, w: Int63, n: Int63, i: Int63, _H: ()) -> Array<bool> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i * i;
      if tmp_1 <= w {
        let tmp_2 = c.get_cloned(i);
        let c_ = if tmp_2 {
          c
        } else {
          mark_from(c, w, i)
        };
        sieve(c_, w, n, i + int63!(1), ())
      } else {
        c
      }
    },
    sumbool::right => {
      c
    },
  }
}

// Rocq: Numbersetshard.numbersetshard_implem.iota
// Variant: uncurried
pub fn iota_1(par: Array<Int63>, n: Int63, i: Int63) -> Array<Int63> {
  iota(par, n, i, ())
}

// Rocq: Numbersetshard.numbersetshard_implem.iota (local: iota)
// Variant: uncurried, lifted
pub fn iota(par: Array<Int63>, n: Int63, i: Int63, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      iota(par.set(i, i), n, i + int63!(1), ())
    },
    sumbool::right => {
      par
    },
  }
}

// Rocq: Numbersetshard.numbersetshard_implem.first_off
// Variant: uncurried
pub fn first_off(a_1: Int63, q: Int63) -> Int63 {
  let tmp = a_1 % q;
  (q - tmp) % q
}

// Rocq: Numbersetshard.numbersetshard_implem.find
// Variant: uncurried
pub fn find_1(par: Array<Int63>, rk: Array<Int63>, x: Int63) -> (Int63, Array<Int63>) {
  find(par, rk, x, ())
}

// Rocq: Numbersetshard.numbersetshard_implem.find (local: find)
// Variant: uncurried, lifted
pub fn find(par: Array<Int63>, rk: Array<Int63>, x: Int63, _H: ()) -> (Int63, Array<Int63>) {
  let y = par.get_cloned(x);
  if y == x {
    std::mem::drop(rk);
    (x, par)
  } else {
    let z = par.get_cloned(y);
    let tmp = rk.get_cloned(x);
    let tmp_1 = rk.get_cloned(z);
    let tmp_2 = tmp < tmp_1;
    match bdec(tmp_2) {
      sumbool::left => {
        find(par.set(x, z), rk, z, ())
      },
      sumbool::right => {
        std::mem::drop(rk);
        (x, par)
      },
    }
  }
}

// Rocq: Numbersetshard.numbersetshard_implem.union
// Variant: uncurried
pub fn union(par: Array<Int63>, rk: Array<Int63>, u: Int63, v: Int63) -> (Array<Int63>, Array<Int63>) {
  let rk_clone = Clone::clone(&rk);
  let tmp = find_1(par, rk_clone, u);
  match tmp {
    (v14, v16) => {
      let rk_clone_1 = Clone::clone(&rk);
      let tmp_1 = find_1(v16, rk_clone_1, v);
      match tmp_1 {
        (v28, v30) => {
          if v14 == v28 {
            (v30, rk)
          } else {
            let ku = rk.get_cloned(v14);
            let kv = rk.get_cloned(v28);
            if ku < kv {
              (v30.set(v14, v28), rk)
            } else {
              if kv < ku {
                (v30.set(v28, v14), rk)
              } else {
                (v30.set(v14, v28), rk.set(v28, kv + int63!(1)))
              }
            }
          }
        },
      }
    },
  }
}

// Rocq: Numbersetshard.numbersetshard_implem.ulink
// Variant: uncurried
pub fn ulink_1(par: Array<Int63>, rk: Array<Int63>, q: Int63, cnt: Int63, t: Int63, o: Int63) -> (Array<Int63>, Array<Int63>) {
  ulink(par, rk, q, cnt, t, o, ())
}

// Rocq: Numbersetshard.numbersetshard_implem.ulink (local: ulink)
// Variant: uncurried, lifted
pub fn ulink(par: Array<Int63>, rk: Array<Int63>, q: Int63, cnt: Int63, t: Int63, o: Int63, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = t < cnt;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = o + q;
      let tmp_2 = union(par, rk, o, tmp_1);
      match tmp_2 {
        (v35, v37) => {
          let tmp_3 = t + int63!(1);
          let tmp_4 = o + q;
          ulink(v35, v37, q, cnt, tmp_3, tmp_4, ())
        },
      }
    },
    sumbool::right => {
      (par, rk)
    },
  }
}

// Rocq: Numbersetshard.numbersetshard_implem.uprimes
// Variant: uncurried
pub fn uprimes_1(c: Array<bool>, a_1: Int63, w: Int63, n: Int63, par: Array<Int63>, rk: Array<Int63>, q: Int63) -> (Array<Int63>, Array<Int63>) {
  uprimes(c, a_1, w, n, par, rk, q, ())
}

// Rocq: Numbersetshard.numbersetshard_implem.uprimes (local: uprimes)
// Variant: uncurried, lifted
pub fn uprimes(c: Array<bool>, a_1: Int63, w: Int63, n: Int63, par: Array<Int63>, rk: Array<Int63>, q: Int63, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = q < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = c.get_cloned(q);
      let tmp_2 = if tmp_1 {
        (par, rk)
      } else {
        let o0 = first_off(a_1, q);
        let tmp_3 = (w - o0) / q;
        ulink_1(par, rk, q, tmp_3, int63!(0), o0)
      };
      match tmp_2 {
        (v70, v72) => {
          uprimes(c, a_1, w, n, v70, v72, q + int63!(1), ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(c);
      (par, rk)
    },
  }
}

// Rocq: Numbersetshard.numbersetshard_implem.count
// Variant: uncurried
pub fn count_1(par: Array<Int63>, n: Int63, o: Int63, acc: Int63) -> Int63 {
  count(par, n, o, acc, ())
}

// Rocq: Numbersetshard.numbersetshard_implem.count (local: count)
// Variant: uncurried, lifted
pub fn count(par: Array<Int63>, n: Int63, o: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = o < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = o + int63!(1);
      let tmp_2 = par.get_cloned(o);
      let tmp_3 = if tmp_2 == o {
        acc + int63!(1)
      } else {
        acc
      };
      count(par, n, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(par);
      acc
    },
  }
}

// Rocq: Numbersetshard.numbersetshard_implem.numbersets_impl
// Variant: uncurried
pub fn numbersets_impl(x: Int63, y: Int63, z: Int63) -> Int63 {
  let w = y - x;
  let n = w + int63!(1);
  let c = sieve_1(Array::<bool>::make(n, false), w, n, int63!(2));
  let par0 = iota_1(Array::<Int63>::make(n, int63!(0)), n, int63!(0));
  let rk0 = Array::<Int63>::make(n, int63!(0));
  let tmp = uprimes_1(c, x, w, n, par0, rk0, z);
  match tmp {
    (v77, v79) => {
      std::mem::drop(v79);
      count_1(v77, n, int63!(0), int63!(0))
    },
  }
}
