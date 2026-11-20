#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

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

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<std::cmp::Ordering>; };

pub struct tables {
  pub t_a1: Int63,
  pub t_nb: Int63,
  pub t_meta: Array<Int63>,
  pub t_slot: Array<Int63>,
}

impl Clone for tables {
  fn clone(&self) -> Self {
    match self {
      tables { t_a1: __field0, t_nb: __field1, t_meta: __field2, t_slot: __field3 } => tables { t_a1: Clone::clone(__field0), t_nb: Clone::clone(__field1), t_meta: Clone::clone(__field2), t_slot: Clone::clone(__field3) },
    }
  }
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type char63 = Int63;

// Rocq: Babelfish.babelfish_implem.prime
pub fn prime() -> Int63 {
  int63!(2147483647)
}

// Rocq: Babelfish.babelfish_implem.seed
pub fn seed() -> Int63 {
  int63!(88172645463325252)
}

// Rocq: Babelfish.babelfish_implem.rng_next
pub fn rng_next(st: Int63) -> Int63 {
  st * int63!(6364136223846793005) + int63!(1442695040888963407)
}

// Rocq: Babelfish.babelfish_implem.rng_draw
pub fn rng_draw(st: Int63) -> Int63 {
  (st >> int63!(17)) % (__rocq_global_95 - int63!(1)) + int63!(1)
}

// Rocq: Babelfish.babelfish_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: rocq_string::RocqString) -> Int63 {
  let tmp = v0.length();
  std::mem::drop(v0);
  tmp
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: rocq_string::RocqString, v1: Int63) -> Int63 {
  let tmp = v0.get(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Babelfish.babelfish_implem.hash_loop
// Variant: uncurried
pub fn hash_loop_1(a_1: Int63, s: rocq_string::RocqString, len: Int63, k: Int63, acc: Int63) -> Int63 {
  hash_loop(a_1, s, len, k, acc, ())
}

// Rocq: Babelfish.babelfish_implem.hash_loop (local: hash_loop)
// Variant: uncurried, lifted
pub fn hash_loop(a_1: Int63, s: rocq_string::RocqString, len: Int63, k: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = k < len;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = k + int63!(1);
      let tmp_2 = acc * a_1;
      let s_clone = Clone::clone(&s);
      hash_loop(a_1, s, len, tmp_1, (tmp_2 + get(s_clone, k) + int63!(1)) % __rocq_global_95, ())
    },
    sumbool::right => {
      std::mem::drop(s);
      acc
    },
  }
}

// Rocq: Babelfish.babelfish_implem.hash
// Variant: uncurried
pub fn hash(a_1: Int63, s: rocq_string::RocqString) -> Int63 {
  let s_clone = Clone::clone(&s);
  let len = length(s_clone);
  hash_loop_1(a_1, s, len, int63!(0), int63!(0))
}

// Rocq: Babelfish.babelfish_implem.count_loop
// Variant: uncurried
pub fn count_loop_1(a_1: Int63, nb: Int63, f: Array<rocq_string::RocqString>, n: Int63, i: Int63, cnt: Array<Int63>, bk: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  count_loop(a_1, nb, f, n, i, cnt, bk, ())
}

// Rocq: Babelfish.babelfish_implem.count_loop (local: count_loop)
// Variant: uncurried, lifted
pub fn count_loop(a_1: Int63, nb: Int63, f: Array<rocq_string::RocqString>, n: Int63, i: Int63, cnt: Array<Int63>, bk: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let f_ref = &f;
      let tmp_1 = f_ref.get_cloned(i);
      let b_1 = hash(a_1, tmp_1) % nb;
      let tmp_2 = i + int63!(1);
      let tmp_3 = cnt.get_cloned(b_1);
      count_loop(a_1, nb, f, n, tmp_2, cnt.set(b_1, tmp_3 + int63!(1)), bk.set(i, b_1), ())
    },
    sumbool::right => {
      std::mem::drop(f);
      (cnt, bk)
    },
  }
}

// Rocq: Babelfish.babelfish_implem.sumsq_loop
// Variant: uncurried
pub fn sumsq_loop_1(cnt: Array<Int63>, nb: Int63, b_1: Int63, acc: Int63) -> Int63 {
  sumsq_loop(cnt, nb, b_1, acc, ())
}

// Rocq: Babelfish.babelfish_implem.sumsq_loop (local: sumsq_loop)
// Variant: uncurried, lifted
pub fn sumsq_loop(cnt: Array<Int63>, nb: Int63, b_1: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = b_1 < nb;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = b_1 + int63!(1);
      let tmp_2 = cnt.get_cloned(b_1);
      let tmp_3 = cnt.get_cloned(b_1);
      sumsq_loop(cnt, nb, tmp_1, acc + tmp_2 * tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(cnt);
      acc
    },
  }
}

// Rocq: Babelfish.babelfish_implem.level1
// Variant: uncurried
pub fn level1_1(f: Array<rocq_string::RocqString>, n: Int63, nb: Int63, tries: Int63, t: Int63, st: Int63, bk: Array<Int63>) -> (((Int63, Int63), Array<Int63>), Array<Int63>) {
  level1(f, n, nb, tries, t, st, bk, ())
}

// Rocq: Babelfish.babelfish_implem.level1 (local: level1)
// Variant: uncurried, lifted
pub fn level1(f: Array<rocq_string::RocqString>, n: Int63, nb: Int63, tries: Int63, t: Int63, st: Int63, bk: Array<Int63>, _H: ()) -> (((Int63, Int63), Array<Int63>), Array<Int63>) {
  let st_ = rng_next(st);
  let a_1 = rng_draw(st_);
  let tmp = Array::<Int63>::make(nb, int63!(0));
  let f_clone = Clone::clone(&f);
  let tmp_1 = count_loop_1(a_1, nb, f_clone, n, int63!(0), tmp, bk);
  match tmp_1 {
    (v43, v45) => {
      let bk_ = &v43;
      let tmp_2 = t < tries;
      match bdec(tmp_2) {
        sumbool::left => {
          let bk__clone = Clone::clone(bk_);
          let tmp_3 = sumsq_loop_1(bk__clone, nb, int63!(0), int63!(0));
          let tmp_4 = int63!(4) * n;
          if tmp_3 <= tmp_4 {
            std::mem::drop(f);
            (((a_1, st_), v43), v45)
          } else {
            std::mem::drop(v43);
            level1(f, n, nb, tries, t + int63!(1), st_, v45, ())
          }
        },
        sumbool::right => {
          std::mem::drop(f);
          (((a_1, st_), v43), v45)
        },
      }
    },
  }
}

// Rocq: Babelfish.babelfish_implem.layout_loop
// Variant: uncurried
pub fn layout_loop_1(cnt: Array<Int63>, nb: Int63, b_1: Int63, off: Int63, st: Int63, meta: Array<Int63>, cur: Array<Int63>) -> ((Array<Int63>, Array<Int63>), Int63) {
  layout_loop(cnt, nb, b_1, off, st, meta, cur, ())
}

// Rocq: Babelfish.babelfish_implem.layout_loop (local: layout_loop)
// Variant: uncurried, lifted
pub fn layout_loop(cnt: Array<Int63>, nb: Int63, b_1: Int63, off: Int63, st: Int63, meta: Array<Int63>, cur: Array<Int63>, _H: ()) -> ((Array<Int63>, Array<Int63>), Int63) {
  let tmp = b_1 < nb;
  match bdec(tmp) {
    sumbool::left => {
      let c = cnt.get_cloned(b_1);
      layout_loop(cnt, nb, b_1 + int63!(1), off + c * c, st + c, meta.set(int63!(3) * b_1, off).set(int63!(3) * b_1 + int63!(1), c * c), cur.set(b_1, st), ())
    },
    sumbool::right => {
      std::mem::drop(cnt);
      ((meta, cur), off)
    },
  }
}

// Rocq: Babelfish.babelfish_implem.distribute
// Variant: uncurried
pub fn distribute_1(bk: Array<Int63>, n: Int63, i: Int63, cur: Array<Int63>, order: Array<Int63>) -> Array<Int63> {
  distribute(bk, n, i, cur, order, ())
}

// Rocq: Babelfish.babelfish_implem.distribute (local: distribute)
// Variant: uncurried, lifted
pub fn distribute(bk: Array<Int63>, n: Int63, i: Int63, cur: Array<Int63>, order: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let b_1 = bk.get_cloned(i);
      let p = cur.get_cloned(b_1);
      distribute(bk, n, i + int63!(1), cur.set(b_1, p + int63!(1)), order.set(p, i), ())
    },
    sumbool::right => {
      std::mem::drop(bk);
      std::mem::drop(cur);
      order
    },
  }
}

// Rocq: Babelfish.babelfish_implem.place_loop
// Variant: uncurried
pub fn place_loop_1(f: Array<rocq_string::RocqString>, order: Array<Int63>, a_1: Int63, off: Int63, sz: Int63, e: Int63, i: Int63, slot: Array<Int63>) -> (Array<Int63>, bool) {
  place_loop(f, order, a_1, off, sz, e, i, slot, ())
}

// Rocq: Babelfish.babelfish_implem.place_loop (local: place_loop)
// Variant: uncurried, lifted
pub fn place_loop(f: Array<rocq_string::RocqString>, order: Array<Int63>, a_1: Int63, off: Int63, sz: Int63, e: Int63, i: Int63, slot: Array<Int63>, _H: ()) -> (Array<Int63>, bool) {
  let tmp = i < e;
  match bdec(tmp) {
    sumbool::left => {
      let k = order.get_cloned(i);
      let f_ref = &f;
      let tmp_1 = f_ref.get_cloned(k);
      let s = off + hash(a_1, tmp_1) % sz;
      let tmp_2 = slot.get_cloned(s);
      if tmp_2 == int63!(0) {
        place_loop(f, order, a_1, off, sz, e, i + int63!(1), slot.set(s, k + int63!(1)), ())
      } else {
        std::mem::drop(order);
        std::mem::drop(f);
        (slot, false)
      }
    },
    sumbool::right => {
      std::mem::drop(f);
      std::mem::drop(order);
      (slot, true)
    },
  }
}

// Rocq: Babelfish.babelfish_implem.clear_loop
// Variant: uncurried
pub fn clear_loop_1(e: Int63, i: Int63, slot: Array<Int63>) -> Array<Int63> {
  clear_loop(e, i, slot, ())
}

// Rocq: Babelfish.babelfish_implem.clear_loop (local: clear_loop)
// Variant: uncurried, lifted
pub fn clear_loop(e: Int63, i: Int63, slot: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < e;
  match bdec(tmp) {
    sumbool::left => {
      clear_loop(e, i + int63!(1), slot.set(i, int63!(0)), ())
    },
    sumbool::right => {
      slot
    },
  }
}

// Rocq: Babelfish.babelfish_implem.level2
// Variant: uncurried
pub fn level2_1(f: Array<rocq_string::RocqString>, order: Array<Int63>, st: Int63, c: Int63, off: Int63, sz: Int63, tries: Int63, t: Int63, rng: Int63, slot: Array<Int63>) -> ((Array<Int63>, Int63), Int63) {
  level2(f, order, st, c, off, sz, tries, t, rng, slot, ())
}

// Rocq: Babelfish.babelfish_implem.level2 (local: level2)
// Variant: uncurried, lifted
pub fn level2(f: Array<rocq_string::RocqString>, order: Array<Int63>, st: Int63, c: Int63, off: Int63, sz: Int63, tries: Int63, t: Int63, rng: Int63, slot: Array<Int63>, _H: ()) -> ((Array<Int63>, Int63), Int63) {
  let rng_ = rng_next(rng);
  let a_1 = rng_draw(rng_);
  let tmp = st + c;
  let f_clone = Clone::clone(&f);
  let order_clone = Clone::clone(&order);
  let tmp_1 = place_loop_1(f_clone, order_clone, a_1, off, sz, tmp, st, slot);
  match tmp_1 {
    (v46, v48) => {
      if v48 {
        std::mem::drop(f);
        std::mem::drop(order);
        ((v46, a_1), rng_)
      } else {
        let tmp_2 = t < tries;
        match bdec(tmp_2) {
          sumbool::left => {
            let tmp_3 = t + int63!(1);
            let tmp_4 = clear_loop_1(off + sz, off, v46);
            level2(f, order, st, c, off, sz, tries, tmp_3, rng_, tmp_4, ())
          },
          sumbool::right => {
            std::mem::drop(f);
            std::mem::drop(order);
            ((v46, a_1), rng_)
          },
        }
      }
    },
  }
}

// Rocq: Babelfish.babelfish_implem.buckets_loop
// Variant: uncurried
pub fn buckets_loop_1(f: Array<rocq_string::RocqString>, order: Array<Int63>, cnt: Array<Int63>, nb: Int63, b_1: Int63, st: Int63, rng: Int63, meta: Array<Int63>, slot: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  buckets_loop(f, order, cnt, nb, b_1, st, rng, meta, slot, ())
}

// Rocq: Babelfish.babelfish_implem.buckets_loop (local: buckets_loop)
// Variant: uncurried, lifted
pub fn buckets_loop(f: Array<rocq_string::RocqString>, order: Array<Int63>, cnt: Array<Int63>, nb: Int63, b_1: Int63, st: Int63, rng: Int63, meta: Array<Int63>, slot: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = b_1 < nb;
  match bdec(tmp) {
    sumbool::left => {
      let c = cnt.get_cloned(b_1);
      if c == int63!(0) {
        buckets_loop(f, order, cnt, nb, b_1 + int63!(1), st, rng, meta, slot, ())
      } else {
        let off = meta.get_cloned(int63!(3) * b_1);
        let sz = meta.get_cloned(int63!(3) * b_1 + int63!(1));
        let f_clone = Clone::clone(&f);
        let order_clone = Clone::clone(&order);
        let tmp_1 = level2_1(f_clone, order_clone, st, c, off, sz, int63!(64), int63!(0), rng, slot);
        match tmp_1 {
          (v130, v132) => {
            match v130 {
              (v135, v137) => {
                buckets_loop(f, order, cnt, nb, b_1 + int63!(1), st + c, v132, meta.set(int63!(3) * b_1 + int63!(2), v137), v135, ())
              },
            }
          },
        }
      }
    },
    sumbool::right => {
      std::mem::drop(f);
      std::mem::drop(order);
      std::mem::drop(cnt);
      (meta, slot)
    },
  }
}

// Rocq: Babelfish.babelfish_implem.build
// Variant: uncurried
pub fn build(f: Array<rocq_string::RocqString>, n: Int63) -> Rc<tables> {
  let tmp = int63!(0);
  let nb = if n == tmp {
    int63!(1)
  } else {
    n
  };
  let tmp_1 = Array::<Int63>::make(n, int63!(0));
  let f_clone = Clone::clone(&f);
  let tmp_2 = level1_1(f_clone, n, nb, int63!(32), int63!(0), __rocq_global_460, tmp_1);
  match tmp_2 {
    (v48, v50) => {
      match v48 {
        (v53, v55) => {
          let p0 = &v55;
          match v53 {
            (v59, v61) => {
              let tmp_3 = Array::<Int63>::make(int63!(3) * nb, int63!(0));
              let tmp_4 = Array::<Int63>::make(nb, int63!(0));
              let p0_clone = Clone::clone(p0);
              let tmp_5 = layout_loop_1(p0_clone, nb, int63!(0), int63!(0), int63!(0), tmp_3, tmp_4);
              match tmp_5 {
                (v108, v110) => {
                  match v108 {
                    (v113, v115) => {
                      let tmp_6 = Array::<Int63>::make(n, int63!(0));
                      let order = distribute_1(v50, n, int63!(0), v115, tmp_6);
                      let tmp_7 = buckets_loop_1(f, order, v55, nb, int63!(0), int63!(0), v61, v113, Array::<Int63>::make(v110, int63!(0)));
                      match tmp_7 {
                        (v170, v172) => {
                          Rc::new(tables { t_a1: v59, t_nb: nb, t_meta: v170, t_slot: v172 })
                        },
                      }
                    },
                  }
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Babelfish.babelfish_implem.t_slot
pub fn t_slot(t: Rc<tables>) -> Array<Int63> {
  let t_t_slot_clone = Clone::clone(&t.t_slot);
  std::mem::drop(t);
  t_t_slot_clone
}

// Rocq: Babelfish.babelfish_implem.t_meta
pub fn t_meta(t: Rc<tables>) -> Array<Int63> {
  let t_t_meta_clone = Clone::clone(&t.t_meta);
  std::mem::drop(t);
  t_t_meta_clone
}

// Rocq: Babelfish.babelfish_implem.t_a1
// Variant: borrowed
pub fn t_a1(t: &Rc<tables>) -> Int63 {
  let tmp = t;
  Clone::clone(&tmp.t_a1)
}

// Rocq: Babelfish.babelfish_implem.t_nb
// Variant: borrowed
pub fn t_nb(t: &Rc<tables>) -> Int63 {
  let tmp = t;
  Clone::clone(&tmp.t_nb)
}

// Rocq: Babelfish.babelfish_implem.pos
// Variant: uncurried
pub fn pos(t: Rc<tables>, x: rocq_string::RocqString) -> Int63 {
  let t_clone = Rc::clone(&t);
  let meta = t_meta(t_clone);
  let tmp = t_a1(&t);
  let x_clone = Clone::clone(&x);
  let b_1 = hash(tmp, x_clone) % t_nb(&t);
  let sz = meta.get_cloned(int63!(3) * b_1 + int63!(1));
  if sz == int63!(0) {
    std::mem::drop(x);
    std::mem::drop(meta);
    let tmp_1 = t_slot(t);
    let tmp_2 = tmp_1.length();
    std::mem::drop(tmp_1);
    tmp_2
  } else {
    std::mem::drop(t);
    let tmp_3 = meta.get_cloned(int63!(3) * b_1);
    let tmp_4 = meta.get_cloned(int63!(3) * b_1 + int63!(2));
    std::mem::drop(meta);
    tmp_3 + hash(tmp_4, x) % sz
  }
}

// Rocq: Babelfish.babelfish_implem.check_loop
// Variant: uncurried
pub fn check_loop_1(t: Rc<tables>, f: Array<rocq_string::RocqString>, n: Int63, i: Int63) -> bool {
  check_loop(t, f, n, i, ())
}

// Rocq: Babelfish.babelfish_implem.check_loop (local: check_loop)
// Variant: uncurried, lifted
pub fn check_loop(t: Rc<tables>, f: Array<rocq_string::RocqString>, n: Int63, i: Int63, _H: ()) -> bool {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let t_clone = Rc::clone(&t);
      let tmp_1 = t_slot(t_clone);
      let f_ref = &f;
      let tmp_2 = f_ref.get_cloned(i);
      let t_clone_1 = Rc::clone(&t);
      let tmp_3 = tmp_1.get_cloned(pos(t_clone_1, tmp_2));
      let tmp_4 = i + int63!(1);
      if tmp_3 == tmp_4 {
        std::mem::drop(tmp_1);
        check_loop(t, f, n, i + int63!(1), ())
      } else {
        std::mem::drop(t);
        std::mem::drop(f);
        std::mem::drop(tmp_1);
        false
      }
    },
    sumbool::right => {
      std::mem::drop(t);
      std::mem::drop(f);
      true
    },
  }
}

// Rocq: Corelib.Strings.PrimString.compare
// Variant: uncurried
pub fn compare(v0: rocq_string::RocqString, v1: rocq_string::RocqString) -> std::cmp::Ordering {
  let tmp = v0.compare(&v1);
  std::mem::drop(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Babelfish.babelfish_implem.scan_loop
// Variant: uncurried
pub fn scan_loop_1(f: Array<rocq_string::RocqString>, x: rocq_string::RocqString, n: Int63, i: Int63) -> Int63 {
  scan_loop(f, x, n, i, ())
}

// Rocq: Babelfish.babelfish_implem.scan_loop (local: scan_loop)
// Variant: uncurried, lifted
pub fn scan_loop(f: Array<rocq_string::RocqString>, x: rocq_string::RocqString, n: Int63, i: Int63, _H: ()) -> Int63 {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let f_ref = &f;
      let tmp_1 = f_ref.get_cloned(i);
      let x_clone = Clone::clone(&x);
      match compare(tmp_1, x_clone) {
        std::cmp::Ordering::Equal => {
          std::mem::drop(f);
          std::mem::drop(x);
          i
        },
        std::cmp::Ordering::Less => {
          scan_loop(f, x, n, i + int63!(1), ())
        },
        std::cmp::Ordering::Greater => {
          scan_loop(f, x, n, i + int63!(1), ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(f);
      std::mem::drop(x);
      n
    },
  }
}

// Rocq: Babelfish.babelfish_implem.query
// Variant: uncurried
pub fn query(e: Array<rocq_string::RocqString>, f: Array<rocq_string::RocqString>, n: Int63, ok: bool, t: Rc<tables>, x: rocq_string::RocqString) -> Rc<option<rocq_string::RocqString>> {
  let i = if ok {
    let t_clone = Rc::clone(&t);
    let tmp = t_slot(t_clone);
    let x_clone = Clone::clone(&x);
    let tmp_1 = tmp.get_cloned(pos(t, x_clone));
    std::mem::drop(tmp);
    tmp_1 - int63!(1)
  } else {
    std::mem::drop(t);
    let f_clone = Clone::clone(&f);
    let x_clone_1 = Clone::clone(&x);
    scan_loop_1(f_clone, x_clone_1, n, int63!(0))
  };
  if i < n {
    let f_ref = &f;
    let tmp_2 = f_ref.get_cloned(i);
    match compare(tmp_2, x) {
      std::cmp::Ordering::Equal => {
        std::mem::drop(f);
        let e_ref = &e;
        let tmp_3 = e_ref.get_cloned(i);
        std::mem::drop(e);
        Rc::new(option::<rocq_string::RocqString>::Some(tmp_3))
      },
      std::cmp::Ordering::Less => {
        std::mem::drop(e);
        std::mem::drop(f);
        Rc::new(option::<rocq_string::RocqString>::None)
      },
      std::cmp::Ordering::Greater => {
        std::mem::drop(e);
        std::mem::drop(f);
        Rc::new(option::<rocq_string::RocqString>::None)
      },
    }
  } else {
    std::mem::drop(e);
    std::mem::drop(f);
    std::mem::drop(x);
    Rc::new(option::<rocq_string::RocqString>::None)
  }
}

// Rocq: Babelfish.babelfish_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(e: Array<rocq_string::RocqString>, f: Array<rocq_string::RocqString>, m: Array<rocq_string::RocqString>, n: Int63, ok: bool, t: Rc<tables>, L: Int63, k: Int63, out: Array<Rc<option<rocq_string::RocqString>>>) -> Array<Rc<option<rocq_string::RocqString>>> {
  fill_loop(e, f, m, n, ok, t, L, k, out, ())
}

// Rocq: Babelfish.babelfish_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(e: Array<rocq_string::RocqString>, f: Array<rocq_string::RocqString>, m: Array<rocq_string::RocqString>, n: Int63, ok: bool, t: Rc<tables>, L: Int63, k: Int63, out: Array<Rc<option<rocq_string::RocqString>>>, _H: ()) -> Array<Rc<option<rocq_string::RocqString>>> {
  let tmp = k < L;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = k + int63!(1);
      let m_ref = &m;
      let tmp_2 = m_ref.get_cloned(k);
      let e_clone = Clone::clone(&e);
      let f_clone = Clone::clone(&f);
      let t_clone = Rc::clone(&t);
      let tmp_3 = query(e_clone, f_clone, n, ok, t_clone, tmp_2);
      fill_loop(e, f, m, n, ok, t, L, tmp_1, out.set(k, tmp_3), ())
    },
    sumbool::right => {
      std::mem::drop(e);
      std::mem::drop(f);
      std::mem::drop(m);
      std::mem::drop(t);
      out
    },
  }
}

// Rocq: Babelfish.babelfish_implem.babelfish_impl
// Variant: uncurried
pub fn babelfish_impl(e: Array<rocq_string::RocqString>, f: Array<rocq_string::RocqString>, m: Array<rocq_string::RocqString>) -> Array<Rc<option<rocq_string::RocqString>>> {
  let n = f.length();
  let f_clone = Clone::clone(&f);
  let t = build(f_clone, n);
  let t_clone = Rc::clone(&t);
  let f_clone_1 = Clone::clone(&f);
  let ok = check_loop_1(t_clone, f_clone_1, n, int63!(0));
  let L = m.length();
  let tmp = Array::<Rc<option<rocq_string::RocqString>>>::make(L, Rc::new(option::<rocq_string::RocqString>::None));
  fill_loop_1(e, f, m, n, ok, t, L, int63!(0), tmp)
}
const __rocq_global_95: Int63 = int63!(2147483647);
const __rocq_global_460: Int63 = int63!(88172645463325252);