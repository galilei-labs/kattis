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

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<std::cmp::Ordering>; };

pub struct tables {
  pub t_a1: u64,
  pub t_nb: u64,
  pub t_meta: Rc<Array<u64>>,
  pub t_slot: Rc<Array<u64>>,
}

impl Clone for tables {
  fn clone(&self) -> Self {
    match self {
      tables { t_a1: __field0, t_nb: __field1, t_meta: __field2, t_slot: __field3 } => tables { t_a1: Clone::clone(__field0), t_nb: Clone::clone(__field1), t_meta: Clone::clone(__field2), t_slot: Clone::clone(__field3) },
    }
  }
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type char63 = u64;

// Rocq: Babelfish.babelfish_implem.prime
pub fn prime() -> u64 {
  2147483647u64
}

// Rocq: Babelfish.babelfish_implem.seed
pub fn seed() -> u64 {
  88172645463325252u64
}

// Rocq: Babelfish.babelfish_implem.babelfish
// Variant: uncurried
pub fn babelfish() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>>> {
  let v0: fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>> = babelfish_impl;
  let v1: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>>> = Rc::new(v0);
  v1
}

// Rocq: Babelfish.babelfish_implem.babelfish
pub fn babelfish_curried() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>>>>> {
  let v0: fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>>>> = babelfish_impl_curried;
  let v1: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsr
// Variant: uncurried
pub fn lsr(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsr(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Babelfish.babelfish_implem.rng_next
pub fn rng_next(st: u64) -> u64 {
  add(mul(st, 6364136223846793005u64), 1442695040888963407u64)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Babelfish.babelfish_implem.rng_draw
pub fn rng_draw(st: u64) -> u64 {
  add(mod_(lsr(st, 17u64), sub(__rocq_global_95, 1u64)), 1u64)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Babelfish.babelfish_implem.bdec
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

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: Rc<rocq_string::RocqString>) -> u64 {
  let v2 = rocq_string::length(&v0);
  std::mem::drop(v0);
  v2
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let v5 = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  v5
}

// Rocq: Babelfish.babelfish_implem.hash_loop
// Variant: uncurried
pub fn hash_loop_1(a: u64, s: Rc<rocq_string::RocqString>, len: u64, k: u64, acc: u64) -> u64 {
  hash_loop(a, s, len, k, acc, ())
}

// Rocq: Babelfish.babelfish_implem.hash_loop (local: hash_loop)
// Variant: uncurried, lifted
pub fn hash_loop(a: u64, s: Rc<rocq_string::RocqString>, len: u64, k: u64, acc: u64, _H: ()) -> u64 {
  let v13 = ltb(k, len);
  match bdec(v13) {
    sumbool::left => {
      let v24 = add(k, 1u64);
      let v33 = mul(acc, a);
      let v37 = Rc::clone(&s);
      let v45 = add(v33, get(v37, k));
      hash_loop(a, s, len, v24, mod_(add(v45, 1u64), __rocq_global_95), ())
    },
    sumbool::right => {
      std::mem::drop(s);
      acc
    },
  }
}

// Rocq: Babelfish.babelfish_implem.hash
// Variant: uncurried
pub fn hash(a: u64, s: Rc<rocq_string::RocqString>) -> u64 {
  let v5 = Rc::clone(&s);
  let len = length(v5);
  hash_loop_1(a, s, len, 0u64, 0u64)
}

// Rocq: Babelfish.babelfish_implem.count_loop
// Variant: uncurried
pub fn count_loop_1(a: u64, nb: u64, f: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, i: u64, cnt: Rc<Array<u64>>, bk: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  count_loop(a, nb, f, n, i, cnt, bk, ())
}

// Rocq: Babelfish.babelfish_implem.count_loop (local: count_loop)
// Variant: uncurried, lifted
pub fn count_loop(a: u64, nb: u64, f: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, i: u64, cnt: Rc<Array<u64>>, bk: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v15 = ltb(i, n);
  match bdec(v15) {
    sumbool::left => {
      let v21 = &f;
      let v24 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v21, i);
      let b = mod_(hash(a, v24), nb);
      let v42 = add(i, 1u64);
      let v44 = &cnt;
      let v47 = rocq_array::get::<u64>(&v44, b);
      let v61 = rocq_array::set::<u64>(cnt, b, add(v47, 1u64));
      let v68 = rocq_array::set::<u64>(bk, i, b);
      count_loop(a, nb, f, n, v42, v61, v68, ())
    },
    sumbool::right => {
      std::mem::drop(f);
      (cnt, bk)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Babelfish.babelfish_implem.sumsq_loop
// Variant: uncurried
pub fn sumsq_loop_1(cnt: Rc<Array<u64>>, nb: u64, b: u64, acc: u64) -> u64 {
  sumsq_loop(cnt, nb, b, acc, ())
}

// Rocq: Babelfish.babelfish_implem.sumsq_loop (local: sumsq_loop)
// Variant: uncurried, lifted
pub fn sumsq_loop(cnt: Rc<Array<u64>>, nb: u64, b: u64, acc: u64, _H: ()) -> u64 {
  let v12 = ltb(b, nb);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(b, 1u64);
      let v26 = &cnt;
      let v29 = rocq_array::get::<u64>(&v26, b);
      let v30 = &cnt;
      let v33 = rocq_array::get::<u64>(&v30, b);
      sumsq_loop(cnt, nb, v23, add(acc, mul(v29, v33)), ())
    },
    sumbool::right => {
      std::mem::drop(cnt);
      acc
    },
  }
}

// Rocq: Babelfish.babelfish_implem.level1
// Variant: uncurried
pub fn level1_1(f: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, nb: u64, tries: u64, t: u64, st: u64, bk: Rc<Array<u64>>) -> (((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>) {
  level1(f, n, nb, tries, t, st, bk, ())
}

// Rocq: Babelfish.babelfish_implem.level1 (local: level1)
// Variant: uncurried, lifted
pub fn level1(f: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, nb: u64, tries: u64, t: u64, st: u64, bk: Rc<Array<u64>>, _H: ()) -> (((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>) {
  let st_ = rng_next(st);
  let a = rng_draw(st_);
  let v25 = rocq_array::make::<u64>(nb, 0u64);
  let v32 = Rc::clone(&f);
  let v41 = count_loop_1(a, nb, v32, n, 0u64, v25, bk);
  match v41 {
    (v43, v45) => {
      let bk_ = &v43;
      let v55 = ltb(t, tries);
      match bdec(v55) {
        sumbool::left => {
          let v66 = Rc::clone(bk_);
          let v73 = sumsq_loop_1(v66, nb, 0u64, 0u64);
          let v81 = mul(4u64, n);
          match leb(v73, v81) {
            true => {
              std::mem::drop(f);
              (((a, st_), v43), v45)
            },
            false => {
              std::mem::drop(v43);
              level1(f, n, nb, tries, add(t, 1u64), st_, v45, ())
            },
          }
        },
        sumbool::right => {
          std::mem::drop(f);
          (((a, st_), v43), v45)
        },
      }
    },
  }
}

// Rocq: Babelfish.babelfish_implem.layout_loop
// Variant: uncurried
pub fn layout_loop_1(cnt: Rc<Array<u64>>, nb: u64, b: u64, off: u64, st: u64, meta: Rc<Array<u64>>, cur: Rc<Array<u64>>) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  layout_loop(cnt, nb, b, off, st, meta, cur, ())
}

// Rocq: Babelfish.babelfish_implem.layout_loop (local: layout_loop)
// Variant: uncurried, lifted
pub fn layout_loop(cnt: Rc<Array<u64>>, nb: u64, b: u64, off: u64, st: u64, meta: Rc<Array<u64>>, cur: Rc<Array<u64>>, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let v15 = ltb(b, nb);
  match bdec(v15) {
    sumbool::left => {
      let v19 = &cnt;
      let c = rocq_array::get::<u64>(&v19, b);
      let v30 = add(b, 1u64);
      let v42 = add(off, mul(c, c));
      let v48 = add(st, c);
      let v63 = rocq_array::set::<u64>(meta, mul(3u64, b), off);
      let v92 = rocq_array::set::<u64>(v63, add(mul(3u64, b), 1u64), mul(c, c));
      let v99 = rocq_array::set::<u64>(cur, b, st);
      layout_loop(cnt, nb, v30, v42, v48, v92, v99, ())
    },
    sumbool::right => {
      std::mem::drop(cnt);
      ((meta, cur), off)
    },
  }
}

// Rocq: Babelfish.babelfish_implem.distribute
// Variant: uncurried
pub fn distribute_1(bk: Rc<Array<u64>>, n: u64, i: u64, cur: Rc<Array<u64>>, order: Rc<Array<u64>>) -> Rc<Array<u64>> {
  distribute(bk, n, i, cur, order, ())
}

// Rocq: Babelfish.babelfish_implem.distribute (local: distribute)
// Variant: uncurried, lifted
pub fn distribute(bk: Rc<Array<u64>>, n: u64, i: u64, cur: Rc<Array<u64>>, order: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v13 = ltb(i, n);
  match bdec(v13) {
    sumbool::left => {
      let v17 = &bk;
      let b = rocq_array::get::<u64>(&v17, i);
      let v21 = &cur;
      let p = rocq_array::get::<u64>(&v21, b);
      let v32 = add(i, 1u64);
      let v47 = rocq_array::set::<u64>(cur, b, add(p, 1u64));
      let v54 = rocq_array::set::<u64>(order, p, i);
      distribute(bk, n, v32, v47, v54, ())
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
pub fn place_loop_1(f: Rc<Array<Rc<rocq_string::RocqString>>>, order: Rc<Array<u64>>, a: u64, off: u64, sz: u64, e: u64, i: u64, slot: Rc<Array<u64>>) -> (Rc<Array<u64>>, bool) {
  place_loop(f, order, a, off, sz, e, i, slot, ())
}

// Rocq: Babelfish.babelfish_implem.place_loop (local: place_loop)
// Variant: uncurried, lifted
pub fn place_loop(f: Rc<Array<Rc<rocq_string::RocqString>>>, order: Rc<Array<u64>>, a: u64, off: u64, sz: u64, e: u64, i: u64, slot: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, bool) {
  let v16 = ltb(i, e);
  match bdec(v16) {
    sumbool::left => {
      let v20 = &order;
      let k = rocq_array::get::<u64>(&v20, i);
      let v27 = &f;
      let v30 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v27, k);
      let s = add(off, mod_(hash(a, v30), sz));
      let v47 = &slot;
      let v50 = rocq_array::get::<u64>(&v47, s);
      match eqb(v50, 0u64) {
        true => {
          let v66 = add(i, 1u64);
          let v81 = rocq_array::set::<u64>(slot, s, add(k, 1u64));
          place_loop(f, order, a, off, sz, e, v66, v81, ())
        },
        false => {
          std::mem::drop(order);
          std::mem::drop(f);
          (slot, false)
        },
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
pub fn clear_loop_1(e: u64, i: u64, slot: Rc<Array<u64>>) -> Rc<Array<u64>> {
  clear_loop(e, i, slot, ())
}

// Rocq: Babelfish.babelfish_implem.clear_loop (local: clear_loop)
// Variant: uncurried, lifted
pub fn clear_loop(e: u64, i: u64, slot: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v11 = ltb(i, e);
  match bdec(v11) {
    sumbool::left => {
      let v22 = add(i, 1u64);
      let v31 = rocq_array::set::<u64>(slot, i, 0u64);
      clear_loop(e, v22, v31, ())
    },
    sumbool::right => {
      slot
    },
  }
}

// Rocq: Babelfish.babelfish_implem.level2
// Variant: uncurried
pub fn level2_1(f: Rc<Array<Rc<rocq_string::RocqString>>>, order: Rc<Array<u64>>, st: u64, c: u64, off: u64, sz: u64, tries: u64, t: u64, rng: u64, slot: Rc<Array<u64>>) -> ((Rc<Array<u64>>, u64), u64) {
  level2(f, order, st, c, off, sz, tries, t, rng, slot, ())
}

// Rocq: Babelfish.babelfish_implem.level2 (local: level2)
// Variant: uncurried, lifted
pub fn level2(f: Rc<Array<Rc<rocq_string::RocqString>>>, order: Rc<Array<u64>>, st: u64, c: u64, off: u64, sz: u64, tries: u64, t: u64, rng: u64, slot: Rc<Array<u64>>, _H: ()) -> ((Rc<Array<u64>>, u64), u64) {
  let rng_ = rng_next(rng);
  let a = rng_draw(rng_);
  let v25 = add(st, c);
  let v28 = Rc::clone(&f);
  let v31 = Rc::clone(&order);
  let v44 = place_loop_1(v28, v31, a, off, sz, v25, st, slot);
  match v44 {
    (v46, v48) => {
      match v48 {
        true => {
          std::mem::drop(f);
          std::mem::drop(order);
          ((v46, a), rng_)
        },
        false => {
          let v72 = ltb(t, tries);
          match bdec(v72) {
            sumbool::left => {
              let v83 = add(t, 1u64);
              let v97 = clear_loop_1(add(off, sz), off, v46);
              level2(f, order, st, c, off, sz, tries, v83, rng_, v97, ())
            },
            sumbool::right => {
              std::mem::drop(f);
              std::mem::drop(order);
              ((v46, a), rng_)
            },
          }
        },
      }
    },
  }
}

// Rocq: Babelfish.babelfish_implem.buckets_loop
// Variant: uncurried
pub fn buckets_loop_1(f: Rc<Array<Rc<rocq_string::RocqString>>>, order: Rc<Array<u64>>, cnt: Rc<Array<u64>>, nb: u64, b: u64, st: u64, rng: u64, meta: Rc<Array<u64>>, slot: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  buckets_loop(f, order, cnt, nb, b, st, rng, meta, slot, ())
}

// Rocq: Babelfish.babelfish_implem.buckets_loop (local: buckets_loop)
// Variant: uncurried, lifted
pub fn buckets_loop(f: Rc<Array<Rc<rocq_string::RocqString>>>, order: Rc<Array<u64>>, cnt: Rc<Array<u64>>, nb: u64, b: u64, st: u64, rng: u64, meta: Rc<Array<u64>>, slot: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v17 = ltb(b, nb);
  match bdec(v17) {
    sumbool::left => {
      let v21 = &cnt;
      let c = rocq_array::get::<u64>(&v21, b);
      let v32 = eqb(c, 0u64);
      match &v32 {
        true => {
          buckets_loop(f, order, cnt, nb, add(b, 1u64), st, rng, meta, slot, ())
        },
        false => {
          let v76 = mul(3u64, b);
          let v77 = &meta;
          let off = rocq_array::get::<u64>(&v77, v76);
          let v96 = add(mul(3u64, b), 1u64);
          let v97 = &meta;
          let sz = rocq_array::get::<u64>(&v97, v96);
          let v108 = Rc::clone(&f);
          let v111 = Rc::clone(&order);
          let v128 = level2_1(v108, v111, st, c, off, sz, 64u64, 0u64, rng, slot);
          match v128 {
            (v130, v132) => {
              match v130 {
                (v135, v137) => {
                  let v146 = add(b, 1u64);
                  let v152 = add(st, c);
                  let v175 = rocq_array::set::<u64>(meta, add(mul(3u64, b), 2u64), v137);
                  buckets_loop(f, order, cnt, nb, v146, v152, v132, v175, v135, ())
                },
              }
            },
          }
        },
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
pub fn build(f: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64) -> Rc<tables> {
  let v4 = 0u64;
  let nb = match eqb(n, v4) {
    true => {
      1u64
    },
    false => {
      n
    },
  };
  let v30 = rocq_array::make::<u64>(n, 0u64);
  let v33 = Rc::clone(&f);
  let v46 = level1_1(v33, n, nb, 32u64, 0u64, __rocq_global_460, v30);
  match v46 {
    (v48, v50) => {
      match v48 {
        (v53, v55) => {
          let p0 = &v55;
          match v53 {
            (v59, v61) => {
              let v84 = rocq_array::make::<u64>(mul(3u64, nb), 0u64);
              let v91 = rocq_array::make::<u64>(nb, 0u64);
              let v93 = Rc::clone(p0);
              let v106 = layout_loop_1(v93, nb, 0u64, 0u64, 0u64, v84, v91);
              match v106 {
                (v108, v110) => {
                  match v108 {
                    (v113, v115) => {
                      let v126 = rocq_array::make::<u64>(n, 0u64);
                      let order = distribute_1(v50, n, 0u64, v115, v126);
                      let v149 = rocq_array::make::<u64>(v110, 0u64);
                      let v168 = buckets_loop_1(f, order, v55, nb, 0u64, 0u64, v61, v113, v149);
                      match v168 {
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
pub fn t_slot(t: Rc<tables>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).t_slot));
  std::mem::drop(t);
  v3
}

// Rocq: Babelfish.babelfish_implem.t_meta
pub fn t_meta(t: Rc<tables>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).t_meta));
  std::mem::drop(t);
  v3
}

// Rocq: Babelfish.babelfish_implem.t_a1
// Variant: borrowed
pub fn t_a1(t: &Rc<tables>) -> u64 {
  let v1 = t;
  Clone::clone((&(&**v1).t_a1))
}

// Rocq: Babelfish.babelfish_implem.t_nb
// Variant: borrowed
pub fn t_nb(t: &Rc<tables>) -> u64 {
  let v1 = t;
  Clone::clone((&(&**v1).t_nb))
}

// Rocq: Babelfish.babelfish_implem.pos
// Variant: uncurried
pub fn pos(t: Rc<tables>, x: Rc<rocq_string::RocqString>) -> u64 {
  let v5 = Rc::clone(&t);
  let meta = t_meta(v5);
  let v13 = t_a1(&t);
  let v17 = Rc::clone(&x);
  let b = mod_(hash(v13, v17), t_nb(&t));
  let v43 = add(mul(3u64, b), 1u64);
  let v44 = &meta;
  let sz = rocq_array::get::<u64>(&v44, v43);
  match eqb(sz, 0u64) {
    true => {
      std::mem::drop(x);
      std::mem::drop(meta);
      let v60 = t_slot(t);
      let v61 = &v60;
      let v62 = rocq_array::length::<u64>(&v61);
      std::mem::drop(v60);
      v62
    },
    false => {
      std::mem::drop(t);
      let v73 = mul(3u64, b);
      let v74 = &meta;
      let v77 = rocq_array::get::<u64>(&v74, v73);
      let v95 = add(mul(3u64, b), 2u64);
      let v96 = &meta;
      let v99 = rocq_array::get::<u64>(&v96, v95);
      std::mem::drop(meta);
      add(v77, mod_(hash(v99, x), sz))
    },
  }
}

// Rocq: Babelfish.babelfish_implem.check_loop
// Variant: uncurried
pub fn check_loop_1(t: Rc<tables>, f: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, i: u64) -> bool {
  check_loop(t, f, n, i, ())
}

// Rocq: Babelfish.babelfish_implem.check_loop (local: check_loop)
// Variant: uncurried, lifted
pub fn check_loop(t: Rc<tables>, f: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, i: u64, _H: ()) -> bool {
  let v12 = ltb(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v20 = Rc::clone(&t);
      let v21 = t_slot(v20);
      let v23 = &f;
      let v26 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v23, i);
      let v29 = Rc::clone(&t);
      let v32 = pos(v29, v26);
      let v33 = &v21;
      let v36 = rocq_array::get::<u64>(&v33, v32);
      let v44 = add(i, 1u64);
      match eqb(v36, v44) {
        true => {
          std::mem::drop(v21);
          check_loop(t, f, n, add(i, 1u64), ())
        },
        false => {
          std::mem::drop(t);
          std::mem::drop(f);
          std::mem::drop(v21);
          false
        },
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
pub fn compare(v0: Rc<rocq_string::RocqString>, v1: Rc<rocq_string::RocqString>) -> std::cmp::Ordering {
  let v4 = rocq_string::compare(&v0, &v1);
  std::mem::drop(v1);
  std::mem::drop(v0);
  v4
}

// Rocq: Babelfish.babelfish_implem.scan_loop
// Variant: uncurried
pub fn scan_loop_1(f: Rc<Array<Rc<rocq_string::RocqString>>>, x: Rc<rocq_string::RocqString>, n: u64, i: u64) -> u64 {
  scan_loop(f, x, n, i, ())
}

// Rocq: Babelfish.babelfish_implem.scan_loop (local: scan_loop)
// Variant: uncurried, lifted
pub fn scan_loop(f: Rc<Array<Rc<rocq_string::RocqString>>>, x: Rc<rocq_string::RocqString>, n: u64, i: u64, _H: ()) -> u64 {
  let v12 = ltb(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v17 = &f;
      let v21 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v17, i);
      let v25 = Rc::clone(&x);
      match compare(v21, v25) {
        std::cmp::Ordering::Equal => {
          std::mem::drop(f);
          std::mem::drop(x);
          i
        },
        std::cmp::Ordering::Less => {
          scan_loop(f, x, n, add(i, 1u64), ())
        },
        std::cmp::Ordering::Greater => {
          scan_loop(f, x, n, add(i, 1u64), ())
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
pub fn query(e: Rc<Array<Rc<rocq_string::RocqString>>>, f: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, ok: bool, t: Rc<tables>, x: Rc<rocq_string::RocqString>) -> Rc<option<Rc<rocq_string::RocqString>>> {
  let i = match ok {
    true => {
      let v11 = Rc::clone(&t);
      let v12 = t_slot(v11);
      let v18 = Rc::clone(&x);
      let v19 = pos(t, v18);
      let v20 = &v12;
      let v23 = rocq_array::get::<u64>(&v20, v19);
      std::mem::drop(v12);
      sub(v23, 1u64)
    },
    false => {
      std::mem::drop(t);
      let v38 = Rc::clone(&f);
      let v41 = Rc::clone(&x);
      scan_loop_1(v38, v41, n, 0u64)
    },
  };
  match ltb(i, n) {
    true => {
      let v58 = &f;
      let v62 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v58, i);
      match compare(v62, x) {
        std::cmp::Ordering::Equal => {
          std::mem::drop(f);
          let v68 = &e;
          let v71 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v68, i);
          std::mem::drop(e);
          Rc::new(option::<Rc<rocq_string::RocqString>>::Some(v71))
        },
        std::cmp::Ordering::Less => {
          std::mem::drop(e);
          std::mem::drop(f);
          Rc::new(option::<Rc<rocq_string::RocqString>>::None)
        },
        std::cmp::Ordering::Greater => {
          std::mem::drop(e);
          std::mem::drop(f);
          Rc::new(option::<Rc<rocq_string::RocqString>>::None)
        },
      }
    },
    false => {
      std::mem::drop(e);
      std::mem::drop(f);
      std::mem::drop(x);
      Rc::new(option::<Rc<rocq_string::RocqString>>::None)
    },
  }
}

// Rocq: Babelfish.babelfish_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(e: Rc<Array<Rc<rocq_string::RocqString>>>, f: Rc<Array<Rc<rocq_string::RocqString>>>, m: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, ok: bool, t: Rc<tables>, L: u64, k: u64, out: Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>>) -> Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>> {
  fill_loop(e, f, m, n, ok, t, L, k, out, ())
}

// Rocq: Babelfish.babelfish_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(e: Rc<Array<Rc<rocq_string::RocqString>>>, f: Rc<Array<Rc<rocq_string::RocqString>>>, m: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, ok: bool, t: Rc<tables>, L: u64, k: u64, out: Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>>, _H: ()) -> Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>> {
  let v17 = ltb(k, L);
  match bdec(v17) {
    sumbool::left => {
      let v28 = add(k, 1u64);
      let v30 = &m;
      let v33 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v30, k);
      let v36 = Rc::clone(&e);
      let v39 = Rc::clone(&f);
      let v46 = Rc::clone(&t);
      let v56 = rocq_array::set::<Rc<option<Rc<rocq_string::RocqString>>>>(out, k, query(v36, v39, n, ok, v46, v33));
      fill_loop(e, f, m, n, ok, t, L, v28, v56, ())
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
pub fn babelfish_impl(e: Rc<Array<Rc<rocq_string::RocqString>>>, f: Rc<Array<Rc<rocq_string::RocqString>>>, m: Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>> {
  let v3 = &f;
  let n = rocq_array::length::<Rc<rocq_string::RocqString>>(&v3);
  let v8 = Rc::clone(&f);
  let t = build(v8, n);
  let v17 = Rc::clone(&t);
  let v20 = Rc::clone(&f);
  let ok = check_loop_1(v17, v20, n, 0u64);
  let v26 = &m;
  let L = rocq_array::length::<Rc<rocq_string::RocqString>>(&v26);
  let v38 = rocq_array::make::<Rc<option<Rc<rocq_string::RocqString>>>>(L, Rc::new(option::<Rc<rocq_string::RocqString>>::None));
  fill_loop_1(e, f, m, n, ok, t, L, 0u64, v38)
}

// Rocq: Babelfish.babelfish_implem.babelfish_impl
pub fn babelfish_impl_curried(e: Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>>>> {
  let v3 = {
    move |f: Rc<Array<Rc<rocq_string::RocqString>>>| -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>>> {
      let e = &e;
      let v8 = Rc::clone(e);
      let v11 = {
        move |m: Rc<Array<Rc<rocq_string::RocqString>>>| -> Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>> {
          let v19 = Rc::clone(&v8);
          let v21 = Rc::clone(&f);
          babelfish_impl(v19, v21, m)
        }
      };
      let v27: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>>> = Rc::new(v11);
      v27
    }
  };
  let v31: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>>>> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>>> {
  let v0: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>>> = __rocq_global_1345.with(Clone::clone);
  v0
}
const __rocq_global_95: u64 = 2147483647u64;
const __rocq_global_460: u64 = 88172645463325252u64;
std::thread_local! { static __rocq_global_1345: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>>> = babelfish(); }
std::thread_local! { static __rocq_global_1348: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<rocq_string::RocqString>>>>>>>> = babelfish_curried(); }