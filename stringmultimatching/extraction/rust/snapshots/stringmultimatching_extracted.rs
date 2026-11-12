// Generated from OwnedANF. This printer is not verified.
#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub struct bstate {
  pub bact: Rc<Array<u64>>,
  pub bcur: Rc<Array<u64>>,
  pub bw: u64,
  pub bt: Rc<trie>,
}

impl Clone for bstate {
  fn clone(&self) -> Self {
    match self {
      bstate { bact: __field0, bcur: __field1, bw: __field2, bt: __field3 } => bstate { bact: Clone::clone(__field0), bcur: Clone::clone(__field1), bw: Clone::clone(__field2), bt: Clone::clone(__field3) },
    }
  }
}

pub struct trie {
  pub tchr: Rc<Array<u64>>,
  pub tpar: Rc<Array<u64>>,
  pub tfc: Rc<Array<u64>>,
  pub tns: Rc<Array<u64>>,
  pub tdep: Rc<Array<u64>>,
  pub tn: u64,
}

impl Clone for trie {
  fn clone(&self) -> Self {
    match self {
      trie { tchr: __field0, tpar: __field1, tfc: __field2, tns: __field3, tdep: __field4, tn: __field5 } => trie { tchr: Clone::clone(__field0), tpar: Clone::clone(__field1), tfc: Clone::clone(__field2), tns: Clone::clone(__field3), tdep: Clone::clone(__field4), tn: Clone::clone(__field5) },
    }
  }
}

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type char63 = u64;

pub type uint = u64;

// Rocq: Stringmultimatching.stringmultimatching_implem.multimatch
// Variant: uncurried
pub fn multimatch() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<rocq_string::RocqString>) -> Rc<Array<Rc<Array<u64>>>>> {
  let v0: fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<rocq_string::RocqString>) -> Rc<Array<Rc<Array<u64>>>> = multimatch_impl;
  let v1: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<rocq_string::RocqString>) -> Rc<Array<Rc<Array<u64>>>>> = Rc::new(v0);
  v1
}

// Rocq: Stringmultimatching.stringmultimatching_implem.multimatch
pub fn multimatch_curried() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<Array<Rc<Array<u64>>>>>> {
  let v0: fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<Array<Rc<Array<u64>>>>> = multimatch_impl_curried;
  let v1: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<Array<Rc<Array<u64>>>>>> = Rc::new(v0);
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

// Rocq: Stringmultimatching.stringmultimatching_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Stringmultimatching.stringmultimatching_implem.sums
// Variant: uncurried
pub fn sums_1(pats: Rc<Array<Rc<rocq_string::RocqString>>>, m: u64, i: u64, P: u64, L: u64) -> (u64, u64) {
  sums(pats, m, i, P, L, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.sums (local: sums)
// Variant: uncurried, lifted
pub fn sums(pats: Rc<Array<Rc<rocq_string::RocqString>>>, m: u64, i: u64, P: u64, L: u64, _H: ()) -> (u64, u64) {
  let v13 = ltb(i, m);
  match bdec(v13) {
    sumbool::left => {
      let v18 = &pats;
      let v22 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v18, i);
      let l = length(v22);
      let v32 = add(i, 1u64);
      let v38 = add(P, l);
      let v45 = match ltb(L, l) {
        true => {
          l
        },
        false => {
          L
        },
      };
      sums(pats, m, v32, v38, v45, ())
    },
    sumbool::right => {
      std::mem::drop(pats);
      (P, L)
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

// Rocq: Stringmultimatching.stringmultimatching_implem.iota
// Variant: uncurried
pub fn iota_1(m: u64, i: u64, a: Rc<Array<u64>>) -> Rc<Array<u64>> {
  iota(m, i, a, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.iota (local: iota)
// Variant: uncurried, lifted
pub fn iota(m: u64, i: u64, a: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v11 = ltb(i, m);
  match bdec(v11) {
    sumbool::left => {
      let v22 = add(i, 1u64);
      let v29 = rocq_array::set::<u64>(a, i, i);
      iota(m, v22, v29, ())
    },
    sumbool::right => {
      a
    },
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.bact
pub fn bact(b: Rc<bstate>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&b).bact));
  std::mem::drop(b);
  v3
}

// Rocq: Stringmultimatching.stringmultimatching_implem.bcur
pub fn bcur(b: Rc<bstate>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&b).bcur));
  std::mem::drop(b);
  v3
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tfc
pub fn tfc_owned(t: Rc<trie>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tfc));
  std::mem::drop(t);
  v3
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tfc
// Variant: borrowed
pub fn tfc(t: &Rc<trie>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tfc))
}

// Rocq: Stringmultimatching.stringmultimatching_implem.lookup_from
// Variant: uncurried
pub fn lookup_from_1(chr: Rc<Array<u64>>, ns: Rc<Array<u64>>, c: u64, v: u64) -> u64 {
  lookup_from(chr, ns, c, v, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.lookup_from (local: lookup_from)
// Variant: uncurried, lifted
pub fn lookup_from(chr: Rc<Array<u64>>, ns: Rc<Array<u64>>, c: u64, v: u64, _H: ()) -> u64 {
  let v14 = eqb(v, 0u64);
  match bdec(v14) {
    sumbool::left => {
      std::mem::drop(chr);
      std::mem::drop(ns);
      0u64
    },
    sumbool::right => {
      let v23 = &chr;
      let v27 = rocq_array::get::<u64>(&v23, v);
      match eqb(v27, c) {
        true => {
          std::mem::drop(chr);
          std::mem::drop(ns);
          v
        },
        false => {
          let v35 = &ns;
          let nx = rocq_array::get::<u64>(&v35, v);
          let v46 = ltb(nx, v);
          match bdec(v46) {
            sumbool::left => {
              lookup_from(chr, ns, c, nx, ())
            },
            sumbool::right => {
              std::mem::drop(chr);
              std::mem::drop(ns);
              0u64
            },
          }
        },
      }
    },
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tchr
pub fn tchr_owned(t: Rc<trie>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tchr));
  std::mem::drop(t);
  v3
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tchr
// Variant: borrowed
pub fn tchr(t: &Rc<trie>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tchr))
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tns
pub fn tns_owned(t: Rc<trie>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tns));
  std::mem::drop(t);
  v3
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tns
// Variant: borrowed
pub fn tns(t: &Rc<trie>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tns))
}

// Rocq: Stringmultimatching.stringmultimatching_implem.lookup
// Variant: borrowed, uncurried
pub fn lookup(t: &Rc<trie>, u: u64, c: u64) -> u64 {
  let u_1 = u;
  let c_1 = c;
  let v8 = tfc(t);
  let v9 = &v8;
  let v = rocq_array::get::<u64>(&v9, u_1);
  std::mem::drop(v8);
  let v17 = tchr(t);
  let v21 = tns(t);
  lookup_from_1(v17, v21, c_1, v)
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tn
// Variant: borrowed
pub fn tn(t: &Rc<trie>) -> u64 {
  let v1 = t;
  Clone::clone((&(&**v1).tn))
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tdep
pub fn tdep(t: Rc<trie>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tdep));
  std::mem::drop(t);
  v3
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tpar
pub fn tpar(t: Rc<trie>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tpar));
  std::mem::drop(t);
  v3
}

// Rocq: Stringmultimatching.stringmultimatching_implem.add_child
// Variant: uncurried
pub fn add_child(t: Rc<trie>, u: u64, c: u64) -> (Rc<trie>, u64) {
  let v = lookup(&t, u, c);
  match eqb(v, 0u64) {
    true => {
      let n = tn(&t);
      let v27 = Rc::clone(&t);
      let v28 = tfc_owned(v27);
      let v29 = &v28;
      let old = rocq_array::get::<u64>(&v29, u);
      std::mem::drop(v28);
      let v36 = Rc::clone(&t);
      let v37 = tdep(v36);
      let v38 = &v37;
      let du = rocq_array::get::<u64>(&v38, u);
      std::mem::drop(v37);
      let v45 = Rc::clone(&t);
      let v47 = tchr_owned(v45);
      let v53 = rocq_array::set::<u64>(v47, n, c);
      let v57 = Rc::clone(&t);
      let v59 = tpar(v57);
      let v65 = rocq_array::set::<u64>(v59, n, u);
      let v69 = Rc::clone(&t);
      let v71 = tfc_owned(v69);
      let v77 = rocq_array::set::<u64>(v71, u, n);
      let v81 = Rc::clone(&t);
      let v83 = tns_owned(v81);
      let v89 = rocq_array::set::<u64>(v83, n, old);
      let v93 = tdep(t);
      let v108 = rocq_array::set::<u64>(v93, n, add(du, 1u64));
      (Rc::new(trie { tchr: v53, tpar: v65, tfc: v77, tns: v89, tdep: v108, tn: add(n, 1u64) }), n)
    },
    false => {
      (t, v)
    },
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.bt
pub fn bt(b: Rc<bstate>) -> Rc<trie> {
  let v3 = Rc::clone((&(&**&b).bt));
  std::mem::drop(b);
  v3
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let v5 = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  v5
}

// Rocq: Stringmultimatching.stringmultimatching_implem.bw
pub fn bw_owned(b: Rc<bstate>) -> u64 {
  let v3 = Clone::clone((&(&**&b).bw));
  std::mem::drop(b);
  v3
}

// Rocq: Stringmultimatching.stringmultimatching_implem.bw
// Variant: borrowed
pub fn bw(b: &Rc<bstate>) -> u64 {
  let v1 = b;
  Clone::clone((&(&**v1).bw))
}

// Rocq: Stringmultimatching.stringmultimatching_implem.round_loop
// Variant: uncurried
pub fn round_loop_1(pats: Rc<Array<Rc<rocq_string::RocqString>>>, d: u64, na: u64, k: u64, st: Rc<bstate>) -> Rc<bstate> {
  round_loop(pats, d, na, k, st, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.round_loop (local: round_loop)
// Variant: uncurried, lifted
pub fn round_loop(pats: Rc<Array<Rc<rocq_string::RocqString>>>, d: u64, na: u64, k: u64, st: Rc<bstate>, _H: ()) -> Rc<bstate> {
  let v13 = ltb(k, na);
  match bdec(v13) {
    sumbool::left => {
      let v20 = Rc::clone(&st);
      let act = bact(v20);
      let v22 = &act;
      let i = rocq_array::get::<u64>(&v22, k);
      let v26 = &pats;
      let s = rocq_array::get::<Rc<rocq_string::RocqString>>(&v26, i);
      let v33 = Rc::clone(&st);
      let cur = bcur(v33);
      let v39 = Rc::clone(&st);
      let v40 = bt(v39);
      let v41 = &cur;
      let v44 = rocq_array::get::<u64>(&v41, i);
      let v48 = Rc::clone(&s);
      let tv = add_child(v40, v44, get(v48, d));
      let v61 = Clone::clone(&tv);
      let cur_ = rocq_array::set::<u64>(cur, i, snd::<Rc<trie>, u64>(v61));
      let w = bw_owned(st);
      let v83 = add(d, 1u64);
      let v87 = length(s);
      match ltb(v83, v87) {
        true => {
          let v101 = add(k, 1u64);
          let v108 = rocq_array::set::<u64>(act, w, i);
          round_loop(pats, d, na, v101, Rc::new(bstate { bact: v108, bcur: cur_, bw: add(w, 1u64), bt: fst::<Rc<trie>, u64>(tv) }), ())
        },
        false => {
          round_loop(pats, d, na, add(k, 1u64), Rc::new(bstate { bact: act, bcur: cur_, bw: w, bt: fst::<Rc<trie>, u64>(tv) }), ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(pats);
      st
    },
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.rounds
// Variant: uncurried
pub fn rounds_1(pats: Rc<Array<Rc<rocq_string::RocqString>>>, L: u64, d: u64, st: Rc<bstate>) -> Rc<bstate> {
  rounds(pats, L, d, st, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.rounds (local: rounds)
// Variant: uncurried, lifted
pub fn rounds(pats: Rc<Array<Rc<rocq_string::RocqString>>>, L: u64, d: u64, st: Rc<bstate>, _H: ()) -> Rc<bstate> {
  let v12 = ltb(d, L);
  match bdec(v12) {
    sumbool::left => {
      let v20 = bw(&st);
      let v26 = Rc::clone(&st);
      let v27 = bact(v26);
      let v31 = Rc::clone(&st);
      let v32 = bcur(v31);
      let v49 = Rc::new(bstate { bact: v27, bcur: v32, bw: 0u64, bt: bt(st) });
      let v52 = Rc::clone(&pats);
      let st_ = round_loop_1(v52, d, v20, 0u64, v49);
      rounds(pats, L, add(d, 1u64), st_, ())
    },
    sumbool::right => {
      std::mem::drop(pats);
      st
    },
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.plist_loop
// Variant: uncurried
pub fn plist_loop_1(cur: Rc<Array<u64>>, m: u64, i: u64, fp: Rc<Array<u64>>, np: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  plist_loop(cur, m, i, fp, np, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.plist_loop (local: plist_loop)
// Variant: uncurried, lifted
pub fn plist_loop(cur: Rc<Array<u64>>, m: u64, i: u64, fp: Rc<Array<u64>>, np: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v13 = ltb(i, m);
  match bdec(v13) {
    sumbool::left => {
      let v17 = &cur;
      let v = rocq_array::get::<u64>(&v17, i);
      let v21 = &fp;
      let old = rocq_array::get::<u64>(&v21, v);
      let v32 = add(i, 1u64);
      let v47 = rocq_array::set::<u64>(fp, v, add(i, 1u64));
      let v62 = rocq_array::set::<u64>(np, add(i, 1u64), old);
      plist_loop(cur, m, v32, v47, v62, ())
    },
    sumbool::right => {
      std::mem::drop(cur);
      (fp, np)
    },
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.walk
// Variant: uncurried
pub fn walk_1(t: Rc<trie>, fl: Rc<Array<u64>>, c: u64, x: u64) -> u64 {
  walk(t, fl, c, x, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(t: Rc<trie>, fl: Rc<Array<u64>>, c: u64, x: u64, _H: ()) -> u64 {
  let y = lookup(&t, x, c);
  let v22 = eqb(y, 0u64);
  match bdec(v22) {
    sumbool::left => {
      let v35 = eqb(x, 0u64);
      match bdec(v35) {
        sumbool::left => {
          std::mem::drop(fl);
          std::mem::drop(t);
          0u64
        },
        sumbool::right => {
          let v43 = &fl;
          let x_ = rocq_array::get::<u64>(&v43, x);
          let v54 = ltb(x_, x);
          match bdec(v54) {
            sumbool::left => {
              walk(t, fl, c, x_, ())
            },
            sumbool::right => {
              std::mem::drop(fl);
              std::mem::drop(t);
              0u64
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(fl);
      std::mem::drop(t);
      y
    },
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.fail_loop
// Variant: uncurried
pub fn fail_loop_1(t: Rc<trie>, fp: Rc<Array<u64>>, N: u64, v: u64, fl: Rc<Array<u64>>, out: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  fail_loop(t, fp, N, v, fl, out, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.fail_loop (local: fail_loop)
// Variant: uncurried, lifted
pub fn fail_loop(t: Rc<trie>, fp: Rc<Array<u64>>, N: u64, v: u64, fl: Rc<Array<u64>>, out: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v14 = ltb(v, N);
  match bdec(v14) {
    sumbool::left => {
      let v21 = Rc::clone(&t);
      let v22 = tpar(v21);
      let v23 = &v22;
      let u = rocq_array::get::<u64>(&v23, v);
      let v30 = Rc::clone(&t);
      let v31 = tchr_owned(v30);
      let v32 = &v31;
      let c = rocq_array::get::<u64>(&v32, v);
      let v38 = 0u64;
      let f = match eqb(u, v38) {
        true => {
          0u64
        },
        false => {
          let v49 = &fl;
          let x = rocq_array::get::<u64>(&v49, u);
          let v56 = Rc::clone(&t);
          let v59 = Rc::clone(&fl);
          walk_1(v56, v59, c, x)
        },
      };
      let v69 = &fp;
      let v72 = rocq_array::get::<u64>(&v69, f);
      let v74 = 0u64;
      let o = match eqb(v72, v74) {
        true => {
          std::mem::drop(v31);
          std::mem::drop(v22);
          let v81 = &out;
          rocq_array::get::<u64>(&v81, f)
        },
        false => {
          std::mem::drop(v31);
          std::mem::drop(v22);
          f
        },
      };
      let v97 = add(v, 1u64);
      let v104 = rocq_array::set::<u64>(fl, v, f);
      let v111 = rocq_array::set::<u64>(out, v, o);
      fail_loop(t, fp, N, v97, v104, v111, ())
    },
    sumbool::right => {
      std::mem::drop(t);
      std::mem::drop(fp);
      (fl, out)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Stringmultimatching.stringmultimatching_implem.emit_list
// Variant: uncurried
pub fn emit_list_1<Sx: Clone + 'static>(f: Rc<dyn Fn(Sx, u64, u64) -> Sx>, np: Rc<Array<u64>>, p: u64, e: u64, s: Sx) -> Sx {
  emit_list::<Sx>(f, np, p, e, s, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.emit_list (local: emit_list)
// Variant: uncurried, lifted
pub fn emit_list<Sx: Clone + 'static>(f: Rc<dyn Fn(Sx, u64, u64) -> Sx>, np: Rc<Array<u64>>, p: u64, e: u64, s: Sx, _H: ()) -> Sx {
  let v15 = eqb(e, 0u64);
  match bdec(v15) {
    sumbool::left => {
      std::mem::drop(f);
      std::mem::drop(np);
      s
    },
    sumbool::right => {
      let v28 = sub(e, 1u64);
      let v29: &Rc<dyn Fn(Sx, u64, u64) -> Sx> = &f;
      let s_ = v29(s, v28, p);
      let v37 = &np;
      let e_ = rocq_array::get::<u64>(&v37, e);
      let v48 = ltb(e_, e);
      match bdec(v48) {
        sumbool::left => {
          emit_list::<Sx>(f, np, p, e_, s_, ())
        },
        sumbool::right => {
          std::mem::drop(np);
          std::mem::drop(f);
          s_
        },
      }
    },
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.emit_chain
// Variant: uncurried
pub fn emit_chain_1<Sx: Clone + 'static>(f: Rc<dyn Fn(Sx, u64, u64) -> Sx>, t: Rc<trie>, out: Rc<Array<u64>>, fp: Rc<Array<u64>>, np: Rc<Array<u64>>, je: u64, x: u64, s: Sx) -> Sx {
  emit_chain::<Sx>(fp, t, f, np, out, je, x, s, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.emit_chain (local: emit_chain)
// Variant: uncurried, lifted
pub fn emit_chain<Sx: Clone + 'static>(fp: Rc<Array<u64>>, t: Rc<trie>, f: Rc<dyn Fn(Sx, u64, u64) -> Sx>, np: Rc<Array<u64>>, out: Rc<Array<u64>>, je: u64, x: u64, s: Sx, _H: ()) -> Sx {
  let v18 = eqb(x, 0u64);
  match bdec(v18) {
    sumbool::left => {
      std::mem::drop(fp);
      std::mem::drop(t);
      std::mem::drop(f);
      std::mem::drop(np);
      std::mem::drop(out);
      s
    },
    sumbool::right => {
      let v24 = &fp;
      let e = rocq_array::get::<u64>(&v24, x);
      let v33 = Rc::clone(&t);
      let v34 = tdep(v33);
      let v35 = &v34;
      let v38 = rocq_array::get::<u64>(&v35, x);
      let v43 = sub(je, v38);
      let v45: Rc<dyn Fn(Sx, u64, u64) -> Sx> = Rc::clone(&f);
      let v49 = Rc::clone(&np);
      let s_ = emit_list_1::<Sx>(v45, v49, v43, e, s);
      let v57 = &out;
      let o = rocq_array::get::<u64>(&v57, x);
      let v68 = ltb(o, x);
      match bdec(v68) {
        sumbool::left => {
          std::mem::drop(v34);
          emit_chain::<Sx>(fp, t, f, np, out, je, o, s_, ())
        },
        sumbool::right => {
          std::mem::drop(v34);
          std::mem::drop(fp);
          std::mem::drop(t);
          std::mem::drop(f);
          std::mem::drop(np);
          std::mem::drop(out);
          s_
        },
      }
    },
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.scan
// Variant: uncurried
pub fn scan_1<Sx: Clone + 'static>(f: Rc<dyn Fn(Sx, u64, u64) -> Sx>, t: Rc<trie>, fl: Rc<Array<u64>>, out: Rc<Array<u64>>, fp: Rc<Array<u64>>, np: Rc<Array<u64>>, txt: Rc<rocq_string::RocqString>, n: u64, j: u64, st: u64, s: Sx) -> Sx {
  scan::<Sx>(txt, t, fl, f, out, fp, np, n, j, st, s, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan<Sx: Clone + 'static>(txt: Rc<rocq_string::RocqString>, t: Rc<trie>, fl: Rc<Array<u64>>, f: Rc<dyn Fn(Sx, u64, u64) -> Sx>, out: Rc<Array<u64>>, fp: Rc<Array<u64>>, np: Rc<Array<u64>>, n: u64, j: u64, st: u64, s: Sx, _H: ()) -> Sx {
  let v19 = ltb(j, n);
  match bdec(v19) {
    sumbool::left => {
      let v27 = Rc::clone(&txt);
      let v30 = get(v27, j);
      let v33 = Rc::clone(&t);
      let v36 = Rc::clone(&fl);
      let st_ = walk_1(v33, v36, v30, st);
      let v50 = add(j, 1u64);
      let v52: Rc<dyn Fn(Sx, u64, u64) -> Sx> = Rc::clone(&f);
      let v56 = Rc::clone(&t);
      let v59 = Rc::clone(&out);
      let v62 = Rc::clone(&fp);
      let v65 = Rc::clone(&np);
      let s_ = emit_chain_1::<Sx>(v52, v56, v59, v62, v65, v50, st_, s);
      scan::<Sx>(txt, t, fl, f, out, fp, np, n, add(j, 1u64), st_, s_, ())
    },
    sumbool::right => {
      std::mem::drop(txt);
      std::mem::drop(t);
      std::mem::drop(fl);
      std::mem::drop(f);
      std::mem::drop(out);
      std::mem::drop(fp);
      std::mem::drop(np);
      s
    },
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.f_cnt
// Variant: uncurried
pub fn f_cnt(cnt: Rc<Array<u64>>, i: u64, _p: u64) -> Rc<Array<u64>> {
  let v3 = &cnt;
  let c = rocq_array::get::<u64>(&v3, i);
  rocq_array::set::<u64>(cnt, i, add(c, 1u64))
}

// Rocq: Stringmultimatching.stringmultimatching_implem.alloc_loop
// Variant: uncurried
pub fn alloc_loop_1(cnt: Rc<Array<u64>>, m: u64, i: u64, rows: Rc<Array<Rc<Array<u64>>>>) -> Rc<Array<Rc<Array<u64>>>> {
  alloc_loop(cnt, m, i, rows, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.alloc_loop (local: alloc_loop)
// Variant: uncurried, lifted
pub fn alloc_loop(cnt: Rc<Array<u64>>, m: u64, i: u64, rows: Rc<Array<Rc<Array<u64>>>>, _H: ()) -> Rc<Array<Rc<Array<u64>>>> {
  let v12 = ltb(i, m);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v24 = &cnt;
      let v27 = rocq_array::get::<u64>(&v24, i);
      let v34 = rocq_array::make::<u64>(v27, 0u64);
      let v41 = rocq_array::set::<Rc<Array<u64>>>(rows, i, v34);
      alloc_loop(cnt, m, v23, v41, ())
    },
    sumbool::right => {
      std::mem::drop(cnt);
      rows
    },
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.f_fill
// Variant: uncurried
pub fn f_fill(st: (Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>), i: u64, p: u64) -> (Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>) {
  let v5 = Clone::clone(&st);
  let rows = fst::<Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>>(v5);
  let ptr = snd::<Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>>(st);
  let v12 = &ptr;
  let k = rocq_array::get::<u64>(&v12, i);
  let v18 = Rc::clone(&rows);
  let row = rocq_array::get::<Rc<Array<u64>>>(&v18, i);
  std::mem::drop(v18);
  let v29 = rocq_array::set::<u64>(row, k, p);
  let v36 = rocq_array::set::<Rc<Array<u64>>>(rows, i, v29);
  let v51 = rocq_array::set::<u64>(ptr, i, add(k, 1u64));
  (v36, v51)
}

// Rocq: Stringmultimatching.stringmultimatching_implem.multimatch_impl
// Variant: uncurried
pub fn multimatch_impl(pats: Rc<Array<Rc<rocq_string::RocqString>>>, txt: Rc<rocq_string::RocqString>) -> Rc<Array<Rc<Array<u64>>>> {
  let v2 = &pats;
  let m = rocq_array::length::<Rc<rocq_string::RocqString>>(&v2);
  let v13 = Rc::clone(&pats);
  let PL = sums_1(v13, m, 0u64, 0u64, 0u64);
  let v26 = Clone::clone(&PL);
  let cap = add(fst::<u64, u64>(v26), 1u64);
  let L = snd::<u64, u64>(PL);
  let v46 = rocq_array::make::<u64>(cap, 0u64);
  let v53 = rocq_array::make::<u64>(cap, 0u64);
  let v60 = rocq_array::make::<u64>(cap, 0u64);
  let v67 = rocq_array::make::<u64>(cap, 0u64);
  let v74 = rocq_array::make::<u64>(cap, 0u64);
  let t0 = Rc::new(trie { tchr: v46, tpar: v53, tfc: v60, tns: v67, tdep: v74, tn: 1u64 });
  let v101 = rocq_array::make::<u64>(m, 0u64);
  let act0 = iota_1(m, 0u64, v101);
  let v118 = rocq_array::make::<u64>(m, 0u64);
  let st = rounds_1(pats, L, 0u64, Rc::new(bstate { bact: act0, bcur: v118, bw: m, bt: t0 }));
  let v142 = Rc::clone(&st);
  let t = bt(v142);
  let v148 = bcur(st);
  let v157 = rocq_array::make::<u64>(cap, 0u64);
  let v172 = rocq_array::make::<u64>(add(m, 1u64), 0u64);
  let pl = plist_loop_1(v148, m, 0u64, v157, v172);
  let v186 = Clone::clone(&pl);
  let fp = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(v186);
  let np = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(pl);
  let v197 = tn(&t);
  let v206 = rocq_array::make::<u64>(cap, 0u64);
  let v213 = rocq_array::make::<u64>(cap, 0u64);
  let v216 = Rc::clone(&t);
  let v219 = Rc::clone(&fp);
  let fo = fail_loop_1(v216, v219, v197, 1u64, v206, v213);
  let v231 = Clone::clone(&fo);
  let fl = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(v231);
  let out = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fo);
  let v241 = Rc::clone(&txt);
  let n = length(v241);
  let v244: fn(Rc<Array<u64>>, u64, u64) -> Rc<Array<u64>> = f_cnt;
  let v245: Rc<dyn Fn(Rc<Array<u64>>, u64, u64) -> Rc<Array<u64>>> = Rc::new(v244);
  let v257 = rocq_array::make::<u64>(m, 0u64);
  let v262 = Rc::clone(&t);
  let v265 = Rc::clone(&fl);
  let v268 = Rc::clone(&out);
  let v271 = Rc::clone(&fp);
  let v274 = Rc::clone(&np);
  let v277 = Rc::clone(&txt);
  let cnt = scan_1::<Rc<Array<u64>>>(v245, v262, v265, v268, v271, v274, v277, n, 0u64, 0u64, v257);
  let v298 = rocq_array::make::<u64>(0u64, 0u64);
  let v303 = rocq_array::make::<Rc<Array<u64>>>(m, v298);
  let rows = alloc_loop_1(cnt, m, 0u64, v303);
  let v315: fn((Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>), u64, u64) -> (Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>) = f_fill;
  let v316: Rc<dyn Fn((Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>), u64, u64) -> (Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>)> = Rc::new(v315);
  let v328 = rocq_array::make::<u64>(m, 0u64);
  fst::<Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>>(scan_1::<(Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>)>(v316, t, fl, out, fp, np, txt, n, 0u64, 0u64, (rows, v328)))
}

// Rocq: Stringmultimatching.stringmultimatching_implem.multimatch_impl
pub fn multimatch_impl_curried(pats: Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<Array<Rc<Array<u64>>>>> {
  let v3 = {
    move |txt: Rc<rocq_string::RocqString>| -> Rc<Array<Rc<Array<u64>>>> {
      let v9 = Rc::clone(&pats);
      multimatch_impl(v9, txt)
    }
  };
  let v15: Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<Array<Rc<Array<u64>>>>> = Rc::new(v3);
  v15
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

pub fn run() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<rocq_string::RocqString>) -> Rc<Array<Rc<Array<u64>>>>> {
  let v0: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<rocq_string::RocqString>) -> Rc<Array<Rc<Array<u64>>>>> = __rocq_global_1311.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_1311: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<rocq_string::RocqString>) -> Rc<Array<Rc<Array<u64>>>>> = multimatch(); }
std::thread_local! { static __rocq_global_1314: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<Array<Rc<Array<u64>>>>>> = multimatch_curried(); }