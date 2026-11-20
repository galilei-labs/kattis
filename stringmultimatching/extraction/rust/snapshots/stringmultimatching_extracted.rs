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
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: Rc<rocq_string::RocqString>) -> u64 {
  let tmp = rocq_string::length(&v0);
  std::mem::drop(v0);
  tmp
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
  let tmp = ltb(i, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<Rc<rocq_string::RocqString>>(&pats, i);
      let l = length(tmp_1);
      let tmp_2 = add(i, 1u64);
      let tmp_3 = add(P, l);
      let tmp_4 = if ltb(L, l) {
        l
      } else {
        L
      };
      sums(pats, m, tmp_2, tmp_3, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(pats);
      (P, L)
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

// Rocq: Stringmultimatching.stringmultimatching_implem.iota
// Variant: uncurried
pub fn iota_1(m: u64, i: u64, a: Rc<Array<u64>>) -> Rc<Array<u64>> {
  iota(m, i, a, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.iota (local: iota)
// Variant: uncurried, lifted
pub fn iota(m: u64, i: u64, a: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::set::<u64>(a, i, i);
      iota(m, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      a
    },
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.bact
pub fn bact(b: Rc<bstate>) -> Rc<Array<u64>> {
  let b_bact_clone = Rc::clone(&b.bact);
  std::mem::drop(b);
  b_bact_clone
}

// Rocq: Stringmultimatching.stringmultimatching_implem.bcur
pub fn bcur(b: Rc<bstate>) -> Rc<Array<u64>> {
  let b_bcur_clone = Rc::clone(&b.bcur);
  std::mem::drop(b);
  b_bcur_clone
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tfc
pub fn tfc_owned(t: Rc<trie>) -> Rc<Array<u64>> {
  let t_tfc_clone = Rc::clone(&t.tfc);
  std::mem::drop(t);
  t_tfc_clone
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tfc
// Variant: borrowed
pub fn tfc(t: &Rc<trie>) -> Rc<Array<u64>> {
  let tmp = t;
  Rc::clone(&tmp.tfc)
}

// Rocq: Stringmultimatching.stringmultimatching_implem.lookup_from
// Variant: uncurried
pub fn lookup_from_1(chr: Rc<Array<u64>>, ns: Rc<Array<u64>>, c: u64, v: u64) -> u64 {
  lookup_from(chr, ns, c, v, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.lookup_from (local: lookup_from)
// Variant: uncurried, lifted
pub fn lookup_from(chr: Rc<Array<u64>>, ns: Rc<Array<u64>>, c: u64, v: u64, _H: ()) -> u64 {
  let tmp = eqb(v, 0u64);
  match bdec(tmp) {
    sumbool::left => {
      std::mem::drop(chr);
      std::mem::drop(ns);
      0u64
    },
    sumbool::right => {
      let tmp_1 = rocq_array::get::<u64>(&chr, v);
      if eqb(tmp_1, c) {
        std::mem::drop(chr);
        std::mem::drop(ns);
        v
      } else {
        let nx = rocq_array::get::<u64>(&ns, v);
        let tmp_2 = ltb(nx, v);
        match bdec(tmp_2) {
          sumbool::left => {
            lookup_from(chr, ns, c, nx, ())
          },
          sumbool::right => {
            std::mem::drop(chr);
            std::mem::drop(ns);
            0u64
          },
        }
      }
    },
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tchr
pub fn tchr_owned(t: Rc<trie>) -> Rc<Array<u64>> {
  let t_tchr_clone = Rc::clone(&t.tchr);
  std::mem::drop(t);
  t_tchr_clone
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tchr
// Variant: borrowed
pub fn tchr(t: &Rc<trie>) -> Rc<Array<u64>> {
  let tmp = t;
  Rc::clone(&tmp.tchr)
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tns
pub fn tns_owned(t: Rc<trie>) -> Rc<Array<u64>> {
  let t_tns_clone = Rc::clone(&t.tns);
  std::mem::drop(t);
  t_tns_clone
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tns
// Variant: borrowed
pub fn tns(t: &Rc<trie>) -> Rc<Array<u64>> {
  let tmp = t;
  Rc::clone(&tmp.tns)
}

// Rocq: Stringmultimatching.stringmultimatching_implem.lookup
// Variant: borrowed, uncurried
pub fn lookup(t: &Rc<trie>, u: u64, c: u64) -> u64 {
  let u_1 = u;
  let c_1 = c;
  let tmp = tfc(t);
  let v = rocq_array::get::<u64>(&tmp, u_1);
  std::mem::drop(tmp);
  let tmp_1 = tchr(t);
  let tmp_2 = tns(t);
  lookup_from_1(tmp_1, tmp_2, c_1, v)
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tn
// Variant: borrowed
pub fn tn(t: &Rc<trie>) -> u64 {
  let tmp = t;
  Clone::clone(&tmp.tn)
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tdep
pub fn tdep(t: Rc<trie>) -> Rc<Array<u64>> {
  let t_tdep_clone = Rc::clone(&t.tdep);
  std::mem::drop(t);
  t_tdep_clone
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tpar
pub fn tpar(t: Rc<trie>) -> Rc<Array<u64>> {
  let t_tpar_clone = Rc::clone(&t.tpar);
  std::mem::drop(t);
  t_tpar_clone
}

// Rocq: Stringmultimatching.stringmultimatching_implem.add_child
// Variant: uncurried
pub fn add_child(t: Rc<trie>, u: u64, c: u64) -> (Rc<trie>, u64) {
  let v = lookup(&t, u, c);
  if eqb(v, 0u64) {
    let n = tn(&t);
    let t_clone = Rc::clone(&t);
    let tmp = tfc_owned(t_clone);
    let old = rocq_array::get::<u64>(&tmp, u);
    std::mem::drop(tmp);
    let t_clone_1 = Rc::clone(&t);
    let tmp_1 = tdep(t_clone_1);
    let du = rocq_array::get::<u64>(&tmp_1, u);
    std::mem::drop(tmp_1);
    let t_clone_2 = Rc::clone(&t);
    let tmp_2 = tchr_owned(t_clone_2);
    let tmp_3 = rocq_array::set::<u64>(tmp_2, n, c);
    let t_clone_3 = Rc::clone(&t);
    let tmp_4 = tpar(t_clone_3);
    let tmp_5 = rocq_array::set::<u64>(tmp_4, n, u);
    let t_clone_4 = Rc::clone(&t);
    let tmp_6 = tfc_owned(t_clone_4);
    let tmp_7 = rocq_array::set::<u64>(tmp_6, u, n);
    let t_clone_5 = Rc::clone(&t);
    let tmp_8 = tns_owned(t_clone_5);
    let tmp_9 = rocq_array::set::<u64>(tmp_8, n, old);
    let tmp_10 = tdep(t);
    let tmp_11 = rocq_array::set::<u64>(tmp_10, n, add(du, 1u64));
    (Rc::new(trie { tchr: tmp_3, tpar: tmp_5, tfc: tmp_7, tns: tmp_9, tdep: tmp_11, tn: add(n, 1u64) }), n)
  } else {
    (t, v)
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.bt
pub fn bt(b: Rc<bstate>) -> Rc<trie> {
  let b_bt_clone = Rc::clone(&b.bt);
  std::mem::drop(b);
  b_bt_clone
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let tmp = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Stringmultimatching.stringmultimatching_implem.bw
pub fn bw_owned(b: Rc<bstate>) -> u64 {
  let b_bw_clone = Clone::clone(&b.bw);
  std::mem::drop(b);
  b_bw_clone
}

// Rocq: Stringmultimatching.stringmultimatching_implem.bw
// Variant: borrowed
pub fn bw(b: &Rc<bstate>) -> u64 {
  let tmp = b;
  Clone::clone(&tmp.bw)
}

// Rocq: Stringmultimatching.stringmultimatching_implem.round_loop
// Variant: uncurried
pub fn round_loop_1(pats: Rc<Array<Rc<rocq_string::RocqString>>>, d: u64, na: u64, k: u64, st: Rc<bstate>) -> Rc<bstate> {
  round_loop(pats, d, na, k, st, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.round_loop (local: round_loop)
// Variant: uncurried, lifted
pub fn round_loop(pats: Rc<Array<Rc<rocq_string::RocqString>>>, d: u64, na: u64, k: u64, st: Rc<bstate>, _H: ()) -> Rc<bstate> {
  let tmp = ltb(k, na);
  match bdec(tmp) {
    sumbool::left => {
      let st_clone = Rc::clone(&st);
      let act = bact(st_clone);
      let i = rocq_array::get::<u64>(&act, k);
      let s = rocq_array::get::<Rc<rocq_string::RocqString>>(&pats, i);
      let st_clone_1 = Rc::clone(&st);
      let cur = bcur(st_clone_1);
      let st_clone_2 = Rc::clone(&st);
      let tmp_1 = bt(st_clone_2);
      let tmp_2 = rocq_array::get::<u64>(&cur, i);
      let s_clone = Rc::clone(&s);
      let tv = add_child(tmp_1, tmp_2, get(s_clone, d));
      let tv_clone = Clone::clone(&tv);
      let cur_ = rocq_array::set::<u64>(cur, i, snd::<Rc<trie>, u64>(tv_clone));
      let w = bw_owned(st);
      let tmp_3 = add(d, 1u64);
      let tmp_4 = length(s);
      if ltb(tmp_3, tmp_4) {
        let tmp_5 = add(k, 1u64);
        let tmp_6 = rocq_array::set::<u64>(act, w, i);
        round_loop(pats, d, na, tmp_5, Rc::new(bstate { bact: tmp_6, bcur: cur_, bw: add(w, 1u64), bt: fst::<Rc<trie>, u64>(tv) }), ())
      } else {
        round_loop(pats, d, na, add(k, 1u64), Rc::new(bstate { bact: act, bcur: cur_, bw: w, bt: fst::<Rc<trie>, u64>(tv) }), ())
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
  let tmp = ltb(d, L);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = bw(&st);
      let st_clone = Rc::clone(&st);
      let tmp_2 = bact(st_clone);
      let st_clone_1 = Rc::clone(&st);
      let tmp_3 = bcur(st_clone_1);
      let tmp_4 = Rc::new(bstate { bact: tmp_2, bcur: tmp_3, bw: 0u64, bt: bt(st) });
      let pats_clone = Rc::clone(&pats);
      let st_ = round_loop_1(pats_clone, d, tmp_1, 0u64, tmp_4);
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
  let tmp = ltb(i, m);
  match bdec(tmp) {
    sumbool::left => {
      let v = rocq_array::get::<u64>(&cur, i);
      let old = rocq_array::get::<u64>(&fp, v);
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::set::<u64>(fp, v, add(i, 1u64));
      let tmp_3 = rocq_array::set::<u64>(np, add(i, 1u64), old);
      plist_loop(cur, m, tmp_1, tmp_2, tmp_3, ())
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
  let tmp = eqb(y, 0u64);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = eqb(x, 0u64);
      match bdec(tmp_1) {
        sumbool::left => {
          std::mem::drop(fl);
          std::mem::drop(t);
          0u64
        },
        sumbool::right => {
          let x_ = rocq_array::get::<u64>(&fl, x);
          let tmp_2 = ltb(x_, x);
          match bdec(tmp_2) {
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
  let tmp = ltb(v, N);
  match bdec(tmp) {
    sumbool::left => {
      let t_clone = Rc::clone(&t);
      let tmp_1 = tpar(t_clone);
      let u = rocq_array::get::<u64>(&tmp_1, v);
      let t_clone_1 = Rc::clone(&t);
      let tmp_2 = tchr_owned(t_clone_1);
      let c = rocq_array::get::<u64>(&tmp_2, v);
      let tmp_3 = 0u64;
      let f = if eqb(u, tmp_3) {
        0u64
      } else {
        let x = rocq_array::get::<u64>(&fl, u);
        let t_clone_2 = Rc::clone(&t);
        let fl_clone = Rc::clone(&fl);
        walk_1(t_clone_2, fl_clone, c, x)
      };
      let tmp_4 = rocq_array::get::<u64>(&fp, f);
      let tmp_5 = 0u64;
      let o = if eqb(tmp_4, tmp_5) {
        std::mem::drop(tmp_2);
        std::mem::drop(tmp_1);
        rocq_array::get::<u64>(&out, f)
      } else {
        std::mem::drop(tmp_2);
        std::mem::drop(tmp_1);
        f
      };
      let tmp_6 = add(v, 1u64);
      let tmp_7 = rocq_array::set::<u64>(fl, v, f);
      let tmp_8 = rocq_array::set::<u64>(out, v, o);
      fail_loop(t, fp, N, tmp_6, tmp_7, tmp_8, ())
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
  let tmp = eqb(e, 0u64);
  match bdec(tmp) {
    sumbool::left => {
      std::mem::drop(f);
      std::mem::drop(np);
      s
    },
    sumbool::right => {
      let tmp_1 = sub(e, 1u64);
      let f_ref: &Rc<dyn Fn(Sx, u64, u64) -> Sx> = &f;
      let s_ = f_ref(s, tmp_1, p);
      let e_ = rocq_array::get::<u64>(&np, e);
      let tmp_2 = ltb(e_, e);
      match bdec(tmp_2) {
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
  let tmp = eqb(x, 0u64);
  match bdec(tmp) {
    sumbool::left => {
      std::mem::drop(fp);
      std::mem::drop(t);
      std::mem::drop(f);
      std::mem::drop(np);
      std::mem::drop(out);
      s
    },
    sumbool::right => {
      let e = rocq_array::get::<u64>(&fp, x);
      let t_clone = Rc::clone(&t);
      let tmp_1 = tdep(t_clone);
      let tmp_2 = rocq_array::get::<u64>(&tmp_1, x);
      let tmp_3 = sub(je, tmp_2);
      let f_clone: Rc<dyn Fn(Sx, u64, u64) -> Sx> = Rc::clone(&f);
      let np_clone = Rc::clone(&np);
      let s_ = emit_list_1::<Sx>(f_clone, np_clone, tmp_3, e, s);
      let o = rocq_array::get::<u64>(&out, x);
      let tmp_4 = ltb(o, x);
      match bdec(tmp_4) {
        sumbool::left => {
          std::mem::drop(tmp_1);
          emit_chain::<Sx>(fp, t, f, np, out, je, o, s_, ())
        },
        sumbool::right => {
          std::mem::drop(tmp_1);
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
  let tmp = ltb(j, n);
  match bdec(tmp) {
    sumbool::left => {
      let txt_clone = Rc::clone(&txt);
      let tmp_1 = get(txt_clone, j);
      let t_clone = Rc::clone(&t);
      let fl_clone = Rc::clone(&fl);
      let st_ = walk_1(t_clone, fl_clone, tmp_1, st);
      let tmp_2 = add(j, 1u64);
      let f_clone: Rc<dyn Fn(Sx, u64, u64) -> Sx> = Rc::clone(&f);
      let t_clone_1 = Rc::clone(&t);
      let out_clone = Rc::clone(&out);
      let fp_clone = Rc::clone(&fp);
      let np_clone = Rc::clone(&np);
      let s_ = emit_chain_1::<Sx>(f_clone, t_clone_1, out_clone, fp_clone, np_clone, tmp_2, st_, s);
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
  let c = rocq_array::get::<u64>(&cnt, i);
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
  let tmp = ltb(i, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&cnt, i);
      let tmp_3 = rocq_array::make::<u64>(tmp_2, 0u64);
      let tmp_4 = rocq_array::set::<Rc<Array<u64>>>(rows, i, tmp_3);
      alloc_loop(cnt, m, tmp_1, tmp_4, ())
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
  let st_clone = Clone::clone(&st);
  let rows = fst::<Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>>(st_clone);
  let ptr = snd::<Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>>(st);
  let k = rocq_array::get::<u64>(&ptr, i);
  let rows_clone = Rc::clone(&rows);
  let row = rocq_array::get::<Rc<Array<u64>>>(&rows_clone, i);
  std::mem::drop(rows_clone);
  let tmp = rocq_array::set::<u64>(row, k, p);
  let tmp_1 = rocq_array::set::<Rc<Array<u64>>>(rows, i, tmp);
  let tmp_2 = rocq_array::set::<u64>(ptr, i, add(k, 1u64));
  (tmp_1, tmp_2)
}

// Rocq: Stringmultimatching.stringmultimatching_implem.multimatch_impl
// Variant: uncurried
pub fn multimatch_impl(pats: Rc<Array<Rc<rocq_string::RocqString>>>, txt: Rc<rocq_string::RocqString>) -> Rc<Array<Rc<Array<u64>>>> {
  let m = rocq_array::length::<Rc<rocq_string::RocqString>>(&pats);
  let pats_clone = Rc::clone(&pats);
  let PL = sums_1(pats_clone, m, 0u64, 0u64, 0u64);
  let PL_clone = Clone::clone(&PL);
  let cap = add(fst::<u64, u64>(PL_clone), 1u64);
  let L = snd::<u64, u64>(PL);
  let tmp = rocq_array::make::<u64>(cap, 0u64);
  let tmp_1 = rocq_array::make::<u64>(cap, 0u64);
  let tmp_2 = rocq_array::make::<u64>(cap, 0u64);
  let tmp_3 = rocq_array::make::<u64>(cap, 0u64);
  let tmp_4 = rocq_array::make::<u64>(cap, 0u64);
  let t0 = Rc::new(trie { tchr: tmp, tpar: tmp_1, tfc: tmp_2, tns: tmp_3, tdep: tmp_4, tn: 1u64 });
  let tmp_5 = rocq_array::make::<u64>(m, 0u64);
  let act0 = iota_1(m, 0u64, tmp_5);
  let tmp_6 = rocq_array::make::<u64>(m, 0u64);
  let st = rounds_1(pats, L, 0u64, Rc::new(bstate { bact: act0, bcur: tmp_6, bw: m, bt: t0 }));
  let st_clone = Rc::clone(&st);
  let t = bt(st_clone);
  let tmp_7 = bcur(st);
  let tmp_8 = rocq_array::make::<u64>(cap, 0u64);
  let tmp_9 = rocq_array::make::<u64>(add(m, 1u64), 0u64);
  let pl = plist_loop_1(tmp_7, m, 0u64, tmp_8, tmp_9);
  let pl_clone = Clone::clone(&pl);
  let fp = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(pl_clone);
  let np = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(pl);
  let tmp_10 = tn(&t);
  let tmp_11 = rocq_array::make::<u64>(cap, 0u64);
  let tmp_12 = rocq_array::make::<u64>(cap, 0u64);
  let t_clone = Rc::clone(&t);
  let fp_clone = Rc::clone(&fp);
  let fo = fail_loop_1(t_clone, fp_clone, tmp_10, 1u64, tmp_11, tmp_12);
  let fo_clone = Clone::clone(&fo);
  let fl = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fo_clone);
  let out = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fo);
  let txt_clone = Rc::clone(&txt);
  let n = length(txt_clone);
  let tmp_13: fn(Rc<Array<u64>>, u64, u64) -> Rc<Array<u64>> = f_cnt;
  let tmp_14: Rc<dyn Fn(Rc<Array<u64>>, u64, u64) -> Rc<Array<u64>>> = Rc::new(tmp_13);
  let tmp_15 = rocq_array::make::<u64>(m, 0u64);
  let t_clone_1 = Rc::clone(&t);
  let fl_clone = Rc::clone(&fl);
  let out_clone = Rc::clone(&out);
  let fp_clone_1 = Rc::clone(&fp);
  let np_clone = Rc::clone(&np);
  let txt_clone_1 = Rc::clone(&txt);
  let cnt = scan_1::<Rc<Array<u64>>>(tmp_14, t_clone_1, fl_clone, out_clone, fp_clone_1, np_clone, txt_clone_1, n, 0u64, 0u64, tmp_15);
  let tmp_16 = rocq_array::make::<u64>(0u64, 0u64);
  let tmp_17 = rocq_array::make::<Rc<Array<u64>>>(m, tmp_16);
  let rows = alloc_loop_1(cnt, m, 0u64, tmp_17);
  let tmp_18: fn((Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>), u64, u64) -> (Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>) = f_fill;
  let tmp_19: Rc<dyn Fn((Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>), u64, u64) -> (Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>)> = Rc::new(tmp_18);
  let tmp_20 = rocq_array::make::<u64>(m, 0u64);
  fst::<Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>>(scan_1::<(Rc<Array<Rc<Array<u64>>>>, Rc<Array<u64>>)>(tmp_19, t, fl, out, fp, np, txt, n, 0u64, 0u64, (rows, tmp_20)))
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
