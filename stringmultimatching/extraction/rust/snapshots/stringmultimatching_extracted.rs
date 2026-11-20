#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

pub struct bstate {
  pub bact: Array<Int63>,
  pub bcur: Array<Int63>,
  pub bw: Int63,
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
  pub tchr: Array<Int63>,
  pub tpar: Array<Int63>,
  pub tfc: Array<Int63>,
  pub tns: Array<Int63>,
  pub tdep: Array<Int63>,
  pub tn: Int63,
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

pub type char63 = Int63;

pub type uint = Int63;

// Rocq: Stringmultimatching.stringmultimatching_implem.bdec
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

// Rocq: Stringmultimatching.stringmultimatching_implem.sums
// Variant: uncurried
pub fn sums_1(pats: Array<rocq_string::RocqString>, m: Int63, i: Int63, P: Int63, L: Int63) -> (Int63, Int63) {
  sums(pats, m, i, P, L, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.sums (local: sums)
// Variant: uncurried, lifted
pub fn sums(pats: Array<rocq_string::RocqString>, m: Int63, i: Int63, P: Int63, L: Int63, _H: ()) -> (Int63, Int63) {
  let tmp = i < m;
  match bdec(tmp) {
    sumbool::left => {
      let pats_ref = &pats;
      let tmp_1 = pats_ref.get_cloned(i);
      let l = length(tmp_1);
      let tmp_2 = i + int63!(1);
      let tmp_3 = P + l;
      let tmp_4 = if L < l {
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
pub fn iota_1(m: Int63, i: Int63, a_1: Array<Int63>) -> Array<Int63> {
  iota(m, i, a_1, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.iota (local: iota)
// Variant: uncurried, lifted
pub fn iota(m: Int63, i: Int63, a_1: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < m;
  match bdec(tmp) {
    sumbool::left => {
      iota(m, i + int63!(1), a_1.set(i, i), ())
    },
    sumbool::right => {
      a_1
    },
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.bact
pub fn bact(b_1: Rc<bstate>) -> Array<Int63> {
  let b_bact_clone = Clone::clone(&b_1.bact);
  std::mem::drop(b_1);
  b_bact_clone
}

// Rocq: Stringmultimatching.stringmultimatching_implem.bcur
pub fn bcur(b_1: Rc<bstate>) -> Array<Int63> {
  let b_bcur_clone = Clone::clone(&b_1.bcur);
  std::mem::drop(b_1);
  b_bcur_clone
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tfc
pub fn tfc_owned(t: Rc<trie>) -> Array<Int63> {
  let t_tfc_clone = Clone::clone(&t.tfc);
  std::mem::drop(t);
  t_tfc_clone
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tfc
// Variant: borrowed
pub fn tfc(t: &Rc<trie>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tfc)
}

// Rocq: Stringmultimatching.stringmultimatching_implem.lookup_from
// Variant: uncurried
pub fn lookup_from_1(chr: Array<Int63>, ns: Array<Int63>, c: Int63, v: Int63) -> Int63 {
  lookup_from(chr, ns, c, v, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.lookup_from (local: lookup_from)
// Variant: uncurried, lifted
pub fn lookup_from(chr: Array<Int63>, ns: Array<Int63>, c: Int63, v: Int63, _H: ()) -> Int63 {
  let tmp = v == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      std::mem::drop(chr);
      std::mem::drop(ns);
      int63!(0)
    },
    sumbool::right => {
      let tmp_1 = chr.get_cloned(v);
      if tmp_1 == c {
        std::mem::drop(chr);
        std::mem::drop(ns);
        v
      } else {
        let nx = ns.get_cloned(v);
        let tmp_2 = nx < v;
        match bdec(tmp_2) {
          sumbool::left => {
            lookup_from(chr, ns, c, nx, ())
          },
          sumbool::right => {
            std::mem::drop(chr);
            std::mem::drop(ns);
            int63!(0)
          },
        }
      }
    },
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tchr
pub fn tchr_owned(t: Rc<trie>) -> Array<Int63> {
  let t_tchr_clone = Clone::clone(&t.tchr);
  std::mem::drop(t);
  t_tchr_clone
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tchr
// Variant: borrowed
pub fn tchr(t: &Rc<trie>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tchr)
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tns
pub fn tns_owned(t: Rc<trie>) -> Array<Int63> {
  let t_tns_clone = Clone::clone(&t.tns);
  std::mem::drop(t);
  t_tns_clone
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tns
// Variant: borrowed
pub fn tns(t: &Rc<trie>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tns)
}

// Rocq: Stringmultimatching.stringmultimatching_implem.lookup
// Variant: borrowed, uncurried
pub fn lookup(t: &Rc<trie>, u: Int63, c: Int63) -> Int63 {
  let u_1 = u;
  let c_1 = c;
  let tmp = tfc(t);
  let v = tmp.get_cloned(u_1);
  std::mem::drop(tmp);
  lookup_from_1(tchr(t), tns(t), c_1, v)
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tn
// Variant: borrowed
pub fn tn(t: &Rc<trie>) -> Int63 {
  let tmp = t;
  Clone::clone(&tmp.tn)
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tdep
pub fn tdep(t: Rc<trie>) -> Array<Int63> {
  let t_tdep_clone = Clone::clone(&t.tdep);
  std::mem::drop(t);
  t_tdep_clone
}

// Rocq: Stringmultimatching.stringmultimatching_implem.tpar
pub fn tpar(t: Rc<trie>) -> Array<Int63> {
  let t_tpar_clone = Clone::clone(&t.tpar);
  std::mem::drop(t);
  t_tpar_clone
}

// Rocq: Stringmultimatching.stringmultimatching_implem.add_child
// Variant: uncurried
pub fn add_child(t: Rc<trie>, u: Int63, c: Int63) -> (Rc<trie>, Int63) {
  let v = lookup(&t, u, c);
  if v == int63!(0) {
    let n = tn(&t);
    let t_clone = Rc::clone(&t);
    let tmp = tfc_owned(t_clone);
    let old = tmp.get_cloned(u);
    std::mem::drop(tmp);
    let t_clone_1 = Rc::clone(&t);
    let tmp_1 = tdep(t_clone_1);
    let du = tmp_1.get_cloned(u);
    std::mem::drop(tmp_1);
    let t_clone_2 = Rc::clone(&t);
    let tmp_2 = tchr_owned(t_clone_2).set(n, c);
    let t_clone_3 = Rc::clone(&t);
    let tmp_3 = tpar(t_clone_3).set(n, u);
    let t_clone_4 = Rc::clone(&t);
    let tmp_4 = tfc_owned(t_clone_4).set(u, n);
    let t_clone_5 = Rc::clone(&t);
    (Rc::new(trie { tchr: tmp_2, tpar: tmp_3, tfc: tmp_4, tns: tns_owned(t_clone_5).set(n, old), tdep: tdep(t).set(n, du + int63!(1)), tn: n + int63!(1) }), n)
  } else {
    (t, v)
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.bt
pub fn bt(b_1: Rc<bstate>) -> Rc<trie> {
  let b_bt_clone = Rc::clone(&b_1.bt);
  std::mem::drop(b_1);
  b_bt_clone
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: rocq_string::RocqString, v1: Int63) -> Int63 {
  let tmp = v0.get(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Stringmultimatching.stringmultimatching_implem.bw
pub fn bw_owned(b_1: Rc<bstate>) -> Int63 {
  let b_bw_clone = Clone::clone(&b_1.bw);
  std::mem::drop(b_1);
  b_bw_clone
}

// Rocq: Stringmultimatching.stringmultimatching_implem.bw
// Variant: borrowed
pub fn bw(b_1: &Rc<bstate>) -> Int63 {
  let tmp = b_1;
  Clone::clone(&tmp.bw)
}

// Rocq: Stringmultimatching.stringmultimatching_implem.round_loop
// Variant: uncurried
pub fn round_loop_1(pats: Array<rocq_string::RocqString>, d: Int63, na: Int63, k: Int63, st: Rc<bstate>) -> Rc<bstate> {
  round_loop(pats, d, na, k, st, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.round_loop (local: round_loop)
// Variant: uncurried, lifted
pub fn round_loop(pats: Array<rocq_string::RocqString>, d: Int63, na: Int63, k: Int63, st: Rc<bstate>, _H: ()) -> Rc<bstate> {
  let tmp = k < na;
  match bdec(tmp) {
    sumbool::left => {
      let st_clone = Rc::clone(&st);
      let act = bact(st_clone);
      let i = act.get_cloned(k);
      let pats_ref = &pats;
      let s = pats_ref.get_cloned(i);
      let st_clone_1 = Rc::clone(&st);
      let cur = bcur(st_clone_1);
      let st_clone_2 = Rc::clone(&st);
      let tmp_1 = bt(st_clone_2);
      let tmp_2 = cur.get_cloned(i);
      let s_clone = Clone::clone(&s);
      let tv = add_child(tmp_1, tmp_2, get(s_clone, d));
      let tv_clone = Clone::clone(&tv);
      let cur_ = cur.set(i, snd::<Rc<trie>, Int63>(tv_clone));
      let w = bw_owned(st);
      let tmp_3 = d + int63!(1);
      let tmp_4 = length(s);
      if tmp_3 < tmp_4 {
        round_loop(pats, d, na, k + int63!(1), Rc::new(bstate { bact: act.set(w, i), bcur: cur_, bw: w + int63!(1), bt: fst::<Rc<trie>, Int63>(tv) }), ())
      } else {
        round_loop(pats, d, na, k + int63!(1), Rc::new(bstate { bact: act, bcur: cur_, bw: w, bt: fst::<Rc<trie>, Int63>(tv) }), ())
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
pub fn rounds_1(pats: Array<rocq_string::RocqString>, L: Int63, d: Int63, st: Rc<bstate>) -> Rc<bstate> {
  rounds(pats, L, d, st, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.rounds (local: rounds)
// Variant: uncurried, lifted
pub fn rounds(pats: Array<rocq_string::RocqString>, L: Int63, d: Int63, st: Rc<bstate>, _H: ()) -> Rc<bstate> {
  let tmp = d < L;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = bw(&st);
      let st_clone = Rc::clone(&st);
      let tmp_2 = bact(st_clone);
      let st_clone_1 = Rc::clone(&st);
      let tmp_3 = Rc::new(bstate { bact: tmp_2, bcur: bcur(st_clone_1), bw: int63!(0), bt: bt(st) });
      let pats_clone = Clone::clone(&pats);
      let st_ = round_loop_1(pats_clone, d, tmp_1, int63!(0), tmp_3);
      rounds(pats, L, d + int63!(1), st_, ())
    },
    sumbool::right => {
      std::mem::drop(pats);
      st
    },
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.plist_loop
// Variant: uncurried
pub fn plist_loop_1(cur: Array<Int63>, m: Int63, i: Int63, fp: Array<Int63>, np: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  plist_loop(cur, m, i, fp, np, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.plist_loop (local: plist_loop)
// Variant: uncurried, lifted
pub fn plist_loop(cur: Array<Int63>, m: Int63, i: Int63, fp: Array<Int63>, np: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = i < m;
  match bdec(tmp) {
    sumbool::left => {
      let v = cur.get_cloned(i);
      let old = fp.get_cloned(v);
      plist_loop(cur, m, i + int63!(1), fp.set(v, i + int63!(1)), np.set(i + int63!(1), old), ())
    },
    sumbool::right => {
      std::mem::drop(cur);
      (fp, np)
    },
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.walk
// Variant: uncurried
pub fn walk_1(t: Rc<trie>, fl: Array<Int63>, c: Int63, x: Int63) -> Int63 {
  walk(t, fl, c, x, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(t: Rc<trie>, fl: Array<Int63>, c: Int63, x: Int63, _H: ()) -> Int63 {
  let y = lookup(&t, x, c);
  let tmp = y == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = x == int63!(0);
      match bdec(tmp_1) {
        sumbool::left => {
          std::mem::drop(fl);
          std::mem::drop(t);
          int63!(0)
        },
        sumbool::right => {
          let x_ = fl.get_cloned(x);
          let tmp_2 = x_ < x;
          match bdec(tmp_2) {
            sumbool::left => {
              walk(t, fl, c, x_, ())
            },
            sumbool::right => {
              std::mem::drop(fl);
              std::mem::drop(t);
              int63!(0)
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
pub fn fail_loop_1(t: Rc<trie>, fp: Array<Int63>, N: Int63, v: Int63, fl: Array<Int63>, out: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  fail_loop(t, fp, N, v, fl, out, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.fail_loop (local: fail_loop)
// Variant: uncurried, lifted
pub fn fail_loop(t: Rc<trie>, fp: Array<Int63>, N: Int63, v: Int63, fl: Array<Int63>, out: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = v < N;
  match bdec(tmp) {
    sumbool::left => {
      let t_clone = Rc::clone(&t);
      let tmp_1 = tpar(t_clone);
      let u = tmp_1.get_cloned(v);
      let t_clone_1 = Rc::clone(&t);
      let tmp_2 = tchr_owned(t_clone_1);
      let c = tmp_2.get_cloned(v);
      let tmp_3 = int63!(0);
      let f = if u == tmp_3 {
        int63!(0)
      } else {
        let x = fl.get_cloned(u);
        let t_clone_2 = Rc::clone(&t);
        let fl_clone = Clone::clone(&fl);
        walk_1(t_clone_2, fl_clone, c, x)
      };
      let tmp_4 = fp.get_cloned(f);
      let tmp_5 = int63!(0);
      let o = if tmp_4 == tmp_5 {
        std::mem::drop(tmp_2);
        std::mem::drop(tmp_1);
        out.get_cloned(f)
      } else {
        std::mem::drop(tmp_2);
        std::mem::drop(tmp_1);
        f
      };
      fail_loop(t, fp, N, v + int63!(1), fl.set(v, f), out.set(v, o), ())
    },
    sumbool::right => {
      std::mem::drop(t);
      std::mem::drop(fp);
      (fl, out)
    },
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.emit_list
// Variant: uncurried
pub fn emit_list_1<Sx: Clone + 'static>(f: Rc<dyn Fn(Sx, Int63, Int63) -> Sx>, np: Array<Int63>, p: Int63, e: Int63, s: Sx) -> Sx {
  emit_list::<Sx>(f, np, p, e, s, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.emit_list (local: emit_list)
// Variant: uncurried, lifted
pub fn emit_list<Sx: Clone + 'static>(f: Rc<dyn Fn(Sx, Int63, Int63) -> Sx>, np: Array<Int63>, p: Int63, e: Int63, s: Sx, _H: ()) -> Sx {
  let tmp = e == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      std::mem::drop(f);
      std::mem::drop(np);
      s
    },
    sumbool::right => {
      let tmp_1 = e - int63!(1);
      let f_ref: &Rc<dyn Fn(Sx, Int63, Int63) -> Sx> = &f;
      let s_ = f_ref(s, tmp_1, p);
      let e_ = np.get_cloned(e);
      let tmp_2 = e_ < e;
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
pub fn emit_chain_1<Sx: Clone + 'static>(f: Rc<dyn Fn(Sx, Int63, Int63) -> Sx>, t: Rc<trie>, out: Array<Int63>, fp: Array<Int63>, np: Array<Int63>, je: Int63, x: Int63, s: Sx) -> Sx {
  emit_chain::<Sx>(fp, t, f, np, out, je, x, s, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.emit_chain (local: emit_chain)
// Variant: uncurried, lifted
pub fn emit_chain<Sx: Clone + 'static>(fp: Array<Int63>, t: Rc<trie>, f: Rc<dyn Fn(Sx, Int63, Int63) -> Sx>, np: Array<Int63>, out: Array<Int63>, je: Int63, x: Int63, s: Sx, _H: ()) -> Sx {
  let tmp = x == int63!(0);
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
      let e = fp.get_cloned(x);
      let t_clone = Rc::clone(&t);
      let tmp_1 = tdep(t_clone);
      let tmp_2 = tmp_1.get_cloned(x);
      let tmp_3 = je - tmp_2;
      let f_clone: Rc<dyn Fn(Sx, Int63, Int63) -> Sx> = Rc::clone(&f);
      let np_clone = Clone::clone(&np);
      let s_ = emit_list_1::<Sx>(f_clone, np_clone, tmp_3, e, s);
      let o = out.get_cloned(x);
      let tmp_4 = o < x;
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
pub fn scan_1<Sx: Clone + 'static>(f: Rc<dyn Fn(Sx, Int63, Int63) -> Sx>, t: Rc<trie>, fl: Array<Int63>, out: Array<Int63>, fp: Array<Int63>, np: Array<Int63>, txt: rocq_string::RocqString, n: Int63, j: Int63, st: Int63, s: Sx) -> Sx {
  scan::<Sx>(txt, t, fl, f, out, fp, np, n, j, st, s, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan<Sx: Clone + 'static>(txt: rocq_string::RocqString, t: Rc<trie>, fl: Array<Int63>, f: Rc<dyn Fn(Sx, Int63, Int63) -> Sx>, out: Array<Int63>, fp: Array<Int63>, np: Array<Int63>, n: Int63, j: Int63, st: Int63, s: Sx, _H: ()) -> Sx {
  let tmp = j < n;
  match bdec(tmp) {
    sumbool::left => {
      let txt_clone = Clone::clone(&txt);
      let tmp_1 = get(txt_clone, j);
      let t_clone = Rc::clone(&t);
      let fl_clone = Clone::clone(&fl);
      let st_ = walk_1(t_clone, fl_clone, tmp_1, st);
      let tmp_2 = j + int63!(1);
      let f_clone: Rc<dyn Fn(Sx, Int63, Int63) -> Sx> = Rc::clone(&f);
      let t_clone_1 = Rc::clone(&t);
      let out_clone = Clone::clone(&out);
      let fp_clone = Clone::clone(&fp);
      let np_clone = Clone::clone(&np);
      let s_ = emit_chain_1::<Sx>(f_clone, t_clone_1, out_clone, fp_clone, np_clone, tmp_2, st_, s);
      scan::<Sx>(txt, t, fl, f, out, fp, np, n, j + int63!(1), st_, s_, ())
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
pub fn f_cnt(cnt: Array<Int63>, i: Int63, _p: Int63) -> Array<Int63> {
  let c = cnt.get_cloned(i);
  cnt.set(i, c + int63!(1))
}

// Rocq: Stringmultimatching.stringmultimatching_implem.alloc_loop
// Variant: uncurried
pub fn alloc_loop_1(cnt: Array<Int63>, m: Int63, i: Int63, rows: Array<Array<Int63>>) -> Array<Array<Int63>> {
  alloc_loop(cnt, m, i, rows, ())
}

// Rocq: Stringmultimatching.stringmultimatching_implem.alloc_loop (local: alloc_loop)
// Variant: uncurried, lifted
pub fn alloc_loop(cnt: Array<Int63>, m: Int63, i: Int63, rows: Array<Array<Int63>>, _H: ()) -> Array<Array<Int63>> {
  let tmp = i < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = cnt.get_cloned(i);
      alloc_loop(cnt, m, tmp_1, rows.set(i, Array::<Int63>::make(tmp_2, int63!(0))), ())
    },
    sumbool::right => {
      std::mem::drop(cnt);
      rows
    },
  }
}

// Rocq: Stringmultimatching.stringmultimatching_implem.f_fill
// Variant: uncurried
pub fn f_fill(st: (Array<Array<Int63>>, Array<Int63>), i: Int63, p: Int63) -> (Array<Array<Int63>>, Array<Int63>) {
  let st_clone = Clone::clone(&st);
  let rows = fst::<Array<Array<Int63>>, Array<Int63>>(st_clone);
  let ptr = snd::<Array<Array<Int63>>, Array<Int63>>(st);
  let k = ptr.get_cloned(i);
  let rows_clone = Clone::clone(&rows);
  let tmp = &rows_clone;
  let row = tmp.get_cloned(i);
  std::mem::drop(rows_clone);
  (rows.set(i, row.set(k, p)), ptr.set(i, k + int63!(1)))
}

// Rocq: Stringmultimatching.stringmultimatching_implem.multimatch_impl
// Variant: uncurried
pub fn multimatch_impl(pats: Array<rocq_string::RocqString>, txt: rocq_string::RocqString) -> Array<Array<Int63>> {
  let m = pats.length();
  let pats_clone = Clone::clone(&pats);
  let PL = sums_1(pats_clone, m, int63!(0), int63!(0), int63!(0));
  let PL_clone = Clone::clone(&PL);
  let cap = fst::<Int63, Int63>(PL_clone) + int63!(1);
  let L = snd::<Int63, Int63>(PL);
  let t0 = Rc::new(trie { tchr: Array::<Int63>::make(cap, int63!(0)), tpar: Array::<Int63>::make(cap, int63!(0)), tfc: Array::<Int63>::make(cap, int63!(0)), tns: Array::<Int63>::make(cap, int63!(0)), tdep: Array::<Int63>::make(cap, int63!(0)), tn: int63!(1) });
  let tmp = Array::<Int63>::make(m, int63!(0));
  let act0 = iota_1(m, int63!(0), tmp);
  let st = rounds_1(pats, L, int63!(0), Rc::new(bstate { bact: act0, bcur: Array::<Int63>::make(m, int63!(0)), bw: m, bt: t0 }));
  let st_clone = Rc::clone(&st);
  let t = bt(st_clone);
  let tmp_1 = bcur(st);
  let tmp_2 = Array::<Int63>::make(cap, int63!(0));
  let tmp_3 = m + int63!(1);
  let pl = plist_loop_1(tmp_1, m, int63!(0), tmp_2, Array::<Int63>::make(tmp_3, int63!(0)));
  let pl_clone = Clone::clone(&pl);
  let fp = fst::<Array<Int63>, Array<Int63>>(pl_clone);
  let np = snd::<Array<Int63>, Array<Int63>>(pl);
  let tmp_4 = tn(&t);
  let tmp_5 = Array::<Int63>::make(cap, int63!(0));
  let tmp_6 = Array::<Int63>::make(cap, int63!(0));
  let t_clone = Rc::clone(&t);
  let fp_clone = Clone::clone(&fp);
  let fo = fail_loop_1(t_clone, fp_clone, tmp_4, int63!(1), tmp_5, tmp_6);
  let fo_clone = Clone::clone(&fo);
  let fl = fst::<Array<Int63>, Array<Int63>>(fo_clone);
  let out = snd::<Array<Int63>, Array<Int63>>(fo);
  let txt_clone = Clone::clone(&txt);
  let n = length(txt_clone);
  let tmp_7: fn(Array<Int63>, Int63, Int63) -> Array<Int63> = f_cnt;
  let tmp_8: Rc<dyn Fn(Array<Int63>, Int63, Int63) -> Array<Int63>> = Rc::new(tmp_7);
  let tmp_9 = Array::<Int63>::make(m, int63!(0));
  let t_clone_1 = Rc::clone(&t);
  let fl_clone = Clone::clone(&fl);
  let out_clone = Clone::clone(&out);
  let fp_clone_1 = Clone::clone(&fp);
  let np_clone = Clone::clone(&np);
  let txt_clone_1 = Clone::clone(&txt);
  let cnt = scan_1::<Array<Int63>>(tmp_8, t_clone_1, fl_clone, out_clone, fp_clone_1, np_clone, txt_clone_1, n, int63!(0), int63!(0), tmp_9);
  let tmp_10 = Array::<Array<Int63>>::make(m, Array::<Int63>::make(int63!(0), int63!(0)));
  let rows = alloc_loop_1(cnt, m, int63!(0), tmp_10);
  let tmp_11: fn((Array<Array<Int63>>, Array<Int63>), Int63, Int63) -> (Array<Array<Int63>>, Array<Int63>) = f_fill;
  let tmp_12: Rc<dyn Fn((Array<Array<Int63>>, Array<Int63>), Int63, Int63) -> (Array<Array<Int63>>, Array<Int63>)> = Rc::new(tmp_11);
  fst::<Array<Array<Int63>>, Array<Int63>>(scan_1::<(Array<Array<Int63>>, Array<Int63>)>(tmp_12, t, fl, out, fp, np, txt, n, int63!(0), int63!(0), (rows, Array::<Int63>::make(m, int63!(0)))))
}
