#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

pub struct d3 {
  pub gord: Array<Int63>,
  pub gn: Int63,
  pub av: Array<rocq_string::RocqString>,
  pub an: Int63,
}

impl Clone for d3 {
  fn clone(&self) -> Self {
    match self {
      d3 { gord: __field0, gn: __field1, av: __field2, an: __field3 } => d3 { gord: Clone::clone(__field0), gn: Clone::clone(__field1), av: Clone::clone(__field2), an: Clone::clone(__field3) },
    }
  }
}

pub struct d2 {
  pub lb: Array<Int63>,
  pub sk: Array<Int63>,
  pub sq: Int63,
  pub ii: Int63,
  pub cc: Int63,
}

impl Clone for d2 {
  fn clone(&self) -> Self {
    match self {
      d2 { lb: __field0, sk: __field1, sq: __field2, ii: __field3, cc: __field4 } => d2 { lb: Clone::clone(__field0), sk: Clone::clone(__field1), sq: Clone::clone(__field2), ii: Clone::clone(__field3), cc: Clone::clone(__field4) },
    }
  }
}

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

pub struct d1 {
  pub mk: Array<Int63>,
  pub sv: Array<Int63>,
  pub sc: Array<Int63>,
  pub po: Array<Int63>,
  pub sp: Int63,
  pub np: Int63,
  pub rt: Int63,
}

impl Clone for d1 {
  fn clone(&self) -> Self {
    match self {
      d1 { mk: __field0, sv: __field1, sc: __field2, po: __field3, sp: __field4, np: __field5, rt: __field6 } => d1 { mk: Clone::clone(__field0), sv: Clone::clone(__field1), sc: Clone::clone(__field2), po: Clone::clone(__field3), sp: Clone::clone(__field4), np: Clone::clone(__field5), rt: Clone::clone(__field6) },
    }
  }
}

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<std::cmp::Ordering>; };

pub struct hstate {
  pub ht: Array<Int63>,
  pub hn: Array<rocq_string::RocqString>,
  pub hc: Int63,
}

impl Clone for hstate {
  fn clone(&self) -> Self {
    match self {
      hstate { ht: __field0, hn: __field1, hc: __field2 } => hstate { ht: Clone::clone(__field0), hn: Clone::clone(__field1), hc: Clone::clone(__field2) },
    }
  }
}

pub type char63 = Int63;

// Rocq: Loopycabdrivers.loopycabdrivers_implem.hsize
pub fn hsize() -> Int63 {
  int63!(65536)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.hmask
pub fn hmask() -> Int63 {
  int63!(65535)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.empty_str
pub fn empty_str(_v0: ()) -> rocq_string::RocqString {
  __rocq_global_281.with(Clone::clone)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.ht
pub fn ht(h: Rc<hstate>) -> Array<Int63> {
  let h_ht_clone = Clone::clone(&h.ht);
  std::mem::drop(h);
  h_ht_clone
}

// Rocq: Corelib.Strings.PrimString.compare
// Variant: uncurried
pub fn compare(v0: rocq_string::RocqString, v1: rocq_string::RocqString) -> std::cmp::Ordering {
  let tmp = v0.compare(&v1);
  std::mem::drop(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.probe
// Variant: uncurried
pub fn probe_1(tbl: Array<Int63>, names: Array<rocq_string::RocqString>, s: rocq_string::RocqString, T: Int63, p: Int63) -> (Int63, bool) {
  probe(tbl, names, s, T, p, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.probe (local: probe)
// Variant: uncurried, lifted
pub fn probe(tbl: Array<Int63>, names: Array<rocq_string::RocqString>, s: rocq_string::RocqString, T: Int63, p: Int63, _H: ()) -> (Int63, bool) {
  let tmp = p < T;
  match bdec(tmp) {
    sumbool::left => {
      let e = tbl.get_cloned(p);
      if e == int63!(0) {
        std::mem::drop(tbl);
        std::mem::drop(names);
        std::mem::drop(s);
        (p, false)
      } else {
        let tmp_1 = e - int63!(1);
        let names_ref = &names;
        let tmp_2 = names_ref.get_cloned(tmp_1);
        let s_clone = Clone::clone(&s);
        match compare(tmp_2, s_clone) {
          std::cmp::Ordering::Equal => {
            std::mem::drop(tbl);
            std::mem::drop(s);
            std::mem::drop(names);
            (p, true)
          },
          std::cmp::Ordering::Less => {
            probe(tbl, names, s, T, p + int63!(1), ())
          },
          std::cmp::Ordering::Greater => {
            probe(tbl, names, s, T, p + int63!(1), ())
          },
        }
      }
    },
    sumbool::right => {
      std::mem::drop(tbl);
      std::mem::drop(names);
      std::mem::drop(s);
      (p, false)
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.hn
pub fn hn(h: Rc<hstate>) -> Array<rocq_string::RocqString> {
  let h_hn_clone = Clone::clone(&h.hn);
  std::mem::drop(h);
  h_hn_clone
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: rocq_string::RocqString, v1: Int63) -> Int63 {
  let tmp = v0.get(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.hloop
// Variant: uncurried
pub fn hloop_1(s: rocq_string::RocqString, n: Int63, k: Int63, h: Int63) -> Int63 {
  hloop(s, n, k, h, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.hloop (local: hloop)
// Variant: uncurried, lifted
pub fn hloop(s: rocq_string::RocqString, n: Int63, k: Int63, h: Int63, _H: ()) -> Int63 {
  let tmp = k < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = k + int63!(1);
      let tmp_2 = h * int63!(31);
      let s_clone = Clone::clone(&s);
      hloop(s, n, tmp_1, tmp_2 + get(s_clone, k), ())
    },
    sumbool::right => {
      std::mem::drop(s);
      h
    },
  }
}

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: rocq_string::RocqString) -> Int63 {
  let tmp = v0.length();
  std::mem::drop(v0);
  tmp
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.hash
pub fn hash(s: rocq_string::RocqString) -> Int63 {
  let s_clone = Clone::clone(&s);
  hloop_1(s, length(s_clone), int63!(0), int63!(7)) & __rocq_global_280.with(Clone::clone)
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

// Rocq: Loopycabdrivers.loopycabdrivers_implem.hc
pub fn hc_owned(h: Rc<hstate>) -> Int63 {
  let h_hc_clone = Clone::clone(&h.hc);
  std::mem::drop(h);
  h_hc_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.hc
// Variant: borrowed
pub fn hc(h: &Rc<hstate>) -> Int63 {
  let tmp = h;
  Clone::clone(&tmp.hc)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.lookup
// Variant: uncurried
pub fn lookup(st: Rc<hstate>, s: rocq_string::RocqString) -> (Rc<hstate>, Int63) {
  let st_clone = Rc::clone(&st);
  let tbl = ht(st_clone);
  let T = tbl.length();
  let st_clone_1 = Rc::clone(&st);
  let tmp = hn(st_clone_1);
  let s_clone = Clone::clone(&s);
  let tmp_1 = hash(s_clone);
  let tbl_clone = Clone::clone(&tbl);
  let s_clone_1 = Clone::clone(&s);
  let pf = probe_1(tbl_clone, tmp, s_clone_1, T, tmp_1);
  let pf_clone = Clone::clone(&pf);
  let p = fst::<Int63, bool>(pf_clone);
  if snd::<Int63, bool>(pf) {
    std::mem::drop(s);
    let tmp_2 = tbl.get_cloned(p);
    std::mem::drop(tbl);
    (st, tmp_2 - int63!(1))
  } else {
    let tmp_3 = hc(&st);
    let tmp_4 = tbl.set(p, tmp_3 + int63!(1));
    let st_clone_2 = Rc::clone(&st);
    let tmp_5 = hn(st_clone_2);
    let tmp_6 = hc(&st);
    let tmp_7 = tmp_5.set(tmp_6, s);
    let tmp_8 = hc(&st);
    (Rc::new(hstate { ht: tmp_4, hn: tmp_7, hc: tmp_8 + int63!(1) }), hc_owned(st))
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.idloop
// Variant: uncurried
pub fn idloop_1(x: Array<rocq_string::RocqString>, y: Array<rocq_string::RocqString>, m: Int63, k: Int63, st: Rc<hstate>, is: Array<Int63>, id: Array<Int63>) -> ((Rc<hstate>, Array<Int63>), Array<Int63>) {
  idloop(x, y, m, k, st, is, id, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.idloop (local: idloop)
// Variant: uncurried, lifted
pub fn idloop(x: Array<rocq_string::RocqString>, y: Array<rocq_string::RocqString>, m: Int63, k: Int63, st: Rc<hstate>, is: Array<Int63>, id: Array<Int63>, _H: ()) -> ((Rc<hstate>, Array<Int63>), Array<Int63>) {
  let tmp = k < m;
  match bdec(tmp) {
    sumbool::left => {
      let x_ref = &x;
      let tmp_1 = x_ref.get_cloned(k);
      let r1 = lookup(st, tmp_1);
      let r1_clone = Clone::clone(&r1);
      let tmp_2 = fst::<Rc<hstate>, Int63>(r1_clone);
      let y_ref = &y;
      let tmp_3 = y_ref.get_cloned(k);
      let r2 = lookup(tmp_2, tmp_3);
      let tmp_4 = k + int63!(1);
      let r2_clone = Clone::clone(&r2);
      idloop(x, y, m, tmp_4, fst::<Rc<hstate>, Int63>(r2_clone), is.set(k, snd::<Rc<hstate>, Int63>(r1)), id.set(k, snd::<Rc<hstate>, Int63>(r2)), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      ((st, is), id)
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.cnt_loop
// Variant: uncurried
pub fn cnt_loop_1(es: Rc<dyn Fn(Int63) -> Int63>, m: Int63, k: Int63, cnt: Array<Int63>) -> Array<Int63> {
  cnt_loop(es, m, k, cnt, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.cnt_loop (local: cnt_loop)
// Variant: uncurried, lifted
pub fn cnt_loop(es: Rc<dyn Fn(Int63) -> Int63>, m: Int63, k: Int63, cnt: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = k < m;
  match bdec(tmp) {
    sumbool::left => {
      let es_ref: &Rc<dyn Fn(Int63) -> Int63> = &es;
      let u = es_ref(k);
      let tmp_1 = k + int63!(1);
      let tmp_2 = cnt.get_cloned(u);
      cnt_loop(es, m, tmp_1, cnt.set(u, tmp_2 + int63!(1)), ())
    },
    sumbool::right => {
      std::mem::drop(es);
      cnt
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.pre_loop
// Variant: uncurried
pub fn pre_loop_1(cnt: Array<Int63>, V: Int63, u: Int63, off: Array<Int63>) -> Array<Int63> {
  pre_loop(cnt, V, u, off, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.pre_loop (local: pre_loop)
// Variant: uncurried, lifted
pub fn pre_loop(cnt: Array<Int63>, V: Int63, u: Int63, off: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = u < V;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = u + int63!(1);
      let tmp_2 = u + int63!(1);
      let tmp_3 = off.get_cloned(u);
      let tmp_4 = cnt.get_cloned(u);
      pre_loop(cnt, V, tmp_1, off.set(tmp_2, tmp_3 + tmp_4), ())
    },
    sumbool::right => {
      std::mem::drop(cnt);
      off
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(es: Rc<dyn Fn(Int63) -> Int63>, ed: Rc<dyn Fn(Int63) -> Int63>, m: Int63, k: Int63, pos: Array<Int63>, adj: Array<Int63>) -> Array<Int63> {
  fill_loop(es, ed, m, k, pos, adj, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(es: Rc<dyn Fn(Int63) -> Int63>, ed: Rc<dyn Fn(Int63) -> Int63>, m: Int63, k: Int63, pos: Array<Int63>, adj: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = k < m;
  match bdec(tmp) {
    sumbool::left => {
      let es_ref: &Rc<dyn Fn(Int63) -> Int63> = &es;
      let u = es_ref(k);
      let p = pos.get_cloned(u);
      let tmp_1 = k + int63!(1);
      let tmp_2 = pos.set(u, p + int63!(1));
      let ed_ref: &Rc<dyn Fn(Int63) -> Int63> = &ed;
      let tmp_3 = ed_ref(k);
      fill_loop(es, ed, m, tmp_1, tmp_2, adj.set(p, tmp_3), ())
    },
    sumbool::right => {
      std::mem::drop(es);
      std::mem::drop(ed);
      std::mem::drop(pos);
      adj
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.csr
// Variant: uncurried
pub fn csr(V: Int63, m: Int63, es: Rc<dyn Fn(Int63) -> Int63>, ed: Rc<dyn Fn(Int63) -> Int63>) -> (Array<Int63>, Array<Int63>) {
  let tmp = Array::<Int63>::make(V, int63!(0));
  let es_clone: Rc<dyn Fn(Int63) -> Int63> = Rc::clone(&es);
  let cnt = cnt_loop_1(es_clone, m, int63!(0), tmp);
  let tmp_1 = V + int63!(1);
  let off = pre_loop_1(cnt, V, int63!(0), Array::<Int63>::make(tmp_1, int63!(0)));
  let off_ref = &off;
  let tmp_2 = off_ref.copy();
  let tmp_3 = Array::<Int63>::make(m, int63!(0));
  let adj = fill_loop_1(es, ed, m, int63!(0), tmp_2, tmp_3);
  (off, adj)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.sp
// Variant: borrowed
pub fn sp(d: &Rc<d1>) -> Int63 {
  let tmp = d;
  Clone::clone(&tmp.sp)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.sv
pub fn sv_owned(d: Rc<d1>) -> Array<Int63> {
  let d_sv_clone = Clone::clone(&d.sv);
  std::mem::drop(d);
  d_sv_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.sv
// Variant: borrowed
pub fn sv(d: &Rc<d1>) -> Array<Int63> {
  let tmp = d;
  Clone::clone(&tmp.sv)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.scan
// Variant: uncurried
pub fn scan_1(mark: Array<Int63>, adj: Array<Int63>, e: Int63, j: Int63) -> Int63 {
  scan(mark, adj, e, j, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(mark: Array<Int63>, adj: Array<Int63>, e: Int63, j: Int63, _H: ()) -> Int63 {
  let tmp = j < e;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = adj.get_cloned(j);
      let tmp_2 = mark.get_cloned(tmp_1);
      if tmp_2 == int63!(0) {
        std::mem::drop(adj);
        std::mem::drop(mark);
        j
      } else {
        scan(mark, adj, e, j + int63!(1), ())
      }
    },
    sumbool::right => {
      std::mem::drop(mark);
      std::mem::drop(adj);
      e
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.mk
pub fn mk_owned(d: Rc<d1>) -> Array<Int63> {
  let d_mk_clone = Clone::clone(&d.mk);
  std::mem::drop(d);
  d_mk_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.mk
// Variant: borrowed
pub fn mk(d: &Rc<d1>) -> Array<Int63> {
  let tmp = d;
  Clone::clone(&tmp.mk)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.sc
pub fn sc_owned(d: Rc<d1>) -> Array<Int63> {
  let d_sc_clone = Clone::clone(&d.sc);
  std::mem::drop(d);
  d_sc_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.sc
// Variant: borrowed
pub fn sc(d: &Rc<d1>) -> Array<Int63> {
  let tmp = d;
  Clone::clone(&tmp.sc)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.po
pub fn po(d: Rc<d1>) -> Array<Int63> {
  let d_po_clone = Clone::clone(&d.po);
  std::mem::drop(d);
  d_po_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.np
pub fn np_owned(d: Rc<d1>) -> Int63 {
  let d_np_clone = Clone::clone(&d.np);
  std::mem::drop(d);
  d_np_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.np
// Variant: borrowed
pub fn np(d: &Rc<d1>) -> Int63 {
  let tmp = d;
  Clone::clone(&tmp.np)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.rt
pub fn rt_owned(d: Rc<d1>) -> Int63 {
  let d_rt_clone = Clone::clone(&d.rt);
  std::mem::drop(d);
  d_rt_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.rt
// Variant: borrowed
pub fn rt(d: &Rc<d1>) -> Int63 {
  let tmp = d;
  Clone::clone(&tmp.rt)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.dfs_step
// Variant: uncurried
pub fn dfs_step(V: Int63, off: Array<Int63>, adj: Array<Int63>, s: Rc<d1>) -> Rc<option<Rc<d1>>> {
  let tmp = sp(&s);
  if int63!(0) < tmp {
    let t = sp(&s) - int63!(1);
    let s_ref = &s;
    let tmp_1 = sv(s_ref);
    let u = tmp_1.get_cloned(t);
    let e = off.get_cloned(u + int63!(1));
    let s_ref_1 = &s;
    let tmp_2 = mk(s_ref_1);
    let s_ref_2 = &s;
    let tmp_3 = sc(s_ref_2);
    let tmp_4 = tmp_3.get_cloned(t);
    let adj_clone = Clone::clone(&adj);
    let j = scan_1(tmp_2, adj_clone, e, tmp_4);
    if j < e {
      std::mem::drop(tmp_3);
      std::mem::drop(tmp_1);
      let w = adj.get_cloned(j);
      std::mem::drop(adj);
      let s_clone = Rc::clone(&s);
      let tmp_5 = mk_owned(s_clone).set(w, int63!(1));
      let s_clone_1 = Rc::clone(&s);
      let tmp_6 = sv_owned(s_clone_1);
      let tmp_7 = sp(&s);
      let tmp_8 = tmp_6.set(tmp_7, w);
      let s_clone_2 = Rc::clone(&s);
      let tmp_9 = sc_owned(s_clone_2).set(t, j + int63!(1));
      let tmp_10 = sp(&s);
      let tmp_11 = off.get_cloned(w);
      std::mem::drop(off);
      let tmp_12 = tmp_9.set(tmp_10, tmp_11);
      let s_clone_3 = Rc::clone(&s);
      let tmp_13 = po(s_clone_3);
      let tmp_14 = sp(&s);
      let tmp_15 = tmp_14 + int63!(1);
      let tmp_16 = np(&s);
      let tmp_17 = Rc::new(d1 { mk: tmp_5, sv: tmp_8, sc: tmp_12, po: tmp_13, sp: tmp_15, np: tmp_16, rt: rt_owned(s) });
      Rc::new(option::<Rc<d1>>::Some(tmp_17))
    } else {
      std::mem::drop(adj);
      std::mem::drop(tmp_3);
      std::mem::drop(off);
      std::mem::drop(tmp_1);
      let s_clone_4 = Rc::clone(&s);
      let tmp_18 = mk_owned(s_clone_4);
      let s_clone_5 = Rc::clone(&s);
      let tmp_19 = sv_owned(s_clone_5);
      let s_clone_6 = Rc::clone(&s);
      let tmp_20 = sc_owned(s_clone_6);
      let s_clone_7 = Rc::clone(&s);
      let tmp_21 = po(s_clone_7);
      let tmp_22 = np(&s);
      let tmp_23 = tmp_21.set(tmp_22, u);
      let tmp_24 = np(&s);
      let tmp_25 = Rc::new(d1 { mk: tmp_18, sv: tmp_19, sc: tmp_20, po: tmp_23, sp: t, np: tmp_24 + int63!(1), rt: rt_owned(s) });
      Rc::new(option::<Rc<d1>>::Some(tmp_25))
    }
  } else {
    let tmp_26 = rt(&s);
    if tmp_26 < V {
      let r = rt(&s);
      let s_ref_3 = &s;
      let tmp_27 = mk(s_ref_3);
      let tmp_28 = tmp_27.get_cloned(r);
      if tmp_28 == int63!(0) {
        std::mem::drop(adj);
        std::mem::drop(tmp_27);
        let s_clone_8 = Rc::clone(&s);
        let tmp_29 = mk_owned(s_clone_8).set(r, int63!(1));
        let s_clone_9 = Rc::clone(&s);
        let tmp_30 = sv_owned(s_clone_9).set(int63!(0), r);
        let s_clone_10 = Rc::clone(&s);
        let tmp_31 = sc_owned(s_clone_10);
        let tmp_32 = int63!(0);
        let tmp_33 = off.get_cloned(r);
        std::mem::drop(off);
        let tmp_34 = tmp_31.set(tmp_32, tmp_33);
        let s_clone_11 = Rc::clone(&s);
        let tmp_35 = Rc::new(d1 { mk: tmp_29, sv: tmp_30, sc: tmp_34, po: po(s_clone_11), sp: int63!(1), np: np_owned(s), rt: r + int63!(1) });
        Rc::new(option::<Rc<d1>>::Some(tmp_35))
      } else {
        std::mem::drop(off);
        std::mem::drop(adj);
        std::mem::drop(tmp_27);
        let s_clone_12 = Rc::clone(&s);
        let tmp_36 = mk_owned(s_clone_12);
        let s_clone_13 = Rc::clone(&s);
        let tmp_37 = sv_owned(s_clone_13);
        let s_clone_14 = Rc::clone(&s);
        let tmp_38 = sc_owned(s_clone_14);
        let s_clone_15 = Rc::clone(&s);
        let tmp_39 = po(s_clone_15);
        let tmp_40 = sp(&s);
        let tmp_41 = Rc::new(d1 { mk: tmp_36, sv: tmp_37, sc: tmp_38, po: tmp_39, sp: tmp_40, np: np_owned(s), rt: r + int63!(1) });
        Rc::new(option::<Rc<d1>>::Some(tmp_41))
      }
    } else {
      std::mem::drop(off);
      std::mem::drop(adj);
      std::mem::drop(s);
      Rc::new(option::<Rc<d1>>::None)
    }
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.dfs
// Variant: uncurried
pub fn dfs_1(V: Int63, off: Array<Int63>, adj: Array<Int63>, s: Rc<d1>, bound: Int63, steps: Int63) -> Array<Int63> {
  dfs(V, off, adj, s, bound, steps, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.dfs (local: dfs)
// Variant: uncurried, lifted
pub fn dfs(V: Int63, off: Array<Int63>, adj: Array<Int63>, s: Rc<d1>, bound: Int63, steps: Int63, _H: ()) -> Array<Int63> {
  let tmp = steps < bound;
  match bdec(tmp) {
    sumbool::left => {
      let off_clone = Clone::clone(&off);
      let adj_clone = Clone::clone(&adj);
      let s_clone = Rc::clone(&s);
      let tmp_1 = dfs_step(V, off_clone, adj_clone, s_clone);
      let (v31, v32) = __rocq_reuse::reset(tmp_1, |__payload| Clone::clone(__payload));
      std::mem::drop(v32);
      match v31 {
        option::Some(v37) => {
          std::mem::drop(s);
          dfs(V, off, adj, v37, bound, steps + int63!(1), ())
        },
        option::None => {
          std::mem::drop(off);
          std::mem::drop(adj);
          po(s)
        },
      }
    },
    sumbool::right => {
      std::mem::drop(off);
      std::mem::drop(adj);
      po(s)
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.sq
// Variant: borrowed
pub fn sq(d: &Rc<d2>) -> Int63 {
  let tmp = d;
  Clone::clone(&tmp.sq)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.sk
pub fn sk(d: Rc<d2>) -> Array<Int63> {
  let d_sk_clone = Clone::clone(&d.sk);
  std::mem::drop(d);
  d_sk_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.push_preds
// Variant: uncurried
pub fn push_preds_1(radj: Array<Int63>, c: Int63, e: Int63, j: Int63, lab: Array<Int63>, stk: Array<Int63>, sp_1: Int63) -> ((Array<Int63>, Array<Int63>), Int63) {
  push_preds(radj, c, e, j, lab, stk, sp_1, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.push_preds (local: push_preds)
// Variant: uncurried, lifted
pub fn push_preds(radj: Array<Int63>, c: Int63, e: Int63, j: Int63, lab: Array<Int63>, stk: Array<Int63>, sp_1: Int63, _H: ()) -> ((Array<Int63>, Array<Int63>), Int63) {
  let tmp = j < e;
  match bdec(tmp) {
    sumbool::left => {
      let w = radj.get_cloned(j);
      let tmp_1 = lab.get_cloned(w);
      if tmp_1 == int63!(0) {
        let tmp_2 = j + int63!(1);
        let tmp_3 = lab.set(w, c);
        push_preds(radj, c, e, tmp_2, tmp_3, stk.set(sp_1, w), sp_1 + int63!(1), ())
      } else {
        push_preds(radj, c, e, j + int63!(1), lab, stk, sp_1, ())
      }
    },
    sumbool::right => {
      std::mem::drop(radj);
      ((lab, stk), sp_1)
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.cc
pub fn cc_owned(d: Rc<d2>) -> Int63 {
  let d_cc_clone = Clone::clone(&d.cc);
  std::mem::drop(d);
  d_cc_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.cc
// Variant: borrowed
pub fn cc(d: &Rc<d2>) -> Int63 {
  let tmp = d;
  Clone::clone(&tmp.cc)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.lb
pub fn lb_owned(d: Rc<d2>) -> Array<Int63> {
  let d_lb_clone = Clone::clone(&d.lb);
  std::mem::drop(d);
  d_lb_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.lb
// Variant: borrowed
pub fn lb(d: &Rc<d2>) -> Array<Int63> {
  let tmp = d;
  Clone::clone(&tmp.lb)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.ii
// Variant: borrowed
pub fn ii(d: &Rc<d2>) -> Int63 {
  let tmp = d;
  Clone::clone(&tmp.ii)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.asg_step
// Variant: uncurried
pub fn asg_step(roff: Array<Int63>, radj: Array<Int63>, post: Array<Int63>, s: Rc<d2>) -> Rc<option<Rc<d2>>> {
  let tmp = sq(&s);
  if int63!(0) < tmp {
    std::mem::drop(post);
    let tmp_1 = sq(&s);
    let t = tmp_1 - int63!(1);
    let s_clone = Rc::clone(&s);
    let tmp_2 = sk(s_clone);
    let u = tmp_2.get_cloned(t);
    std::mem::drop(tmp_2);
    let tmp_3 = cc(&s);
    let tmp_4 = roff.get_cloned(u + int63!(1));
    let tmp_5 = roff.get_cloned(u);
    std::mem::drop(roff);
    let s_clone_1 = Rc::clone(&s);
    let tmp_6 = lb_owned(s_clone_1);
    let s_clone_2 = Rc::clone(&s);
    let r = push_preds_1(radj, tmp_3, tmp_4, tmp_5, tmp_6, sk(s_clone_2), t);
    let r_clone = Clone::clone(&r);
    let tmp_7 = fst::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), Int63>(r_clone));
    let r_clone_1 = Clone::clone(&r);
    let tmp_8 = snd::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), Int63>(r_clone_1));
    let tmp_9 = snd::<(Array<Int63>, Array<Int63>), Int63>(r);
    let tmp_10 = ii(&s);
    let tmp_11 = Rc::new(d2 { lb: tmp_7, sk: tmp_8, sq: tmp_9, ii: tmp_10, cc: cc_owned(s) });
    Rc::new(option::<Rc<d2>>::Some(tmp_11))
  } else {
    let tmp_12 = ii(&s);
    if int63!(0) < tmp_12 {
      let i = ii(&s) - int63!(1);
      let r = post.get_cloned(i);
      let s_ref = &s;
      let tmp_13 = lb(s_ref);
      let tmp_14 = tmp_13.get_cloned(r);
      if tmp_14 == int63!(0) {
        std::mem::drop(roff);
        std::mem::drop(radj);
        std::mem::drop(tmp_13);
        std::mem::drop(post);
        let s_clone_3 = Rc::clone(&s);
        let tmp_15 = lb_owned(s_clone_3);
        let tmp_16 = cc(&s);
        let tmp_17 = tmp_15.set(r, tmp_16 + int63!(1));
        let s_clone_4 = Rc::clone(&s);
        let tmp_18 = Rc::new(d2 { lb: tmp_17, sk: sk(s_clone_4).set(int63!(0), r), sq: int63!(1), ii: i, cc: cc_owned(s) + int63!(1) });
        Rc::new(option::<Rc<d2>>::Some(tmp_18))
      } else {
        std::mem::drop(roff);
        std::mem::drop(radj);
        std::mem::drop(tmp_13);
        std::mem::drop(post);
        let s_clone_5 = Rc::clone(&s);
        let tmp_19 = lb_owned(s_clone_5);
        let s_clone_6 = Rc::clone(&s);
        let tmp_20 = sk(s_clone_6);
        let tmp_21 = sq(&s);
        let tmp_22 = Rc::new(d2 { lb: tmp_19, sk: tmp_20, sq: tmp_21, ii: i, cc: cc_owned(s) });
        Rc::new(option::<Rc<d2>>::Some(tmp_22))
      }
    } else {
      std::mem::drop(roff);
      std::mem::drop(radj);
      std::mem::drop(post);
      std::mem::drop(s);
      Rc::new(option::<Rc<d2>>::None)
    }
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.assign
// Variant: uncurried
pub fn assign_1(roff: Array<Int63>, radj: Array<Int63>, post: Array<Int63>, s: Rc<d2>, bound: Int63, steps: Int63) -> Rc<d2> {
  assign(roff, radj, post, s, bound, steps, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.assign (local: assign)
// Variant: uncurried, lifted
pub fn assign(roff: Array<Int63>, radj: Array<Int63>, post: Array<Int63>, s: Rc<d2>, bound: Int63, steps: Int63, _H: ()) -> Rc<d2> {
  let tmp = steps < bound;
  match bdec(tmp) {
    sumbool::left => {
      let roff_clone = Clone::clone(&roff);
      let radj_clone = Clone::clone(&radj);
      let post_clone = Clone::clone(&post);
      let s_clone = Rc::clone(&s);
      let tmp_1 = asg_step(roff_clone, radj_clone, post_clone, s_clone);
      let (v32, v33) = __rocq_reuse::reset(tmp_1, |__payload| Clone::clone(__payload));
      std::mem::drop(v33);
      match v32 {
        option::Some(v38) => {
          std::mem::drop(s);
          assign(roff, radj, post, v38, bound, steps + int63!(1), ())
        },
        option::None => {
          std::mem::drop(roff);
          std::mem::drop(radj);
          std::mem::drop(post);
          s
        },
      }
    },
    sumbool::right => {
      std::mem::drop(roff);
      std::mem::drop(radj);
      std::mem::drop(post);
      s
    },
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

// Rocq: Corelib.Init.Datatypes.orb
// Variant: uncurried
pub fn orb(b1: bool, b2: bool) -> bool {
  if b1 {
    true
  } else {
    b2
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.merge_loop
// Variant: uncurried
pub fn merge_loop_1(le: Rc<dyn Fn(Int63, Int63) -> bool>, a_1: Array<Int63>, t: Array<Int63>, mid: Int63, hi: Int63, i: Int63, j: Int63, k: Int63) -> Array<Int63> {
  merge_loop(le, a_1, t, mid, hi, i, j, k, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.merge_loop (local: merge_loop)
// Variant: uncurried, lifted
pub fn merge_loop(le: Rc<dyn Fn(Int63, Int63) -> bool>, a_1: Array<Int63>, t: Array<Int63>, mid: Int63, hi: Int63, i: Int63, j: Int63, k: Int63, _H: ()) -> Array<Int63> {
  let tmp = k < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i < mid;
      let tmp_2 = hi <= j;
      let tmp_3 = a_1.get_cloned(i);
      let tmp_4 = a_1.get_cloned(j);
      let le_ref: &Rc<dyn Fn(Int63, Int63) -> bool> = &le;
      let tmp_5 = le_ref(tmp_3, tmp_4);
      let tmp_6 = orb(tmp_2, tmp_5);
      if andb(tmp_1, tmp_6) {
        let tmp_7 = a_1.get_cloned(i);
        merge_loop(le, a_1, t.set(k, tmp_7), mid, hi, i + int63!(1), j, k + int63!(1), ())
      } else {
        let tmp_8 = a_1.get_cloned(j);
        merge_loop(le, a_1, t.set(k, tmp_8), mid, hi, i, j + int63!(1), k + int63!(1), ())
      }
    },
    sumbool::right => {
      std::mem::drop(le);
      std::mem::drop(a_1);
      t
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.copy_back
// Variant: uncurried
pub fn copy_back_1(t: Array<Int63>, a_1: Array<Int63>, hi: Int63, k: Int63) -> Array<Int63> {
  copy_back(t, a_1, hi, k, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.copy_back (local: copy_back)
// Variant: uncurried, lifted
pub fn copy_back(t: Array<Int63>, a_1: Array<Int63>, hi: Int63, k: Int63, _H: ()) -> Array<Int63> {
  let tmp = k < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = t.get_cloned(k);
      copy_back(t, a_1.set(k, tmp_1), hi, k + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(t);
      a_1
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.msort
// Variant: uncurried
pub fn msort_1(le: Rc<dyn Fn(Int63, Int63) -> bool>, a_1: Array<Int63>, t: Array<Int63>, lo: Int63, hi: Int63) -> (Array<Int63>, Array<Int63>) {
  msort(le, a_1, t, lo, hi, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(le: Rc<dyn Fn(Int63, Int63) -> bool>, a_1: Array<Int63>, t: Array<Int63>, lo: Int63, hi: Int63, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = lo < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = int63!(1) < hi - lo;
      match bdec(tmp_1) {
        sumbool::left => {
          let tmp_2 = hi - lo;
          let mid = lo + tmp_2 / int63!(2);
          let le_clone: Rc<dyn Fn(Int63, Int63) -> bool> = Rc::clone(&le);
          let r1 = msort(le_clone, a_1, t, lo, mid, ());
          let r1_clone = Clone::clone(&r1);
          let tmp_3 = fst::<Array<Int63>, Array<Int63>>(r1_clone);
          let tmp_4 = snd::<Array<Int63>, Array<Int63>>(r1);
          let le_clone_1: Rc<dyn Fn(Int63, Int63) -> bool> = Rc::clone(&le);
          let r2 = msort(le_clone_1, tmp_3, tmp_4, mid, hi, ());
          let r2_clone = Clone::clone(&r2);
          let tmp_5 = fst::<Array<Int63>, Array<Int63>>(r2_clone);
          let r2_clone_1 = Clone::clone(&r2);
          let t3 = merge_loop_1(le, tmp_5, snd::<Array<Int63>, Array<Int63>>(r2_clone_1), mid, hi, lo, mid, lo);
          let tmp_6 = fst::<Array<Int63>, Array<Int63>>(r2);
          let t3_clone = Clone::clone(&t3);
          (copy_back_1(t3_clone, tmp_6, hi, lo), t3)
        },
        sumbool::right => {
          std::mem::drop(le);
          (a_1, t)
        },
      }
    },
    sumbool::right => {
      std::mem::drop(le);
      (a_1, t)
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.name_le
// Variant: borrowed, uncurried
pub fn name_le(names: &Array<rocq_string::RocqString>, a_1: Int63, b_1: Int63) -> bool {
  let a_2 = a_1;
  let b_2 = b_1;
  let tmp = names.get_cloned(a_2);
  let tmp_1 = names.get_cloned(b_2);
  match compare(tmp, tmp_1) {
    std::cmp::Ordering::Equal => {
      true
    },
    std::cmp::Ordering::Less => {
      true
    },
    std::cmp::Ordering::Greater => {
      false
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.iota_loop
// Variant: uncurried
pub fn iota_loop_1(n: Int63, k: Int63, a_1: Array<Int63>) -> Array<Int63> {
  iota_loop(n, k, a_1, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.iota_loop (local: iota_loop)
// Variant: uncurried, lifted
pub fn iota_loop(n: Int63, k: Int63, a_1: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = k < n;
  match bdec(tmp) {
    sumbool::left => {
      iota_loop(n, k + int63!(1), a_1.set(k, k), ())
    },
    sumbool::right => {
      a_1
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.gord
pub fn gord(d: Rc<d3>) -> Array<Int63> {
  let d_gord_clone = Clone::clone(&d.gord);
  std::mem::drop(d);
  d_gord_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.gn
pub fn gn_owned(d: Rc<d3>) -> Int63 {
  let d_gn_clone = Clone::clone(&d.gn);
  std::mem::drop(d);
  d_gn_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.gn
// Variant: borrowed
pub fn gn(d: &Rc<d3>) -> Int63 {
  let tmp = d;
  Clone::clone(&tmp.gn)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.av
pub fn av(d: Rc<d3>) -> Array<rocq_string::RocqString> {
  let d_av_clone = Clone::clone(&d.av);
  std::mem::drop(d);
  d_av_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.an
pub fn an_owned(d: Rc<d3>) -> Int63 {
  let d_an_clone = Clone::clone(&d.an);
  std::mem::drop(d);
  d_an_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.an
// Variant: borrowed
pub fn an(d: &Rc<d3>) -> Int63 {
  let tmp = d;
  Clone::clone(&tmp.an)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.emit_loop
// Variant: uncurried
pub fn emit_loop_1(names: Array<rocq_string::RocqString>, lab: Array<Int63>, csz: Array<Int63>, boff: Array<Int63>, badj: Array<Int63>, byname: Array<Int63>, V: Int63, k: Int63, s: Rc<d3>) -> Rc<d3> {
  emit_loop(names, lab, csz, boff, badj, byname, V, k, s, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.emit_loop (local: emit_loop)
// Variant: uncurried, lifted
pub fn emit_loop(names: Array<rocq_string::RocqString>, lab: Array<Int63>, csz: Array<Int63>, boff: Array<Int63>, badj: Array<Int63>, byname: Array<Int63>, V: Int63, k: Int63, s: Rc<d3>, _H: ()) -> Rc<d3> {
  let tmp = k < V;
  match bdec(tmp) {
    sumbool::left => {
      let v = byname.get_cloned(k);
      let c = lab.get_cloned(v);
      let tmp_1 = csz.get_cloned(c);
      if int63!(1) < tmp_1 {
        let tmp_2 = boff.get_cloned(c);
        let tmp_3 = badj.get_cloned(tmp_2);
        if tmp_3 == v {
          let tmp_4 = k + int63!(1);
          let s_clone = Rc::clone(&s);
          let tmp_5 = gord(s_clone);
          let tmp_6 = gn(&s);
          let tmp_7 = tmp_5.set(tmp_6, c);
          let tmp_8 = gn(&s);
          let tmp_9 = tmp_8 + int63!(1);
          let s_clone_1 = Rc::clone(&s);
          emit_loop(names, lab, csz, boff, badj, byname, V, tmp_4, Rc::new(d3 { gord: tmp_7, gn: tmp_9, av: av(s_clone_1), an: an_owned(s) }), ())
        } else {
          emit_loop(names, lab, csz, boff, badj, byname, V, k + int63!(1), s, ())
        }
      } else {
        let tmp_10 = k + int63!(1);
        let s_clone_2 = Rc::clone(&s);
        let tmp_11 = gord(s_clone_2);
        let tmp_12 = gn(&s);
        let s_clone_3 = Rc::clone(&s);
        let tmp_13 = av(s_clone_3);
        let tmp_14 = an(&s);
        let names_ref = &names;
        let tmp_15 = names_ref.get_cloned(v);
        emit_loop(names, lab, csz, boff, badj, byname, V, tmp_10, Rc::new(d3 { gord: tmp_11, gn: tmp_12, av: tmp_13.set(tmp_14, tmp_15), an: an_owned(s) + int63!(1) }), ())
      }
    },
    sumbool::right => {
      std::mem::drop(names);
      std::mem::drop(lab);
      std::mem::drop(csz);
      std::mem::drop(boff);
      std::mem::drop(badj);
      std::mem::drop(byname);
      s
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.copy_loop
// Variant: uncurried
pub fn copy_loop_1(src: Array<rocq_string::RocqString>, n: Int63, k: Int63, dst: Array<rocq_string::RocqString>) -> Array<rocq_string::RocqString> {
  copy_loop(src, n, k, dst, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.copy_loop (local: copy_loop)
// Variant: uncurried, lifted
pub fn copy_loop(src: Array<rocq_string::RocqString>, n: Int63, k: Int63, dst: Array<rocq_string::RocqString>, _H: ()) -> Array<rocq_string::RocqString> {
  let tmp = k < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = k + int63!(1);
      let src_ref = &src;
      let tmp_2 = src_ref.get_cloned(k);
      copy_loop(src, n, tmp_1, dst.set(k, tmp_2), ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.inner_loop
// Variant: uncurried
pub fn inner_loop_1(names: Array<rocq_string::RocqString>, badj: Array<Int63>, st: Int63, n: Int63, k: Int63, g: Array<rocq_string::RocqString>) -> Array<rocq_string::RocqString> {
  inner_loop(names, badj, st, n, k, g, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.inner_loop (local: inner_loop)
// Variant: uncurried, lifted
pub fn inner_loop(names: Array<rocq_string::RocqString>, badj: Array<Int63>, st: Int63, n: Int63, k: Int63, g: Array<rocq_string::RocqString>, _H: ()) -> Array<rocq_string::RocqString> {
  let tmp = k < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = k + int63!(1);
      let tmp_2 = badj.get_cloned(st + k);
      let names_ref = &names;
      let tmp_3 = names_ref.get_cloned(tmp_2);
      inner_loop(names, badj, st, n, tmp_1, g.set(k, tmp_3), ())
    },
    sumbool::right => {
      std::mem::drop(names);
      std::mem::drop(badj);
      g
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.group_arr
// Variant: uncurried
pub fn group_arr(names: Array<rocq_string::RocqString>, boff: Array<Int63>, badj: Array<Int63>, c: Int63) -> Array<rocq_string::RocqString> {
  let st = boff.get_cloned(c);
  let tmp = boff.get_cloned(c + int63!(1));
  std::mem::drop(boff);
  let n = tmp - st;
  let tmp_1 = Array::<rocq_string::RocqString>::make(n, rocq_string::RocqString::make(int63!(0), int63!(0)));
  inner_loop_1(names, badj, st, n, int63!(0), tmp_1)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.groups_loop
// Variant: uncurried
pub fn groups_loop_1(names: Array<rocq_string::RocqString>, boff: Array<Int63>, badj: Array<Int63>, gord_1: Array<Int63>, G: Int63, g: Int63, out: Array<Array<rocq_string::RocqString>>) -> Array<Array<rocq_string::RocqString>> {
  groups_loop(names, boff, badj, gord_1, G, g, out, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.groups_loop (local: groups_loop)
// Variant: uncurried, lifted
pub fn groups_loop(names: Array<rocq_string::RocqString>, boff: Array<Int63>, badj: Array<Int63>, gord_1: Array<Int63>, G: Int63, g: Int63, out: Array<Array<rocq_string::RocqString>>, _H: ()) -> Array<Array<rocq_string::RocqString>> {
  let tmp = g < G;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = g + int63!(1);
      let tmp_2 = gord_1.get_cloned(g);
      let names_clone = Clone::clone(&names);
      let boff_clone = Clone::clone(&boff);
      let badj_clone = Clone::clone(&badj);
      groups_loop(names, boff, badj, gord_1, G, tmp_1, out.set(g, group_arr(names_clone, boff_clone, badj_clone, tmp_2)), ())
    },
    sumbool::right => {
      std::mem::drop(names);
      std::mem::drop(boff);
      std::mem::drop(badj);
      std::mem::drop(gord_1);
      out
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.loopy_impl
// Variant: uncurried
pub fn loopy_impl(x: Array<rocq_string::RocqString>, y: Array<rocq_string::RocqString>) -> (Array<Array<rocq_string::RocqString>>, Array<rocq_string::RocqString>) {
  let m = x.length();
  let st0 = Rc::new(hstate { ht: Array::<Int63>::make(__rocq_global_19.with(Clone::clone) + int63!(2) * m + int63!(1), int63!(0)), hn: Array::<rocq_string::RocqString>::make(int63!(2) * m + int63!(1), empty_str(())), hc: int63!(0) });
  let tmp = Array::<Int63>::make(m, int63!(0));
  let tmp_1 = Array::<Int63>::make(m, int63!(0));
  let r0 = idloop_1(x, y, m, int63!(0), st0, tmp, tmp_1);
  let r0_clone = Clone::clone(&r0);
  let st = fst::<Rc<hstate>, Array<Int63>>(fst::<(Rc<hstate>, Array<Int63>), Array<Int63>>(r0_clone));
  let r0_clone_1 = Clone::clone(&r0);
  let is = snd::<Rc<hstate>, Array<Int63>>(fst::<(Rc<hstate>, Array<Int63>), Array<Int63>>(r0_clone_1));
  let id = snd::<(Rc<hstate>, Array<Int63>), Array<Int63>>(r0);
  let V = hc(&st);
  let names = hn(st);
  let is_clone = Clone::clone(&is);
  let callback: Rc<dyn Fn(Int63) -> Int63> = Rc::new({
    move |k: Int63| -> Int63 {
      is_clone.get_cloned(k)
    }
  });
  let id_clone = Clone::clone(&id);
  let callback_1: Rc<dyn Fn(Int63) -> Int63> = Rc::new({
    move |k: Int63| -> Int63 {
      id_clone.get_cloned(k)
    }
  });
  let g = csr(V, m, callback, callback_1);
  let callback_2: Rc<dyn Fn(Int63) -> Int63> = Rc::new({
    let __anf_capture_176 = id;
    move |k: Int63| -> Int63 {
      __anf_capture_176.get_cloned(k)
    }
  });
  let callback_3: Rc<dyn Fn(Int63) -> Int63> = Rc::new({
    let __anf_capture_189 = is;
    move |k: Int63| -> Int63 {
      __anf_capture_189.get_cloned(k)
    }
  });
  let gt = csr(V, m, callback_2, callback_3);
  let bound = int63!(3) * V + int63!(1);
  let g_clone = Clone::clone(&g);
  let tmp_2 = fst::<Array<Int63>, Array<Int63>>(g_clone);
  let tmp_3 = snd::<Array<Int63>, Array<Int63>>(g);
  let tmp_4 = Array::<Int63>::make(V, int63!(0));
  let tmp_5 = Array::<Int63>::make(V, int63!(0));
  let tmp_6 = Array::<Int63>::make(V, int63!(0));
  let tmp_7 = Array::<Int63>::make(V, int63!(0));
  let post = dfs_1(V, tmp_2, tmp_3, Rc::new(d1 { mk: tmp_4, sv: tmp_5, sc: tmp_6, po: tmp_7, sp: int63!(0), np: int63!(0), rt: int63!(0) }), bound, int63!(0));
  let gt_clone = Clone::clone(&gt);
  let s2 = assign_1(fst::<Array<Int63>, Array<Int63>>(gt_clone), snd::<Array<Int63>, Array<Int63>>(gt), post, Rc::new(d2 { lb: Array::<Int63>::make(V, int63!(0)), sk: Array::<Int63>::make(V, int63!(0)), sq: int63!(0), ii: V, cc: int63!(0) }), bound, int63!(0));
  let s2_clone = Rc::clone(&s2);
  let lab = lb_owned(s2_clone);
  let C = cc_owned(s2);
  let lab_clone = Clone::clone(&lab);
  let callback_4: Rc<dyn Fn(Int63) -> Int63> = Rc::new({
    move |v: Int63| -> Int63 {
      lab_clone.get_cloned(v)
    }
  });
  let csz = cnt_loop_1(callback_4, V, int63!(0), Array::<Int63>::make(C + int63!(1), int63!(0)));
  let names_clone = Clone::clone(&names);
  let callback_5: Rc<dyn Fn(Int63, Int63) -> bool> = Rc::new({
    move |v414: Int63, v415: Int63| -> bool {
      name_le(&names_clone, v414, v415)
    }
  });
  let tmp_8 = Array::<Int63>::make(V, int63!(0));
  let byname = fst::<Array<Int63>, Array<Int63>>(msort_1(callback_5, iota_loop_1(V, int63!(0), tmp_8), Array::<Int63>::make(V, int63!(0)), int63!(0), V));
  let tmp_9 = C + int63!(1);
  let byname_clone = Clone::clone(&byname);
  let lab_clone_1 = Clone::clone(&lab);
  let callback_6: Rc<dyn Fn(Int63) -> Int63> = Rc::new({
    move |k: Int63| -> Int63 {
      let byname = &byname_clone;
      let lab = &lab_clone_1;
      let tmp_10 = byname.get_cloned(k);
      lab.get_cloned(tmp_10)
    }
  });
  let byname_clone_1 = Clone::clone(&byname);
  let callback_7: Rc<dyn Fn(Int63) -> Int63> = Rc::new({
    move |k: Int63| -> Int63 {
      byname_clone_1.get_cloned(k)
    }
  });
  let b_1 = csr(tmp_9, V, callback_6, callback_7);
  let b_clone = Clone::clone(&b_1);
  let tmp_11 = fst::<Array<Int63>, Array<Int63>>(b_clone);
  let b_clone_1 = Clone::clone(&b_1);
  let tmp_12 = snd::<Array<Int63>, Array<Int63>>(b_clone_1);
  let tmp_13 = Rc::new(d3 { gord: Array::<Int63>::make(V, int63!(0)), gn: int63!(0), av: Array::<rocq_string::RocqString>::make(V, empty_str(())), an: int63!(0) });
  let names_clone_1 = Clone::clone(&names);
  let s3 = emit_loop_1(names_clone_1, lab, csz, tmp_11, tmp_12, byname, V, int63!(0), tmp_13);
  let s3_clone = Rc::clone(&s3);
  let tmp_14 = av(s3_clone);
  let tmp_15 = an(&s3);
  let tmp_16 = an(&s3);
  let avoid = copy_loop_1(tmp_14, tmp_15, int63!(0), Array::<rocq_string::RocqString>::make(tmp_16, empty_str(())));
  let b_clone_2 = Clone::clone(&b_1);
  let tmp_17 = fst::<Array<Int63>, Array<Int63>>(b_clone_2);
  let tmp_18 = snd::<Array<Int63>, Array<Int63>>(b_1);
  let s3_clone_1 = Rc::clone(&s3);
  let tmp_19 = gord(s3_clone_1);
  let tmp_20 = gn(&s3);
  let groups = groups_loop_1(names, tmp_17, tmp_18, tmp_19, tmp_20, int63!(0), Array::<Array<rocq_string::RocqString>>::make(gn_owned(s3), Array::<rocq_string::RocqString>::make(int63!(0), empty_str(()))));
  (groups, avoid)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.empty_str
pub fn empty_str_1() -> rocq_string::RocqString {
  rocq_string::RocqString::make(int63!(0), int63!(0))
}
std::thread_local! { static __rocq_global_19: Int63 = hsize(); }
std::thread_local! { static __rocq_global_280: Int63 = hmask(); }
std::thread_local! { static __rocq_global_281: rocq_string::RocqString = empty_str_1(); }