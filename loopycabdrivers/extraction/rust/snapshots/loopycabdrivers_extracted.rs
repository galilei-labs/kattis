#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub struct d3 {
  pub gord: Rc<Array<u64>>,
  pub gn: u64,
  pub av: Rc<Array<Rc<rocq_string::RocqString>>>,
  pub an: u64,
}

impl Clone for d3 {
  fn clone(&self) -> Self {
    match self {
      d3 { gord: __field0, gn: __field1, av: __field2, an: __field3 } => d3 { gord: Clone::clone(__field0), gn: Clone::clone(__field1), av: Clone::clone(__field2), an: Clone::clone(__field3) },
    }
  }
}

pub struct d2 {
  pub lb: Rc<Array<u64>>,
  pub sk: Rc<Array<u64>>,
  pub sq: u64,
  pub ii: u64,
  pub cc: u64,
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
  pub mk: Rc<Array<u64>>,
  pub sv: Rc<Array<u64>>,
  pub sc: Rc<Array<u64>>,
  pub po: Rc<Array<u64>>,
  pub sp: u64,
  pub np: u64,
  pub rt: u64,
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
  pub ht: Rc<Array<u64>>,
  pub hn: Rc<Array<Rc<rocq_string::RocqString>>>,
  pub hc: u64,
}

impl Clone for hstate {
  fn clone(&self) -> Self {
    match self {
      hstate { ht: __field0, hn: __field1, hc: __field2 } => hstate { ht: Clone::clone(__field0), hn: Clone::clone(__field1), hc: Clone::clone(__field2) },
    }
  }
}

pub type char63 = u64;

// Rocq: Loopycabdrivers.loopycabdrivers_implem.hsize
pub fn hsize() -> u64 {
  65536u64
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.hmask
pub fn hmask() -> u64 {
  65535u64
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

// Rocq: Corelib.Strings.PrimString.make
// Variant: uncurried
pub fn make(v0: u64, v1: u64) -> Rc<rocq_string::RocqString> {
  let tmp = rocq_string::make(v0, v1);
  tmp
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.empty_str
pub fn empty_str(_v0: ()) -> Rc<rocq_string::RocqString> {
  let tmp = make(0u64, 0u64);
  tmp
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.land
// Variant: uncurried
pub fn land(v0: u64, v1: u64) -> u64 {
  rocq_int63::land(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.ht
pub fn ht(h: Rc<hstate>) -> Rc<Array<u64>> {
  let h_ht_clone = Rc::clone(&h.ht);
  std::mem::drop(h);
  h_ht_clone
}

// Rocq: Corelib.Strings.PrimString.compare
// Variant: uncurried
pub fn compare(v0: Rc<rocq_string::RocqString>, v1: Rc<rocq_string::RocqString>) -> std::cmp::Ordering {
  let tmp = rocq_string::compare(&v0, &v1);
  std::mem::drop(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.probe
// Variant: uncurried
pub fn probe_1(tbl: Rc<Array<u64>>, names: Rc<Array<Rc<rocq_string::RocqString>>>, s: Rc<rocq_string::RocqString>, T: u64, p: u64) -> (u64, bool) {
  probe(tbl, names, s, T, p, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.probe (local: probe)
// Variant: uncurried, lifted
pub fn probe(tbl: Rc<Array<u64>>, names: Rc<Array<Rc<rocq_string::RocqString>>>, s: Rc<rocq_string::RocqString>, T: u64, p: u64, _H: ()) -> (u64, bool) {
  let tmp = ltb(p, T);
  match bdec(tmp) {
    sumbool::left => {
      let e = rocq_array::get::<u64>(&tbl, p);
      if eqb(e, 0u64) {
        std::mem::drop(tbl);
        std::mem::drop(names);
        std::mem::drop(s);
        (p, false)
      } else {
        let tmp_1 = rocq_array::get::<Rc<rocq_string::RocqString>>(&names, sub(e, 1u64));
        let s_clone = Rc::clone(&s);
        match compare(tmp_1, s_clone) {
          std::cmp::Ordering::Equal => {
            std::mem::drop(tbl);
            std::mem::drop(s);
            std::mem::drop(names);
            (p, true)
          },
          std::cmp::Ordering::Less => {
            probe(tbl, names, s, T, add(p, 1u64), ())
          },
          std::cmp::Ordering::Greater => {
            probe(tbl, names, s, T, add(p, 1u64), ())
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
pub fn hn(h: Rc<hstate>) -> Rc<Array<Rc<rocq_string::RocqString>>> {
  let h_hn_clone = Rc::clone(&h.hn);
  std::mem::drop(h);
  h_hn_clone
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let tmp = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.hloop
// Variant: uncurried
pub fn hloop_1(s: Rc<rocq_string::RocqString>, n: u64, k: u64, h: u64) -> u64 {
  hloop(s, n, k, h, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.hloop (local: hloop)
// Variant: uncurried, lifted
pub fn hloop(s: Rc<rocq_string::RocqString>, n: u64, k: u64, h: u64, _H: ()) -> u64 {
  let tmp = ltb(k, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(k, 1u64);
      let tmp_2 = mul(h, 31u64);
      let s_clone = Rc::clone(&s);
      hloop(s, n, tmp_1, add(tmp_2, get(s_clone, k)), ())
    },
    sumbool::right => {
      std::mem::drop(s);
      h
    },
  }
}

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: Rc<rocq_string::RocqString>) -> u64 {
  let tmp = rocq_string::length(&v0);
  std::mem::drop(v0);
  tmp
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.hash
pub fn hash(s: Rc<rocq_string::RocqString>) -> u64 {
  let s_clone = Rc::clone(&s);
  land(hloop_1(s, length(s_clone), 0u64, 7u64), __rocq_global_280)
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
pub fn hc_owned(h: Rc<hstate>) -> u64 {
  let h_hc_clone = Clone::clone(&h.hc);
  std::mem::drop(h);
  h_hc_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.hc
// Variant: borrowed
pub fn hc(h: &Rc<hstate>) -> u64 {
  let tmp = h;
  Clone::clone(&tmp.hc)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.lookup
// Variant: uncurried
pub fn lookup(st: Rc<hstate>, s: Rc<rocq_string::RocqString>) -> (Rc<hstate>, u64) {
  let st_clone = Rc::clone(&st);
  let tbl = ht(st_clone);
  let T = rocq_array::length::<u64>(&tbl);
  let st_clone_1 = Rc::clone(&st);
  let tmp = hn(st_clone_1);
  let s_clone = Rc::clone(&s);
  let tmp_1 = hash(s_clone);
  let tbl_clone = Rc::clone(&tbl);
  let s_clone_1 = Rc::clone(&s);
  let pf = probe_1(tbl_clone, tmp, s_clone_1, T, tmp_1);
  let pf_clone = Clone::clone(&pf);
  let p = fst::<u64, bool>(pf_clone);
  if snd::<u64, bool>(pf) {
    std::mem::drop(s);
    let tmp_2 = rocq_array::get::<u64>(&tbl, p);
    std::mem::drop(tbl);
    (st, sub(tmp_2, 1u64))
  } else {
    let tmp_3 = hc(&st);
    let tmp_4 = rocq_array::set::<u64>(tbl, p, add(tmp_3, 1u64));
    let st_clone_2 = Rc::clone(&st);
    let tmp_5 = hn(st_clone_2);
    let tmp_6 = hc(&st);
    let tmp_7 = rocq_array::set::<Rc<rocq_string::RocqString>>(tmp_5, tmp_6, s);
    let tmp_8 = hc(&st);
    (Rc::new(hstate { ht: tmp_4, hn: tmp_7, hc: add(tmp_8, 1u64) }), hc_owned(st))
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.idloop
// Variant: uncurried
pub fn idloop_1(x: Rc<Array<Rc<rocq_string::RocqString>>>, y: Rc<Array<Rc<rocq_string::RocqString>>>, m: u64, k: u64, st: Rc<hstate>, is: Rc<Array<u64>>, id: Rc<Array<u64>>) -> ((Rc<hstate>, Rc<Array<u64>>), Rc<Array<u64>>) {
  idloop(x, y, m, k, st, is, id, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.idloop (local: idloop)
// Variant: uncurried, lifted
pub fn idloop(x: Rc<Array<Rc<rocq_string::RocqString>>>, y: Rc<Array<Rc<rocq_string::RocqString>>>, m: u64, k: u64, st: Rc<hstate>, is: Rc<Array<u64>>, id: Rc<Array<u64>>, _H: ()) -> ((Rc<hstate>, Rc<Array<u64>>), Rc<Array<u64>>) {
  let tmp = ltb(k, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<Rc<rocq_string::RocqString>>(&x, k);
      let r1 = lookup(st, tmp_1);
      let r1_clone = Clone::clone(&r1);
      let tmp_2 = fst::<Rc<hstate>, u64>(r1_clone);
      let tmp_3 = rocq_array::get::<Rc<rocq_string::RocqString>>(&y, k);
      let r2 = lookup(tmp_2, tmp_3);
      let tmp_4 = add(k, 1u64);
      let r2_clone = Clone::clone(&r2);
      let tmp_5 = fst::<Rc<hstate>, u64>(r2_clone);
      let tmp_6 = rocq_array::set::<u64>(is, k, snd::<Rc<hstate>, u64>(r1));
      let tmp_7 = rocq_array::set::<u64>(id, k, snd::<Rc<hstate>, u64>(r2));
      idloop(x, y, m, tmp_4, tmp_5, tmp_6, tmp_7, ())
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
pub fn cnt_loop_1(es: Rc<dyn Fn(u64) -> u64>, m: u64, k: u64, cnt: Rc<Array<u64>>) -> Rc<Array<u64>> {
  cnt_loop(es, m, k, cnt, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.cnt_loop (local: cnt_loop)
// Variant: uncurried, lifted
pub fn cnt_loop(es: Rc<dyn Fn(u64) -> u64>, m: u64, k: u64, cnt: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, m);
  match bdec(tmp) {
    sumbool::left => {
      let es_ref: &Rc<dyn Fn(u64) -> u64> = &es;
      let u = es_ref(k);
      let tmp_1 = add(k, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&cnt, u);
      let tmp_3 = rocq_array::set::<u64>(cnt, u, add(tmp_2, 1u64));
      cnt_loop(es, m, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(es);
      cnt
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.pre_loop
// Variant: uncurried
pub fn pre_loop_1(cnt: Rc<Array<u64>>, V: u64, u: u64, off: Rc<Array<u64>>) -> Rc<Array<u64>> {
  pre_loop(cnt, V, u, off, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.pre_loop (local: pre_loop)
// Variant: uncurried, lifted
pub fn pre_loop(cnt: Rc<Array<u64>>, V: u64, u: u64, off: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(u, V);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(u, 1u64);
      let tmp_2 = add(u, 1u64);
      let tmp_3 = rocq_array::get::<u64>(&off, u);
      let tmp_4 = rocq_array::get::<u64>(&cnt, u);
      let tmp_5 = rocq_array::set::<u64>(off, tmp_2, add(tmp_3, tmp_4));
      pre_loop(cnt, V, tmp_1, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(cnt);
      off
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(es: Rc<dyn Fn(u64) -> u64>, ed: Rc<dyn Fn(u64) -> u64>, m: u64, k: u64, pos: Rc<Array<u64>>, adj: Rc<Array<u64>>) -> Rc<Array<u64>> {
  fill_loop(es, ed, m, k, pos, adj, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(es: Rc<dyn Fn(u64) -> u64>, ed: Rc<dyn Fn(u64) -> u64>, m: u64, k: u64, pos: Rc<Array<u64>>, adj: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, m);
  match bdec(tmp) {
    sumbool::left => {
      let es_ref: &Rc<dyn Fn(u64) -> u64> = &es;
      let u = es_ref(k);
      let p = rocq_array::get::<u64>(&pos, u);
      let tmp_1 = add(k, 1u64);
      let tmp_2 = rocq_array::set::<u64>(pos, u, add(p, 1u64));
      let ed_ref: &Rc<dyn Fn(u64) -> u64> = &ed;
      let tmp_3 = ed_ref(k);
      let tmp_4 = rocq_array::set::<u64>(adj, p, tmp_3);
      fill_loop(es, ed, m, tmp_1, tmp_2, tmp_4, ())
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
pub fn csr(V: u64, m: u64, es: Rc<dyn Fn(u64) -> u64>, ed: Rc<dyn Fn(u64) -> u64>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = rocq_array::make::<u64>(V, 0u64);
  let es_clone: Rc<dyn Fn(u64) -> u64> = Rc::clone(&es);
  let cnt = cnt_loop_1(es_clone, m, 0u64, tmp);
  let tmp_1 = rocq_array::make::<u64>(add(V, 1u64), 0u64);
  let off = pre_loop_1(cnt, V, 0u64, tmp_1);
  let tmp_2 = rocq_array::copy::<u64>(&off);
  let tmp_3 = rocq_array::make::<u64>(m, 0u64);
  let adj = fill_loop_1(es, ed, m, 0u64, tmp_2, tmp_3);
  (off, adj)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.sp
// Variant: borrowed
pub fn sp(d: &Rc<d1>) -> u64 {
  let tmp = d;
  Clone::clone(&tmp.sp)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.sv
pub fn sv_owned(d: Rc<d1>) -> Rc<Array<u64>> {
  let d_sv_clone = Rc::clone(&d.sv);
  std::mem::drop(d);
  d_sv_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.sv
// Variant: borrowed
pub fn sv(d: &Rc<d1>) -> Rc<Array<u64>> {
  let tmp = d;
  Rc::clone(&tmp.sv)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.scan
// Variant: uncurried
pub fn scan_1(mark: Rc<Array<u64>>, adj: Rc<Array<u64>>, e: u64, j: u64) -> u64 {
  scan(mark, adj, e, j, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(mark: Rc<Array<u64>>, adj: Rc<Array<u64>>, e: u64, j: u64, _H: ()) -> u64 {
  let tmp = ltb(j, e);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&adj, j);
      let tmp_2 = rocq_array::get::<u64>(&mark, tmp_1);
      if eqb(tmp_2, 0u64) {
        std::mem::drop(adj);
        std::mem::drop(mark);
        j
      } else {
        scan(mark, adj, e, add(j, 1u64), ())
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
pub fn mk_owned(d: Rc<d1>) -> Rc<Array<u64>> {
  let d_mk_clone = Rc::clone(&d.mk);
  std::mem::drop(d);
  d_mk_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.mk
// Variant: borrowed
pub fn mk(d: &Rc<d1>) -> Rc<Array<u64>> {
  let tmp = d;
  Rc::clone(&tmp.mk)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.sc
pub fn sc_owned(d: Rc<d1>) -> Rc<Array<u64>> {
  let d_sc_clone = Rc::clone(&d.sc);
  std::mem::drop(d);
  d_sc_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.sc
// Variant: borrowed
pub fn sc(d: &Rc<d1>) -> Rc<Array<u64>> {
  let tmp = d;
  Rc::clone(&tmp.sc)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.po
pub fn po(d: Rc<d1>) -> Rc<Array<u64>> {
  let d_po_clone = Rc::clone(&d.po);
  std::mem::drop(d);
  d_po_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.np
pub fn np_owned(d: Rc<d1>) -> u64 {
  let d_np_clone = Clone::clone(&d.np);
  std::mem::drop(d);
  d_np_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.np
// Variant: borrowed
pub fn np(d: &Rc<d1>) -> u64 {
  let tmp = d;
  Clone::clone(&tmp.np)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.rt
pub fn rt_owned(d: Rc<d1>) -> u64 {
  let d_rt_clone = Clone::clone(&d.rt);
  std::mem::drop(d);
  d_rt_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.rt
// Variant: borrowed
pub fn rt(d: &Rc<d1>) -> u64 {
  let tmp = d;
  Clone::clone(&tmp.rt)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.dfs_step
// Variant: uncurried
pub fn dfs_step(V: u64, off: Rc<Array<u64>>, adj: Rc<Array<u64>>, s: Rc<d1>) -> Rc<option<Rc<d1>>> {
  let tmp = sp(&s);
  if ltb(0u64, tmp) {
    let t = sub(sp(&s), 1u64);
    let tmp_1 = sv(&s);
    let u = rocq_array::get::<u64>(&tmp_1, t);
    let e = rocq_array::get::<u64>(&off, add(u, 1u64));
    let tmp_2 = mk(&s);
    let tmp_3 = sc(&s);
    let tmp_4 = rocq_array::get::<u64>(&tmp_3, t);
    let adj_clone = Rc::clone(&adj);
    let j = scan_1(tmp_2, adj_clone, e, tmp_4);
    if ltb(j, e) {
      std::mem::drop(tmp_3);
      std::mem::drop(tmp_1);
      let w = rocq_array::get::<u64>(&adj, j);
      std::mem::drop(adj);
      let s_clone = Rc::clone(&s);
      let tmp_5 = mk_owned(s_clone);
      let tmp_6 = rocq_array::set::<u64>(tmp_5, w, 1u64);
      let s_clone_1 = Rc::clone(&s);
      let tmp_7 = sv_owned(s_clone_1);
      let tmp_8 = sp(&s);
      let tmp_9 = rocq_array::set::<u64>(tmp_7, tmp_8, w);
      let s_clone_2 = Rc::clone(&s);
      let tmp_10 = sc_owned(s_clone_2);
      let tmp_11 = rocq_array::set::<u64>(tmp_10, t, add(j, 1u64));
      let tmp_12 = sp(&s);
      let tmp_13 = rocq_array::get::<u64>(&off, w);
      std::mem::drop(off);
      let tmp_14 = rocq_array::set::<u64>(tmp_11, tmp_12, tmp_13);
      let s_clone_3 = Rc::clone(&s);
      let tmp_15 = po(s_clone_3);
      let tmp_16 = sp(&s);
      let tmp_17 = add(tmp_16, 1u64);
      let tmp_18 = np(&s);
      let tmp_19 = Rc::new(d1 { mk: tmp_6, sv: tmp_9, sc: tmp_14, po: tmp_15, sp: tmp_17, np: tmp_18, rt: rt_owned(s) });
      Rc::new(option::<Rc<d1>>::Some(tmp_19))
    } else {
      std::mem::drop(adj);
      std::mem::drop(tmp_3);
      std::mem::drop(off);
      std::mem::drop(tmp_1);
      let s_clone_4 = Rc::clone(&s);
      let tmp_20 = mk_owned(s_clone_4);
      let s_clone_5 = Rc::clone(&s);
      let tmp_21 = sv_owned(s_clone_5);
      let s_clone_6 = Rc::clone(&s);
      let tmp_22 = sc_owned(s_clone_6);
      let s_clone_7 = Rc::clone(&s);
      let tmp_23 = po(s_clone_7);
      let tmp_24 = np(&s);
      let tmp_25 = rocq_array::set::<u64>(tmp_23, tmp_24, u);
      let tmp_26 = np(&s);
      let tmp_27 = Rc::new(d1 { mk: tmp_20, sv: tmp_21, sc: tmp_22, po: tmp_25, sp: t, np: add(tmp_26, 1u64), rt: rt_owned(s) });
      Rc::new(option::<Rc<d1>>::Some(tmp_27))
    }
  } else {
    let tmp_28 = rt(&s);
    if ltb(tmp_28, V) {
      let r = rt(&s);
      let tmp_29 = mk(&s);
      let tmp_30 = rocq_array::get::<u64>(&tmp_29, r);
      if eqb(tmp_30, 0u64) {
        std::mem::drop(adj);
        std::mem::drop(tmp_29);
        let s_clone_8 = Rc::clone(&s);
        let tmp_31 = mk_owned(s_clone_8);
        let tmp_32 = rocq_array::set::<u64>(tmp_31, r, 1u64);
        let s_clone_9 = Rc::clone(&s);
        let tmp_33 = sv_owned(s_clone_9);
        let tmp_34 = rocq_array::set::<u64>(tmp_33, 0u64, r);
        let s_clone_10 = Rc::clone(&s);
        let tmp_35 = sc_owned(s_clone_10);
        let tmp_36 = 0u64;
        let tmp_37 = rocq_array::get::<u64>(&off, r);
        std::mem::drop(off);
        let tmp_38 = rocq_array::set::<u64>(tmp_35, tmp_36, tmp_37);
        let s_clone_11 = Rc::clone(&s);
        let tmp_39 = po(s_clone_11);
        let tmp_40 = Rc::new(d1 { mk: tmp_32, sv: tmp_34, sc: tmp_38, po: tmp_39, sp: 1u64, np: np_owned(s), rt: add(r, 1u64) });
        Rc::new(option::<Rc<d1>>::Some(tmp_40))
      } else {
        std::mem::drop(off);
        std::mem::drop(adj);
        std::mem::drop(tmp_29);
        let s_clone_12 = Rc::clone(&s);
        let tmp_41 = mk_owned(s_clone_12);
        let s_clone_13 = Rc::clone(&s);
        let tmp_42 = sv_owned(s_clone_13);
        let s_clone_14 = Rc::clone(&s);
        let tmp_43 = sc_owned(s_clone_14);
        let s_clone_15 = Rc::clone(&s);
        let tmp_44 = po(s_clone_15);
        let tmp_45 = sp(&s);
        let tmp_46 = Rc::new(d1 { mk: tmp_41, sv: tmp_42, sc: tmp_43, po: tmp_44, sp: tmp_45, np: np_owned(s), rt: add(r, 1u64) });
        Rc::new(option::<Rc<d1>>::Some(tmp_46))
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
pub fn dfs_1(V: u64, off: Rc<Array<u64>>, adj: Rc<Array<u64>>, s: Rc<d1>, bound: u64, steps: u64) -> Rc<Array<u64>> {
  dfs(V, off, adj, s, bound, steps, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.dfs (local: dfs)
// Variant: uncurried, lifted
pub fn dfs(V: u64, off: Rc<Array<u64>>, adj: Rc<Array<u64>>, s: Rc<d1>, bound: u64, steps: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(steps, bound);
  match bdec(tmp) {
    sumbool::left => {
      let off_clone = Rc::clone(&off);
      let adj_clone = Rc::clone(&adj);
      let s_clone = Rc::clone(&s);
      let tmp_1 = dfs_step(V, off_clone, adj_clone, s_clone);
      let (v31, v32) = __rocq_reuse::reset(tmp_1, |__payload| Clone::clone(__payload));
      std::mem::drop(v32);
      match v31 {
        option::Some(v37) => {
          std::mem::drop(s);
          dfs(V, off, adj, v37, bound, add(steps, 1u64), ())
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
pub fn sq(d: &Rc<d2>) -> u64 {
  let tmp = d;
  Clone::clone(&tmp.sq)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.sk
pub fn sk(d: Rc<d2>) -> Rc<Array<u64>> {
  let d_sk_clone = Rc::clone(&d.sk);
  std::mem::drop(d);
  d_sk_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.push_preds
// Variant: uncurried
pub fn push_preds_1(radj: Rc<Array<u64>>, c: u64, e: u64, j: u64, lab: Rc<Array<u64>>, stk: Rc<Array<u64>>, sp_1: u64) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  push_preds(radj, c, e, j, lab, stk, sp_1, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.push_preds (local: push_preds)
// Variant: uncurried, lifted
pub fn push_preds(radj: Rc<Array<u64>>, c: u64, e: u64, j: u64, lab: Rc<Array<u64>>, stk: Rc<Array<u64>>, sp_1: u64, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let tmp = ltb(j, e);
  match bdec(tmp) {
    sumbool::left => {
      let w = rocq_array::get::<u64>(&radj, j);
      let tmp_1 = rocq_array::get::<u64>(&lab, w);
      if eqb(tmp_1, 0u64) {
        let tmp_2 = add(j, 1u64);
        let tmp_3 = rocq_array::set::<u64>(lab, w, c);
        let tmp_4 = rocq_array::set::<u64>(stk, sp_1, w);
        push_preds(radj, c, e, tmp_2, tmp_3, tmp_4, add(sp_1, 1u64), ())
      } else {
        push_preds(radj, c, e, add(j, 1u64), lab, stk, sp_1, ())
      }
    },
    sumbool::right => {
      std::mem::drop(radj);
      ((lab, stk), sp_1)
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.cc
pub fn cc_owned(d: Rc<d2>) -> u64 {
  let d_cc_clone = Clone::clone(&d.cc);
  std::mem::drop(d);
  d_cc_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.cc
// Variant: borrowed
pub fn cc(d: &Rc<d2>) -> u64 {
  let tmp = d;
  Clone::clone(&tmp.cc)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.lb
pub fn lb_owned(d: Rc<d2>) -> Rc<Array<u64>> {
  let d_lb_clone = Rc::clone(&d.lb);
  std::mem::drop(d);
  d_lb_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.lb
// Variant: borrowed
pub fn lb(d: &Rc<d2>) -> Rc<Array<u64>> {
  let tmp = d;
  Rc::clone(&tmp.lb)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.ii
// Variant: borrowed
pub fn ii(d: &Rc<d2>) -> u64 {
  let tmp = d;
  Clone::clone(&tmp.ii)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.asg_step
// Variant: uncurried
pub fn asg_step(roff: Rc<Array<u64>>, radj: Rc<Array<u64>>, post: Rc<Array<u64>>, s: Rc<d2>) -> Rc<option<Rc<d2>>> {
  let tmp = sq(&s);
  if ltb(0u64, tmp) {
    std::mem::drop(post);
    let tmp_1 = sq(&s);
    let t = sub(tmp_1, 1u64);
    let s_clone = Rc::clone(&s);
    let tmp_2 = sk(s_clone);
    let u = rocq_array::get::<u64>(&tmp_2, t);
    std::mem::drop(tmp_2);
    let tmp_3 = cc(&s);
    let tmp_4 = rocq_array::get::<u64>(&roff, add(u, 1u64));
    let tmp_5 = rocq_array::get::<u64>(&roff, u);
    std::mem::drop(roff);
    let s_clone_1 = Rc::clone(&s);
    let tmp_6 = lb_owned(s_clone_1);
    let s_clone_2 = Rc::clone(&s);
    let tmp_7 = sk(s_clone_2);
    let r = push_preds_1(radj, tmp_3, tmp_4, tmp_5, tmp_6, tmp_7, t);
    let r_clone = Clone::clone(&r);
    let tmp_8 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r_clone));
    let r_clone_1 = Clone::clone(&r);
    let tmp_9 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r_clone_1));
    let tmp_10 = snd::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r);
    let tmp_11 = ii(&s);
    let tmp_12 = Rc::new(d2 { lb: tmp_8, sk: tmp_9, sq: tmp_10, ii: tmp_11, cc: cc_owned(s) });
    Rc::new(option::<Rc<d2>>::Some(tmp_12))
  } else {
    let tmp_13 = ii(&s);
    if ltb(0u64, tmp_13) {
      let i = sub(ii(&s), 1u64);
      let r = rocq_array::get::<u64>(&post, i);
      let tmp_14 = lb(&s);
      let tmp_15 = rocq_array::get::<u64>(&tmp_14, r);
      if eqb(tmp_15, 0u64) {
        std::mem::drop(roff);
        std::mem::drop(radj);
        std::mem::drop(tmp_14);
        std::mem::drop(post);
        let s_clone_3 = Rc::clone(&s);
        let tmp_16 = lb_owned(s_clone_3);
        let tmp_17 = cc(&s);
        let tmp_18 = rocq_array::set::<u64>(tmp_16, r, add(tmp_17, 1u64));
        let s_clone_4 = Rc::clone(&s);
        let tmp_19 = sk(s_clone_4);
        let tmp_20 = rocq_array::set::<u64>(tmp_19, 0u64, r);
        let tmp_21 = Rc::new(d2 { lb: tmp_18, sk: tmp_20, sq: 1u64, ii: i, cc: add(cc_owned(s), 1u64) });
        Rc::new(option::<Rc<d2>>::Some(tmp_21))
      } else {
        std::mem::drop(roff);
        std::mem::drop(radj);
        std::mem::drop(tmp_14);
        std::mem::drop(post);
        let s_clone_5 = Rc::clone(&s);
        let tmp_22 = lb_owned(s_clone_5);
        let s_clone_6 = Rc::clone(&s);
        let tmp_23 = sk(s_clone_6);
        let tmp_24 = sq(&s);
        let tmp_25 = Rc::new(d2 { lb: tmp_22, sk: tmp_23, sq: tmp_24, ii: i, cc: cc_owned(s) });
        Rc::new(option::<Rc<d2>>::Some(tmp_25))
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
pub fn assign_1(roff: Rc<Array<u64>>, radj: Rc<Array<u64>>, post: Rc<Array<u64>>, s: Rc<d2>, bound: u64, steps: u64) -> Rc<d2> {
  assign(roff, radj, post, s, bound, steps, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.assign (local: assign)
// Variant: uncurried, lifted
pub fn assign(roff: Rc<Array<u64>>, radj: Rc<Array<u64>>, post: Rc<Array<u64>>, s: Rc<d2>, bound: u64, steps: u64, _H: ()) -> Rc<d2> {
  let tmp = ltb(steps, bound);
  match bdec(tmp) {
    sumbool::left => {
      let roff_clone = Rc::clone(&roff);
      let radj_clone = Rc::clone(&radj);
      let post_clone = Rc::clone(&post);
      let s_clone = Rc::clone(&s);
      let tmp_1 = asg_step(roff_clone, radj_clone, post_clone, s_clone);
      let (v32, v33) = __rocq_reuse::reset(tmp_1, |__payload| Clone::clone(__payload));
      std::mem::drop(v33);
      match v32 {
        option::Some(v38) => {
          std::mem::drop(s);
          assign(roff, radj, post, v38, bound, add(steps, 1u64), ())
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.merge_loop
// Variant: uncurried
pub fn merge_loop_1(le: Rc<dyn Fn(u64, u64) -> bool>, a: Rc<Array<u64>>, t: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64) -> Rc<Array<u64>> {
  merge_loop(le, a, t, mid, hi, i, j, k, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.merge_loop (local: merge_loop)
// Variant: uncurried, lifted
pub fn merge_loop(le: Rc<dyn Fn(u64, u64) -> bool>, a: Rc<Array<u64>>, t: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = ltb(i, mid);
      let tmp_2 = leb(hi, j);
      let tmp_3 = rocq_array::get::<u64>(&a, i);
      let tmp_4 = rocq_array::get::<u64>(&a, j);
      let le_ref: &Rc<dyn Fn(u64, u64) -> bool> = &le;
      let tmp_5 = le_ref(tmp_3, tmp_4);
      let tmp_6 = orb(tmp_2, tmp_5);
      if andb(tmp_1, tmp_6) {
        let tmp_7 = rocq_array::get::<u64>(&a, i);
        let tmp_8 = rocq_array::set::<u64>(t, k, tmp_7);
        merge_loop(le, a, tmp_8, mid, hi, add(i, 1u64), j, add(k, 1u64), ())
      } else {
        let tmp_9 = rocq_array::get::<u64>(&a, j);
        let tmp_10 = rocq_array::set::<u64>(t, k, tmp_9);
        merge_loop(le, a, tmp_10, mid, hi, i, add(j, 1u64), add(k, 1u64), ())
      }
    },
    sumbool::right => {
      std::mem::drop(le);
      std::mem::drop(a);
      t
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.copy_back
// Variant: uncurried
pub fn copy_back_1(t: Rc<Array<u64>>, a: Rc<Array<u64>>, hi: u64, k: u64) -> Rc<Array<u64>> {
  copy_back(t, a, hi, k, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.copy_back (local: copy_back)
// Variant: uncurried, lifted
pub fn copy_back(t: Rc<Array<u64>>, a: Rc<Array<u64>>, hi: u64, k: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&t, k);
      let tmp_2 = rocq_array::set::<u64>(a, k, tmp_1);
      copy_back(t, tmp_2, hi, add(k, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(t);
      a
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.msort
// Variant: uncurried
pub fn msort_1(le: Rc<dyn Fn(u64, u64) -> bool>, a: Rc<Array<u64>>, t: Rc<Array<u64>>, lo: u64, hi: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  msort(le, a, t, lo, hi, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(le: Rc<dyn Fn(u64, u64) -> bool>, a: Rc<Array<u64>>, t: Rc<Array<u64>>, lo: u64, hi: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(lo, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = ltb(1u64, sub(hi, lo));
      match bdec(tmp_1) {
        sumbool::left => {
          let tmp_2 = sub(hi, lo);
          let mid = add(lo, div(tmp_2, 2u64));
          let le_clone: Rc<dyn Fn(u64, u64) -> bool> = Rc::clone(&le);
          let r1 = msort(le_clone, a, t, lo, mid, ());
          let r1_clone = Clone::clone(&r1);
          let tmp_3 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(r1_clone);
          let tmp_4 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(r1);
          let le_clone_1: Rc<dyn Fn(u64, u64) -> bool> = Rc::clone(&le);
          let r2 = msort(le_clone_1, tmp_3, tmp_4, mid, hi, ());
          let r2_clone = Clone::clone(&r2);
          let tmp_5 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(r2_clone);
          let r2_clone_1 = Clone::clone(&r2);
          let tmp_6 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(r2_clone_1);
          let t3 = merge_loop_1(le, tmp_5, tmp_6, mid, hi, lo, mid, lo);
          let tmp_7 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(r2);
          let t3_clone = Rc::clone(&t3);
          let tmp_8 = copy_back_1(t3_clone, tmp_7, hi, lo);
          (tmp_8, t3)
        },
        sumbool::right => {
          std::mem::drop(le);
          (a, t)
        },
      }
    },
    sumbool::right => {
      std::mem::drop(le);
      (a, t)
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.name_le
// Variant: borrowed, uncurried
pub fn name_le(names: &Rc<Array<Rc<rocq_string::RocqString>>>, a: u64, b: u64) -> bool {
  let a_1 = a;
  let b_1 = b;
  let tmp = rocq_array::get::<Rc<rocq_string::RocqString>>(names, a_1);
  let tmp_1 = rocq_array::get::<Rc<rocq_string::RocqString>>(names, b_1);
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
pub fn iota_loop_1(n: u64, k: u64, a: Rc<Array<u64>>) -> Rc<Array<u64>> {
  iota_loop(n, k, a, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.iota_loop (local: iota_loop)
// Variant: uncurried, lifted
pub fn iota_loop(n: u64, k: u64, a: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(k, 1u64);
      let tmp_2 = rocq_array::set::<u64>(a, k, k);
      iota_loop(n, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      a
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.gord
pub fn gord(d: Rc<d3>) -> Rc<Array<u64>> {
  let d_gord_clone = Rc::clone(&d.gord);
  std::mem::drop(d);
  d_gord_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.gn
pub fn gn_owned(d: Rc<d3>) -> u64 {
  let d_gn_clone = Clone::clone(&d.gn);
  std::mem::drop(d);
  d_gn_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.gn
// Variant: borrowed
pub fn gn(d: &Rc<d3>) -> u64 {
  let tmp = d;
  Clone::clone(&tmp.gn)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.av
pub fn av(d: Rc<d3>) -> Rc<Array<Rc<rocq_string::RocqString>>> {
  let d_av_clone = Rc::clone(&d.av);
  std::mem::drop(d);
  d_av_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.an
pub fn an_owned(d: Rc<d3>) -> u64 {
  let d_an_clone = Clone::clone(&d.an);
  std::mem::drop(d);
  d_an_clone
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.an
// Variant: borrowed
pub fn an(d: &Rc<d3>) -> u64 {
  let tmp = d;
  Clone::clone(&tmp.an)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.emit_loop
// Variant: uncurried
pub fn emit_loop_1(names: Rc<Array<Rc<rocq_string::RocqString>>>, lab: Rc<Array<u64>>, csz: Rc<Array<u64>>, boff: Rc<Array<u64>>, badj: Rc<Array<u64>>, byname: Rc<Array<u64>>, V: u64, k: u64, s: Rc<d3>) -> Rc<d3> {
  emit_loop(names, lab, csz, boff, badj, byname, V, k, s, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.emit_loop (local: emit_loop)
// Variant: uncurried, lifted
pub fn emit_loop(names: Rc<Array<Rc<rocq_string::RocqString>>>, lab: Rc<Array<u64>>, csz: Rc<Array<u64>>, boff: Rc<Array<u64>>, badj: Rc<Array<u64>>, byname: Rc<Array<u64>>, V: u64, k: u64, s: Rc<d3>, _H: ()) -> Rc<d3> {
  let tmp = ltb(k, V);
  match bdec(tmp) {
    sumbool::left => {
      let v = rocq_array::get::<u64>(&byname, k);
      let c = rocq_array::get::<u64>(&lab, v);
      let tmp_1 = rocq_array::get::<u64>(&csz, c);
      if ltb(1u64, tmp_1) {
        let tmp_2 = rocq_array::get::<u64>(&boff, c);
        let tmp_3 = rocq_array::get::<u64>(&badj, tmp_2);
        if eqb(tmp_3, v) {
          let tmp_4 = add(k, 1u64);
          let s_clone = Rc::clone(&s);
          let tmp_5 = gord(s_clone);
          let tmp_6 = gn(&s);
          let tmp_7 = rocq_array::set::<u64>(tmp_5, tmp_6, c);
          let tmp_8 = gn(&s);
          let tmp_9 = add(tmp_8, 1u64);
          let s_clone_1 = Rc::clone(&s);
          let tmp_10 = av(s_clone_1);
          emit_loop(names, lab, csz, boff, badj, byname, V, tmp_4, Rc::new(d3 { gord: tmp_7, gn: tmp_9, av: tmp_10, an: an_owned(s) }), ())
        } else {
          emit_loop(names, lab, csz, boff, badj, byname, V, add(k, 1u64), s, ())
        }
      } else {
        let tmp_11 = add(k, 1u64);
        let s_clone_2 = Rc::clone(&s);
        let tmp_12 = gord(s_clone_2);
        let tmp_13 = gn(&s);
        let s_clone_3 = Rc::clone(&s);
        let tmp_14 = av(s_clone_3);
        let tmp_15 = an(&s);
        let tmp_16 = rocq_array::get::<Rc<rocq_string::RocqString>>(&names, v);
        let tmp_17 = rocq_array::set::<Rc<rocq_string::RocqString>>(tmp_14, tmp_15, tmp_16);
        emit_loop(names, lab, csz, boff, badj, byname, V, tmp_11, Rc::new(d3 { gord: tmp_12, gn: tmp_13, av: tmp_17, an: add(an_owned(s), 1u64) }), ())
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
pub fn copy_loop_1(src: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, k: u64, dst: Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<rocq_string::RocqString>>> {
  copy_loop(src, n, k, dst, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.copy_loop (local: copy_loop)
// Variant: uncurried, lifted
pub fn copy_loop(src: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, k: u64, dst: Rc<Array<Rc<rocq_string::RocqString>>>, _H: ()) -> Rc<Array<Rc<rocq_string::RocqString>>> {
  let tmp = ltb(k, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(k, 1u64);
      let tmp_2 = rocq_array::get::<Rc<rocq_string::RocqString>>(&src, k);
      let tmp_3 = rocq_array::set::<Rc<rocq_string::RocqString>>(dst, k, tmp_2);
      copy_loop(src, n, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.inner_loop
// Variant: uncurried
pub fn inner_loop_1(names: Rc<Array<Rc<rocq_string::RocqString>>>, badj: Rc<Array<u64>>, st: u64, n: u64, k: u64, g: Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<rocq_string::RocqString>>> {
  inner_loop(names, badj, st, n, k, g, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.inner_loop (local: inner_loop)
// Variant: uncurried, lifted
pub fn inner_loop(names: Rc<Array<Rc<rocq_string::RocqString>>>, badj: Rc<Array<u64>>, st: u64, n: u64, k: u64, g: Rc<Array<Rc<rocq_string::RocqString>>>, _H: ()) -> Rc<Array<Rc<rocq_string::RocqString>>> {
  let tmp = ltb(k, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(k, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&badj, add(st, k));
      let tmp_3 = rocq_array::get::<Rc<rocq_string::RocqString>>(&names, tmp_2);
      let tmp_4 = rocq_array::set::<Rc<rocq_string::RocqString>>(g, k, tmp_3);
      inner_loop(names, badj, st, n, tmp_1, tmp_4, ())
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
pub fn group_arr(names: Rc<Array<Rc<rocq_string::RocqString>>>, boff: Rc<Array<u64>>, badj: Rc<Array<u64>>, c: u64) -> Rc<Array<Rc<rocq_string::RocqString>>> {
  let st = rocq_array::get::<u64>(&boff, c);
  let tmp = rocq_array::get::<u64>(&boff, add(c, 1u64));
  std::mem::drop(boff);
  let n = sub(tmp, st);
  let tmp_1 = make(0u64, 0u64);
  let tmp_2 = rocq_array::make::<Rc<rocq_string::RocqString>>(n, tmp_1);
  inner_loop_1(names, badj, st, n, 0u64, tmp_2)
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.groups_loop
// Variant: uncurried
pub fn groups_loop_1(names: Rc<Array<Rc<rocq_string::RocqString>>>, boff: Rc<Array<u64>>, badj: Rc<Array<u64>>, gord_1: Rc<Array<u64>>, G: u64, g: u64, out: Rc<Array<Rc<Array<Rc<rocq_string::RocqString>>>>>) -> Rc<Array<Rc<Array<Rc<rocq_string::RocqString>>>>> {
  groups_loop(names, boff, badj, gord_1, G, g, out, ())
}

// Rocq: Loopycabdrivers.loopycabdrivers_implem.groups_loop (local: groups_loop)
// Variant: uncurried, lifted
pub fn groups_loop(names: Rc<Array<Rc<rocq_string::RocqString>>>, boff: Rc<Array<u64>>, badj: Rc<Array<u64>>, gord_1: Rc<Array<u64>>, G: u64, g: u64, out: Rc<Array<Rc<Array<Rc<rocq_string::RocqString>>>>>, _H: ()) -> Rc<Array<Rc<Array<Rc<rocq_string::RocqString>>>>> {
  let tmp = ltb(g, G);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(g, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&gord_1, g);
      let names_clone = Rc::clone(&names);
      let boff_clone = Rc::clone(&boff);
      let badj_clone = Rc::clone(&badj);
      let tmp_3 = group_arr(names_clone, boff_clone, badj_clone, tmp_2);
      let tmp_4 = rocq_array::set::<Rc<Array<Rc<rocq_string::RocqString>>>>(out, g, tmp_3);
      groups_loop(names, boff, badj, gord_1, G, tmp_1, tmp_4, ())
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
pub fn loopy_impl(x: Rc<Array<Rc<rocq_string::RocqString>>>, y: Rc<Array<Rc<rocq_string::RocqString>>>) -> (Rc<Array<Rc<Array<Rc<rocq_string::RocqString>>>>>, Rc<Array<Rc<rocq_string::RocqString>>>) {
  let m = rocq_array::length::<Rc<rocq_string::RocqString>>(&x);
  let tmp = add(__rocq_global_19, mul(2u64, m));
  let tmp_1 = rocq_array::make::<u64>(add(tmp, 1u64), 0u64);
  let tmp_2 = add(mul(2u64, m), 1u64);
  let tmp_3 = empty_str(());
  let tmp_4 = rocq_array::make::<Rc<rocq_string::RocqString>>(tmp_2, tmp_3);
  let st0 = Rc::new(hstate { ht: tmp_1, hn: tmp_4, hc: 0u64 });
  let tmp_5 = rocq_array::make::<u64>(m, 0u64);
  let tmp_6 = rocq_array::make::<u64>(m, 0u64);
  let r0 = idloop_1(x, y, m, 0u64, st0, tmp_5, tmp_6);
  let r0_clone = Clone::clone(&r0);
  let st = fst::<Rc<hstate>, Rc<Array<u64>>>(fst::<(Rc<hstate>, Rc<Array<u64>>), Rc<Array<u64>>>(r0_clone));
  let r0_clone_1 = Clone::clone(&r0);
  let is = snd::<Rc<hstate>, Rc<Array<u64>>>(fst::<(Rc<hstate>, Rc<Array<u64>>), Rc<Array<u64>>>(r0_clone_1));
  let id = snd::<(Rc<hstate>, Rc<Array<u64>>), Rc<Array<u64>>>(r0);
  let V = hc(&st);
  let names = hn(st);
  let is_clone = Rc::clone(&is);
  let callback: Rc<dyn Fn(u64) -> u64> = Rc::new({
    move |k: u64| -> u64 {
      rocq_array::get::<u64>(&is_clone, k)
    }
  });
  let id_clone = Rc::clone(&id);
  let callback_1: Rc<dyn Fn(u64) -> u64> = Rc::new({
    move |k: u64| -> u64 {
      rocq_array::get::<u64>(&id_clone, k)
    }
  });
  let g = csr(V, m, callback, callback_1);
  let callback_2: Rc<dyn Fn(u64) -> u64> = Rc::new({
    let __anf_capture_176 = id;
    move |k: u64| -> u64 {
      rocq_array::get::<u64>(&__anf_capture_176, k)
    }
  });
  let callback_3: Rc<dyn Fn(u64) -> u64> = Rc::new({
    let __anf_capture_189 = is;
    move |k: u64| -> u64 {
      rocq_array::get::<u64>(&__anf_capture_189, k)
    }
  });
  let gt = csr(V, m, callback_2, callback_3);
  let bound = add(mul(3u64, V), 1u64);
  let g_clone = Clone::clone(&g);
  let tmp_7 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(g_clone);
  let tmp_8 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(g);
  let tmp_9 = rocq_array::make::<u64>(V, 0u64);
  let tmp_10 = rocq_array::make::<u64>(V, 0u64);
  let tmp_11 = rocq_array::make::<u64>(V, 0u64);
  let tmp_12 = rocq_array::make::<u64>(V, 0u64);
  let post = dfs_1(V, tmp_7, tmp_8, Rc::new(d1 { mk: tmp_9, sv: tmp_10, sc: tmp_11, po: tmp_12, sp: 0u64, np: 0u64, rt: 0u64 }), bound, 0u64);
  let gt_clone = Clone::clone(&gt);
  let tmp_13 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(gt_clone);
  let tmp_14 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(gt);
  let tmp_15 = rocq_array::make::<u64>(V, 0u64);
  let tmp_16 = rocq_array::make::<u64>(V, 0u64);
  let s2 = assign_1(tmp_13, tmp_14, post, Rc::new(d2 { lb: tmp_15, sk: tmp_16, sq: 0u64, ii: V, cc: 0u64 }), bound, 0u64);
  let s2_clone = Rc::clone(&s2);
  let lab = lb_owned(s2_clone);
  let C = cc_owned(s2);
  let lab_clone = Rc::clone(&lab);
  let callback_4: Rc<dyn Fn(u64) -> u64> = Rc::new({
    move |v: u64| -> u64 {
      rocq_array::get::<u64>(&lab_clone, v)
    }
  });
  let tmp_17 = rocq_array::make::<u64>(add(C, 1u64), 0u64);
  let csz = cnt_loop_1(callback_4, V, 0u64, tmp_17);
  let names_clone = Rc::clone(&names);
  let callback_5: Rc<dyn Fn(u64, u64) -> bool> = Rc::new({
    move |v414: u64, v415: u64| -> bool {
      name_le(&names_clone, v414, v415)
    }
  });
  let tmp_18 = rocq_array::make::<u64>(V, 0u64);
  let tmp_19 = iota_loop_1(V, 0u64, tmp_18);
  let tmp_20 = rocq_array::make::<u64>(V, 0u64);
  let byname = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(msort_1(callback_5, tmp_19, tmp_20, 0u64, V));
  let tmp_21 = add(C, 1u64);
  let byname_clone = Rc::clone(&byname);
  let lab_clone_1 = Rc::clone(&lab);
  let callback_6: Rc<dyn Fn(u64) -> u64> = Rc::new({
    move |k: u64| -> u64 {
      let byname = &byname_clone;
      let lab = &lab_clone_1;
      let tmp_22 = rocq_array::get::<u64>(byname, k);
      rocq_array::get::<u64>(lab, tmp_22)
    }
  });
  let byname_clone_1 = Rc::clone(&byname);
  let callback_7: Rc<dyn Fn(u64) -> u64> = Rc::new({
    move |k: u64| -> u64 {
      rocq_array::get::<u64>(&byname_clone_1, k)
    }
  });
  let b = csr(tmp_21, V, callback_6, callback_7);
  let b_clone = Clone::clone(&b);
  let tmp_23 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(b_clone);
  let b_clone_1 = Clone::clone(&b);
  let tmp_24 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(b_clone_1);
  let tmp_25 = rocq_array::make::<u64>(V, 0u64);
  let tmp_26 = empty_str(());
  let tmp_27 = rocq_array::make::<Rc<rocq_string::RocqString>>(V, tmp_26);
  let tmp_28 = Rc::new(d3 { gord: tmp_25, gn: 0u64, av: tmp_27, an: 0u64 });
  let names_clone_1 = Rc::clone(&names);
  let s3 = emit_loop_1(names_clone_1, lab, csz, tmp_23, tmp_24, byname, V, 0u64, tmp_28);
  let s3_clone = Rc::clone(&s3);
  let tmp_29 = av(s3_clone);
  let tmp_30 = an(&s3);
  let tmp_31 = an(&s3);
  let tmp_32 = empty_str(());
  let tmp_33 = rocq_array::make::<Rc<rocq_string::RocqString>>(tmp_31, tmp_32);
  let avoid = copy_loop_1(tmp_29, tmp_30, 0u64, tmp_33);
  let b_clone_2 = Clone::clone(&b);
  let tmp_34 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(b_clone_2);
  let tmp_35 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(b);
  let s3_clone_1 = Rc::clone(&s3);
  let tmp_36 = gord(s3_clone_1);
  let tmp_37 = gn(&s3);
  let tmp_38 = gn_owned(s3);
  let tmp_39 = empty_str(());
  let tmp_40 = rocq_array::make::<Rc<rocq_string::RocqString>>(0u64, tmp_39);
  let tmp_41 = rocq_array::make::<Rc<Array<Rc<rocq_string::RocqString>>>>(tmp_38, tmp_40);
  let groups = groups_loop_1(names, tmp_34, tmp_35, tmp_36, tmp_37, 0u64, tmp_41);
  (groups, avoid)
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
const __rocq_global_19: u64 = 65536u64;
const __rocq_global_280: u64 = 65535u64;