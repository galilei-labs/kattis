#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub struct fh {
  pub hkey: Rc<Array<u64>>,
  pub hpar: Rc<Array<u64>>,
  pub hchd: Rc<Array<u64>>,
  pub hlft: Rc<Array<u64>>,
  pub hrgt: Rc<Array<u64>>,
  pub hdeg: Rc<Array<u64>>,
  pub hmrk: Rc<Array<u64>>,
  pub hbuf: Rc<Array<u64>>,
  pub hmin: u64,
}

impl Clone for fh {
  fn clone(&self) -> Self {
    match self {
      fh { hkey: __field0, hpar: __field1, hchd: __field2, hlft: __field3, hrgt: __field4, hdeg: __field5, hmrk: __field6, hbuf: __field7, hmin: __field8 } => fh { hkey: Clone::clone(__field0), hpar: Clone::clone(__field1), hchd: Clone::clone(__field2), hlft: Clone::clone(__field3), hrgt: Clone::clone(__field4), hdeg: Clone::clone(__field5), hmrk: Clone::clone(__field6), hbuf: Clone::clone(__field7), hmin: Clone::clone(__field8) },
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

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = u64;

// Rocq: Fulltank.fulltank_implem.nil
pub fn nil() -> u64 {
  9223372036854775807u64
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

// Rocq: Fulltank.fulltank_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
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

// Rocq: Fulltank.fulltank_implem.build
// Variant: uncurried
pub fn build_1(U: Rc<Array<u64>>, V: Rc<Array<u64>>, head: Rc<Array<u64>>, nxt: Rc<Array<u64>>, j: u64, m: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  build(U, V, head, nxt, j, m, ())
}

// Rocq: Fulltank.fulltank_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(U: Rc<Array<u64>>, V: Rc<Array<u64>>, head: Rc<Array<u64>>, nxt: Rc<Array<u64>>, j: u64, m: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(j, m);
  match bdec(tmp) {
    sumbool::left => {
      let a = rocq_array::get::<u64>(&U, j);
      let b = rocq_array::get::<u64>(&V, j);
      let e1 = add(mul(2u64, j), 1u64);
      let e2 = add(mul(2u64, j), 2u64);
      let tmp_1 = rocq_array::get::<u64>(&head, a);
      let nxt1 = rocq_array::set::<u64>(nxt, e1, tmp_1);
      let head1 = rocq_array::set::<u64>(head, a, e1);
      let tmp_2 = rocq_array::get::<u64>(&head1, b);
      let nxt2 = rocq_array::set::<u64>(nxt1, e2, tmp_2);
      let head2 = rocq_array::set::<u64>(head1, b, e2);
      build(U, V, head2, nxt2, add(j, 1u64), m, ())
    },
    sumbool::right => {
      std::mem::drop(U);
      std::mem::drop(V);
      (head, nxt)
    },
  }
}

// Rocq: Fulltank.fulltank_implem.hmin
pub fn hmin_owned(f: Rc<fh>) -> u64 {
  let f_hmin_clone = Clone::clone(&f.hmin);
  std::mem::drop(f);
  f_hmin_clone
}

// Rocq: Fulltank.fulltank_implem.hmin
// Variant: borrowed
pub fn hmin(f: &Rc<fh>) -> u64 {
  let tmp = f;
  Clone::clone(&tmp.hmin)
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Fulltank.fulltank_implem.hchd
pub fn hchd(f: Rc<fh>) -> Rc<Array<u64>> {
  let f_hchd_clone = Rc::clone(&f.hchd);
  std::mem::drop(f);
  f_hchd_clone
}

// Rocq: Fulltank.fulltank_implem.hdeg
pub fn hdeg(f: Rc<fh>) -> Rc<Array<u64>> {
  let f_hdeg_clone = Rc::clone(&f.hdeg);
  std::mem::drop(f);
  f_hdeg_clone
}

// Rocq: Fulltank.fulltank_implem.hbuf
pub fn hbuf(f: Rc<fh>) -> Rc<Array<u64>> {
  let f_hbuf_clone = Rc::clone(&f.hbuf);
  std::mem::drop(f);
  f_hbuf_clone
}

// Rocq: Fulltank.fulltank_implem.s_min
// Variant: uncurried
pub fn s_min(h: Rc<fh>, v: u64) -> Rc<fh> {
  let (v2, v3) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v2 {
    fh { hkey: v16, hpar: v18, hchd: v20, hlft: v22, hrgt: v24, hdeg: v26, hmrk: v28, hbuf: v30, hmin: _v32 } => {
      __rocq_reuse::rebuild(v3, fh { hkey: v16, hpar: v18, hchd: v20, hlft: v22, hrgt: v24, hdeg: v26, hmrk: v28, hbuf: v30, hmin: v })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.hrgt
pub fn hrgt(f: Rc<fh>) -> Rc<Array<u64>> {
  let f_hrgt_clone = Rc::clone(&f.hrgt);
  std::mem::drop(f);
  f_hrgt_clone
}

// Rocq: Fulltank.fulltank_implem.s_par
// Variant: uncurried
pub fn s_par(h: Rc<fh>, i: u64, v: u64) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      let tmp = rocq_array::set::<u64>(v19, i, v);
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: tmp, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.s_buf
// Variant: uncurried
pub fn s_buf(h: Rc<fh>, i: u64, v: u64) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      let tmp = rocq_array::set::<u64>(v31, i, v);
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: tmp, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.hkey
pub fn hkey(f: Rc<fh>) -> Rc<Array<u64>> {
  let f_hkey_clone = Rc::clone(&f.hkey);
  std::mem::drop(f);
  f_hkey_clone
}

// Rocq: Fulltank.fulltank_implem.s_rgt
// Variant: uncurried
pub fn s_rgt(h: Rc<fh>, i: u64, v: u64) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      let tmp = rocq_array::set::<u64>(v25, i, v);
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: tmp, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.s_lft
// Variant: uncurried
pub fn s_lft(h: Rc<fh>, i: u64, v: u64) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      let tmp = rocq_array::set::<u64>(v23, i, v);
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v19, hchd: v21, hlft: tmp, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.s_chd
// Variant: uncurried
pub fn s_chd(h: Rc<fh>, i: u64, v: u64) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      let tmp = rocq_array::set::<u64>(v21, i, v);
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v19, hchd: tmp, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.ring_ins
// Variant: uncurried
pub fn ring_ins(h: Rc<fh>, a: u64, x: u64) -> Rc<fh> {
  let h_clone = Rc::clone(&h);
  let tmp = hrgt(h_clone);
  let b = rocq_array::get::<u64>(&tmp, a);
  std::mem::drop(tmp);
  let tmp_1 = s_lft(s_rgt(h, a, x), x, a);
  s_lft(s_rgt(tmp_1, x, b), b, x)
}

// Rocq: Fulltank.fulltank_implem.s_mrk
// Variant: uncurried
pub fn s_mrk(h: Rc<fh>, i: u64, v: u64) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      let tmp = rocq_array::set::<u64>(v29, i, v);
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: tmp, hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.s_deg
// Variant: uncurried
pub fn s_deg(h: Rc<fh>, i: u64, v: u64) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      let tmp = rocq_array::set::<u64>(v27, i, v);
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: tmp, hmrk: v29, hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.fh_link
// Variant: uncurried
pub fn fh_link(h: Rc<fh>, y: u64, x: u64) -> Rc<fh> {
  let h_clone = Rc::clone(&h);
  let tmp = hdeg(h_clone);
  let tmp_1 = rocq_array::get::<u64>(&tmp, x);
  let tmp_2 = 0u64;
  let h1 = if eqb(tmp_1, tmp_2) {
    std::mem::drop(tmp);
    s_rgt(s_lft(s_chd(h, x, y), y, y), y, y)
  } else {
    std::mem::drop(tmp);
    let h_clone_1 = Rc::clone(&h);
    let tmp_3 = hchd(h_clone_1);
    let tmp_4 = rocq_array::get::<u64>(&tmp_3, x);
    std::mem::drop(tmp_3);
    ring_ins(h, tmp_4, y)
  };
  let h1_clone = Rc::clone(&h1);
  let tmp_5 = s_par(h1_clone, y, x);
  let tmp_6 = hdeg(h1);
  let tmp_7 = rocq_array::get::<u64>(&tmp_6, x);
  std::mem::drop(tmp_6);
  s_mrk(s_deg(tmp_5, x, add(tmp_7, 1u64)), y, 0u64)
}

// Rocq: Fulltank.fulltank_implem.link_loop
// Variant: uncurried
pub fn link_loop_1(h: Rc<fh>, x: u64, d: u64, N: u64) -> (Rc<fh>, u64) {
  link_loop(h, x, d, N, ())
}

// Rocq: Fulltank.fulltank_implem.link_loop (local: link_loop)
// Variant: uncurried, lifted
pub fn link_loop(h: Rc<fh>, x: u64, d: u64, N: u64, _H: ()) -> (Rc<fh>, u64) {
  let tmp = ltb(d, N);
  match bdec(tmp) {
    sumbool::left => {
      let h_clone = Rc::clone(&h);
      let tmp_1 = hbuf(h_clone);
      let y = rocq_array::get::<u64>(&tmp_1, d);
      if eqb(y, __rocq_global_147) {
        std::mem::drop(tmp_1);
        (s_buf(h, d, x), d)
      } else {
        let h1 = s_buf(h, d, __rocq_global_147);
        let h1_clone = Rc::clone(&h1);
        let tmp_2 = hkey(h1_clone);
        let tmp_3 = rocq_array::get::<u64>(&tmp_2, y);
        let h1_clone_1 = Rc::clone(&h1);
        let tmp_4 = hkey(h1_clone_1);
        let tmp_5 = rocq_array::get::<u64>(&tmp_4, x);
        if ltb(tmp_3, tmp_5) {
          std::mem::drop(tmp_2);
          std::mem::drop(tmp_1);
          std::mem::drop(tmp_4);
          link_loop(fh_link(h1, x, y), y, add(d, 1u64), N, ())
        } else {
          std::mem::drop(tmp_2);
          std::mem::drop(tmp_1);
          std::mem::drop(tmp_4);
          link_loop(fh_link(h1, y, x), x, add(d, 1u64), N, ())
        }
      }
    },
    sumbool::right => {
      (h, d)
    },
  }
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Fulltank.fulltank_implem.proc
// Variant: uncurried
pub fn proc(h: Rc<fh>, w: u64, md: u64) -> (Rc<fh>, u64) {
  let h1 = s_par(h, w, __rocq_global_147);
  let h1_clone = Rc::clone(&h1);
  let tmp = hbuf(h1_clone);
  let N = rocq_array::length::<u64>(&tmp);
  let h1_clone_1 = Rc::clone(&h1);
  let tmp_1 = hdeg(h1_clone_1);
  let tmp_2 = rocq_array::get::<u64>(&tmp_1, w);
  let r = link_loop_1(h1, w, tmp_2, N);
  let r_clone = Clone::clone(&r);
  let tmp_3 = fst::<Rc<fh>, u64>(r_clone);
  let r_clone_1 = Clone::clone(&r);
  let tmp_4 = snd::<Rc<fh>, u64>(r_clone_1);
  let tmp_5 = if ltb(md, tmp_4) {
    std::mem::drop(tmp);
    std::mem::drop(tmp_1);
    snd::<Rc<fh>, u64>(r)
  } else {
    std::mem::drop(r);
    std::mem::drop(tmp);
    std::mem::drop(tmp_1);
    md
  };
  (tmp_3, tmp_5)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Fulltank.fulltank_implem.walk
// Variant: uncurried
pub fn walk_1(h: Rc<fh>, cur: u64, stop: u64, md: u64, cnt: u64) -> (Rc<fh>, u64) {
  walk(h, cur, stop, md, cnt, ())
}

// Rocq: Fulltank.fulltank_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(h: Rc<fh>, cur: u64, stop: u64, md: u64, cnt: u64, _H: ()) -> (Rc<fh>, u64) {
  if eqb(cur, stop) {
    (h, md)
  } else {
    let tmp = ltb(0u64, cnt);
    match bdec(tmp) {
      sumbool::left => {
        let h_clone = Rc::clone(&h);
        let tmp_1 = hrgt(h_clone);
        let nx = rocq_array::get::<u64>(&tmp_1, cur);
        std::mem::drop(tmp_1);
        let r = proc(h, cur, md);
        let r_clone = Clone::clone(&r);
        walk(fst::<Rc<fh>, u64>(r_clone), nx, stop, snd::<Rc<fh>, u64>(r), sub(cnt, 1u64), ())
      },
      sumbool::right => {
        (h, md)
      },
    }
  }
}

// Rocq: Fulltank.fulltank_implem.root_add
// Variant: uncurried
pub fn root_add(h: Rc<fh>, x: u64) -> Rc<fh> {
  let h_clone = Rc::clone(&h);
  let m = hmin_owned(h_clone);
  if eqb(m, __rocq_global_147) {
    s_min(s_rgt(s_lft(h, x, x), x, x), x)
  } else {
    let h1 = ring_ins(h, m, x);
    let h1_clone = Rc::clone(&h1);
    let tmp = hkey(h1_clone);
    let tmp_1 = rocq_array::get::<u64>(&tmp, x);
    let h1_clone_1 = Rc::clone(&h1);
    let tmp_2 = hkey(h1_clone_1);
    let tmp_3 = rocq_array::get::<u64>(&tmp_2, m);
    if ltb(tmp_1, tmp_3) {
      std::mem::drop(tmp_2);
      std::mem::drop(tmp);
      s_min(h1, x)
    } else {
      std::mem::drop(tmp_2);
      std::mem::drop(tmp);
      h1
    }
  }
}

// Rocq: Fulltank.fulltank_implem.rebuild
// Variant: uncurried
pub fn rebuild_1(h: Rc<fh>, d: u64, M: u64) -> Rc<fh> {
  rebuild(h, d, M, ())
}

// Rocq: Fulltank.fulltank_implem.rebuild (local: rebuild)
// Variant: uncurried, lifted
pub fn rebuild(h: Rc<fh>, d: u64, M: u64, _H: ()) -> Rc<fh> {
  let tmp = ltb(d, M);
  match bdec(tmp) {
    sumbool::left => {
      let h_clone = Rc::clone(&h);
      let tmp_1 = hbuf(h_clone);
      let x = rocq_array::get::<u64>(&tmp_1, d);
      let tmp_2 = __rocq_global_147;
      let h1 = if eqb(x, tmp_2) {
        std::mem::drop(tmp_1);
        h
      } else {
        std::mem::drop(tmp_1);
        root_add(s_buf(h, d, __rocq_global_147), x)
      };
      rebuild(h1, add(d, 1u64), M, ())
    },
    sumbool::right => {
      h
    },
  }
}

// Rocq: Fulltank.fulltank_implem.fh_extract
pub fn fh_extract(h: Rc<fh>) -> (Rc<fh>, u64) {
  let h_clone = Rc::clone(&h);
  let z = hmin_owned(h_clone);
  let h_clone_1 = Rc::clone(&h);
  let tmp = hchd(h_clone_1);
  let c = rocq_array::get::<u64>(&tmp, z);
  let h_clone_2 = Rc::clone(&h);
  let tmp_1 = hdeg(h_clone_2);
  let dz = rocq_array::get::<u64>(&tmp_1, z);
  let h_clone_3 = Rc::clone(&h);
  let tmp_2 = hbuf(h_clone_3);
  let N = rocq_array::length::<u64>(&tmp_2);
  let h0 = s_min(h, __rocq_global_147);
  let h0_clone = Rc::clone(&h0);
  let tmp_3 = hrgt(h0_clone);
  let tmp_4 = rocq_array::get::<u64>(&tmp_3, z);
  let r1 = walk_1(h0, tmp_4, z, 0u64, N);
  let tmp_5 = 0u64;
  let r2 = if eqb(dz, tmp_5) {
    std::mem::drop(tmp_2);
    std::mem::drop(tmp_3);
    std::mem::drop(tmp_1);
    std::mem::drop(tmp);
    r1
  } else {
    std::mem::drop(tmp_2);
    std::mem::drop(tmp_3);
    std::mem::drop(tmp_1);
    std::mem::drop(tmp);
    let r1_clone = Clone::clone(&r1);
    let tmp_6 = hrgt(fst::<Rc<fh>, u64>(r1_clone));
    let nx = rocq_array::get::<u64>(&tmp_6, c);
    std::mem::drop(tmp_6);
    let r1_clone_1 = Clone::clone(&r1);
    let r = proc(fst::<Rc<fh>, u64>(r1_clone_1), c, snd::<Rc<fh>, u64>(r1));
    let r_clone = Clone::clone(&r);
    walk_1(fst::<Rc<fh>, u64>(r_clone), nx, c, snd::<Rc<fh>, u64>(r), N)
  };
  let r2_clone = Clone::clone(&r2);
  let M = add(snd::<Rc<fh>, u64>(r2_clone), 1u64);
  (rebuild_1(fst::<Rc<fh>, u64>(r2), 0u64, M), z)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Fulltank.fulltank_implem.s_key
// Variant: uncurried
pub fn s_key(h: Rc<fh>, i: u64, v: u64) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      let tmp = rocq_array::set::<u64>(v17, i, v);
      __rocq_reuse::rebuild(v4, fh { hkey: tmp, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.fh_insert
// Variant: uncurried
pub fn fh_insert(h: Rc<fh>, x: u64, k: u64) -> Rc<fh> {
  root_add(s_mrk(s_deg(s_chd(s_par(s_key(h, x, k), x, __rocq_global_147), x, __rocq_global_147), x, 0u64), x, 0u64), x)
}

// Rocq: Fulltank.fulltank_implem.hpar
pub fn hpar(f: Rc<fh>) -> Rc<Array<u64>> {
  let f_hpar_clone = Rc::clone(&f.hpar);
  std::mem::drop(f);
  f_hpar_clone
}

// Rocq: Fulltank.fulltank_implem.hmrk
pub fn hmrk(f: Rc<fh>) -> Rc<Array<u64>> {
  let f_hmrk_clone = Rc::clone(&f.hmrk);
  std::mem::drop(f);
  f_hmrk_clone
}

// Rocq: Fulltank.fulltank_implem.hlft
pub fn hlft(f: Rc<fh>) -> Rc<Array<u64>> {
  let f_hlft_clone = Rc::clone(&f.hlft);
  std::mem::drop(f);
  f_hlft_clone
}

// Rocq: Fulltank.fulltank_implem.fh_cut
// Variant: uncurried
pub fn fh_cut(h: Rc<fh>, x: u64, y: u64) -> Rc<fh> {
  let h_clone = Rc::clone(&h);
  let tmp = hdeg(h_clone);
  let tmp_1 = rocq_array::get::<u64>(&tmp, y);
  let tmp_2 = 1u64;
  let h1 = if eqb(tmp_1, tmp_2) {
    std::mem::drop(tmp);
    s_chd(h, y, __rocq_global_147)
  } else {
    let h_clone_1 = Rc::clone(&h);
    let tmp_3 = hlft(h_clone_1);
    let a = rocq_array::get::<u64>(&tmp_3, x);
    let h_clone_2 = Rc::clone(&h);
    let tmp_4 = hrgt(h_clone_2);
    let b = rocq_array::get::<u64>(&tmp_4, x);
    let h_ = s_lft(s_rgt(h, a, b), b, a);
    let h__clone = Rc::clone(&h_);
    let tmp_5 = hchd(h__clone);
    let tmp_6 = rocq_array::get::<u64>(&tmp_5, y);
    if eqb(tmp_6, x) {
      std::mem::drop(tmp_5);
      std::mem::drop(tmp_3);
      std::mem::drop(tmp_4);
      std::mem::drop(tmp);
      s_chd(h_, y, b)
    } else {
      std::mem::drop(tmp_5);
      std::mem::drop(tmp_3);
      std::mem::drop(tmp_4);
      std::mem::drop(tmp);
      h_
    }
  };
  let h1_clone = Rc::clone(&h1);
  let tmp_7 = hdeg(h1_clone);
  let tmp_8 = rocq_array::get::<u64>(&tmp_7, y);
  std::mem::drop(tmp_7);
  let h2 = s_deg(h1, y, sub(tmp_8, 1u64));
  root_add(s_mrk(s_par(h2, x, __rocq_global_147), x, 0u64), x)
}

// Rocq: Fulltank.fulltank_implem.ccut
// Variant: uncurried
pub fn ccut_1(h: Rc<fh>, y: u64, cnt: u64) -> Rc<fh> {
  ccut(h, y, cnt, ())
}

// Rocq: Fulltank.fulltank_implem.ccut (local: ccut)
// Variant: uncurried, lifted
pub fn ccut(h: Rc<fh>, y: u64, cnt: u64, _H: ()) -> Rc<fh> {
  let tmp = ltb(0u64, cnt);
  match bdec(tmp) {
    sumbool::left => {
      let h_clone = Rc::clone(&h);
      let tmp_1 = hpar(h_clone);
      let z = rocq_array::get::<u64>(&tmp_1, y);
      if eqb(z, __rocq_global_147) {
        std::mem::drop(tmp_1);
        h
      } else {
        let h_clone_1 = Rc::clone(&h);
        let tmp_2 = hmrk(h_clone_1);
        let tmp_3 = rocq_array::get::<u64>(&tmp_2, y);
        if eqb(tmp_3, 0u64) {
          std::mem::drop(tmp_2);
          std::mem::drop(tmp_1);
          s_mrk(h, y, 1u64)
        } else {
          std::mem::drop(tmp_2);
          std::mem::drop(tmp_1);
          ccut(fh_cut(h, y, z), z, sub(cnt, 1u64), ())
        }
      }
    },
    sumbool::right => {
      h
    },
  }
}

// Rocq: Fulltank.fulltank_implem.fh_decrease
// Variant: uncurried
pub fn fh_decrease(h: Rc<fh>, x: u64, k: u64) -> Rc<fh> {
  let h1 = s_key(h, x, k);
  let h1_clone = Rc::clone(&h1);
  let tmp = hpar(h1_clone);
  let y = rocq_array::get::<u64>(&tmp, x);
  let tmp_1 = __rocq_global_147;
  let h2 = if eqb(y, tmp_1) {
    h1
  } else {
    let h1_clone_1 = Rc::clone(&h1);
    let tmp_2 = hkey(h1_clone_1);
    let tmp_3 = rocq_array::get::<u64>(&tmp_2, y);
    if ltb(k, tmp_3) {
      std::mem::drop(tmp_2);
      let h1_clone_2 = Rc::clone(&h1);
      let tmp_4 = hpar(h1_clone_2);
      let N = rocq_array::length::<u64>(&tmp_4);
      std::mem::drop(tmp_4);
      ccut_1(fh_cut(h1, x, y), y, N)
    } else {
      std::mem::drop(tmp_2);
      h1
    }
  };
  let h2_clone = Rc::clone(&h2);
  let tmp_5 = hkey(h2_clone);
  let tmp_6 = rocq_array::get::<u64>(&tmp_5, hmin(&h2));
  if ltb(k, tmp_6) {
    std::mem::drop(tmp_5);
    std::mem::drop(tmp);
    s_min(h2, x)
  } else {
    std::mem::drop(tmp_5);
    std::mem::drop(tmp);
    h2
  }
}

// Rocq: Fulltank.fulltank_implem.relax
// Variant: uncurried
pub fn relax(h: Rc<fh>, st: Rc<Array<u64>>, v: u64, nk: u64) -> (Rc<fh>, Rc<Array<u64>>) {
  let s = rocq_array::get::<u64>(&st, v);
  if eqb(s, 0u64) {
    let tmp = fh_insert(h, v, nk);
    let tmp_1 = rocq_array::set::<u64>(st, v, 1u64);
    (tmp, tmp_1)
  } else {
    if eqb(s, 1u64) {
      let h_clone = Rc::clone(&h);
      let tmp_2 = hkey(h_clone);
      let tmp_3 = rocq_array::get::<u64>(&tmp_2, v);
      if ltb(nk, tmp_3) {
        std::mem::drop(tmp_2);
        (fh_decrease(h, v, nk), st)
      } else {
        std::mem::drop(tmp_2);
        (h, st)
      }
    } else {
      (h, st)
    }
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Fulltank.fulltank_implem.edges
// Variant: uncurried
pub fn edges_1(U: Rc<Array<u64>>, V: Rc<Array<u64>>, Dl: Rc<Array<u64>>, nxt: Rc<Array<u64>>, C: u64, f: u64, kz: u64, hs: (Rc<fh>, Rc<Array<u64>>), e: u64) -> (Rc<fh>, Rc<Array<u64>>) {
  edges(U, V, Dl, nxt, C, f, kz, hs, e, ())
}

// Rocq: Fulltank.fulltank_implem.edges (local: edges)
// Variant: uncurried, lifted
pub fn edges(U: Rc<Array<u64>>, V: Rc<Array<u64>>, Dl: Rc<Array<u64>>, nxt: Rc<Array<u64>>, C: u64, f: u64, kz: u64, hs: (Rc<fh>, Rc<Array<u64>>), e: u64, _H: ()) -> (Rc<fh>, Rc<Array<u64>>) {
  if eqb(e, 0u64) {
    std::mem::drop(U);
    std::mem::drop(V);
    std::mem::drop(Dl);
    std::mem::drop(nxt);
    hs
  } else {
    let j = div(sub(e, 1u64), 2u64);
    let tmp = mod_(sub(e, 1u64), 2u64);
    let tmp_1 = 0u64;
    let y = if eqb(tmp, tmp_1) {
      rocq_array::get::<u64>(&V, j)
    } else {
      rocq_array::get::<u64>(&U, j)
    };
    let l = rocq_array::get::<u64>(&Dl, j);
    let hs1 = if leb(l, f) {
      let hs_clone = Clone::clone(&hs);
      let tmp_2 = fst::<Rc<fh>, Rc<Array<u64>>>(hs_clone);
      let tmp_3 = snd::<Rc<fh>, Rc<Array<u64>>>(hs);
      relax(tmp_2, tmp_3, add(mul(y, C), sub(f, l)), kz)
    } else {
      hs
    };
    let e_ = rocq_array::get::<u64>(&nxt, e);
    let tmp_4 = ltb(e_, e);
    match bdec(tmp_4) {
      sumbool::left => {
        edges(U, V, Dl, nxt, C, f, kz, hs1, e_, ())
      },
      sumbool::right => {
        std::mem::drop(U);
        std::mem::drop(V);
        std::mem::drop(nxt);
        std::mem::drop(Dl);
        hs1
      },
    }
  }
}

// Rocq: Fulltank.fulltank_implem.expand
// Variant: uncurried
pub fn expand(P: Rc<Array<u64>>, U: Rc<Array<u64>>, V: Rc<Array<u64>>, Dl: Rc<Array<u64>>, head: Rc<Array<u64>>, nxt: Rc<Array<u64>>, C: u64, cap: u64, hs: (Rc<fh>, Rc<Array<u64>>), z: u64) -> (Rc<fh>, Rc<Array<u64>>) {
  let x = div(z, C);
  let f = mod_(z, C);
  let hs_clone = Clone::clone(&hs);
  let tmp = hkey(fst::<Rc<fh>, Rc<Array<u64>>>(hs_clone));
  let kz = rocq_array::get::<u64>(&tmp, z);
  let hs1 = if ltb(f, cap) {
    std::mem::drop(tmp);
    let hs_clone_1 = Clone::clone(&hs);
    let tmp_1 = fst::<Rc<fh>, Rc<Array<u64>>>(hs_clone_1);
    let tmp_2 = snd::<Rc<fh>, Rc<Array<u64>>>(hs);
    let tmp_3 = add(z, 1u64);
    let tmp_4 = rocq_array::get::<u64>(&P, x);
    std::mem::drop(P);
    relax(tmp_1, tmp_2, tmp_3, add(kz, tmp_4))
  } else {
    std::mem::drop(P);
    std::mem::drop(tmp);
    hs
  };
  let tmp_5 = rocq_array::get::<u64>(&head, x);
  std::mem::drop(head);
  edges_1(U, V, Dl, nxt, C, f, kz, hs1, tmp_5)
}

// Rocq: Fulltank.fulltank_implem.dijk
// Variant: uncurried
pub fn dijk_1(P: Rc<Array<u64>>, U: Rc<Array<u64>>, V: Rc<Array<u64>>, Dl: Rc<Array<u64>>, head: Rc<Array<u64>>, nxt: Rc<Array<u64>>, C: u64, cap: u64, g: u64, hs: (Rc<fh>, Rc<Array<u64>>), cnt: u64) -> Rc<option<u64>> {
  dijk(P, U, V, Dl, head, nxt, C, cap, g, hs, cnt, ())
}

// Rocq: Fulltank.fulltank_implem.dijk (local: dijk)
// Variant: uncurried, lifted
pub fn dijk(P: Rc<Array<u64>>, U: Rc<Array<u64>>, V: Rc<Array<u64>>, Dl: Rc<Array<u64>>, head: Rc<Array<u64>>, nxt: Rc<Array<u64>>, C: u64, cap: u64, g: u64, hs: (Rc<fh>, Rc<Array<u64>>), cnt: u64, _H: ()) -> Rc<option<u64>> {
  let hs_clone = Clone::clone(&hs);
  let tmp = hmin_owned(fst::<Rc<fh>, Rc<Array<u64>>>(hs_clone));
  if eqb(tmp, __rocq_global_147) {
    std::mem::drop(P);
    std::mem::drop(U);
    std::mem::drop(V);
    std::mem::drop(Dl);
    std::mem::drop(head);
    std::mem::drop(nxt);
    std::mem::drop(hs);
    Rc::new(option::<u64>::None)
  } else {
    let tmp_1 = ltb(0u64, cnt);
    match bdec(tmp_1) {
      sumbool::left => {
        let hs_clone_1 = Clone::clone(&hs);
        let r = fh_extract(fst::<Rc<fh>, Rc<Array<u64>>>(hs_clone_1));
        let r_clone = Clone::clone(&r);
        let z = snd::<Rc<fh>, u64>(r_clone);
        let tmp_2 = snd::<Rc<fh>, Rc<Array<u64>>>(hs);
        let st1 = rocq_array::set::<u64>(tmp_2, z, 2u64);
        let tmp_3 = div(z, C);
        if eqb(tmp_3, g) {
          std::mem::drop(st1);
          std::mem::drop(P);
          std::mem::drop(U);
          std::mem::drop(V);
          std::mem::drop(Dl);
          std::mem::drop(head);
          std::mem::drop(nxt);
          let tmp_4 = hkey(fst::<Rc<fh>, u64>(r));
          let tmp_5 = rocq_array::get::<u64>(&tmp_4, z);
          std::mem::drop(tmp_4);
          Rc::new(option::<u64>::Some(tmp_5))
        } else {
          let tmp_6 = (fst::<Rc<fh>, u64>(r), st1);
          let P_clone = Rc::clone(&P);
          let U_clone = Rc::clone(&U);
          let V_clone = Rc::clone(&V);
          let Dl_clone = Rc::clone(&Dl);
          let head_clone = Rc::clone(&head);
          let nxt_clone = Rc::clone(&nxt);
          let tmp_7 = expand(P_clone, U_clone, V_clone, Dl_clone, head_clone, nxt_clone, C, cap, tmp_6, z);
          dijk(P, U, V, Dl, head, nxt, C, cap, g, tmp_7, sub(cnt, 1u64), ())
        }
      },
      sumbool::right => {
        std::mem::drop(P);
        std::mem::drop(U);
        std::mem::drop(V);
        std::mem::drop(Dl);
        std::mem::drop(head);
        std::mem::drop(nxt);
        std::mem::drop(hs);
        Rc::new(option::<u64>::None)
      },
    }
  }
}

// Rocq: Fulltank.fulltank_implem.query
// Variant: uncurried
pub fn query(n: u64, P: Rc<Array<u64>>, U: Rc<Array<u64>>, V: Rc<Array<u64>>, Dl: Rc<Array<u64>>, head: Rc<Array<u64>>, nxt: Rc<Array<u64>>, cap: u64, s: u64, g: u64) -> Rc<option<u64>> {
  let C = add(cap, 1u64);
  let N = mul(n, C);
  let tmp = rocq_array::make::<u64>(N, 0u64);
  let tmp_1 = rocq_array::make::<u64>(N, __rocq_global_147);
  let tmp_2 = rocq_array::make::<u64>(N, __rocq_global_147);
  let tmp_3 = rocq_array::make::<u64>(N, __rocq_global_147);
  let tmp_4 = rocq_array::make::<u64>(N, __rocq_global_147);
  let tmp_5 = rocq_array::make::<u64>(N, 0u64);
  let tmp_6 = rocq_array::make::<u64>(N, 0u64);
  let tmp_7 = rocq_array::make::<u64>(N, __rocq_global_147);
  let h0 = Rc::new(fh { hkey: tmp, hpar: tmp_1, hchd: tmp_2, hlft: tmp_3, hrgt: tmp_4, hdeg: tmp_5, hmrk: tmp_6, hbuf: tmp_7, hmin: __rocq_global_147 });
  let src = mul(s, C);
  let tmp_8 = fh_insert(h0, src, 0u64);
  let tmp_9 = rocq_array::make::<u64>(N, 0u64);
  let tmp_10 = rocq_array::set::<u64>(tmp_9, src, 1u64);
  dijk_1(P, U, V, Dl, head, nxt, C, cap, g, (tmp_8, tmp_10), N)
}

// Rocq: Fulltank.fulltank_implem.qloop
// Variant: uncurried
pub fn qloop_1(n: u64, P: Rc<Array<u64>>, U: Rc<Array<u64>>, V: Rc<Array<u64>>, Dl: Rc<Array<u64>>, head: Rc<Array<u64>>, nxt: Rc<Array<u64>>, Cs: Rc<Array<u64>>, Ss: Rc<Array<u64>>, Es: Rc<Array<u64>>, out: Rc<Array<Rc<option<u64>>>>, i: u64, q: u64) -> Rc<Array<Rc<option<u64>>>> {
  qloop(n, P, U, V, Dl, head, nxt, Cs, Ss, Es, out, i, q, ())
}

// Rocq: Fulltank.fulltank_implem.qloop (local: qloop)
// Variant: uncurried, lifted
pub fn qloop(n: u64, P: Rc<Array<u64>>, U: Rc<Array<u64>>, V: Rc<Array<u64>>, Dl: Rc<Array<u64>>, head: Rc<Array<u64>>, nxt: Rc<Array<u64>>, Cs: Rc<Array<u64>>, Ss: Rc<Array<u64>>, Es: Rc<Array<u64>>, out: Rc<Array<Rc<option<u64>>>>, i: u64, q: u64, _H: ()) -> Rc<Array<Rc<option<u64>>>> {
  let tmp = ltb(i, q);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&Cs, i);
      let tmp_2 = rocq_array::get::<u64>(&Ss, i);
      let tmp_3 = rocq_array::get::<u64>(&Es, i);
      let P_clone = Rc::clone(&P);
      let U_clone = Rc::clone(&U);
      let V_clone = Rc::clone(&V);
      let Dl_clone = Rc::clone(&Dl);
      let head_clone = Rc::clone(&head);
      let nxt_clone = Rc::clone(&nxt);
      let tmp_4 = rocq_array::set::<Rc<option<u64>>>(out, i, query(n, P_clone, U_clone, V_clone, Dl_clone, head_clone, nxt_clone, tmp_1, tmp_2, tmp_3));
      qloop(n, P, U, V, Dl, head, nxt, Cs, Ss, Es, tmp_4, add(i, 1u64), q, ())
    },
    sumbool::right => {
      std::mem::drop(P);
      std::mem::drop(U);
      std::mem::drop(V);
      std::mem::drop(Dl);
      std::mem::drop(head);
      std::mem::drop(nxt);
      std::mem::drop(Cs);
      std::mem::drop(Ss);
      std::mem::drop(Es);
      out
    },
  }
}

// Rocq: Fulltank.fulltank_implem.fulltank_impl
// Variant: uncurried
pub fn fulltank_impl(n: u64, p: Rc<Array<u64>>, u: Rc<Array<u64>>, v: Rc<Array<u64>>, d: Rc<Array<u64>>, c: Rc<Array<u64>>, s: Rc<Array<u64>>, e: Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>> {
  let m = rocq_array::length::<u64>(&u);
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let tmp_1 = rocq_array::make::<u64>(add(mul(2u64, m), 1u64), 0u64);
  let u_clone = Rc::clone(&u);
  let v_clone = Rc::clone(&v);
  let hn = build_1(u_clone, v_clone, tmp, tmp_1, 0u64, m);
  let q = rocq_array::length::<u64>(&c);
  let hn_clone = Clone::clone(&hn);
  let tmp_2 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(hn_clone);
  let tmp_3 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(hn);
  let tmp_4 = rocq_array::make::<Rc<option<u64>>>(q, Rc::new(option::<u64>::None));
  qloop_1(n, p, u, v, d, tmp_2, tmp_3, c, s, e, tmp_4, 0u64, q)
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
const __rocq_global_147: u64 = 9223372036854775807u64;