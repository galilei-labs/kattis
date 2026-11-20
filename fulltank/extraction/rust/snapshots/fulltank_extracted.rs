#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

pub struct fh {
  pub hkey: Array<Int63>,
  pub hpar: Array<Int63>,
  pub hchd: Array<Int63>,
  pub hlft: Array<Int63>,
  pub hrgt: Array<Int63>,
  pub hdeg: Array<Int63>,
  pub hmrk: Array<Int63>,
  pub hbuf: Array<Int63>,
  pub hmin: Int63,
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

pub type uint = Int63;

// Rocq: Fulltank.fulltank_implem.nil
pub fn nil() -> Int63 {
  int63!(9223372036854775807)
}

// Rocq: Fulltank.fulltank_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Fulltank.fulltank_implem.build
// Variant: uncurried
pub fn build_1(U: Array<Int63>, V: Array<Int63>, head: Array<Int63>, nxt: Array<Int63>, j: Int63, m: Int63) -> (Array<Int63>, Array<Int63>) {
  build(U, V, head, nxt, j, m, ())
}

// Rocq: Fulltank.fulltank_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(U: Array<Int63>, V: Array<Int63>, head: Array<Int63>, nxt: Array<Int63>, j: Int63, m: Int63, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = j < m;
  match bdec(tmp) {
    sumbool::left => {
      let a_1 = U.get_cloned(j);
      let b_1 = V.get_cloned(j);
      let e1 = int63!(2) * j + int63!(1);
      let e2 = int63!(2) * j + int63!(2);
      let tmp_1 = head.get_cloned(a_1);
      let nxt1 = nxt.set(e1, tmp_1);
      let head1 = head.set(a_1, e1);
      let tmp_2 = head1.get_cloned(b_1);
      let nxt2 = nxt1.set(e2, tmp_2);
      let head2 = head1.set(b_1, e2);
      build(U, V, head2, nxt2, j + int63!(1), m, ())
    },
    sumbool::right => {
      std::mem::drop(U);
      std::mem::drop(V);
      (head, nxt)
    },
  }
}

// Rocq: Fulltank.fulltank_implem.hmin
pub fn hmin_owned(f: Rc<fh>) -> Int63 {
  let f_hmin_clone = Clone::clone(&f.hmin);
  std::mem::drop(f);
  f_hmin_clone
}

// Rocq: Fulltank.fulltank_implem.hmin
// Variant: borrowed
pub fn hmin(f: &Rc<fh>) -> Int63 {
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
pub fn hchd(f: Rc<fh>) -> Array<Int63> {
  let f_hchd_clone = Clone::clone(&f.hchd);
  std::mem::drop(f);
  f_hchd_clone
}

// Rocq: Fulltank.fulltank_implem.hdeg
pub fn hdeg(f: Rc<fh>) -> Array<Int63> {
  let f_hdeg_clone = Clone::clone(&f.hdeg);
  std::mem::drop(f);
  f_hdeg_clone
}

// Rocq: Fulltank.fulltank_implem.hbuf
pub fn hbuf(f: Rc<fh>) -> Array<Int63> {
  let f_hbuf_clone = Clone::clone(&f.hbuf);
  std::mem::drop(f);
  f_hbuf_clone
}

// Rocq: Fulltank.fulltank_implem.s_min
// Variant: uncurried
pub fn s_min(h: Rc<fh>, v: Int63) -> Rc<fh> {
  let (v2, v3) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v2 {
    fh { hkey: v16, hpar: v18, hchd: v20, hlft: v22, hrgt: v24, hdeg: v26, hmrk: v28, hbuf: v30, hmin: _v32 } => {
      __rocq_reuse::rebuild(v3, fh { hkey: v16, hpar: v18, hchd: v20, hlft: v22, hrgt: v24, hdeg: v26, hmrk: v28, hbuf: v30, hmin: v })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.hrgt
pub fn hrgt(f: Rc<fh>) -> Array<Int63> {
  let f_hrgt_clone = Clone::clone(&f.hrgt);
  std::mem::drop(f);
  f_hrgt_clone
}

// Rocq: Fulltank.fulltank_implem.s_par
// Variant: uncurried
pub fn s_par(h: Rc<fh>, i: Int63, v: Int63) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v19.set(i, v), hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.s_buf
// Variant: uncurried
pub fn s_buf(h: Rc<fh>, i: Int63, v: Int63) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31.set(i, v), hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.hkey
pub fn hkey(f: Rc<fh>) -> Array<Int63> {
  let f_hkey_clone = Clone::clone(&f.hkey);
  std::mem::drop(f);
  f_hkey_clone
}

// Rocq: Fulltank.fulltank_implem.s_rgt
// Variant: uncurried
pub fn s_rgt(h: Rc<fh>, i: Int63, v: Int63) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25.set(i, v), hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.s_lft
// Variant: uncurried
pub fn s_lft(h: Rc<fh>, i: Int63, v: Int63) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23.set(i, v), hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.s_chd
// Variant: uncurried
pub fn s_chd(h: Rc<fh>, i: Int63, v: Int63) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v19, hchd: v21.set(i, v), hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.ring_ins
// Variant: uncurried
pub fn ring_ins(h: Rc<fh>, a_1: Int63, x: Int63) -> Rc<fh> {
  let h_clone = Rc::clone(&h);
  let tmp = hrgt(h_clone);
  let b_1 = tmp.get_cloned(a_1);
  std::mem::drop(tmp);
  let tmp_1 = s_lft(s_rgt(h, a_1, x), x, a_1);
  s_lft(s_rgt(tmp_1, x, b_1), b_1, x)
}

// Rocq: Fulltank.fulltank_implem.s_mrk
// Variant: uncurried
pub fn s_mrk(h: Rc<fh>, i: Int63, v: Int63) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29.set(i, v), hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.s_deg
// Variant: uncurried
pub fn s_deg(h: Rc<fh>, i: Int63, v: Int63) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27.set(i, v), hmrk: v29, hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.fh_link
// Variant: uncurried
pub fn fh_link(h: Rc<fh>, y: Int63, x: Int63) -> Rc<fh> {
  let h_clone = Rc::clone(&h);
  let tmp = hdeg(h_clone);
  let tmp_1 = tmp.get_cloned(x);
  let tmp_2 = int63!(0);
  let h1 = if tmp_1 == tmp_2 {
    std::mem::drop(tmp);
    s_rgt(s_lft(s_chd(h, x, y), y, y), y, y)
  } else {
    std::mem::drop(tmp);
    let h_clone_1 = Rc::clone(&h);
    let tmp_3 = hchd(h_clone_1);
    let tmp_4 = tmp_3.get_cloned(x);
    std::mem::drop(tmp_3);
    ring_ins(h, tmp_4, y)
  };
  let h1_clone = Rc::clone(&h1);
  let tmp_5 = s_par(h1_clone, y, x);
  let tmp_6 = hdeg(h1);
  let tmp_7 = tmp_6.get_cloned(x);
  std::mem::drop(tmp_6);
  s_mrk(s_deg(tmp_5, x, tmp_7 + int63!(1)), y, int63!(0))
}

// Rocq: Fulltank.fulltank_implem.link_loop
// Variant: uncurried
pub fn link_loop_1(h: Rc<fh>, x: Int63, d: Int63, N: Int63) -> (Rc<fh>, Int63) {
  link_loop(h, x, d, N, ())
}

// Rocq: Fulltank.fulltank_implem.link_loop (local: link_loop)
// Variant: uncurried, lifted
pub fn link_loop(h: Rc<fh>, x: Int63, d: Int63, N: Int63, _H: ()) -> (Rc<fh>, Int63) {
  let tmp = d < N;
  match bdec(tmp) {
    sumbool::left => {
      let h_clone = Rc::clone(&h);
      let tmp_1 = hbuf(h_clone);
      let y = tmp_1.get_cloned(d);
      if y == __rocq_global_147 {
        std::mem::drop(tmp_1);
        (s_buf(h, d, x), d)
      } else {
        let h1 = s_buf(h, d, __rocq_global_147);
        let h1_clone = Rc::clone(&h1);
        let tmp_2 = hkey(h1_clone);
        let tmp_3 = tmp_2.get_cloned(y);
        let h1_clone_1 = Rc::clone(&h1);
        let tmp_4 = hkey(h1_clone_1);
        let tmp_5 = tmp_4.get_cloned(x);
        if tmp_3 < tmp_5 {
          std::mem::drop(tmp_2);
          std::mem::drop(tmp_1);
          std::mem::drop(tmp_4);
          link_loop(fh_link(h1, x, y), y, d + int63!(1), N, ())
        } else {
          std::mem::drop(tmp_2);
          std::mem::drop(tmp_1);
          std::mem::drop(tmp_4);
          link_loop(fh_link(h1, y, x), x, d + int63!(1), N, ())
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
pub fn proc(h: Rc<fh>, w: Int63, md: Int63) -> (Rc<fh>, Int63) {
  let h1 = s_par(h, w, __rocq_global_147);
  let h1_clone = Rc::clone(&h1);
  let tmp = hbuf(h1_clone);
  let N = tmp.length();
  let h1_clone_1 = Rc::clone(&h1);
  let tmp_1 = hdeg(h1_clone_1);
  let tmp_2 = tmp_1.get_cloned(w);
  let r = link_loop_1(h1, w, tmp_2, N);
  let r_clone = Clone::clone(&r);
  let tmp_3 = fst::<Rc<fh>, Int63>(r_clone);
  let r_clone_1 = Clone::clone(&r);
  let tmp_4 = snd::<Rc<fh>, Int63>(r_clone_1);
  let tmp_5 = if md < tmp_4 {
    std::mem::drop(tmp);
    std::mem::drop(tmp_1);
    snd::<Rc<fh>, Int63>(r)
  } else {
    std::mem::drop(r);
    std::mem::drop(tmp);
    std::mem::drop(tmp_1);
    md
  };
  (tmp_3, tmp_5)
}

// Rocq: Fulltank.fulltank_implem.walk
// Variant: uncurried
pub fn walk_1(h: Rc<fh>, cur: Int63, stop: Int63, md: Int63, cnt: Int63) -> (Rc<fh>, Int63) {
  walk(h, cur, stop, md, cnt, ())
}

// Rocq: Fulltank.fulltank_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(h: Rc<fh>, cur: Int63, stop: Int63, md: Int63, cnt: Int63, _H: ()) -> (Rc<fh>, Int63) {
  if cur == stop {
    (h, md)
  } else {
    let tmp = int63!(0) < cnt;
    match bdec(tmp) {
      sumbool::left => {
        let h_clone = Rc::clone(&h);
        let tmp_1 = hrgt(h_clone);
        let nx = tmp_1.get_cloned(cur);
        std::mem::drop(tmp_1);
        let r = proc(h, cur, md);
        let r_clone = Clone::clone(&r);
        walk(fst::<Rc<fh>, Int63>(r_clone), nx, stop, snd::<Rc<fh>, Int63>(r), cnt - int63!(1), ())
      },
      sumbool::right => {
        (h, md)
      },
    }
  }
}

// Rocq: Fulltank.fulltank_implem.root_add
// Variant: uncurried
pub fn root_add(h: Rc<fh>, x: Int63) -> Rc<fh> {
  let h_clone = Rc::clone(&h);
  let m = hmin_owned(h_clone);
  if m == __rocq_global_147 {
    s_min(s_rgt(s_lft(h, x, x), x, x), x)
  } else {
    let h1 = ring_ins(h, m, x);
    let h1_clone = Rc::clone(&h1);
    let tmp = hkey(h1_clone);
    let tmp_1 = tmp.get_cloned(x);
    let h1_clone_1 = Rc::clone(&h1);
    let tmp_2 = hkey(h1_clone_1);
    let tmp_3 = tmp_2.get_cloned(m);
    if tmp_1 < tmp_3 {
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
pub fn rebuild_1(h: Rc<fh>, d: Int63, M: Int63) -> Rc<fh> {
  rebuild(h, d, M, ())
}

// Rocq: Fulltank.fulltank_implem.rebuild (local: rebuild)
// Variant: uncurried, lifted
pub fn rebuild(h: Rc<fh>, d: Int63, M: Int63, _H: ()) -> Rc<fh> {
  let tmp = d < M;
  match bdec(tmp) {
    sumbool::left => {
      let h_clone = Rc::clone(&h);
      let tmp_1 = hbuf(h_clone);
      let x = tmp_1.get_cloned(d);
      let tmp_2 = __rocq_global_147;
      let h1 = if x == tmp_2 {
        std::mem::drop(tmp_1);
        h
      } else {
        std::mem::drop(tmp_1);
        root_add(s_buf(h, d, __rocq_global_147), x)
      };
      rebuild(h1, d + int63!(1), M, ())
    },
    sumbool::right => {
      h
    },
  }
}

// Rocq: Fulltank.fulltank_implem.fh_extract
pub fn fh_extract(h: Rc<fh>) -> (Rc<fh>, Int63) {
  let h_clone = Rc::clone(&h);
  let z = hmin_owned(h_clone);
  let h_clone_1 = Rc::clone(&h);
  let tmp = hchd(h_clone_1);
  let c = tmp.get_cloned(z);
  let h_clone_2 = Rc::clone(&h);
  let tmp_1 = hdeg(h_clone_2);
  let dz = tmp_1.get_cloned(z);
  let h_clone_3 = Rc::clone(&h);
  let tmp_2 = hbuf(h_clone_3);
  let N = tmp_2.length();
  let h0 = s_min(h, __rocq_global_147);
  let h0_clone = Rc::clone(&h0);
  let tmp_3 = hrgt(h0_clone);
  let tmp_4 = tmp_3.get_cloned(z);
  let r1 = walk_1(h0, tmp_4, z, int63!(0), N);
  let tmp_5 = int63!(0);
  let r2 = if dz == tmp_5 {
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
    let tmp_6 = hrgt(fst::<Rc<fh>, Int63>(r1_clone));
    let nx = tmp_6.get_cloned(c);
    std::mem::drop(tmp_6);
    let r1_clone_1 = Clone::clone(&r1);
    let r = proc(fst::<Rc<fh>, Int63>(r1_clone_1), c, snd::<Rc<fh>, Int63>(r1));
    let r_clone = Clone::clone(&r);
    walk_1(fst::<Rc<fh>, Int63>(r_clone), nx, c, snd::<Rc<fh>, Int63>(r), N)
  };
  let r2_clone = Clone::clone(&r2);
  let M = snd::<Rc<fh>, Int63>(r2_clone) + int63!(1);
  (rebuild_1(fst::<Rc<fh>, Int63>(r2), int63!(0), M), z)
}

// Rocq: Fulltank.fulltank_implem.s_key
// Variant: uncurried
pub fn s_key(h: Rc<fh>, i: Int63, v: Int63) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      __rocq_reuse::rebuild(v4, fh { hkey: v17.set(i, v), hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.fh_insert
// Variant: uncurried
pub fn fh_insert(h: Rc<fh>, x: Int63, k: Int63) -> Rc<fh> {
  root_add(s_mrk(s_deg(s_chd(s_par(s_key(h, x, k), x, __rocq_global_147), x, __rocq_global_147), x, int63!(0)), x, int63!(0)), x)
}

// Rocq: Fulltank.fulltank_implem.hpar
pub fn hpar(f: Rc<fh>) -> Array<Int63> {
  let f_hpar_clone = Clone::clone(&f.hpar);
  std::mem::drop(f);
  f_hpar_clone
}

// Rocq: Fulltank.fulltank_implem.hmrk
pub fn hmrk(f: Rc<fh>) -> Array<Int63> {
  let f_hmrk_clone = Clone::clone(&f.hmrk);
  std::mem::drop(f);
  f_hmrk_clone
}

// Rocq: Fulltank.fulltank_implem.hlft
pub fn hlft(f: Rc<fh>) -> Array<Int63> {
  let f_hlft_clone = Clone::clone(&f.hlft);
  std::mem::drop(f);
  f_hlft_clone
}

// Rocq: Fulltank.fulltank_implem.fh_cut
// Variant: uncurried
pub fn fh_cut(h: Rc<fh>, x: Int63, y: Int63) -> Rc<fh> {
  let h_clone = Rc::clone(&h);
  let tmp = hdeg(h_clone);
  let tmp_1 = tmp.get_cloned(y);
  let tmp_2 = int63!(1);
  let h1 = if tmp_1 == tmp_2 {
    std::mem::drop(tmp);
    s_chd(h, y, __rocq_global_147)
  } else {
    let h_clone_1 = Rc::clone(&h);
    let tmp_3 = hlft(h_clone_1);
    let a_1 = tmp_3.get_cloned(x);
    let h_clone_2 = Rc::clone(&h);
    let tmp_4 = hrgt(h_clone_2);
    let b_1 = tmp_4.get_cloned(x);
    let h_ = s_lft(s_rgt(h, a_1, b_1), b_1, a_1);
    let h__clone = Rc::clone(&h_);
    let tmp_5 = hchd(h__clone);
    let tmp_6 = tmp_5.get_cloned(y);
    if tmp_6 == x {
      std::mem::drop(tmp_5);
      std::mem::drop(tmp_3);
      std::mem::drop(tmp_4);
      std::mem::drop(tmp);
      s_chd(h_, y, b_1)
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
  let tmp_8 = tmp_7.get_cloned(y);
  std::mem::drop(tmp_7);
  let h2 = s_deg(h1, y, tmp_8 - int63!(1));
  root_add(s_mrk(s_par(h2, x, __rocq_global_147), x, int63!(0)), x)
}

// Rocq: Fulltank.fulltank_implem.ccut
// Variant: uncurried
pub fn ccut_1(h: Rc<fh>, y: Int63, cnt: Int63) -> Rc<fh> {
  ccut(h, y, cnt, ())
}

// Rocq: Fulltank.fulltank_implem.ccut (local: ccut)
// Variant: uncurried, lifted
pub fn ccut(h: Rc<fh>, y: Int63, cnt: Int63, _H: ()) -> Rc<fh> {
  let tmp = int63!(0) < cnt;
  match bdec(tmp) {
    sumbool::left => {
      let h_clone = Rc::clone(&h);
      let tmp_1 = hpar(h_clone);
      let z = tmp_1.get_cloned(y);
      if z == __rocq_global_147 {
        std::mem::drop(tmp_1);
        h
      } else {
        let h_clone_1 = Rc::clone(&h);
        let tmp_2 = hmrk(h_clone_1);
        let tmp_3 = tmp_2.get_cloned(y);
        if tmp_3 == int63!(0) {
          std::mem::drop(tmp_2);
          std::mem::drop(tmp_1);
          s_mrk(h, y, int63!(1))
        } else {
          std::mem::drop(tmp_2);
          std::mem::drop(tmp_1);
          ccut(fh_cut(h, y, z), z, cnt - int63!(1), ())
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
pub fn fh_decrease(h: Rc<fh>, x: Int63, k: Int63) -> Rc<fh> {
  let h1 = s_key(h, x, k);
  let h1_clone = Rc::clone(&h1);
  let tmp = hpar(h1_clone);
  let y = tmp.get_cloned(x);
  let tmp_1 = __rocq_global_147;
  let h2 = if y == tmp_1 {
    h1
  } else {
    let h1_clone_1 = Rc::clone(&h1);
    let tmp_2 = hkey(h1_clone_1);
    let tmp_3 = tmp_2.get_cloned(y);
    if k < tmp_3 {
      std::mem::drop(tmp_2);
      let h1_clone_2 = Rc::clone(&h1);
      let tmp_4 = hpar(h1_clone_2);
      let N = tmp_4.length();
      std::mem::drop(tmp_4);
      ccut_1(fh_cut(h1, x, y), y, N)
    } else {
      std::mem::drop(tmp_2);
      h1
    }
  };
  let h2_clone = Rc::clone(&h2);
  let tmp_5 = hkey(h2_clone);
  let tmp_6 = tmp_5.get_cloned(hmin(&h2));
  if k < tmp_6 {
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
pub fn relax(h: Rc<fh>, st: Array<Int63>, v: Int63, nk: Int63) -> (Rc<fh>, Array<Int63>) {
  let s = st.get_cloned(v);
  if s == int63!(0) {
    (fh_insert(h, v, nk), st.set(v, int63!(1)))
  } else {
    if s == int63!(1) {
      let h_clone = Rc::clone(&h);
      let tmp = hkey(h_clone);
      let tmp_1 = tmp.get_cloned(v);
      if nk < tmp_1 {
        std::mem::drop(tmp);
        (fh_decrease(h, v, nk), st)
      } else {
        std::mem::drop(tmp);
        (h, st)
      }
    } else {
      (h, st)
    }
  }
}

// Rocq: Fulltank.fulltank_implem.edges
// Variant: uncurried
pub fn edges_1(U: Array<Int63>, V: Array<Int63>, Dl: Array<Int63>, nxt: Array<Int63>, C: Int63, f: Int63, kz: Int63, hs: (Rc<fh>, Array<Int63>), e: Int63) -> (Rc<fh>, Array<Int63>) {
  edges(U, V, Dl, nxt, C, f, kz, hs, e, ())
}

// Rocq: Fulltank.fulltank_implem.edges (local: edges)
// Variant: uncurried, lifted
pub fn edges(U: Array<Int63>, V: Array<Int63>, Dl: Array<Int63>, nxt: Array<Int63>, C: Int63, f: Int63, kz: Int63, hs: (Rc<fh>, Array<Int63>), e: Int63, _H: ()) -> (Rc<fh>, Array<Int63>) {
  if e == int63!(0) {
    std::mem::drop(U);
    std::mem::drop(V);
    std::mem::drop(Dl);
    std::mem::drop(nxt);
    hs
  } else {
    let j = (e - int63!(1)) / int63!(2);
    let tmp = (e - int63!(1)) % int63!(2);
    let tmp_1 = int63!(0);
    let y = if tmp == tmp_1 {
      V.get_cloned(j)
    } else {
      U.get_cloned(j)
    };
    let l = Dl.get_cloned(j);
    let hs1 = if l <= f {
      let hs_clone = Clone::clone(&hs);
      relax(fst::<Rc<fh>, Array<Int63>>(hs_clone), snd::<Rc<fh>, Array<Int63>>(hs), y * C + (f - l), kz)
    } else {
      hs
    };
    let e_ = nxt.get_cloned(e);
    let tmp_2 = e_ < e;
    match bdec(tmp_2) {
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
pub fn expand(P: Array<Int63>, U: Array<Int63>, V: Array<Int63>, Dl: Array<Int63>, head: Array<Int63>, nxt: Array<Int63>, C: Int63, cap: Int63, hs: (Rc<fh>, Array<Int63>), z: Int63) -> (Rc<fh>, Array<Int63>) {
  let x = z / C;
  let f = z % C;
  let hs_clone = Clone::clone(&hs);
  let tmp = hkey(fst::<Rc<fh>, Array<Int63>>(hs_clone));
  let kz = tmp.get_cloned(z);
  let hs1 = if f < cap {
    std::mem::drop(tmp);
    let hs_clone_1 = Clone::clone(&hs);
    let tmp_1 = fst::<Rc<fh>, Array<Int63>>(hs_clone_1);
    let tmp_2 = snd::<Rc<fh>, Array<Int63>>(hs);
    let tmp_3 = z + int63!(1);
    let tmp_4 = P.get_cloned(x);
    std::mem::drop(P);
    relax(tmp_1, tmp_2, tmp_3, kz + tmp_4)
  } else {
    std::mem::drop(P);
    std::mem::drop(tmp);
    hs
  };
  let tmp_5 = head.get_cloned(x);
  std::mem::drop(head);
  edges_1(U, V, Dl, nxt, C, f, kz, hs1, tmp_5)
}

// Rocq: Fulltank.fulltank_implem.dijk
// Variant: uncurried
pub fn dijk_1(P: Array<Int63>, U: Array<Int63>, V: Array<Int63>, Dl: Array<Int63>, head: Array<Int63>, nxt: Array<Int63>, C: Int63, cap: Int63, g: Int63, hs: (Rc<fh>, Array<Int63>), cnt: Int63) -> Rc<option<Int63>> {
  dijk(P, U, V, Dl, head, nxt, C, cap, g, hs, cnt, ())
}

// Rocq: Fulltank.fulltank_implem.dijk (local: dijk)
// Variant: uncurried, lifted
pub fn dijk(P: Array<Int63>, U: Array<Int63>, V: Array<Int63>, Dl: Array<Int63>, head: Array<Int63>, nxt: Array<Int63>, C: Int63, cap: Int63, g: Int63, hs: (Rc<fh>, Array<Int63>), cnt: Int63, _H: ()) -> Rc<option<Int63>> {
  let hs_clone = Clone::clone(&hs);
  let tmp = hmin_owned(fst::<Rc<fh>, Array<Int63>>(hs_clone));
  if tmp == __rocq_global_147 {
    std::mem::drop(P);
    std::mem::drop(U);
    std::mem::drop(V);
    std::mem::drop(Dl);
    std::mem::drop(head);
    std::mem::drop(nxt);
    std::mem::drop(hs);
    Rc::new(option::<Int63>::None)
  } else {
    let tmp_1 = int63!(0) < cnt;
    match bdec(tmp_1) {
      sumbool::left => {
        let hs_clone_1 = Clone::clone(&hs);
        let r = fh_extract(fst::<Rc<fh>, Array<Int63>>(hs_clone_1));
        let r_clone = Clone::clone(&r);
        let z = snd::<Rc<fh>, Int63>(r_clone);
        let st1 = snd::<Rc<fh>, Array<Int63>>(hs).set(z, int63!(2));
        let tmp_2 = z / C;
        if tmp_2 == g {
          std::mem::drop(st1);
          std::mem::drop(P);
          std::mem::drop(U);
          std::mem::drop(V);
          std::mem::drop(Dl);
          std::mem::drop(head);
          std::mem::drop(nxt);
          let tmp_3 = hkey(fst::<Rc<fh>, Int63>(r));
          let tmp_4 = tmp_3.get_cloned(z);
          std::mem::drop(tmp_3);
          Rc::new(option::<Int63>::Some(tmp_4))
        } else {
          let tmp_5 = (fst::<Rc<fh>, Int63>(r), st1);
          let P_clone = Clone::clone(&P);
          let U_clone = Clone::clone(&U);
          let V_clone = Clone::clone(&V);
          let Dl_clone = Clone::clone(&Dl);
          let head_clone = Clone::clone(&head);
          let nxt_clone = Clone::clone(&nxt);
          let tmp_6 = expand(P_clone, U_clone, V_clone, Dl_clone, head_clone, nxt_clone, C, cap, tmp_5, z);
          dijk(P, U, V, Dl, head, nxt, C, cap, g, tmp_6, cnt - int63!(1), ())
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
        Rc::new(option::<Int63>::None)
      },
    }
  }
}

// Rocq: Fulltank.fulltank_implem.query
// Variant: uncurried
pub fn query(n: Int63, P: Array<Int63>, U: Array<Int63>, V: Array<Int63>, Dl: Array<Int63>, head: Array<Int63>, nxt: Array<Int63>, cap: Int63, s: Int63, g: Int63) -> Rc<option<Int63>> {
  let C = cap + int63!(1);
  let N = n * C;
  let h0 = Rc::new(fh { hkey: Array::<Int63>::make(N, int63!(0)), hpar: Array::<Int63>::make(N, __rocq_global_147), hchd: Array::<Int63>::make(N, __rocq_global_147), hlft: Array::<Int63>::make(N, __rocq_global_147), hrgt: Array::<Int63>::make(N, __rocq_global_147), hdeg: Array::<Int63>::make(N, int63!(0)), hmrk: Array::<Int63>::make(N, int63!(0)), hbuf: Array::<Int63>::make(N, __rocq_global_147), hmin: __rocq_global_147 });
  let src = s * C;
  dijk_1(P, U, V, Dl, head, nxt, C, cap, g, (fh_insert(h0, src, int63!(0)), Array::<Int63>::make(N, int63!(0)).set(src, int63!(1))), N)
}

// Rocq: Fulltank.fulltank_implem.qloop
// Variant: uncurried
pub fn qloop_1(n: Int63, P: Array<Int63>, U: Array<Int63>, V: Array<Int63>, Dl: Array<Int63>, head: Array<Int63>, nxt: Array<Int63>, Cs: Array<Int63>, Ss: Array<Int63>, Es: Array<Int63>, out: Array<Rc<option<Int63>>>, i: Int63, q: Int63) -> Array<Rc<option<Int63>>> {
  qloop(n, P, U, V, Dl, head, nxt, Cs, Ss, Es, out, i, q, ())
}

// Rocq: Fulltank.fulltank_implem.qloop (local: qloop)
// Variant: uncurried, lifted
pub fn qloop(n: Int63, P: Array<Int63>, U: Array<Int63>, V: Array<Int63>, Dl: Array<Int63>, head: Array<Int63>, nxt: Array<Int63>, Cs: Array<Int63>, Ss: Array<Int63>, Es: Array<Int63>, out: Array<Rc<option<Int63>>>, i: Int63, q: Int63, _H: ()) -> Array<Rc<option<Int63>>> {
  let tmp = i < q;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = Cs.get_cloned(i);
      let tmp_2 = Ss.get_cloned(i);
      let tmp_3 = Es.get_cloned(i);
      let P_clone = Clone::clone(&P);
      let U_clone = Clone::clone(&U);
      let V_clone = Clone::clone(&V);
      let Dl_clone = Clone::clone(&Dl);
      let head_clone = Clone::clone(&head);
      let nxt_clone = Clone::clone(&nxt);
      let tmp_4 = query(n, P_clone, U_clone, V_clone, Dl_clone, head_clone, nxt_clone, tmp_1, tmp_2, tmp_3);
      qloop(n, P, U, V, Dl, head, nxt, Cs, Ss, Es, out.set(i, tmp_4), i + int63!(1), q, ())
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
pub fn fulltank_impl(n: Int63, p: Array<Int63>, u: Array<Int63>, v: Array<Int63>, d: Array<Int63>, c: Array<Int63>, s: Array<Int63>, e: Array<Int63>) -> Array<Rc<option<Int63>>> {
  let m = u.length();
  let tmp = Array::<Int63>::make(n, int63!(0));
  let tmp_1 = Array::<Int63>::make(int63!(2) * m + int63!(1), int63!(0));
  let u_clone = Clone::clone(&u);
  let v_clone = Clone::clone(&v);
  let hn = build_1(u_clone, v_clone, tmp, tmp_1, int63!(0), m);
  let q = c.length();
  let hn_clone = Clone::clone(&hn);
  qloop_1(n, p, u, v, d, fst::<Array<Int63>, Array<Int63>>(hn_clone), snd::<Array<Int63>, Array<Int63>>(hn), c, s, e, Array::<Rc<option<Int63>>>::make(q, Rc::new(option::<Int63>::None)), int63!(0), q)
}
const __rocq_global_147: Int63 = int63!(9223372036854775807);