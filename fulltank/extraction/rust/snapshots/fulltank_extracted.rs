// Generated from OwnedANF. This printer is not verified.
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

// Rocq: Fulltank.fulltank_implem.fulltank
// Variant: uncurried
pub fn fulltank() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>> {
  let v0: fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>> = fulltank_impl;
  let v1: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>> = Rc::new(v0);
  v1
}

// Rocq: Fulltank.fulltank_implem.fulltank
pub fn fulltank_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>>>>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>>>>>> = fulltank_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>>>>>>> = Rc::new(v0);
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

// Rocq: Fulltank.fulltank_implem.bdec
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
  let v14 = ltb(j, m);
  match bdec(v14) {
    sumbool::left => {
      let v18 = &U;
      let a = rocq_array::get::<u64>(&v18, j);
      let v22 = &V;
      let b = rocq_array::get::<u64>(&v22, j);
      let e1 = add(mul(2u64, j), 1u64);
      let e2 = add(mul(2u64, j), 2u64);
      let v58 = &head;
      let v61 = rocq_array::get::<u64>(&v58, a);
      let nxt1 = rocq_array::set::<u64>(nxt, e1, v61);
      let head1 = rocq_array::set::<u64>(head, a, e1);
      let v76 = &head1;
      let v79 = rocq_array::get::<u64>(&v76, b);
      let nxt2 = rocq_array::set::<u64>(nxt1, e2, v79);
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
  let v3 = Clone::clone((&(&**&f).hmin));
  std::mem::drop(f);
  v3
}

// Rocq: Fulltank.fulltank_implem.hmin
// Variant: borrowed
pub fn hmin(f: &Rc<fh>) -> u64 {
  let v1 = f;
  Clone::clone((&(&**v1).hmin))
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
}

// Rocq: Fulltank.fulltank_implem.hchd
pub fn hchd(f: Rc<fh>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&f).hchd));
  std::mem::drop(f);
  v3
}

// Rocq: Fulltank.fulltank_implem.hdeg
pub fn hdeg(f: Rc<fh>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&f).hdeg));
  std::mem::drop(f);
  v3
}

// Rocq: Fulltank.fulltank_implem.hbuf
pub fn hbuf(f: Rc<fh>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&f).hbuf));
  std::mem::drop(f);
  v3
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
  let v3 = Rc::clone((&(&**&f).hrgt));
  std::mem::drop(f);
  v3
}

// Rocq: Fulltank.fulltank_implem.s_par
// Variant: uncurried
pub fn s_par(h: Rc<fh>, i: u64, v: u64) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      let v41 = rocq_array::set::<u64>(v19, i, v);
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v41, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.s_buf
// Variant: uncurried
pub fn s_buf(h: Rc<fh>, i: u64, v: u64) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      let v41 = rocq_array::set::<u64>(v31, i, v);
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v41, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.hkey
pub fn hkey(f: Rc<fh>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&f).hkey));
  std::mem::drop(f);
  v3
}

// Rocq: Fulltank.fulltank_implem.s_rgt
// Variant: uncurried
pub fn s_rgt(h: Rc<fh>, i: u64, v: u64) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      let v41 = rocq_array::set::<u64>(v25, i, v);
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v41, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.s_lft
// Variant: uncurried
pub fn s_lft(h: Rc<fh>, i: u64, v: u64) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      let v41 = rocq_array::set::<u64>(v23, i, v);
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v19, hchd: v21, hlft: v41, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.s_chd
// Variant: uncurried
pub fn s_chd(h: Rc<fh>, i: u64, v: u64) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      let v41 = rocq_array::set::<u64>(v21, i, v);
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v19, hchd: v41, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.ring_ins
// Variant: uncurried
pub fn ring_ins(h: Rc<fh>, a: u64, x: u64) -> Rc<fh> {
  let v6 = Rc::clone(&h);
  let v7 = hrgt(v6);
  let v8 = &v7;
  let b = rocq_array::get::<u64>(&v8, a);
  std::mem::drop(v7);
  let v30 = s_lft(s_rgt(h, a, x), x, a);
  s_lft(s_rgt(v30, x, b), b, x)
}

// Rocq: Fulltank.fulltank_implem.s_mrk
// Variant: uncurried
pub fn s_mrk(h: Rc<fh>, i: u64, v: u64) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      let v41 = rocq_array::set::<u64>(v29, i, v);
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v41, hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.s_deg
// Variant: uncurried
pub fn s_deg(h: Rc<fh>, i: u64, v: u64) -> Rc<fh> {
  let (v3, v4) = __rocq_reuse::reset(h, |__payload| Clone::clone(__payload));
  match v3 {
    fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 } => {
      let v41 = rocq_array::set::<u64>(v27, i, v);
      __rocq_reuse::rebuild(v4, fh { hkey: v17, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v41, hmrk: v29, hbuf: v31, hmin: v33 })
    },
  }
}

// Rocq: Fulltank.fulltank_implem.fh_link
// Variant: uncurried
pub fn fh_link(h: Rc<fh>, y: u64, x: u64) -> Rc<fh> {
  let v7 = Rc::clone(&h);
  let v8 = hdeg(v7);
  let v9 = &v8;
  let v12 = rocq_array::get::<u64>(&v9, x);
  let v14 = 0u64;
  let h1 = match eqb(v12, v14) {
    true => {
      std::mem::drop(v8);
      s_rgt(s_lft(s_chd(h, x, y), y, y), y, y)
    },
    false => {
      std::mem::drop(v8);
      let v51 = Rc::clone(&h);
      let v52 = hchd(v51);
      let v53 = &v52;
      let v56 = rocq_array::get::<u64>(&v53, x);
      std::mem::drop(v52);
      ring_ins(h, v56, y)
    },
  };
  let v72 = Rc::clone(&h1);
  let v77 = s_par(v72, y, x);
  let v82 = hdeg(h1);
  let v83 = &v82;
  let v86 = rocq_array::get::<u64>(&v83, x);
  std::mem::drop(v82);
  s_mrk(s_deg(v77, x, add(v86, 1u64)), y, 0u64)
}

// Rocq: Fulltank.fulltank_implem.link_loop
// Variant: uncurried
pub fn link_loop_1(h: Rc<fh>, x: u64, d: u64, N: u64) -> (Rc<fh>, u64) {
  link_loop(h, x, d, N, ())
}

// Rocq: Fulltank.fulltank_implem.link_loop (local: link_loop)
// Variant: uncurried, lifted
pub fn link_loop(h: Rc<fh>, x: u64, d: u64, N: u64, _H: ()) -> (Rc<fh>, u64) {
  let v12 = ltb(d, N);
  match bdec(v12) {
    sumbool::left => {
      let v19 = Rc::clone(&h);
      let v20 = hbuf(v19);
      let v21 = &v20;
      let y = rocq_array::get::<u64>(&v21, d);
      match eqb(y, __rocq_global_147) {
        true => {
          std::mem::drop(v20);
          (s_buf(h, d, x), d)
        },
        false => {
          let h1 = s_buf(h, d, __rocq_global_147);
          let v62 = Rc::clone(&h1);
          let v63 = hkey(v62);
          let v64 = &v63;
          let v67 = rocq_array::get::<u64>(&v64, y);
          let v71 = Rc::clone(&h1);
          let v72 = hkey(v71);
          let v73 = &v72;
          let v76 = rocq_array::get::<u64>(&v73, x);
          match ltb(v67, v76) {
            true => {
              std::mem::drop(v63);
              std::mem::drop(v20);
              std::mem::drop(v72);
              link_loop(fh_link(h1, x, y), y, add(d, 1u64), N, ())
            },
            false => {
              std::mem::drop(v63);
              std::mem::drop(v20);
              std::mem::drop(v72);
              link_loop(fh_link(h1, y, x), x, add(d, 1u64), N, ())
            },
          }
        },
      }
    },
    sumbool::right => {
      (h, d)
    },
  }
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let v3 = Clone::clone((&(&p).1));
  std::mem::drop(p);
  v3
}

// Rocq: Fulltank.fulltank_implem.proc
// Variant: uncurried
pub fn proc(h: Rc<fh>, w: u64, md: u64) -> (Rc<fh>, u64) {
  let h1 = s_par(h, w, __rocq_global_147);
  let v15 = Rc::clone(&h1);
  let v16 = hbuf(v15);
  let v17 = &v16;
  let N = rocq_array::length::<u64>(&v17);
  let v23 = Rc::clone(&h1);
  let v24 = hdeg(v23);
  let v25 = &v24;
  let v28 = rocq_array::get::<u64>(&v25, w);
  let r = link_loop_1(h1, w, v28, N);
  let v40 = Clone::clone(&r);
  let v42 = fst::<Rc<fh>, u64>(v40);
  let v46 = Clone::clone(&r);
  let v48 = snd::<Rc<fh>, u64>(v46);
  let v54 = match ltb(md, v48) {
    true => {
      std::mem::drop(v16);
      std::mem::drop(v24);
      snd::<Rc<fh>, u64>(r)
    },
    false => {
      std::mem::drop(r);
      std::mem::drop(v16);
      std::mem::drop(v24);
      md
    },
  };
  (v42, v54)
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
  match eqb(cur, stop) {
    true => {
      (h, md)
    },
    false => {
      let v30 = ltb(0u64, cnt);
      match bdec(v30) {
        sumbool::left => {
          let v37 = Rc::clone(&h);
          let v38 = hrgt(v37);
          let v39 = &v38;
          let nx = rocq_array::get::<u64>(&v39, cur);
          std::mem::drop(v38);
          let r = proc(h, cur, md);
          let v53 = Clone::clone(&r);
          walk(fst::<Rc<fh>, u64>(v53), nx, stop, snd::<Rc<fh>, u64>(r), sub(cnt, 1u64), ())
        },
        sumbool::right => {
          (h, md)
        },
      }
    },
  }
}

// Rocq: Fulltank.fulltank_implem.root_add
// Variant: uncurried
pub fn root_add(h: Rc<fh>, x: u64) -> Rc<fh> {
  let v5 = Rc::clone(&h);
  let m = hmin_owned(v5);
  match eqb(m, __rocq_global_147) {
    true => {
      s_min(s_rgt(s_lft(h, x, x), x, x), x)
    },
    false => {
      let h1 = ring_ins(h, m, x);
      let v51 = Rc::clone(&h1);
      let v52 = hkey(v51);
      let v53 = &v52;
      let v56 = rocq_array::get::<u64>(&v53, x);
      let v60 = Rc::clone(&h1);
      let v61 = hkey(v60);
      let v62 = &v61;
      let v65 = rocq_array::get::<u64>(&v62, m);
      match ltb(v56, v65) {
        true => {
          std::mem::drop(v61);
          std::mem::drop(v52);
          s_min(h1, x)
        },
        false => {
          std::mem::drop(v61);
          std::mem::drop(v52);
          h1
        },
      }
    },
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
  let v11 = ltb(d, M);
  match bdec(v11) {
    sumbool::left => {
      let v18 = Rc::clone(&h);
      let v19 = hbuf(v18);
      let v20 = &v19;
      let x = rocq_array::get::<u64>(&v20, d);
      let v25 = __rocq_global_147;
      let h1 = match eqb(x, v25) {
        true => {
          std::mem::drop(v19);
          h
        },
        false => {
          std::mem::drop(v19);
          root_add(s_buf(h, d, __rocq_global_147), x)
        },
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
  let v4 = Rc::clone(&h);
  let z = hmin_owned(v4);
  let v9 = Rc::clone(&h);
  let v10 = hchd(v9);
  let v11 = &v10;
  let c = rocq_array::get::<u64>(&v11, z);
  let v18 = Rc::clone(&h);
  let v19 = hdeg(v18);
  let v20 = &v19;
  let dz = rocq_array::get::<u64>(&v20, z);
  let v27 = Rc::clone(&h);
  let v28 = hbuf(v27);
  let v29 = &v28;
  let N = rocq_array::length::<u64>(&v29);
  let h0 = s_min(h, __rocq_global_147);
  let v42 = Rc::clone(&h0);
  let v43 = hrgt(v42);
  let v44 = &v43;
  let v47 = rocq_array::get::<u64>(&v44, z);
  let r1 = walk_1(h0, v47, z, 0u64, N);
  let v63 = 0u64;
  let r2 = match eqb(dz, v63) {
    true => {
      std::mem::drop(v28);
      std::mem::drop(v43);
      std::mem::drop(v19);
      std::mem::drop(v10);
      r1
    },
    false => {
      std::mem::drop(v28);
      std::mem::drop(v43);
      std::mem::drop(v19);
      std::mem::drop(v10);
      let v75 = Clone::clone(&r1);
      let v80 = hrgt(fst::<Rc<fh>, u64>(v75));
      let v81 = &v80;
      let nx = rocq_array::get::<u64>(&v81, c);
      std::mem::drop(v80);
      let v88 = Clone::clone(&r1);
      let r = proc(fst::<Rc<fh>, u64>(v88), c, snd::<Rc<fh>, u64>(r1));
      let v105 = Clone::clone(&r);
      walk_1(fst::<Rc<fh>, u64>(v105), nx, c, snd::<Rc<fh>, u64>(r), N)
    },
  };
  let v129 = Clone::clone(&r2);
  let M = add(snd::<Rc<fh>, u64>(v129), 1u64);
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
      let v42 = rocq_array::set::<u64>(v17, i, v);
      __rocq_reuse::rebuild(v4, fh { hkey: v42, hpar: v19, hchd: v21, hlft: v23, hrgt: v25, hdeg: v27, hmrk: v29, hbuf: v31, hmin: v33 })
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
  let v3 = Rc::clone((&(&**&f).hpar));
  std::mem::drop(f);
  v3
}

// Rocq: Fulltank.fulltank_implem.hmrk
pub fn hmrk(f: Rc<fh>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&f).hmrk));
  std::mem::drop(f);
  v3
}

// Rocq: Fulltank.fulltank_implem.hlft
pub fn hlft(f: Rc<fh>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&f).hlft));
  std::mem::drop(f);
  v3
}

// Rocq: Fulltank.fulltank_implem.fh_cut
// Variant: uncurried
pub fn fh_cut(h: Rc<fh>, x: u64, y: u64) -> Rc<fh> {
  let v7 = Rc::clone(&h);
  let v8 = hdeg(v7);
  let v9 = &v8;
  let v12 = rocq_array::get::<u64>(&v9, y);
  let v14 = 1u64;
  let h1 = match eqb(v12, v14) {
    true => {
      std::mem::drop(v8);
      s_chd(h, y, __rocq_global_147)
    },
    false => {
      let v35 = Rc::clone(&h);
      let v36 = hlft(v35);
      let v37 = &v36;
      let a = rocq_array::get::<u64>(&v37, x);
      let v44 = Rc::clone(&h);
      let v45 = hrgt(v44);
      let v46 = &v45;
      let b = rocq_array::get::<u64>(&v46, x);
      let h_ = s_lft(s_rgt(h, a, b), b, a);
      let v70 = Rc::clone(&h_);
      let v71 = hchd(v70);
      let v72 = &v71;
      let v76 = rocq_array::get::<u64>(&v72, y);
      match eqb(v76, x) {
        true => {
          std::mem::drop(v71);
          std::mem::drop(v36);
          std::mem::drop(v45);
          std::mem::drop(v8);
          s_chd(h_, y, b)
        },
        false => {
          std::mem::drop(v71);
          std::mem::drop(v36);
          std::mem::drop(v45);
          std::mem::drop(v8);
          h_
        },
      }
    },
  };
  let v103 = Rc::clone(&h1);
  let v104 = hdeg(v103);
  let v105 = &v104;
  let v108 = rocq_array::get::<u64>(&v105, y);
  std::mem::drop(v104);
  let h2 = s_deg(h1, y, sub(v108, 1u64));
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
  let v13 = ltb(0u64, cnt);
  match bdec(v13) {
    sumbool::left => {
      let v20 = Rc::clone(&h);
      let v21 = hpar(v20);
      let v22 = &v21;
      let z = rocq_array::get::<u64>(&v22, y);
      match eqb(z, __rocq_global_147) {
        true => {
          std::mem::drop(v21);
          h
        },
        false => {
          let v40 = Rc::clone(&h);
          let v41 = hmrk(v40);
          let v42 = &v41;
          let v45 = rocq_array::get::<u64>(&v42, y);
          match eqb(v45, 0u64) {
            true => {
              std::mem::drop(v41);
              std::mem::drop(v21);
              s_mrk(h, y, 1u64)
            },
            false => {
              std::mem::drop(v41);
              std::mem::drop(v21);
              ccut(fh_cut(h, y, z), z, sub(cnt, 1u64), ())
            },
          }
        },
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
  let v14 = Rc::clone(&h1);
  let v15 = hpar(v14);
  let v16 = &v15;
  let y = rocq_array::get::<u64>(&v16, x);
  let v21 = __rocq_global_147;
  let h2 = match eqb(y, v21) {
    true => {
      h1
    },
    false => {
      let v34 = Rc::clone(&h1);
      let v35 = hkey(v34);
      let v36 = &v35;
      let v39 = rocq_array::get::<u64>(&v36, y);
      match ltb(k, v39) {
        true => {
          std::mem::drop(v35);
          let v49 = Rc::clone(&h1);
          let v50 = hpar(v49);
          let v51 = &v50;
          let N = rocq_array::length::<u64>(&v51);
          std::mem::drop(v50);
          ccut_1(fh_cut(h1, x, y), y, N)
        },
        false => {
          std::mem::drop(v35);
          h1
        },
      }
    },
  };
  let v81 = Rc::clone(&h2);
  let v82 = hkey(v81);
  let v86 = hmin(&h2);
  let v87 = &v82;
  let v90 = rocq_array::get::<u64>(&v87, v86);
  match ltb(k, v90) {
    true => {
      std::mem::drop(v82);
      std::mem::drop(v15);
      s_min(h2, x)
    },
    false => {
      std::mem::drop(v82);
      std::mem::drop(v15);
      h2
    },
  }
}

// Rocq: Fulltank.fulltank_implem.relax
// Variant: uncurried
pub fn relax(h: Rc<fh>, st: Rc<Array<u64>>, v: u64, nk: u64) -> (Rc<fh>, Rc<Array<u64>>) {
  let v4 = &st;
  let s = rocq_array::get::<u64>(&v4, v);
  match eqb(s, 0u64) {
    true => {
      let v24 = fh_insert(h, v, nk);
      let v33 = rocq_array::set::<u64>(st, v, 1u64);
      (v24, v33)
    },
    false => {
      match eqb(s, 1u64) {
        true => {
          let v55 = Rc::clone(&h);
          let v56 = hkey(v55);
          let v57 = &v56;
          let v60 = rocq_array::get::<u64>(&v57, v);
          match ltb(nk, v60) {
            true => {
              std::mem::drop(v56);
              (fh_decrease(h, v, nk), st)
            },
            false => {
              std::mem::drop(v56);
              (h, st)
            },
          }
        },
        false => {
          (h, st)
        },
      }
    },
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
  match eqb(e, 0u64) {
    true => {
      std::mem::drop(U);
      std::mem::drop(V);
      std::mem::drop(Dl);
      std::mem::drop(nxt);
      hs
    },
    false => {
      let j = div(sub(e, 1u64), 2u64);
      let v53 = mod_(sub(e, 1u64), 2u64);
      let v55 = 0u64;
      let y = match eqb(v53, v55) {
        true => {
          let v62 = &V;
          rocq_array::get::<u64>(&v62, j)
        },
        false => {
          let v68 = &U;
          rocq_array::get::<u64>(&v68, j)
        },
      };
      let v75 = &Dl;
      let l = rocq_array::get::<u64>(&v75, j);
      let hs1 = match leb(l, f) {
        true => {
          let v89 = Clone::clone(&hs);
          let v91 = fst::<Rc<fh>, Rc<Array<u64>>>(v89);
          let v95 = snd::<Rc<fh>, Rc<Array<u64>>>(hs);
          relax(v91, v95, add(mul(y, C), sub(f, l)), kz)
        },
        false => {
          hs
        },
      };
      let v128 = &nxt;
      let e_ = rocq_array::get::<u64>(&v128, e);
      let v139 = ltb(e_, e);
      match bdec(v139) {
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
    },
  }
}

// Rocq: Fulltank.fulltank_implem.expand
// Variant: uncurried
pub fn expand(P: Rc<Array<u64>>, U: Rc<Array<u64>>, V: Rc<Array<u64>>, Dl: Rc<Array<u64>>, head: Rc<Array<u64>>, nxt: Rc<Array<u64>>, C: u64, cap: u64, hs: (Rc<fh>, Rc<Array<u64>>), z: u64) -> (Rc<fh>, Rc<Array<u64>>) {
  let x = div(z, C);
  let f = mod_(z, C);
  let v25 = Clone::clone(&hs);
  let v30 = hkey(fst::<Rc<fh>, Rc<Array<u64>>>(v25));
  let v31 = &v30;
  let kz = rocq_array::get::<u64>(&v31, z);
  let hs1 = match ltb(f, cap) {
    true => {
      std::mem::drop(v30);
      let v45 = Clone::clone(&hs);
      let v47 = fst::<Rc<fh>, Rc<Array<u64>>>(v45);
      let v51 = snd::<Rc<fh>, Rc<Array<u64>>>(hs);
      let v59 = add(z, 1u64);
      let v61 = &P;
      let v64 = rocq_array::get::<u64>(&v61, x);
      std::mem::drop(P);
      relax(v47, v51, v59, add(kz, v64))
    },
    false => {
      std::mem::drop(P);
      std::mem::drop(v30);
      hs
    },
  };
  let v85 = &head;
  let v88 = rocq_array::get::<u64>(&v85, x);
  std::mem::drop(head);
  edges_1(U, V, Dl, nxt, C, f, kz, hs1, v88)
}

// Rocq: Fulltank.fulltank_implem.dijk
// Variant: uncurried
pub fn dijk_1(P: Rc<Array<u64>>, U: Rc<Array<u64>>, V: Rc<Array<u64>>, Dl: Rc<Array<u64>>, head: Rc<Array<u64>>, nxt: Rc<Array<u64>>, C: u64, cap: u64, g: u64, hs: (Rc<fh>, Rc<Array<u64>>), cnt: u64) -> Rc<option<u64>> {
  dijk(P, U, V, Dl, head, nxt, C, cap, g, hs, cnt, ())
}

// Rocq: Fulltank.fulltank_implem.dijk (local: dijk)
// Variant: uncurried, lifted
pub fn dijk(P: Rc<Array<u64>>, U: Rc<Array<u64>>, V: Rc<Array<u64>>, Dl: Rc<Array<u64>>, head: Rc<Array<u64>>, nxt: Rc<Array<u64>>, C: u64, cap: u64, g: u64, hs: (Rc<fh>, Rc<Array<u64>>), cnt: u64, _H: ()) -> Rc<option<u64>> {
  let v16 = Clone::clone(&hs);
  let v21 = hmin_owned(fst::<Rc<fh>, Rc<Array<u64>>>(v16));
  match eqb(v21, __rocq_global_147) {
    true => {
      std::mem::drop(P);
      std::mem::drop(U);
      std::mem::drop(V);
      std::mem::drop(Dl);
      std::mem::drop(head);
      std::mem::drop(nxt);
      std::mem::drop(hs);
      Rc::new(option::<u64>::None)
    },
    false => {
      let v43 = ltb(0u64, cnt);
      match bdec(v43) {
        sumbool::left => {
          let v50 = Clone::clone(&hs);
          let r = fh_extract(fst::<Rc<fh>, Rc<Array<u64>>>(v50));
          let v58 = Clone::clone(&r);
          let z = snd::<Rc<fh>, u64>(v58);
          let v64 = snd::<Rc<fh>, Rc<Array<u64>>>(hs);
          let st1 = rocq_array::set::<u64>(v64, z, 2u64);
          let v81 = div(z, C);
          match eqb(v81, g) {
            true => {
              std::mem::drop(st1);
              std::mem::drop(P);
              std::mem::drop(U);
              std::mem::drop(V);
              std::mem::drop(Dl);
              std::mem::drop(head);
              std::mem::drop(nxt);
              let v94 = hkey(fst::<Rc<fh>, u64>(r));
              let v95 = &v94;
              let v98 = rocq_array::get::<u64>(&v95, z);
              std::mem::drop(v94);
              Rc::new(option::<u64>::Some(v98))
            },
            false => {
              let v116 = (fst::<Rc<fh>, u64>(r), st1);
              let v119 = Rc::clone(&P);
              let v122 = Rc::clone(&U);
              let v125 = Rc::clone(&V);
              let v128 = Rc::clone(&Dl);
              let v131 = Rc::clone(&head);
              let v134 = Rc::clone(&nxt);
              let v143 = expand(v119, v122, v125, v128, v131, v134, C, cap, v116, z);
              dijk(P, U, V, Dl, head, nxt, C, cap, g, v143, sub(cnt, 1u64), ())
            },
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
    },
  }
}

// Rocq: Fulltank.fulltank_implem.query
// Variant: uncurried
pub fn query(n: u64, P: Rc<Array<u64>>, U: Rc<Array<u64>>, V: Rc<Array<u64>>, Dl: Rc<Array<u64>>, head: Rc<Array<u64>>, nxt: Rc<Array<u64>>, cap: u64, s: u64, g: u64) -> Rc<option<u64>> {
  let C = add(cap, 1u64);
  let N = mul(n, C);
  let v30 = rocq_array::make::<u64>(N, 0u64);
  let v36 = rocq_array::make::<u64>(N, __rocq_global_147);
  let v42 = rocq_array::make::<u64>(N, __rocq_global_147);
  let v48 = rocq_array::make::<u64>(N, __rocq_global_147);
  let v54 = rocq_array::make::<u64>(N, __rocq_global_147);
  let v61 = rocq_array::make::<u64>(N, 0u64);
  let v68 = rocq_array::make::<u64>(N, 0u64);
  let v74 = rocq_array::make::<u64>(N, __rocq_global_147);
  let h0 = Rc::new(fh { hkey: v30, hpar: v36, hchd: v42, hlft: v48, hrgt: v54, hdeg: v61, hmrk: v68, hbuf: v74, hmin: __rocq_global_147 });
  let src = mul(s, C);
  let v113 = fh_insert(h0, src, 0u64);
  let v120 = rocq_array::make::<u64>(N, 0u64);
  let v129 = rocq_array::set::<u64>(v120, src, 1u64);
  dijk_1(P, U, V, Dl, head, nxt, C, cap, g, (v113, v129), N)
}

// Rocq: Fulltank.fulltank_implem.qloop
// Variant: uncurried
pub fn qloop_1(n: u64, P: Rc<Array<u64>>, U: Rc<Array<u64>>, V: Rc<Array<u64>>, Dl: Rc<Array<u64>>, head: Rc<Array<u64>>, nxt: Rc<Array<u64>>, Cs: Rc<Array<u64>>, Ss: Rc<Array<u64>>, Es: Rc<Array<u64>>, out: Rc<Array<Rc<option<u64>>>>, i: u64, q: u64) -> Rc<Array<Rc<option<u64>>>> {
  qloop(n, P, U, V, Dl, head, nxt, Cs, Ss, Es, out, i, q, ())
}

// Rocq: Fulltank.fulltank_implem.qloop (local: qloop)
// Variant: uncurried, lifted
pub fn qloop(n: u64, P: Rc<Array<u64>>, U: Rc<Array<u64>>, V: Rc<Array<u64>>, Dl: Rc<Array<u64>>, head: Rc<Array<u64>>, nxt: Rc<Array<u64>>, Cs: Rc<Array<u64>>, Ss: Rc<Array<u64>>, Es: Rc<Array<u64>>, out: Rc<Array<Rc<option<u64>>>>, i: u64, q: u64, _H: ()) -> Rc<Array<Rc<option<u64>>>> {
  let v21 = ltb(i, q);
  match bdec(v21) {
    sumbool::left => {
      let v26 = &Cs;
      let v29 = rocq_array::get::<u64>(&v26, i);
      let v30 = &Ss;
      let v33 = rocq_array::get::<u64>(&v30, i);
      let v34 = &Es;
      let v37 = rocq_array::get::<u64>(&v34, i);
      let v42 = Rc::clone(&P);
      let v45 = Rc::clone(&U);
      let v48 = Rc::clone(&V);
      let v51 = Rc::clone(&Dl);
      let v54 = Rc::clone(&head);
      let v57 = Rc::clone(&nxt);
      let v71 = rocq_array::set::<Rc<option<u64>>>(out, i, query(n, v42, v45, v48, v51, v54, v57, v29, v33, v37));
      qloop(n, P, U, V, Dl, head, nxt, Cs, Ss, Es, v71, add(i, 1u64), q, ())
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
  let v8 = &u;
  let m = rocq_array::length::<u64>(&v8);
  let v17 = rocq_array::make::<u64>(n, 0u64);
  let v40 = rocq_array::make::<u64>(add(mul(2u64, m), 1u64), 0u64);
  let v45 = Rc::clone(&u);
  let v48 = Rc::clone(&v);
  let hn = build_1(v45, v48, v17, v40, 0u64, m);
  let v58 = &c;
  let q = rocq_array::length::<u64>(&v58);
  let v63 = Clone::clone(&hn);
  let v65 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(v63);
  let v69 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(hn);
  let v77 = rocq_array::make::<Rc<option<u64>>>(q, Rc::new(option::<u64>::None));
  qloop_1(n, p, u, v, d, v65, v69, c, s, e, v77, 0u64, q)
}

// Rocq: Fulltank.fulltank_implem.fulltank_impl
pub fn fulltank_impl_curried(n: u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>>>>>> {
  let v3 = {
    move |p: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>>>>> {
      let n = &n;
      let v8 = Clone::clone(n);
      let v11 = {
        move |u: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>>>> {
          let n = &v8;
          let p = &p;
          let v18 = Clone::clone(n);
          let v20 = Rc::clone(p);
          let v23 = {
            move |v: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>>> {
              let n = &v18;
              let p = &v20;
              let u = &u;
              let v32 = Clone::clone(n);
              let v34 = Rc::clone(p);
              let v36 = Rc::clone(u);
              let v39 = {
                move |d: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>> {
                  let n = &v32;
                  let p = &v34;
                  let u = &v36;
                  let v = &v;
                  let v50 = Clone::clone(n);
                  let v52 = Rc::clone(p);
                  let v54 = Rc::clone(u);
                  let v56 = Rc::clone(v);
                  let v59 = {
                    move |c: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>> {
                      let n = &v50;
                      let p = &v52;
                      let u = &v54;
                      let v = &v56;
                      let d = &d;
                      let v72 = Clone::clone(n);
                      let v74 = Rc::clone(p);
                      let v76 = Rc::clone(u);
                      let v78 = Rc::clone(v);
                      let v80 = Rc::clone(d);
                      let v83 = {
                        move |s: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>> {
                          let n = &v72;
                          let p = &v74;
                          let u = &v76;
                          let v = &v78;
                          let d = &v80;
                          let c = &c;
                          let v98 = Clone::clone(n);
                          let v100 = Rc::clone(p);
                          let v102 = Rc::clone(u);
                          let v104 = Rc::clone(v);
                          let v106 = Rc::clone(d);
                          let v108 = Rc::clone(c);
                          let v111 = {
                            move |e: Rc<Array<u64>>| -> Rc<Array<Rc<option<u64>>>> {
                              let v129 = Clone::clone(&v98);
                              let v131 = Rc::clone(&v100);
                              let v133 = Rc::clone(&v102);
                              let v135 = Rc::clone(&v104);
                              let v137 = Rc::clone(&v106);
                              let v139 = Rc::clone(&v108);
                              let v141 = Rc::clone(&s);
                              fulltank_impl(v129, v131, v133, v135, v137, v139, v141, e)
                            }
                          };
                          let v147: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>> = Rc::new(v111);
                          v147
                        }
                      };
                      let v151: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>> = Rc::new(v83);
                      v151
                    }
                  };
                  let v155: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>> = Rc::new(v59);
                  v155
                }
              };
              let v159: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>>> = Rc::new(v39);
              v159
            }
          };
          let v163: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>>>> = Rc::new(v23);
          v163
        }
      };
      let v167: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>>>>> = Rc::new(v11);
      v167
    }
  };
  let v171: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>>>>>> = Rc::new(v3);
  v171
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>> {
  let v0: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>> = __rocq_global_1571.with(Clone::clone);
  v0
}
const __rocq_global_147: u64 = 9223372036854775807u64;
std::thread_local! { static __rocq_global_1571: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>> = fulltank(); }
std::thread_local! { static __rocq_global_1574: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<Rc<option<u64>>>>>>>>>>>> = fulltank_curried(); }