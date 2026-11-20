#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<std::cmp::Ordering>; };

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

pub type char63 = Int63;

// Rocq: Doublets.doublets_implem.M_word
pub fn M_word() -> Int63 {
  int63!(65536)
}

// Rocq: Doublets.doublets_implem.M_key
pub fn M_key() -> Int63 {
  int63!(1048576)
}

// Rocq: Doublets.doublets_implem.bdec
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

// Rocq: Doublets.doublets_implem.hloop
// Variant: uncurried
pub fn hloop_1(x: rocq_string::RocqString, p: Int63, len: Int63, j: Int63, h: Int63) -> Int63 {
  hloop(x, p, len, j, h, ())
}

// Rocq: Doublets.doublets_implem.hloop (local: hloop)
// Variant: uncurried, lifted
pub fn hloop(x: rocq_string::RocqString, p: Int63, len: Int63, j: Int63, h: Int63, _H: ()) -> Int63 {
  let tmp = j < len;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = j + int63!(1);
      let tmp_2 = h * int63!(31);
      let tmp_3 = if j == p {
        int63!(1)
      } else {
        let x_clone = Clone::clone(&x);
        get(x_clone, j) + int63!(2)
      };
      hloop(x, p, len, tmp_1, tmp_2 + tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      h
    },
  }
}

// Rocq: Doublets.doublets_implem.khash
// Variant: uncurried
pub fn khash(m: Int63, x: rocq_string::RocqString, p: Int63) -> Int63 {
  let x_clone = Clone::clone(&x);
  let len = length(x_clone);
  hloop_1(x, p, len, int63!(0), int63!(7)) % m
}

// Rocq: Doublets.doublets_implem.wbuild
// Variant: uncurried
pub fn wbuild_1(xd: Array<rocq_string::RocqString>, n: Int63, i: Int63, wl: Array<Int63>, wb: Array<Int63>, wn: Array<Int63>) -> ((Array<Int63>, Array<Int63>), Array<Int63>) {
  wbuild(xd, n, i, wl, wb, wn, ())
}

// Rocq: Doublets.doublets_implem.wbuild (local: wbuild)
// Variant: uncurried, lifted
pub fn wbuild(xd: Array<rocq_string::RocqString>, n: Int63, i: Int63, wl: Array<Int63>, wb: Array<Int63>, wn: Array<Int63>, _H: ()) -> ((Array<Int63>, Array<Int63>), Array<Int63>) {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let xd_ref = &xd;
      let w = xd_ref.get_cloned(i);
      let w_clone = Clone::clone(&w);
      let tmp_1 = length(w_clone);
      let w_clone_1 = Clone::clone(&w);
      let h = khash(__rocq_global_196, w_clone_1, tmp_1);
      let old = wb.get_cloned(h);
      wbuild(xd, n, i + int63!(1), wl.set(i, length(w)), wb.set(h, i + int63!(1)), wn.set(i, old), ())
    },
    sumbool::right => {
      std::mem::drop(xd);
      ((wl, wb), wn)
    },
  }
}

// Rocq: Doublets.doublets_implem.find
// Variant: uncurried
pub fn find_1(nx: Array<Int63>, test: Rc<dyn Fn(Int63) -> bool>, ptr: Int63) -> Int63 {
  find(nx, test, ptr, ())
}

// Rocq: Doublets.doublets_implem.find (local: find)
// Variant: uncurried, lifted
pub fn find(nx: Array<Int63>, test: Rc<dyn Fn(Int63) -> bool>, ptr: Int63, _H: ()) -> Int63 {
  if ptr == int63!(0) {
    std::mem::drop(nx);
    std::mem::drop(test);
    int63!(0)
  } else {
    let tmp = ptr - int63!(1);
    let test_ref: &Rc<dyn Fn(Int63) -> bool> = &test;
    let tmp_1 = test_ref(tmp);
    if tmp_1 {
      std::mem::drop(nx);
      std::mem::drop(test);
      ptr
    } else {
      let tmp_2 = nx.get_cloned(ptr - int63!(1));
      let tmp_3 = tmp_2 < ptr;
      match bdec(tmp_3) {
        sumbool::left => {
          let tmp_4 = nx.get_cloned(ptr - int63!(1));
          find(nx, test, tmp_4, ())
        },
        sumbool::right => {
          std::mem::drop(nx);
          std::mem::drop(test);
          int63!(0)
        },
      }
    }
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

// Rocq: Doublets.doublets_implem.kloop
// Variant: uncurried
pub fn kloop_1(x: rocq_string::RocqString, y: rocq_string::RocqString, p: Int63, len: Int63, j: Int63) -> bool {
  kloop(x, y, p, len, j, ())
}

// Rocq: Doublets.doublets_implem.kloop (local: kloop)
// Variant: uncurried, lifted
pub fn kloop(x: rocq_string::RocqString, y: rocq_string::RocqString, p: Int63, len: Int63, j: Int63, _H: ()) -> bool {
  let tmp = j < len;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = j == p;
      let x_clone = Clone::clone(&x);
      let tmp_2 = get(x_clone, j);
      let y_clone = Clone::clone(&y);
      let tmp_3 = tmp_2 == get(y_clone, j);
      if orb(tmp_1, tmp_3) {
        kloop(x, y, p, len, j + int63!(1), ())
      } else {
        std::mem::drop(x);
        std::mem::drop(y);
        false
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      true
    },
  }
}

// Rocq: Doublets.doublets_implem.keq
// Variant: uncurried
pub fn keq(x: rocq_string::RocqString, y: rocq_string::RocqString, p: Int63) -> bool {
  let x_clone = Clone::clone(&x);
  let len = length(x_clone);
  let y_clone = Clone::clone(&y);
  let tmp = length(y_clone);
  if len == tmp {
    kloop_1(x, y, p, len, int63!(0))
  } else {
    std::mem::drop(x);
    std::mem::drop(y);
    false
  }
}

// Rocq: Doublets.doublets_implem.ktest
// Variant: borrowed, uncurried
pub fn ktest(xd: &Array<rocq_string::RocqString>, w: &rocq_string::RocqString, p: Int63, y: Int63) -> bool {
  let p_1 = p;
  let y_1 = y;
  andb(y_1 % int63!(16) == p_1, keq(xd.get_cloned(y_1 >> int63!(4)), Clone::clone(w), p_1))
}

// Rocq: Doublets.doublets_implem.build
// Variant: uncurried
pub fn build_1(xd: Array<rocq_string::RocqString>, N16: Int63, e: Int63, cls: Array<Int63>, bk: Array<Int63>, bn: Array<Int63>, hd: Array<Int63>, cn: Array<Int63>) -> ((Array<Int63>, Array<Int63>), Array<Int63>) {
  build(xd, N16, e, cls, bk, bn, hd, cn, ())
}

// Rocq: Doublets.doublets_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(xd: Array<rocq_string::RocqString>, N16: Int63, e: Int63, cls: Array<Int63>, bk: Array<Int63>, bn: Array<Int63>, hd: Array<Int63>, cn: Array<Int63>, _H: ()) -> ((Array<Int63>, Array<Int63>), Array<Int63>) {
  let tmp = e < N16;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = e >> int63!(4);
      let xd_ref = &xd;
      let w = xd_ref.get_cloned(tmp_1);
      let p = e % int63!(16);
      let w_clone = Clone::clone(&w);
      let tmp_2 = length(w_clone);
      if p < tmp_2 {
        let w_clone_1 = Clone::clone(&w);
        let h = khash(__rocq_global_276, w_clone_1, p);
        let old = bk.get_cloned(h);
        let xd_clone = Clone::clone(&xd);
        let w_clone_2 = Clone::clone(&w);
        let callback: Rc<dyn Fn(Int63) -> bool> = Rc::new({
          let __anf_capture_80 = p;
          move |v82: Int63| -> bool {
            let xd = &xd_clone;
            let w = &w_clone_2;
            let tmp_3 = Clone::clone(&__anf_capture_80);
            ktest(xd, w, tmp_3, v82)
          }
        });
        let bn_clone = Clone::clone(&bn);
        let r = find_1(bn_clone, callback, old);
        let tmp_4 = int63!(0);
        let c = if r == tmp_4 {
          std::mem::drop(w);
          e
        } else {
          std::mem::drop(w);
          let tmp_5 = r - int63!(1);
          cls.get_cloned(tmp_5)
        };
        let oldc = hd.get_cloned(c);
        build(xd, N16, e + int63!(1), cls.set(e, c), bk.set(h, e + int63!(1)), bn.set(e, old), hd.set(c, e + int63!(1)), cn.set(e, oldc), ())
      } else {
        std::mem::drop(w);
        build(xd, N16, e + int63!(1), cls, bk, bn, hd, cn, ())
      }
    },
    sumbool::right => {
      std::mem::drop(xd);
      std::mem::drop(bk);
      std::mem::drop(bn);
      ((cls, hd), cn)
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

// Rocq: Doublets.doublets_implem.wtest
// Variant: borrowed, uncurried
pub fn wtest(xd: &Array<rocq_string::RocqString>, q: &rocq_string::RocqString, y: Int63) -> bool {
  let y_1 = y;
  let tmp = xd.get_cloned(y_1);
  let q_clone = Clone::clone(q);
  match compare(tmp, q_clone) {
    std::cmp::Ordering::Equal => {
      true
    },
    std::cmp::Ordering::Less => {
      false
    },
    std::cmp::Ordering::Greater => {
      false
    },
  }
}

// Rocq: Doublets.doublets_implem.lookup
// Variant: uncurried
pub fn lookup(xd: Array<rocq_string::RocqString>, wb: Array<Int63>, wn: Array<Int63>, q: rocq_string::RocqString) -> Int63 {
  let q_clone = Clone::clone(&q);
  let tmp = length(q_clone);
  let q_clone_1 = Clone::clone(&q);
  let h = khash(__rocq_global_196, q_clone_1, tmp);
  let ptr = wb.get_cloned(h);
  std::mem::drop(wb);
  let callback: Rc<dyn Fn(Int63) -> bool> = Rc::new({
    let __anf_capture_31 = q;
    move |v33: Int63| -> bool {
      wtest(&xd, &__anf_capture_31, v33)
    }
  });
  find_1(wn, callback, ptr)
}

// Rocq: Doublets.doublets_implem.sT
pub fn sT(s: ((((Array<Int63>, Array<Int63>), Array<Int63>), Int63), Array<Int63>)) -> Int63 {
  match s {
    (v2, v4) => {
      match v2 {
        (v7, v9) => {
          match v7 {
            (v12, v14) => {
              match v12 {
                (v17, v19) => {
                  std::mem::drop(v14);
                  std::mem::drop(v4);
                  std::mem::drop(v17);
                  std::mem::drop(v19);
                  v9
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Doublets.doublets_implem.sQ
pub fn sQ(s: ((((Array<Int63>, Array<Int63>), Array<Int63>), Int63), Array<Int63>)) -> Array<Int63> {
  match s {
    (v2, v4) => {
      match v2 {
        (v7, _v9) => {
          match v7 {
            (v12, v14) => {
              match v12 {
                (v17, v19) => {
                  std::mem::drop(v4);
                  std::mem::drop(v17);
                  std::mem::drop(v19);
                  v14
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Doublets.doublets_implem.sM
pub fn sM(s: ((((Array<Int63>, Array<Int63>), Array<Int63>), Int63), Array<Int63>)) -> Array<Int63> {
  match s {
    (v2, v4) => {
      match v2 {
        (v7, _v9) => {
          match v7 {
            (v12, v14) => {
              match v12 {
                (v17, v19) => {
                  std::mem::drop(v14);
                  std::mem::drop(v17);
                  std::mem::drop(v19);
                  v4
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Doublets.doublets_implem.sD
pub fn sD(s: ((((Array<Int63>, Array<Int63>), Array<Int63>), Int63), Array<Int63>)) -> Array<Int63> {
  match s {
    (v2, v4) => {
      match v2 {
        (v7, _v9) => {
          match v7 {
            (v12, v14) => {
              std::mem::drop(v4);
              let a0 = &v12;
              std::mem::drop(v14);
              let a0_0_clone = Clone::clone(&a0.0);
              std::mem::drop(v12);
              a0_0_clone
            },
          }
        },
      }
    },
  }
}

// Rocq: Doublets.doublets_implem.mkb
// Variant: uncurried
pub fn mkb(D: Array<Int63>, P: Array<Int63>, Q: Array<Int63>, T: Int63, M: Array<Int63>) -> ((((Array<Int63>, Array<Int63>), Array<Int63>), Int63), Array<Int63>) {
  ((((D, P), Q), T), M)
}

// Rocq: Doublets.doublets_implem.sP
pub fn sP(s: ((((Array<Int63>, Array<Int63>), Array<Int63>), Int63), Array<Int63>)) -> Array<Int63> {
  match s {
    (v2, v4) => {
      match v2 {
        (v7, _v9) => {
          match v7 {
            (v12, v14) => {
              std::mem::drop(v4);
              let a0 = &v12;
              std::mem::drop(v14);
              let a0_1_clone = Clone::clone(&a0.1);
              std::mem::drop(v12);
              a0_1_clone
            },
          }
        },
      }
    },
  }
}

// Rocq: Doublets.doublets_implem.cwalk
// Variant: uncurried
pub fn cwalk_1(cn: Array<Int63>, u: Int63, du: Int63, ptr: Int63, s: ((((Array<Int63>, Array<Int63>), Array<Int63>), Int63), Array<Int63>)) -> ((((Array<Int63>, Array<Int63>), Array<Int63>), Int63), Array<Int63>) {
  cwalk(cn, u, du, ptr, s, ())
}

// Rocq: Doublets.doublets_implem.cwalk (local: cwalk)
// Variant: uncurried, lifted
pub fn cwalk(cn: Array<Int63>, u: Int63, du: Int63, ptr: Int63, s: ((((Array<Int63>, Array<Int63>), Array<Int63>), Int63), Array<Int63>), _H: ()) -> ((((Array<Int63>, Array<Int63>), Array<Int63>), Int63), Array<Int63>) {
  if ptr == int63!(0) {
    std::mem::drop(cn);
    s
  } else {
    let e = ptr - int63!(1);
    let v = e >> int63!(4);
    let s_clone = Clone::clone(&s);
    let tmp = sD(s_clone);
    let tmp_1 = tmp.get_cloned(v);
    let tmp_2 = int63!(0);
    let s_ = if tmp_1 == tmp_2 {
      let s_clone_1 = Clone::clone(&s);
      let tmp_3 = sD(s_clone_1).set(v, du + int63!(1));
      let s_clone_2 = Clone::clone(&s);
      let tmp_4 = sP(s_clone_2).set(v, u);
      let s_clone_3 = Clone::clone(&s);
      let tmp_5 = sQ(s_clone_3);
      let s_clone_4 = Clone::clone(&s);
      let tmp_6 = tmp_5.set(sT(s_clone_4), v);
      let s_clone_5 = Clone::clone(&s);
      mkb(tmp_3, tmp_4, tmp_6, sT(s_clone_5) + int63!(1), sM(s))
    } else {
      s
    };
    let tmp_7 = cn.get_cloned(e);
    let tmp_8 = tmp_7 < ptr;
    match bdec(tmp_8) {
      sumbool::left => {
        std::mem::drop(tmp);
        let tmp_9 = cn.get_cloned(e);
        cwalk(cn, u, du, tmp_9, s_, ())
      },
      sumbool::right => {
        std::mem::drop(cn);
        std::mem::drop(tmp);
        s_
      },
    }
  }
}

// Rocq: Doublets.doublets_implem.ploop
// Variant: uncurried
pub fn ploop_1(cls: Array<Int63>, hd: Array<Int63>, cn: Array<Int63>, u: Int63, du: Int63, base: Int63, len: Int63, p: Int63, s: ((((Array<Int63>, Array<Int63>), Array<Int63>), Int63), Array<Int63>)) -> ((((Array<Int63>, Array<Int63>), Array<Int63>), Int63), Array<Int63>) {
  ploop(cls, hd, cn, u, du, base, len, p, s, ())
}

// Rocq: Doublets.doublets_implem.ploop (local: ploop)
// Variant: uncurried, lifted
pub fn ploop(cls: Array<Int63>, hd: Array<Int63>, cn: Array<Int63>, u: Int63, du: Int63, base: Int63, len: Int63, p: Int63, s: ((((Array<Int63>, Array<Int63>), Array<Int63>), Int63), Array<Int63>), _H: ()) -> ((((Array<Int63>, Array<Int63>), Array<Int63>), Int63), Array<Int63>) {
  let tmp = p < len;
  match bdec(tmp) {
    sumbool::left => {
      let c = cls.get_cloned(base + p);
      let s_clone = Clone::clone(&s);
      let tmp_1 = sM(s_clone);
      let tmp_2 = tmp_1.get_cloned(c);
      if tmp_2 == int63!(0) {
        std::mem::drop(tmp_1);
        let tmp_3 = hd.get_cloned(c);
        let cn_clone = Clone::clone(&cn);
        let s1 = cwalk_1(cn_clone, u, du, tmp_3, s);
        let tmp_4 = p + int63!(1);
        let s1_clone = Clone::clone(&s1);
        let tmp_5 = sD(s1_clone);
        let s1_clone_1 = Clone::clone(&s1);
        let tmp_6 = sP(s1_clone_1);
        let s1_clone_2 = Clone::clone(&s1);
        let tmp_7 = sQ(s1_clone_2);
        let s1_clone_3 = Clone::clone(&s1);
        ploop(cls, hd, cn, u, du, base, len, tmp_4, mkb(tmp_5, tmp_6, tmp_7, sT(s1_clone_3), sM(s1).set(c, int63!(1))), ())
      } else {
        std::mem::drop(tmp_1);
        ploop(cls, hd, cn, u, du, base, len, p + int63!(1), s, ())
      }
    },
    sumbool::right => {
      std::mem::drop(cls);
      std::mem::drop(hd);
      std::mem::drop(cn);
      s
    },
  }
}

// Rocq: Doublets.doublets_implem.bfs
// Variant: uncurried
pub fn bfs_1(cls: Array<Int63>, hd: Array<Int63>, cn: Array<Int63>, wl: Array<Int63>, n: Int63, qh: Int63, s: ((((Array<Int63>, Array<Int63>), Array<Int63>), Int63), Array<Int63>)) -> ((((Array<Int63>, Array<Int63>), Array<Int63>), Int63), Array<Int63>) {
  bfs(cls, hd, cn, wl, n, qh, s, ())
}

// Rocq: Doublets.doublets_implem.bfs (local: bfs)
// Variant: uncurried, lifted
pub fn bfs(cls: Array<Int63>, hd: Array<Int63>, cn: Array<Int63>, wl: Array<Int63>, n: Int63, qh: Int63, s: ((((Array<Int63>, Array<Int63>), Array<Int63>), Int63), Array<Int63>), _H: ()) -> ((((Array<Int63>, Array<Int63>), Array<Int63>), Int63), Array<Int63>) {
  let tmp = qh < n;
  match bdec(tmp) {
    sumbool::left => {
      let s_clone = Clone::clone(&s);
      let tmp_1 = sT(s_clone);
      if qh < tmp_1 {
        let s_clone_1 = Clone::clone(&s);
        let tmp_2 = sQ(s_clone_1);
        let u = tmp_2.get_cloned(qh);
        std::mem::drop(tmp_2);
        let len = wl.get_cloned(u);
        let s_clone_2 = Clone::clone(&s);
        let tmp_3 = sD(s_clone_2);
        let tmp_4 = tmp_3.get_cloned(u);
        std::mem::drop(tmp_3);
        let tmp_5 = u * int63!(16);
        let cls_clone = Clone::clone(&cls);
        let hd_clone = Clone::clone(&hd);
        let cn_clone = Clone::clone(&cn);
        let s_ = ploop_1(cls_clone, hd_clone, cn_clone, u, tmp_4, tmp_5, len, int63!(0), s);
        bfs(cls, hd, cn, wl, n, qh + int63!(1), s_, ())
      } else {
        std::mem::drop(cls);
        std::mem::drop(hd);
        std::mem::drop(cn);
        std::mem::drop(wl);
        s
      }
    },
    sumbool::right => {
      std::mem::drop(cls);
      std::mem::drop(hd);
      std::mem::drop(cn);
      std::mem::drop(wl);
      s
    },
  }
}

// Rocq: Doublets.doublets_implem.bfs_from
// Variant: uncurried
pub fn bfs_from(cls: Array<Int63>, hd: Array<Int63>, cn: Array<Int63>, wl: Array<Int63>, n: Int63, N16: Int63, s0: Int63) -> ((((Array<Int63>, Array<Int63>), Array<Int63>), Int63), Array<Int63>) {
  let tmp = Array::<Int63>::make(n, int63!(0)).set(s0, int63!(1));
  let tmp_1 = Array::<Int63>::make(n, int63!(0));
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  bfs_1(cls, hd, cn, wl, n, int63!(0), mkb(tmp, tmp_1, tmp_2.set(int63!(0), s0), int63!(1), Array::<Int63>::make(N16, int63!(0))))
}

// Rocq: Doublets.doublets_implem.recon
// Variant: uncurried
pub fn recon_1(xd: Array<rocq_string::RocqString>, D: Array<Int63>, P: Array<Int63>, v: Int63, out: Array<rocq_string::RocqString>) -> Array<rocq_string::RocqString> {
  recon(xd, D, P, v, out, ())
}

// Rocq: Doublets.doublets_implem.recon (local: recon)
// Variant: uncurried, lifted
pub fn recon(xd: Array<rocq_string::RocqString>, D: Array<Int63>, P: Array<Int63>, v: Int63, out: Array<rocq_string::RocqString>, _H: ()) -> Array<rocq_string::RocqString> {
  let tmp = D.get_cloned(v);
  let tmp_1 = tmp - int63!(1);
  let xd_ref = &xd;
  let tmp_2 = xd_ref.get_cloned(v);
  let out_ = out.set(tmp_1, tmp_2);
  let tmp_3 = D.get_cloned(v);
  if tmp_3 <= int63!(1) {
    std::mem::drop(P);
    std::mem::drop(xd);
    std::mem::drop(D);
    out_
  } else {
    let tmp_4 = P.get_cloned(v);
    let tmp_5 = D.get_cloned(tmp_4);
    let tmp_6 = D.get_cloned(v);
    let tmp_7 = tmp_5 < tmp_6;
    match bdec(tmp_7) {
      sumbool::left => {
        let tmp_8 = P.get_cloned(v);
        recon(xd, D, P, tmp_8, out_, ())
      },
      sumbool::right => {
        std::mem::drop(P);
        std::mem::drop(xd);
        std::mem::drop(D);
        out_
      },
    }
  }
}

// Rocq: Doublets.doublets_implem.answer2
// Variant: uncurried
pub fn answer2(xd: Array<rocq_string::RocqString>, n: Int63, N16: Int63, cls: Array<Int63>, hd: Array<Int63>, cn: Array<Int63>, wl: Array<Int63>, wb: Array<Int63>, wn: Array<Int63>, s0: Int63, tgt: rocq_string::RocqString) -> Rc<option<Array<rocq_string::RocqString>>> {
  let xd_clone = Clone::clone(&xd);
  let rt = lookup(xd_clone, wb, wn, tgt);
  if rt == int63!(0) {
    std::mem::drop(xd);
    std::mem::drop(cls);
    std::mem::drop(hd);
    std::mem::drop(cn);
    std::mem::drop(wl);
    Rc::new(option::<Array<rocq_string::RocqString>>::None)
  } else {
    let t = rt - int63!(1);
    let st = bfs_from(cls, hd, cn, wl, n, N16, s0);
    let st_clone = Clone::clone(&st);
    let tmp = sD(st_clone);
    let dt = tmp.get_cloned(t);
    if dt == int63!(0) {
      std::mem::drop(st);
      std::mem::drop(xd);
      std::mem::drop(tmp);
      Rc::new(option::<Array<rocq_string::RocqString>>::None)
    } else {
      std::mem::drop(tmp);
      let st_clone_1 = Clone::clone(&st);
      let tmp_1 = sD(st_clone_1);
      let tmp_2 = sP(st);
      let xd_ref = &xd;
      let tmp_3 = xd_ref.get_cloned(t);
      Rc::new(option::<Array<rocq_string::RocqString>>::Some(recon_1(xd, tmp_1, tmp_2, t, Array::<rocq_string::RocqString>::make(dt, tmp_3))))
    }
  }
}

// Rocq: Doublets.doublets_implem.answer1
// Variant: uncurried
pub fn answer1(xd: Array<rocq_string::RocqString>, n: Int63, N16: Int63, cls: Array<Int63>, hd: Array<Int63>, cn: Array<Int63>, wl: Array<Int63>, wb: Array<Int63>, wn: Array<Int63>, src: rocq_string::RocqString, tgt: rocq_string::RocqString) -> Rc<option<Array<rocq_string::RocqString>>> {
  let xd_clone = Clone::clone(&xd);
  let wb_clone = Clone::clone(&wb);
  let wn_clone = Clone::clone(&wn);
  let src_clone = Clone::clone(&src);
  let rs = lookup(xd_clone, wb_clone, wn_clone, src_clone);
  if rs == int63!(0) {
    std::mem::drop(xd);
    std::mem::drop(cls);
    std::mem::drop(hd);
    std::mem::drop(cn);
    std::mem::drop(wl);
    std::mem::drop(wb);
    std::mem::drop(wn);
    std::mem::drop(src);
    std::mem::drop(tgt);
    Rc::new(option::<Array<rocq_string::RocqString>>::None)
  } else {
    let s0 = rs - int63!(1);
    let tgt_clone = Clone::clone(&tgt);
    match compare(src, tgt_clone) {
      std::cmp::Ordering::Equal => {
        std::mem::drop(cls);
        std::mem::drop(hd);
        std::mem::drop(cn);
        std::mem::drop(wl);
        std::mem::drop(wb);
        std::mem::drop(wn);
        std::mem::drop(tgt);
        let tmp = int63!(1);
        let xd_ref = &xd;
        let tmp_1 = xd_ref.get_cloned(s0);
        std::mem::drop(xd);
        Rc::new(option::<Array<rocq_string::RocqString>>::Some(Array::<rocq_string::RocqString>::make(tmp, tmp_1)))
      },
      std::cmp::Ordering::Less => {
        answer2(xd, n, N16, cls, hd, cn, wl, wb, wn, s0, tgt)
      },
      std::cmp::Ordering::Greater => {
        answer2(xd, n, N16, cls, hd, cn, wl, wb, wn, s0, tgt)
      },
    }
  }
}

// Rocq: Doublets.doublets_implem.qloop
// Variant: uncurried
pub fn qloop_1(xd: Array<rocq_string::RocqString>, xs: Array<rocq_string::RocqString>, xt: Array<rocq_string::RocqString>, n: Int63, N16: Int63, cls: Array<Int63>, hd: Array<Int63>, cn: Array<Int63>, wl: Array<Int63>, wb: Array<Int63>, wn: Array<Int63>, nq: Int63, q: Int63, out: Array<Rc<option<Array<rocq_string::RocqString>>>>) -> Array<Rc<option<Array<rocq_string::RocqString>>>> {
  qloop(xd, xs, xt, n, N16, cls, hd, cn, wl, wb, wn, nq, q, out, ())
}

// Rocq: Doublets.doublets_implem.qloop (local: qloop)
// Variant: uncurried, lifted
pub fn qloop(xd: Array<rocq_string::RocqString>, xs: Array<rocq_string::RocqString>, xt: Array<rocq_string::RocqString>, n: Int63, N16: Int63, cls: Array<Int63>, hd: Array<Int63>, cn: Array<Int63>, wl: Array<Int63>, wb: Array<Int63>, wn: Array<Int63>, nq: Int63, q: Int63, out: Array<Rc<option<Array<rocq_string::RocqString>>>>, _H: ()) -> Array<Rc<option<Array<rocq_string::RocqString>>>> {
  let tmp = q < nq;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = q + int63!(1);
      let xs_ref = &xs;
      let tmp_2 = xs_ref.get_cloned(q);
      let xt_ref = &xt;
      let tmp_3 = xt_ref.get_cloned(q);
      let xd_clone = Clone::clone(&xd);
      let cls_clone = Clone::clone(&cls);
      let hd_clone = Clone::clone(&hd);
      let cn_clone = Clone::clone(&cn);
      let wl_clone = Clone::clone(&wl);
      let wb_clone = Clone::clone(&wb);
      let wn_clone = Clone::clone(&wn);
      let tmp_4 = answer1(xd_clone, n, N16, cls_clone, hd_clone, cn_clone, wl_clone, wb_clone, wn_clone, tmp_2, tmp_3);
      qloop(xd, xs, xt, n, N16, cls, hd, cn, wl, wb, wn, nq, tmp_1, out.set(q, tmp_4), ())
    },
    sumbool::right => {
      std::mem::drop(xd);
      std::mem::drop(xs);
      std::mem::drop(xt);
      std::mem::drop(cls);
      std::mem::drop(hd);
      std::mem::drop(cn);
      std::mem::drop(wl);
      std::mem::drop(wb);
      std::mem::drop(wn);
      out
    },
  }
}

// Rocq: Doublets.doublets_implem.doublets_impl
// Variant: uncurried
pub fn doublets_impl(xd: Array<rocq_string::RocqString>, xs: Array<rocq_string::RocqString>, xt: Array<rocq_string::RocqString>) -> Array<Rc<option<Array<rocq_string::RocqString>>>> {
  let n = xd.length();
  let N16 = n * int63!(16);
  let tmp = Array::<Int63>::make(n, int63!(0));
  let tmp_1 = Array::<Int63>::make(__rocq_global_196, int63!(0));
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  let xd_clone = Clone::clone(&xd);
  let tmp_3 = wbuild_1(xd_clone, n, int63!(0), tmp, tmp_1, tmp_2);
  match tmp_3 {
    (v53, v55) => {
      match v53 {
        (v58, v60) => {
          let tmp_4 = Array::<Int63>::make(N16, int63!(0));
          let tmp_5 = Array::<Int63>::make(__rocq_global_276, int63!(0));
          let tmp_6 = Array::<Int63>::make(N16, int63!(0));
          let tmp_7 = Array::<Int63>::make(N16, int63!(0));
          let tmp_8 = Array::<Int63>::make(N16, int63!(0));
          let xd_clone_1 = Clone::clone(&xd);
          let tmp_9 = build_1(xd_clone_1, N16, int63!(0), tmp_4, tmp_5, tmp_6, tmp_7, tmp_8);
          match tmp_9 {
            (v120, v122) => {
              match v120 {
                (v125, v127) => {
                  let nq = xs.length();
                  let tmp_10 = Array::<Rc<option<Array<rocq_string::RocqString>>>>::make(nq, Rc::new(option::<Array<rocq_string::RocqString>>::None));
                  qloop_1(xd, xs, xt, n, N16, v125, v127, v122, v58, v60, v55, nq, int63!(0), tmp_10)
                },
              }
            },
          }
        },
      }
    },
  }
}
const __rocq_global_196: Int63 = int63!(65536);
const __rocq_global_276: Int63 = int63!(1048576);