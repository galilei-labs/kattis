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

pub enum command {
  Add { energy: Int63, gold: Int63 },
  Query { energy: Int63 },
}

impl Clone for command {
  fn clone(&self) -> Self {
    match self {
      command::Add { energy: __field0, gold: __field1 } => command::Add { energy: Clone::clone(__field0), gold: Clone::clone(__field1) },
      command::Query { energy: __field0 } => command::Query { energy: Clone::clone(__field0) },
    }
  }
}

pub type uint = Int63;

// Rocq: Kattissquest.kattissquest_implem.nil
pub fn nil() -> Int63 {
  int63!(9223372036854775807)
}

// Rocq: Kattissquest.kattissquest_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Kattissquest.kattissquest_implem.scan
// Variant: uncurried
pub fn scan_1(x: Array<Rc<command>>, N: Int63, j: Int63, m: Int63, q: Int63) -> (Int63, Int63) {
  scan(x, N, j, m, q, ())
}

// Rocq: Kattissquest.kattissquest_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(x: Array<Rc<command>>, N: Int63, j: Int63, m: Int63, q: Int63, _H: ()) -> (Int63, Int63) {
  let tmp = j < N;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = x.get_cloned(j);
      let (v21, v22) = __rocq_reuse::reset(tmp_1, |__payload| Clone::clone(__payload));
      std::mem::drop(v22);
      match v21 {
        command::Add { energy: v29, gold: _v31 } => {
          let tmp_2 = j + int63!(1);
          let tmp_3 = if m < v29 {
            v29
          } else {
            m
          };
          scan(x, N, tmp_2, tmp_3, q, ())
        },
        command::Query { energy: _v71 } => {
          scan(x, N, j + int63!(1), m, q + int63!(1), ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      (m, q)
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

// Rocq: Kattissquest.kattissquest_implem.kloop
// Variant: uncurried
pub fn kloop_1(m: Int63, k: Int63) -> Int63 {
  kloop(m, k, ())
}

// Rocq: Kattissquest.kattissquest_implem.kloop (local: kloop)
// Variant: uncurried, lifted
pub fn kloop(m: Int63, k: Int63, _H: ()) -> Int63 {
  let tmp = andb(k < int63!(62), int63!(1) << k <= m);
  match bdec(tmp) {
    sumbool::left => {
      kloop(m, k + int63!(1), ())
    },
    sumbool::right => {
      k
    },
  }
}

// Rocq: Kattissquest.kattissquest_implem.kh
pub fn kh(k: Int63) -> Int63 {
  let tmp = k >> int63!(1);
  k - tmp
}

// Rocq: Kattissquest.kattissquest_implem.kl
pub fn kl(k: Int63) -> Int63 {
  k >> int63!(1)
}

// Rocq: Kattissquest.kattissquest_implem.stab
// Variant: uncurried
pub fn stab_1(t: Array<Int63>, K: Int63, k: Int63) -> Array<Int63> {
  stab(t, K, k, ())
}

// Rocq: Kattissquest.kattissquest_implem.stab (local: stab)
// Variant: uncurried, lifted
pub fn stab(t: Array<Int63>, K: Int63, k: Int63, _H: ()) -> Array<Int63> {
  let tmp = k < K + int63!(1);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = int63!(1);
      let s = if k <= tmp_1 {
        int63!(2)
      } else {
        let tmp_2 = t.get_cloned(kh(k));
        let tmp_3 = int63!(2) + tmp_2;
        let tmp_4 = t.get_cloned(kl(k));
        tmp_3 + (tmp_4 << kh(k))
      };
      stab(t.set(k, s), K, k + int63!(1), ())
    },
    sumbool::right => {
      t
    },
  }
}

// Rocq: Kattissquest.kattissquest_implem.cntloop
// Variant: uncurried
pub fn cntloop_1(x: Array<Rc<command>>, N: Int63, j: Int63, c: Array<Int63>) -> Array<Int63> {
  cntloop(x, N, j, c, ())
}

// Rocq: Kattissquest.kattissquest_implem.cntloop (local: cntloop)
// Variant: uncurried, lifted
pub fn cntloop(x: Array<Rc<command>>, N: Int63, j: Int63, c: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = j < N;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = x.get_cloned(j);
      let (v20, v21) = __rocq_reuse::reset(tmp_1, |__payload| Clone::clone(__payload));
      std::mem::drop(v21);
      match v20 {
        command::Add { energy: v28, gold: _v30 } => {
          let tmp_2 = j + int63!(1);
          let tmp_3 = c.get_cloned(v28);
          cntloop(x, N, tmp_2, c.set(v28, tmp_3 + int63!(1)), ())
        },
        command::Query { energy: _v75 } => {
          cntloop(x, N, j + int63!(1), c, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      c
    },
  }
}

// Rocq: Kattissquest.kattissquest_implem.pref
// Variant: uncurried
pub fn pref_1(c: Array<Int63>, U: Int63, e: Int63, acc: Int63) -> Array<Int63> {
  pref(c, U, e, acc, ())
}

// Rocq: Kattissquest.kattissquest_implem.pref (local: pref)
// Variant: uncurried, lifted
pub fn pref(c: Array<Int63>, U: Int63, e: Int63, acc: Int63, _H: ()) -> Array<Int63> {
  let tmp = e < U;
  match bdec(tmp) {
    sumbool::left => {
      let ce = c.get_cloned(e);
      pref(c.set(e, acc), U, e + int63!(1), acc + ce, ())
    },
    sumbool::right => {
      c
    },
  }
}

// Rocq: Kattissquest.kattissquest_implem.sup
// Variant: uncurried
pub fn sup_1(gd: Array<Int63>, s: Int63, i: Int63) -> Array<Int63> {
  sup(gd, s, i, ())
}

// Rocq: Kattissquest.kattissquest_implem.sup (local: sup)
// Variant: uncurried, lifted
pub fn sup(gd: Array<Int63>, s: Int63, i: Int63, _H: ()) -> Array<Int63> {
  let tmp = int63!(0) < i;
  match bdec(tmp) {
    sumbool::left => {
      let p = i - int63!(1) >> int63!(1);
      let a_1 = gd.get_cloned(s + p);
      let b_1 = gd.get_cloned(s + i);
      if a_1 < b_1 {
        sup(gd.set(s + p, b_1).set(s + i, a_1), s, p, ())
      } else {
        gd
      }
    },
    sumbool::right => {
      gd
    },
  }
}

// Rocq: Kattissquest.kattissquest_implem.hpush
// Variant: uncurried
pub fn hpush(gd: Array<Int63>, s: Int63, n: Int63, g: Int63) -> Array<Int63> {
  sup_1(gd.set(s + n, g), s, n)
}

// Rocq: Kattissquest.kattissquest_implem.clb
// Variant: uncurried
pub fn clb(t: Array<Int63>, b_1: Int63, k: Int63, i: Int63) -> Int63 {
  let tmp = b_1 + int63!(2);
  let tmp_1 = t.get_cloned(kh(k));
  let tmp_2 = tmp + tmp_1;
  let tmp_3 = t.get_cloned(kl(k));
  std::mem::drop(t);
  tmp_2 + i * tmp_3
}

// Rocq: Kattissquest.kattissquest_implem.vins
// Variant: uncurried
pub fn vins_1(t: Array<Int63>, v: Array<Int63>, b_1: Int63, k: Int63, x: Int63) -> Array<Int63> {
  vins(t, v, b_1, k, x, ())
}

// Rocq: Kattissquest.kattissquest_implem.vins (local: vins)
// Variant: uncurried, lifted
pub fn vins(t: Array<Int63>, v: Array<Int63>, b_1: Int63, k: Int63, x: Int63, _H: ()) -> Array<Int63> {
  let m = v.get_cloned(b_1);
  if m == __rocq_global_488 {
    std::mem::drop(t);
    v.set(b_1, x).set(b_1 + int63!(1), x)
  } else {
    let y = if x < m {
      m
    } else {
      x
    };
    let v1 = if x < m {
      v.set(b_1, x)
    } else {
      v
    };
    let tmp = int63!(1) < k;
    let v2 = match bdec(tmp) {
      sumbool::left => {
        let hy = y >> kl(k);
        let ly = y - (hy << kl(k));
        let t_clone = Clone::clone(&t);
        let c = clb(t_clone, b_1, k, hy);
        let tmp_1 = v1.get_cloned(c);
        if tmp_1 == __rocq_global_488 {
          let v3 = vins(t, v1, b_1 + int63!(2), kh(k), hy, ());
          v3.set(c, ly).set(c + int63!(1), ly)
        } else {
          vins(t, v1, c, kl(k), ly, ())
        }
      },
      sumbool::right => {
        std::mem::drop(t);
        v1
      },
    };
    let tmp_2 = v2.get_cloned(b_1 + int63!(1));
    if tmp_2 < y {
      v2.set(b_1 + int63!(1), y)
    } else {
      v2
    }
  }
}

// Rocq: Kattissquest.kattissquest_implem.vpred
// Variant: uncurried
pub fn vpred_1(t: Array<Int63>, v: Array<Int63>, b_1: Int63, k: Int63, x: Int63) -> Int63 {
  vpred(t, v, b_1, k, x, ())
}

// Rocq: Kattissquest.kattissquest_implem.vpred (local: vpred)
// Variant: uncurried, lifted
pub fn vpred(t: Array<Int63>, v: Array<Int63>, b_1: Int63, k: Int63, x: Int63, _H: ()) -> Int63 {
  let m = v.get_cloned(b_1);
  if x < m {
    std::mem::drop(t);
    std::mem::drop(v);
    __rocq_global_488
  } else {
    let M = v.get_cloned(b_1 + int63!(1));
    if M <= x {
      std::mem::drop(t);
      std::mem::drop(v);
      M
    } else {
      let tmp = int63!(1) < k;
      match bdec(tmp) {
        sumbool::left => {
          let hx = x >> kl(k);
          let lx = x - (hx << kl(k));
          let t_clone = Clone::clone(&t);
          let c = clb(t_clone, b_1, k, hx);
          let tmp_1 = v.get_cloned(c);
          if tmp_1 <= lx {
            (hx << kl(k)) + vpred(t, v, c, kl(k), lx, ())
          } else {
            if hx == int63!(0) {
              std::mem::drop(t);
              std::mem::drop(v);
              m
            } else {
              let tmp_2 = b_1 + int63!(2);
              let tmp_3 = kh(k);
              let tmp_4 = hx - int63!(1);
              let t_clone_1 = Clone::clone(&t);
              let v_clone = Clone::clone(&v);
              let ph = vpred(t_clone_1, v_clone, tmp_2, tmp_3, tmp_4, ());
              if ph == __rocq_global_488 {
                std::mem::drop(t);
                std::mem::drop(v);
                m
              } else {
                let tmp_5 = ph << kl(k);
                let tmp_6 = v.get_cloned(clb(t, b_1, k, ph) + int63!(1));
                std::mem::drop(v);
                tmp_5 + tmp_6
              }
            }
          }
        },
        sumbool::right => {
          std::mem::drop(t);
          std::mem::drop(v);
          m
        },
      }
    }
  }
}

// Rocq: Kattissquest.kattissquest_implem.pickc
// Variant: uncurried
pub fn pickc(gd: Array<Int63>, s: Int63, n: Int63, i: Int63) -> Int63 {
  let c1 = int63!(2) * i + int63!(1);
  let tmp = c1 + int63!(1);
  if tmp < n {
    let tmp_1 = gd.get_cloned(s + c1);
    let tmp_2 = gd.get_cloned(s + (c1 + int63!(1)));
    if tmp_1 < tmp_2 {
      std::mem::drop(gd);
      c1 + int63!(1)
    } else {
      std::mem::drop(gd);
      c1
    }
  } else {
    std::mem::drop(gd);
    c1
  }
}

// Rocq: Kattissquest.kattissquest_implem.sdown
// Variant: uncurried
pub fn sdown_1(gd: Array<Int63>, s: Int63, n: Int63, i: Int63) -> Array<Int63> {
  sdown(gd, s, n, i, ())
}

// Rocq: Kattissquest.kattissquest_implem.sdown (local: sdown)
// Variant: uncurried, lifted
pub fn sdown(gd: Array<Int63>, s: Int63, n: Int63, i: Int63, _H: ()) -> Array<Int63> {
  let tmp = int63!(2) * i;
  let tmp_1 = andb(i < tmp + int63!(1), int63!(2) * i + int63!(1) < n);
  match bdec(tmp_1) {
    sumbool::left => {
      let gd_clone = Clone::clone(&gd);
      let c = pickc(gd_clone, s, n, i);
      let a_1 = gd.get_cloned(s + i);
      let b_1 = gd.get_cloned(s + c);
      if a_1 < b_1 {
        sdown(gd.set(s + i, b_1).set(s + c, a_1), s, n, c, ())
      } else {
        gd
      }
    },
    sumbool::right => {
      gd
    },
  }
}

// Rocq: Kattissquest.kattissquest_implem.hpop
// Variant: uncurried
pub fn hpop(gd: Array<Int63>, s: Int63, n: Int63) -> Array<Int63> {
  let last = gd.get_cloned(s + (n - int63!(1)));
  sdown_1(gd.set(s, last), s, n - int63!(1), int63!(0))
}

// Rocq: Kattissquest.kattissquest_implem.vdel
// Variant: uncurried
pub fn vdel_1(t: Array<Int63>, v: Array<Int63>, b_1: Int63, k: Int63, x: Int63) -> Array<Int63> {
  vdel(t, v, b_1, k, x, ())
}

// Rocq: Kattissquest.kattissquest_implem.vdel (local: vdel)
// Variant: uncurried, lifted
pub fn vdel(t: Array<Int63>, v: Array<Int63>, b_1: Int63, k: Int63, x: Int63, _H: ()) -> Array<Int63> {
  let m = v.get_cloned(b_1);
  let M = v.get_cloned(b_1 + int63!(1));
  if m == M {
    std::mem::drop(t);
    v.set(b_1, __rocq_global_488).set(b_1 + int63!(1), __rocq_global_488)
  } else {
    let tmp = int63!(1) < k;
    match bdec(tmp) {
      sumbool::left => {
        let y = if x == m {
          let f = v.get_cloned(b_1 + int63!(2));
          let tmp_1 = f << kl(k);
          let t_clone = Clone::clone(&t);
          let tmp_2 = v.get_cloned(clb(t_clone, b_1, k, f));
          tmp_1 + tmp_2
        } else {
          x
        };
        let v1 = if x == m {
          v.set(b_1, y)
        } else {
          v
        };
        let hy = y >> kl(k);
        let ly = y - (hy << kl(k));
        let t_clone_1 = Clone::clone(&t);
        let c = clb(t_clone_1, b_1, k, hy);
        let tmp_3 = kl(k);
        let t_clone_2 = Clone::clone(&t);
        let v2 = vdel(t_clone_2, v1, c, tmp_3, ly, ());
        let tmp_4 = v2.get_cloned(c);
        if tmp_4 == __rocq_global_488 {
          let tmp_5 = b_1 + int63!(2);
          let tmp_6 = kh(k);
          let t_clone_3 = Clone::clone(&t);
          let v3 = vdel(t_clone_3, v2, tmp_5, tmp_6, hy, ());
          let tmp_7 = v3.get_cloned(b_1 + int63!(1));
          if y == tmp_7 {
            let sm = v3.get_cloned(b_1 + int63!(2) + int63!(1));
            if sm == __rocq_global_488 {
              std::mem::drop(t);
              let tmp_8 = b_1 + int63!(1);
              let tmp_9 = v3.get_cloned(b_1);
              v3.set(tmp_8, tmp_9)
            } else {
              let tmp_10 = b_1 + int63!(1);
              let tmp_11 = sm << kl(k);
              let tmp_12 = v3.get_cloned(clb(t, b_1, k, sm) + int63!(1));
              v3.set(tmp_10, tmp_11 + tmp_12)
            }
          } else {
            std::mem::drop(t);
            v3
          }
        } else {
          let tmp_13 = v2.get_cloned(b_1 + int63!(1));
          if y == tmp_13 {
            std::mem::drop(t);
            let tmp_14 = b_1 + int63!(1);
            let tmp_15 = hy << kl(k);
            let tmp_16 = v2.get_cloned(c + int63!(1));
            v2.set(tmp_14, tmp_15 + tmp_16)
          } else {
            std::mem::drop(t);
            v2
          }
        }
      },
      sumbool::right => {
        let tmp_17 = int63!(0);
        let r = if x == tmp_17 {
          std::mem::drop(t);
          int63!(1)
        } else {
          std::mem::drop(t);
          int63!(0)
        };
        v.set(b_1, r).set(b_1 + int63!(1), r)
      },
    }
  }
}

// Rocq: Kattissquest.kattissquest_implem.sess
// Variant: uncurried
pub fn sess_1(t: Array<Int63>, st: Array<Int63>, K: Int63, U: Int63, v: Array<Int63>, gd: Array<Int63>, hz: Array<Int63>, x: Int63, acc: Int63) -> (((Array<Int63>, Array<Int63>), Array<Int63>), Int63) {
  sess(t, st, K, U, v, gd, hz, x, acc, ())
}

// Rocq: Kattissquest.kattissquest_implem.sess (local: sess)
// Variant: uncurried, lifted
pub fn sess(t: Array<Int63>, st: Array<Int63>, K: Int63, U: Int63, v: Array<Int63>, gd: Array<Int63>, hz: Array<Int63>, x: Int63, acc: Int63, _H: ()) -> (((Array<Int63>, Array<Int63>), Array<Int63>), Int63) {
  let x_ = if x < U {
    x
  } else {
    U - int63!(1)
  };
  let t_clone = Clone::clone(&t);
  let v_clone = Clone::clone(&v);
  let e = vpred_1(t_clone, v_clone, int63!(0), K, x_);
  let tmp = andb(int63!(0) < e, e <= x);
  match bdec(tmp) {
    sumbool::left => {
      let s = st.get_cloned(e);
      let n = hz.get_cloned(e);
      let g = gd.get_cloned(s);
      let gd1 = hpop(gd, s, n);
      let hz1 = hz.set(e, n - int63!(1));
      let tmp_1 = int63!(1);
      let v1 = if n == tmp_1 {
        let t_clone_1 = Clone::clone(&t);
        vdel_1(t_clone_1, v, int63!(0), K, e)
      } else {
        v
      };
      sess(t, st, K, U, v1, gd1, hz1, x - e, acc + g, ())
    },
    sumbool::right => {
      std::mem::drop(t);
      std::mem::drop(st);
      (((v, gd), hz), acc)
    },
  }
}

// Rocq: Kattissquest.kattissquest_implem.mloop
// Variant: uncurried
pub fn mloop_1(x: Array<Rc<command>>, t: Array<Int63>, st: Array<Int63>, K: Int63, U: Int63, N: Int63, j: Int63, v: Array<Int63>, gd: Array<Int63>, hz: Array<Int63>, out: Array<Int63>, qi: Int63) -> Array<Int63> {
  mloop(x, t, st, K, U, N, j, v, gd, hz, out, qi, ())
}

// Rocq: Kattissquest.kattissquest_implem.mloop (local: mloop)
// Variant: uncurried, lifted
pub fn mloop(x: Array<Rc<command>>, t: Array<Int63>, st: Array<Int63>, K: Int63, U: Int63, N: Int63, j: Int63, v: Array<Int63>, gd: Array<Int63>, hz: Array<Int63>, out: Array<Int63>, qi: Int63, _H: ()) -> Array<Int63> {
  let tmp = j < N;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = x.get_cloned(j);
      match &*tmp_1 {
        command::Add { energy: g, gold: e } => {
          let st_ref = &st;
          let s = st_ref.get_cloned(Clone::clone(g));
          let hz_ref = &hz;
          let n = hz_ref.get_cloned(Clone::clone(g));
          let gd1 = hpush(gd, s, n, Clone::clone(e));
          let tmp_2 = n + int63!(1);
          let hz1 = hz.set(Clone::clone(g), tmp_2);
          let tmp_3 = int63!(0);
          let v1 = if n == tmp_3 {
            let tmp_4 = int63!(0);
            let t_clone = Clone::clone(&t);
            let g_clone = Clone::clone(g);
            std::mem::drop(tmp_1);
            vins_1(t_clone, v, tmp_4, K, g_clone)
          } else {
            std::mem::drop(tmp_1);
            v
          };
          mloop(x, t, st, K, U, N, j + int63!(1), v1, gd1, hz1, out, qi, ())
        },
        command::Query { energy: q } => {
          let tmp_5 = int63!(0);
          let t_clone_1 = Clone::clone(&t);
          let st_clone = Clone::clone(&st);
          let q_clone = Clone::clone(q);
          std::mem::drop(tmp_1);
          let tmp_6 = sess_1(t_clone_1, st_clone, K, U, v, gd, hz, q_clone, tmp_5);
          match tmp_6 {
            (v163, v165) => {
              match v163 {
                (v168, v170) => {
                  match v168 {
                    (v173, v175) => {
                      mloop(x, t, st, K, U, N, j + int63!(1), v173, v175, v170, out.set(qi, v165), qi + int63!(1), ())
                    },
                  }
                },
              }
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(t);
      std::mem::drop(st);
      std::mem::drop(v);
      std::mem::drop(gd);
      std::mem::drop(hz);
      out
    },
  }
}

// Rocq: Kattissquest.kattissquest_implem.kattissquest_impl
pub fn kattissquest_impl(x: Array<Rc<command>>) -> Array<Int63> {
  let N = x.length();
  let x_clone = Clone::clone(&x);
  let tmp = scan_1(x_clone, N, int63!(0), int63!(1), int63!(0));
  match tmp {
    (v23, v25) => {
      let K = kloop_1(v23, int63!(1));
      let t = stab_1(Array::<Int63>::make(K + int63!(1), int63!(0)), K, int63!(1));
      let U = int63!(1) << K;
      let tmp_1 = Array::<Int63>::make(U, int63!(0));
      let x_clone_1 = Clone::clone(&x);
      let cnt = cntloop_1(x_clone_1, N, int63!(0), tmp_1);
      let st = pref_1(cnt, U, int63!(0), int63!(0));
      let tmp_2 = t.get_cloned(K);
      let tmp_3 = Array::<Int63>::make(tmp_2, __rocq_global_488);
      let tmp_4 = Array::<Int63>::make(N, int63!(0));
      let tmp_5 = Array::<Int63>::make(U, int63!(0));
      mloop_1(x, t, st, K, U, N, int63!(0), tmp_3, tmp_4, tmp_5, Array::<Int63>::make(v25, int63!(0)), int63!(0))
    },
  }
}
const __rocq_global_488: Int63 = int63!(9223372036854775807);