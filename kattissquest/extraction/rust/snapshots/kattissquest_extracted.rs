#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub enum command {
  Add { energy: u64, gold: u64 },
  Query { energy: u64 },
}

impl Clone for command {
  fn clone(&self) -> Self {
    match self {
      command::Add { energy: __field0, gold: __field1 } => command::Add { energy: Clone::clone(__field0), gold: Clone::clone(__field1) },
      command::Query { energy: __field0 } => command::Query { energy: Clone::clone(__field0) },
    }
  }
}

pub type uint = u64;

// Rocq: Kattissquest.kattissquest_implem.nil
pub fn nil() -> u64 {
  9223372036854775807u64
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsr
// Variant: uncurried
pub fn lsr(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsr(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Kattissquest.kattissquest_implem.bdec
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

// Rocq: Kattissquest.kattissquest_implem.scan
// Variant: uncurried
pub fn scan_1(x: Rc<Array<Rc<command>>>, N: u64, j: u64, m: u64, q: u64) -> (u64, u64) {
  scan(x, N, j, m, q, ())
}

// Rocq: Kattissquest.kattissquest_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(x: Rc<Array<Rc<command>>>, N: u64, j: u64, m: u64, q: u64, _H: ()) -> (u64, u64) {
  let tmp = ltb(j, N);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<Rc<command>>(&x, j);
      let (v21, v22) = __rocq_reuse::reset(tmp_1, |__payload| Clone::clone(__payload));
      std::mem::drop(v22);
      match v21 {
        command::Add { energy: v29, gold: _v31 } => {
          let tmp_2 = add(j, 1u64);
          let tmp_3 = if ltb(m, v29) {
            v29
          } else {
            m
          };
          scan(x, N, tmp_2, tmp_3, q, ())
        },
        command::Query { energy: _v71 } => {
          scan(x, N, add(j, 1u64), m, add(q, 1u64), ())
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsl
// Variant: uncurried
pub fn lsl(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsl(v0, v1)
}

// Rocq: Kattissquest.kattissquest_implem.kloop
// Variant: uncurried
pub fn kloop_1(m: u64, k: u64) -> u64 {
  kloop(m, k, ())
}

// Rocq: Kattissquest.kattissquest_implem.kloop (local: kloop)
// Variant: uncurried, lifted
pub fn kloop(m: u64, k: u64, _H: ()) -> u64 {
  let tmp = andb(ltb(k, 62u64), leb(lsl(1u64, k), m));
  match bdec(tmp) {
    sumbool::left => {
      kloop(m, add(k, 1u64), ())
    },
    sumbool::right => {
      k
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Kattissquest.kattissquest_implem.kh
pub fn kh(k: u64) -> u64 {
  let tmp = lsr(k, 1u64);
  sub(k, tmp)
}

// Rocq: Kattissquest.kattissquest_implem.kl
pub fn kl(k: u64) -> u64 {
  lsr(k, 1u64)
}

// Rocq: Kattissquest.kattissquest_implem.stab
// Variant: uncurried
pub fn stab_1(t: Rc<Array<u64>>, K: u64, k: u64) -> Rc<Array<u64>> {
  stab(t, K, k, ())
}

// Rocq: Kattissquest.kattissquest_implem.stab (local: stab)
// Variant: uncurried, lifted
pub fn stab(t: Rc<Array<u64>>, K: u64, k: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, add(K, 1u64));
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = 1u64;
      let s = if leb(k, tmp_1) {
        2u64
      } else {
        let tmp_2 = rocq_array::get::<u64>(&t, kh(k));
        let tmp_3 = add(2u64, tmp_2);
        let tmp_4 = rocq_array::get::<u64>(&t, kl(k));
        add(tmp_3, lsl(tmp_4, kh(k)))
      };
      let tmp_5 = rocq_array::set::<u64>(t, k, s);
      stab(tmp_5, K, add(k, 1u64), ())
    },
    sumbool::right => {
      t
    },
  }
}

// Rocq: Kattissquest.kattissquest_implem.cntloop
// Variant: uncurried
pub fn cntloop_1(x: Rc<Array<Rc<command>>>, N: u64, j: u64, c: Rc<Array<u64>>) -> Rc<Array<u64>> {
  cntloop(x, N, j, c, ())
}

// Rocq: Kattissquest.kattissquest_implem.cntloop (local: cntloop)
// Variant: uncurried, lifted
pub fn cntloop(x: Rc<Array<Rc<command>>>, N: u64, j: u64, c: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(j, N);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<Rc<command>>(&x, j);
      let (v20, v21) = __rocq_reuse::reset(tmp_1, |__payload| Clone::clone(__payload));
      std::mem::drop(v21);
      match v20 {
        command::Add { energy: v28, gold: _v30 } => {
          let tmp_2 = add(j, 1u64);
          let tmp_3 = rocq_array::get::<u64>(&c, v28);
          let tmp_4 = rocq_array::set::<u64>(c, v28, add(tmp_3, 1u64));
          cntloop(x, N, tmp_2, tmp_4, ())
        },
        command::Query { energy: _v75 } => {
          cntloop(x, N, add(j, 1u64), c, ())
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
pub fn pref_1(c: Rc<Array<u64>>, U: u64, e: u64, acc: u64) -> Rc<Array<u64>> {
  pref(c, U, e, acc, ())
}

// Rocq: Kattissquest.kattissquest_implem.pref (local: pref)
// Variant: uncurried, lifted
pub fn pref(c: Rc<Array<u64>>, U: u64, e: u64, acc: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(e, U);
  match bdec(tmp) {
    sumbool::left => {
      let ce = rocq_array::get::<u64>(&c, e);
      let tmp_1 = rocq_array::set::<u64>(c, e, acc);
      pref(tmp_1, U, add(e, 1u64), add(acc, ce), ())
    },
    sumbool::right => {
      c
    },
  }
}

// Rocq: Kattissquest.kattissquest_implem.sup
// Variant: uncurried
pub fn sup_1(gd: Rc<Array<u64>>, s: u64, i: u64) -> Rc<Array<u64>> {
  sup(gd, s, i, ())
}

// Rocq: Kattissquest.kattissquest_implem.sup (local: sup)
// Variant: uncurried, lifted
pub fn sup(gd: Rc<Array<u64>>, s: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(0u64, i);
  match bdec(tmp) {
    sumbool::left => {
      let p = lsr(sub(i, 1u64), 1u64);
      let a = rocq_array::get::<u64>(&gd, add(s, p));
      let b = rocq_array::get::<u64>(&gd, add(s, i));
      if ltb(a, b) {
        let tmp_1 = rocq_array::set::<u64>(gd, add(s, p), b);
        let tmp_2 = rocq_array::set::<u64>(tmp_1, add(s, i), a);
        sup(tmp_2, s, p, ())
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
pub fn hpush(gd: Rc<Array<u64>>, s: u64, n: u64, g: u64) -> Rc<Array<u64>> {
  let tmp = rocq_array::set::<u64>(gd, add(s, n), g);
  sup_1(tmp, s, n)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Kattissquest.kattissquest_implem.clb
// Variant: uncurried
pub fn clb(t: Rc<Array<u64>>, b: u64, k: u64, i: u64) -> u64 {
  let tmp = add(b, 2u64);
  let tmp_1 = rocq_array::get::<u64>(&t, kh(k));
  let tmp_2 = add(tmp, tmp_1);
  let tmp_3 = rocq_array::get::<u64>(&t, kl(k));
  std::mem::drop(t);
  add(tmp_2, mul(i, tmp_3))
}

// Rocq: Kattissquest.kattissquest_implem.vins
// Variant: uncurried
pub fn vins_1(t: Rc<Array<u64>>, v: Rc<Array<u64>>, b: u64, k: u64, x: u64) -> Rc<Array<u64>> {
  vins(t, v, b, k, x, ())
}

// Rocq: Kattissquest.kattissquest_implem.vins (local: vins)
// Variant: uncurried, lifted
pub fn vins(t: Rc<Array<u64>>, v: Rc<Array<u64>>, b: u64, k: u64, x: u64, _H: ()) -> Rc<Array<u64>> {
  let m = rocq_array::get::<u64>(&v, b);
  if eqb(m, __rocq_global_488) {
    std::mem::drop(t);
    let tmp = rocq_array::set::<u64>(v, b, x);
    rocq_array::set::<u64>(tmp, add(b, 1u64), x)
  } else {
    let y = if ltb(x, m) {
      m
    } else {
      x
    };
    let v1 = if ltb(x, m) {
      rocq_array::set::<u64>(v, b, x)
    } else {
      v
    };
    let tmp_1 = ltb(1u64, k);
    let v2 = match bdec(tmp_1) {
      sumbool::left => {
        let hy = lsr(y, kl(k));
        let ly = sub(y, lsl(hy, kl(k)));
        let t_clone = Rc::clone(&t);
        let c = clb(t_clone, b, k, hy);
        let tmp_2 = rocq_array::get::<u64>(&v1, c);
        if eqb(tmp_2, __rocq_global_488) {
          let v3 = vins(t, v1, add(b, 2u64), kh(k), hy, ());
          let tmp_3 = rocq_array::set::<u64>(v3, c, ly);
          rocq_array::set::<u64>(tmp_3, add(c, 1u64), ly)
        } else {
          vins(t, v1, c, kl(k), ly, ())
        }
      },
      sumbool::right => {
        std::mem::drop(t);
        v1
      },
    };
    let tmp_4 = rocq_array::get::<u64>(&v2, add(b, 1u64));
    if ltb(tmp_4, y) {
      rocq_array::set::<u64>(v2, add(b, 1u64), y)
    } else {
      v2
    }
  }
}

// Rocq: Kattissquest.kattissquest_implem.vpred
// Variant: uncurried
pub fn vpred_1(t: Rc<Array<u64>>, v: Rc<Array<u64>>, b: u64, k: u64, x: u64) -> u64 {
  vpred(t, v, b, k, x, ())
}

// Rocq: Kattissquest.kattissquest_implem.vpred (local: vpred)
// Variant: uncurried, lifted
pub fn vpred(t: Rc<Array<u64>>, v: Rc<Array<u64>>, b: u64, k: u64, x: u64, _H: ()) -> u64 {
  let m = rocq_array::get::<u64>(&v, b);
  if ltb(x, m) {
    std::mem::drop(t);
    std::mem::drop(v);
    __rocq_global_488
  } else {
    let M = rocq_array::get::<u64>(&v, add(b, 1u64));
    if leb(M, x) {
      std::mem::drop(t);
      std::mem::drop(v);
      M
    } else {
      let tmp = ltb(1u64, k);
      match bdec(tmp) {
        sumbool::left => {
          let hx = lsr(x, kl(k));
          let lx = sub(x, lsl(hx, kl(k)));
          let t_clone = Rc::clone(&t);
          let c = clb(t_clone, b, k, hx);
          let tmp_1 = rocq_array::get::<u64>(&v, c);
          if leb(tmp_1, lx) {
            add(lsl(hx, kl(k)), vpred(t, v, c, kl(k), lx, ()))
          } else {
            if eqb(hx, 0u64) {
              std::mem::drop(t);
              std::mem::drop(v);
              m
            } else {
              let tmp_2 = add(b, 2u64);
              let tmp_3 = kh(k);
              let tmp_4 = sub(hx, 1u64);
              let t_clone_1 = Rc::clone(&t);
              let v_clone = Rc::clone(&v);
              let ph = vpred(t_clone_1, v_clone, tmp_2, tmp_3, tmp_4, ());
              if eqb(ph, __rocq_global_488) {
                std::mem::drop(t);
                std::mem::drop(v);
                m
              } else {
                let tmp_5 = lsl(ph, kl(k));
                let tmp_6 = rocq_array::get::<u64>(&v, add(clb(t, b, k, ph), 1u64));
                std::mem::drop(v);
                add(tmp_5, tmp_6)
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
pub fn pickc(gd: Rc<Array<u64>>, s: u64, n: u64, i: u64) -> u64 {
  let c1 = add(mul(2u64, i), 1u64);
  let tmp = add(c1, 1u64);
  if ltb(tmp, n) {
    let tmp_1 = rocq_array::get::<u64>(&gd, add(s, c1));
    let tmp_2 = add(c1, 1u64);
    let tmp_3 = rocq_array::get::<u64>(&gd, add(s, tmp_2));
    if ltb(tmp_1, tmp_3) {
      std::mem::drop(gd);
      add(c1, 1u64)
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
pub fn sdown_1(gd: Rc<Array<u64>>, s: u64, n: u64, i: u64) -> Rc<Array<u64>> {
  sdown(gd, s, n, i, ())
}

// Rocq: Kattissquest.kattissquest_implem.sdown (local: sdown)
// Variant: uncurried, lifted
pub fn sdown(gd: Rc<Array<u64>>, s: u64, n: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = mul(2u64, i);
  let tmp_1 = andb(ltb(i, add(tmp, 1u64)), ltb(add(mul(2u64, i), 1u64), n));
  match bdec(tmp_1) {
    sumbool::left => {
      let gd_clone = Rc::clone(&gd);
      let c = pickc(gd_clone, s, n, i);
      let a = rocq_array::get::<u64>(&gd, add(s, i));
      let b = rocq_array::get::<u64>(&gd, add(s, c));
      if ltb(a, b) {
        let tmp_2 = rocq_array::set::<u64>(gd, add(s, i), b);
        let tmp_3 = rocq_array::set::<u64>(tmp_2, add(s, c), a);
        sdown(tmp_3, s, n, c, ())
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
pub fn hpop(gd: Rc<Array<u64>>, s: u64, n: u64) -> Rc<Array<u64>> {
  let last = rocq_array::get::<u64>(&gd, add(s, sub(n, 1u64)));
  let tmp = rocq_array::set::<u64>(gd, s, last);
  sdown_1(tmp, s, sub(n, 1u64), 0u64)
}

// Rocq: Kattissquest.kattissquest_implem.vdel
// Variant: uncurried
pub fn vdel_1(t: Rc<Array<u64>>, v: Rc<Array<u64>>, b: u64, k: u64, x: u64) -> Rc<Array<u64>> {
  vdel(t, v, b, k, x, ())
}

// Rocq: Kattissquest.kattissquest_implem.vdel (local: vdel)
// Variant: uncurried, lifted
pub fn vdel(t: Rc<Array<u64>>, v: Rc<Array<u64>>, b: u64, k: u64, x: u64, _H: ()) -> Rc<Array<u64>> {
  let m = rocq_array::get::<u64>(&v, b);
  let M = rocq_array::get::<u64>(&v, add(b, 1u64));
  if eqb(m, M) {
    std::mem::drop(t);
    let tmp = rocq_array::set::<u64>(v, b, __rocq_global_488);
    rocq_array::set::<u64>(tmp, add(b, 1u64), __rocq_global_488)
  } else {
    let tmp_1 = ltb(1u64, k);
    match bdec(tmp_1) {
      sumbool::left => {
        let y = if eqb(x, m) {
          let f = rocq_array::get::<u64>(&v, add(b, 2u64));
          let tmp_2 = lsl(f, kl(k));
          let t_clone = Rc::clone(&t);
          let tmp_3 = rocq_array::get::<u64>(&v, clb(t_clone, b, k, f));
          add(tmp_2, tmp_3)
        } else {
          x
        };
        let v1 = if eqb(x, m) {
          rocq_array::set::<u64>(v, b, y)
        } else {
          v
        };
        let hy = lsr(y, kl(k));
        let ly = sub(y, lsl(hy, kl(k)));
        let t_clone_1 = Rc::clone(&t);
        let c = clb(t_clone_1, b, k, hy);
        let tmp_4 = kl(k);
        let t_clone_2 = Rc::clone(&t);
        let v2 = vdel(t_clone_2, v1, c, tmp_4, ly, ());
        let tmp_5 = rocq_array::get::<u64>(&v2, c);
        if eqb(tmp_5, __rocq_global_488) {
          let tmp_6 = add(b, 2u64);
          let tmp_7 = kh(k);
          let t_clone_3 = Rc::clone(&t);
          let v3 = vdel(t_clone_3, v2, tmp_6, tmp_7, hy, ());
          let tmp_8 = rocq_array::get::<u64>(&v3, add(b, 1u64));
          if eqb(y, tmp_8) {
            let tmp_9 = add(b, 2u64);
            let sm = rocq_array::get::<u64>(&v3, add(tmp_9, 1u64));
            if eqb(sm, __rocq_global_488) {
              std::mem::drop(t);
              let tmp_10 = add(b, 1u64);
              let tmp_11 = rocq_array::get::<u64>(&v3, b);
              rocq_array::set::<u64>(v3, tmp_10, tmp_11)
            } else {
              let tmp_12 = add(b, 1u64);
              let tmp_13 = lsl(sm, kl(k));
              let tmp_14 = rocq_array::get::<u64>(&v3, add(clb(t, b, k, sm), 1u64));
              rocq_array::set::<u64>(v3, tmp_12, add(tmp_13, tmp_14))
            }
          } else {
            std::mem::drop(t);
            v3
          }
        } else {
          let tmp_15 = rocq_array::get::<u64>(&v2, add(b, 1u64));
          if eqb(y, tmp_15) {
            std::mem::drop(t);
            let tmp_16 = add(b, 1u64);
            let tmp_17 = lsl(hy, kl(k));
            let tmp_18 = rocq_array::get::<u64>(&v2, add(c, 1u64));
            rocq_array::set::<u64>(v2, tmp_16, add(tmp_17, tmp_18))
          } else {
            std::mem::drop(t);
            v2
          }
        }
      },
      sumbool::right => {
        let tmp_19 = 0u64;
        let r = if eqb(x, tmp_19) {
          std::mem::drop(t);
          1u64
        } else {
          std::mem::drop(t);
          0u64
        };
        let tmp_20 = rocq_array::set::<u64>(v, b, r);
        rocq_array::set::<u64>(tmp_20, add(b, 1u64), r)
      },
    }
  }
}

// Rocq: Kattissquest.kattissquest_implem.sess
// Variant: uncurried
pub fn sess_1(t: Rc<Array<u64>>, st: Rc<Array<u64>>, K: u64, U: u64, v: Rc<Array<u64>>, gd: Rc<Array<u64>>, hz: Rc<Array<u64>>, x: u64, acc: u64) -> (((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64) {
  sess(t, st, K, U, v, gd, hz, x, acc, ())
}

// Rocq: Kattissquest.kattissquest_implem.sess (local: sess)
// Variant: uncurried, lifted
pub fn sess(t: Rc<Array<u64>>, st: Rc<Array<u64>>, K: u64, U: u64, v: Rc<Array<u64>>, gd: Rc<Array<u64>>, hz: Rc<Array<u64>>, x: u64, acc: u64, _H: ()) -> (((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64) {
  let x_ = if ltb(x, U) {
    x
  } else {
    sub(U, 1u64)
  };
  let t_clone = Rc::clone(&t);
  let v_clone = Rc::clone(&v);
  let e = vpred_1(t_clone, v_clone, 0u64, K, x_);
  let tmp = andb(ltb(0u64, e), leb(e, x));
  match bdec(tmp) {
    sumbool::left => {
      let s = rocq_array::get::<u64>(&st, e);
      let n = rocq_array::get::<u64>(&hz, e);
      let g = rocq_array::get::<u64>(&gd, s);
      let gd1 = hpop(gd, s, n);
      let hz1 = rocq_array::set::<u64>(hz, e, sub(n, 1u64));
      let tmp_1 = 1u64;
      let v1 = if eqb(n, tmp_1) {
        let t_clone_1 = Rc::clone(&t);
        vdel_1(t_clone_1, v, 0u64, K, e)
      } else {
        v
      };
      sess(t, st, K, U, v1, gd1, hz1, sub(x, e), add(acc, g), ())
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
pub fn mloop_1(x: Rc<Array<Rc<command>>>, t: Rc<Array<u64>>, st: Rc<Array<u64>>, K: u64, U: u64, N: u64, j: u64, v: Rc<Array<u64>>, gd: Rc<Array<u64>>, hz: Rc<Array<u64>>, out: Rc<Array<u64>>, qi: u64) -> Rc<Array<u64>> {
  mloop(x, t, st, K, U, N, j, v, gd, hz, out, qi, ())
}

// Rocq: Kattissquest.kattissquest_implem.mloop (local: mloop)
// Variant: uncurried, lifted
pub fn mloop(x: Rc<Array<Rc<command>>>, t: Rc<Array<u64>>, st: Rc<Array<u64>>, K: u64, U: u64, N: u64, j: u64, v: Rc<Array<u64>>, gd: Rc<Array<u64>>, hz: Rc<Array<u64>>, out: Rc<Array<u64>>, qi: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(j, N);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<Rc<command>>(&x, j);
      match &*tmp_1 {
        command::Add { energy: g, gold: e } => {
          let st_ref = &st;
          let s = rocq_array::get::<u64>(st_ref, Clone::clone(g));
          let hz_ref = &hz;
          let n = rocq_array::get::<u64>(hz_ref, Clone::clone(g));
          let gd1 = hpush(gd, s, n, Clone::clone(e));
          let tmp_2 = add(n, 1u64);
          let hz1 = rocq_array::set::<u64>(hz, Clone::clone(g), tmp_2);
          let tmp_3 = 0u64;
          let v1 = if eqb(n, tmp_3) {
            let tmp_4 = 0u64;
            let t_clone = Rc::clone(&t);
            let g_clone = Clone::clone(g);
            std::mem::drop(tmp_1);
            vins_1(t_clone, v, tmp_4, K, g_clone)
          } else {
            std::mem::drop(tmp_1);
            v
          };
          mloop(x, t, st, K, U, N, add(j, 1u64), v1, gd1, hz1, out, qi, ())
        },
        command::Query { energy: q } => {
          let tmp_5 = 0u64;
          let t_clone_1 = Rc::clone(&t);
          let st_clone = Rc::clone(&st);
          let q_clone = Clone::clone(q);
          std::mem::drop(tmp_1);
          let tmp_6 = sess_1(t_clone_1, st_clone, K, U, v, gd, hz, q_clone, tmp_5);
          match tmp_6 {
            (v163, v165) => {
              match v163 {
                (v168, v170) => {
                  match v168 {
                    (v173, v175) => {
                      let tmp_7 = add(j, 1u64);
                      let tmp_8 = rocq_array::set::<u64>(out, qi, v165);
                      mloop(x, t, st, K, U, N, tmp_7, v173, v175, v170, tmp_8, add(qi, 1u64), ())
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
pub fn kattissquest_impl(x: Rc<Array<Rc<command>>>) -> Rc<Array<u64>> {
  let N = rocq_array::length::<Rc<command>>(&x);
  let x_clone = Rc::clone(&x);
  let tmp = scan_1(x_clone, N, 0u64, 1u64, 0u64);
  match tmp {
    (v23, v25) => {
      let K = kloop_1(v23, 1u64);
      let tmp_1 = rocq_array::make::<u64>(add(K, 1u64), 0u64);
      let t = stab_1(tmp_1, K, 1u64);
      let U = lsl(1u64, K);
      let tmp_2 = rocq_array::make::<u64>(U, 0u64);
      let x_clone_1 = Rc::clone(&x);
      let cnt = cntloop_1(x_clone_1, N, 0u64, tmp_2);
      let st = pref_1(cnt, U, 0u64, 0u64);
      let tmp_3 = rocq_array::get::<u64>(&t, K);
      let tmp_4 = rocq_array::make::<u64>(tmp_3, __rocq_global_488);
      let tmp_5 = rocq_array::make::<u64>(N, 0u64);
      let tmp_6 = rocq_array::make::<u64>(U, 0u64);
      let tmp_7 = rocq_array::make::<u64>(v25, 0u64);
      mloop_1(x, t, st, K, U, N, 0u64, tmp_4, tmp_5, tmp_6, tmp_7, 0u64)
    },
  }
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
const __rocq_global_488: u64 = 9223372036854775807u64;