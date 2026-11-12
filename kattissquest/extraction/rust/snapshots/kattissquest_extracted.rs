// Generated from OwnedANF. This printer is not verified.
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

// Rocq: Kattissquest.kattissquest_implem.kattissquest
pub fn kattissquest() -> Rc<dyn Fn(Rc<Array<Rc<command>>>) -> Rc<Array<u64>>> {
  let v0: fn(Rc<Array<Rc<command>>>) -> Rc<Array<u64>> = kattissquest_impl;
  let v1: Rc<dyn Fn(Rc<Array<Rc<command>>>) -> Rc<Array<u64>>> = Rc::new(v0);
  v1
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

// Rocq: Kattissquest.kattissquest_implem.scan
// Variant: uncurried
pub fn scan_1(x: Rc<Array<Rc<command>>>, N: u64, j: u64, m: u64, q: u64) -> (u64, u64) {
  scan(x, N, j, m, q, ())
}

// Rocq: Kattissquest.kattissquest_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(x: Rc<Array<Rc<command>>>, N: u64, j: u64, m: u64, q: u64, _H: ()) -> (u64, u64) {
  let v13 = ltb(j, N);
  match bdec(v13) {
    sumbool::left => {
      let v17 = &x;
      let v20 = rocq_array::get::<Rc<command>>(&v17, j);
      let (v21, v22) = __rocq_reuse::reset(v20, |__payload| Clone::clone(__payload));
      std::mem::drop(v22);
      match v21 {
        command::Add { energy: v29, gold: _v31 } => {
          let v40 = add(j, 1u64);
          let v47 = match ltb(m, v29) {
            true => {
              v29
            },
            false => {
              m
            },
          };
          scan(x, N, v40, v47, q, ())
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
  match b1 {
    true => {
      b2
    },
    false => {
      false
    },
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
  let v32 = andb(ltb(k, 62u64), leb(lsl(1u64, k), m));
  match bdec(v32) {
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
  let v9 = lsr(k, 1u64);
  sub(k, v9)
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
  let v19 = ltb(k, add(K, 1u64));
  match bdec(v19) {
    sumbool::left => {
      let v25 = 1u64;
      let s = match leb(k, v25) {
        true => {
          2u64
        },
        false => {
          let v43 = kh(k);
          let v44 = &t;
          let v47 = rocq_array::get::<u64>(&v44, v43);
          let v52 = add(2u64, v47);
          let v57 = kl(k);
          let v58 = &t;
          let v61 = rocq_array::get::<u64>(&v58, v57);
          add(v52, lsl(v61, kh(k)))
        },
      };
      let v85 = rocq_array::set::<u64>(t, k, s);
      stab(v85, K, add(k, 1u64), ())
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
  let v12 = ltb(j, N);
  match bdec(v12) {
    sumbool::left => {
      let v16 = &x;
      let v19 = rocq_array::get::<Rc<command>>(&v16, j);
      let (v20, v21) = __rocq_reuse::reset(v19, |__payload| Clone::clone(__payload));
      std::mem::drop(v21);
      match v20 {
        command::Add { energy: v28, gold: _v30 } => {
          let v39 = add(j, 1u64);
          let v41 = &c;
          let v44 = rocq_array::get::<u64>(&v41, v28);
          let v58 = rocq_array::set::<u64>(c, v28, add(v44, 1u64));
          cntloop(x, N, v39, v58, ())
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
  let v12 = ltb(e, U);
  match bdec(v12) {
    sumbool::left => {
      let v16 = &c;
      let ce = rocq_array::get::<u64>(&v16, e);
      let v26 = rocq_array::set::<u64>(c, e, acc);
      pref(v26, U, add(e, 1u64), add(acc, ce), ())
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
  let v13 = ltb(0u64, i);
  match bdec(v13) {
    sumbool::left => {
      let p = lsr(sub(i, 1u64), 1u64);
      let v38 = add(s, p);
      let v39 = &gd;
      let a = rocq_array::get::<u64>(&v39, v38);
      let v48 = add(s, i);
      let v49 = &gd;
      let b = rocq_array::get::<u64>(&v49, v48);
      match ltb(a, b) {
        true => {
          let v72 = rocq_array::set::<u64>(gd, add(s, p), b);
          let v85 = rocq_array::set::<u64>(v72, add(s, i), a);
          sup(v85, s, p, ())
        },
        false => {
          gd
        },
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
  let v18 = rocq_array::set::<u64>(gd, add(s, n), g);
  sup_1(v18, s, n)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Kattissquest.kattissquest_implem.clb
// Variant: uncurried
pub fn clb(t: Rc<Array<u64>>, b: u64, k: u64, i: u64) -> u64 {
  let v13 = add(b, 2u64);
  let v17 = kh(k);
  let v18 = &t;
  let v21 = rocq_array::get::<u64>(&v18, v17);
  let v26 = add(v13, v21);
  let v31 = kl(k);
  let v32 = &t;
  let v35 = rocq_array::get::<u64>(&v32, v31);
  std::mem::drop(t);
  add(v26, mul(i, v35))
}

// Rocq: Kattissquest.kattissquest_implem.vins
// Variant: uncurried
pub fn vins_1(t: Rc<Array<u64>>, v: Rc<Array<u64>>, b: u64, k: u64, x: u64) -> Rc<Array<u64>> {
  vins(t, v, b, k, x, ())
}

// Rocq: Kattissquest.kattissquest_implem.vins (local: vins)
// Variant: uncurried, lifted
pub fn vins(t: Rc<Array<u64>>, v: Rc<Array<u64>>, b: u64, k: u64, x: u64, _H: ()) -> Rc<Array<u64>> {
  let v6 = &v;
  let m = rocq_array::get::<u64>(&v6, b);
  match eqb(m, __rocq_global_488) {
    true => {
      std::mem::drop(t);
      let v24 = rocq_array::set::<u64>(v, b, x);
      rocq_array::set::<u64>(v24, add(b, 1u64), x)
    },
    false => {
      let y = match ltb(x, m) {
        true => {
          m
        },
        false => {
          x
        },
      };
      let v1 = match ltb(x, m) {
        true => {
          rocq_array::set::<u64>(v, b, x)
        },
        false => {
          v
        },
      };
      let v82 = ltb(1u64, k);
      let v2 = match bdec(v82) {
        sumbool::left => {
          let hy = lsr(y, kl(k));
          let ly = sub(y, lsl(hy, kl(k)));
          let v115 = Rc::clone(&t);
          let c = clb(v115, b, k, hy);
          let v124 = &v1;
          let v127 = rocq_array::get::<u64>(&v124, c);
          match eqb(v127, __rocq_global_488) {
            true => {
              let v3 = vins(t, v1, add(b, 2u64), kh(k), hy, ());
              let v169 = rocq_array::set::<u64>(v3, c, ly);
              rocq_array::set::<u64>(v169, add(c, 1u64), ly)
            },
            false => {
              vins(t, v1, c, kl(k), ly, ())
            },
          }
        },
        sumbool::right => {
          std::mem::drop(t);
          v1
        },
      };
      let v223 = add(b, 1u64);
      let v224 = &v2;
      let v228 = rocq_array::get::<u64>(&v224, v223);
      match ltb(v228, y) {
        true => {
          rocq_array::set::<u64>(v2, add(b, 1u64), y)
        },
        false => {
          v2
        },
      }
    },
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
  let v6 = &v;
  let m = rocq_array::get::<u64>(&v6, b);
  match ltb(x, m) {
    true => {
      std::mem::drop(t);
      std::mem::drop(v);
      __rocq_global_488
    },
    false => {
      let v27 = add(b, 1u64);
      let v28 = &v;
      let M = rocq_array::get::<u64>(&v28, v27);
      match leb(M, x) {
        true => {
          std::mem::drop(t);
          std::mem::drop(v);
          M
        },
        false => {
          let v50 = ltb(1u64, k);
          match bdec(v50) {
            sumbool::left => {
              let hx = lsr(x, kl(k));
              let lx = sub(x, lsl(hx, kl(k)));
              let v83 = Rc::clone(&t);
              let c = clb(v83, b, k, hx);
              let v92 = &v;
              let v96 = rocq_array::get::<u64>(&v92, c);
              match leb(v96, lx) {
                true => {
                  add(lsl(hx, kl(k)), vpred(t, v, c, kl(k), lx, ()))
                },
                false => {
                  match eqb(hx, 0u64) {
                    true => {
                      std::mem::drop(t);
                      std::mem::drop(v);
                      m
                    },
                    false => {
                      let v158 = add(b, 2u64);
                      let v162 = kh(k);
                      let v170 = sub(hx, 1u64);
                      let v176 = Rc::clone(&t);
                      let v179 = Rc::clone(&v);
                      let ph = vpred(v176, v179, v158, v162, v170, ());
                      match eqb(ph, __rocq_global_488) {
                        true => {
                          std::mem::drop(t);
                          std::mem::drop(v);
                          m
                        },
                        false => {
                          let v209 = lsl(ph, kl(k));
                          let v227 = add(clb(t, b, k, ph), 1u64);
                          let v228 = &v;
                          let v231 = rocq_array::get::<u64>(&v228, v227);
                          std::mem::drop(v);
                          add(v209, v231)
                        },
                      }
                    },
                  }
                },
              }
            },
            sumbool::right => {
              std::mem::drop(t);
              std::mem::drop(v);
              m
            },
          }
        },
      }
    },
  }
}

// Rocq: Kattissquest.kattissquest_implem.pickc
// Variant: uncurried
pub fn pickc(gd: Rc<Array<u64>>, s: u64, n: u64, i: u64) -> u64 {
  let c1 = add(mul(2u64, i), 1u64);
  let v29 = add(c1, 1u64);
  match ltb(v29, n) {
    true => {
      let v41 = add(s, c1);
      let v42 = &gd;
      let v45 = rocq_array::get::<u64>(&v42, v41);
      let v54 = add(c1, 1u64);
      let v59 = add(s, v54);
      let v60 = &gd;
      let v63 = rocq_array::get::<u64>(&v60, v59);
      match ltb(v45, v63) {
        true => {
          std::mem::drop(gd);
          add(c1, 1u64)
        },
        false => {
          std::mem::drop(gd);
          c1
        },
      }
    },
    false => {
      std::mem::drop(gd);
      c1
    },
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
  let v16 = mul(2u64, i);
  let v56 = andb(ltb(i, add(v16, 1u64)), ltb(add(mul(2u64, i), 1u64), n));
  match bdec(v56) {
    sumbool::left => {
      let v63 = Rc::clone(&gd);
      let c = pickc(v63, s, n, i);
      let v76 = add(s, i);
      let v77 = &gd;
      let a = rocq_array::get::<u64>(&v77, v76);
      let v86 = add(s, c);
      let v87 = &gd;
      let b = rocq_array::get::<u64>(&v87, v86);
      match ltb(a, b) {
        true => {
          let v110 = rocq_array::set::<u64>(gd, add(s, i), b);
          let v123 = rocq_array::set::<u64>(v110, add(s, c), a);
          sdown(v123, s, n, c, ())
        },
        false => {
          gd
        },
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
  let v16 = add(s, sub(n, 1u64));
  let v17 = &gd;
  let last = rocq_array::get::<u64>(&v17, v16);
  let v28 = rocq_array::set::<u64>(gd, s, last);
  sdown_1(v28, s, sub(n, 1u64), 0u64)
}

// Rocq: Kattissquest.kattissquest_implem.vdel
// Variant: uncurried
pub fn vdel_1(t: Rc<Array<u64>>, v: Rc<Array<u64>>, b: u64, k: u64, x: u64) -> Rc<Array<u64>> {
  vdel(t, v, b, k, x, ())
}

// Rocq: Kattissquest.kattissquest_implem.vdel (local: vdel)
// Variant: uncurried, lifted
pub fn vdel(t: Rc<Array<u64>>, v: Rc<Array<u64>>, b: u64, k: u64, x: u64, _H: ()) -> Rc<Array<u64>> {
  let v6 = &v;
  let m = rocq_array::get::<u64>(&v6, b);
  let v17 = add(b, 1u64);
  let v18 = &v;
  let M = rocq_array::get::<u64>(&v18, v17);
  match eqb(m, M) {
    true => {
      std::mem::drop(t);
      let v36 = rocq_array::set::<u64>(v, b, __rocq_global_488);
      rocq_array::set::<u64>(v36, add(b, 1u64), __rocq_global_488)
    },
    false => {
      let v64 = ltb(1u64, k);
      match bdec(v64) {
        sumbool::left => {
          let y = match eqb(x, m) {
            true => {
              let v82 = add(b, 2u64);
              let v83 = &v;
              let f = rocq_array::get::<u64>(&v83, v82);
              let v97 = lsl(f, kl(k));
              let v101 = Rc::clone(&t);
              let v108 = clb(v101, b, k, f);
              let v109 = &v;
              let v112 = rocq_array::get::<u64>(&v109, v108);
              add(v97, v112)
            },
            false => {
              x
            },
          };
          let v1 = match eqb(x, m) {
            true => {
              rocq_array::set::<u64>(v, b, y)
            },
            false => {
              v
            },
          };
          let hy = lsr(y, kl(k));
          let ly = sub(y, lsl(hy, kl(k)));
          let v171 = Rc::clone(&t);
          let c = clb(v171, b, k, hy);
          let v182 = kl(k);
          let v188 = Rc::clone(&t);
          let v2 = vdel(v188, v1, c, v182, ly, ());
          let v201 = &v2;
          let v204 = rocq_array::get::<u64>(&v201, c);
          match eqb(v204, __rocq_global_488) {
            true => {
              let v219 = add(b, 2u64);
              let v223 = kh(k);
              let v229 = Rc::clone(&t);
              let v3 = vdel(v229, v2, v219, v223, hy, ());
              let v249 = add(b, 1u64);
              let v250 = &v3;
              let v253 = rocq_array::get::<u64>(&v250, v249);
              match eqb(y, v253) {
                true => {
                  let v268 = add(b, 2u64);
                  let v275 = add(v268, 1u64);
                  let v276 = &v3;
                  let sm = rocq_array::get::<u64>(&v276, v275);
                  match eqb(sm, __rocq_global_488) {
                    true => {
                      std::mem::drop(t);
                      let v295 = add(b, 1u64);
                      let v296 = &v3;
                      let v299 = rocq_array::get::<u64>(&v296, b);
                      rocq_array::set::<u64>(v3, v295, v299)
                    },
                    false => {
                      let v316 = add(b, 1u64);
                      let v327 = lsl(sm, kl(k));
                      let v345 = add(clb(t, b, k, sm), 1u64);
                      let v346 = &v3;
                      let v349 = rocq_array::get::<u64>(&v346, v345);
                      rocq_array::set::<u64>(v3, v316, add(v327, v349))
                    },
                  }
                },
                false => {
                  std::mem::drop(t);
                  v3
                },
              }
            },
            false => {
              let v380 = add(b, 1u64);
              let v381 = &v2;
              let v384 = rocq_array::get::<u64>(&v381, v380);
              match eqb(y, v384) {
                true => {
                  std::mem::drop(t);
                  let v398 = add(b, 1u64);
                  let v409 = lsl(hy, kl(k));
                  let v417 = add(c, 1u64);
                  let v418 = &v2;
                  let v421 = rocq_array::get::<u64>(&v418, v417);
                  rocq_array::set::<u64>(v2, v398, add(v409, v421))
                },
                false => {
                  std::mem::drop(t);
                  v2
                },
              }
            },
          }
        },
        sumbool::right => {
          let v446 = 0u64;
          let r = match eqb(x, v446) {
            true => {
              std::mem::drop(t);
              1u64
            },
            false => {
              std::mem::drop(t);
              0u64
            },
          };
          let v468 = rocq_array::set::<u64>(v, b, r);
          rocq_array::set::<u64>(v468, add(b, 1u64), r)
        },
      }
    },
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
  let x_ = match ltb(x, U) {
    true => {
      x
    },
    false => {
      sub(U, 1u64)
    },
  };
  let v35 = Rc::clone(&t);
  let v38 = Rc::clone(&v);
  let e = vpred_1(v35, v38, 0u64, K, x_);
  let v67 = andb(ltb(0u64, e), leb(e, x));
  match bdec(v67) {
    sumbool::left => {
      let v71 = &st;
      let s = rocq_array::get::<u64>(&v71, e);
      let v75 = &hz;
      let n = rocq_array::get::<u64>(&v75, e);
      let v79 = &gd;
      let g = rocq_array::get::<u64>(&v79, s);
      let gd1 = hpop(gd, s, n);
      let hz1 = rocq_array::set::<u64>(hz, e, sub(n, 1u64));
      let v108 = 1u64;
      let v1 = match eqb(n, v108) {
        true => {
          let v120 = Rc::clone(&t);
          vdel_1(v120, v, 0u64, K, e)
        },
        false => {
          v
        },
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
  let v20 = ltb(j, N);
  match bdec(v20) {
    sumbool::left => {
      let v24 = &x;
      let v27 = rocq_array::get::<Rc<command>>(&v24, j);
      match &*v27 {
        command::Add { energy: g, gold: e } => {
          let v34 = &st;
          let v36 = Clone::clone(g);
          let s = rocq_array::get::<u64>(&v34, v36);
          let v38 = &hz;
          let v40 = Clone::clone(g);
          let n = rocq_array::get::<u64>(&v38, v40);
          let gd1 = hpush(gd, s, n, Clone::clone(e));
          let v59 = add(n, 1u64);
          let hz1 = rocq_array::set::<u64>(hz, Clone::clone(g), v59);
          let v69 = 0u64;
          let v1 = match eqb(n, v69) {
            true => {
              let v78 = 0u64;
              let v81 = Rc::clone(&t);
              let v88 = Clone::clone(g);
              std::mem::drop(v27);
              vins_1(v81, v, v78, K, v88)
            },
            false => {
              std::mem::drop(v27);
              v
            },
          };
          mloop(x, t, st, K, U, N, add(j, 1u64), v1, gd1, hz1, out, qi, ())
        },
        command::Query { energy: q } => {
          let v140 = 0u64;
          let v143 = Rc::clone(&t);
          let v146 = Rc::clone(&st);
          let v157 = Clone::clone(q);
          std::mem::drop(v27);
          let v161 = sess_1(v143, v146, K, U, v, gd, hz, v157, v140);
          match v161 {
            (v163, v165) => {
              match v163 {
                (v168, v170) => {
                  match v168 {
                    (v173, v175) => {
                      let v184 = add(j, 1u64);
                      let v191 = rocq_array::set::<u64>(out, qi, v165);
                      mloop(x, t, st, K, U, N, v184, v173, v175, v170, v191, add(qi, 1u64), ())
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
  let v1 = &x;
  let N = rocq_array::length::<Rc<command>>(&v1);
  let v12 = Rc::clone(&x);
  let v21 = scan_1(v12, N, 0u64, 1u64, 0u64);
  match v21 {
    (v23, v25) => {
      let K = kloop_1(v23, 1u64);
      let v50 = rocq_array::make::<u64>(add(K, 1u64), 0u64);
      let t = stab_1(v50, K, 1u64);
      let U = lsl(1u64, K);
      let v77 = rocq_array::make::<u64>(U, 0u64);
      let v80 = Rc::clone(&x);
      let cnt = cntloop_1(v80, N, 0u64, v77);
      let st = pref_1(cnt, U, 0u64, 0u64);
      let v105 = &t;
      let v108 = rocq_array::get::<u64>(&v105, K);
      let v114 = rocq_array::make::<u64>(v108, __rocq_global_488);
      let v121 = rocq_array::make::<u64>(N, 0u64);
      let v128 = rocq_array::make::<u64>(U, 0u64);
      let v135 = rocq_array::make::<u64>(v25, 0u64);
      mloop_1(x, t, st, K, U, N, 0u64, v114, v121, v128, v135, 0u64)
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

pub fn run() -> Rc<dyn Fn(Rc<Array<Rc<command>>>) -> Rc<Array<u64>>> {
  let v0: Rc<dyn Fn(Rc<Array<Rc<command>>>) -> Rc<Array<u64>>> = __rocq_global_1365.with(Clone::clone);
  v0
}
const __rocq_global_488: u64 = 9223372036854775807u64;
std::thread_local! { static __rocq_global_1365: Rc<dyn Fn(Rc<Array<Rc<command>>>) -> Rc<Array<u64>>> = kattissquest(); }