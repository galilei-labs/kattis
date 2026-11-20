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

pub type uint = Int63;

// Rocq: Indoorienteering.indoorienteering_implem.hmul
pub fn hmul() -> Int63 {
  int63!(7046029254386353131)
}

// Rocq: Indoorienteering.indoorienteering_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Indoorienteering.indoorienteering_implem.fill
// Variant: uncurried
pub fn fill_1(x: Array<Array<Int63>>, n: Int63, N: Int63, i: Int63, D: Array<Int63>) -> Array<Int63> {
  fill(x, n, N, i, D, ())
}

// Rocq: Indoorienteering.indoorienteering_implem.fill (local: fill)
// Variant: uncurried, lifted
pub fn fill(x: Array<Array<Int63>>, n: Int63, N: Int63, i: Int63, D: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < N;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = i / n;
      let x_clone = Clone::clone(&x);
      let tmp_3 = &x_clone;
      let tmp_4 = tmp_3.get_cloned(tmp_2);
      std::mem::drop(x_clone);
      let tmp_5 = tmp_4.get_cloned(i % n);
      std::mem::drop(tmp_4);
      fill(x, n, N, tmp_1, D.set(i, tmp_5), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      D
    },
  }
}

// Rocq: Indoorienteering.indoorienteering_implem.logcap
pub fn logcap(n: Int63) -> Int63 {
  if n <= int63!(8) {
    int63!(7)
  } else {
    if n == int63!(9) {
      int63!(9)
    } else {
      if n == int63!(10) {
        int63!(11)
      } else {
        if n == int63!(11) {
          int63!(13)
        } else {
          if n == int63!(12) {
            int63!(15)
          } else {
            if n == int63!(13) {
              int63!(17)
            } else {
              int63!(20)
            }
          }
        }
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

// Rocq: Indoorienteering.indoorienteering_implem.find
// Variant: uncurried
pub fn find_1(t: Array<Int63>, k: Int63, i: Int63) -> Int63 {
  find(t, k, i, ())
}

// Rocq: Indoorienteering.indoorienteering_implem.find (local: find)
// Variant: uncurried, lifted
pub fn find(t: Array<Int63>, k: Int63, i: Int63, _H: ()) -> Int63 {
  let tmp = t.length();
  let tmp_1 = i < tmp;
  match bdec(tmp_1) {
    sumbool::left => {
      let x = t.get_cloned(i);
      let tmp_2 = x == int63!(0);
      let tmp_3 = x == k;
      if orb(tmp_2, tmp_3) {
        std::mem::drop(t);
        i
      } else {
        find(t, k, i + int63!(1), ())
      }
    },
    sumbool::right => {
      std::mem::drop(t);
      i
    },
  }
}

// Rocq: Indoorienteering.indoorienteering_implem.hidx
// Variant: uncurried
pub fn hidx(sh: Int63, k: Int63) -> Int63 {
  k * __rocq_global_342 >> sh
}

// Rocq: Indoorienteering.indoorienteering_implem.find0
// Variant: uncurried
pub fn find0(sh: Int63, t: Array<Int63>, k: Int63) -> Int63 {
  let tmp = hidx(sh, k);
  find_1(t, k, tmp)
}

// Rocq: Indoorienteering.indoorienteering_implem.insert
// Variant: uncurried
pub fn insert(sh: Int63, t: Array<Int63>, k: Int63) -> (Array<Int63>, bool) {
  let t_clone = Clone::clone(&t);
  let j = find0(sh, t_clone, k);
  let tmp = t.length();
  if j < tmp {
    let tmp_1 = t.get_cloned(j);
    if tmp_1 == int63!(0) {
      (t.set(j, k), true)
    } else {
      (t, true)
    }
  } else {
    (t, false)
  }
}

// Rocq: Indoorienteering.indoorienteering_implem.lookup
// Variant: uncurried
pub fn lookup(sh: Int63, t: Array<Int63>, k: Int63) -> bool {
  let t_clone = Clone::clone(&t);
  let j = find0(sh, t_clone, k);
  let tmp = t.length();
  let tmp_1 = j < tmp;
  let tmp_2 = t.get_cloned(j);
  std::mem::drop(t);
  andb(tmp_1, tmp_2 == k)
}

// Rocq: Indoorienteering.indoorienteering_implem.key
// Variant: uncurried
pub fn key(S: Int63, l: Int63) -> Int63 {
  (S << int63!(50)) + l + int63!(1)
}

// Rocq: Indoorienteering.indoorienteering_implem.pdfs
// Variant: uncurried
pub fn pdfs_1(D: Array<Int63>, n: Int63, L: Int63, a_1: Int63, base2: Int63, sh: Int63, t: Array<Int63>, c: Int63, free: Int63, len: Int63, r: Int63, v: Int63) -> bool {
  pdfs(n, a_1, D, L, base2, sh, t, c, free, len, r, v, ())
}

// Rocq: Indoorienteering.indoorienteering_implem.pdfs (local: pdfs)
// Variant: uncurried, lifted
pub fn pdfs(n: Int63, a_1: Int63, D: Array<Int63>, L: Int63, base2: Int63, sh: Int63, t: Array<Int63>, c: Int63, free: Int63, len: Int63, r: Int63, v: Int63, _H: ()) -> bool {
  let tmp = r == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = D.get_cloned(c * n + a_1);
      let l = len + tmp_1;
      if l <= L {
        std::mem::drop(D);
        lookup(sh, t, key(base2 ^ free, L - l))
      } else {
        std::mem::drop(t);
        std::mem::drop(D);
        false
      }
    },
    sumbool::right => {
      let tmp_2 = v < n;
      match bdec(tmp_2) {
        sumbool::left => {
          let bv = int63!(1) << v;
          let tmp_3 = free & bv;
          if tmp_3 == int63!(0) {
            pdfs(n, a_1, D, L, base2, sh, t, c, free, len, r, v + int63!(1), ())
          } else {
            let tmp_4 = D.get_cloned(c * n + v);
            let l = len + tmp_4;
            if l <= L {
              let tmp_5 = free ^ bv;
              let tmp_6 = r - int63!(1);
              let D_clone = Clone::clone(&D);
              let t_clone = Clone::clone(&t);
              if pdfs(n, a_1, D_clone, L, base2, sh, t_clone, v, tmp_5, l, tmp_6, int63!(0), ()) {
                std::mem::drop(t);
                std::mem::drop(D);
                true
              } else {
                pdfs(n, a_1, D, L, base2, sh, t, c, free, len, r, v + int63!(1), ())
              }
            } else {
              pdfs(n, a_1, D, L, base2, sh, t, c, free, len, r, v + int63!(1), ())
            }
          }
        },
        sumbool::right => {
          std::mem::drop(D);
          std::mem::drop(t);
          false
        },
      }
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Indoorienteering.indoorienteering_implem.leafins
// Variant: uncurried
pub fn leafins(D: Array<Int63>, n: Int63, L: Int63, a_1: Int63, m: Int63, fr2: Int63, base2: Int63, k2: Int63, sh: Int63, size: Int63, t: Array<Int63>, k: Int63) -> (Array<Int63>, bool) {
  let tmp = insert(sh, t, k);
  match tmp {
    (v21, v23) => {
      let b_1 = &v21;
      if v23 {
        std::mem::drop(D);
        (v21, false)
      } else {
        let b_clone = Clone::clone(b_1);
        if pdfs_1(D, n, L, a_1, base2, sh, b_clone, m, fr2, int63!(0), k2, int63!(0)) {
          (v21, true)
        } else {
          std::mem::drop(v21);
          (fst::<Array<Int63>, bool>(insert(sh, Array::<Int63>::make(size, int63!(0)), k)), false)
        }
      }
    },
  }
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b_1: bool) -> bool {
  if b_1 {
    false
  } else {
    true
  }
}

// Rocq: Indoorienteering.indoorienteering_implem.idfs
// Variant: uncurried
pub fn idfs_1(D: Array<Int63>, n: Int63, L: Int63, a_1: Int63, m: Int63, fp: Int63, need: Int63, fr2: Int63, base2: Int63, k2: Int63, sh: Int63, size: Int63, t: Array<Int63>, c: Int63, free: Int63, len: Int63, r: Int63, v: Int63) -> (Array<Int63>, bool) {
  idfs(n, m, D, L, fp, a_1, fr2, base2, k2, sh, size, need, t, c, free, len, r, v, ())
}

// Rocq: Indoorienteering.indoorienteering_implem.idfs (local: idfs)
// Variant: uncurried, lifted
pub fn idfs(n: Int63, m: Int63, D: Array<Int63>, L: Int63, fp: Int63, a_1: Int63, fr2: Int63, base2: Int63, k2: Int63, sh: Int63, size: Int63, need: Int63, t: Array<Int63>, c: Int63, free: Int63, len: Int63, r: Int63, v: Int63, _H: ()) -> (Array<Int63>, bool) {
  let tmp = r == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = D.get_cloned(c * n + m);
      let l = len + tmp_1;
      if l <= L {
        leafins(D, n, L, a_1, m, fr2, base2, k2, sh, size, t, key(fp ^ free, l))
      } else {
        std::mem::drop(D);
        (t, false)
      }
    },
    sumbool::right => {
      let tmp_2 = v < n;
      match bdec(tmp_2) {
        sumbool::left => {
          let bv = int63!(1) << v;
          let tmp_3 = free & bv;
          if tmp_3 == int63!(0) {
            idfs(n, m, D, L, fp, a_1, fr2, base2, k2, sh, size, need, t, c, free, len, r, v + int63!(1), ())
          } else {
            let tmp_4 = r == int63!(1);
            let tmp_5 = negb(need & (free ^ bv) == int63!(0));
            if andb(tmp_4, tmp_5) {
              idfs(n, m, D, L, fp, a_1, fr2, base2, k2, sh, size, need, t, c, free, len, r, v + int63!(1), ())
            } else {
              let tmp_6 = D.get_cloned(c * n + v);
              let l = len + tmp_6;
              if l <= L {
                let tmp_7 = free ^ bv;
                let tmp_8 = r - int63!(1);
                let D_clone = Clone::clone(&D);
                let tmp_9 = idfs(n, m, D_clone, L, fp, a_1, fr2, base2, k2, sh, size, need, t, v, tmp_7, l, tmp_8, int63!(0), ());
                match tmp_9 {
                  (v380, v382) => {
                    if v382 {
                      std::mem::drop(D);
                      (v380, true)
                    } else {
                      idfs(n, m, D, L, fp, a_1, fr2, base2, k2, sh, size, need, v380, c, free, len, r, v + int63!(1), ())
                    }
                  },
                }
              } else {
                idfs(n, m, D, L, fp, a_1, fr2, base2, k2, sh, size, need, t, c, free, len, r, v + int63!(1), ())
              }
            }
          }
        },
        sumbool::right => {
          std::mem::drop(D);
          (t, false)
        },
      }
    },
  }
}

// Rocq: Indoorienteering.indoorienteering_implem.search_m
// Variant: uncurried
pub fn search_m(D: Array<Int63>, n: Int63, L: Int63, a_1: Int63, k1: Int63, k2: Int63, sh: Int63, size: Int63, m: Int63) -> bool {
  let fp = (int63!(1) << a_1) - int63!(1) ^ int63!(1) << m;
  let tmp = n & int63!(1) == int63!(0);
  let tmp_1 = int63!(4) <= n;
  let need = if andb(tmp, tmp_1) {
    let tmp_2 = int63!(1);
    let tmp_3 = int63!(0);
    let tmp_4 = if m == tmp_3 {
      int63!(1)
    } else {
      int63!(0)
    };
    tmp_2 << tmp_4
  } else {
    int63!(0)
  };
  let fr2 = fp ^ need;
  let tmp_5 = Array::<Int63>::make(size, int63!(0));
  let D_clone = Clone::clone(&D);
  let tmp_6 = idfs_1(D_clone, n, L, a_1, m, fp, need, fr2, need, k2, sh, size, tmp_5, a_1, fp, int63!(0), k1, int63!(0));
  match tmp_6 {
    (v160, v162) => {
      if v162 {
        std::mem::drop(D);
        std::mem::drop(v160);
        true
      } else {
        pdfs_1(D, n, L, a_1, need, sh, v160, m, fr2, int63!(0), k2, int63!(0))
      }
    },
  }
}

// Rocq: Indoorienteering.indoorienteering_implem.mloop
// Variant: uncurried
pub fn mloop_1(D: Array<Int63>, n: Int63, L: Int63, a_1: Int63, k1: Int63, k2: Int63, sh: Int63, size: Int63, m: Int63) -> bool {
  mloop(D, n, L, a_1, k1, k2, sh, size, m, ())
}

// Rocq: Indoorienteering.indoorienteering_implem.mloop (local: mloop)
// Variant: uncurried, lifted
pub fn mloop(D: Array<Int63>, n: Int63, L: Int63, a_1: Int63, k1: Int63, k2: Int63, sh: Int63, size: Int63, m: Int63, _H: ()) -> bool {
  let tmp = m < a_1;
  match bdec(tmp) {
    sumbool::left => {
      let D_clone = Clone::clone(&D);
      if search_m(D_clone, n, L, a_1, k1, k2, sh, size, m) {
        std::mem::drop(D);
        true
      } else {
        mloop(D, n, L, a_1, k1, k2, sh, size, m + int63!(1), ())
      }
    },
    sumbool::right => {
      std::mem::drop(D);
      false
    },
  }
}

// Rocq: Indoorienteering.indoorienteering_implem.indoor
// Variant: uncurried
pub fn indoor(x: Array<Array<Int63>>, L: Int63) -> bool {
  let n = x.length();
  let N = n * n;
  let tmp = Array::<Int63>::make(N, int63!(0));
  let D = fill_1(x, n, N, int63!(0), tmp);
  let a_1 = n - int63!(1);
  let k1 = (n - int63!(2)) / int63!(2);
  let k2 = n - int63!(2) - k1;
  let b_1 = logcap(n);
  mloop_1(D, n, L, a_1, k1, k2, int63!(63) - b_1, (int63!(1) << b_1) + int63!(256), int63!(0))
}
const __rocq_global_342: Int63 = int63!(7046029254386353131);