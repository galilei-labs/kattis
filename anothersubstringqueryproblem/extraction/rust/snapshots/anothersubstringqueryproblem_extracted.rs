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

pub type uint = Int63;

pub type char63 = Int63;

pub type sint = Int63;

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: rocq_string::RocqString) -> Int63 {
  let tmp = v0.length();
  std::mem::drop(v0);
  tmp
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
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

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.midp
// Variant: uncurried
pub fn midp(lo: Int63, hi: Int63) -> Int63 {
  let tmp = hi - lo;
  lo + tmp / int63!(2)
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.copy
// Variant: uncurried
pub fn copy_1(a_1: Array<Int63>, b_1: Array<Int63>, hi: Int63, k: Int63) -> Array<Int63> {
  copy(a_1, b_1, hi, k, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.copy (local: copy)
// Variant: uncurried, lifted
pub fn copy(a_1: Array<Int63>, b_1: Array<Int63>, hi: Int63, k: Int63, _H: ()) -> Array<Int63> {
  let tmp = k < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = a_1.get_cloned(k);
      copy(a_1, b_1.set(k, tmp_1), hi, k + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(a_1);
      b_1
    },
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

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.merge
// Variant: uncurried
pub fn merge_1(le: Rc<dyn Fn(Int63, Int63) -> bool>, src: Array<Int63>, dst: Array<Int63>, mid: Int63, hi: Int63, i: Int63, j: Int63, k: Int63) -> Array<Int63> {
  merge(le, src, dst, mid, hi, i, j, k, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.merge (local: merge)
// Variant: uncurried, lifted
pub fn merge(le: Rc<dyn Fn(Int63, Int63) -> bool>, src: Array<Int63>, dst: Array<Int63>, mid: Int63, hi: Int63, i: Int63, j: Int63, k: Int63, _H: ()) -> Array<Int63> {
  let tmp = k < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i < mid;
      let tmp_2 = hi <= j;
      let tmp_3 = src.get_cloned(i);
      let tmp_4 = src.get_cloned(j);
      let le_ref: &Rc<dyn Fn(Int63, Int63) -> bool> = &le;
      let tmp_5 = le_ref(tmp_3, tmp_4);
      let tmp_6 = orb(tmp_2, tmp_5);
      if andb(tmp_1, tmp_6) {
        let tmp_7 = src.get_cloned(i);
        merge(le, src, dst.set(k, tmp_7), mid, hi, i + int63!(1), j, k + int63!(1), ())
      } else {
        let tmp_8 = src.get_cloned(j);
        merge(le, src, dst.set(k, tmp_8), mid, hi, i, j + int63!(1), k + int63!(1), ())
      }
    },
    sumbool::right => {
      std::mem::drop(le);
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.msort
// Variant: uncurried
pub fn msort_1(le: Rc<dyn Fn(Int63, Int63) -> bool>, a_1: Array<Int63>, b_1: Array<Int63>, lo: Int63, hi: Int63) -> (Array<Int63>, Array<Int63>) {
  msort(le, a_1, b_1, lo, hi, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(le: Rc<dyn Fn(Int63, Int63) -> bool>, a_1: Array<Int63>, b_1: Array<Int63>, lo: Int63, hi: Int63, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = andb(lo < hi, int63!(1) < hi - lo);
  match bdec(tmp) {
    sumbool::left => {
      let mid = midp(lo, hi);
      let le_clone: Rc<dyn Fn(Int63, Int63) -> bool> = Rc::clone(&le);
      let tmp_1 = msort(le_clone, a_1, b_1, lo, mid, ());
      match &tmp_1 {
        (b1, a1) => {
          let tmp_2 = ();
          let le_clone_1: Rc<dyn Fn(Int63, Int63) -> bool> = Rc::clone(&le);
          let b1_clone = Clone::clone(b1);
          let a1_clone = Clone::clone(a1);
          std::mem::drop(tmp_1);
          let tmp_3 = msort(le_clone_1, b1_clone, a1_clone, mid, hi, tmp_2);
          match tmp_3 {
            (v84, v86) => {
              let b2 = &v84;
              let b2_clone = Clone::clone(b2);
              let b3 = copy_1(b2_clone, v86, hi, lo);
              let b3_clone = Clone::clone(&b3);
              (merge_1(le, b3_clone, v84, mid, hi, lo, mid, lo), b3)
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(le);
      (a_1, b_1)
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.r2
// Variant: borrowed, uncurried
pub fn r2(rk: &Array<Int63>, h: Int63, n: Int63, p: Int63) -> Int63 {
  let h_1 = h;
  let n_1 = n;
  let p_1 = p;
  let tmp = p_1 + h_1;
  if tmp < n_1 {
    rk.get_cloned(p_1 + h_1) + int63!(1)
  } else {
    int63!(0)
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.keyle
// Variant: borrowed, uncurried
pub fn keyle(rk: &Array<Int63>, h: Int63, n: Int63, p: Int63, q: Int63) -> bool {
  let h_1 = h;
  let n_1 = n;
  let p_1 = p;
  let q_1 = q;
  orb(rk.get_cloned(p_1) < rk.get_cloned(q_1), andb(rk.get_cloned(p_1) == rk.get_cloned(q_1), r2(rk, h_1, n_1, p_1) <= r2(rk, h_1, n_1, q_1)))
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.iota_loop
// Variant: uncurried
pub fn iota_loop_1(a_1: Array<Int63>, n: Int63, i: Int63) -> Array<Int63> {
  iota_loop(a_1, n, i, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.iota_loop (local: iota_loop)
// Variant: uncurried, lifted
pub fn iota_loop(a_1: Array<Int63>, n: Int63, i: Int63, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      iota_loop(a_1.set(i, i), n, i + int63!(1), ())
    },
    sumbool::right => {
      a_1
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.sort_round
// Variant: uncurried
pub fn sort_round(rk: Array<Int63>, h: Int63, n: Int63) -> Array<Int63> {
  let callback: Rc<dyn Fn(Int63, Int63) -> bool> = Rc::new({
    let __anf_capture_16 = n;
    move |v18: Int63, v19: Int63| -> bool {
      let rk = &rk;
      let h_clone = Clone::clone(&h);
      let tmp = Clone::clone(&__anf_capture_16);
      keyle(rk, h_clone, tmp, v18, v19)
    }
  });
  fst::<Array<Int63>, Array<Int63>>(msort_1(callback, iota_loop_1(Array::<Int63>::make(n, int63!(0)), n, int63!(0)), Array::<Int63>::make(n, int63!(0)), int63!(0), n))
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.rank_loop
// Variant: uncurried
pub fn rank_loop_1(le: Rc<dyn Fn(Int63, Int63) -> bool>, sa: Array<Int63>, nr: Array<Int63>, n: Int63, i: Int63) -> Array<Int63> {
  rank_loop(le, sa, nr, n, i, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.rank_loop (local: rank_loop)
// Variant: uncurried, lifted
pub fn rank_loop(le: Rc<dyn Fn(Int63, Int63) -> bool>, sa: Array<Int63>, nr: Array<Int63>, n: Int63, i: Int63, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let p = sa.get_cloned(i);
      let q = sa.get_cloned(i - int63!(1));
      let tmp_1 = nr.get_cloned(q);
      let le_ref: &Rc<dyn Fn(Int63, Int63) -> bool> = &le;
      let tmp_2 = le_ref(p, q);
      let tmp_3 = if tmp_2 {
        int63!(0)
      } else {
        int63!(1)
      };
      rank_loop(le, sa, nr.set(p, tmp_1 + tmp_3), n, i + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(le);
      std::mem::drop(sa);
      nr
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

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.rounds
// Variant: uncurried
pub fn rounds_1(n: Int63, rk: Array<Int63>, h: Int63) -> Array<Int63> {
  rounds(n, rk, h, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.rounds (local: rounds)
// Variant: uncurried, lifted
pub fn rounds(n: Int63, rk: Array<Int63>, h: Int63, _H: ()) -> Array<Int63> {
  let rk_clone = Clone::clone(&rk);
  let sa = sort_round(rk_clone, h, n);
  let rk_clone_1 = Clone::clone(&rk);
  let callback: Rc<dyn Fn(Int63, Int63) -> bool> = Rc::new({
    let __anf_capture_24 = h;
    let __anf_capture_26 = n;
    move |v28: Int63, v29: Int63| -> bool {
      let rk = &rk_clone_1;
      let tmp = Clone::clone(&__anf_capture_24);
      let tmp_1 = Clone::clone(&__anf_capture_26);
      keyle(rk, tmp, tmp_1, v28, v29)
    }
  });
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  let sa_clone = Clone::clone(&sa);
  let nr = rank_loop_1(callback, sa_clone, tmp_2, n, int63!(1));
  let tmp_3 = andb(int63!(0) < h, h < n);
  let tmp_4 = n - h;
  let tmp_5 = h < tmp_4;
  let tmp_6 = sa.get_cloned(n - int63!(1));
  let tmp_7 = nr.get_cloned(tmp_6);
  let tmp_8 = andb(tmp_5, negb(tmp_7 == n - int63!(1)));
  let tmp_9 = andb(tmp_3, tmp_8);
  match bdec(tmp_9) {
    sumbool::left => {
      std::mem::drop(rk);
      std::mem::drop(sa);
      rounds(n, nr, h + h, ())
    },
    sumbool::right => {
      std::mem::drop(rk);
      std::mem::drop(nr);
      sa
    },
  }
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get_owned(v0: rocq_string::RocqString, v1: Int63) -> Int63 {
  let tmp = v0.get(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: borrowed, uncurried
pub fn get(v0: &rocq_string::RocqString, v1: Int63) -> Int63 {
  v0.get(v1)
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.init_rk
// Variant: uncurried
pub fn init_rk_1(x: rocq_string::RocqString, rk: Array<Int63>, n: Int63, i: Int63) -> Array<Int63> {
  init_rk(x, rk, n, i, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.init_rk (local: init_rk)
// Variant: uncurried, lifted
pub fn init_rk(x: rocq_string::RocqString, rk: Array<Int63>, n: Int63, i: Int63, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let x_clone = Clone::clone(&x);
      let tmp_1 = get_owned(x_clone, i);
      init_rk(x, rk.set(i, tmp_1), n, i + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      rk
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.build_sa
// Variant: uncurried
pub fn build_sa(x: rocq_string::RocqString, n: Int63) -> Array<Int63> {
  let tmp = init_rk_1(x, Array::<Int63>::make(n, int63!(0)), n, int63!(0));
  rounds_1(n, tmp, int63!(1))
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.depth_loop
// Variant: uncurried
pub fn depth_loop_1(n: Int63, d: Int63) -> Int63 {
  depth_loop(n, d, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.depth_loop (local: depth_loop)
// Variant: uncurried, lifted
pub fn depth_loop(n: Int63, d: Int63, _H: ()) -> Int63 {
  let tmp = d < int63!(20);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = int63!(1) << d;
      if tmp_1 < n {
        depth_loop(n, d + int63!(1), ())
      } else {
        d
      }
    },
    sumbool::right => {
      d
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.ins
// Variant: uncurried
pub fn ins_1(L: Array<Int63>, R: Array<Int63>, C: Array<Int63>, nx: Int63, x: Int63, d: Int63, v: Int63) -> ((Array<Int63>, Array<Int63>), Array<Int63>) {
  ins(L, R, C, nx, x, d, v, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.ins (local: ins)
// Variant: uncurried, lifted
pub fn ins(L: Array<Int63>, R: Array<Int63>, C: Array<Int63>, nx: Int63, x: Int63, d: Int63, v: Int63, _H: ()) -> ((Array<Int63>, Array<Int63>), Array<Int63>) {
  let tmp = int63!(0) < d;
  match bdec(tmp) {
    sumbool::left => {
      let half = int63!(1) << d - int63!(1);
      let y = nx + d;
      if v < half {
        let tmp_1 = L.get_cloned(x);
        let tmp_2 = ins(L, R, C, nx, tmp_1, d - int63!(1), v, ());
        match tmp_2 {
          (v84, v86) => {
            let p = &v86;
            match v84 {
              (v90, v92) => {
                let Lq = &v92;
                let tmp_3 = v90.set(y, nx + (d - int63!(1)));
                let tmp_4 = Lq.get_cloned(x);
                let tmp_5 = (tmp_3, v92.set(y, tmp_4));
                let tmp_6 = p.get_cloned(x);
                (tmp_5, v86.set(y, tmp_6 + int63!(1)))
              },
            }
          },
        }
      } else {
        let tmp_7 = R.get_cloned(x);
        let tmp_8 = ins(L, R, C, nx, tmp_7, d - int63!(1), v - half, ());
        match tmp_8 {
          (v203, v205) => {
            let p = &v205;
            match v203 {
              (v209, v211) => {
                let Rq = &v209;
                let tmp_9 = Rq.get_cloned(x);
                let tmp_10 = (v209.set(y, tmp_9), v211.set(y, nx + (d - int63!(1))));
                let tmp_11 = p.get_cloned(x);
                (tmp_10, v205.set(y, tmp_11 + int63!(1)))
              },
            }
          },
        }
      }
    },
    sumbool::right => {
      let tmp_12 = (L, R);
      let tmp_13 = C.get_cloned(x);
      (tmp_12, C.set(nx, tmp_13 + int63!(1)))
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.build
// Variant: uncurried
pub fn build_1(sa: Array<Int63>, L: Array<Int63>, R: Array<Int63>, C: Array<Int63>, roots: Array<Int63>, n: Int63, D: Int63, i: Int63, nx: Int63) -> (((Array<Int63>, Array<Int63>), Array<Int63>), Array<Int63>) {
  build(sa, L, R, C, roots, n, D, i, nx, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(sa: Array<Int63>, L: Array<Int63>, R: Array<Int63>, C: Array<Int63>, roots: Array<Int63>, n: Int63, D: Int63, i: Int63, nx: Int63, _H: ()) -> (((Array<Int63>, Array<Int63>), Array<Int63>), Array<Int63>) {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = roots.get_cloned(i);
      let tmp_2 = sa.get_cloned(i);
      let tmp_3 = ins_1(L, R, C, nx, tmp_1, D, tmp_2);
      match tmp_3 {
        (v46, v48) => {
          match v46 {
            (v51, v53) => {
              let tmp_4 = roots.set(i + int63!(1), nx + D);
              let tmp_5 = i + int63!(1);
              let tmp_6 = nx + D;
              build(sa, v51, v53, v48, tmp_4, n, D, tmp_5, tmp_6 + int63!(1), ())
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(sa);
      (((L, R), C), roots)
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.bs
// Variant: uncurried
pub fn bs_1(P: Rc<dyn Fn(Int63) -> bool>, lo: Int63, hi: Int63) -> Int63 {
  bs(P, lo, hi, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.bs (local: bs)
// Variant: uncurried, lifted
pub fn bs(P: Rc<dyn Fn(Int63) -> bool>, lo: Int63, hi: Int63, _H: ()) -> Int63 {
  let tmp = lo < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = midp(lo, hi);
      let P_ref: &Rc<dyn Fn(Int63) -> bool> = &P;
      let tmp_2 = P_ref(tmp_1);
      if tmp_2 {
        let tmp_3 = midp(lo, hi);
        bs(P, lo, tmp_3, ())
      } else {
        bs(P, midp(lo, hi) + int63!(1), hi, ())
      }
    },
    sumbool::right => {
      std::mem::drop(P);
      lo
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.cmpt
// Variant: borrowed, uncurried
pub fn cmpt_1(x: &rocq_string::RocqString, t: &rocq_string::RocqString, n: Int63, m: Int63, p: Int63, k: Int63) -> std::cmp::Ordering {
  let n_1 = n;
  let m_1 = m;
  let p_1 = p;
  let k_1 = k;
  cmpt(x, t, n_1, m_1, p_1, k_1, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.cmpt (local: cmpt)
// Variant: borrowed, uncurried, lifted
pub fn cmpt(x: &rocq_string::RocqString, t: &rocq_string::RocqString, n: Int63, m: Int63, p: Int63, k: Int63, _H: ()) -> std::cmp::Ordering {
  let n_1 = n;
  let m_1 = m;
  let p_1 = p;
  let k_1 = k;
  let tmp = k_1 < m_1;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = p_1 + k_1;
      if tmp_1 < n_1 {
        let a_1 = get(t, k_1);
        let b_1 = get(x, p_1 + k_1);
        if a_1 < b_1 {
          std::cmp::Ordering::Less
        } else {
          if b_1 < a_1 {
            std::cmp::Ordering::Greater
          } else {
            cmpt(x, t, n_1, m_1, p_1, k_1 + int63!(1), ())
          }
        }
      } else {
        std::cmp::Ordering::Greater
      }
    },
    sumbool::right => {
      std::cmp::Ordering::Equal
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.cmp_at
// Variant: borrowed, uncurried
pub fn cmp_at(x: &rocq_string::RocqString, t: &rocq_string::RocqString, n: Int63, m: Int63, sa: &Array<Int63>, i: Int63) -> std::cmp::Ordering {
  let n_1 = n;
  let m_1 = m;
  let i_1 = i;
  cmpt_1(x, t, n_1, m_1, sa.get_cloned(i_1), int63!(0))
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.qry
// Variant: uncurried
pub fn qry_1(L: Array<Int63>, R: Array<Int63>, C: Array<Int63>, a_1: Int63, b_1: Int63, d: Int63, k: Int63) -> Int63 {
  qry(L, R, C, a_1, b_1, d, k, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.qry (local: qry)
// Variant: uncurried, lifted
pub fn qry(L: Array<Int63>, R: Array<Int63>, C: Array<Int63>, a_1: Int63, b_1: Int63, d: Int63, k: Int63, _H: ()) -> Int63 {
  let tmp = int63!(0) < d;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = L.get_cloned(b_1);
      let tmp_2 = C.get_cloned(tmp_1);
      let tmp_3 = L.get_cloned(a_1);
      let tmp_4 = C.get_cloned(tmp_3);
      let cl = tmp_2 - tmp_4;
      if k <= cl {
        let tmp_5 = L.get_cloned(a_1);
        let tmp_6 = L.get_cloned(b_1);
        qry(L, R, C, tmp_5, tmp_6, d - int63!(1), k, ())
      } else {
        let tmp_7 = int63!(1) << d - int63!(1);
        let tmp_8 = R.get_cloned(a_1);
        let tmp_9 = R.get_cloned(b_1);
        tmp_7 + qry(L, R, C, tmp_8, tmp_9, d - int63!(1), k - cl, ())
      }
    },
    sumbool::right => {
      std::mem::drop(L);
      std::mem::drop(R);
      std::mem::drop(C);
      int63!(0)
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.answer1
// Variant: uncurried
pub fn answer1(x: rocq_string::RocqString, n: Int63, sa: Array<Int63>, L: Array<Int63>, R: Array<Int63>, C: Array<Int63>, roots: Array<Int63>, D: Int63, t: rocq_string::RocqString, k: Int63) -> Int63 {
  let t_clone = Clone::clone(&t);
  let m = length(t_clone);
  let x_clone = Clone::clone(&x);
  let t_clone_1 = Clone::clone(&t);
  let sa_clone = Clone::clone(&sa);
  let callback: Rc<dyn Fn(Int63) -> bool> = Rc::new({
    let __anf_capture_34 = n;
    let __anf_capture_36 = m;
    move |i: Int63| -> bool {
      let x = &x_clone;
      let t = &t_clone_1;
      let n = &__anf_capture_34;
      let m = &__anf_capture_36;
      let sa = &sa_clone;
      let n_clone = Clone::clone(n);
      let m_clone = Clone::clone(m);
      match cmp_at(x, t, n_clone, m_clone, sa, i) {
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
  });
  let lo = bs_1(callback, int63!(0), n);
  let x_clone_1 = Clone::clone(&x);
  let t_clone_2 = Clone::clone(&t);
  let sa_clone_1 = Clone::clone(&sa);
  let callback_1: Rc<dyn Fn(Int63) -> bool> = Rc::new({
    let __anf_capture_98 = n;
    let __anf_capture_100 = m;
    move |i: Int63| -> bool {
      let x = &x_clone_1;
      let t = &t_clone_2;
      let n = &__anf_capture_98;
      let m = &__anf_capture_100;
      let sa = &sa_clone_1;
      let n_clone_1 = Clone::clone(n);
      let m_clone_1 = Clone::clone(m);
      match cmp_at(x, t, n_clone_1, m_clone_1, sa, i) {
        std::cmp::Ordering::Equal => {
          false
        },
        std::cmp::Ordering::Less => {
          true
        },
        std::cmp::Ordering::Greater => {
          false
        },
      }
    }
  });
  let hi = bs_1(callback_1, int63!(0), n);
  let tmp = hi - lo;
  if k <= tmp {
    std::mem::drop(x);
    std::mem::drop(sa);
    std::mem::drop(t);
    let tmp_1 = roots.get_cloned(lo);
    let tmp_2 = roots.get_cloned(hi);
    std::mem::drop(roots);
    qry_1(L, R, C, tmp_1, tmp_2, D, k) + int63!(1)
  } else {
    std::mem::drop(x);
    std::mem::drop(sa);
    std::mem::drop(L);
    std::mem::drop(R);
    std::mem::drop(C);
    std::mem::drop(roots);
    std::mem::drop(t);
    int63!(0) - int63!(1)
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.qloop
// Variant: uncurried
pub fn qloop_1(x: rocq_string::RocqString, n: Int63, sa: Array<Int63>, L: Array<Int63>, R: Array<Int63>, C: Array<Int63>, roots: Array<Int63>, D: Int63, ts: Array<rocq_string::RocqString>, ks: Array<Int63>, out: Array<Int63>, q: Int63, Q: Int63) -> Array<Int63> {
  qloop(x, n, sa, L, R, C, roots, D, ts, ks, out, q, Q, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.qloop (local: qloop)
// Variant: uncurried, lifted
pub fn qloop(x: rocq_string::RocqString, n: Int63, sa: Array<Int63>, L: Array<Int63>, R: Array<Int63>, C: Array<Int63>, roots: Array<Int63>, D: Int63, ts: Array<rocq_string::RocqString>, ks: Array<Int63>, out: Array<Int63>, q: Int63, Q: Int63, _H: ()) -> Array<Int63> {
  let tmp = q < Q;
  match bdec(tmp) {
    sumbool::left => {
      let ts_ref = &ts;
      let tmp_1 = ts_ref.get_cloned(q);
      let tmp_2 = ks.get_cloned(q);
      let x_clone = Clone::clone(&x);
      let sa_clone = Clone::clone(&sa);
      let L_clone = Clone::clone(&L);
      let R_clone = Clone::clone(&R);
      let C_clone = Clone::clone(&C);
      let roots_clone = Clone::clone(&roots);
      let tmp_3 = answer1(x_clone, n, sa_clone, L_clone, R_clone, C_clone, roots_clone, D, tmp_1, tmp_2);
      qloop(x, n, sa, L, R, C, roots, D, ts, ks, out.set(q, tmp_3), q + int63!(1), Q, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(sa);
      std::mem::drop(L);
      std::mem::drop(R);
      std::mem::drop(C);
      std::mem::drop(roots);
      std::mem::drop(ts);
      std::mem::drop(ks);
      out
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.kth_occurrences_impl
// Variant: uncurried
pub fn kth_occurrences_impl(x: rocq_string::RocqString, ts: Array<rocq_string::RocqString>, ks: Array<Int63>) -> Array<Int63> {
  let x_clone = Clone::clone(&x);
  let n = length(x_clone);
  let x_clone_1 = Clone::clone(&x);
  let sa = build_sa(x_clone_1, n);
  let D = depth_loop_1(n, int63!(0));
  let M = n * (D + int63!(1)) + int63!(1);
  let tmp = Array::<Int63>::make(M, int63!(0));
  let tmp_1 = Array::<Int63>::make(M, int63!(0));
  let tmp_2 = Array::<Int63>::make(M, int63!(0));
  let tmp_3 = Array::<Int63>::make(n + int63!(1), int63!(0));
  let sa_clone = Clone::clone(&sa);
  let tmp_4 = build_1(sa_clone, tmp, tmp_1, tmp_2, tmp_3, n, D, int63!(0), int63!(1));
  match tmp_4 {
    (v107, v109) => {
      match v107 {
        (v112, v114) => {
          match v112 {
            (v117, v119) => {
              let Q = ts.length();
              qloop_1(x, n, sa, v117, v119, v114, v109, D, ts, ks, Array::<Int63>::make(Q, int63!(0)), int63!(0), Q)
            },
          }
        },
      }
    },
  }
}
