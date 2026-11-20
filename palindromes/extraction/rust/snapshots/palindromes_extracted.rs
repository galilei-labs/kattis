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

pub type char63 = Int63;

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: rocq_string::RocqString) -> Int63 {
  let tmp = v0.length();
  std::mem::drop(v0);
  tmp
}

// Rocq: Palindromes.palindromes_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Palindromes.palindromes_implem.imin
// Variant: uncurried
pub fn imin(a_1: Int63, b_1: Int63) -> Int63 {
  if a_1 < b_1 {
    a_1
  } else {
    b_1
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

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: rocq_string::RocqString, v1: Int63) -> Int63 {
  let tmp = v0.get(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Palindromes.palindromes_implem.hcond
// Variant: uncurried
pub fn hcond(x: rocq_string::RocqString, n: Int63, q: Int63, k: Int63) -> bool {
  let tmp = andb(k <= q >> int63!(1), (q + int63!(1) >> int63!(1)) + k < n);
  let tmp_1 = (q >> int63!(1)) - k;
  let x_clone = Clone::clone(&x);
  andb(tmp, get(x_clone, tmp_1) == get(x, (q + int63!(1) >> int63!(1)) + k))
}

// Rocq: Palindromes.palindromes_implem.expand
// Variant: uncurried
pub fn expand_1(x: rocq_string::RocqString, n: Int63, q: Int63, k: Int63) -> Int63 {
  expand(x, n, q, k, ())
}

// Rocq: Palindromes.palindromes_implem.expand (local: expand)
// Variant: uncurried, lifted
pub fn expand(x: rocq_string::RocqString, n: Int63, q: Int63, k: Int63, _H: ()) -> Int63 {
  let tmp = k < n;
  match bdec(tmp) {
    sumbool::left => {
      let x_clone = Clone::clone(&x);
      if hcond(x_clone, n, q, k) {
        expand(x, n, q, k + int63!(1), ())
      } else {
        std::mem::drop(x);
        k
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      k
    },
  }
}

// Rocq: Palindromes.palindromes_implem.man
// Variant: uncurried
pub fn man_1(x: rocq_string::RocqString, n: Int63, n2: Int63, cnt: Array<Int63>, q: Int63, Q: Int63, rb: Int63) -> Array<Int63> {
  man(x, n, n2, cnt, q, Q, rb, ())
}

// Rocq: Palindromes.palindromes_implem.man (local: man)
// Variant: uncurried, lifted
pub fn man(x: rocq_string::RocqString, n: Int63, n2: Int63, cnt: Array<Int63>, q: Int63, Q: Int63, rb: Int63, _H: ()) -> Array<Int63> {
  let tmp = q < n2;
  match bdec(tmp) {
    sumbool::left => {
      let bq = q + int63!(1) >> int63!(1);
      let k0 = if bq < rb {
        let tmp_1 = cnt.get_cloned(Q + Q - q);
        imin(tmp_1, rb - bq)
      } else {
        int63!(0)
      };
      let x_clone = Clone::clone(&x);
      let c = expand_1(x_clone, n, q, k0);
      let tmp_2 = bq + c;
      if rb < tmp_2 {
        man(x, n, n2, cnt.set(q, c), q + int63!(1), q, bq + c, ())
      } else {
        man(x, n, n2, cnt.set(q, c), q + int63!(1), Q, rb, ())
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      cnt
    },
  }
}

// Rocq: Palindromes.palindromes_implem.manacher
pub fn manacher(x: rocq_string::RocqString) -> Array<Int63> {
  let x_clone = Clone::clone(&x);
  let n = length(x_clone);
  let tmp = n + n;
  let tmp_1 = n + n;
  man_1(x, n, tmp, Array::<Int63>::make(tmp_1, int63!(0)), int63!(0), int63!(0), int63!(0))
}

// Rocq: Palindromes.palindromes_implem.tab_loop
// Variant: uncurried
pub fn tab_loop_1(f: Rc<dyn Fn(Int63) -> Int63>, n: Int63, i: Int63, a_1: Array<Int63>) -> Array<Int63> {
  tab_loop(f, n, i, a_1, ())
}

// Rocq: Palindromes.palindromes_implem.tab_loop (local: tab_loop)
// Variant: uncurried, lifted
pub fn tab_loop(f: Rc<dyn Fn(Int63) -> Int63>, n: Int63, i: Int63, a_1: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let f_ref: &Rc<dyn Fn(Int63) -> Int63> = &f;
      let tmp_2 = f_ref(i);
      tab_loop(f, n, tmp_1, a_1.set(i, tmp_2), ())
    },
    sumbool::right => {
      std::mem::drop(f);
      a_1
    },
  }
}

// Rocq: Palindromes.palindromes_implem.tab
// Variant: uncurried
pub fn tab(n: Int63, f: Rc<dyn Fn(Int63) -> Int63>) -> Array<Int63> {
  let tmp = Array::<Int63>::make(n, int63!(0));
  tab_loop_1(f, n, int63!(0), tmp)
}

// Rocq: Palindromes.palindromes_implem.build
// Variant: uncurried
pub fn build_1(ts: Array<Int63>, m: Int63, k: Int63, head: Array<Int63>, next: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  build(ts, m, k, head, next, ())
}

// Rocq: Palindromes.palindromes_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(ts: Array<Int63>, m: Int63, k: Int63, head: Array<Int63>, next: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = k < m;
  match bdec(tmp) {
    sumbool::left => {
      let t = ts.get_cloned(k);
      let h = head.get_cloned(t);
      build(ts, m, k + int63!(1), head.set(t, k + int63!(1)), next.set(k, h), ())
    },
    sumbool::right => {
      std::mem::drop(ts);
      (head, next)
    },
  }
}

// Rocq: Palindromes.palindromes_implem.fen_sum
// Variant: uncurried
pub fn fen_sum_1(t: Array<Int63>, j: Int63, acc: Int63) -> Int63 {
  fen_sum(t, j, acc, ())
}

// Rocq: Palindromes.palindromes_implem.fen_sum (local: fen_sum)
// Variant: uncurried, lifted
pub fn fen_sum(t: Array<Int63>, j: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = int63!(0) < j;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = j - int63!(1);
      let tmp_2 = j & tmp_1;
      let tmp_3 = t.get_cloned(j);
      fen_sum(t, tmp_2, acc + tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(t);
      acc
    },
  }
}

// Rocq: Palindromes.palindromes_implem.fsum
// Variant: uncurried
pub fn fsum(t: Array<Int63>, j: Int63) -> Int63 {
  fen_sum_1(t, j, int63!(0))
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

// Rocq: Palindromes.palindromes_implem.fval
// Variant: uncurried
pub fn fval(t: (Array<Int63>, Array<Int63>), a_1: Int63) -> Int63 {
  let t_clone = Clone::clone(&t);
  let tmp = fsum(fst::<Array<Int63>, Array<Int63>>(t_clone), a_1 + int63!(1));
  let tmp_1 = snd::<Array<Int63>, Array<Int63>>(t);
  let tmp_2 = a_1 + int63!(1);
  tmp + a_1 * fsum(tmp_1, tmp_2)
}

// Rocq: Palindromes.palindromes_implem.walk
// Variant: uncurried
pub fn walk_1(as_: Array<Int63>, next: Array<Int63>, t: (Array<Int63>, Array<Int63>), v: Array<Int63>, ptr: Int63) -> Array<Int63> {
  walk(as_, next, t, v, ptr, ())
}

// Rocq: Palindromes.palindromes_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(as_: Array<Int63>, next: Array<Int63>, t: (Array<Int63>, Array<Int63>), v: Array<Int63>, ptr: Int63, _H: ()) -> Array<Int63> {
  let tmp = int63!(0) < ptr;
  match bdec(tmp) {
    sumbool::left => {
      let k = ptr - int63!(1);
      let nx = next.get_cloned(k);
      let tmp_1 = as_.get_cloned(k);
      let t_clone = Clone::clone(&t);
      let v_ = v.set(k, fval(t_clone, tmp_1));
      let tmp_2 = nx < ptr;
      match bdec(tmp_2) {
        sumbool::left => {
          walk(as_, next, t, v_, nx, ())
        },
        sumbool::right => {
          std::mem::drop(next);
          std::mem::drop(t);
          std::mem::drop(as_);
          v_
        },
      }
    },
    sumbool::right => {
      std::mem::drop(as_);
      std::mem::drop(next);
      std::mem::drop(t);
      v
    },
  }
}

// Rocq: Palindromes.palindromes_implem.lowb
pub fn lowb(j: Int63) -> Int63 {
  let tmp = j - int63!(1);
  let tmp_1 = j & tmp;
  j - tmp_1
}

// Rocq: Palindromes.palindromes_implem.fen_add
// Variant: uncurried
pub fn fen_add_1(t: Array<Int63>, N: Int63, j: Int63, delta: Int63) -> Array<Int63> {
  fen_add(t, N, j, delta, ())
}

// Rocq: Palindromes.palindromes_implem.fen_add (local: fen_add)
// Variant: uncurried, lifted
pub fn fen_add(t: Array<Int63>, N: Int63, j: Int63, delta: Int63, _H: ()) -> Array<Int63> {
  let tmp = andb(int63!(0) < j, j <= N);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = t.get_cloned(j);
      let t_ = t.set(j, tmp_1 + delta);
      let tmp_2 = lowb(j);
      let nj = j + tmp_2;
      let tmp_3 = j < nj;
      match bdec(tmp_3) {
        sumbool::left => {
          fen_add(t_, N, nj, delta, ())
        },
        sumbool::right => {
          t_
        },
      }
    },
    sumbool::right => {
      t
    },
  }
}

// Rocq: Palindromes.palindromes_implem.fadd
// Variant: uncurried
pub fn fadd(t: Array<Int63>, N: Int63, j: Int63, delta: Int63) -> Array<Int63> {
  fen_add_1(t, N, j, delta)
}

// Rocq: Palindromes.palindromes_implem.insert
// Variant: uncurried
pub fn insert(NN: Int63, t: (Array<Int63>, Array<Int63>), i: Int63, di: Int63) -> (Array<Int63>, Array<Int63>) {
  let dd = imin(di, i + int63!(1));
  let lft = i + int63!(1) - dd;
  let t_clone = Clone::clone(&t);
  let t0 = fadd(fst::<Array<Int63>, Array<Int63>>(t_clone), NN, int63!(1), dd);
  let t0_1 = fadd(t0, NN, lft + int63!(2), lft);
  let t0_2 = fadd(t0_1, NN, i + int63!(2), int63!(0) - (i + int63!(1)));
  let t1 = fadd(snd::<Array<Int63>, Array<Int63>>(t), NN, lft + int63!(2), int63!(0) - int63!(1));
  let t1_1 = fadd(t1, NN, i + int63!(2), int63!(1));
  (t0_2, t1_1)
}

// Rocq: Palindromes.palindromes_implem.sweep
// Variant: uncurried
pub fn sweep_1(d: Array<Int63>, as_: Array<Int63>, head: Array<Int63>, next: Array<Int63>, n: Int63, n1: Int63, NN: Int63, t: (Array<Int63>, Array<Int63>), v: Array<Int63>, tau: Int63) -> Array<Int63> {
  sweep(d, as_, head, next, n, n1, NN, t, v, tau, ())
}

// Rocq: Palindromes.palindromes_implem.sweep (local: sweep)
// Variant: uncurried, lifted
pub fn sweep(d: Array<Int63>, as_: Array<Int63>, head: Array<Int63>, next: Array<Int63>, n: Int63, n1: Int63, NN: Int63, t: (Array<Int63>, Array<Int63>), v: Array<Int63>, tau: Int63, _H: ()) -> Array<Int63> {
  let tmp = tau < n1;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = head.get_cloned(tau);
      let as__clone = Clone::clone(&as_);
      let next_clone = Clone::clone(&next);
      let t_clone = Clone::clone(&t);
      let v_ = walk_1(as__clone, next_clone, t_clone, v, tmp_1);
      let t_ = if tau < n {
        let tmp_2 = d.get_cloned(tau);
        insert(NN, t, tau, tmp_2)
      } else {
        t
      };
      sweep(d, as_, head, next, n, n1, NN, t_, v_, tau + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(d);
      std::mem::drop(as_);
      std::mem::drop(head);
      std::mem::drop(next);
      std::mem::drop(t);
      v
    },
  }
}

// Rocq: Palindromes.palindromes_implem.lsum_all
// Variant: uncurried
pub fn lsum_all(n: Int63, m: Int63, d: Array<Int63>, as_: Array<Int63>, ts: Array<Int63>) -> Array<Int63> {
  let tmp = Array::<Int63>::make(n + int63!(1), int63!(0));
  let tmp_1 = Array::<Int63>::make(m, int63!(0));
  let hn = build_1(ts, m, int63!(0), tmp, tmp_1);
  let NN = n + int63!(2);
  let hn_clone = Clone::clone(&hn);
  let tmp_2 = fst::<Array<Int63>, Array<Int63>>(hn_clone);
  let tmp_3 = snd::<Array<Int63>, Array<Int63>>(hn);
  let tmp_4 = n + int63!(1);
  let tmp_5 = Array::<Int63>::make(NN + int63!(1), int63!(0));
  let tmp_6 = NN + int63!(1);
  sweep_1(d, as_, tmp_2, tmp_3, n, tmp_4, NN, (tmp_5, Array::<Int63>::make(tmp_6, int63!(0))), Array::<Int63>::make(m, int63!(0)), int63!(0))
}

// Rocq: Palindromes.palindromes_implem.fam
// Variant: uncurried
pub fn fam(n: Int63, m: Int63, cnt: Array<Int63>, xl: Array<Int63>, xr: Array<Int63>, par: Int63, rev: bool) -> Array<Int63> {
  let callback: Rc<dyn Fn(Int63) -> Int63> = Rc::new({
    let __anf_capture_17 = rev;
    let __anf_capture_19 = n;
    let __anf_capture_21 = par;
    move |i: Int63| -> Int63 {
      let rev = &__anf_capture_17;
      let n = &__anf_capture_19;
      let par = &__anf_capture_21;
      let cnt = &cnt;
      let tmp = int63!(2);
      let tmp_1 = if *rev {
        let tmp_2 = int63!(1);
        Clone::clone(n) - tmp_2 - i
      } else {
        i
      };
      let tmp_3 = tmp * tmp_1 + Clone::clone(par);
      cnt.get_cloned(tmp_3)
    }
  });
  let d = tab(n, callback);
  let xr_clone = Clone::clone(&xr);
  let xl_clone = Clone::clone(&xl);
  let callback_1: Rc<dyn Fn(Int63) -> Int63> = Rc::new({
    let __anf_capture_86 = rev;
    let __anf_capture_90 = par;
    let __anf_capture_92 = n;
    move |k: Int63| -> Int63 {
      let rev = &__anf_capture_86;
      let xr = &xr_clone;
      let par = &__anf_capture_90;
      let n = &__anf_capture_92;
      let xl = &xl_clone;
      if *rev {
        let tmp_4 = xr.get_cloned(k) - Clone::clone(par);
        let n_clone = Clone::clone(n);
        n_clone - tmp_4
      } else {
        let tmp_5 = xl.get_cloned(k);
        tmp_5 - int63!(1)
      }
    }
  });
  let as_ = tab(m, callback_1);
  let callback_2: Rc<dyn Fn(Int63) -> Int63> = Rc::new({
    let __anf_capture_150 = xl;
    let __anf_capture_152 = xr;
    let __anf_capture_154 = par;
    let __anf_capture_156 = rev;
    let __anf_capture_158 = n;
    move |k: Int63| -> Int63 {
      let xl = &__anf_capture_150;
      let xr = &__anf_capture_152;
      let par = &__anf_capture_154;
      let rev = &__anf_capture_156;
      let n = &__anf_capture_158;
      let h = xl.get_cloned(k) + xr.get_cloned(k) - Clone::clone(par) >> int63!(1);
      if *rev {
        let n_clone_1 = Clone::clone(n);
        n_clone_1 - h
      } else {
        h
      }
    }
  });
  let ts = tab(m, callback_2);
  lsum_all(n, m, d, as_, ts)
}

// Rocq: Palindromes.palindromes_implem.palindromes_impl
// Variant: uncurried
pub fn palindromes_impl(x: rocq_string::RocqString, xl: Array<Int63>, xr: Array<Int63>) -> Array<Int63> {
  let x_clone = Clone::clone(&x);
  let n = length(x_clone);
  let m = xl.length();
  let cnt = manacher(x);
  let cnt_clone = Clone::clone(&cnt);
  let xl_clone = Clone::clone(&xl);
  let xr_clone = Clone::clone(&xr);
  let v0 = fam(n, m, cnt_clone, xl_clone, xr_clone, int63!(0), false);
  let cnt_clone_1 = Clone::clone(&cnt);
  let xl_clone_1 = Clone::clone(&xl);
  let xr_clone_1 = Clone::clone(&xr);
  let v1 = fam(n, m, cnt_clone_1, xl_clone_1, xr_clone_1, int63!(0), true);
  let cnt_clone_2 = Clone::clone(&cnt);
  let xl_clone_2 = Clone::clone(&xl);
  let xr_clone_2 = Clone::clone(&xr);
  let v2 = fam(n, m, cnt_clone_2, xl_clone_2, xr_clone_2, int63!(1), false);
  let v3_1 = fam(n, m, cnt, xl, xr, int63!(1), true);
  let callback: Rc<dyn Fn(Int63) -> Int63> = Rc::new({
    move |k: Int63| -> Int63 {
      let v0 = &v0;
      let v1 = &v1;
      let v2 = &v2;
      let v3 = &v3_1;
      let tmp = v0.get_cloned(k) + v1.get_cloned(k) + v2.get_cloned(k);
      let tmp_1 = v3.get_cloned(k);
      tmp + tmp_1
    }
  });
  tab(m, callback)
}
