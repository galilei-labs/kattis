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

#[derive(Clone, Copy)]
pub enum player {
  Ruben,
  Albert,
}

pub type uint = Int63;

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.loop
// Variant: uncurried
pub fn loop__1<A: Clone + 'static>(f: Rc<dyn Fn(Int63, A) -> A>, hi: Int63, i: Int63, acc: A) -> A {
  loop_::<A>((), f, hi, i, acc, ())
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.loop (local: loop)
// Variant: uncurried, lifted
pub fn loop_<A: Clone + 'static>(_A_1: (), f: Rc<dyn Fn(Int63, A) -> A>, hi: Int63, i: Int63, acc: A, _H: ()) -> A {
  let tmp = i < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let f_ref: &Rc<dyn Fn(Int63, A) -> A> = &f;
      let tmp_2 = f_ref(i, acc);
      loop_::<A>((), f, hi, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      std::mem::drop(f);
      acc
    },
  }
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.for_
// Variant: uncurried
pub fn for_<A: Clone + 'static>(f: Rc<dyn Fn(Int63, A) -> A>, lo: Int63, hi: Int63, acc: A) -> A {
  loop__1::<A>(f, hi, lo, acc)
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.imax
// Variant: uncurried
pub fn imax(a_1: Int63, b_1: Int63) -> Int63 {
  if a_1 <= b_1 {
    b_1
  } else {
    a_1
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.cidx
// Variant: uncurried
pub fn cidx(D: Int63, x: Int63, y: Int63, z: Int63) -> Int63 {
  (x * D + y) * D + z
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.imin
// Variant: uncurried
pub fn imin(a_1: Int63, b_1: Int63) -> Int63 {
  if a_1 <= b_1 {
    a_1
  } else {
    b_1
  }
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.look
// Variant: borrowed, uncurried
pub fn look(T: &Array<Int63>, D: Int63, x: Int63, y: Int63, z: Int63) -> Int63 {
  let D_1 = D;
  let x_1 = x;
  let y_1 = y;
  let z_1 = z;
  let tmp = imin(y_1, z_1);
  let lo = imin(x_1, tmp);
  let tmp_1 = imax(y_1, z_1);
  let hi = imax(x_1, tmp_1);
  let tmp_2 = x_1 + y_1 + z_1 - lo;
  T.get_cloned(cidx(D_1, lo, tmp_2 - hi, hi))
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.cutv
// Variant: borrowed, uncurried
pub fn cutv(T: &Array<Int63>, D: Int63, x: Int63, y: Int63, z: Int63, a_1: Int63, b_1: Int63, c: Int63) -> Int63 {
  let D_1 = D;
  let x_1 = x;
  let y_1 = y;
  let z_1 = z;
  let a_2 = a_1;
  let b_2 = b_1;
  let c_1 = c;
  let p1 = a_2 - int63!(1);
  let p2 = x_1 - a_2;
  let q1 = b_2 - int63!(1);
  let q2 = y_1 - b_2;
  let r1 = c_1 - int63!(1);
  let r2 = z_1 - c_1;
  look(T, D_1, p1, q1, r1) ^ (look(T, D_1, p1, q1, r2) ^ (look(T, D_1, p1, q2, r1) ^ (look(T, D_1, p1, q2, r2) ^ (look(T, D_1, p2, q1, r1) ^ (look(T, D_1, p2, q1, r2) ^ (look(T, D_1, p2, q2, r1) ^ look(T, D_1, p2, q2, r2)))))))
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.mark_c
// Variant: uncurried
pub fn mark_c(T: Array<Int63>, D: Int63, x: Int63, y: Int63, z: Int63, a_1: Int63, b_1: Int63, hc: Int63, st: Int63, s: Array<Int63>) -> Array<Int63> {
  let callback: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
    move |c: Int63, s: Array<Int63>| -> Array<Int63> {
      let T = &T;
      let D = &D;
      let x = &x;
      let y = &y;
      let z = &z;
      let a_1 = &a_1;
      let b_1 = &b_1;
      let st = &st;
      let tmp = cutv(T, Clone::clone(D), Clone::clone(x), Clone::clone(y), Clone::clone(z), Clone::clone(a_1), Clone::clone(b_1), c);
      let st_clone = Clone::clone(st);
      s.set(tmp, st_clone)
    }
  });
  for_::<Array<Int63>>(callback, int63!(1), hc + int63!(1), s)
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.mark_b
// Variant: uncurried
pub fn mark_b(T: Array<Int63>, D: Int63, x: Int63, y: Int63, z: Int63, a_1: Int63, hb: Int63, hc: Int63, st: Int63, s: Array<Int63>) -> Array<Int63> {
  let callback: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
    move |b_1: Int63, s: Array<Int63>| -> Array<Int63> {
      let T_clone = Clone::clone(&T);
      let D_clone = Clone::clone(&D);
      let x_clone = Clone::clone(&x);
      let y_clone = Clone::clone(&y);
      let z_clone = Clone::clone(&z);
      let a_clone = Clone::clone(&a_1);
      let hc_clone = Clone::clone(&hc);
      let st_clone = Clone::clone(&st);
      mark_c(T_clone, D_clone, x_clone, y_clone, z_clone, a_clone, b_1, hc_clone, st_clone, s)
    }
  });
  for_::<Array<Int63>>(callback, int63!(1), hb + int63!(1), s)
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.mark_a
// Variant: uncurried
pub fn mark_a(T: Array<Int63>, D: Int63, x: Int63, y: Int63, z: Int63, ha: Int63, hb: Int63, hc: Int63, st: Int63, s: Array<Int63>) -> Array<Int63> {
  let callback: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
    move |a_1: Int63, s: Array<Int63>| -> Array<Int63> {
      let T_clone = Clone::clone(&T);
      let D_clone = Clone::clone(&D);
      let x_clone = Clone::clone(&x);
      let y_clone = Clone::clone(&y);
      let z_clone = Clone::clone(&z);
      let hb_clone = Clone::clone(&hb);
      let hc_clone = Clone::clone(&hc);
      let st_clone = Clone::clone(&st);
      mark_b(T_clone, D_clone, x_clone, y_clone, z_clone, a_1, hb_clone, hc_clone, st_clone, s)
    }
  });
  for_::<Array<Int63>>(callback, int63!(1), ha + int63!(1), s)
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.mex_loop
// Variant: uncurried
pub fn mex_loop_1(s: Array<Int63>, st: Int63, L: Int63, t: Int63) -> Int63 {
  mex_loop(s, st, L, t, ())
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.mex_loop (local: mex_loop)
// Variant: uncurried, lifted
pub fn mex_loop(s: Array<Int63>, st: Int63, L: Int63, t: Int63, _H: ()) -> Int63 {
  let tmp = t < L;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = s.get_cloned(t);
      if tmp_1 == st {
        mex_loop(s, st, L, t + int63!(1), ())
      } else {
        std::mem::drop(s);
        t
      }
    },
    sumbool::right => {
      std::mem::drop(s);
      t
    },
  }
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.cell
// Variant: uncurried
pub fn cell(D: Int63, L: Int63, x: Int63, y: Int63, z: Int63, st: (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>) {
  match st {
    (v7, v9) => {
      let seen = &v7;
      let k = cidx(D, x, y, z);
      let stamp = k + int63!(1);
      let tmp = (x + int63!(1)) / int63!(2);
      let tmp_1 = (y + int63!(1)) / int63!(2);
      let tmp_2 = (z + int63!(1)) / int63!(2);
      let seen_clone = Clone::clone(seen);
      let seen_1 = mark_a(seen_clone, D, x, y, z, tmp, tmp_1, tmp_2, stamp, v9);
      let seen_clone_1 = Clone::clone(&seen_1);
      let m = mex_loop_1(seen_clone_1, stamp, L, int63!(0));
      (v7.set(k, m), seen_1)
    },
  }
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.table
// Variant: uncurried
pub fn table(D: Int63, L: Int63) -> (Array<Int63>, Array<Int63>) {
  let callback: Rc<dyn Fn(Int63, (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>)> = Rc::new({
    let __anf_capture_8 = L;
    let __anf_capture_10 = D;
    move |x: Int63, st: (Array<Int63>, Array<Int63>)| -> (Array<Int63>, Array<Int63>) {
      let L = &__anf_capture_8;
      let D = &__anf_capture_10;
      let L_clone = Clone::clone(L);
      let D_clone = Clone::clone(D);
      let callback_1: Rc<dyn Fn(Int63, (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>)> = Rc::new({
        let __anf_capture_24 = x;
        move |y: Int63, st: (Array<Int63>, Array<Int63>)| -> (Array<Int63>, Array<Int63>) {
          let L = &L_clone;
          let x = &__anf_capture_24;
          let D = &D_clone;
          let D_clone_1 = Clone::clone(D);
          let L_clone_1 = Clone::clone(L);
          let x_clone = Clone::clone(x);
          let callback_2: Rc<dyn Fn(Int63, (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>)> = Rc::new({
            let __anf_capture_46 = y;
            move |z: Int63, st: (Array<Int63>, Array<Int63>)| -> (Array<Int63>, Array<Int63>) {
              let tmp = Clone::clone(&D_clone_1);
              let tmp_1 = Clone::clone(&L_clone_1);
              let tmp_2 = Clone::clone(&x_clone);
              let tmp_3 = Clone::clone(&__anf_capture_46);
              cell(tmp, tmp_1, tmp_2, tmp_3, z, st)
            }
          });
          let D_clone_2 = Clone::clone(D);
          for_::<(Array<Int63>, Array<Int63>)>(callback_2, y, D_clone_2, st)
        }
      });
      let D_clone_3 = Clone::clone(D);
      for_::<(Array<Int63>, Array<Int63>)>(callback_1, x, D_clone_3, st)
    }
  });
  for_::<(Array<Int63>, Array<Int63>)>(callback, int63!(1), D, (Array::<Int63>::make(L, int63!(0)), Array::<Int63>::make(L, int63!(0))))
}

// Rocq: Cuboidslicinggame.spec.Prelude.opponent
pub fn opponent(who: player) -> player {
  match who {
    player::Ruben => {
      player::Albert
    },
    player::Albert => {
      player::Ruben
    },
  }
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.winner_impl
// Variant: uncurried
pub fn winner_impl(s: player, xs: Array<Int63>, ys: Array<Int63>, zs: Array<Int63>) -> player {
  let n = xs.length();
  let xs_clone = Clone::clone(&xs);
  let ys_clone = Clone::clone(&ys);
  let zs_clone = Clone::clone(&zs);
  let callback: Rc<dyn Fn(Int63, Int63) -> Int63> = Rc::new({
    move |i: Int63, m: Int63| -> Int63 {
      let xs = &xs_clone;
      let ys = &ys_clone;
      let zs = &zs_clone;
      let tmp = xs.get_cloned(i);
      let tmp_1 = ys.get_cloned(i);
      let tmp_2 = zs.get_cloned(i);
      let tmp_3 = imax(tmp_1, tmp_2);
      let tmp_4 = imax(tmp, tmp_3);
      imax(m, tmp_4)
    }
  });
  let M = for_::<Int63>(callback, int63!(0), n, int63!(0));
  let D = M + int63!(1);
  let L = D * D * D;
  let T = fst::<Array<Int63>, Array<Int63>>(table(D, L));
  let xs_clone_1 = Clone::clone(&xs);
  let ys_clone_1 = Clone::clone(&ys);
  let zs_clone_1 = Clone::clone(&zs);
  let T_clone = Clone::clone(&T);
  let callback_1: Rc<dyn Fn(Int63, Int63) -> Int63> = Rc::new({
    let __anf_capture_123 = D;
    move |i: Int63, acc: Int63| -> Int63 {
      let xs = &xs_clone_1;
      let ys = &ys_clone_1;
      let zs = &zs_clone_1;
      let T = &T_clone;
      let D = &__anf_capture_123;
      let tmp_5 = xs.get_cloned(i);
      let tmp_6 = ys.get_cloned(i);
      let tmp_7 = zs.get_cloned(i);
      let tmp_8 = look(T, Clone::clone(D), tmp_5, tmp_6, tmp_7);
      acc ^ tmp_8
    }
  });
  let gx = for_::<Int63>(callback_1, int63!(0), n, int63!(0));
  if gx == int63!(0) {
    std::mem::drop(T);
    std::mem::drop(xs);
    std::mem::drop(ys);
    std::mem::drop(zs);
    opponent(s)
  } else {
    std::mem::drop(T);
    std::mem::drop(xs);
    std::mem::drop(ys);
    std::mem::drop(zs);
    s
  }
}
