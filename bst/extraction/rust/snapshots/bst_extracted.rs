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

pub enum rbt {
  RE,
  RN(color, Rc<rbt>, Int63, Rc<rbt>),
}

impl Clone for rbt {
  fn clone(&self) -> Self {
    match self {
      rbt::RE => rbt::RE,
      rbt::RN(__field0, __field1, __field2, __field3) => rbt::RN(Clone::clone(__field0), Clone::clone(__field1), Clone::clone(__field2), Clone::clone(__field3)),
    }
  }
}

#[derive(Clone, Copy)]
pub enum color {
  Red,
  Black,
}

pub type uint = Int63;

// Rocq: Bst.bst_implem.around
pub fn around_curried() -> Rc<dyn Fn(Int63) -> Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(Int63) -> Rc<dyn Fn(Int63) -> (Int63, Int63)>>>> {
  let callback: Rc<dyn Fn(Int63, Rc<rbt>) -> Rc<dyn Fn(Int63) -> Rc<dyn Fn(Int63) -> (Int63, Int63)>>> = Rc::new(move |y: Int63, t: Rc<rbt>| -> Rc<dyn Fn(Int63) -> Rc<dyn Fn(Int63) -> (Int63, Int63)>> {
    let tmp: Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(Int63) -> Rc<dyn Fn(Int63) -> (Int63, Int63)>>> = around_curried_owned(y);
    let tmp_1: &Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(Int63) -> Rc<dyn Fn(Int63) -> (Int63, Int63)>>> = &tmp;
    let tmp_2: Rc<dyn Fn(Int63) -> Rc<dyn Fn(Int63) -> (Int63, Int63)>> = tmp_1(t);
    std::mem::drop(tmp);
    tmp_2
  });
  let callback_1: Rc<dyn Fn(Int63) -> Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(Int63) -> Rc<dyn Fn(Int63) -> (Int63, Int63)>>>> = Rc::new({
    move |y: Int63| -> Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(Int63) -> Rc<dyn Fn(Int63) -> (Int63, Int63)>>> {
      let v18 = &callback;
      let tmp_3: Rc<dyn Fn(Int63, Rc<rbt>) -> Rc<dyn Fn(Int63) -> Rc<dyn Fn(Int63) -> (Int63, Int63)>>> = Rc::clone(v18);
      let callback_2: Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(Int63) -> Rc<dyn Fn(Int63) -> (Int63, Int63)>>> = Rc::new({
        move |t: Rc<rbt>| -> Rc<dyn Fn(Int63) -> Rc<dyn Fn(Int63) -> (Int63, Int63)>> {
          let v26 = &tmp_3;
          let tmp_4: Rc<dyn Fn(Int63) -> Rc<dyn Fn(Int63) -> (Int63, Int63)>> = v26(Clone::clone(&y), t);
          tmp_4
        }
      });
      callback_2
    }
  });
  callback_1
}

// Rocq: Bst.bst_implem.around (local: around)
// Variant: lifted
pub fn around_curried_owned(y: Int63) -> Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(Int63) -> Rc<dyn Fn(Int63) -> (Int63, Int63)>>> {
  let callback: Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(Int63) -> Rc<dyn Fn(Int63) -> (Int63, Int63)>>> = Rc::new({
    move |t: Rc<rbt>| -> Rc<dyn Fn(Int63) -> Rc<dyn Fn(Int63) -> (Int63, Int63)>> {
      let y = &y;
      let y_clone = Clone::clone(y);
      let callback_1: Rc<dyn Fn(Int63) -> Rc<dyn Fn(Int63) -> (Int63, Int63)>> = Rc::new({
        move |p: Int63| -> Rc<dyn Fn(Int63) -> (Int63, Int63)> {
          let y = &y_clone;
          let t = &t;
          let y_clone_1 = Clone::clone(y);
          let t_clone = Rc::clone(t);
          let callback_2: Rc<dyn Fn(Int63) -> (Int63, Int63)> = Rc::new({
            move |s: Int63| -> (Int63, Int63) {
              let y = &y_clone_1;
              let t = &t_clone;
              let tmp = around(Clone::clone(y), t, Clone::clone(&p), s);
              tmp
            }
          });
          callback_2
        }
      });
      callback_1
    }
  });
  callback
}

// Rocq: Bst.bst_implem.around (local: around)
// Variant: uncurried, lifted
pub fn around_owned(y: Int63, t: Rc<rbt>, p: Int63, s: Int63) -> (Int63, Int63) {
  let (v4, v5) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v5);
  match v4 {
    rbt::RE => {
      (p, s)
    },
    rbt::RN(_v21, v23, v25, v27) => {
      if y < v25 {
        std::mem::drop(v27);
        around_owned(y, v23, p, v25)
      } else {
        std::mem::drop(v23);
        around_owned(y, v27, v25, s)
      }
    },
  }
}

// Rocq: Bst.bst_implem.around (local: around)
// Variant: borrowed, uncurried, lifted
pub fn around(y: Int63, t: &Rc<rbt>, p: Int63, s: Int63) -> (Int63, Int63) {
  let y_1 = y;
  let p_1 = p;
  let s_1 = s;
  let tmp = t;
  match &**tmp {
    rbt::RE => {
      (p_1, s_1)
    },
    rbt::RN(_r, k, l, c) => {
      let l_clone = Clone::clone(l);
      if y_1 < l_clone {
        let k_clone = Rc::clone(k);
        let l_clone_1 = Clone::clone(l);
        around_owned(y_1, k_clone, p_1, l_clone_1)
      } else {
        let c_clone = Rc::clone(c);
        let l_clone_2 = Clone::clone(l);
        around_owned(y_1, c_clone, l_clone_2, s_1)
      }
    },
  }
}

// Rocq: Bst.bst_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Bst.bst_implem.around
// Variant: uncurried
pub fn around_2(y: Int63, t: Rc<rbt>, p: Int63, s: Int63) -> (Int63, Int63) {
  around_1(y, t, p, s)
}

// Rocq: Bst.bst_implem.around (local: around)
// Variant: uncurried, lifted
pub fn around_1(y: Int63, t: Rc<rbt>, p: Int63, s: Int63) -> (Int63, Int63) {
  let (v4, v5) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v5);
  match v4 {
    rbt::RE => {
      (p, s)
    },
    rbt::RN(_v21, v23, v25, v27) => {
      if y < v25 {
        std::mem::drop(v27);
        around_1(y, v23, p, v25)
      } else {
        std::mem::drop(v23);
        around_1(y, v27, v25, s)
      }
    },
  }
}

// Rocq: Bst.bst_implem.imax
// Variant: uncurried
pub fn imax(u: Int63, v: Int63) -> Int63 {
  if u < v {
    v
  } else {
    u
  }
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

// Rocq: Bst.bst_implem.make_black
pub fn make_black(t: Rc<rbt>) -> Rc<rbt> {
  let (v1, v2) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  match v1 {
    rbt::RE => {
      __rocq_reuse::rebuild(v2, rbt::RE)
    },
    rbt::RN(_v15, v17, v19, v21) => {
      __rocq_reuse::rebuild(v2, rbt::RN(color::Black, v17, v19, v21))
    },
  }
}

// Rocq: Bst.bst_implem.lbal
// Variant: uncurried
pub fn lbal(l: Rc<rbt>, k: Int63, r: Rc<rbt>) -> Rc<rbt> {
  match &*l {
    rbt::RE => {
      Rc::new(rbt::RN(color::Black, l, k, r))
    },
    rbt::RN(c, x, a_1, c0) => {
      match c {
        color::Red => {
          match &**x {
            rbt::RE => {
              match &**c0 {
                rbt::RE => {
                  Rc::new(rbt::RN(color::Black, l, k, r))
                },
                rbt::RN(c_1, y, b_1, c1) => {
                  match c_1 {
                    color::Red => {
                      let tmp = Rc::new(rbt::RN(color::Black, Rc::clone(x), Clone::clone(a_1), Rc::clone(y)));
                      let tmp_1 = Rc::new(rbt::RN(color::Black, Rc::clone(c1), k, r));
                      let b_clone = Clone::clone(b_1);
                      std::mem::drop(l);
                      Rc::new(rbt::RN(color::Red, tmp, b_clone, tmp_1))
                    },
                    color::Black => {
                      Rc::new(rbt::RN(color::Black, l, k, r))
                    },
                  }
                },
              }
            },
            rbt::RN(b_1, x_1, a_2, c1) => {
              match b_1 {
                color::Red => {
                  let x_clone = Rc::clone(x_1);
                  let a_clone = Clone::clone(a_2);
                  let c1_clone = Rc::clone(c1);
                  let tmp_2 = Rc::new(rbt::RN(color::Black, x_clone, a_clone, c1_clone));
                  let tmp_3 = Rc::new(rbt::RN(color::Black, Rc::clone(c0), k, r));
                  let a_clone_1 = Clone::clone(a_1);
                  std::mem::drop(l);
                  Rc::new(rbt::RN(color::Red, tmp_2, a_clone_1, tmp_3))
                },
                color::Black => {
                  match &**c0 {
                    rbt::RE => {
                      Rc::new(rbt::RN(color::Black, l, k, r))
                    },
                    rbt::RN(c_1, y, b_2, c2) => {
                      match c_1 {
                        color::Red => {
                          let tmp_4 = Rc::new(rbt::RN(color::Black, Rc::clone(x), Clone::clone(a_1), Rc::clone(y)));
                          let tmp_5 = Rc::new(rbt::RN(color::Black, Rc::clone(c2), k, r));
                          let b_clone_1 = Clone::clone(b_2);
                          std::mem::drop(l);
                          Rc::new(rbt::RN(color::Red, tmp_4, b_clone_1, tmp_5))
                        },
                        color::Black => {
                          Rc::new(rbt::RN(color::Black, l, k, r))
                        },
                      }
                    },
                  }
                },
              }
            },
          }
        },
        color::Black => {
          Rc::new(rbt::RN(color::Black, l, k, r))
        },
      }
    },
  }
}

// Rocq: Bst.bst_implem.rbal
// Variant: uncurried
pub fn rbal(l: Rc<rbt>, k: Int63, r: Rc<rbt>) -> Rc<rbt> {
  match &*r {
    rbt::RE => {
      Rc::new(rbt::RN(color::Black, l, k, r))
    },
    rbt::RN(d, y, b_1, c0) => {
      match d {
        color::Red => {
          match &**y {
            rbt::RE => {
              match &**c0 {
                rbt::RE => {
                  Rc::new(rbt::RN(color::Black, l, k, r))
                },
                rbt::RN(d_1, z, c, c1) => {
                  match d_1 {
                    color::Red => {
                      let tmp = Rc::new(rbt::RN(color::Black, l, k, Rc::clone(y)));
                      let z_clone = Rc::clone(z);
                      let c_clone = Clone::clone(c);
                      let c1_clone = Rc::clone(c1);
                      let tmp_1 = Rc::new(rbt::RN(color::Black, z_clone, c_clone, c1_clone));
                      let b_clone = Clone::clone(b_1);
                      std::mem::drop(r);
                      Rc::new(rbt::RN(color::Red, tmp, b_clone, tmp_1))
                    },
                    color::Black => {
                      Rc::new(rbt::RN(color::Black, l, k, r))
                    },
                  }
                },
              }
            },
            rbt::RN(c, y_1, b_2, c1) => {
              match c {
                color::Red => {
                  let tmp_2 = Rc::new(rbt::RN(color::Black, l, k, Rc::clone(y_1)));
                  let tmp_3 = Rc::new(rbt::RN(color::Black, Rc::clone(c1), Clone::clone(b_1), Rc::clone(c0)));
                  let b_clone_1 = Clone::clone(b_2);
                  std::mem::drop(r);
                  Rc::new(rbt::RN(color::Red, tmp_2, b_clone_1, tmp_3))
                },
                color::Black => {
                  match &**c0 {
                    rbt::RE => {
                      Rc::new(rbt::RN(color::Black, l, k, r))
                    },
                    rbt::RN(d_1, z, c_1, c2) => {
                      match d_1 {
                        color::Red => {
                          let tmp_4 = Rc::new(rbt::RN(color::Black, l, k, Rc::clone(y)));
                          let z_clone_1 = Rc::clone(z);
                          let c_clone_1 = Clone::clone(c_1);
                          let c2_clone = Rc::clone(c2);
                          let tmp_5 = Rc::new(rbt::RN(color::Black, z_clone_1, c_clone_1, c2_clone));
                          let b_clone_2 = Clone::clone(b_1);
                          std::mem::drop(r);
                          Rc::new(rbt::RN(color::Red, tmp_4, b_clone_2, tmp_5))
                        },
                        color::Black => {
                          Rc::new(rbt::RN(color::Black, l, k, r))
                        },
                      }
                    },
                  }
                },
              }
            },
          }
        },
        color::Black => {
          Rc::new(rbt::RN(color::Black, l, k, r))
        },
      }
    },
  }
}

// Rocq: Bst.bst_implem.rb_ins
// Variant: uncurried
pub fn rb_ins_1(y: Int63, t: Rc<rbt>) -> Rc<rbt> {
  rb_ins(y, t)
}

// Rocq: Bst.bst_implem.rb_ins (local: rb_ins)
// Variant: uncurried, lifted
pub fn rb_ins(y: Int63, t: Rc<rbt>) -> Rc<rbt> {
  match &*t {
    rbt::RE => {
      std::mem::drop(t);
      let tmp = Rc::new(rbt::RE);
      let tmp_1 = Rc::new(rbt::RE);
      Rc::new(rbt::RN(color::Red, tmp, y, tmp_1))
    },
    rbt::RN(r, k, l, c) => {
      let l_clone = Clone::clone(l);
      if y < l_clone {
        match r {
          color::Red => {
            let tmp_2 = rb_ins(y, Rc::clone(k));
            let l_clone_1 = Clone::clone(l);
            let c_clone = Rc::clone(c);
            std::mem::drop(t);
            Rc::new(rbt::RN(color::Red, tmp_2, l_clone_1, c_clone))
          },
          color::Black => {
            let tmp_3 = rb_ins(y, Rc::clone(k));
            let l_clone_2 = Clone::clone(l);
            let c_clone_1 = Rc::clone(c);
            std::mem::drop(t);
            lbal(tmp_3, l_clone_2, c_clone_1)
          },
        }
      } else {
        let l_clone_3 = Clone::clone(l);
        if l_clone_3 < y {
          match r {
            color::Red => {
              let tmp_4 = rb_ins(y, Rc::clone(c));
              let k_clone = Rc::clone(k);
              let l_clone_4 = Clone::clone(l);
              std::mem::drop(t);
              Rc::new(rbt::RN(color::Red, k_clone, l_clone_4, tmp_4))
            },
            color::Black => {
              let tmp_5 = rb_ins(y, Rc::clone(c));
              let k_clone_1 = Rc::clone(k);
              let l_clone_5 = Clone::clone(l);
              std::mem::drop(t);
              rbal(k_clone_1, l_clone_5, tmp_5)
            },
          }
        } else {
          t
        }
      }
    },
  }
}

// Rocq: Bst.bst_implem.rb_insert
// Variant: uncurried
pub fn rb_insert(y: Int63, t: Rc<rbt>) -> Rc<rbt> {
  make_black(rb_ins_1(y, t))
}

// Rocq: Bst.bst_implem.loop
// Variant: uncurried
pub fn loop__1(x: Array<Int63>, n: Int63, j: Int63, t: Rc<rbt>, d: Array<Int63>, c: Int63, o: Array<Int63>) -> Array<Int63> {
  loop_(x, n, j, t, d, c, o, ())
}

// Rocq: Bst.bst_implem.loop (local: loop)
// Variant: uncurried, lifted
pub fn loop_(x: Array<Int63>, n: Int63, j: Int63, t: Rc<rbt>, d: Array<Int63>, c: Int63, o: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = j < n;
  match bdec(tmp) {
    sumbool::left => {
      let y = x.get_cloned(j);
      let tmp_1 = n + int63!(1);
      let t_clone = Rc::clone(&t);
      let ps = around_2(y, t_clone, int63!(0), tmp_1);
      let ps_clone = Clone::clone(&ps);
      let tmp_2 = d.get_cloned(fst::<Int63, Int63>(ps_clone));
      let tmp_3 = d.get_cloned(snd::<Int63, Int63>(ps));
      let e = int63!(1) + imax(tmp_2, tmp_3);
      let c_ = c + e - int63!(1);
      let tmp_4 = j + int63!(1);
      let tmp_5 = rb_insert(y, t);
      let tmp_6 = d.set(y, e);
      let tmp_7 = o.set(j, c_);
      loop_(x, n, tmp_4, tmp_5, tmp_6, c_, tmp_7, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(t);
      std::mem::drop(d);
      o
    },
  }
}

// Rocq: Bst.bst_implem.bst_impl
pub fn bst_impl(x: Array<Int63>) -> Array<Int63> {
  let n = x.length();
  let tmp = Rc::new(rbt::RE);
  let tmp_1 = Array::<Int63>::make(n + int63!(2), int63!(0));
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  loop__1(x, n, int63!(0), tmp, tmp_1, int63!(0), tmp_2)
}
std::thread_local! { static __rocq_global_55: Rc<dyn Fn(Int63) -> Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(Int63) -> Rc<dyn Fn(Int63) -> (Int63, Int63)>>>> = around_curried(); }