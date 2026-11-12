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

pub enum rbt {
  RE,
  RN(color, Rc<rbt>, u64, Rc<rbt>),
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

pub type uint = u64;

// Rocq: Bst.bst_implem.around
pub fn around_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>>> {
  let v0 = {
    move |y: u64, t: Rc<rbt>| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>> {
      let v6: Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>> = around_curried_owned(y);
      let v7: &Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>> = &v6;
      let v10: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>> = v7(t);
      std::mem::drop(v6);
      v10
    }
  };
  let v13: Rc<dyn Fn(u64, Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>> = Rc::new(v0);
  let v17 = {
    move |y: u64| -> Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>> {
      let v18 = &v13;
      let v21: Rc<dyn Fn(u64, Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>> = Rc::clone(v18);
      let v25 = {
        move |t: Rc<rbt>| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>> {
          let v26 = &v21;
          let v35: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>> = v26(Clone::clone(&y), t);
          v35
        }
      };
      let v38: Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>> = Rc::new(v25);
      v38
    }
  };
  let v42: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>>> = Rc::new(v17);
  v42
}

// Rocq: Bst.bst_implem.around (local: around)
// Variant: lifted
pub fn around_curried_owned(y: u64) -> Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>> {
  let v3 = {
    move |t: Rc<rbt>| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>> {
      let y = &y;
      let v8 = Clone::clone(y);
      let v11 = {
        move |p: u64| -> Rc<dyn Fn(u64) -> (u64, u64)> {
          let y = &v8;
          let t = &t;
          let v18 = Clone::clone(y);
          let v20 = Rc::clone(t);
          let v23 = {
            move |s: u64| -> (u64, u64) {
              let y = &v18;
              let t = &v20;
              let v39 = around(Clone::clone(y), t, Clone::clone(&p), s);
              v39
            }
          };
          let v42: Rc<dyn Fn(u64) -> (u64, u64)> = Rc::new(v23);
          v42
        }
      };
      let v46: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>> = Rc::new(v11);
      v46
    }
  };
  let v50: Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>> = Rc::new(v3);
  v50
}

// Rocq: Bst.bst_implem.around (local: around)
// Variant: uncurried, lifted
pub fn around_owned(y: u64, t: Rc<rbt>, p: u64, s: u64) -> (u64, u64) {
  let (v4, v5) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v5);
  match v4 {
    rbt::RE => {
      (p, s)
    },
    rbt::RN(_v21, v23, v25, v27) => {
      match ltb(y, v25) {
        true => {
          std::mem::drop(v27);
          around_owned(y, v23, p, v25)
        },
        false => {
          std::mem::drop(v23);
          around_owned(y, v27, v25, s)
        },
      }
    },
  }
}

// Rocq: Bst.bst_implem.around (local: around)
// Variant: borrowed, uncurried, lifted
pub fn around(y: u64, t: &Rc<rbt>, p: u64, s: u64) -> (u64, u64) {
  let y_1 = y;
  let p_1 = p;
  let s_1 = s;
  let v7 = t;
  match &**v7 {
    rbt::RE => {
      (p_1, s_1)
    },
    rbt::RN(_r, k, l, c) => {
      let v29 = Clone::clone(l);
      match ltb(y_1, v29) {
        true => {
          let v36 = Rc::clone(k);
          let v40 = Clone::clone(l);
          around_owned(y_1, v36, p_1, v40)
        },
        false => {
          let v48 = Rc::clone(c);
          let v50 = Clone::clone(l);
          around_owned(y_1, v48, v50, s_1)
        },
      }
    },
  }
}

// Rocq: Bst.bst_implem.bst
pub fn bst() -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: fn(Rc<Array<u64>>) -> Rc<Array<u64>> = bst_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Bst.bst_implem.bdec
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

// Rocq: Bst.bst_implem.around
// Variant: uncurried
pub fn around_2(y: u64, t: Rc<rbt>, p: u64, s: u64) -> (u64, u64) {
  around_1(y, t, p, s)
}

// Rocq: Bst.bst_implem.around (local: around)
// Variant: uncurried, lifted
pub fn around_1(y: u64, t: Rc<rbt>, p: u64, s: u64) -> (u64, u64) {
  let (v4, v5) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v5);
  match v4 {
    rbt::RE => {
      (p, s)
    },
    rbt::RN(_v21, v23, v25, v27) => {
      match ltb(y, v25) {
        true => {
          std::mem::drop(v27);
          around_1(y, v23, p, v25)
        },
        false => {
          std::mem::drop(v23);
          around_1(y, v27, v25, s)
        },
      }
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Bst.bst_implem.imax
// Variant: uncurried
pub fn imax(u: u64, v: u64) -> u64 {
  match ltb(u, v) {
    true => {
      v
    },
    false => {
      u
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let v3 = Clone::clone((&(&p).1));
  std::mem::drop(p);
  v3
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
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
pub fn lbal(l: Rc<rbt>, k: u64, r: Rc<rbt>) -> Rc<rbt> {
  match &*l {
    rbt::RE => {
      Rc::new(rbt::RN(color::Black, l, k, r))
    },
    rbt::RN(c, x, a, c0) => {
      match c {
        color::Red => {
          match &**x {
            rbt::RE => {
              match &**c0 {
                rbt::RE => {
                  Rc::new(rbt::RN(color::Black, l, k, r))
                },
                rbt::RN(c_1, y, b, c1) => {
                  match c_1 {
                    color::Red => {
                      let v69 = Rc::new(rbt::RN(color::Black, Rc::clone(x), Clone::clone(a), Rc::clone(y)));
                      let v82 = Rc::new(rbt::RN(color::Black, Rc::clone(c1), k, r));
                      let v87 = Clone::clone(b);
                      std::mem::drop(l);
                      Rc::new(rbt::RN(color::Red, v69, v87, v82))
                    },
                    color::Black => {
                      Rc::new(rbt::RN(color::Black, l, k, r))
                    },
                  }
                },
              }
            },
            rbt::RN(b, x_1, a_1, c1) => {
              match b {
                color::Red => {
                  let v133 = Rc::clone(x_1);
                  let v135 = Clone::clone(a_1);
                  let v137 = Rc::clone(c1);
                  let v140 = Rc::new(rbt::RN(color::Black, v133, v135, v137));
                  let v153 = Rc::new(rbt::RN(color::Black, Rc::clone(c0), k, r));
                  let v158 = Clone::clone(a);
                  std::mem::drop(l);
                  Rc::new(rbt::RN(color::Red, v140, v158, v153))
                },
                color::Black => {
                  match &**c0 {
                    rbt::RE => {
                      Rc::new(rbt::RN(color::Black, l, k, r))
                    },
                    rbt::RN(c_1, y, b_1, c2) => {
                      match c_1 {
                        color::Red => {
                          let v206 = Rc::new(rbt::RN(color::Black, Rc::clone(x), Clone::clone(a), Rc::clone(y)));
                          let v219 = Rc::new(rbt::RN(color::Black, Rc::clone(c2), k, r));
                          let v224 = Clone::clone(b_1);
                          std::mem::drop(l);
                          Rc::new(rbt::RN(color::Red, v206, v224, v219))
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
pub fn rbal(l: Rc<rbt>, k: u64, r: Rc<rbt>) -> Rc<rbt> {
  match &*r {
    rbt::RE => {
      Rc::new(rbt::RN(color::Black, l, k, r))
    },
    rbt::RN(d, y, b, c0) => {
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
                      let v69 = Rc::new(rbt::RN(color::Black, l, k, Rc::clone(y)));
                      let v75 = Rc::clone(z);
                      let v77 = Clone::clone(c);
                      let v79 = Rc::clone(c1);
                      let v82 = Rc::new(rbt::RN(color::Black, v75, v77, v79));
                      let v87 = Clone::clone(b);
                      std::mem::drop(r);
                      Rc::new(rbt::RN(color::Red, v69, v87, v82))
                    },
                    color::Black => {
                      Rc::new(rbt::RN(color::Black, l, k, r))
                    },
                  }
                },
              }
            },
            rbt::RN(c, y_1, b_1, c1) => {
              match c {
                color::Red => {
                  let v140 = Rc::new(rbt::RN(color::Black, l, k, Rc::clone(y_1)));
                  let v153 = Rc::new(rbt::RN(color::Black, Rc::clone(c1), Clone::clone(b), Rc::clone(c0)));
                  let v158 = Clone::clone(b_1);
                  std::mem::drop(r);
                  Rc::new(rbt::RN(color::Red, v140, v158, v153))
                },
                color::Black => {
                  match &**c0 {
                    rbt::RE => {
                      Rc::new(rbt::RN(color::Black, l, k, r))
                    },
                    rbt::RN(d_1, z, c_1, c2) => {
                      match d_1 {
                        color::Red => {
                          let v206 = Rc::new(rbt::RN(color::Black, l, k, Rc::clone(y)));
                          let v212 = Rc::clone(z);
                          let v214 = Clone::clone(c_1);
                          let v216 = Rc::clone(c2);
                          let v219 = Rc::new(rbt::RN(color::Black, v212, v214, v216));
                          let v224 = Clone::clone(b);
                          std::mem::drop(r);
                          Rc::new(rbt::RN(color::Red, v206, v224, v219))
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
pub fn rb_ins_1(y: u64, t: Rc<rbt>) -> Rc<rbt> {
  rb_ins(y, t)
}

// Rocq: Bst.bst_implem.rb_ins (local: rb_ins)
// Variant: uncurried, lifted
pub fn rb_ins(y: u64, t: Rc<rbt>) -> Rc<rbt> {
  match &*t {
    rbt::RE => {
      std::mem::drop(t);
      let v8 = Rc::new(rbt::RE);
      let v11 = Rc::new(rbt::RE);
      Rc::new(rbt::RN(color::Red, v8, y, v11))
    },
    rbt::RN(r, k, l, c) => {
      let v37 = Clone::clone(l);
      match ltb(y, v37) {
        true => {
          match r {
            color::Red => {
              let v48 = rb_ins(y, Rc::clone(k));
              let v54 = Clone::clone(l);
              let v55 = Rc::clone(c);
              std::mem::drop(t);
              Rc::new(rbt::RN(color::Red, v48, v54, v55))
            },
            color::Black => {
              let v69 = rb_ins(y, Rc::clone(k));
              let v72 = Clone::clone(l);
              let v73 = Rc::clone(c);
              std::mem::drop(t);
              lbal(v69, v72, v73)
            },
          }
        },
        false => {
          let v83 = Clone::clone(l);
          match ltb(v83, y) {
            true => {
              match r {
                color::Red => {
                  let v96 = rb_ins(y, Rc::clone(c));
                  let v100 = Rc::clone(k);
                  let v101 = Clone::clone(l);
                  std::mem::drop(t);
                  Rc::new(rbt::RN(color::Red, v100, v101, v96))
                },
                color::Black => {
                  let v116 = rb_ins(y, Rc::clone(c));
                  let v118 = Rc::clone(k);
                  let v119 = Clone::clone(l);
                  std::mem::drop(t);
                  rbal(v118, v119, v116)
                },
              }
            },
            false => {
              t
            },
          }
        },
      }
    },
  }
}

// Rocq: Bst.bst_implem.rb_insert
// Variant: uncurried
pub fn rb_insert(y: u64, t: Rc<rbt>) -> Rc<rbt> {
  make_black(rb_ins_1(y, t))
}

// Rocq: Bst.bst_implem.loop
// Variant: uncurried
pub fn loop__1(x: Rc<Array<u64>>, n: u64, j: u64, t: Rc<rbt>, d: Rc<Array<u64>>, c: u64, o: Rc<Array<u64>>) -> Rc<Array<u64>> {
  loop_(x, n, j, t, d, c, o, ())
}

// Rocq: Bst.bst_implem.loop (local: loop)
// Variant: uncurried, lifted
pub fn loop_(x: Rc<Array<u64>>, n: u64, j: u64, t: Rc<rbt>, d: Rc<Array<u64>>, c: u64, o: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v15 = ltb(j, n);
  match bdec(v15) {
    sumbool::left => {
      let v19 = &x;
      let y = rocq_array::get::<u64>(&v19, j);
      let v33 = add(n, 1u64);
      let v38 = Rc::clone(&t);
      let ps = around_2(y, v38, 0u64, v33);
      let v50 = Clone::clone(&ps);
      let v52 = fst::<u64, u64>(v50);
      let v53 = &d;
      let v56 = rocq_array::get::<u64>(&v53, v52);
      let v60 = snd::<u64, u64>(ps);
      let v61 = &d;
      let v64 = rocq_array::get::<u64>(&v61, v60);
      let e = add(1u64, imax(v56, v64));
      let c_ = sub(add(c, e), 1u64);
      let v96 = add(j, 1u64);
      let v102 = rb_insert(y, t);
      let v109 = rocq_array::set::<u64>(d, y, e);
      let v116 = rocq_array::set::<u64>(o, j, c_);
      loop_(x, n, v96, v102, v109, c_, v116, ())
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
pub fn bst_impl(x: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v1 = &x;
  let n = rocq_array::length::<u64>(&v1);
  let v8 = Rc::new(rbt::RE);
  let v23 = rocq_array::make::<u64>(add(n, 2u64), 0u64);
  let v32 = rocq_array::make::<u64>(n, 0u64);
  loop__1(x, n, 0u64, v8, v23, 0u64, v32)
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

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = __rocq_global_448.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_55: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>>> = around_curried(); }
std::thread_local! { static __rocq_global_448: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = bst(); }