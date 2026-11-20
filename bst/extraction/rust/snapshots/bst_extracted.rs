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
  let callback: Rc<dyn Fn(u64, Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>> = Rc::new(move |y: u64, t: Rc<rbt>| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>> {
    let tmp: Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>> = around_curried_owned(y);
    let tmp_1: &Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>> = &tmp;
    let tmp_2: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>> = tmp_1(t);
    std::mem::drop(tmp);
    tmp_2
  });
  let callback_1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>>> = Rc::new({
    move |y: u64| -> Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>> {
      let v18 = &callback;
      let tmp_3: Rc<dyn Fn(u64, Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>> = Rc::clone(v18);
      let callback_2: Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>> = Rc::new({
        move |t: Rc<rbt>| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>> {
          let v26 = &tmp_3;
          let tmp_4: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>> = v26(Clone::clone(&y), t);
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
pub fn around_curried_owned(y: u64) -> Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>> {
  let callback: Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>> = Rc::new({
    move |t: Rc<rbt>| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>> {
      let y = &y;
      let y_clone = Clone::clone(y);
      let callback_1: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>> = Rc::new({
        move |p: u64| -> Rc<dyn Fn(u64) -> (u64, u64)> {
          let y = &y_clone;
          let t = &t;
          let y_clone_1 = Clone::clone(y);
          let t_clone = Rc::clone(t);
          let callback_2: Rc<dyn Fn(u64) -> (u64, u64)> = Rc::new({
            move |s: u64| -> (u64, u64) {
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
pub fn around_owned(y: u64, t: Rc<rbt>, p: u64, s: u64) -> (u64, u64) {
  let (v4, v5) = __rocq_reuse::reset(t, |__payload| Clone::clone(__payload));
  std::mem::drop(v5);
  match v4 {
    rbt::RE => {
      (p, s)
    },
    rbt::RN(_v21, v23, v25, v27) => {
      if ltb(y, v25) {
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
pub fn around(y: u64, t: &Rc<rbt>, p: u64, s: u64) -> (u64, u64) {
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
      if ltb(y_1, l_clone) {
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Bst.bst_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
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
      if ltb(y, v25) {
        std::mem::drop(v27);
        around_1(y, v23, p, v25)
      } else {
        std::mem::drop(v23);
        around_1(y, v27, v25, s)
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
  if ltb(u, v) {
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
                      let tmp = Rc::new(rbt::RN(color::Black, Rc::clone(x), Clone::clone(a), Rc::clone(y)));
                      let tmp_1 = Rc::new(rbt::RN(color::Black, Rc::clone(c1), k, r));
                      let b_clone = Clone::clone(b);
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
            rbt::RN(b, x_1, a_1, c1) => {
              match b {
                color::Red => {
                  let x_clone = Rc::clone(x_1);
                  let a_clone = Clone::clone(a_1);
                  let c1_clone = Rc::clone(c1);
                  let tmp_2 = Rc::new(rbt::RN(color::Black, x_clone, a_clone, c1_clone));
                  let tmp_3 = Rc::new(rbt::RN(color::Black, Rc::clone(c0), k, r));
                  let a_clone_1 = Clone::clone(a);
                  std::mem::drop(l);
                  Rc::new(rbt::RN(color::Red, tmp_2, a_clone_1, tmp_3))
                },
                color::Black => {
                  match &**c0 {
                    rbt::RE => {
                      Rc::new(rbt::RN(color::Black, l, k, r))
                    },
                    rbt::RN(c_1, y, b_1, c2) => {
                      match c_1 {
                        color::Red => {
                          let tmp_4 = Rc::new(rbt::RN(color::Black, Rc::clone(x), Clone::clone(a), Rc::clone(y)));
                          let tmp_5 = Rc::new(rbt::RN(color::Black, Rc::clone(c2), k, r));
                          let b_clone_1 = Clone::clone(b_1);
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
                      let tmp = Rc::new(rbt::RN(color::Black, l, k, Rc::clone(y)));
                      let z_clone = Rc::clone(z);
                      let c_clone = Clone::clone(c);
                      let c1_clone = Rc::clone(c1);
                      let tmp_1 = Rc::new(rbt::RN(color::Black, z_clone, c_clone, c1_clone));
                      let b_clone = Clone::clone(b);
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
            rbt::RN(c, y_1, b_1, c1) => {
              match c {
                color::Red => {
                  let tmp_2 = Rc::new(rbt::RN(color::Black, l, k, Rc::clone(y_1)));
                  let tmp_3 = Rc::new(rbt::RN(color::Black, Rc::clone(c1), Clone::clone(b), Rc::clone(c0)));
                  let b_clone_1 = Clone::clone(b_1);
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
                          let b_clone_2 = Clone::clone(b);
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
pub fn rb_ins_1(y: u64, t: Rc<rbt>) -> Rc<rbt> {
  rb_ins(y, t)
}

// Rocq: Bst.bst_implem.rb_ins (local: rb_ins)
// Variant: uncurried, lifted
pub fn rb_ins(y: u64, t: Rc<rbt>) -> Rc<rbt> {
  match &*t {
    rbt::RE => {
      std::mem::drop(t);
      let tmp = Rc::new(rbt::RE);
      let tmp_1 = Rc::new(rbt::RE);
      Rc::new(rbt::RN(color::Red, tmp, y, tmp_1))
    },
    rbt::RN(r, k, l, c) => {
      let l_clone = Clone::clone(l);
      if ltb(y, l_clone) {
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
        if ltb(l_clone_3, y) {
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
  let tmp = ltb(j, n);
  match bdec(tmp) {
    sumbool::left => {
      let y = rocq_array::get::<u64>(&x, j);
      let tmp_1 = add(n, 1u64);
      let t_clone = Rc::clone(&t);
      let ps = around_2(y, t_clone, 0u64, tmp_1);
      let ps_clone = Clone::clone(&ps);
      let tmp_2 = rocq_array::get::<u64>(&d, fst::<u64, u64>(ps_clone));
      let tmp_3 = rocq_array::get::<u64>(&d, snd::<u64, u64>(ps));
      let e = add(1u64, imax(tmp_2, tmp_3));
      let c_ = sub(add(c, e), 1u64);
      let tmp_4 = add(j, 1u64);
      let tmp_5 = rb_insert(y, t);
      let tmp_6 = rocq_array::set::<u64>(d, y, e);
      let tmp_7 = rocq_array::set::<u64>(o, j, c_);
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
pub fn bst_impl(x: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let n = rocq_array::length::<u64>(&x);
  let tmp = Rc::new(rbt::RE);
  let tmp_1 = rocq_array::make::<u64>(add(n, 2u64), 0u64);
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  loop__1(x, n, 0u64, tmp, tmp_1, 0u64, tmp_2)
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
std::thread_local! { static __rocq_global_55: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<rbt>) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>>> = around_curried(); }