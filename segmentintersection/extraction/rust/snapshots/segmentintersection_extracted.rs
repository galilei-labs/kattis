// Generated from OwnedANF. This printer is not verified.
#[allow(unused_imports)] use std::rc::Rc;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub enum inter<A: 'static> {
  Empty,
  Point { x: A, y: A, denominator: A },
  Segment { start_x: A, start_y: A, end_x: A, end_y: A },
}

impl<A: Clone + 'static> Clone for inter<A> {
  fn clone(&self) -> Self {
    match self {
      inter::Empty => inter::Empty,
      inter::Point { x: __field0, y: __field1, denominator: __field2 } => inter::Point { x: Clone::clone(__field0), y: Clone::clone(__field1), denominator: Clone::clone(__field2) },
      inter::Segment { start_x: __field0, start_y: __field1, end_x: __field2, end_y: __field3 } => inter::Segment { start_x: Clone::clone(__field0), start_y: Clone::clone(__field1), end_x: Clone::clone(__field2), end_y: Clone::clone(__field3) },
    }
  }
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type sint = u64;

// Rocq: Segmentintersection.segmentintersection_implem.intersect
// Variant: uncurried
pub fn intersect() -> Rc<dyn Fn(u64, u64, u64, u64, u64, u64, u64, u64) -> Rc<inter<u64>>> {
  let v0: fn(u64, u64, u64, u64, u64, u64, u64, u64) -> Rc<inter<u64>> = isect_m;
  let v1: Rc<dyn Fn(u64, u64, u64, u64, u64, u64, u64, u64) -> Rc<inter<u64>>> = Rc::new(v0);
  v1
}

// Rocq: Segmentintersection.segmentintersection_implem.intersect
pub fn intersect_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<inter<u64>>>>>>>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<inter<u64>>>>>>>>> = isect_m_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<inter<u64>>>>>>>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
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

// Rocq: Corelib.Init.Datatypes.orb
// Variant: uncurried
pub fn orb(b1: bool, b2: bool) -> bool {
  match b1 {
    true => {
      true
    },
    false => {
      b2
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lesb
// Variant: uncurried
pub fn lesb(v0: u64, v1: u64) -> bool {
  rocq_int63::lesb(v0, v1)
}

// Rocq: Segmentintersection.segmentintersection_implem.onseg_m
// Variant: uncurried
pub fn onseg_m(ax: u64, ay: u64, bx: u64, by_: u64, px: u64, py: u64) -> bool {
  let v49 = eqb(mul(sub(bx, ax), sub(py, ay)), mul(sub(by_, ay), sub(px, ax)));
  let v68 = andb(lesb(ax, px), lesb(px, bx));
  let v86 = andb(lesb(bx, px), lesb(px, ax));
  let v96 = andb(v49, orb(v68, v86));
  let v115 = andb(lesb(ay, py), lesb(py, by_));
  let v133 = andb(lesb(by_, py), lesb(py, ay));
  andb(v96, orb(v115, v133))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb
// Variant: uncurried
pub fn ltsb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltsb(v0, v1)
}

// Rocq: Segmentintersection.segmentintersection_implem.lexle_m
// Variant: uncurried
pub fn lexle_m(ux: u64, uy: u64, vx: u64, vy: u64) -> bool {
  orb(ltsb(ux, vx), andb(eqb(ux, vx), lesb(uy, vy)))
}

// Rocq: Segmentintersection.segmentintersection_implem.lexlt_m
// Variant: uncurried
pub fn lexlt_m(ux: u64, uy: u64, vx: u64, vy: u64) -> bool {
  orb(ltsb(ux, vx), andb(eqb(ux, vx), ltsb(uy, vy)))
}

// Rocq: Segmentintersection.segmentintersection_implem.finish_m
// Variant: uncurried
pub fn finish_m(lox: u64, loy: u64, hix: u64, hiy: u64) -> Rc<inter<u64>> {
  match lexlt_m(lox, loy, hix, hiy) {
    true => {
      Rc::new(inter::<u64>::Segment { start_x: lox, start_y: loy, end_x: hix, end_y: hiy })
    },
    false => {
      let v34 = eqb(lox, hix);
      let v40 = eqb(loy, hiy);
      match andb(v34, v40) {
        true => {
          Rc::new(inter::<u64>::Point { x: lox, y: loy, denominator: 1u64 })
        },
        false => {
          Rc::new(inter::<u64>::Empty)
        },
      }
    },
  }
}

// Rocq: Segmentintersection.segmentintersection_implem.coll2_m
// Variant: uncurried
pub fn coll2_m(p1x: u64, p1y: u64, p2x: u64, p2y: u64, p3x: u64, p3y: u64, p4x: u64, p4y: u64) -> Rc<inter<u64>> {
  match lexle_m(p1x, p1y, p3x, p3y) {
    true => {
      match lexle_m(p2x, p2y, p4x, p4y) {
        true => {
          finish_m(p3x, p3y, p2x, p2y)
        },
        false => {
          finish_m(p3x, p3y, p4x, p4y)
        },
      }
    },
    false => {
      match lexle_m(p2x, p2y, p4x, p4y) {
        true => {
          finish_m(p1x, p1y, p2x, p2y)
        },
        false => {
          finish_m(p1x, p1y, p4x, p4y)
        },
      }
    },
  }
}

// Rocq: Segmentintersection.segmentintersection_implem.coll1_m
// Variant: uncurried
pub fn coll1_m(p1x: u64, p1y: u64, p2x: u64, p2y: u64, x3: u64, y3: u64, x4: u64, y4: u64) -> Rc<inter<u64>> {
  match lexle_m(x3, y3, x4, y4) {
    true => {
      coll2_m(p1x, p1y, p2x, p2y, x3, y3, x4, y4)
    },
    false => {
      coll2_m(p1x, p1y, p2x, p2y, x4, y4, x3, y3)
    },
  }
}

// Rocq: Segmentintersection.segmentintersection_implem.coll_m
// Variant: uncurried
pub fn coll_m(x1: u64, y1: u64, x2: u64, y2: u64, x3: u64, y3: u64, x4: u64, y4: u64) -> Rc<inter<u64>> {
  match lexle_m(x1, y1, x2, y2) {
    true => {
      coll1_m(x1, y1, x2, y2, x3, y3, x4, y4)
    },
    false => {
      coll1_m(x2, y2, x1, y1, x3, y3, x4, y4)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Segmentintersection.segmentintersection_implem.cross_fin_m
// Variant: uncurried
pub fn cross_fin_m(x1: u64, y1: u64, rx: u64, ry: u64, den: u64, tn: u64, un: u64) -> Rc<inter<u64>> {
  let v28 = andb(lesb(0u64, tn), lesb(tn, den));
  let v41 = andb(v28, lesb(0u64, un));
  let v47 = lesb(un, den);
  match andb(v41, v47) {
    true => {
      Rc::new(inter::<u64>::Point { x: add(mul(x1, den), mul(tn, rx)), y: add(mul(y1, den), mul(tn, ry)), denominator: den })
    },
    false => {
      Rc::new(inter::<u64>::Empty)
    },
  }
}

// Rocq: Segmentintersection.segmentintersection_implem.crossing_m
// Variant: uncurried
pub fn crossing_m(x1: u64, y1: u64, rx: u64, ry: u64, den: u64, tn: u64, un: u64) -> Rc<inter<u64>> {
  match ltsb(den, 0u64) {
    true => {
      cross_fin_m(x1, y1, rx, ry, sub(0u64, den), sub(0u64, tn), sub(0u64, un))
    },
    false => {
      cross_fin_m(x1, y1, rx, ry, den, tn, un)
    },
  }
}

// Rocq: Segmentintersection.segmentintersection_implem.isect_m
// Variant: uncurried
pub fn isect_m(x1: u64, y1: u64, x2: u64, y2: u64, x3: u64, y3: u64, x4: u64, y4: u64) -> Rc<inter<u64>> {
  let rx = sub(x2, x1);
  let ry = sub(y2, y1);
  let sx = sub(x4, x3);
  let sy = sub(y4, y3);
  let qx = sub(x3, x1);
  let qy = sub(y3, y1);
  let den = sub(mul(rx, sy), mul(ry, sx));
  let un = sub(mul(qx, ry), mul(qy, rx));
  match eqb(den, 0u64) {
    true => {
      let v97 = eqb(rx, 0u64);
      let v105 = eqb(ry, 0u64);
      match andb(v97, v105) {
        true => {
          match onseg_m(x3, y3, x4, y4, x1, y1) {
            true => {
              Rc::new(inter::<u64>::Point { x: x1, y: y1, denominator: 1u64 })
            },
            false => {
              Rc::new(inter::<u64>::Empty)
            },
          }
        },
        false => {
          let v156 = eqb(sx, 0u64);
          let v164 = eqb(sy, 0u64);
          match andb(v156, v164) {
            true => {
              match onseg_m(x1, y1, x2, y2, x3, y3) {
                true => {
                  Rc::new(inter::<u64>::Point { x: x3, y: y3, denominator: 1u64 })
                },
                false => {
                  Rc::new(inter::<u64>::Empty)
                },
              }
            },
            false => {
              match eqb(un, 0u64) {
                true => {
                  coll_m(x1, y1, x2, y2, x3, y3, x4, y4)
                },
                false => {
                  Rc::new(inter::<u64>::Empty)
                },
              }
            },
          }
        },
      }
    },
    false => {
      crossing_m(x1, y1, rx, ry, den, sub(mul(qx, sy), mul(qy, sx)), un)
    },
  }
}

// Rocq: Segmentintersection.segmentintersection_implem.isect_m
pub fn isect_m_curried(x1: u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<inter<u64>>>>>>>>> {
  let v3 = {
    move |y1: u64| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<inter<u64>>>>>>>> {
      let x1 = &x1;
      let v8 = Clone::clone(x1);
      let v11 = {
        move |x2: u64| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<inter<u64>>>>>>> {
          let x1 = &v8;
          let y1 = &y1;
          let v18 = Clone::clone(x1);
          let v20 = Clone::clone(y1);
          let v23 = {
            move |y2: u64| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<inter<u64>>>>>> {
              let x1 = &v18;
              let y1 = &v20;
              let x2 = &x2;
              let v32 = Clone::clone(x1);
              let v34 = Clone::clone(y1);
              let v36 = Clone::clone(x2);
              let v39 = {
                move |x3: u64| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<inter<u64>>>>> {
                  let x1 = &v32;
                  let y1 = &v34;
                  let x2 = &v36;
                  let y2 = &y2;
                  let v50 = Clone::clone(x1);
                  let v52 = Clone::clone(y1);
                  let v54 = Clone::clone(x2);
                  let v56 = Clone::clone(y2);
                  let v59 = {
                    move |y3: u64| -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<inter<u64>>>> {
                      let x1 = &v50;
                      let y1 = &v52;
                      let x2 = &v54;
                      let y2 = &v56;
                      let x3 = &x3;
                      let v72 = Clone::clone(x1);
                      let v74 = Clone::clone(y1);
                      let v76 = Clone::clone(x2);
                      let v78 = Clone::clone(y2);
                      let v80 = Clone::clone(x3);
                      let v83 = {
                        move |x4: u64| -> Rc<dyn Fn(u64) -> Rc<inter<u64>>> {
                          let x1 = &v72;
                          let y1 = &v74;
                          let x2 = &v76;
                          let y2 = &v78;
                          let x3 = &v80;
                          let y3 = &y3;
                          let v98 = Clone::clone(x1);
                          let v100 = Clone::clone(y1);
                          let v102 = Clone::clone(x2);
                          let v104 = Clone::clone(y2);
                          let v106 = Clone::clone(x3);
                          let v108 = Clone::clone(y3);
                          let v111 = {
                            move |y4: u64| -> Rc<inter<u64>> {
                              let v129 = Clone::clone(&v98);
                              let v131 = Clone::clone(&v100);
                              let v133 = Clone::clone(&v102);
                              let v135 = Clone::clone(&v104);
                              let v137 = Clone::clone(&v106);
                              let v139 = Clone::clone(&v108);
                              let v141 = Clone::clone(&x4);
                              isect_m(v129, v131, v133, v135, v137, v139, v141, y4)
                            }
                          };
                          let v147: Rc<dyn Fn(u64) -> Rc<inter<u64>>> = Rc::new(v111);
                          v147
                        }
                      };
                      let v151: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<inter<u64>>>> = Rc::new(v83);
                      v151
                    }
                  };
                  let v155: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<inter<u64>>>>> = Rc::new(v59);
                  v155
                }
              };
              let v159: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<inter<u64>>>>>> = Rc::new(v39);
              v159
            }
          };
          let v163: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<inter<u64>>>>>>> = Rc::new(v23);
          v163
        }
      };
      let v167: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<inter<u64>>>>>>>> = Rc::new(v11);
      v167
    }
  };
  let v171: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<inter<u64>>>>>>>>> = Rc::new(v3);
  v171
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

pub fn run() -> Rc<dyn Fn(u64, u64, u64, u64, u64, u64, u64, u64) -> Rc<inter<u64>>> {
  let v0: Rc<dyn Fn(u64, u64, u64, u64, u64, u64, u64, u64) -> Rc<inter<u64>>> = __rocq_global_561.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_561: Rc<dyn Fn(u64, u64, u64, u64, u64, u64, u64, u64) -> Rc<inter<u64>>> = intersect(); }
std::thread_local! { static __rocq_global_564: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<inter<u64>>>>>>>>>> = intersect_curried(); }