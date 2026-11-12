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

pub type sint = u64;

pub type uint = u64;

// Rocq: Corelib.Floats.PrimFloat.zero
pub fn zero() -> f64 {
  f64::from_bits(0u64)
}

// Rocq: Communicationssatellite.communicationssatellite_implem.communicationssatellite
// Variant: uncurried
pub fn communicationssatellite() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> f64> {
  let v0: fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> f64 = comsat;
  let v1: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> f64> = Rc::new(v0);
  v1
}

// Rocq: Communicationssatellite.communicationssatellite_implem.communicationssatellite
pub fn communicationssatellite_curried() -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> f64>>> {
  let v0: fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> f64>> = comsat_curried;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> f64>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Communicationssatellite.communicationssatellite_implem.bdec
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

// Rocq: Communicationssatellite.communicationssatellite_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: u64, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop::<St>(hi, f, i, s, ())
}

// Rocq: Communicationssatellite.communicationssatellite_implem.wloop (local: wloop)
// Variant: uncurried, lifted
pub fn wloop<St: Clone + 'static>(hi: u64, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St, _H: ()) -> St {
  let v12 = ltb(i, hi);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v24: &Rc<dyn Fn(u64, St) -> St> = &f;
      let v29 = v24(i, s);
      wloop::<St>(hi, f, v23, v29, ())
    },
    sumbool::right => {
      std::mem::drop(f);
      s
    },
  }
}

// Rocq: Communicationssatellite.communicationssatellite_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: u64, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop_1::<St>(hi, f, i, s)
}

// Rocq: Corelib.Floats.PrimFloat.sub
// Variant: uncurried
pub fn sub(v0: f64, v1: f64) -> f64 {
  rocq_float64::sub(v0, v1)
}

// Rocq: Corelib.Floats.PrimFloat.sqrt
pub fn sqrt(v0: f64) -> f64 {
  rocq_float64::sqrt(v0)
}

// Rocq: Corelib.Floats.PrimFloat.of_uint63
pub fn of_uint63(v0: u64) -> f64 {
  rocq_float64::of_uint63(v0)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub_1(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Communicationssatellite.communicationssatellite_implem.dsq
// Variant: uncurried
pub fn dsq(x: Rc<Array<u64>>, y: Rc<Array<u64>>, i: u64, j: u64) -> u64 {
  let v5 = &x;
  let v8 = rocq_array::get::<u64>(&v5, i);
  let v9 = &x;
  let v12 = rocq_array::get::<u64>(&v9, j);
  std::mem::drop(x);
  let dx = sub_1(v8, v12);
  let v19 = &y;
  let v22 = rocq_array::get::<u64>(&v19, i);
  let v23 = &y;
  let v26 = rocq_array::get::<u64>(&v23, j);
  std::mem::drop(y);
  let dy = sub_1(v22, v26);
  add(mul(dx, dx), mul(dy, dy))
}

// Rocq: Communicationssatellite.communicationssatellite_implem.wt
// Variant: uncurried
pub fn wt(x: Rc<Array<u64>>, y: Rc<Array<u64>>, r: Rc<Array<u64>>, i: u64, j: u64) -> f64 {
  let v23 = sqrt(of_uint63(dsq(x, y, i, j)));
  let v26 = &r;
  let v29 = rocq_array::get::<u64>(&v26, i);
  let v30 = &r;
  let v33 = rocq_array::get::<u64>(&v30, j);
  std::mem::drop(r);
  sub(v23, of_uint63(add(v29, v33)))
}

// Rocq: Communicationssatellite.communicationssatellite_implem.init_step
// Variant: uncurried
pub fn init_step(x: Rc<Array<u64>>, y: Rc<Array<u64>>, r: Rc<Array<u64>>, v: u64, key: Rc<Array<f64>>) -> Rc<Array<f64>> {
  let v18 = wt(x, y, r, 0u64, v);
  rocq_array::set::<f64>(key, v, v18)
}

// Rocq: Corelib.Floats.PrimFloat.ltb
// Variant: uncurried
pub fn ltb_1(v0: f64, v1: f64) -> bool {
  rocq_float64::ltb(v0, v1)
}

// Rocq: Communicationssatellite.communicationssatellite_implem.amin_step
// Variant: borrowed, uncurried
pub fn amin_step(n: u64, inT: &Rc<Array<bool>>, key: &Rc<Array<f64>>, v: u64, st: (u64, f64)) -> (u64, f64) {
  let n_1 = n;
  let v_1 = v;
  let st_1 = st;
  match &st_1 {
    (bv, b) => {
      let v14 = inT;
      match rocq_array::get::<bool>(&v14, v_1) {
        true => {
          st_1
        },
        false => {
          let v23 = Clone::clone(bv);
          match eqb(v23, n_1) {
            true => {
              std::mem::drop(st_1);
              let v28 = key;
              let v31 = rocq_array::get::<f64>(&v28, v_1);
              (v_1, v31)
            },
            false => {
              let v41 = key;
              let v45 = rocq_array::get::<f64>(&v41, v_1);
              let v48 = Clone::clone(b);
              match ltb_1(v45, v48) {
                true => {
                  std::mem::drop(st_1);
                  let v51 = key;
                  let v54 = rocq_array::get::<f64>(&v51, v_1);
                  (v_1, v54)
                },
                false => {
                  st_1
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Corelib.Floats.PrimFloat.add
// Variant: uncurried
pub fn add_1(v0: f64, v1: f64) -> f64 {
  rocq_float64::add(v0, v1)
}

// Rocq: Communicationssatellite.communicationssatellite_implem.upd_step
// Variant: uncurried
pub fn upd_step(x: Rc<Array<u64>>, y: Rc<Array<u64>>, r: Rc<Array<u64>>, inT: Rc<Array<bool>>, b: u64, v: u64, key: Rc<Array<f64>>) -> Rc<Array<f64>> {
  let v7 = &inT;
  let v10 = rocq_array::get::<bool>(&v7, v);
  match v10 {
    true => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(r);
      std::mem::drop(inT);
      key
    },
    false => {
      let wv = wt(x, y, r, b, v);
      let v27 = &key;
      let v30 = rocq_array::get::<f64>(&v27, v);
      match ltb_1(wv, v30) {
        true => {
          std::mem::drop(inT);
          rocq_array::set::<f64>(key, v, wv)
        },
        false => {
          std::mem::drop(inT);
          key
        },
      }
    },
  }
}

// Rocq: Communicationssatellite.communicationssatellite_implem.prim_step
// Variant: borrowed, uncurried
pub fn prim_step(x: &Rc<Array<u64>>, y: &Rc<Array<u64>>, r: &Rc<Array<u64>>, n: u64, _k: u64, st: ((Rc<Array<bool>>, Rc<Array<f64>>), f64)) -> ((Rc<Array<bool>>, Rc<Array<f64>>), f64) {
  let n_1 = n;
  let st_1 = st;
  match st_1 {
    (v9, v11) => {
      match v9 {
        (v14, v16) => {
          let key = &v14;
          let inT = &v16;
          let v24 = Rc::clone(key);
          let v26 = Rc::clone(inT);
          let v27 = {
            let __anf_capture_28 = n_1;
            move |v34: u64, v35: (u64, f64)| -> (u64, f64) {
              let n = &__anf_capture_28;
              let key = &v24;
              let inT = &v26;
              let v45 = amin_step(Clone::clone(n), key, inT, v34, v35);
              v45
            }
          };
          let v48: Rc<dyn Fn(u64, (u64, f64)) -> (u64, f64)> = Rc::new(v27);
          let v57 = (n_1, __rocq_global_353);
          let v67 = loop_::<(u64, f64)>(n_1, v48, 0u64, v57);
          match v67 {
            (v69, _v71) => {
              let v76 = rocq_array::get::<f64>(&inT, v69);
              let tot = add_1(v11, v76);
              let inT_1 = rocq_array::set::<bool>(v14, v69, true);
              let v94 = Rc::clone(x);
              let v97 = Rc::clone(y);
              let v100 = Rc::clone(r);
              let v103 = Rc::clone(&inT_1);
              let v106 = {
                let __anf_capture_115 = v69;
                move |v117: u64, v118: Rc<Array<f64>>| -> Rc<Array<f64>> {
                  let v121 = Rc::clone(&v94);
                  let v123 = Rc::clone(&v97);
                  let v125 = Rc::clone(&v100);
                  let v127 = Rc::clone(&v103);
                  let v129 = Clone::clone(&__anf_capture_115);
                  upd_step(v121, v123, v125, v127, v129, v117, v118)
                }
              };
              let v137: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new(v106);
              let key_1 = loop_::<Rc<Array<f64>>>(n_1, v137, 0u64, v16);
              ((inT_1, key_1), tot)
            },
          }
        },
      }
    },
  }
}

// Rocq: Communicationssatellite.communicationssatellite_implem.comsat
// Variant: uncurried
pub fn comsat(x: Rc<Array<u64>>, y: Rc<Array<u64>>, r: Rc<Array<u64>>) -> f64 {
  let v3 = &x;
  let n = rocq_array::length::<u64>(&v3);
  let v11 = rocq_array::make::<bool>(n, false);
  let inT = rocq_array::set::<bool>(v11, 0u64, true);
  let v26 = Rc::clone(&x);
  let v29 = Rc::clone(&y);
  let v32 = Rc::clone(&r);
  let v33 = {
    move |v40: u64, v41: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let v44 = Rc::clone(&v26);
      let v46 = Rc::clone(&v29);
      let v48 = Rc::clone(&v32);
      init_step(v44, v46, v48, v40, v41)
    }
  };
  let v56: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new(v33);
  let v65 = rocq_array::make::<f64>(n, __rocq_global_353);
  let key = loop_::<Rc<Array<f64>>>(n, v56, 0u64, v65);
  let v84 = {
    let __anf_capture_85 = x;
    let __anf_capture_87 = y;
    let __anf_capture_89 = r;
    let __anf_capture_91 = n;
    move |v93: u64, v94: ((Rc<Array<bool>>, Rc<Array<f64>>), f64)| -> ((Rc<Array<bool>>, Rc<Array<f64>>), f64) {
      let x = &__anf_capture_85;
      let y = &__anf_capture_87;
      let r = &__anf_capture_89;
      let v105 = prim_step(x, y, r, Clone::clone(&__anf_capture_91), v93, v94);
      v105
    }
  };
  let v108: Rc<dyn Fn(u64, ((Rc<Array<bool>>, Rc<Array<f64>>), f64)) -> ((Rc<Array<bool>>, Rc<Array<f64>>), f64)> = Rc::new(v84);
  let v133 = loop_::<((Rc<Array<bool>>, Rc<Array<f64>>), f64)>(n, v108, 1u64, ((inT, key), __rocq_global_353));
  match v133 {
    (v135, v137) => {
      match v135 {
        (v140, v142) => {
          std::mem::drop(v140);
          std::mem::drop(v142);
          v137
        },
      }
    },
  }
}

// Rocq: Communicationssatellite.communicationssatellite_implem.comsat
pub fn comsat_curried(x: Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> f64>> {
  let v3 = {
    move |y: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> f64> {
      let x = &x;
      let v8 = Rc::clone(x);
      let v11 = {
        move |r: Rc<Array<u64>>| -> f64 {
          let v19 = Rc::clone(&v8);
          let v21 = Rc::clone(&y);
          comsat(v19, v21, r)
        }
      };
      let v27: Rc<dyn Fn(Rc<Array<u64>>) -> f64> = Rc::new(v11);
      v27
    }
  };
  let v31: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> f64>> = Rc::new(v3);
  v31
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

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> f64> {
  let v0: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> f64> = __rocq_global_551.with(Clone::clone);
  v0
}
const __rocq_global_353: f64 = f64::from_bits(0u64);
std::thread_local! { static __rocq_global_551: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> f64> = communicationssatellite(); }
std::thread_local! { static __rocq_global_554: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> f64>>> = communicationssatellite_curried(); }