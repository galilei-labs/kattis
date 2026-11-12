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

pub type uint = u64;

// Rocq: Kingpinescape.kingpinescape_implem.kingpin_escape
// Variant: uncurried
pub fn kingpin_escape() -> Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>)> {
  let v0: fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) = kingpin_impl;
  let v1: Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new(v0);
  v1
}

// Rocq: Kingpinescape.kingpinescape_implem.kingpin_escape
pub fn kingpin_escape_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>)>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>)>>> = kingpin_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>)>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
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

// Rocq: Kingpinescape.kingpinescape_implem.bdec
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

// Rocq: Kingpinescape.kingpinescape_implem.cnt_loop
// Variant: uncurried
pub fn cnt_loop_1(col: Rc<Array<u64>>, m: u64, i: u64, deg: Rc<Array<u64>>) -> Rc<Array<u64>> {
  cnt_loop(col, m, i, deg, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.cnt_loop (local: cnt_loop)
// Variant: uncurried, lifted
pub fn cnt_loop(col: Rc<Array<u64>>, m: u64, i: u64, deg: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(i, m);
  match bdec(v12) {
    sumbool::left => {
      let v16 = &col;
      let v = rocq_array::get::<u64>(&v16, i);
      let v27 = add(i, 1u64);
      let v29 = &deg;
      let v32 = rocq_array::get::<u64>(&v29, v);
      let v46 = rocq_array::set::<u64>(deg, v, add(v32, 1u64));
      cnt_loop(col, m, v27, v46, ())
    },
    sumbool::right => {
      std::mem::drop(col);
      deg
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.pre_loop
// Variant: uncurried
pub fn pre_loop_1(deg: Rc<Array<u64>>, n: u64, i: u64, acc: u64, pos: Rc<Array<u64>>) -> Rc<Array<u64>> {
  pre_loop(deg, n, i, acc, pos, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.pre_loop (local: pre_loop)
// Variant: uncurried, lifted
pub fn pre_loop(deg: Rc<Array<u64>>, n: u64, i: u64, acc: u64, pos: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v13 = ltb(i, n);
  match bdec(v13) {
    sumbool::left => {
      let v24 = add(i, 1u64);
      let v26 = &deg;
      let v29 = rocq_array::get::<u64>(&v26, i);
      let v34 = add(acc, v29);
      let v41 = rocq_array::set::<u64>(pos, i, acc);
      pre_loop(deg, n, v24, v34, v41, ())
    },
    sumbool::right => {
      std::mem::drop(deg);
      pos
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(col: Rc<Array<u64>>, base: u64, m: u64, i: u64, pos: Rc<Array<u64>>, adj: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  fill_loop(col, base, m, i, pos, adj, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(col: Rc<Array<u64>>, base: u64, m: u64, i: u64, pos: Rc<Array<u64>>, adj: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v14 = ltb(i, m);
  match bdec(v14) {
    sumbool::left => {
      let v18 = &col;
      let v = rocq_array::get::<u64>(&v18, i);
      let v22 = &pos;
      let p = rocq_array::get::<u64>(&v22, v);
      let v33 = add(i, 1u64);
      let v48 = rocq_array::set::<u64>(pos, v, add(p, 1u64));
      let v61 = rocq_array::set::<u64>(adj, p, add(base, i));
      fill_loop(col, base, m, v33, v48, v61, ())
    },
    sumbool::right => {
      std::mem::drop(col);
      (pos, adj)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Kingpinescape.kingpinescape_implem.root_loop
// Variant: uncurried
pub fn root_loop_1(deg: Rc<Array<u64>>, n: u64, i: u64) -> u64 {
  root_loop(deg, n, i, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.root_loop (local: root_loop)
// Variant: uncurried, lifted
pub fn root_loop(deg: Rc<Array<u64>>, n: u64, i: u64, _H: ()) -> u64 {
  let v11 = ltb(i, n);
  match bdec(v11) {
    sumbool::left => {
      let v18 = &deg;
      let v21 = rocq_array::get::<u64>(&v18, i);
      match leb(2u64, v21) {
        true => {
          std::mem::drop(deg);
          i
        },
        false => {
          root_loop(deg, n, add(i, 1u64), ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(deg);
      0u64
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.other
// Variant: uncurried
pub fn other(ea: Rc<Array<u64>>, eb: Rc<Array<u64>>, m: u64, hh: u64) -> u64 {
  match ltb(hh, m) {
    true => {
      std::mem::drop(ea);
      let v11 = &eb;
      let v14 = rocq_array::get::<u64>(&v11, hh);
      std::mem::drop(eb);
      v14
    },
    false => {
      std::mem::drop(eb);
      let v22 = sub(hh, m);
      let v23 = &ea;
      let v26 = rocq_array::get::<u64>(&v23, v22);
      std::mem::drop(ea);
      v26
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.nb_loop
// Variant: uncurried
pub fn nb_loop_1(ea: Rc<Array<u64>>, eb: Rc<Array<u64>>, adj: Rc<Array<u64>>, m: u64, e: u64, s: u64, mark: Rc<Array<u64>>, stk: Rc<Array<u64>>, sp: u64) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  nb_loop(ea, eb, adj, m, e, s, mark, stk, sp, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.nb_loop (local: nb_loop)
// Variant: uncurried, lifted
pub fn nb_loop(ea: Rc<Array<u64>>, eb: Rc<Array<u64>>, adj: Rc<Array<u64>>, m: u64, e: u64, s: u64, mark: Rc<Array<u64>>, stk: Rc<Array<u64>>, sp: u64, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let v17 = ltb(s, e);
  match bdec(v17) {
    sumbool::left => {
      let v22 = &adj;
      let v25 = rocq_array::get::<u64>(&v22, s);
      let v28 = Rc::clone(&ea);
      let v31 = Rc::clone(&eb);
      let w = other(v28, v31, m, v25);
      let v38 = &mark;
      let v41 = rocq_array::get::<u64>(&v38, w);
      match eqb(v41, 0u64) {
        true => {
          let v57 = add(s, 1u64);
          let v66 = rocq_array::set::<u64>(mark, w, 1u64);
          let v73 = rocq_array::set::<u64>(stk, sp, w);
          nb_loop(ea, eb, adj, m, e, v57, v66, v73, add(sp, 1u64), ())
        },
        false => {
          nb_loop(ea, eb, adj, m, e, add(s, 1u64), mark, stk, sp, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(ea);
      std::mem::drop(eb);
      std::mem::drop(adj);
      ((mark, stk), sp)
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.dfs_loop
// Variant: uncurried
pub fn dfs_loop_1(ea: Rc<Array<u64>>, eb: Rc<Array<u64>>, adj: Rc<Array<u64>>, deg: Rc<Array<u64>>, pos: Rc<Array<u64>>, n: u64, m: u64, t: u64, mark: Rc<Array<u64>>, stk: Rc<Array<u64>>, sp: u64, lv: Rc<Array<u64>>, L: u64) -> (Rc<Array<u64>>, u64) {
  dfs_loop(ea, eb, adj, deg, pos, n, m, t, mark, stk, sp, lv, L, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.dfs_loop (local: dfs_loop)
// Variant: uncurried, lifted
pub fn dfs_loop(ea: Rc<Array<u64>>, eb: Rc<Array<u64>>, adj: Rc<Array<u64>>, deg: Rc<Array<u64>>, pos: Rc<Array<u64>>, n: u64, m: u64, t: u64, mark: Rc<Array<u64>>, stk: Rc<Array<u64>>, sp: u64, lv: Rc<Array<u64>>, L: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let v21 = ltb(t, n);
  match bdec(v21) {
    sumbool::left => {
      match ltb(0u64, sp) {
        true => {
          let v41 = sub(sp, 1u64);
          let v42 = &stk;
          let v = rocq_array::get::<u64>(&v42, v41);
          let v46 = &deg;
          let dv = rocq_array::get::<u64>(&v46, v);
          let v50 = &pos;
          let e = rocq_array::get::<u64>(&v50, v);
          let v56 = 1u64;
          let lv_ = match eqb(dv, v56) {
            true => {
              rocq_array::set::<u64>(lv, L, v)
            },
            false => {
              lv
            },
          };
          let v77 = 1u64;
          let L_ = match eqb(dv, v77) {
            true => {
              add(L, 1u64)
            },
            false => {
              L
            },
          };
          let v103 = sub(e, dv);
          let v111 = sub(sp, 1u64);
          let v114 = Rc::clone(&ea);
          let v117 = Rc::clone(&eb);
          let v120 = Rc::clone(&adj);
          let v133 = nb_loop_1(v114, v117, v120, m, e, v103, mark, stk, v111);
          match v133 {
            (v135, v137) => {
              match v135 {
                (v140, v142) => {
                  dfs_loop(ea, eb, adj, deg, pos, n, m, add(t, 1u64), v140, v142, v137, lv_, L_, ())
                },
              }
            },
          }
        },
        false => {
          std::mem::drop(ea);
          std::mem::drop(eb);
          std::mem::drop(adj);
          std::mem::drop(deg);
          std::mem::drop(pos);
          std::mem::drop(mark);
          std::mem::drop(stk);
          (lv, L)
        },
      }
    },
    sumbool::right => {
      std::mem::drop(ea);
      std::mem::drop(eb);
      std::mem::drop(adj);
      std::mem::drop(deg);
      std::mem::drop(pos);
      std::mem::drop(mark);
      std::mem::drop(stk);
      (lv, L)
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.out_loop
// Variant: uncurried
pub fn out_loop_1(lv: Rc<Array<u64>>, a: u64, c: u64, i: u64, xs: Rc<Array<u64>>, ys: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  out_loop(lv, a, c, i, xs, ys, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.out_loop (local: out_loop)
// Variant: uncurried, lifted
pub fn out_loop(lv: Rc<Array<u64>>, a: u64, c: u64, i: u64, xs: Rc<Array<u64>>, ys: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v14 = ltb(i, c);
  match bdec(v14) {
    sumbool::left => {
      let v25 = add(i, 1u64);
      let v26 = &lv;
      let v29 = rocq_array::get::<u64>(&v26, i);
      let v36 = rocq_array::set::<u64>(xs, i, v29);
      let v42 = add(i, a);
      let v43 = &lv;
      let v46 = rocq_array::get::<u64>(&v43, v42);
      let v53 = rocq_array::set::<u64>(ys, i, v46);
      out_loop(lv, a, c, v25, v36, v53, ())
    },
    sumbool::right => {
      std::mem::drop(lv);
      (xs, ys)
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.kingpin_impl
// Variant: uncurried
pub fn kingpin_impl(n: u64, _h: u64, ea: Rc<Array<u64>>, eb: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let m = sub(n, 1u64);
  let v21 = rocq_array::make::<u64>(n, 0u64);
  let v24 = Rc::clone(&ea);
  let deg0 = cnt_loop_1(v24, m, 0u64, v21);
  let v37 = Rc::clone(&eb);
  let deg = cnt_loop_1(v37, m, 0u64, deg0);
  let v56 = rocq_array::make::<u64>(n, 0u64);
  let v59 = Rc::clone(&deg);
  let pos0 = pre_loop_1(v59, n, 0u64, 0u64, v56);
  let v86 = rocq_array::make::<u64>(add(m, m), 0u64);
  let v89 = Rc::clone(&ea);
  let v100 = fill_loop_1(v89, 0u64, m, 0u64, pos0, v86);
  match v100 {
    (v102, v104) => {
      let v111 = Rc::clone(&eb);
      let v122 = fill_loop_1(v111, m, m, 0u64, v102, v104);
      match &v122 {
        (adj, pos) => {
          let v134 = Rc::clone(&deg);
          let r = root_loop_1(v134, n, 0u64);
          let v146 = rocq_array::make::<u64>(n, 0u64);
          let mark = rocq_array::set::<u64>(v146, r, 1u64);
          let v162 = rocq_array::make::<u64>(n, 0u64);
          let stk = rocq_array::set::<u64>(v162, 0u64, r);
          let v174 = 0u64;
          let v176 = 1u64;
          let v183 = rocq_array::make::<u64>(n, 0u64);
          let v185 = 0u64;
          let v191 = Rc::clone(pos);
          let v194 = Rc::clone(adj);
          std::mem::drop(v122);
          let v212 = dfs_loop_1(ea, eb, v191, deg, v194, n, m, v174, mark, stk, v176, v183, v185);
          match v212 {
            (v214, v216) => {
              let a = lsr(v216, 1u64);
              let c = sub(v216, a);
              let v241 = rocq_array::make::<u64>(c, 0u64);
              let v248 = rocq_array::make::<u64>(c, 0u64);
              out_loop_1(v214, a, c, 0u64, v241, v248)
            },
          }
        },
      }
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.kingpin_impl
pub fn kingpin_impl_curried(n: u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>)>>> {
  let v3 = {
    move |h: u64| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>)>> {
      let n = &n;
      let v8 = Clone::clone(n);
      let v11 = {
        move |ea: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>)> {
          let n = &v8;
          let h = &h;
          let v18 = Clone::clone(n);
          let v20 = Clone::clone(h);
          let v23 = {
            move |eb: Rc<Array<u64>>| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
              let v33 = Clone::clone(&v18);
              let v35 = Clone::clone(&v20);
              let v37 = Rc::clone(&ea);
              kingpin_impl(v33, v35, v37, eb)
            }
          };
          let v43: Rc<dyn Fn(Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new(v23);
          v43
        }
      };
      let v47: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>)>> = Rc::new(v11);
      v47
    }
  };
  let v51: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>)>>> = Rc::new(v3);
  v51
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

pub fn run() -> Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>)> {
  let v0: Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = __rocq_global_707.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_707: Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = kingpin_escape(); }
std::thread_local! { static __rocq_global_710: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>)>>>> = kingpin_escape_curried(); }