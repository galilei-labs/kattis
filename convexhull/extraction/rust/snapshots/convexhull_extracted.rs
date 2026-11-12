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

// Rocq: Convexhull.convexhull_implem.convex_hull
// Variant: uncurried
pub fn convex_hull() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>> = hull;
  let v1: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v0);
  v1
}

// Rocq: Convexhull.convexhull_implem.convex_hull
pub fn convex_hull_curried() -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> {
  let v0: fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = hull_curried;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> = Rc::new(v0);
  v1
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Convexhull.convexhull_implem.bdec
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

// Rocq: Convexhull.convexhull_implem.min_i
// Variant: uncurried
pub fn min_i(a: u64, b: u64) -> u64 {
  match ltb(a, b) {
    true => {
      a
    },
    false => {
      b
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb
// Variant: uncurried
pub fn ltsb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltsb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lesb
// Variant: uncurried
pub fn lesb(v0: u64, v1: u64) -> bool {
  rocq_int63::lesb(v0, v1)
}

// Rocq: Convexhull.convexhull_implem.le_pt
// Variant: uncurried
pub fn le_pt(x: Rc<Array<u64>>, y: Rc<Array<u64>>, a: u64, b: u64) -> bool {
  let v4 = &x;
  let xa = rocq_array::get::<u64>(&v4, a);
  let v8 = &x;
  let xb = rocq_array::get::<u64>(&v8, b);
  match ltsb(xa, xb) {
    true => {
      std::mem::drop(y);
      std::mem::drop(x);
      true
    },
    false => {
      match eqb(xa, xb) {
        true => {
          std::mem::drop(x);
          let v31 = &y;
          let v34 = rocq_array::get::<u64>(&v31, a);
          let v35 = &y;
          let v38 = rocq_array::get::<u64>(&v35, b);
          std::mem::drop(y);
          lesb(v34, v38)
        },
        false => {
          std::mem::drop(y);
          std::mem::drop(x);
          false
        },
      }
    },
  }
}

// Rocq: Convexhull.convexhull_implem.take_left
// Variant: uncurried
pub fn take_left(x: Rc<Array<u64>>, y: Rc<Array<u64>>, src: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64) -> bool {
  match ltb(i, mid) {
    true => {
      match ltb(j, hi) {
        true => {
          let v22 = &src;
          let v25 = rocq_array::get::<u64>(&v22, i);
          let v26 = &src;
          let v29 = rocq_array::get::<u64>(&v26, j);
          std::mem::drop(src);
          le_pt(x, y, v25, v29)
        },
        false => {
          std::mem::drop(x);
          std::mem::drop(y);
          std::mem::drop(src);
          true
        },
      }
    },
    false => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(src);
      false
    },
  }
}

// Rocq: Convexhull.convexhull_implem.merge
// Variant: uncurried
pub fn merge_1(x: Rc<Array<u64>>, y: Rc<Array<u64>>, src: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  merge(x, y, src, mid, hi, i, j, k, dst, ())
}

// Rocq: Convexhull.convexhull_implem.merge (local: merge)
// Variant: uncurried, lifted
pub fn merge(x: Rc<Array<u64>>, y: Rc<Array<u64>>, src: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v17 = ltb(k, hi);
  match bdec(v17) {
    sumbool::left => {
      let v24 = Rc::clone(&x);
      let v27 = Rc::clone(&y);
      let v30 = Rc::clone(&src);
      match take_left(v24, v27, v30, mid, hi, i, j) {
        true => {
          let v48 = add(i, 1u64);
          let v56 = add(k, 1u64);
          let v57 = &src;
          let v60 = rocq_array::get::<u64>(&v57, i);
          let v67 = rocq_array::set::<u64>(dst, k, v60);
          merge(x, y, src, mid, hi, v48, j, v56, v67, ())
        },
        false => {
          let v101 = add(j, 1u64);
          let v109 = add(k, 1u64);
          let v110 = &src;
          let v113 = rocq_array::get::<u64>(&v110, j);
          let v120 = rocq_array::set::<u64>(dst, k, v113);
          merge(x, y, src, mid, hi, i, v101, v109, v120, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Convexhull.convexhull_implem.pass
// Variant: uncurried
pub fn pass_1(x: Rc<Array<u64>>, y: Rc<Array<u64>>, src: Rc<Array<u64>>, w: u64, n: u64, lo: u64, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  pass(x, y, src, w, n, lo, dst, ())
}

// Rocq: Convexhull.convexhull_implem.pass (local: pass)
// Variant: uncurried, lifted
pub fn pass(x: Rc<Array<u64>>, y: Rc<Array<u64>>, src: Rc<Array<u64>>, w: u64, n: u64, lo: u64, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v18 = add(lo, w);
  let v33 = ltb(lo, min_i(add(v18, w), n));
  match bdec(v33) {
    sumbool::left => {
      let v45 = add(lo, w);
      let v54 = min_i(add(v45, w), n);
      let v67 = min_i(add(lo, w), n);
      let v76 = add(lo, w);
      let v85 = min_i(add(v76, w), n);
      let v97 = min_i(add(lo, w), n);
      let v100 = Rc::clone(&x);
      let v103 = Rc::clone(&y);
      let v106 = Rc::clone(&src);
      let v119 = merge_1(v100, v103, v106, v67, v85, lo, v97, lo, dst);
      pass(x, y, src, w, n, v54, v119, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Convexhull.convexhull_implem.sortl
// Variant: uncurried
pub fn sortl_1(x: Rc<Array<u64>>, y: Rc<Array<u64>>, n: u64, w: u64, src: Rc<Array<u64>>, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  sortl(x, y, n, w, src, dst, ())
}

// Rocq: Convexhull.convexhull_implem.sortl (local: sortl)
// Variant: uncurried, lifted
pub fn sortl(x: Rc<Array<u64>>, y: Rc<Array<u64>>, n: u64, w: u64, src: Rc<Array<u64>>, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v14 = ltb(w, n);
  let v21 = add(w, w);
  let v32 = andb(v14, ltb(w, v21));
  match bdec(v32) {
    sumbool::left => {
      let v41 = add(w, w);
      let v47 = Rc::clone(&x);
      let v50 = Rc::clone(&y);
      let v53 = Rc::clone(&src);
      let v62 = pass_1(v47, v50, v53, w, n, 0u64, dst);
      sortl(x, y, n, v41, v62, src, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(dst);
      src
    },
  }
}

// Rocq: Convexhull.convexhull_implem.initl
// Variant: uncurried
pub fn initl_1(n: u64, i: u64, a: Rc<Array<u64>>) -> Rc<Array<u64>> {
  initl(n, i, a, ())
}

// Rocq: Convexhull.convexhull_implem.initl (local: initl)
// Variant: uncurried, lifted
pub fn initl(n: u64, i: u64, a: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v11 = ltb(i, n);
  match bdec(v11) {
    sumbool::left => {
      let v22 = add(i, 1u64);
      let v29 = rocq_array::set::<u64>(a, i, i);
      initl(n, v22, v29, ())
    },
    sumbool::right => {
      a
    },
  }
}

// Rocq: Convexhull.convexhull_implem.msort
// Variant: uncurried
pub fn msort(x: Rc<Array<u64>>, y: Rc<Array<u64>>, n: u64) -> Rc<Array<u64>> {
  let v15 = rocq_array::make::<u64>(n, 0u64);
  let v22 = initl_1(n, 0u64, v15);
  let v29 = rocq_array::make::<u64>(n, 0u64);
  sortl_1(x, y, n, 1u64, v22, v29)
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

// Rocq: Convexhull.convexhull_implem.cross_m
// Variant: uncurried
pub fn cross_m(x: Rc<Array<u64>>, y: Rc<Array<u64>>, a: u64, b: u64, c: u64) -> u64 {
  let v5 = &x;
  let xa = rocq_array::get::<u64>(&v5, a);
  let v9 = &y;
  let ya = rocq_array::get::<u64>(&v9, a);
  let v16 = &x;
  let v20 = rocq_array::get::<u64>(&v16, b);
  let v24 = sub(v20, xa);
  let v26 = &y;
  let v30 = rocq_array::get::<u64>(&v26, c);
  let v39 = mul(v24, sub(v30, ya));
  let v42 = &y;
  let v45 = rocq_array::get::<u64>(&v42, b);
  std::mem::drop(y);
  let v50 = sub(v45, ya);
  let v52 = &x;
  let v55 = rocq_array::get::<u64>(&v52, c);
  std::mem::drop(x);
  let v60 = sub(v55, xa);
  sub(v39, mul(v50, v60))
}

// Rocq: Convexhull.convexhull_implem.pop
// Variant: uncurried
pub fn pop_1(x: Rc<Array<u64>>, y: Rc<Array<u64>>, st: Rc<Array<u64>>, lim: u64, k: u64, q: u64) -> u64 {
  pop(x, y, st, lim, k, q, ())
}

// Rocq: Convexhull.convexhull_implem.pop (local: pop)
// Variant: uncurried, lifted
pub fn pop(x: Rc<Array<u64>>, y: Rc<Array<u64>>, st: Rc<Array<u64>>, lim: u64, k: u64, q: u64, _H: ()) -> u64 {
  let v14 = ltb(lim, k);
  let v24 = sub(k, 2u64);
  let v25 = &st;
  let v28 = rocq_array::get::<u64>(&v25, v24);
  let v36 = sub(k, 1u64);
  let v37 = &st;
  let v40 = rocq_array::get::<u64>(&v37, v36);
  let v43 = Rc::clone(&x);
  let v46 = Rc::clone(&y);
  let v66 = andb(v14, lesb(cross_m(v43, v46, v28, v40, q), 0u64));
  match bdec(v66) {
    sumbool::left => {
      pop(x, y, st, lim, sub(k, 1u64), q, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(st);
      k
    },
  }
}

// Rocq: Convexhull.convexhull_implem.lower
// Variant: uncurried
pub fn lower_1(x: Rc<Array<u64>>, y: Rc<Array<u64>>, ord: Rc<Array<u64>>, st: Rc<Array<u64>>, n: u64, k: u64, i: u64) -> (Rc<Array<u64>>, u64) {
  lower(x, y, ord, st, n, k, i, ())
}

// Rocq: Convexhull.convexhull_implem.lower (local: lower)
// Variant: uncurried, lifted
pub fn lower(x: Rc<Array<u64>>, y: Rc<Array<u64>>, ord: Rc<Array<u64>>, st: Rc<Array<u64>>, n: u64, k: u64, i: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let v15 = ltb(i, n);
  match bdec(v15) {
    sumbool::left => {
      let v19 = &ord;
      let q = rocq_array::get::<u64>(&v19, i);
      let v28 = Rc::clone(&x);
      let v31 = Rc::clone(&y);
      let v34 = Rc::clone(&st);
      let k_ = pop_1(v28, v31, v34, 1u64, k, q);
      let v48 = rocq_array::set::<u64>(st, k_, q);
      lower(x, y, ord, v48, n, add(k_, 1u64), add(i, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(ord);
      (st, k)
    },
  }
}

// Rocq: Convexhull.convexhull_implem.upper
// Variant: uncurried
pub fn upper_1(x: Rc<Array<u64>>, y: Rc<Array<u64>>, ord: Rc<Array<u64>>, st: Rc<Array<u64>>, lim: u64, k: u64, j: u64) -> (Rc<Array<u64>>, u64) {
  upper(x, y, ord, st, lim, k, j, ())
}

// Rocq: Convexhull.convexhull_implem.upper (local: upper)
// Variant: uncurried, lifted
pub fn upper(x: Rc<Array<u64>>, y: Rc<Array<u64>>, ord: Rc<Array<u64>>, st: Rc<Array<u64>>, lim: u64, k: u64, j: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let v17 = ltb(0u64, j);
  match bdec(v17) {
    sumbool::left => {
      let v28 = sub(j, 1u64);
      let v29 = &ord;
      let q = rocq_array::get::<u64>(&v29, v28);
      let v36 = Rc::clone(&x);
      let v39 = Rc::clone(&y);
      let v42 = Rc::clone(&st);
      let k_ = pop_1(v36, v39, v42, lim, k, q);
      let v56 = rocq_array::set::<u64>(st, k_, q);
      upper(x, y, ord, v56, lim, add(k_, 1u64), sub(j, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(ord);
      (st, k)
    },
  }
}

// Rocq: Convexhull.convexhull_implem.copyl
// Variant: uncurried
pub fn copyl_1(src: Rc<Array<u64>>, dst: Rc<Array<u64>>, h: u64, i: u64) -> Rc<Array<u64>> {
  copyl(src, dst, h, i, ())
}

// Rocq: Convexhull.convexhull_implem.copyl (local: copyl)
// Variant: uncurried, lifted
pub fn copyl(src: Rc<Array<u64>>, dst: Rc<Array<u64>>, h: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(i, h);
  match bdec(v12) {
    sumbool::left => {
      let v16 = &src;
      let v19 = rocq_array::get::<u64>(&v16, i);
      let v26 = rocq_array::set::<u64>(dst, i, v19);
      copyl(src, v26, h, add(i, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Convexhull.convexhull_implem.hull
// Variant: uncurried
pub fn hull(x: Rc<Array<u64>>, y: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v2 = &x;
  let n = rocq_array::length::<u64>(&v2);
  let v7 = Rc::clone(&x);
  let v10 = Rc::clone(&y);
  let ord = msort(v7, v10, n);
  let v15 = 0u64;
  let v16 = &ord;
  let a = rocq_array::get::<u64>(&v16, v15);
  let v27 = sub(n, 1u64);
  let v28 = &ord;
  let b = rocq_array::get::<u64>(&v28, v27);
  let v34 = &x;
  let v37 = rocq_array::get::<u64>(&v34, a);
  let v38 = &x;
  let v41 = rocq_array::get::<u64>(&v38, b);
  let v46 = eqb(v37, v41);
  let v48 = &y;
  let v51 = rocq_array::get::<u64>(&v48, a);
  let v52 = &y;
  let v55 = rocq_array::get::<u64>(&v52, b);
  let v60 = eqb(v51, v55);
  match andb(v46, v60) {
    true => {
      std::mem::drop(y);
      std::mem::drop(x);
      std::mem::drop(ord);
      rocq_array::make::<u64>(1u64, a)
    },
    false => {
      let v89 = rocq_array::make::<u64>(add(n, n), 0u64);
      let v98 = rocq_array::set::<u64>(v89, 0u64, a);
      let v105 = Rc::clone(&x);
      let v108 = Rc::clone(&y);
      let v111 = Rc::clone(&ord);
      let v120 = lower_1(v105, v108, v111, v98, n, 1u64, 1u64);
      match &v120 {
        (l, st1) => {
          let v135 = sub(n, 1u64);
          let v143 = Rc::clone(l);
          let v145 = Clone::clone(st1);
          let v146 = Clone::clone(st1);
          std::mem::drop(v120);
          let v150 = upper_1(x, y, ord, v143, v145, v146, v135);
          match v150 {
            (v152, v154) => {
              let v171 = rocq_array::make::<u64>(sub(v154, 1u64), 0u64);
              copyl_1(v152, v171, sub(v154, 1u64), 0u64)
            },
          }
        },
      }
    },
  }
}

// Rocq: Convexhull.convexhull_implem.hull
pub fn hull_curried(x: Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v3 = {
    move |y: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let v9 = Rc::clone(&x);
      hull(v9, y)
    }
  };
  let v15: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v3);
  v15
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

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = __rocq_global_867.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_867: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = convex_hull(); }
std::thread_local! { static __rocq_global_870: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> = convex_hull_curried(); }