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

#[derive(Clone, Copy)]
pub enum player {
  Ruben,
  Albert,
}

pub type uint = u64;

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.winner
// Variant: uncurried
pub fn winner() -> Rc<dyn Fn(player, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> player> {
  let v0: fn(player, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> player = winner_impl;
  let v1: Rc<dyn Fn(player, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> player> = Rc::new(v0);
  v1
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.winner
pub fn winner_curried() -> Rc<dyn Fn(player) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> player>>>> {
  let v0: fn(player) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> player>>> = winner_impl_curried;
  let v1: Rc<dyn Fn(player) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> player>>>> = Rc::new(v0);
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

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.bdec
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

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.loop
// Variant: uncurried
pub fn loop__1<A: Clone + 'static>(f: Rc<dyn Fn(u64, A) -> A>, hi: u64, i: u64, acc: A) -> A {
  loop_::<A>((), f, hi, i, acc, ())
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.loop (local: loop)
// Variant: uncurried, lifted
pub fn loop_<A: Clone + 'static>(_A_1: (), f: Rc<dyn Fn(u64, A) -> A>, hi: u64, i: u64, acc: A, _H: ()) -> A {
  let v13 = ltb(i, hi);
  match bdec(v13) {
    sumbool::left => {
      let v26 = add(i, 1u64);
      let v27: &Rc<dyn Fn(u64, A) -> A> = &f;
      let v32 = v27(i, acc);
      loop_::<A>((), f, hi, v26, v32, ())
    },
    sumbool::right => {
      std::mem::drop(f);
      acc
    },
  }
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.for_
// Variant: uncurried
pub fn for_<A: Clone + 'static>(f: Rc<dyn Fn(u64, A) -> A>, lo: u64, hi: u64, acc: A) -> A {
  loop__1::<A>(f, hi, lo, acc)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.imax
// Variant: uncurried
pub fn imax(a: u64, b: u64) -> u64 {
  match leb(a, b) {
    true => {
      b
    },
    false => {
      a
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.cidx
// Variant: uncurried
pub fn cidx(D: u64, x: u64, y: u64, z: u64) -> u64 {
  let v18 = add(mul(x, D), y);
  add(mul(v18, D), z)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lxor
// Variant: uncurried
pub fn lxor(v0: u64, v1: u64) -> u64 {
  rocq_int63::lxor(v0, v1)
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.imin
// Variant: uncurried
pub fn imin(a: u64, b: u64) -> u64 {
  match leb(a, b) {
    true => {
      a
    },
    false => {
      b
    },
  }
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.look
// Variant: borrowed, uncurried
pub fn look(T: &Rc<Array<u64>>, D: u64, x: u64, y: u64, z: u64) -> u64 {
  let D_1 = D;
  let x_1 = x;
  let y_1 = y;
  let z_1 = z;
  let v15 = imin(y_1, z_1);
  let lo = imin(x_1, v15);
  let v27 = imax(y_1, z_1);
  let hi = imax(x_1, v27);
  let v43 = add(x_1, y_1);
  let v53 = sub(add(v43, z_1), lo);
  let v66 = cidx(D_1, lo, sub(v53, hi), hi);
  let v67 = T;
  rocq_array::get::<u64>(&v67, v66)
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.cutv
// Variant: borrowed, uncurried
pub fn cutv(T: &Rc<Array<u64>>, D: u64, x: u64, y: u64, z: u64, a: u64, b: u64, c: u64) -> u64 {
  let D_1 = D;
  let x_1 = x;
  let y_1 = y;
  let z_1 = z;
  let a_1 = a;
  let b_1 = b;
  let c_1 = c;
  let p1 = sub(a_1, 1u64);
  let p2 = sub(x_1, a_1);
  let q1 = sub(b_1, 1u64);
  let q2 = sub(y_1, b_1);
  let r1 = sub(c_1, 1u64);
  let r2 = sub(z_1, c_1);
  let v69 = look(T, D_1, p1, q1, r1);
  let v82 = look(T, D_1, p1, q1, r2);
  let v95 = look(T, D_1, p1, q2, r1);
  let v108 = look(T, D_1, p1, q2, r2);
  let v121 = look(T, D_1, p2, q1, r1);
  let v134 = look(T, D_1, p2, q1, r2);
  let v164 = lxor(look(T, D_1, p2, q2, r1), look(T, D_1, p2, q2, r2));
  let v169 = lxor(v134, v164);
  let v174 = lxor(v121, v169);
  let v179 = lxor(v108, v174);
  let v184 = lxor(v95, v179);
  let v189 = lxor(v82, v184);
  lxor(v69, v189)
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.mark_c
// Variant: uncurried
pub fn mark_c(T: Rc<Array<u64>>, D: u64, x: u64, y: u64, z: u64, a: u64, b: u64, hc: u64, st: u64, s: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v27 = {
    move |c: u64, s: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let T = &T;
      let D = &D;
      let x = &x;
      let y = &y;
      let z = &z;
      let a = &a;
      let b = &b;
      let st = &st;
      let v62 = cutv(T, Clone::clone(D), Clone::clone(x), Clone::clone(y), Clone::clone(z), Clone::clone(a), Clone::clone(b), c);
      let v68 = Clone::clone(st);
      rocq_array::set::<u64>(s, v62, v68)
    }
  };
  let v72: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v27);
  for_::<Rc<Array<u64>>>(v72, 1u64, add(hc, 1u64), s)
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.mark_b
// Variant: uncurried
pub fn mark_b(T: Rc<Array<u64>>, D: u64, x: u64, y: u64, z: u64, a: u64, hb: u64, hc: u64, st: u64, s: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v27 = {
    move |b: u64, s: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let v48 = Rc::clone(&T);
      let v50 = Clone::clone(&D);
      let v52 = Clone::clone(&x);
      let v54 = Clone::clone(&y);
      let v56 = Clone::clone(&z);
      let v58 = Clone::clone(&a);
      let v62 = Clone::clone(&hc);
      let v64 = Clone::clone(&st);
      mark_c(v48, v50, v52, v54, v56, v58, b, v62, v64, s)
    }
  };
  let v70: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v27);
  for_::<Rc<Array<u64>>>(v70, 1u64, add(hb, 1u64), s)
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.mark_a
// Variant: uncurried
pub fn mark_a(T: Rc<Array<u64>>, D: u64, x: u64, y: u64, z: u64, ha: u64, hb: u64, hc: u64, st: u64, s: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v27 = {
    move |a: u64, s: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let v48 = Rc::clone(&T);
      let v50 = Clone::clone(&D);
      let v52 = Clone::clone(&x);
      let v54 = Clone::clone(&y);
      let v56 = Clone::clone(&z);
      let v60 = Clone::clone(&hb);
      let v62 = Clone::clone(&hc);
      let v64 = Clone::clone(&st);
      mark_b(v48, v50, v52, v54, v56, a, v60, v62, v64, s)
    }
  };
  let v70: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v27);
  for_::<Rc<Array<u64>>>(v70, 1u64, add(ha, 1u64), s)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.mex_loop
// Variant: uncurried
pub fn mex_loop_1(s: Rc<Array<u64>>, st: u64, L: u64, t: u64) -> u64 {
  mex_loop(s, st, L, t, ())
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.mex_loop (local: mex_loop)
// Variant: uncurried, lifted
pub fn mex_loop(s: Rc<Array<u64>>, st: u64, L: u64, t: u64, _H: ()) -> u64 {
  let v12 = ltb(t, L);
  match bdec(v12) {
    sumbool::left => {
      let v17 = &s;
      let v21 = rocq_array::get::<u64>(&v17, t);
      match eqb(v21, st) {
        true => {
          mex_loop(s, st, L, add(t, 1u64), ())
        },
        false => {
          std::mem::drop(s);
          t
        },
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
pub fn cell(D: u64, L: u64, x: u64, y: u64, z: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  match st {
    (v7, v9) => {
      let seen = &v7;
      let k = cidx(D, x, y, z);
      let stamp = add(k, 1u64);
      let v46 = div(add(x, 1u64), 2u64);
      let v62 = div(add(y, 1u64), 2u64);
      let v78 = div(add(z, 1u64), 2u64);
      let v80 = Rc::clone(seen);
      let seen_1 = mark_a(v80, D, x, y, z, v46, v62, v78, stamp, v9);
      let v105 = Rc::clone(&seen_1);
      let m = mex_loop_1(v105, stamp, L, 0u64);
      let v120 = rocq_array::set::<u64>(v7, k, m);
      (v120, seen_1)
    },
  }
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.table
// Variant: uncurried
pub fn table(D: u64, L: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v7 = {
    let __anf_capture_8 = L;
    let __anf_capture_10 = D;
    move |x: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
      let L = &__anf_capture_8;
      let D = &__anf_capture_10;
      let v16 = Clone::clone(L);
      let v20 = Clone::clone(D);
      let v21 = {
        let __anf_capture_24 = x;
        move |y: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
          let L = &v16;
          let x = &__anf_capture_24;
          let D = &v20;
          let v32 = Clone::clone(D);
          let v34 = Clone::clone(L);
          let v36 = Clone::clone(x);
          let v39 = {
            let __anf_capture_46 = y;
            move |z: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
              let v52 = Clone::clone(&v32);
              let v54 = Clone::clone(&v34);
              let v56 = Clone::clone(&v36);
              let v58 = Clone::clone(&__anf_capture_46);
              cell(v52, v54, v56, v58, z, st)
            }
          };
          let v66: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new(v39);
          let v73 = Clone::clone(D);
          for_::<(Rc<Array<u64>>, Rc<Array<u64>>)>(v66, y, v73, st)
        }
      };
      let v79: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new(v21);
      let v86 = Clone::clone(D);
      for_::<(Rc<Array<u64>>, Rc<Array<u64>>)>(v79, x, v86, st)
    }
  };
  let v92: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new(v7);
  let v102 = rocq_array::make::<u64>(L, 0u64);
  let v109 = rocq_array::make::<u64>(L, 0u64);
  for_::<(Rc<Array<u64>>, Rc<Array<u64>>)>(v92, 1u64, D, (v102, v109))
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
pub fn winner_impl(s: player, xs: Rc<Array<u64>>, ys: Rc<Array<u64>>, zs: Rc<Array<u64>>) -> player {
  let v4 = &xs;
  let n = rocq_array::length::<u64>(&v4);
  let v9 = Rc::clone(&xs);
  let v12 = Rc::clone(&ys);
  let v15 = Rc::clone(&zs);
  let v16 = {
    move |i: u64, m: u64| -> u64 {
      let xs = &v9;
      let ys = &v12;
      let zs = &v15;
      let v29 = rocq_array::get::<u64>(&xs, i);
      let v33 = rocq_array::get::<u64>(&ys, i);
      let v36 = rocq_array::get::<u64>(&zs, i);
      let v41 = imax(v33, v36);
      let v46 = imax(v29, v41);
      imax(m, v46)
    }
  };
  let v54: Rc<dyn Fn(u64, u64) -> u64> = Rc::new(v16);
  let M = for_::<u64>(v54, 0u64, n, 0u64);
  let D = add(M, 1u64);
  let v84 = mul(D, D);
  let L = mul(v84, D);
  let T = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(table(D, L));
  let v102 = Rc::clone(&xs);
  let v105 = Rc::clone(&ys);
  let v108 = Rc::clone(&zs);
  let v111 = Rc::clone(&T);
  let v114 = {
    let __anf_capture_123 = D;
    move |i: u64, acc: u64| -> u64 {
      let xs = &v102;
      let ys = &v105;
      let zs = &v108;
      let T = &v111;
      let D = &__anf_capture_123;
      let v130 = rocq_array::get::<u64>(&xs, i);
      let v133 = rocq_array::get::<u64>(&ys, i);
      let v136 = rocq_array::get::<u64>(&zs, i);
      let v147 = look(T, Clone::clone(D), v130, v133, v136);
      lxor(acc, v147)
    }
  };
  let v155: Rc<dyn Fn(u64, u64) -> u64> = Rc::new(v114);
  let gx = for_::<u64>(v155, 0u64, n, 0u64);
  match eqb(gx, 0u64) {
    true => {
      std::mem::drop(T);
      std::mem::drop(xs);
      std::mem::drop(ys);
      std::mem::drop(zs);
      opponent(s)
    },
    false => {
      std::mem::drop(T);
      std::mem::drop(xs);
      std::mem::drop(ys);
      std::mem::drop(zs);
      s
    },
  }
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.winner_impl
pub fn winner_impl_curried(s: player) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> player>>> {
  let v3 = {
    move |xs: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> player>> {
      let s = &s;
      let v8 = Clone::clone(s);
      let v11 = {
        move |ys: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> player> {
          let s = &v8;
          let xs = &xs;
          let v18 = Clone::clone(s);
          let v20 = Rc::clone(xs);
          let v23 = {
            move |zs: Rc<Array<u64>>| -> player {
              let v33 = Clone::clone(&v18);
              let v35 = Rc::clone(&v20);
              let v37 = Rc::clone(&ys);
              winner_impl(v33, v35, v37, zs)
            }
          };
          let v43: Rc<dyn Fn(Rc<Array<u64>>) -> player> = Rc::new(v23);
          v43
        }
      };
      let v47: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> player>> = Rc::new(v11);
      v47
    }
  };
  let v51: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> player>>> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(player, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> player> {
  let v0: Rc<dyn Fn(player, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> player> = __rocq_global_824.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_824: Rc<dyn Fn(player, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> player> = winner(); }
std::thread_local! { static __rocq_global_827: Rc<dyn Fn(player) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> player>>>> = winner_curried(); }