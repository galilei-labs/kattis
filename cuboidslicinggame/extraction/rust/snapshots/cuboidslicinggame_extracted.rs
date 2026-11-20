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
  if b {
    sumbool::left
  } else {
    sumbool::right
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
  let tmp = ltb(i, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let f_ref: &Rc<dyn Fn(u64, A) -> A> = &f;
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
  if leb(a, b) {
    b
  } else {
    a
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.cidx
// Variant: uncurried
pub fn cidx(D: u64, x: u64, y: u64, z: u64) -> u64 {
  let tmp = add(mul(x, D), y);
  add(mul(tmp, D), z)
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
  if leb(a, b) {
    a
  } else {
    b
  }
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.look
// Variant: borrowed, uncurried
pub fn look(T: &Rc<Array<u64>>, D: u64, x: u64, y: u64, z: u64) -> u64 {
  let D_1 = D;
  let x_1 = x;
  let y_1 = y;
  let z_1 = z;
  let tmp = imin(y_1, z_1);
  let lo = imin(x_1, tmp);
  let tmp_1 = imax(y_1, z_1);
  let hi = imax(x_1, tmp_1);
  let tmp_2 = add(x_1, y_1);
  let tmp_3 = sub(add(tmp_2, z_1), lo);
  rocq_array::get::<u64>(T, cidx(D_1, lo, sub(tmp_3, hi), hi))
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
  let tmp = look(T, D_1, p1, q1, r1);
  let tmp_1 = look(T, D_1, p1, q1, r2);
  let tmp_2 = look(T, D_1, p1, q2, r1);
  let tmp_3 = look(T, D_1, p1, q2, r2);
  let tmp_4 = look(T, D_1, p2, q1, r1);
  let tmp_5 = look(T, D_1, p2, q1, r2);
  let tmp_6 = lxor(look(T, D_1, p2, q2, r1), look(T, D_1, p2, q2, r2));
  let tmp_7 = lxor(tmp_5, tmp_6);
  let tmp_8 = lxor(tmp_4, tmp_7);
  let tmp_9 = lxor(tmp_3, tmp_8);
  let tmp_10 = lxor(tmp_2, tmp_9);
  let tmp_11 = lxor(tmp_1, tmp_10);
  lxor(tmp, tmp_11)
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.mark_c
// Variant: uncurried
pub fn mark_c(T: Rc<Array<u64>>, D: u64, x: u64, y: u64, z: u64, a: u64, b: u64, hc: u64, st: u64, s: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
    move |c: u64, s: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let T = &T;
      let D = &D;
      let x = &x;
      let y = &y;
      let z = &z;
      let a = &a;
      let b = &b;
      let st = &st;
      let tmp = cutv(T, Clone::clone(D), Clone::clone(x), Clone::clone(y), Clone::clone(z), Clone::clone(a), Clone::clone(b), c);
      let st_clone = Clone::clone(st);
      rocq_array::set::<u64>(s, tmp, st_clone)
    }
  });
  for_::<Rc<Array<u64>>>(callback, 1u64, add(hc, 1u64), s)
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.mark_b
// Variant: uncurried
pub fn mark_b(T: Rc<Array<u64>>, D: u64, x: u64, y: u64, z: u64, a: u64, hb: u64, hc: u64, st: u64, s: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
    move |b: u64, s: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let T_clone = Rc::clone(&T);
      let D_clone = Clone::clone(&D);
      let x_clone = Clone::clone(&x);
      let y_clone = Clone::clone(&y);
      let z_clone = Clone::clone(&z);
      let a_clone = Clone::clone(&a);
      let hc_clone = Clone::clone(&hc);
      let st_clone = Clone::clone(&st);
      mark_c(T_clone, D_clone, x_clone, y_clone, z_clone, a_clone, b, hc_clone, st_clone, s)
    }
  });
  for_::<Rc<Array<u64>>>(callback, 1u64, add(hb, 1u64), s)
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.mark_a
// Variant: uncurried
pub fn mark_a(T: Rc<Array<u64>>, D: u64, x: u64, y: u64, z: u64, ha: u64, hb: u64, hc: u64, st: u64, s: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
    move |a: u64, s: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let T_clone = Rc::clone(&T);
      let D_clone = Clone::clone(&D);
      let x_clone = Clone::clone(&x);
      let y_clone = Clone::clone(&y);
      let z_clone = Clone::clone(&z);
      let hb_clone = Clone::clone(&hb);
      let hc_clone = Clone::clone(&hc);
      let st_clone = Clone::clone(&st);
      mark_b(T_clone, D_clone, x_clone, y_clone, z_clone, a, hb_clone, hc_clone, st_clone, s)
    }
  });
  for_::<Rc<Array<u64>>>(callback, 1u64, add(ha, 1u64), s)
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
  let tmp = ltb(t, L);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&s, t);
      if eqb(tmp_1, st) {
        mex_loop(s, st, L, add(t, 1u64), ())
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
pub fn cell(D: u64, L: u64, x: u64, y: u64, z: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  match st {
    (v7, v9) => {
      let seen = &v7;
      let k = cidx(D, x, y, z);
      let stamp = add(k, 1u64);
      let tmp = div(add(x, 1u64), 2u64);
      let tmp_1 = div(add(y, 1u64), 2u64);
      let tmp_2 = div(add(z, 1u64), 2u64);
      let seen_clone = Rc::clone(seen);
      let seen_1 = mark_a(seen_clone, D, x, y, z, tmp, tmp_1, tmp_2, stamp, v9);
      let seen_clone_1 = Rc::clone(&seen_1);
      let m = mex_loop_1(seen_clone_1, stamp, L, 0u64);
      let tmp_3 = rocq_array::set::<u64>(v7, k, m);
      (tmp_3, seen_1)
    },
  }
}

// Rocq: Cuboidslicinggame.cuboidslicinggame_implem.table
// Variant: uncurried
pub fn table(D: u64, L: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let callback: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new({
    let __anf_capture_8 = L;
    let __anf_capture_10 = D;
    move |x: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
      let L = &__anf_capture_8;
      let D = &__anf_capture_10;
      let L_clone = Clone::clone(L);
      let D_clone = Clone::clone(D);
      let callback_1: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new({
        let __anf_capture_24 = x;
        move |y: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
          let L = &L_clone;
          let x = &__anf_capture_24;
          let D = &D_clone;
          let D_clone_1 = Clone::clone(D);
          let L_clone_1 = Clone::clone(L);
          let x_clone = Clone::clone(x);
          let callback_2: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new({
            let __anf_capture_46 = y;
            move |z: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
              let tmp = Clone::clone(&D_clone_1);
              let tmp_1 = Clone::clone(&L_clone_1);
              let tmp_2 = Clone::clone(&x_clone);
              let tmp_3 = Clone::clone(&__anf_capture_46);
              cell(tmp, tmp_1, tmp_2, tmp_3, z, st)
            }
          });
          let D_clone_2 = Clone::clone(D);
          for_::<(Rc<Array<u64>>, Rc<Array<u64>>)>(callback_2, y, D_clone_2, st)
        }
      });
      let D_clone_3 = Clone::clone(D);
      for_::<(Rc<Array<u64>>, Rc<Array<u64>>)>(callback_1, x, D_clone_3, st)
    }
  });
  let tmp_4 = rocq_array::make::<u64>(L, 0u64);
  let tmp_5 = rocq_array::make::<u64>(L, 0u64);
  for_::<(Rc<Array<u64>>, Rc<Array<u64>>)>(callback, 1u64, D, (tmp_4, tmp_5))
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
  let n = rocq_array::length::<u64>(&xs);
  let xs_clone = Rc::clone(&xs);
  let ys_clone = Rc::clone(&ys);
  let zs_clone = Rc::clone(&zs);
  let callback: Rc<dyn Fn(u64, u64) -> u64> = Rc::new({
    move |i: u64, m: u64| -> u64 {
      let xs = &xs_clone;
      let ys = &ys_clone;
      let zs = &zs_clone;
      let tmp = rocq_array::get::<u64>(xs, i);
      let tmp_1 = rocq_array::get::<u64>(ys, i);
      let tmp_2 = rocq_array::get::<u64>(zs, i);
      let tmp_3 = imax(tmp_1, tmp_2);
      let tmp_4 = imax(tmp, tmp_3);
      imax(m, tmp_4)
    }
  });
  let M = for_::<u64>(callback, 0u64, n, 0u64);
  let D = add(M, 1u64);
  let tmp_5 = mul(D, D);
  let L = mul(tmp_5, D);
  let T = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(table(D, L));
  let xs_clone_1 = Rc::clone(&xs);
  let ys_clone_1 = Rc::clone(&ys);
  let zs_clone_1 = Rc::clone(&zs);
  let T_clone = Rc::clone(&T);
  let callback_1: Rc<dyn Fn(u64, u64) -> u64> = Rc::new({
    let __anf_capture_123 = D;
    move |i: u64, acc: u64| -> u64 {
      let xs = &xs_clone_1;
      let ys = &ys_clone_1;
      let zs = &zs_clone_1;
      let T = &T_clone;
      let D = &__anf_capture_123;
      let tmp_6 = rocq_array::get::<u64>(xs, i);
      let tmp_7 = rocq_array::get::<u64>(ys, i);
      let tmp_8 = rocq_array::get::<u64>(zs, i);
      let tmp_9 = look(T, Clone::clone(D), tmp_6, tmp_7, tmp_8);
      lxor(acc, tmp_9)
    }
  });
  let gx = for_::<u64>(callback_1, 0u64, n, 0u64);
  if eqb(gx, 0u64) {
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
