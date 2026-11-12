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

// Rocq: Basincity.basincity_implem.basincity
// Variant: uncurried
pub fn basincity() -> Rc<dyn Fn(u64, Rc<Array<Rc<Array<u64>>>>) -> bool> {
  let v0: fn(u64, Rc<Array<Rc<Array<u64>>>>) -> bool = basincity_impl;
  let v1: Rc<dyn Fn(u64, Rc<Array<Rc<Array<u64>>>>) -> bool> = Rc::new(v0);
  v1
}

// Rocq: Basincity.basincity_implem.basincity
pub fn basincity_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> bool>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> bool> = basincity_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> bool>> = Rc::new(v0);
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

// Rocq: Basincity.basincity_implem.bdec
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

// Rocq: Basincity.basincity_implem.fill_dg
// Variant: uncurried
pub fn fill_dg_1(y: Rc<Array<Rc<Array<u64>>>>, n: u64, i: u64, dg: Rc<Array<u64>>) -> Rc<Array<u64>> {
  fill_dg(y, n, i, dg, ())
}

// Rocq: Basincity.basincity_implem.fill_dg (local: fill_dg)
// Variant: uncurried, lifted
pub fn fill_dg(y: Rc<Array<Rc<Array<u64>>>>, n: u64, i: u64, dg: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v26 = Rc::clone(&y);
      let v30 = rocq_array::get::<Rc<Array<u64>>>(&v26, i);
      std::mem::drop(v26);
      let v31 = &v30;
      let v32 = rocq_array::length::<u64>(&v31);
      std::mem::drop(v30);
      let v39 = rocq_array::set::<u64>(dg, i, v32);
      fill_dg(y, n, v23, v39, ())
    },
    sumbool::right => {
      std::mem::drop(y);
      dg
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Basincity.basincity_implem.put_slot
// Variant: uncurried
pub fn put_slot(row: Rc<Array<u64>>, b: u64, j: u64, nb: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v5 = &row;
  let v6 = rocq_array::length::<u64>(&v5);
  match ltb(j, v6) {
    true => {
      let v18 = add(b, j);
      let v20 = &row;
      let v23 = rocq_array::get::<u64>(&v20, j);
      std::mem::drop(row);
      rocq_array::set::<u64>(nb, v18, sub(v23, 1u64))
    },
    false => {
      std::mem::drop(row);
      nb
    },
  }
}

// Rocq: Basincity.basincity_implem.fill_nb
// Variant: uncurried
pub fn fill_nb_1(y: Rc<Array<Rc<Array<u64>>>>, n: u64, i: u64, nb: Rc<Array<u64>>) -> Rc<Array<u64>> {
  fill_nb(y, n, i, nb, ())
}

// Rocq: Basincity.basincity_implem.fill_nb (local: fill_nb)
// Variant: uncurried, lifted
pub fn fill_nb(y: Rc<Array<Rc<Array<u64>>>>, n: u64, i: u64, nb: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v18 = Rc::clone(&y);
      let row = rocq_array::get::<Rc<Array<u64>>>(&v18, i);
      std::mem::drop(v18);
      let b = mul(4u64, i);
      let v38 = add(i, 1u64);
      let v53 = Rc::clone(&row);
      let v60 = put_slot(v53, b, 0u64, nb);
      let v63 = Rc::clone(&row);
      let v70 = put_slot(v63, b, 1u64, v60);
      let v73 = Rc::clone(&row);
      let v80 = put_slot(v73, b, 2u64, v70);
      let v89 = put_slot(row, b, 3u64, v80);
      fill_nb(y, n, v38, v89, ())
    },
    sumbool::right => {
      std::mem::drop(y);
      nb
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Basincity.basincity_implem.alive
// Variant: uncurried
pub fn alive_owned(rm: Rc<Array<u64>>, x: u64) -> bool {
  let v3 = &rm;
  let v6 = rocq_array::get::<u64>(&v3, x);
  std::mem::drop(rm);
  eqb(v6, 0u64)
}

// Rocq: Basincity.basincity_implem.alive
// Variant: borrowed, uncurried
pub fn alive(rm: &Rc<Array<u64>>, x: u64) -> bool {
  let x_1 = x;
  let v4 = rm;
  eqb(rocq_array::get::<u64>(&v4, x_1), 0u64)
}

// Rocq: Basincity.basincity_implem.cnt_loop
// Variant: uncurried
pub fn cnt_loop_1(n: u64, rm: Rc<Array<u64>>, i: u64, acc: u64) -> u64 {
  cnt_loop(n, rm, i, acc, ())
}

// Rocq: Basincity.basincity_implem.cnt_loop (local: cnt_loop)
// Variant: uncurried, lifted
pub fn cnt_loop(n: u64, rm: Rc<Array<u64>>, i: u64, acc: u64, _H: ()) -> u64 {
  let v12 = ltb(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v27 = Rc::clone(&rm);
      let v31 = match alive_owned(v27, i) {
        true => {
          add(acc, 1u64)
        },
        false => {
          acc
        },
      };
      cnt_loop(n, rm, v23, v31, ())
    },
    sumbool::right => {
      std::mem::drop(rm);
      acc
    },
  }
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

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  match b {
    true => {
      false
    },
    false => {
      true
    },
  }
}

// Rocq: Basincity.basincity_implem.forall4
// Variant: uncurried
pub fn forall4(f: Rc<dyn Fn(u64) -> bool>, d: u64) -> bool {
  let v17 = negb(ltb(0u64, d));
  let v20: &Rc<dyn Fn(u64) -> bool> = &f;
  let v23 = v20(0u64);
  let v28 = orb(v17, v23);
  let v41 = negb(ltb(1u64, d));
  let v44: &Rc<dyn Fn(u64) -> bool> = &f;
  let v47 = v44(1u64);
  let v57 = andb(v28, orb(v41, v47));
  let v70 = negb(ltb(2u64, d));
  let v73: &Rc<dyn Fn(u64) -> bool> = &f;
  let v76 = v73(2u64);
  let v86 = andb(v57, orb(v70, v76));
  let v99 = negb(ltb(3u64, d));
  let v102: &Rc<dyn Fn(u64) -> bool> = &f;
  let v105 = v102(3u64);
  std::mem::drop(f);
  andb(v86, orb(v99, v105))
}

// Rocq: Basincity.basincity_implem.nbr
// Variant: uncurried
pub fn nbr_owned(nb: Rc<Array<u64>>, v: u64, j: u64) -> u64 {
  let v16 = add(mul(4u64, v), j);
  let v17 = &nb;
  let v20 = rocq_array::get::<u64>(&v17, v16);
  std::mem::drop(nb);
  v20
}

// Rocq: Basincity.basincity_implem.nbr
// Variant: borrowed, uncurried
pub fn nbr(nb: &Rc<Array<u64>>, v: u64, j: u64) -> u64 {
  let v_1 = v;
  let j_1 = j;
  let v18 = add(mul(4u64, v_1), j_1);
  let v19 = nb;
  rocq_array::get::<u64>(&v19, v18)
}

// Rocq: Basincity.basincity_implem.exists4
// Variant: uncurried
pub fn exists4(f: Rc<dyn Fn(u64) -> bool>, d: u64) -> bool {
  let v13 = ltb(0u64, d);
  let v16: &Rc<dyn Fn(u64) -> bool> = &f;
  let v19 = v16(0u64);
  let v24 = andb(v13, v19);
  let v33 = ltb(1u64, d);
  let v36: &Rc<dyn Fn(u64) -> bool> = &f;
  let v39 = v36(1u64);
  let v49 = orb(v24, andb(v33, v39));
  let v58 = ltb(2u64, d);
  let v61: &Rc<dyn Fn(u64) -> bool> = &f;
  let v64 = v61(2u64);
  let v74 = orb(v49, andb(v58, v64));
  let v83 = ltb(3u64, d);
  let v86: &Rc<dyn Fn(u64) -> bool> = &f;
  let v89 = v86(3u64);
  std::mem::drop(f);
  orb(v74, andb(v83, v89))
}

// Rocq: Basincity.basincity_implem.adjb
// Variant: borrowed, uncurried
pub fn adjb(nb: &Rc<Array<u64>>, dg: &Rc<Array<u64>>, a: u64, x: u64) -> bool {
  let v9 = Rc::clone(nb);
  let v14 = {
    let __anf_capture_17 = a;
    move |j: u64| -> bool {
      let nb = &v9;
      let a = &__anf_capture_17;
      let x = &x;
      let v29 = nbr(nb, Clone::clone(a), j);
      let v31 = Clone::clone(x);
      eqb(v31, v29)
    }
  };
  let v37: Rc<dyn Fn(u64) -> bool> = Rc::new(v14);
  let v39 = dg;
  exists4(v37, rocq_array::get::<u64>(&v39, a))
}

// Rocq: Basincity.basincity_implem.simp
// Variant: uncurried
pub fn simp(nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, rm: Rc<Array<u64>>, v: u64) -> bool {
  let v4 = &dg;
  let d = rocq_array::get::<u64>(&v4, v);
  let v19 = {
    let __anf_capture_22 = v;
    let __anf_capture_26 = dg;
    let __anf_capture_28 = d;
    move |j1: u64| -> bool {
      let rm = &rm;
      let v = &__anf_capture_22;
      let nb = &nb;
      let dg = &__anf_capture_26;
      let d = &__anf_capture_28;
      let v33 = Rc::clone(rm);
      let v37 = Clone::clone(v);
      let v39 = Rc::clone(nb);
      let v41 = Rc::clone(dg);
      let v42 = {
        move |j2: u64| -> bool {
          let rm = &v33;
          let j1 = &j1;
          let v = &v37;
          let nb = &v39;
          let dg = &v41;
          let v83 = orb(leb(j2, Clone::clone(j1)), negb(alive(rm, nbr(nb, Clone::clone(v), Clone::clone(j1)))));
          let v104 = orb(v83, negb(alive(rm, nbr(nb, Clone::clone(v), j2))));
          let v111 = nbr(nb, Clone::clone(v), Clone::clone(j1));
          let v113 = Clone::clone(v);
          let v117 = nb;
          let v126 = adjb(nb, dg, v111, nbr(v117, v113, j2));
          orb(v104, v126)
        }
      };
      let v134: Rc<dyn Fn(u64) -> bool> = Rc::new(v42);
      let v139 = Clone::clone(d);
      forall4(v134, v139)
    }
  };
  let v143: Rc<dyn Fn(u64) -> bool> = Rc::new(v19);
  forall4(v143, d)
}

// Rocq: Basincity.basincity_implem.b2i
pub fn b2i(b: bool) -> u64 {
  match b {
    true => {
      1u64
    },
    false => {
      0u64
    },
  }
}

// Rocq: Basincity.basincity_implem.count4
// Variant: uncurried
pub fn count4(f: Rc<dyn Fn(u64) -> bool>, d: u64) -> u64 {
  let v14 = ltb(0u64, d);
  let v17: &Rc<dyn Fn(u64) -> bool> = &f;
  let v20 = v17(0u64);
  let v28 = b2i(andb(v14, v20));
  let v38 = ltb(1u64, d);
  let v41: &Rc<dyn Fn(u64) -> bool> = &f;
  let v44 = v41(1u64);
  let v57 = add(v28, b2i(andb(v38, v44)));
  let v67 = ltb(2u64, d);
  let v70: &Rc<dyn Fn(u64) -> bool> = &f;
  let v73 = v70(2u64);
  let v86 = add(v57, b2i(andb(v67, v73)));
  let v96 = ltb(3u64, d);
  let v99: &Rc<dyn Fn(u64) -> bool> = &f;
  let v102 = v99(3u64);
  std::mem::drop(f);
  add(v86, b2i(andb(v96, v102)))
}

// Rocq: Basincity.basincity_implem.deg
// Variant: uncurried
pub fn deg(nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, rm: Rc<Array<u64>>, v: u64) -> u64 {
  let v11 = {
    let __anf_capture_14 = v;
    move |j: u64| -> bool {
      let nb = &nb;
      let v = &__anf_capture_14;
      let rm = &rm;
      let v26 = nbr(nb, Clone::clone(v), j);
      alive(rm, v26)
    }
  };
  let v33: Rc<dyn Fn(u64) -> bool> = Rc::new(v11);
  let v35 = &dg;
  let v38 = rocq_array::get::<u64>(&v35, v);
  std::mem::drop(dg);
  count4(v33, v38)
}

// Rocq: Basincity.basincity_implem.sel_loop
// Variant: uncurried
pub fn sel_loop_1(n: u64, nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, rm: Rc<Array<u64>>, i: u64, best: u64, bd: u64) -> (u64, bool) {
  sel_loop(n, nb, dg, rm, i, best, bd, ())
}

// Rocq: Basincity.basincity_implem.sel_loop (local: sel_loop)
// Variant: uncurried, lifted
pub fn sel_loop(n: u64, nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, rm: Rc<Array<u64>>, i: u64, best: u64, bd: u64, _H: ()) -> (u64, bool) {
  let v15 = ltb(i, n);
  match bdec(v15) {
    sumbool::left => {
      let v22 = Rc::clone(&rm);
      match alive_owned(v22, i) {
        true => {
          let v30 = Rc::clone(&nb);
          let v33 = Rc::clone(&dg);
          let v36 = Rc::clone(&rm);
          match simp(v30, v33, v36, i) {
            true => {
              std::mem::drop(nb);
              std::mem::drop(dg);
              std::mem::drop(rm);
              (i, true)
            },
            false => {
              let v54 = Rc::clone(&nb);
              let v57 = Rc::clone(&dg);
              let v60 = Rc::clone(&rm);
              let d = deg(v54, v57, v60, i);
              match ltb(d, bd) {
                true => {
                  sel_loop(n, nb, dg, rm, add(i, 1u64), i, d, ())
                },
                false => {
                  sel_loop(n, nb, dg, rm, add(i, 1u64), best, bd, ())
                },
              }
            },
          }
        },
        false => {
          sel_loop(n, nb, dg, rm, add(i, 1u64), best, bd, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(nb);
      std::mem::drop(dg);
      std::mem::drop(rm);
      (best, false)
    },
  }
}

// Rocq: Basincity.basincity_implem.mark1
// Variant: uncurried
pub fn mark1(w: u64, k: u64, rm: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v4 = &rm;
  let v7 = rocq_array::get::<u64>(&v4, w);
  match eqb(v7, 0u64) {
    true => {
      rocq_array::set::<u64>(rm, w, k)
    },
    false => {
      rm
    },
  }
}

// Rocq: Basincity.basincity_implem.mark
// Variant: uncurried
pub fn mark(nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, u: u64, k: u64, rm: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v5 = &dg;
  let d = rocq_array::get::<u64>(&v5, u);
  let rm_1 = mark1(u, k, rm);
  let v19 = 0u64;
  let rm_2 = match ltb(v19, d) {
    true => {
      let v32 = Rc::clone(&nb);
      mark1(nbr_owned(v32, u, 0u64), k, rm_1)
    },
    false => {
      rm_1
    },
  };
  let v52 = 1u64;
  let rm_3 = match ltb(v52, d) {
    true => {
      let v65 = Rc::clone(&nb);
      mark1(nbr_owned(v65, u, 1u64), k, rm_2)
    },
    false => {
      rm_2
    },
  };
  let v85 = 2u64;
  let rm_4 = match ltb(v85, d) {
    true => {
      let v98 = Rc::clone(&nb);
      mark1(nbr_owned(v98, u, 2u64), k, rm_3)
    },
    false => {
      rm_3
    },
  };
  match ltb(3u64, d) {
    true => {
      std::mem::drop(dg);
      mark1(nbr_owned(nb, u, 3u64), k, rm_4)
    },
    false => {
      std::mem::drop(nb);
      std::mem::drop(dg);
      rm_4
    },
  }
}

// Rocq: Basincity.basincity_implem.unmark1
// Variant: uncurried
pub fn unmark1(w: u64, k: u64, rm: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v4 = &rm;
  let v8 = rocq_array::get::<u64>(&v4, w);
  match eqb(v8, k) {
    true => {
      rocq_array::set::<u64>(rm, w, 0u64)
    },
    false => {
      rm
    },
  }
}

// Rocq: Basincity.basincity_implem.unmark
// Variant: uncurried
pub fn unmark(nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, u: u64, k: u64, rm: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v5 = &dg;
  let d = rocq_array::get::<u64>(&v5, u);
  let rm_1 = unmark1(u, k, rm);
  let v19 = 0u64;
  let rm_2 = match ltb(v19, d) {
    true => {
      let v32 = Rc::clone(&nb);
      unmark1(nbr_owned(v32, u, 0u64), k, rm_1)
    },
    false => {
      rm_1
    },
  };
  let v52 = 1u64;
  let rm_3 = match ltb(v52, d) {
    true => {
      let v65 = Rc::clone(&nb);
      unmark1(nbr_owned(v65, u, 1u64), k, rm_2)
    },
    false => {
      rm_2
    },
  };
  let v85 = 2u64;
  let rm_4 = match ltb(v85, d) {
    true => {
      let v98 = Rc::clone(&nb);
      unmark1(nbr_owned(v98, u, 2u64), k, rm_3)
    },
    false => {
      rm_3
    },
  };
  match ltb(3u64, d) {
    true => {
      std::mem::drop(dg);
      unmark1(nbr_owned(nb, u, 3u64), k, rm_4)
    },
    false => {
      std::mem::drop(nb);
      std::mem::drop(dg);
      rm_4
    },
  }
}

// Rocq: Basincity.basincity_implem.child
// Variant: uncurried
pub fn child(nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, rec: Rc<dyn Fn(Rc<Array<u64>>) -> (bool, Rc<Array<u64>>)>, k: u64, u: u64, rm: Rc<Array<u64>>) -> (bool, Rc<Array<u64>>) {
  let v9 = Rc::clone(&nb);
  let v12 = Rc::clone(&dg);
  let rm1 = mark(v9, v12, u, k, rm);
  let v20: &Rc<dyn Fn(Rc<Array<u64>>) -> (bool, Rc<Array<u64>>)> = &rec;
  let v23 = v20(rm1);
  std::mem::drop(rec);
  match v23 {
    (v25, v27) => {
      let v40 = unmark(nb, dg, u, k, v27);
      (v25, v40)
    },
  }
}

// Rocq: Basincity.basincity_implem.try_slot
// Variant: uncurried
pub fn try_slot(nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, rec: Rc<dyn Fn(Rc<Array<u64>>) -> (bool, Rc<Array<u64>>)>, k: u64, v: u64, j: u64, r: (bool, Rc<Array<u64>>)) -> (bool, Rc<Array<u64>>) {
  match r {
    (v8, v10) => {
      let b = &v10;
      match v8 {
        true => {
          std::mem::drop(nb);
          std::mem::drop(dg);
          std::mem::drop(rec);
          (true, v10)
        },
        false => {
          let v25 = &dg;
          let v28 = rocq_array::get::<u64>(&v25, v);
          match ltb(j, v28) {
            true => {
              let v38 = Rc::clone(&nb);
              let u = nbr_owned(v38, v, j);
              let v46 = Rc::clone(b);
              match alive_owned(v46, u) {
                true => {
                  child(nb, dg, rec, k, u, v10)
                },
                false => {
                  std::mem::drop(nb);
                  std::mem::drop(rec);
                  std::mem::drop(dg);
                  (false, v10)
                },
              }
            },
            false => {
              std::mem::drop(nb);
              std::mem::drop(rec);
              std::mem::drop(dg);
              (false, v10)
            },
          }
        },
      }
    },
  }
}

// Rocq: Basincity.basincity_implem.node
// Variant: uncurried
pub fn node(n: u64, nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, rec: Rc<dyn Fn(Rc<Array<u64>>) -> (bool, Rc<Array<u64>>)>, k: u64, rm: Rc<Array<u64>>) -> (bool, Rc<Array<u64>>) {
  let v14 = mul(5u64, k);
  let v24 = Rc::clone(&rm);
  let v29 = cnt_loop_1(n, v24, 0u64, 0u64);
  match leb(v14, v29) {
    true => {
      std::mem::drop(nb);
      std::mem::drop(dg);
      std::mem::drop(rec);
      (true, rm)
    },
    false => {
      let v55 = Rc::clone(&nb);
      let v58 = Rc::clone(&dg);
      let v61 = Rc::clone(&rm);
      let v68 = sel_loop_1(n, v55, v58, v61, 0u64, n, 5u64);
      match v68 {
        (v70, v72) => {
          match v72 {
            true => {
              child(nb, dg, rec, k, v70, rm)
            },
            false => {
              match ltb(v70, n) {
                true => {
                  let v113 = Rc::clone(&nb);
                  let v116 = Rc::clone(&dg);
                  let v118: Rc<dyn Fn(Rc<Array<u64>>) -> (bool, Rc<Array<u64>>)> = Rc::clone(&rec);
                  let v126 = child(v113, v116, v118, k, v70, rm);
                  let v129 = Rc::clone(&nb);
                  let v132 = Rc::clone(&dg);
                  let v134: Rc<dyn Fn(Rc<Array<u64>>) -> (bool, Rc<Array<u64>>)> = Rc::clone(&rec);
                  let v144 = try_slot(v129, v132, v134, k, v70, 0u64, v126);
                  let v147 = Rc::clone(&nb);
                  let v150 = Rc::clone(&dg);
                  let v152: Rc<dyn Fn(Rc<Array<u64>>) -> (bool, Rc<Array<u64>>)> = Rc::clone(&rec);
                  let v162 = try_slot(v147, v150, v152, k, v70, 1u64, v144);
                  let v165 = Rc::clone(&nb);
                  let v168 = Rc::clone(&dg);
                  let v170: Rc<dyn Fn(Rc<Array<u64>>) -> (bool, Rc<Array<u64>>)> = Rc::clone(&rec);
                  let v180 = try_slot(v165, v168, v170, k, v70, 2u64, v162);
                  try_slot(nb, dg, rec, k, v70, 3u64, v180)
                },
                false => {
                  std::mem::drop(nb);
                  std::mem::drop(dg);
                  std::mem::drop(rec);
                  (false, rm)
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Basincity.basincity_implem.search
// Variant: uncurried
pub fn search_1(n: u64, nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, k: u64, rm: Rc<Array<u64>>) -> (bool, Rc<Array<u64>>) {
  search(n, nb, dg, k, rm, ())
}

// Rocq: Basincity.basincity_implem.search (local: search)
// Variant: uncurried, lifted
pub fn search(n: u64, nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, k: u64, rm: Rc<Array<u64>>, _H: ()) -> (bool, Rc<Array<u64>>) {
  let v15 = eqb(k, 0u64);
  match bdec(v15) {
    sumbool::left => {
      std::mem::drop(nb);
      std::mem::drop(dg);
      (true, rm)
    },
    sumbool::right => {
      let v36 = Rc::clone(&nb);
      let v39 = Rc::clone(&dg);
      let v40 = {
        let __anf_capture_41 = k;
        let __anf_capture_43 = n;
        move |rm_: Rc<Array<u64>>| -> (bool, Rc<Array<u64>>) {
          let v52 = 1u64;
          let v57 = sub(Clone::clone(&__anf_capture_41), v52);
          let v62 = Clone::clone(&__anf_capture_43);
          let v64 = Rc::clone(&v36);
          let v66 = Rc::clone(&v39);
          search(v62, v64, v66, v57, rm_, ())
        }
      };
      let v76: Rc<dyn Fn(Rc<Array<u64>>) -> (bool, Rc<Array<u64>>)> = Rc::new(v40);
      node(n, nb, dg, v76, k, rm)
    },
  }
}

// Rocq: Basincity.basincity_implem.basincity_impl
// Variant: uncurried
pub fn basincity_impl(k: u64, y: Rc<Array<Rc<Array<u64>>>>) -> bool {
  let v2 = &y;
  let n = rocq_array::length::<Rc<Array<u64>>>(&v2);
  let v13 = rocq_array::make::<u64>(n, 0u64);
  let v16 = Rc::clone(&y);
  let dg = fill_dg_1(v16, n, 0u64, v13);
  let v41 = rocq_array::make::<u64>(mul(4u64, n), 0u64);
  let nb = fill_nb_1(y, n, 0u64, v41);
  let v59 = rocq_array::make::<u64>(n, 0u64);
  fst::<bool, Rc<Array<u64>>>(search_1(n, nb, dg, k, v59))
}

// Rocq: Basincity.basincity_implem.basincity_impl
pub fn basincity_impl_curried(k: u64) -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> bool> {
  let v3 = {
    move |y: Rc<Array<Rc<Array<u64>>>>| -> bool {
      let v9 = Clone::clone(&k);
      basincity_impl(v9, y)
    }
  };
  let v15: Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> bool> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<Rc<Array<u64>>>>) -> bool> {
  let v0: Rc<dyn Fn(u64, Rc<Array<Rc<Array<u64>>>>) -> bool> = __rocq_global_1029.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_1029: Rc<dyn Fn(u64, Rc<Array<Rc<Array<u64>>>>) -> bool> = basincity(); }
std::thread_local! { static __rocq_global_1032: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> bool>> = basincity_curried(); }