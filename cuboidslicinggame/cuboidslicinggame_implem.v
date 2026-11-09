(* Executable implementation and its required termination dependencies.
   Correctness proofs are in cuboidslicinggame_proofs.v. *)
From Cuboidslicinggame.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Btauto.
Import ListNotations.

Unset Lia Cache.

(* ================================================================== *)
(* Part C. The program                                                *)
(* ================================================================== *)

Open Scope uint63_scope.
Open Scope array_scope.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

(* The one loop combinator: f lo (f (lo+1) ... acc), i ranging over [lo, hi). *)
Fixpoint loop {A : Type} (f : int -> A -> A) (hi i : int) (acc : A)
    (H : Acc (Zwf 0) (gap hi i)) {struct H} : A :=
  match bdec (i <? hi) with
  | left Hi => loop f hi (i + 1) (f i acc) (Acc_inv H (dec_step hi i Hi))
  | right _ => acc
  end.

Definition for_ {A : Type} (f : int -> A -> A) (lo hi : int) (acc : A) : A :=
  loop f hi lo acc (Zwf_well_founded 0 (gap hi lo)).

Definition imin (a b : int) : int := if a <=? b then a else b.
Definition imax (a b : int) : int := if a <=? b then b else a.

(* Cell (x, y, z) of the flat D x D x D table. *)
Definition cidx (D x y z : int) : int := (x * D + y) * D + z.

(* The Grundy number of x * y * z, read at its canonical cell (sides sorted). *)
Definition look (T : array int) (D x y z : int) : int :=
  let lo := imin x (imin y z) in
  let hi := imax x (imax y z) in
  T.[cidx D lo (x + y + z - lo - hi) hi].

(* The xor of the Grundy numbers of the pieces of the cut (a, b, c). *)
Definition cutv (T : array int) (D x y z a b c : int) : int :=
  let p1 := a - 1 in let p2 := x - a in
  let q1 := b - 1 in let q2 := y - b in
  let r1 := c - 1 in let r2 := z - c in
  look T D p1 q1 r1 lxor (look T D p1 q1 r2 lxor (look T D p1 q2 r1 lxor
  (look T D p1 q2 r2 lxor (look T D p2 q1 r1 lxor (look T D p2 q1 r2 lxor
  (look T D p2 q2 r1 lxor look T D p2 q2 r2)))))).

(* Stamp the values of the cuts a in [1, ha], b in [1, hb], c in [1, hc]. *)
Definition mark_c (T : array int) (D x y z a b hc st : int) (s : array int) : array int :=
  for_ (fun c s => s.[cutv T D x y z a b c <- st]) 1 (hc + 1) s.
Definition mark_b (T : array int) (D x y z a hb hc st : int) (s : array int) : array int :=
  for_ (fun b s => mark_c T D x y z a b hc st s) 1 (hb + 1) s.
Definition mark_a (T : array int) (D x y z ha hb hc st : int) (s : array int) : array int :=
  for_ (fun a s => mark_b T D x y z a hb hc st s) 1 (ha + 1) s.

(* The first t >= t0 whose cell does not carry the stamp. *)
Fixpoint mex_loop (s : array int) (st L t : int) (H : Acc (Zwf 0) (gap L t))
    {struct H} : int :=
  match bdec (t <? L) with
  | left Ht =>
      if s.[t] =? st then mex_loop s st L (t + 1) (Acc_inv H (dec_step L t Ht))
      else t
  | right _ => t
  end.

(* One canonical cell: stamp the values of its cuts up to mirroring, then mex. *)
Definition cell (D L x y z : int) (st : array int * array int) : array int * array int :=
  let (T, seen) := st in
  let k := cidx D x y z in
  let stamp := k + 1 in
  let seen := mark_a T D x y z ((x + 1) / 2) ((y + 1) / 2) ((z + 1) / 2) stamp seen in
  let m := mex_loop seen stamp L 0 (Zwf_well_founded 0 (gap L 0)) in
  (T.[k <- m], seen).

(* Every canonical cell 1 <= x <= y <= z < D, in increasing index order. *)
Definition table (D L : int) : array int * array int :=
  for_ (fun x st => for_ (fun y st => for_ (fun z st => cell D L x y z st) y D st) x D st)
    1 D (PArray.make L 0, PArray.make L 0).

Definition winner_impl (s : player) (xs ys zs : array uint) : player :=
  let n := PArray.length xs in
  let M := for_ (fun i m => imax m (imax xs.[i] (imax ys.[i] zs.[i]))) 0 n 0 in
  let D := M + 1 in
  let L := D * D * D in
  let T := fst (table D L) in
  let gx := for_ (fun i acc => acc lxor look T D xs.[i] ys.[i] zs.[i]) 0 n 0 in
  if gx =? 0 then opponent s else s.

Notation toN i := (Z.to_N (to_Z i)).
Notation ofN p := (of_Z (Z.of_N p)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition winner : player -> array uint -> array uint -> array uint -> player :=
  winner_impl.
