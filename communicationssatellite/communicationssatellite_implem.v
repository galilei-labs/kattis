(* Executable implementation and its required termination dependencies.
   Correctness proofs are in communicationssatellite_proofs.v. *)
(* Implementation of communicationssatellite.spec : the minimum total beam
   length, as the weight of a minimum spanning tree.

   Code (Part 5).  Dense Prim, O(n^2) : the complete graph on the dishes,
   edge i j weighing  sqrt (dx^2 + dy^2) - (r_i + r_j)  in binary64 (the
   squared distance and r_i + r_j are exact in int, then converted).  One
   flat [array bool] (in tree), one flat [array float] (best known weight
   to the tree), threaded linearly; each round scans for the minimum key
   ([amin_step]), adds it to the float total, then updates the keys from
   the new dish ([upd_step]).  Every loop is the combinator [loop],
   terminating by an erased Acc on hi - i ; no nat, no Z, no list in the code.

   Proof.
   - Part 1 : Prim on an abstract symmetric weight W >= 0 ([run] : the
     sequence of greedy steps).  [prim_lower] : the cost of any run is at
     most the cost of any edge list connecting every vertex to the start
     (exchange argument on the first edge leaving the tree);
     [run_exists] : a run exists for any weight.
   - Parts 2-3 : plane geometry ([dist_tri], its equality case [tri_eq]);
     the exact weight w i j = |c_i c_j| - r_i - r_j ; the segment of the
     centre line between two dishes ([seg_pts]).  [occl] : the beam of a
     Prim step enters no dish ; [apart_core] : beams of two Prim steps share
     no point (a common point forces a collinear configuration in which a
     centre lies on a beam).
   - Part 4 : the exact run's tree, beams along the centre lines of its
     positive-weight edges ([design]), is compliant and costs the run's
     weight ; every compliant design yields a connecting edge list (touching
     pairs, and for each beam the dishes it meets sorted along it) of
     weight at most its length ([lower_bound]).  Hence [exact_min] : the
     exact Prim weight m is the minimum cost.
   - Part 6 : the program performs a Prim run on the float weights Wh
     (comparisons are exact on floats) ; |Wh - w| <= 4000 u per edge, so the
     Wh-optimum is within 2000 * 4000 u of m (prim_lower both ways), and the
     float sum of the n - 1 chosen keys has relative error <= 2000 u
     ([acc_err]) : the output is within 10^-6 of m, absolutely when m <= 1,
     relatively otherwise.  Nothing is computed exactly in reals at run
     time; the only exact values are the int squared distance and radius sum. *)

From Speck Require Import Prelude.
From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf.
From Stdlib Require Import FinFun.
From Stdlib Require Sint63.
From Stdlib Require Import Relation_Operators Operators_Properties Sorting.Sorted Sorting.Permutation Classical_Prop.
From StdGalilei Require Import repr.
From StdGalilei Require Import repr_float.
Import ListNotations.

(* ================================================================== *)
(* Part 1. Prim's algorithm on an abstract weighted complete graph     *)
(* ================================================================== *)

Open Scope R_scope.

Close Scope R_scope.

(* ================================================================== *)
(* Part 5. The program                                                 *)
(* ================================================================== *)

Open Scope uint63_scope.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

Definition gap (m j : int) : Z := (to_Z m - to_Z j)%Z.

Lemma dec_step : forall hi i : int, (i <? hi) = true -> Zwf 0 (gap hi (i + 1)) (gap hi i).
Proof.
  intros hi i H. rewrite Uint63.ltb_spec in H. pose proof (to_Z_bounded hi).
  assert (to_Z (i + 1) = (to_Z i + 1)%Z) by sia. unfold Zwf, gap. lia.
Qed.

Section Loop.
Context {St : Type}.

Fixpoint wloop (hi : int) (f : int -> St -> St)
    (i : int) (s : St) (H : Acc (Zwf 0) (gap hi i)) {struct H} : St :=
  match bdec (i <? hi) with
  | left Hi => wloop hi f (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
  | right _ => s
  end.

(* for i = lo, lo+1, ..., hi-1 : s := f i s *)
Definition loop (hi : int) (f : int -> St -> St) (i : int) (s : St) : St :=
  wloop hi f i s (Zwf_well_founded 0 (gap hi i)).

End Loop.

(* the squared distance of the centres of dishes i and j, exact in int *)
Definition dsq (x y : array sint) (i j : int) : int :=
  let dx := x.[i] - x.[j] in
  let dy := y.[i] - y.[j] in
  dx * dx + dy * dy.

(* the weight of the edge i j : the gap between the two dishes *)
Definition wt (x y : array sint) (r : array uint) (i j : int) : float :=
  (PrimFloat.sqrt (of_uint63 (dsq x y i j)) - of_uint63 (r.[i] + r.[j]))%float.

Definition init_step (x y : array sint) (r : array uint) (v : int) (key : array float) : array float :=
  key.[v <- wt x y r 0 v].

(* the argmin of key over the dishes not in the tree ; n is "none yet" *)
Definition amin_step (n : int) (inT : array bool) (key : array float) (v : int) (st : int * float)
    : int * float :=
  let '(b, bv) := st in
  if inT.[v] then st
  else if b =? n then (v, key.[v])
  else if (key.[v] <? bv)%float then (v, key.[v]) else st.

(* dish b joined the tree : update the keys of the others *)
Definition upd_step (x y : array sint) (r : array uint) (inT : array bool) (b : int)
    (v : int) (key : array float) : array float :=
  if inT.[v] then key
  else
    let wv := wt x y r b v in
    if (wv <? key.[v])%float then key.[v <- wv] else key.

Definition prim_step (x y : array sint) (r : array uint) (n : int) (k : int)
    (st : array bool * array float * float) : array bool * array float * float :=
  let '(inT, key, tot) := st in
  let '(b, _) := loop n (amin_step n inT key) 0 (n, PrimFloat.zero) in
  let tot := (tot + key.[b])%float in
  let inT := inT.[b <- true] in
  let key := loop n (upd_step x y r inT b) 0 key in
  (inT, key, tot).

Definition comsat (x y : array sint) (r : array uint) : float :=
  let n := PArray.length x in
  let inT := (PArray.make n false).[0 <- true] in
  let key := loop n (init_step x y r) 0 (PArray.make n PrimFloat.zero) in
  let '(_, _, tot) := loop n (prim_step x y r n) 1 (inT, key, PrimFloat.zero) in
  tot.

Close Scope uint63_scope.
Open Scope R_scope.

Definition communicationssatellite : array sint -> array sint -> array uint -> float := comsat.
