(* Executable implementation and its required termination dependencies.
   Correctness proofs are in knapsack2_proofs.v. *)
(* Implementation of knapsack2 (knapsack2.spec). *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* The termination device                                              *)
(* ------------------------------------------------------------------ *)

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

Lemma gcd_dec : forall u v : int,
  (v =? 0) = false -> Zwf 0 (φ (u mod v)) (φ v).
Proof.
  intros u v H. rewrite eqb_false_spec in H.
  assert ((φ v) <> 0%Z) by (intro E; apply H; apply to_Z_inj; exact E).
  unfold Zwf. rewrite mod_spec. pose proof (to_Z_bounded v).
  pose proof (Z.mod_pos_bound (φ u) (φ v) ltac:(lia)). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* "No filling found yet" for a residue class. *)
Definition inf : int := 9223372036854775807.

(* The smallest of g.[i], ..., g.[n-1] and best. *)
Fixpoint min_loop (g : array int) (n i best : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : int :=
  match bdec (i <? n) with
  | left Hi =>
      min_loop g n (i + 1) (if g.[i] <? best then g.[i] else best)
        (Acc_inv H (dec_step n i Hi))
  | right _ => best
  end.

(* Euclid's algorithm. *)
Fixpoint gcd_loop (u v : int) (H : Acc (Zwf 0) (φ v)) {struct H} : int :=
  match bdec (v =? 0) with
  | left _ => u
  | right Hv => gcd_loop v (u mod v) (Acc_inv H (gcd_dec u v Hv))
  end.

(* x + a modulo m, for x < m and a' = a mod m. *)
Definition nxt (m a' x : int) : int :=
  let y := x + a' in if y <? m then y else y - m.

(* The position of the smallest cell among x, x + a, ..., (L - j more
   steps) modulo m, p being the best one seen so far. *)
Fixpoint scan (A : array int) (m a' L j x p : int)
    (H : Acc (Zwf 0) (gap L j)) {struct H} : int :=
  match bdec (j <? L) with
  | left Hj =>
      scan A m a' L (j + 1) (nxt m a' x) (if A.[x] <? A.[p] then x else p)
        (Acc_inv H (dec_step L j Hj))
  | right _ => p
  end.

(* One walk around a cycle of +a modulo m, from x whose cell holds cur:
   each next cell becomes min(itself, previous + a). *)
Fixpoint relax (m a a' L1 j x cur : int) (A : array int)
    (H : Acc (Zwf 0) (gap L1 j)) {struct H} : array int :=
  match bdec (j <? L1) with
  | left Hj =>
      let y := nxt m a' x in
      let c := cur + a in
      let v := A.[y] in
      if c <? v then relax m a a' L1 (j + 1) y c A.[y <- c]
                       (Acc_inv H (dec_step L1 j Hj))
      else relax m a a' L1 (j + 1) y v A (Acc_inv H (dec_step L1 j Hj))
  | right _ => A
  end.

(* The cycles of +a modulo m are the classes modulo d = gcd(m, a), each
   of length L = m / d; class c is walked from its smallest cell. *)
Fixpoint classes (m a a' d L c : int) (A : array int)
    (H : Acc (Zwf 0) (gap d c)) {struct H} : array int :=
  match bdec (c <? d) with
  | left Hc =>
      let p := scan A m a' L 0 c c (Zwf_well_founded 0 (gap L 0)) in
      let v := A.[p] in
      classes m a a' d L (c + 1)
        (if v =? inf then A
         else relax m a a' (L - 1) 0 p v A (Zwf_well_founded 0 (gap (L - 1) 0)))
        (Acc_inv H (dec_step d c Hc))
  | right _ => A
  end.

(* Close the table under adding an item of size a. *)
Definition item (m a : int) (A : array int) : array int :=
  let a' := a mod m in
  let d := gcd_loop m a' (Zwf_well_founded 0 (φ a')) in
  classes m a a' d (m / d) 0 A (Zwf_well_founded 0 (gap d 0)).

Fixpoint items (g : array int) (n m i : int) (A : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi => items g n m (i + 1) (item m g.[i] A) (Acc_inv H (dec_step n i Hi))
  | right _ => A
  end.

(* Cell r of the table: the smallest fillable size congruent to r modulo
   the smallest item size m (inf when none). *)
Definition fillable_core (k : int) (g : array int) : bool :=
  let n := PArray.length g in
  let m := min_loop g n 1 g.[0] (Zwf_well_founded 0 (gap n 1)) in
  let A := items g n m 0 (PArray.make m inf).[0 <- 0]
             (Zwf_well_founded 0 (gap n 0)) in
  A.[k mod m] <=? k.

Definition fillable_impl (k : uint) (g : array uint) : bool := fillable_core k g.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition fillable : uint -> array uint -> bool := fillable_impl.
