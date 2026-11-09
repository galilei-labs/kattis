(* Executable implementation and its required termination dependencies.
   Correctness proofs are in satisfiability_proofs.v. *)
(* Implementation of satisfiability (satisfiability.spec): exhaustive
   search over the 2^n assignments, each one a Uint63 bit mask.

   Code.  Each clause is first converted, once, into two bit masks: [pos]
   has bit i-1 set for every literal Xi of the clause, [neg] for every
   literal ~Xi.  They are stored in two flat arrays indexed by the clause
   number.  The search then runs t = 0 .. 2^n - 1 (variable Xi is bit i-1
   of t) and checks the clauses in order: clause k holds under t iff
   [pos.[k] land t <> 0] (a positive literal is true) or
   [neg.[k] land t <> neg.[k]] (a negative literal is false in t).  The
   first false clause ends the check of t, the first satisfying t ends the
   search.  No Z, no lists, no nat in the code.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) (gap m i)] proof, as in template/polymul1.

   Proof.  The masks are characterised bit by bit (Z.testbit of their
   value: [mask_of]); a clause test under t is then [clause_true] under
   the assignment [vz t] (Xi := bit i-1 of t).  The search returns true
   iff some t < 2^n satisfies every clause; conversely every assignment v
   agrees on X1..Xn with the mask whose bit i-1 is v i ([mask_exists]),
   which is below 2^n, and the literals only mention X1..Xn. *)

From Satisfiability.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Bool.
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

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* The bit of variable Xv. *)
Definition bitof (v : int) : int := 1 << (v - 1).

(* The bit a literal contributes to the positive (s = true) or the
   negative (s = false) mask of its clause. *)
Definition lit_bits (s : bool) (l : literal uint) : int :=
  match l with
  | X v => if s then bitof v else 0
  | NotX v => if s then 0 else bitof v
  end.

(* acc lor the bits of the literals c.[i .. len-1]. *)
Fixpoint mask_loop (s : bool) (c : array (literal uint)) (len i acc : int)
    (H : Acc (Zwf 0) (gap len i)) {struct H} : int :=
  match bdec (i <? len) with
  | left Hi =>
      mask_loop s c len (i + 1) (acc lor lit_bits s c.[i])
        (Acc_inv H (dec_step len i Hi))
  | right _ => acc
  end.

Definition clause_mask (s : bool) (c : array (literal uint)) : int :=
  mask_loop s c (PArray.length c) 0 0
    (Zwf_well_founded 0 (gap (PArray.length c) 0)).

(* Cells k .. m-1 of r receive the mask of clause k. *)
Fixpoint fill_loop (s : bool) (y : array (array (literal uint))) (m k : int)
    (r : array int) (H : Acc (Zwf 0) (gap m k)) {struct H} : array int :=
  match bdec (k <? m) with
  | left Hk =>
      fill_loop s y m (k + 1) r.[k <- clause_mask s y.[k]]
        (Acc_inv H (dec_step m k Hk))
  | right _ => r
  end.

Definition masks (s : bool) (y : array (array (literal uint))) : array int :=
  fill_loop s y (PArray.length y) 0 (PArray.make (PArray.length y) 0)
    (Zwf_well_founded 0 (gap (PArray.length y) 0)).

(* The clause of masks p (positive) and q (negative) holds under t. *)
Definition clause_ok (t p q : int) : bool :=
  if (p land t) =? 0 then negb ((q land t) =? q) else true.

(* Clauses k .. m-1 all hold under t. *)
Fixpoint check_loop (pos neg : array int) (m k t : int)
    (H : Acc (Zwf 0) (gap m k)) {struct H} : bool :=
  match bdec (k <? m) with
  | left Hk =>
      if clause_ok t pos.[k] neg.[k]
      then check_loop pos neg m (k + 1) t (Acc_inv H (dec_step m k Hk))
      else false
  | right _ => true
  end.

Definition check_all (pos neg : array int) (m t : int) : bool :=
  check_loop pos neg m 0 t (Zwf_well_founded 0 (gap m 0)).

(* Some t in [t0, lim) satisfies every clause. *)
Fixpoint search_loop (pos neg : array int) (m lim t : int)
    (H : Acc (Zwf 0) (gap lim t)) {struct H} : bool :=
  match bdec (t <? lim) with
  | left Ht =>
      if check_all pos neg m t then true
      else search_loop pos neg m lim (t + 1) (Acc_inv H (dec_step lim t Ht))
  | right _ => false
  end.

Definition satisfiable_impl (n : int) (y : array (array (literal uint))) : bool :=
  let m := PArray.length y in
  let lim := 1 << n in
  search_loop (masks true y) (masks false y) m lim 0
    (Zwf_well_founded 0 (gap lim 0)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition satisfiable : uint -> array (array (literal uint)) -> bool :=
  satisfiable_impl.
