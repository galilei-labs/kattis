(* Executable implementation and its required termination dependencies.
   Correctness proofs are in remainderreminder_proofs.v. *)
(* Implementation of remainderreminder (remainderreminder.spec).

   Code.  Phase 1 ([scan]): one pass over the corner cuts x = 1 .. with
   2x < a (that is x < (a+1)/2; a <= b), keeping the three largest distinct
   volumes x (a-2x) (b-2x) seen so far in a triple, 0 standing for "none
   yet" (every volume is at least 1).  No table, no sort.
   Phase 2 ([merge], twice): general Chinese remaindering.  [egcd] is the
   iterative extended Euclidean algorithm on (m1, m2): it returns
   g = gcd(m1, m2) and a Bezout coefficient s with s m1 = g (mod m2); the
   coefficient is kept reduced modulo m2 (in [0, m2)), so that no value is
   ever negative and every product stays below 2^60.  The pair
   n = r1 (m1), n = r2 (m2) is rejected when g does not divide r2 - r1,
   otherwise merged into n = r1 + m1 k (mod m1 (m2/g)), with
   k = ((r2 - r1)/g) s mod (m2/g).  The answer is then the least n >= f in
   the final class ([lift]), a constant number of divisions.
   Everything is Uint63 [int]; no Z, no N, no list, no array.

   Termination: [scan] on an erased [Acc (Zwf 0) (gap m x)], [egcd] on an
   erased [Acc (Zwf 0) (φ r1)] (the remainder decreases); no nat, no fuel. *)

From Remainderreminder.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith Uint63 ZifyUint63 Lia Zwf.

Open Scope uint63_scope.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* The termination devices                                             *)
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

Lemma mod_dec : forall r0 r1 : int,
  (r1 =? 0) = false -> Zwf 0 (φ (r0 mod r1)) (φ r1).
Proof.
  intros r0 r1 H. rewrite eqb_false_spec in H.
  assert (H1 : (φ r1) <> 0%Z) by (intro E; apply H; apply to_Z_inj; exact E).
  pose proof (to_Z_bounded r0). pose proof (to_Z_bounded r1).
  unfold Zwf. rewrite mod_spec.
  pose proof (Z.mod_pos_bound (φ r0) (φ r1) ltac:(lia)). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* The volume of the box folded with x-by-x corner cuts. *)
Definition vol (a b x : int) : int := x * (a - 2 * x) * (b - 2 * x).

(* Insert volume v into the triple t1 > t2 > t3 of the largest distinct
   volumes (0 = absent). *)
Definition upd (t : int * int * int) (v : int) : int * int * int :=
  let '(t1, t2, t3) := t in
  if t1 <? v then (v, t1, t2)
  else if v =? t1 then t
  else if t2 <? v then (t1, v, t2)
  else if v =? t2 then t
  else if t3 <? v then (t1, t2, v)
  else t.

(* Cuts x, x+1, ..., m-1. *)
Fixpoint scan (a b m x : int) (t : int * int * int)
    (H : Acc (Zwf 0) (gap m x)) {struct H} : int * int * int :=
  match bdec (x <? m) with
  | left Hx => scan a b m (x + 1) (upd t (vol a b x)) (Acc_inv H (dec_step m x Hx))
  | right _ => t
  end.

(* Extended Euclid on (r0, r1), the coefficients si with
   ri = si * m1 (mod m), kept in [0, m). *)
Fixpoint egcd (m r0 s0 r1 s1 : int) (H : Acc (Zwf 0) (φ r1)) {struct H}
    : int * int :=
  match bdec (r1 =? 0) with
  | left _ => (r0, s0)
  | right Hn =>
      egcd m r1 s1 (r0 mod r1) ((s0 + m - (r0 / r1) mod m * s1 mod m) mod m)
        (Acc_inv H (mod_dec r0 r1 Hn))
  end.

(* n = r1 (mod m1) and n = r2 (mod m2)  into  n = r (mod l);
   (0, 0) when the pair is incompatible. *)
Definition merge (r1 m1 r2 m2 : int) : int * int :=
  let '(g, s) := egcd m2 m1 (1 mod m2) m2 0 (Zwf_well_founded 0 (φ m2)) in
  let dd := (r2 + m2 - r1 mod m2) mod m2 in
  if dd mod g =? 0 then
    let m2' := m2 / g in
    (r1 + m1 * ((dd / g * s) mod m2'), m1 * m2')
  else (0, 0).

(* The least n >= f with n = r (mod l). *)
Definition lift (f r l : int) : int := f + (r + l - f mod l) mod l.

Definition rr_impl (a b c d e f g : uint) : uint :=
  let m := (a + 1) / 2 in
  let '(v1, v2, v3) := scan a b m 1 (0, 0, 0) (Zwf_well_founded 0 (gap m 1)) in
  let '(r12, l12) := merge c v1 d v2 in
  let '(r, l) := merge r12 l12 e v3 in
  lift f r l.

(* ------------------------------------------------------------------ *)
(* Uint63 arithmetic                                                   *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition remainderreminder :
  uint -> uint -> uint -> uint -> uint -> uint -> uint -> uint := rr_impl.
