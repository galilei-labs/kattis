(* Executable implementation and its required termination dependencies.
   Correctness proofs are in relatives_proofs.v. *)
(* Implementation of relatives (relatives.spec): Euler's phi function by
   trial division, as the steering asks.

   Code.  [relatives n] returns 0 for n <= 1 and otherwise runs the loop
   [outer p m res] from p = 2, m = n, res = n: while p * p <= m (and p < m,
   which the first test implies on every input but keeps the termination
   measure m - p honest), if p divides m then res := res / p * (p - 1) and
   every factor p is divided out of m ([divout]); then p := p + 1.  When the
   loop stops, a remaining m > 1 is a prime and res := res / m * (m - 1).
   Pure Uint63 arithmetic, no array, no Z; every value stays below n.

   Termination: both loops recurse structurally on an erased
   [Acc (Zwf 0) _] proof (measure m for [divout], m - p for [outer]), as in
   template/polymul1.

   Proof.  The math side counts with [cnt P a l], the number of
   k in [a, a + l) with P k.  With [cop r k := gcd k r =? 1], the loop
   invariant is res = #{k in [0, n) | gcd k r = 1}, for r the product of
   the primes found so far, and gcd k n = 1 <-> gcd k r = 1 /\ gcd k m = 1.
   The step for a new prime p (Lemma step_count) uses that the predicate
   is periodic with period n / p (a multiple of r), so the count over
   [0, n) is p times the count over [0, n / p), and that the k < n that
   are multiples of p and coprime to r are the p * j with j < n / p coprime
   to r.  The final count over [0, n) is the spec's count over [1, n) for
   n >= 2, and gcd k n = 1 is the statement's "relatively prime". *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 ZifyUint63 Lia Zwf Znumtheory Bool.
Import ListNotations.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Section Program.
Local Open Scope uint63_scope.

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

Lemma divout_dec : forall p m : int,
  ((m mod p =? 0) && ((0 <? m) && (1 <? p))) = true ->
  Zwf 0 (φ (m / p)) (φ m).
Proof.
  intros p m H. apply andb_prop in H as [_ H]. apply andb_prop in H as [H1 H2].
  rewrite ltb_spec in H1, H2. change (φ 0) with 0%Z in H1.
  change (φ 1) with 1%Z in H2.
  unfold Zwf. rewrite div_spec.
  pose proof (Z.div_pos (φ m) (φ p) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt (φ m) (φ p) ltac:(lia) ltac:(lia)).
  lia.
Qed.

(* m with every factor p divided out (p >= 2, m >= 1) *)
Fixpoint divout (p m : int) (H : Acc (Zwf 0) (φ m)) {struct H} : int :=
  match bdec ((m mod p =? 0) && ((0 <? m) && (1 <? p))) with
  | left Hc => divout p (m / p) (Acc_inv H (divout_dec p m Hc))
  | right _ => m
  end.

Lemma divout_eq : forall p m H,
  divout p m H =
  match bdec ((m mod p =? 0) && ((0 <? m) && (1 <? p))) with
  | left Hc => divout p (m / p) (Acc_inv H (divout_dec p m Hc))
  | right _ => m
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma divout_le_aux : forall z p m H, (φ m) = z -> ((φ (divout p m H)) <= (φ m))%Z.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros p m H Hz. rewrite divout_eq.
  destruct (bdec _) as [Hc | Hc].
  - pose proof (divout_dec p m Hc) as D.
    eapply Z.le_trans.
    + apply (IH (φ (m / p))); [rewrite <- Hz; exact D | reflexivity].
    + unfold Zwf in D. lia.
  - lia.
Qed.

Lemma divout_le : forall p m H, ((φ (divout p m H)) <= (φ m))%Z.
Proof. intros p m H. exact (divout_le_aux _ p m H eq_refl). Qed.

Lemma outer_dec : forall p m m' : int,
  ((p * p <=? m) && (p <? m)) = true -> ((φ m') <= (φ m))%Z ->
  Zwf 0 ((φ m') - (φ (p + 1))) ((φ m) - (φ p)).
Proof.
  intros p m m' Hc Hm. apply andb_prop in Hc as [_ Hc]. rewrite ltb_spec in Hc.
  pose proof (to_Z_bounded p). pose proof (to_Z_bounded m).
  assert ((φ (p + 1)) = (φ p) + 1)%Z by sia.
  unfold Zwf. lia.
Qed.

(* trial division from p on, m what remains of n, res the running count *)
Fixpoint outer (p m res : int) (H : Acc (Zwf 0) ((φ m) - (φ p))%Z) {struct H} : int :=
  match bdec ((p * p <=? m) && (p <? m)) with
  | left Hc =>
      if m mod p =? 0 then
        let m' := divout p m (Zwf_well_founded 0 (φ m)) in
        outer (p + 1) m' (res / p * (p - 1))
          (Acc_inv H (outer_dec p m m' Hc (divout_le p m _)))
      else
        outer (p + 1) m res (Acc_inv H (outer_dec p m m Hc (Z.le_refl _)))
  | right _ => if 1 <? m then res / m * (m - 1) else res
  end.

Lemma outer_eq : forall p m res H,
  outer p m res H =
  match bdec ((p * p <=? m) && (p <? m)) with
  | left Hc =>
      if m mod p =? 0 then
        let m' := divout p m (Zwf_well_founded 0 (φ m)) in
        outer (p + 1) m' (res / p * (p - 1))
          (Acc_inv H (outer_dec p m m' Hc (divout_le p m _)))
      else
        outer (p + 1) m res (Acc_inv H (outer_dec p m m Hc (Z.le_refl _)))
  | right _ => if 1 <? m then res / m * (m - 1) else res
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition relatives_impl (n : uint) : uint :=
  if n <=? 1 then 0
  else outer 2 n n (Zwf_well_founded 0 ((φ n) - (φ 2))%Z).

End Program.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition relatives : uint -> uint := relatives_impl.
