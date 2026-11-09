(* Executable implementation and its required termination dependencies.
   Correctness proofs are in primepower_proofs.v. *)
From Primepower.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Znumtheory.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* The termination devices                                             *)
(* ------------------------------------------------------------------ *)

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

(* Distance to the top of the word: decreases on every strict increase. *)
Definition up (j : int) : Z := (wB - (φ j))%Z.

Lemma dec_up : forall a b : int, (a <? b) = true -> Zwf 0 (up b) (up a).
Proof.
  intros a b H. rewrite ltb_spec in H.
  pose proof (to_Z_bounded b). unfold Zwf, up. lia.
Qed.

Lemma dec_down : forall a p : int, (a <? p) = true -> Zwf 0 (φ (p - 1)) (φ p).
Proof. intros a p H. rewrite ltb_spec in H. unfold Zwf. sia. Qed.

Lemma dec_half : forall e : int, (0 <? e) = true -> Zwf 0 (φ (e >> 1)) (φ e).
Proof. intros e H. rewrite ltb_spec in H. unfold Zwf. sia. Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Definition M : int := 1000000007.

(* acc * b^e mod M, by repeated squaring. *)
Fixpoint pow_loop (b e acc : int) (H : Acc (Zwf 0) (φ e)) {struct H} : int :=
  match bdec (0 <? e) with
  | left He =>
      pow_loop ((b * b) mod M) (e >> 1)
        (if is_even e then acc else (acc * b) mod M)
        (Acc_inv H (dec_half e He))
  | right _ => acc
  end.

Definition powmod (b e : int) : int :=
  pow_loop (b mod M) e 1 (Zwf_well_founded 0 (φ e)).

(* Cross out j, j + i, j + 2i, ... up to R. *)
Fixpoint cross_loop (i R j : int) (s : array int)
    (H : Acc (Zwf 0) (up j)) {struct H} : array int :=
  match bdec (j <=? R) with
  | left _ =>
      let j' := j + i in
      match bdec (j <? j') with
      | left Hj => cross_loop i R j' s.[j <- 0] (Acc_inv H (dec_up j j' Hj))
      | right _ => s.[j <- 0]
      end
  | right _ => s
  end.

(* The sieve of Eratosthenes, for i = 2, 3, ... while i * i <= R. *)
Fixpoint sieve_loop (R i : int) (s : array int)
    (H : Acc (Zwf 0) (up i)) {struct H} : array int :=
  match bdec (i * i <=? R) with
  | left _ =>
      let s' := if s.[i] =? 0 then s
                else cross_loop i R (i * i) s
                       (Zwf_well_founded 0 (up (i * i))) in
      match bdec (i <? i + 1) with
      | left Hi => sieve_loop R (i + 1) s' (Acc_inv H (dec_up i (i + 1) Hi))
      | right _ => s'
      end
  | right _ => s
  end.

(* s.[p] <> 0 iff p is prime, for p <= R. *)
Definition sieve (R : int) : array int :=
  sieve_loop R 2 (PArray.make (R + 1) 1).[0 <- 0].[1 <- 0]
    (Zwf_well_founded 0 (up 2)).

(* p = R, R - 1, ..., L: acc becomes the product of p^E over the primes
   p seen, modulo M. *)
Fixpoint prod_loop (s : array int) (E L p acc : int)
    (H : Acc (Zwf 0) (φ p)) {struct H} : int :=
  let acc' := if s.[p] =? 0 then acc else (powmod p E * acc) mod M in
  match bdec (L <? p) with
  | left Hp => prod_loop s E L (p - 1) acc' (Acc_inv H (dec_down L p Hp))
  | right _ => acc'
  end.

Definition primepower_impl (E L R : uint) : uint :=
  if R <? L then 1
  else prod_loop (sieve R) E L R 1 (Zwf_well_founded 0 (φ R)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition primepower : uint -> uint -> uint -> uint := primepower_impl.
