(* Executable implementation and its required termination dependencies.
   Correctness proofs are in candydistribution_proofs.v. *)
(* Implementation of candydistribution (candydistribution.spec): the
   modular linear equation  b * C = 1 (mod K)  solved by the extended
   Euclidean algorithm (CLRS 31.2 / 31.4).

   Code.  [egcd_loop] is the iterative extended Euclid on the pair
   (K, C mod K): the state (a, b, sa, sb) keeps  sa * C = a  and
   sb * C = b  modulo K, the Bezout coefficients being held as their
   residues in [0, K) (so every word stays unsigned and below K^2 <= 10^18:
   no overflow, no signed reading needed).  At the end a = gcd(K, C) and
   sa * C = gcd(K, C) (mod K).  If the gcd is not 1 there is no answer;
   otherwise sa is the inverse b0 of C modulo K, and the smallest fair
   number of bags is b0 (or K when b0 = 0, i.e. K = 1), plus K when that
   gives exactly one candy (b = C = 1, x would be 0).  It is returned when
   at most 10^9, otherwise "IMPOSSIBLE".  O(log K) steps, O(1) memory.

   Termination: the loop recurses on an erased [Acc (Zwf 0) (φ b)]
   proof (b decreases strictly, a mod b < b), the device of
   template/polymul1.  No nat, no Z in the code. *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 ZifyUint63 Lia Zwf.
Import ListNotations.

Open Scope uint63_scope.

Unset Lia Cache.

(* ------------------------------------------------------------------ *)
(* The termination device                                              *)
(* ------------------------------------------------------------------ *)

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

Lemma dec_mod : forall a b : int,
  (b =? 0) = false -> Zwf 0 (φ (a mod b)) (φ b).
Proof.
  intros a b H.
  assert (Hb : (φ b) <> 0%Z).
  { intros E. assert (b = 0) by (apply to_Z_inj; exact E). subst b. discriminate H. }
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  rewrite mod_spec. unfold Zwf.
  pose proof (Z.mod_pos_bound (φ a) (φ b) ltac:(lia)). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Extended Euclid modulo k: returns (gcd, coefficient of C mod k). *)
Fixpoint egcd_loop (k a b sa sb : int)
    (H : Acc (Zwf 0) (φ b)) {struct H} : int * int :=
  match bdec (b =? 0) with
  | left _ => (a, sa)
  | right Hb =>
      egcd_loop k b (a mod b) sb ((sa + (k - ((a / b) * sb) mod k)) mod k)
        (Acc_inv H (dec_mod a b Hb))
  end.

Definition candy_impl (k c : uint) : option uint :=
  let p := egcd_loop k k (c mod k) 0 (1 mod k)
             (Zwf_well_founded 0 (φ (c mod k))) in
  let g := fst p in
  let s := snd p in
  if g =? 1 then
    let b1 := if s =? 0 then k else s in
    let b2 := if andb (b1 =? 1) (c =? 1) then b1 + k else b1 in
    if b2 <=? 1000000000 then Some b2 else None
  else None.

(* ------------------------------------------------------------------ *)
(* Prop side: arithmetic in Z                                          *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.

Close Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition candydistribution : uint -> uint -> option uint := candy_impl.
