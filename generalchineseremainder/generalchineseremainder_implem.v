(* Executable implementation and its required termination dependencies.
   Correctness proofs are in generalchineseremainder_proofs.v. *)
(* Implementation of generalchineseremainder (generalchineseremainder.spec):
   the general Chinese remainder theorem for two moduli, CRT via the
   extended Euclidean algorithm.

   Code.  [egcd_loop] runs Euclid on (n, m) and tracks, for every remainder
   r of the sequence, a coefficient s in [0, m) with  s * n = r (mod m)
   (the Bezout coefficient of n, kept reduced modulo m so that it stays an
   unsigned word: s' = (s0 + m - (q * s1 mod m)) mod m).  It returns
   g = gcd(n, m) and s with s * n = g (mod m), hence
   s * (n/g) = 1 (mod m/g).  Then, with d = (b - a) mod m computed as
   (b + m - a mod m) mod m:
     - g does not divide d       -> None;
     - otherwise t = (d/g * s) mod (m/g), x = a + n * t, K = n * (m/g).
   Every intermediate value is below 10^18 < 2^63 under valid_input: no Z,
   no signed word.

   Termination: [egcd_loop] recurses structurally on an erased
   [Acc (Zwf 0) (φ r1)] proof, the shape of the loops of
   template/polymul1/implem-bens-1/polymul1_implem.v. *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
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

Lemma dec_mod : forall r0 r1 : int,
  (r1 =? 0) = false -> Zwf 0 (φ (r0 mod r1)) (φ r1).
Proof.
  intros r0 r1 H.
  assert (H1 : (φ r1) <> 0%Z).
  { intros E. assert (r1 = 0) by (apply to_Z_inj; exact E). subst. discriminate. }
  unfold Zwf. rewrite mod_spec. pose proof (to_Z_bounded r0). pose proof (to_Z_bounded r1).
  pose proof (Z.mod_pos_bound (φ r0) (φ r1) ltac:(lia)). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Euclid on (r0, r1), with s0 * n = r0 and s1 * n = r1 (mod m). *)
Fixpoint egcd_loop (m r0 r1 s0 s1 : int)
    (H : Acc (Zwf 0) (φ r1)) {struct H} : int * int :=
  match bdec (r1 =? 0) with
  | left _ => (r0, s0)
  | right Hne =>
      egcd_loop m r1 (r0 mod r1) s1 ((s0 + m - (r0 / r1 * s1) mod m) mod m)
        (Acc_inv H (dec_mod r0 r1 Hne))
  end.

Definition crt_impl (a n b m : uint) : option (uint * uint) :=
  let '(g, s) := egcd_loop m n m (1 mod m) 0 (Zwf_well_founded 0 (φ m)) in
  let mg := m / g in
  let d := (b + m - a mod m) mod m in
  if d mod g =? 0 then
    let t := (d / g * s) mod mg in
    Some (a + n * t, n * mg)
  else None.

(* ------------------------------------------------------------------ *)
(* Prop side: arithmetic over Z                                        *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.

Definition crt : uint -> uint -> uint -> uint -> option (uint * uint) :=
  crt_impl.
