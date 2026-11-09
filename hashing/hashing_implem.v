(* Executable implementation and its required termination dependencies.
   Correctness proofs are in hashing_proofs.v. *)
(* Implementation of hashing (hashing.spec): keyed polynomial prefix
   hashing modulo the Mersenne prime p = 2^61 - 1.  See README.md. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Znumtheory Zpow_facts String Ascii.
From Stdlib Require PrimString.
Import ListNotations.

Open Scope Z_scope.

Unset Lia Cache.

(* ================================================================== *)
(* Part 2. The program                                                *)
(* ================================================================== *)

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

Section Code.
Local Open Scope uint63_scope.
Local Open Scope array_scope.

(* p = 2^61 - 1, also the mask of the low 61 bits. *)
Definition P61 : int := 2305843009213693951.

(* a * b mod p for a, b < p: the 122-bit product by mulc, then two
   Mersenne folds (2^61 = 1 mod p) and one conditional subtraction. *)
Definition mulmod (a b : int) : int :=
  let (h, l) := mulc a b in
  let s := (h << 2) + (l >> 61) + (l land P61) in
  let t := (s >> 61) + (s land P61) in
  if P61 <=? t then t - P61 else t.

Definition addmod (a b : int) : int :=
  let s := a + b in if P61 <=? s then s - P61 else s.

Definition submod (a b : int) : int :=
  if b <=? a then a - b else a + P61 - b.

(* The termination device. *)
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

(* Prefix hashes: t.[i+1] = t.[i] * r + s[i] mod p, t.[0] = 0. *)
Fixpoint pre_loop (r : int) (s : PrimString.string) (n i : int) (t : array int)
    (acc : int) (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi =>
      let acc' := addmod (mulmod acc r) (PrimString.get s i) in
      pre_loop r s n (i + 1) t.[i + 1 <- acc'] acc' (Acc_inv H (dec_step n i Hi))
  | right _ => t
  end.

(* Powers of the key: t.[i+1] = t.[i] * r mod p, t.[0] = 1. *)
Fixpoint pow_loop (r n i : int) (t : array int) (acc : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi =>
      let acc' := mulmod acc r in
      pow_loop r n (i + 1) t.[i + 1 <- acc'] acc' (Acc_inv H (dec_step n i Hi))
  | right _ => t
  end.

Definition prefix_hashes (r : int) (s : PrimString.string) (n : int) : array int :=
  pre_loop r s n 0 (PArray.make (n + 1) 0) 0 (Zwf_well_founded 0 (gap n 0)).

Definition powers (r n : int) : array int :=
  pow_loop r n 0 (PArray.make (n + 1) 1) 1 (Zwf_well_founded 0 (gap n 0)).

(* The hash of s[L..R): pre[R] - pre[L] * r^(R-L) + r^(R-L), mod p. *)
Definition hash (pre pw : array int) (L R : int) : int :=
  let k := pw.[R - L] in
  addmod (submod pre.[R] (mulmod pre.[L] k)) k.

Fixpoint q_loop (pre pw xl xr : array int) (q j : int) (out : array int)
    (H : Acc (Zwf 0) (gap q j)) {struct H} : array int :=
  match bdec (j <? q) with
  | left Hj =>
      q_loop pre pw xl xr q (j + 1) out.[j <- hash pre pw xl.[j] xr.[j]]
        (Acc_inv H (dec_step q j Hj))
  | right _ => out
  end.

Definition hashes_impl (r : uint) (s : PrimString.string) (xl xr : array uint)
    : array uint :=
  let n := PrimString.length s in
  let pre := prefix_hashes r s n in
  let pw := powers r n in
  let q := PArray.length xl in
  q_loop pre pw xl xr q 0 (PArray.make q 0) (Zwf_well_founded 0 (gap q 0)).

End Code.

Open Scope uint63_scope.
Open Scope array_scope.
Open Scope Z_scope.

(* ================================================================== *)
(* The spec's items, at top level                                     *)
(* ================================================================== *)

Definition hashes : uint -> PrimString.string -> array uint -> array uint ->
                    array uint := hashes_impl.
