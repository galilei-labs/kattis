(* Executable implementation and its required termination dependencies.
   Correctness proofs are in magicsequence_proofs.v. *)
(* Implementation of magicsequence (magicsequence.spec). *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Sorting.Sorted Sorting.Permutation.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.
Open Scope nat_scope.

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
  (i <? m)%uint63 = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1))%uint63 = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Section Program.
Local Open Scope uint63_scope.

(* Number of buckets of a counting-sort pass: 16-bit digits. *)
Definition K : int := 65536.
Definition mask : int := 65535.

(* Cells i .. n-1 of arr receive S[i] .. S[n-1], t being S[i]; m is the
   running maximum of the terms written; lo and hi are the histograms of
   the low and high 16-bit digits of the terms written.  The digit
   expressions are written inline (no helper call in the loop body). *)
Fixpoint gen_loop (a b c n i t m : int) (arr lo hi : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H}
    : array int * int * array int * array int :=
  match bdec (i <? n) with
  | left Hi =>
      let dl := t land mask in
      let dh := (t >> 16) land mask in
      let kl := lo.[dl] in
      let kh := hi.[dh] in
      gen_loop a b c n (i + 1) ((t * b + a) mod c)
        (if m <? t then t else m) arr.[i <- t]
        lo.[dl <- kl + 1] hi.[dh <- kh + 1]
        (Acc_inv H (dec_step n i Hi))
  | right _ => (arr, m, lo, hi)
  end.

(* Exclusive prefix sums of cnt, in place. *)
Fixpoint prefix_loop (e acc : int) (cnt : array int)
    (H : Acc (Zwf 0) (gap K e)) {struct H} : array int :=
  match bdec (e <? K) with
  | left He =>
      let k := cnt.[e] in
      prefix_loop (e + 1) (acc + k) cnt.[e <- acc]
        (Acc_inv H (dec_step K e He))
  | right _ => cnt
  end.

(* Stable placement: src[i] goes to the next free slot of its bucket; the
   digit (e >> s) land mask is written inline. *)
Fixpoint place_loop (s n : int) (src : array int) (i : int) (cnt dst : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi =>
      let e := src.[i] in
      let d := (e >> s) land mask in
      let p := cnt.[d] in
      place_loop s n src (i + 1) cnt.[d <- p + 1] dst.[p <- e]
        (Acc_inv H (dec_step n i Hi))
  | right _ => dst
  end.

(* One stable counting-sort pass on the digit at bit s, src into dst, cnt
   being the histogram of that digit over src (taken during generation). *)
Definition pass (s n : int) (src cnt dst : array int) : array int :=
  let cnt := prefix_loop 0 0 cnt (Zwf_well_founded 0 (gap K 0)) in
  place_loop s n src 0 cnt dst (Zwf_well_founded 0 (gap n 0)).

(* The Horner hash of r[i] .. r[n-1], from v. *)
Fixpoint hash_loop (x y n i v : int) (r : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : int :=
  match bdec (i <? n) with
  | left Hi =>
      hash_loop x y n (i + 1) ((v * x + r.[i]) mod y) r
        (Acc_inv H (dec_step n i Hi))
  | right _ => v
  end.

Definition magic_impl (n a b c x y : int) : int :=
  match gen_loop a b c n 0 a 0 (PArray.make n 0) (PArray.make K 0) (PArray.make K 0)
          (Zwf_well_founded 0 (gap n 0)) with
  | (g, m, lo, hi) =>
      let r1 := pass 0 n g lo (PArray.make n 0) in
      let r := if m <? K then r1 else pass 16 n r1 hi g in
      hash_loop x y n 0 0 r (Zwf_well_founded 0 (gap n 0))
  end.

End Program.

(* ------------------------------------------------------------------ *)
(* The list model of a counting-sort pass                              *)
(* ------------------------------------------------------------------ *)

(* The number of buckets, as an opaque nat (no unary 65536 in proofs). *)
Definition KN : nat := N.to_nat 65536.
Global Opaque KN.

(* The 16-bit digit of e at bit s. *)
Definition keyN (s e : N) : N := ((e / 2 ^ s) mod 65536)%N.

(* Bucket d: the elements of L of digit d, in order. *)
Definition blk (s : N) (L : list N) (d : nat) : list N :=
  filter (fun e => N.eqb (keyN s e) (N.of_nat d)) L.
Arguments blk : simpl never.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition magic : uint -> uint -> uint -> uint -> uint -> uint -> uint :=
  magic_impl.
