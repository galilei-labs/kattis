(* Executable implementation and its required termination dependencies.
   Correctness proofs are in ultraquicksort_proofs.v. *)
(* Implementation of ultraquicksort (ultraquicksort.spec): the number of
   inversions of an array of distinct values, counted by a top-down merge
   sort.

   Code.  [inversions a] makes the two working arrays of the run: w, the
   one copy of the input ([PArray.copy a]), and s, a scratch array
   ([PArray.make n 0]); the caller's array is only read by that copy.
   [msort b lo hi w s c] sorts the segment [lo, hi) of w and leaves the
   sorted segment in w when b = true, in s when b = false (ping-pong: the
   two halves are sorted into the other array, then merged back, so no
   copy-back pass).  [merge src dst mid hi i j k c] merges the sorted runs
   src[i, mid) and src[j, hi) into dst from position k; when the head of the
   right run is strictly smaller it is taken and the mid - i elements left
   in the left run are added to the counter (ties go left).  The counter is
   a 63-bit int; the arrays are threaded linearly (every [set] on the latest
   version).

   Termination: both functions recurse structurally on an erased
   [Acc (Zwf 0) _] proof: the wrapped difference [φ (hi - lo)] for msort,
   [max 0 (mid - i) + max 0 (hi - j)] for merge.

   Proof.  On the math side, [seg t i n] reads n cells of t from i as a list
   of N; [mergec] is the list merge with its count, proven to return a
   sorted permutation of its arguments and, on sorted arguments, the number
   of cross inversions [cross l r].  [merge] simulates [mergec] step by
   step (merge_spec); [msort] returns a sorted permutation of its segment
   and adds its [inv_list] (msort_spec), by
   [inv_list (l1 ++ l2) = inv_list l1 + inv_list l2 + cross l1 l2] and the
   invariance of [cross] under permutation of either argument.  The count
   is exact because it is below n^2 < 2^63. *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Sorted Permutation.
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

(* the merge measure: what is left of the two runs *)
Definition mm (mid hi i j : int) : Z :=
  (Z.max 0 ((φ mid) - (φ i)) + Z.max 0 ((φ hi) - (φ j)))%Z.

Lemma mm_dec_i : forall mid hi i j,
  (i <? mid) = true -> Zwf 0 (mm mid hi (i + 1) j) (mm mid hi i j).
Proof.
  intros mid hi i j H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, mm. lia.
Qed.

Lemma mm_dec_j : forall mid hi i j,
  (j <? hi) = true -> Zwf 0 (mm mid hi i (j + 1)) (mm mid hi i j).
Proof.
  intros mid hi i j H. rewrite ltb_spec in H.
  assert (H1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
  unfold Zwf, mm. lia.
Qed.

Lemma dec_left : forall lo hi,
  (1 <? hi - lo) = true -> Zwf 0 (φ (lo + (hi - lo) / 2 - lo)) (φ (hi - lo)).
Proof.
  intros lo hi H. rewrite ltb_spec in H. change (φ 1) with 1%Z in H.
  assert (E : (φ (lo + (hi - lo) / 2 - lo)) = ((φ (hi - lo)) / 2)%Z) by sia.
  rewrite E. unfold Zwf. split; [lia | apply Z.div_lt; lia].
Qed.

Lemma dec_right : forall lo hi,
  (1 <? hi - lo) = true -> Zwf 0 (φ (hi - (lo + (hi - lo) / 2))) (φ (hi - lo)).
Proof.
  intros lo hi H. rewrite ltb_spec in H. change (φ 1) with 1%Z in H.
  assert (E : (φ (hi - (lo + (hi - lo) / 2))) = ((φ (hi - lo)) - (φ (hi - lo)) / 2)%Z)
    by sia.
  rewrite E. unfold Zwf.
  assert (1 <= (φ (hi - lo)) / 2)%Z by (apply Z.div_le_lower_bound; lia).
  assert ((φ (hi - lo)) / 2 <= (φ (hi - lo)))%Z by (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Merges src[i, mid) and src[j, hi) into dst from k; c counts the pairs
   (left element, right element) with the right one strictly smaller. *)
Fixpoint merge (src dst : array int) (mid hi i j k c : int)
    (H : Acc (Zwf 0) (mm mid hi i j)) {struct H} : array int * int :=
  match bdec (i <? mid) with
  | left Hi =>
      match bdec (j <? hi) with
      | left Hj =>
          let x := src.[i] in
          let y := src.[j] in
          if y <? x then
            merge src dst.[k <- y] mid hi i (j + 1) (k + 1) (c + (mid - i))
              (Acc_inv H (mm_dec_j mid hi i j Hj))
          else
            merge src dst.[k <- x] mid hi (i + 1) j (k + 1) c
              (Acc_inv H (mm_dec_i mid hi i j Hi))
      | right _ =>
          merge src dst.[k <- src.[i]] mid hi (i + 1) j (k + 1) c
            (Acc_inv H (mm_dec_i mid hi i j Hi))
      end
  | right _ =>
      match bdec (j <? hi) with
      | left Hj =>
          merge src dst.[k <- src.[j]] mid hi i (j + 1) (k + 1) c
            (Acc_inv H (mm_dec_j mid hi i j Hj))
      | right _ => (dst, c)
      end
  end.

(* Sorts the segment [lo, hi) of w (lo < hi), the result landing in w when
   b = true and in s when b = false; adds its inversions to c. *)
Fixpoint msort (b : bool) (lo hi : int) (w s : array int) (c : int)
    (H : Acc (Zwf 0) (φ (hi - lo))) {struct H} : array int * array int * int :=
  match bdec (1 <? hi - lo) with
  | left Hd =>
      let mid := lo + (hi - lo) / 2 in
      match msort (negb b) lo mid w s c (Acc_inv H (dec_left lo hi Hd)) with
      | (w1, s1, c1) =>
          match msort (negb b) mid hi w1 s1 c1 (Acc_inv H (dec_right lo hi Hd)) with
          | (w2, s2, c2) =>
              if b then
                match merge s2 w2 mid hi lo mid lo c2
                        (Zwf_well_founded 0 (mm mid hi lo mid)) with
                | (w3, c3) => (w3, s2, c3)
                end
              else
                match merge w2 s2 mid hi lo mid lo c2
                        (Zwf_well_founded 0 (mm mid hi lo mid)) with
                | (s3, c3) => (w2, s3, c3)
                end
          end
      end
  | right _ => if b then (w, s, c) else (w, s.[lo <- w.[lo]], c)
  end.

Definition inversions_impl (a : array uint) : uint :=
  let n := PArray.length a in
  snd (msort true 0 n (PArray.copy a) (PArray.make n 0) 0
         (Zwf_well_founded 0 (φ (n - 0)))).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition inversions : array uint -> uint := inversions_impl.
