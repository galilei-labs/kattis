(* Executable implementation and its required termination dependencies.
   Correctness proofs are in suffixsorting_proofs.v. *)
From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Permutation Sorted String Ascii.
From Stdlib Require PrimString Sint63.
Import ListNotations.

Unset Lia Cache.
Open Scope nat_scope.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.
(* ================================================================== *)
(* Uint63 / PArray plumbing                                            *)
(* ================================================================== *)

Open Scope uint63_scope.
Open Scope array_scope.

(* ================================================================== *)
(* The termination device                                              *)
(* ================================================================== *)

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

Lemma dec_dbl : forall n k : int, (andb (k <? k + k) (k + k <? n)) = true ->
  Zwf 0 (gap n (k + k)) (gap n k).
Proof.
  intros n k H. apply andb_prop in H as [H1 H2].
  rewrite ltb_spec in H1, H2. unfold Zwf, gap. lia.
Qed.

(* ================================================================== *)
(* The program                                                         *)
(* ================================================================== *)

(* r.[i] = code of character i, plus one (rank 0 is the sentinel) *)
Fixpoint init_rank (x : PrimString.string) (n i : int) (r : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi =>
      init_rank x n (i + 1) r.[i <- PrimString.get x i + 1]
        (Acc_inv H (dec_step n i Hi))
  | right _ => r
  end.

(* sa.[i] = i *)
Fixpoint init_id (n i : int) (sa : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi => init_id n (i + 1) sa.[i <- i] (Acc_inv H (dec_step n i Hi))
  | right _ => sa
  end.

(* the key of position x for gap k: the rank of x + k, 0 past the end;
   k = 0 gives the rank of x itself *)
Definition skey (r : array int) (n k x : int) : int :=
  if x + k <? n then r.[x + k] else 0.

(* the count table has one cell per possible rank: 0 .. max(n, 256) *)
Definition cbound (n : int) : int := if n <? 256 then 257 else n + 1.

(* counting pass: cnt.[v] = number of i < n with key src.[i] = v *)
Fixpoint count_loop (r : array int) (n k : int) (src : array int) (i : int)
    (cnt : array int) (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi =>
      let x := src.[i] in
      let v := if x + k <? n then r.[x + k] else 0 in
      count_loop r n k src (i + 1) cnt.[v <- cnt.[v] + 1] (Acc_inv H (dec_step n i Hi))
  | right _ => cnt
  end.

(* exclusive prefix sums: cnt.[v] = number of keys below v *)
Fixpoint prefix_loop (B v acc : int) (cnt : array int)
    (H : Acc (Zwf 0) (gap B v)) {struct H} : array int :=
  match bdec (v <? B) with
  | left Hv =>
      let c := cnt.[v] in
      prefix_loop B (v + 1) (acc + c) cnt.[v <- acc] (Acc_inv H (dec_step B v Hv))
  | right _ => cnt
  end.

(* placement, in the order of src (stable) *)
Fixpoint place_loop (r : array int) (n k : int) (src : array int) (i : int)
    (cnt dst : array int) (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi =>
      let x := src.[i] in
      let v := if x + k <? n then r.[x + k] else 0 in
      let p := cnt.[v] in
      place_loop r n k src (i + 1) cnt.[v <- p + 1] dst.[p <- x] (Acc_inv H (dec_step n i Hi))
  | right _ => dst
  end.

(* stable counting sort of src[0, n) into dst on the key skey r n k *)
Definition csort (r : array int) (n k : int) (src dst : array int) : array int :=
  let B := cbound n in
  let c0 := count_loop r n k src 0 (PArray.make B 0) (Zwf_well_founded 0 (gap n 0)) in
  let c1 := prefix_loop B 0 0 c0 (Zwf_well_founded 0 (gap B 0)) in
  place_loop r n k src 0 c1 dst (Zwf_well_founded 0 (gap n 0)).

(* the new ranks, in sorted order: equal pairs share a rank *)
Fixpoint rank_loop (r : array int) (n k : int) (sa : array int) (t cur : int)
    (nr : array int) (H : Acc (Zwf 0) (gap n t)) {struct H} : array int * int :=
  match bdec (t <? n) with
  | left Ht =>
      let a := sa.[t - 1] in
      let b := sa.[t] in
      let c := if (if r.[a] =? r.[b] then skey r n k a =? skey r n k b else false)
               then cur else cur + 1 in
      rank_loop r n k sa (t + 1) c nr.[b <- c] (Acc_inv H (dec_step n t Ht))
  | right _ => (nr, cur)
  end.

(* one doubling round per call: ranks of length k -> ranks of length 2k;
   the positions are sorted on the second key, then (stably) on the first *)
Fixpoint rounds (n k : int) (r nr sa tmp : array int)
    (H : Acc (Zwf 0) (gap n k)) {struct H} : array int :=
  let tmp1 := csort r n k sa tmp in
  let sa1 := csort r n 0 tmp1 sa in
  let q := rank_loop r n k sa1 1 1 nr.[sa1.[0] <- 1] (Zwf_well_founded 0 (gap n 1)) in
  if snd q =? n then sa1
  else
    match bdec (andb (k <? k + k) (k + k <? n)) with
    | left Hc => rounds n (k + k) (fst q) r sa1 tmp1 (Acc_inv H (dec_dbl n k Hc))
    | right _ => sa1
    end.

Definition suffix_array_impl (x : PrimString.string) : array uint :=
  let n := PrimString.length x in
  let r := init_rank x n 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)) in
  let sa := init_id n 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)) in
  rounds n 1 r (PArray.make n 0) sa (PArray.make n 0) (Zwf_well_founded 0 (gap n 1)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition suffix_array : PrimString.string -> array uint := suffix_array_impl.
