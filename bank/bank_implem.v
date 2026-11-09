(* Executable implementation and its required termination dependencies.
   Correctness proofs are in bank_proofs.v. *)
(* Implementation of bank (bank.spec).

   Code.  CLRS 16.5 / Problem 16-4: unit-time jobs with deadlines as a
   matroid greedy.
   - [p] := the permutation 0 .. n-1 of the persons (init_loop), sorted by
     cash, decreasing, with a top-down merge sort [msort] on the index
     array (scratch buffer [b], merge into the buffer, copy back).
   - L := min(t, n) minutes are enough: no schedule serves more than n
     persons, and the greedy places person i in the latest free minute
     <= min(t_i, L - 1).  The free minutes are a disjoint-set forest over
     the cells 0 .. L of one flat array [uf] (cell y + 1 is minute y, cell
     0 the sentinel "no free minute"); [find] follows parent pointers down
     to the root, the latest free cell <= its argument, and compresses the
     path; occupying cell r links it to r - 1.
   - the total cash collected is accumulated in a 63-bit int (at most
     10^4 * 10^5).

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) _] proof on a Z measure, as in template/polymul1.  Every
   array is threaded linearly.

   Proof.  Merge sort: segment lists [seg] and Permutation, sorted
   segments.  Union-find: [UFInv] ties the forest to a ghost owner map
   (cell -> person).  Optimality: at every prefix P of the sorted order,
   every valid schedule serves at most as many persons of P as the greedy
   accepted ([rank_state]: the classical rank bound m + #{i in P, d_i >= m}
   at m = the first free minute), then an Abel summation ([abel]) over the
   decreasing cash turns the prefix counts into the value bound. *)

From Bank.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Permutation Sorted Bool.
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

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_lt : forall p x : int, (p <? x) = true -> Zwf 0 (φ p) (φ x).
Proof.
  intros p x H. rewrite ltb_spec in H. pose proof (to_Z_bounded p).
  unfold Zwf. lia.
Qed.

Lemma dec_half : forall len : int, (1 <? len) = true -> Zwf 0 (φ (len / 2)) (φ len).
Proof.
  intros len H. rewrite ltb_spec in H. change (φ 1) with 1%Z in H.
  assert (E : (φ (len / 2)) = ((φ len) / 2)%Z) by (rewrite div_spec; reflexivity).
  unfold Zwf. rewrite E. lia.
Qed.

Lemma dec_rest : forall len : int, (1 <? len) = true ->
  Zwf 0 (φ (len - len / 2)) (φ len).
Proof.
  intros len H. rewrite ltb_spec in H. change (φ 1) with 1%Z in H.
  assert (E : (φ (len / 2)) = ((φ len) / 2)%Z) by (rewrite div_spec; reflexivity).
  assert (E2 : (φ (len - len / 2)) = ((φ len) - (φ len) / 2)%Z) by sia.
  unfold Zwf. rewrite E2. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* a.[k] := k for k = k0 .. m-1. *)
Fixpoint init_loop (m k : int) (a : array int)
    (H : Acc (Zwf 0) (gap m k)) {struct H} : array int :=
  match bdec (k <? m) with
  | left Hk => init_loop m (k + 1) a.[k <- k] (Acc_inv H (dec_step m k Hk))
  | right _ => a
  end.

(* Whether the merge takes the next element of the left run src.[i..mid)
   rather than that of the right run src.[j..hi): the larger cash first. *)
Definition take_left (cash src : array int) (mid hi i j : int) : bool :=
  if i <? mid then (if j <? hi then cash.[src.[j]] <=? cash.[src.[i]] else true)
  else false.

(* Merge src.[i..mid) and src.[j..hi) into dst.[k..hi). *)
Fixpoint merge_loop (cash src : array int) (mid hi i j k : int) (dst : array int)
    (H : Acc (Zwf 0) (gap hi k)) {struct H} : array int :=
  match bdec (k <? hi) with
  | left Hk =>
      if take_left cash src mid hi i j
      then merge_loop cash src mid hi (i + 1) j (k + 1) dst.[k <- src.[i]]
             (Acc_inv H (dec_step hi k Hk))
      else merge_loop cash src mid hi i (j + 1) (k + 1) dst.[k <- src.[j]]
             (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.

(* dst.[k..hi) := src.[k..hi). *)
Fixpoint copy_loop (src : array int) (hi k : int) (dst : array int)
    (H : Acc (Zwf 0) (gap hi k)) {struct H} : array int :=
  match bdec (k <? hi) with
  | left Hk => copy_loop src hi (k + 1) dst.[k <- src.[k]]
                 (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.

(* Sort a.[lo..lo+len) by cash, decreasing; b is the scratch buffer. *)
Fixpoint msort (cash a b : array int) (lo len : int)
    (H : Acc (Zwf 0) (φ len)) {struct H} : array int * array int :=
  match bdec (1 <? len) with
  | left Hl =>
      let len1 := len / 2 in
      let mid := lo + len1 in
      let hi := lo + len in
      let (a1, b1) := msort cash a b lo len1 (Acc_inv H (dec_half len Hl)) in
      let (a2, b2) := msort cash a1 b1 mid (len - len1)
                        (Acc_inv H (dec_rest len Hl)) in
      let b3 := merge_loop cash a2 mid hi lo mid lo b2
                  (Zwf_well_founded 0 (gap hi lo)) in
      let a3 := copy_loop b3 hi lo a2 (Zwf_well_founded 0 (gap hi lo)) in
      (a3, b3)
  | right _ => (a, b)
  end.

(* The root of x: the latest free cell <= x; path compression. *)
Fixpoint find (a : array int) (x : int)
    (H : Acc (Zwf 0) (φ x)) {struct H} : array int * int :=
  let p := a.[x] in
  match bdec (p <? x) with
  | left Hp =>
      let (a1, r) := find a p (Acc_inv H (dec_lt p x Hp)) in
      (a1.[x <- r], r)
  | right _ => (a, x)
  end.

(* Persons perm.[j], perm.[j+1], ..., perm.[n-1], in decreasing cash. *)
Fixpoint greedy_loop (cash dl perm : array int) (n L j : int) (uf : array int)
    (tot : int) (H : Acc (Zwf 0) (gap n j)) {struct H} : int :=
  match bdec (j <? n) with
  | left Hj =>
      let i := perm.[j] in
      let d := dl.[i] in
      let c := if d <? L then d + 1 else L in
      let (uf1, r) := find uf c (Zwf_well_founded 0 (φ c)) in
      if r =? 0
      then greedy_loop cash dl perm n L (j + 1) uf1 tot
             (Acc_inv H (dec_step n j Hj))
      else greedy_loop cash dl perm n L (j + 1) uf1.[r <- r - 1] (tot + cash.[i])
             (Acc_inv H (dec_step n j Hj))
  | right _ => tot
  end.

Definition bank_impl (t : uint) (cash dl : array uint) : uint :=
  let n := PArray.length cash in
  let p0 := init_loop n 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)) in
  let p := fst (msort cash p0 (PArray.make n 0) 0 n (Zwf_well_founded 0 (φ n))) in
  let L := if t <? n then t else n in
  let uf := init_loop (L + 1) 0 (PArray.make (L + 1) 0)
              (Zwf_well_founded 0 (gap (L + 1) 0)) in
  greedy_loop cash dl p n L 0 uf 0 (Zwf_well_founded 0 (gap n 0)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition bank : uint -> array uint -> array uint -> uint := bank_impl.
