(* Executable implementation and its required termination dependencies.
   Correctness proofs are in securitybadge_proofs.v. *)
(* Implementation of securitybadge (securitybadge.spec): DFS repeated over
   the elementary badge intervals.

   Code.  The boundaries 1, b+1, x_i, y_i+1 (2L+2 values) are sorted once by
   a bottom-up merge sort (two flat buffers in turn); on each interval
   [S[j-1], S[j]) with S[j-1] < S[j] the set of open locks is constant, so
   one search from s with badge S[j-1] decides the whole interval, whose
   length is added when d is reached.  The adjacency is CSR-style: lock i
   is keyed (a_i << 13) + i, the keys sorted by the same merge sort, and
   st[u] is the first position of room u's keys (one downward pass).  The
   search is an iterative DFS with an explicit stack in a flat array and a
   visited table stamped with the interval index (no clearing between
   searches).  Every array is threaded linearly; no nat, no Z, no list in
   the code.

   Termination: erased [Acc (Zwf 0) _] on a Z measure everywhere; the DFS
   measure is 2 * (unstamped cells) + stack height, the count of unstamped
   cells being a Prop-side function ([unm]).  See README.md. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf
  Relations.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.
Open Scope bool_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* PArray plumbing at array int                                        *)
(* ------------------------------------------------------------------ *)

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec in H. exact H.
Qed.

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
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_down : forall p : int,
  (0 <? p) = true -> Zwf 0 (φ (p - 1)) (φ p).
Proof. intros p H. rewrite ltb_spec in H. unfold Zwf. sia. Qed.

(* ------------------------------------------------------------------ *)
(* Bottom-up merge sort on a flat array, two buffers in turn            *)
(* ------------------------------------------------------------------ *)

Definition mgap (mid hi i j : int) : Z :=
  (Z.max 0 ((φ mid) - (φ i)) + Z.max 0 ((φ hi) - (φ j)))%Z.

Lemma mdec_i : forall mid hi i j : int,
  (i <? mid) = true -> Zwf 0 (mgap mid hi (i + 1) j) (mgap mid hi i j).
Proof. intros mid hi i j H. rewrite ltb_spec in H. unfold Zwf, mgap. sia. Qed.

Lemma mdec_j : forall mid hi i j : int,
  (j <? hi) = true -> Zwf 0 (mgap mid hi i (j + 1)) (mgap mid hi i j).
Proof. intros mid hi i j H. rewrite ltb_spec in H. unfold Zwf, mgap. sia. Qed.

(* src[i..mid) and src[j..hi) merged into dst[k..). *)
Fixpoint merge (src : array int) (mid hi i j k : int) (dst : array int)
    (H : Acc (Zwf 0) (mgap mid hi i j)) {struct H} : array int :=
  match bdec (i <? mid) with
  | left Hi =>
      match bdec (j <? hi) with
      | left Hj =>
          if src.[i] <=? src.[j]
          then merge src mid hi (i + 1) j (k + 1) dst.[k <- src.[i]]
                 (Acc_inv H (mdec_i mid hi i j Hi))
          else merge src mid hi i (j + 1) (k + 1) dst.[k <- src.[j]]
                 (Acc_inv H (mdec_j mid hi i j Hj))
      | right _ =>
          merge src mid hi (i + 1) j (k + 1) dst.[k <- src.[i]]
            (Acc_inv H (mdec_i mid hi i j Hi))
      end
  | right _ =>
      match bdec (j <? hi) with
      | left Hj =>
          merge src mid hi i (j + 1) (k + 1) dst.[k <- src.[j]]
            (Acc_inv H (mdec_j mid hi i j Hj))
      | right _ => dst
      end
  end.

(* min(lo + w, m), without overflow when lo <= m *)
Definition mid_of (m w lo : int) : int := if w <? m - lo then lo + w else m.

Lemma pdec : forall m w lo : int, (0 <? w) = true -> (lo <? m) = true ->
  Zwf 0 (gap m (mid_of m w (mid_of m w lo))) (gap m lo).
Proof.
  intros m w lo Hw Hl. rewrite ltb_spec in Hw, Hl. unfold Zwf, gap, mid_of.
  destruct (w <? m - lo) eqn:E1; rewrite ?ltb_spec in E1;
    [ | rewrite <- Bool.not_true_iff_false, ltb_spec in E1].
  - destruct (w <? m - (lo + w)) eqn:E2; rewrite ?ltb_spec in E2;
      [ | rewrite <- Bool.not_true_iff_false, ltb_spec in E2]; sia.
  - destruct (w <? m - m) eqn:E2; rewrite ?ltb_spec in E2;
      [ | rewrite <- Bool.not_true_iff_false, ltb_spec in E2]; sia.
Qed.

(* One pass: the runs of width w of src, merged pairwise into dst. *)
Fixpoint pass (src : array int) (m w lo : int) (dst : array int)
    (Hw : (0 <? w) = true) (H : Acc (Zwf 0) (gap m lo)) {struct H}
    : array int :=
  match bdec (lo <? m) with
  | left Hl =>
      let mid := mid_of m w lo in
      let hi := mid_of m w mid in
      pass src m w hi
        (merge src mid hi lo mid lo dst (Zwf_well_founded 0 (mgap mid hi lo mid)))
        Hw (Acc_inv H (pdec m w lo Hw Hl))
  | right _ => dst
  end.

Lemma sdec : forall m w : int, (m <=? PArray.max_length) = true ->
  (0 <? w) = true -> (w <? m) = true -> Zwf 0 (gap m (w + w)) (gap m w).
Proof.
  intros m w Hm Hw Hl. rewrite leb_spec in Hm. rewrite ltb_spec in Hw, Hl.
  change (φ PArray.max_length) with 4194303%Z in Hm. unfold Zwf, gap. sia.
Qed.

Lemma spos : forall m w : int, (m <=? PArray.max_length) = true ->
  (0 <? w) = true -> (w <? m) = true -> (0 <? w + w) = true.
Proof.
  intros m w Hm Hw Hl. rewrite leb_spec in Hm. rewrite ltb_spec in Hw, Hl |- *.
  change (φ PArray.max_length) with 4194303%Z in Hm. sia.
Qed.

Fixpoint sort_loop (m w : int) (src dst : array int)
    (Hm : (m <=? PArray.max_length) = true) (Hw : (0 <? w) = true)
    (H : Acc (Zwf 0) (gap m w)) {struct H} : array int :=
  match bdec (w <? m) with
  | left Hl =>
      sort_loop m (w + w)
        (pass src m w 0 dst Hw (Zwf_well_founded 0 (gap m 0))) src
        Hm (spos m w Hm Hw Hl) (Acc_inv H (sdec m w Hm Hw Hl))
  | right _ => src
  end.

Definition msort (a : array int) : array int :=
  sort_loop (PArray.length a) 1 a (PArray.make (PArray.length a) 0)
    (leb_length int a) eq_refl (Zwf_well_founded 0 (gap (PArray.length a) 1)).

(* ------------------------------------------------------------------ *)
(* The adjacency: lock i keyed (a_i << 13) + i, the keys sorted, and    *)
(* st[u] the first position of room u's keys                           *)
(* ------------------------------------------------------------------ *)

Definition src_of (key : int) : int := key >> 13.
Definition idx_of (key : int) : int := key - ((key >> 13) << 13).

Fixpoint keys_loop (xla : array int) (L i : int) (K : array int)
    (H : Acc (Zwf 0) (gap L i)) {struct H} : array int :=
  match bdec (i <? L) with
  | left Hi =>
      keys_loop xla L (i + 1) K.[i <- (xla.[i] << 13) + i]
        (Acc_inv H (dec_step L i Hi))
  | right _ => K
  end.

Fixpoint st_loop (K : array int) (p : int) (st : array int)
    (H : Acc (Zwf 0) (φ p)) {struct H} : array int :=
  match bdec (0 <? p) with
  | left Hp =>
      st_loop K (p - 1) st.[src_of K.[p - 1] <- p - 1]
        (Acc_inv H (dec_down p Hp))
  | right _ => st
  end.

(* ------------------------------------------------------------------ *)
(* The badge boundaries: 1, b + 1, and x_i, y_i + 1 for every lock      *)
(* ------------------------------------------------------------------ *)

Fixpoint bnd_loop (xlx xly : array int) (L i : int) (B : array int)
    (H : Acc (Zwf 0) (gap L i)) {struct H} : array int :=
  match bdec (i <? L) with
  | left Hi =>
      bnd_loop xlx xly L (i + 1)
        B.[i + i + 2 <- xlx.[i]].[i + i + 3 <- xly.[i] + 1]
        (Acc_inv H (dec_step L i Hi))
  | right _ => B
  end.

(* ------------------------------------------------------------------ *)
(* The search: visited table stamped, explicit stack                   *)
(* ------------------------------------------------------------------ *)

(* Room u's keys from position p on: every open lock leading to an
   unvisited room pushes it. *)
Fixpoint scan (K xlb xlx xly : array int) (L u k stamp p : int)
    (vis stk : array int) (sp : int)
    (H : Acc (Zwf 0) (gap L p)) {struct H} : array int * array int * int :=
  match bdec (p <? L) with
  | left Hp =>
      let key := K.[p] in
      if src_of key =? u then
        let i := idx_of key in
        let v := xlb.[i] in
        if (xlx.[i] <=? k) && (k <=? xly.[i]) && negb (vis.[v] =? stamp)
           && (v <? PArray.length vis)
        then scan K xlb xlx xly L u k stamp (p + 1) vis.[v <- stamp]
               stk.[sp <- v] (sp + 1) (Acc_inv H (dec_step L p Hp))
        else scan K xlb xlx xly L u k stamp (p + 1) vis stk sp
               (Acc_inv H (dec_step L p Hp))
      else (vis, stk, sp)
  | right _ => (vis, stk, sp)
  end.

(* Prop side of the termination: the number of unstamped cells. *)
Fixpoint csum (f : nat -> Z) (c : nat) : Z :=
  match c with
  | O => 0%Z
  | S c' => (csum f c' + f c')%Z
  end.

Definition unm (stamp : int) (vis : array int) : Z :=
  csum (fun t => if vis.[of_Z (Z.of_nat t)] =? stamp then 0%Z else 1%Z)
       (Z.to_nat (φ (PArray.length vis))).

Definition meas (stamp : int) (vis : array int) (sp : int) : Z :=
  (2 * unm stamp vis + (φ sp))%Z.

Lemma csum_nonneg : forall f c,
  (forall t, (0 <= f t)%Z) -> (0 <= csum f c)%Z.
Proof.
  intros f c Hf. induction c as [| c IH]; simpl; [lia|]. specialize (Hf c). lia.
Qed.

Lemma csum_ext : forall f g c,
  (forall t, (t < c)%nat -> f t = g t) -> csum f c = csum g c.
Proof.
  intros f g c. induction c as [| c IH]; intros E; simpl; [reflexivity|].
  rewrite IH by (intros t Ht; apply E; lia). rewrite E by lia. reflexivity.
Qed.

Lemma csum_point : forall f g c v,
  (v < c)%nat -> (forall t, (t < c)%nat -> t <> v -> f t = g t) ->
  csum g c = (csum f c - f v + g v)%Z.
Proof.
  intros f g c v. induction c as [| c IH]; intros Hv E; simpl; [lia|].
  destruct (Nat.eq_dec c v) as [-> | Ne].
  - rewrite (csum_ext g f) by (intros t Ht; symmetry; apply E; lia). lia.
  - rewrite IH by (auto; lia). rewrite (E c ltac:(lia) Ne). lia.
Qed.

Lemma of_Z_nat_to : forall v : int, of_Z (Z.of_nat (Z.to_nat (φ v))) = v.
Proof.
  intros v. pose proof (to_Z_bounded v).
  rewrite Z2Nat.id by lia. apply of_to_Z.
Qed.

Lemma unm_nonneg : forall stamp vis, (0 <= unm stamp vis)%Z.
Proof.
  intros. unfold unm. apply csum_nonneg. intros t.
  match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

Lemma unm_set : forall stamp (vis : array int) v,
  (v <? PArray.length vis) = true -> (vis.[v] =? stamp) = false ->
  unm stamp vis.[v <- stamp] = (unm stamp vis - 1)%Z.
Proof.
  intros stamp vis v Hv Hs. unfold unm. rewrite alength_set.
  pose proof Hv as Hv'. rewrite ltb_spec in Hv. pose proof (to_Z_bounded v).
  rewrite (csum_point
    (fun t => if vis.[of_Z (Z.of_nat t)] =? stamp then 0%Z else 1%Z) _ _
    (Z.to_nat (φ v))); [ | lia | ].
  - cbv beta. rewrite !of_Z_nat_to, aget_set_same, Hs, eqb_refl by exact Hv'.
    lia.
  - intros t Htc Ht. cbv beta. rewrite aget_set_other; [reflexivity|].
    intros E. apply Ht. rewrite E. rewrite of_Z_spec.
    rewrite Z.mod_small; [lia|]. pose proof (alength_bound vis). lia.
Qed.

Lemma scan_eq : forall K xlb xlx xly L u k stamp p vis stk sp H,
  scan K xlb xlx xly L u k stamp p vis stk sp H =
  match bdec (p <? L) with
  | left Hp =>
      let key := K.[p] in
      if src_of key =? u then
        let i := idx_of key in
        let v := xlb.[i] in
        if (xlx.[i] <=? k) && (k <=? xly.[i]) && negb (vis.[v] =? stamp)
           && (v <? PArray.length vis)
        then scan K xlb xlx xly L u k stamp (p + 1) vis.[v <- stamp]
               stk.[sp <- v] (sp + 1) (Acc_inv H (dec_step L p Hp))
        else scan K xlb xlx xly L u k stamp (p + 1) vis stk sp
               (Acc_inv H (dec_step L p Hp))
      else (vis, stk, sp)
  | right _ => (vis, stk, sp)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma scan_meas_aux : forall K xlb xlx xly L u k stamp z p vis stk sp H,
  gap L p = z ->
  (meas stamp (fst (fst (scan K xlb xlx xly L u k stamp p vis stk sp H)))
        (snd (scan K xlb xlx xly L u k stamp p vis stk sp H))
   <= meas stamp vis sp)%Z.
Proof.
  intros K xlb xlx xly L u k stamp z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros p vis stk sp H Hz.
  rewrite scan_eq. destruct (bdec (p <? L)) as [Hp | Hp]; [ | simpl; lia].
  cbv zeta. destruct (src_of K.[p] =? u); [ | simpl; lia].
  destruct ((xlx.[idx_of K.[p]] <=? k) && (k <=? xly.[idx_of K.[p]])
            && negb (vis.[xlb.[idx_of K.[p]]] =? stamp)
            && (xlb.[idx_of K.[p]] <? PArray.length vis)) eqn:E.
  - eapply Z.le_trans; [eapply IH; [rewrite <- Hz; apply (dec_step L p Hp) | reflexivity]|].
    rewrite !Bool.andb_true_iff, Bool.negb_true_iff in E.
    destruct E as [[[_ E1] E2]].
    unfold meas. rewrite unm_set by assumption.
    pose proof (to_Z_bounded sp). sia.
  - eapply IH; [rewrite <- Hz; apply (dec_step L p Hp) | reflexivity].
Qed.

Lemma scan_meas : forall K xlb xlx xly L u k stamp p vis stk sp H,
  (meas stamp (fst (fst (scan K xlb xlx xly L u k stamp p vis stk sp H)))
        (snd (scan K xlb xlx xly L u k stamp p vis stk sp H))
   <= meas stamp vis sp)%Z.
Proof. intros. eapply scan_meas_aux. reflexivity. Qed.

Lemma ddec : forall K st xlb xlx xly L k stamp (vis stk : array int) sp,
  (0 <? sp) = true ->
  Zwf 0
    (meas stamp
       (fst (fst (scan K xlb xlx xly L stk.[sp - 1] k stamp st.[stk.[sp - 1]]
                   vis stk (sp - 1)
                   (Zwf_well_founded 0 (gap L st.[stk.[sp - 1]])))))
       (snd (scan K xlb xlx xly L stk.[sp - 1] k stamp st.[stk.[sp - 1]]
               vis stk (sp - 1)
               (Zwf_well_founded 0 (gap L st.[stk.[sp - 1]])))))
    (meas stamp vis sp).
Proof.
  intros. unfold Zwf. split.
  - unfold meas. pose proof (unm_nonneg stamp vis).
    pose proof (to_Z_bounded sp). lia.
  - eapply Z.le_lt_trans; [apply scan_meas|].
    unfold meas. rewrite ltb_spec in H. sia.
Qed.

Fixpoint dfs (K st xlb xlx xly : array int) (L k stamp : int)
    (vis stk : array int) (sp : int)
    (H : Acc (Zwf 0) (meas stamp vis sp)) {struct H} : array int * array int :=
  match bdec (0 <? sp) with
  | left Hs =>
      let u := stk.[sp - 1] in
      let r := scan K xlb xlx xly L u k stamp st.[u] vis stk (sp - 1)
                 (Zwf_well_founded 0 (gap L st.[u])) in
      dfs K st xlb xlx xly L k stamp (fst (fst r)) (snd (fst r)) (snd r)
        (Acc_inv H (ddec K st xlb xlx xly L k stamp vis stk sp Hs))
  | right _ => (vis, stk)
  end.

(* ------------------------------------------------------------------ *)
(* The intervals [S[j-1], S[j]) of the sorted boundaries, j = 1 .. m-1  *)
(* ------------------------------------------------------------------ *)

Fixpoint count_loop (K st xlb xlx xly S : array int) (L m s d j : int)
    (vis stk : array int) (acc : int)
    (H : Acc (Zwf 0) (gap m j)) {struct H} : int :=
  match bdec (j <? m) with
  | left Hj =>
      let p := S.[j - 1] in
      let q := S.[j] in
      if p <? q then
        let r := dfs K st xlb xlx xly L p j vis.[s <- j] stk.[0 <- s] 1
                   (Zwf_well_founded 0 (meas j vis.[s <- j] 1)) in
        count_loop K st xlb xlx xly S L m s d (j + 1) (fst r) (snd r)
          (if (fst r).[d] =? j then acc + (q - p) else acc)
          (Acc_inv H (dec_step m j Hj))
      else
        count_loop K st xlb xlx xly S L m s d (j + 1) vis stk acc
          (Acc_inv H (dec_step m j Hj))
  | right _ => acc
  end.

Definition securitybadge_core (n b s d : int) (xla xlb xlx xly : array int)
    : int :=
  let L := PArray.length xla in
  let K := msort (keys_loop xla L 0 (PArray.make L 0)
                    (Zwf_well_founded 0 (gap L 0))) in
  let st := st_loop K L (PArray.make (n + 2) L) (Zwf_well_founded 0 (φ L)) in
  let m := L + L + 2 in
  let S := msort (bnd_loop xlx xly L 0
                    (PArray.make m 0).[0 <- 1].[1 <- b + 1]
                    (Zwf_well_founded 0 (gap L 0))) in
  count_loop K st xlb xlx xly S L m s d 1
    (PArray.make (n + 1) 0) (PArray.make (n + 1) 0) 0
    (Zwf_well_founded 0 (gap m 1)).

Definition securitybadge_impl (n b s d : uint) (xla xlb xlx xly : array uint)
    : uint :=
  securitybadge_core n b s d xla xlb xlx xly.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition securitybadge : uint -> uint -> uint -> uint -> array uint ->
  array uint -> array uint -> array uint -> uint := securitybadge_impl.
