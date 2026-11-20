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

From Securitybadge.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf
  Relations.
From KattisLib Require Import Cost.
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

Lemma aget_make : forall (n : int) (b i : int), (PArray.make n b).[i] = b.
Proof. intros n b i. exact (get_make int b n i). Qed.

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

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
Elpi complexity sumbool.
Elpi complexity bdec.
Arguments bdec_cost : simpl never.
Elpi complexity andb.
Arguments andb_cost : simpl never.
Elpi complexity negb.
Arguments negb_cost : simpl never.
Elpi complexity fst.

Elpi complexity snd.


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
Elpi complexity merge.
Arguments merge_cost : simpl never.

(* min(lo + w, m), without overflow when lo <= m *)
Definition mid_of (m w lo : int) : int := if w <? m - lo then lo + w else m.
Elpi complexity mid_of.
Arguments mid_of_cost : simpl never.

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
Elpi complexity pass.
Arguments pass_cost : simpl never.

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
Elpi complexity sort_loop.
Arguments sort_loop_cost : simpl never.

Definition msort (a : array int) : array int :=
  sort_loop (PArray.length a) 1 a (PArray.make (PArray.length a) 0)
    (leb_length int a) eq_refl (Zwf_well_founded 0 (gap (PArray.length a) 1)).
Elpi complexity msort.
Arguments msort_cost : simpl never.

(* ------------------------------------------------------------------ *)
(* The adjacency: lock i keyed (a_i << 13) + i, the keys sorted, and    *)
(* st[u] the first position of room u's keys                           *)
(* ------------------------------------------------------------------ *)

Definition src_of (key : int) : int := key >> 13.
Elpi complexity src_of.
Arguments src_of_cost : simpl never.
Definition idx_of (key : int) : int := key - ((key >> 13) << 13).
Elpi complexity idx_of.
Arguments idx_of_cost : simpl never.

Fixpoint keys_loop (xla : array int) (L i : int) (K : array int)
    (H : Acc (Zwf 0) (gap L i)) {struct H} : array int :=
  match bdec (i <? L) with
  | left Hi =>
      keys_loop xla L (i + 1) K.[i <- (xla.[i] << 13) + i]
        (Acc_inv H (dec_step L i Hi))
  | right _ => K
  end.
Elpi complexity keys_loop.
Arguments keys_loop_cost : simpl never.

Fixpoint st_loop (K : array int) (p : int) (st : array int)
    (H : Acc (Zwf 0) (φ p)) {struct H} : array int :=
  match bdec (0 <? p) with
  | left Hp =>
      st_loop K (p - 1) st.[src_of K.[p - 1] <- p - 1]
        (Acc_inv H (dec_down p Hp))
  | right _ => st
  end.
Elpi complexity st_loop.
Arguments st_loop_cost : simpl never.

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
Elpi complexity bnd_loop.
Arguments bnd_loop_cost : simpl never.

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
Elpi complexity scan.
Arguments scan_cost : simpl never.

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

Lemma csum_ge : forall f c v,
  (v < c)%nat -> (forall t, (0 <= f t)%Z) -> (f v <= csum f c)%Z.
Proof.
  intros f c v. induction c as [| c IH]; intros Hv Hf; simpl; [lia|].
  destruct (Nat.eq_dec c v) as [-> | Ne].
  - pose proof (csum_nonneg f v Hf). lia.
  - pose proof (Hf c). specialize (IH ltac:(lia) Hf). lia.
Qed.

Lemma csum_const : forall c, csum (fun _ => 1%Z) c = Z.of_nat c.
Proof. induction c as [| c IH]; simpl; lia. Qed.

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

Lemma unm_pos : forall stamp (vis : array int) v,
  (v <? PArray.length vis) = true -> (vis.[v] =? stamp) = false ->
  (1 <= unm stamp vis)%Z.
Proof.
  intros stamp vis v Hv Hs. unfold unm. rewrite ltb_spec in Hv.
  pose proof (to_Z_bounded v).
  eapply Z.le_trans; [ | apply (csum_ge _ _ (Z.to_nat (φ v))) ].
  - cbv beta. rewrite of_Z_nat_to, Hs. lia.
  - lia.
  - intros t. match goal with |- context [if ?c then _ else _] => destruct c end;
    lia.
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
Elpi complexity dfs.
Arguments dfs_cost : simpl never.

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
Elpi complexity count_loop.
Arguments count_loop_cost : simpl never.

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
Elpi complexity securitybadge_core.
Arguments securitybadge_core_cost : simpl never.

Definition securitybadge_impl (n b s d : uint) (xla xlb xlx xly : array uint)
    : uint :=
  securitybadge_core n b s d xla xlb xlx xly.
Elpi complexity securitybadge_impl.
Arguments securitybadge_impl_cost : simpl never.

(* ================================================================== *)
(* Prop side                                                           *)
(* ================================================================== *)

Ltac neq_tac := let F := fresh in intro F; apply (f_equal to_Z) in F; sia.

Lemma add_sub1 : forall k : int, k + 1 - 1 = k.
Proof. intros k. apply to_Z_inj. sia. Qed.

Lemma int_cases : forall a b : int, a = b \/ ((φ a) <> (φ b))%Z.
Proof.
  intros a b. destruct (Z.eq_dec (φ a) (φ b)) as [E | E]; [left; apply to_Z_inj; exact E | right; exact E].
Qed.

(* ------------------------------------------------------------------ *)
(* merge                                                               *)
(* ------------------------------------------------------------------ *)

Section Merge.
  Variables (src dst0 : array int) (lo mid hi : int).
  Hypothesis Hlm : ((φ lo) <= (φ mid) <= (φ hi))%Z.
  Hypothesis Hhi : ((φ hi) <= (φ (PArray.length dst0)))%Z.
  Hypothesis Hs1 : forall t : int, ((φ lo) <= (φ t))%Z -> ((φ t) + 1 < (φ mid))%Z ->
    ((φ (src.[t])) <= (φ (src.[t + 1])))%Z.
  Hypothesis Hs2 : forall t : int, ((φ mid) <= (φ t))%Z -> ((φ t) + 1 < (φ hi))%Z ->
    ((φ (src.[t])) <= (φ (src.[t + 1])))%Z.

  Definition MInv (i j k : int) (dst : array int) : Prop :=
    ((φ lo) <= (φ i) <= (φ mid))%Z /\ ((φ mid) <= (φ j) <= (φ hi))%Z /\
    (φ k) = ((φ i) + (φ j) - (φ mid))%Z /\
    PArray.length dst = PArray.length dst0 /\
    (forall t, ((φ t) < (φ lo))%Z -> dst.[t] = dst0.[t]) /\
    (forall t, ((φ lo) <= (φ t))%Z -> ((φ t) + 1 < (φ k))%Z -> ((φ (dst.[t])) <= (φ (dst.[t + 1])))%Z) /\
    (((φ lo) < (φ k))%Z -> ((φ i) < (φ mid))%Z -> ((φ (dst.[k - 1])) <= (φ (src.[i])))%Z) /\
    (((φ lo) < (φ k))%Z -> ((φ j) < (φ hi))%Z -> ((φ (dst.[k - 1])) <= (φ (src.[j])))%Z) /\
    (forall t, ((φ lo) <= (φ t) < (φ k))%Z -> exists t',
       (((φ lo) <= (φ t') < (φ i))%Z \/ ((φ mid) <= (φ t') < (φ j))%Z) /\ dst.[t] = src.[t']) /\
    (forall t', (((φ lo) <= (φ t') < (φ i))%Z \/ ((φ mid) <= (φ t') < (φ j))%Z) ->
       exists t, ((φ lo) <= (φ t) < (φ k))%Z /\ dst.[t] = src.[t']).

  Lemma minv_take_i : forall i j k dst, MInv i j k dst ->
    ((φ i) < (φ mid))%Z -> (((φ j) < (φ hi))%Z -> ((φ (src.[i])) <= (φ (src.[j])))%Z) ->
    MInv (i + 1) j (k + 1) dst.[k <- src.[i]].
  Proof.
    intros i j k dst (Hi & Hj & Hk & Hl & Hlo & Hso & Hli & Hlj & H4 & H5) Hlt Hij.
    pose proof (alength_bound dst0).
    assert (Ei : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    assert (Ek : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    assert (Kin : (k <? PArray.length dst) = true) by (rewrite ltb_spec, Hl; lia).
    unfold MInv. rewrite Ei, Ek. rewrite add_sub1.
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [rewrite alength_set; exact Hl|].
    split; [intros t Ht; rewrite aget_set_other by neq_tac; apply Hlo; lia|].
    split.
    { intros t Ht1 Ht2. destruct (int_cases (t + 1) k) as [E | E].
      - rewrite E, aget_set_same by exact Kin.
        assert (t = k - 1) by (rewrite <- E, add_sub1; reflexivity). subst t.
        rewrite aget_set_other by neq_tac. apply Hli; sia.
      - assert ((φ (t + 1)) = ((φ t) + 1)%Z) by sia.
        rewrite !aget_set_other by neq_tac. apply Hso; lia. }
    split.
    { intros _ Hi1. rewrite aget_set_same by exact Kin.
      replace (src.[i + 1]) with (src.[i + 1]) by reflexivity.
      apply Hs1; lia. }
    split.
    { intros _ Hj1. rewrite aget_set_same by exact Kin. apply Hij; lia. }
    split.
    { intros t Ht. destruct (int_cases t k) as [E | E].
      - subst t. rewrite aget_set_same by exact Kin. exists i. split; [lia | reflexivity].
      - rewrite aget_set_other by neq_tac.
        destruct (H4 t ltac:(lia)) as (t' & Ht' & Et'). exists t'. split; [lia | exact Et']. }
    { intros t' Ht'. destruct (int_cases t' i) as [E | E].
      - subst t'. exists k. split; [lia|]. rewrite aget_set_same by exact Kin. reflexivity.
      - destruct (H5 t' ltac:(lia)) as (t & Ht & Et). exists t. split; [lia|].
        rewrite aget_set_other by neq_tac. exact Et. }
  Qed.

  Lemma minv_take_j : forall i j k dst, MInv i j k dst ->
    ((φ j) < (φ hi))%Z -> (((φ i) < (φ mid))%Z -> ((φ (src.[j])) <= (φ (src.[i])))%Z) ->
    MInv i (j + 1) (k + 1) dst.[k <- src.[j]].
  Proof.
    intros i j k dst (Hi & Hj & Hk & Hl & Hlo & Hso & Hli & Hlj & H4 & H5) Hlt Hij.
    pose proof (alength_bound dst0).
    assert (Ej : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    assert (Ek : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    assert (Kin : (k <? PArray.length dst) = true) by (rewrite ltb_spec, Hl; lia).
    unfold MInv. rewrite Ej, Ek. rewrite add_sub1.
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [rewrite alength_set; exact Hl|].
    split; [intros t Ht; rewrite aget_set_other by neq_tac; apply Hlo; lia|].
    split.
    { intros t Ht1 Ht2. destruct (int_cases (t + 1) k) as [E | E].
      - rewrite E, aget_set_same by exact Kin.
        assert (t = k - 1) by (rewrite <- E, add_sub1; reflexivity). subst t.
        rewrite aget_set_other by neq_tac. apply Hlj; sia.
      - assert ((φ (t + 1)) = ((φ t) + 1)%Z) by sia.
        rewrite !aget_set_other by neq_tac. apply Hso; lia. }
    split.
    { intros _ Hi1. rewrite aget_set_same by exact Kin. apply Hij; lia. }
    split.
    { intros _ Hj1. rewrite aget_set_same by exact Kin. apply Hs2; lia. }
    split.
    { intros t Ht. destruct (int_cases t k) as [E | E].
      - subst t. rewrite aget_set_same by exact Kin. exists j. split; [lia | reflexivity].
      - rewrite aget_set_other by neq_tac.
        destruct (H4 t ltac:(lia)) as (t' & Ht' & Et'). exists t'. split; [lia | exact Et']. }
    { intros t' Ht'. destruct (int_cases t' j) as [E | E].
      - subst t'. exists k. split; [lia|]. rewrite aget_set_same by exact Kin. reflexivity.
      - destruct (H5 t' ltac:(lia)) as (t & Ht & Et). exists t. split; [lia|].
        rewrite aget_set_other by neq_tac. exact Et. }
  Qed.

  Definition merged (r : array int) : Prop :=
    PArray.length r = PArray.length dst0 /\
    (forall t, ((φ t) < (φ lo))%Z -> r.[t] = dst0.[t]) /\
    (forall t, ((φ lo) <= (φ t))%Z -> ((φ t) + 1 < (φ hi))%Z -> ((φ (r.[t])) <= (φ (r.[t + 1])))%Z) /\
    (forall t, ((φ lo) <= (φ t) < (φ hi))%Z -> exists t',
       ((φ lo) <= (φ t') < (φ hi))%Z /\ r.[t] = src.[t']) /\
    (forall t', ((φ lo) <= (φ t') < (φ hi))%Z ->
       exists t, ((φ lo) <= (φ t) < (φ hi))%Z /\ r.[t] = src.[t']).

  Lemma merge_spec_aux : forall z i j k dst H, mgap mid hi i j = z ->
    MInv i j k dst -> merged (merge src mid hi i j k dst H).
  Proof.
    intro z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros i j k dst H Hz HI. destruct H as [Hacc]. simpl.
    pose proof HI as (Hi & Hj & Hk & Hl & Hlo & Hso & Hli & Hlj & H4 & H5).
    destruct (bdec (i <? mid)) as [Ci | Ci];
      [pose proof Ci as Ci'; rewrite ltb_spec in Ci'
      | pose proof Ci as Ci'; rewrite <- Bool.not_true_iff_false, ltb_spec in Ci'];
    (destruct (bdec (j <? hi)) as [Cj | Cj];
      [pose proof Cj as Cj'; rewrite ltb_spec in Cj'
      | pose proof Cj as Cj'; rewrite <- Bool.not_true_iff_false, ltb_spec in Cj']).
    - destruct (src.[i] <=? src.[j]) eqn:Cs.
      + rewrite leb_spec in Cs.
        eapply IH; [rewrite <- Hz; apply mdec_i; exact Ci | reflexivity |].
        apply minv_take_i; [exact HI | lia | intros; lia].
      + rewrite <- Bool.not_true_iff_false, leb_spec in Cs.
        eapply IH; [rewrite <- Hz; apply mdec_j; exact Cj | reflexivity |].
        apply minv_take_j; [exact HI | lia | intros; lia].
    - eapply IH; [rewrite <- Hz; apply mdec_i; exact Ci | reflexivity |].
      apply minv_take_i; [exact HI | lia | intros; lia].
    - eapply IH; [rewrite <- Hz; apply mdec_j; exact Cj | reflexivity |].
      apply minv_take_j; [exact HI | lia | intros; lia].
    - assert ((φ i) = (φ mid)) by lia. assert ((φ j) = (φ hi)) by lia.
      split; [exact Hl|]. split; [exact Hlo|]. split.
      { intros t Ht1 Ht2. apply Hso; lia. }
      split.
      { intros t Ht. destruct (H4 t ltac:(lia)) as (t' & Ht' & E).
        exists t'. split; [lia | exact E]. }
      { intros t' Ht'. destruct (H5 t' ltac:(lia)) as (t & Ht & E).
        exists t. split; [lia | exact E]. }
  Qed.

  Lemma merge_spec : forall H, merged (merge src mid hi lo mid lo dst0 H).
  Proof.
    intros H. eapply merge_spec_aux; [reflexivity|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|].
    split; [reflexivity|]. split; [intros; lia|].
    split; [intros; lia|]. split; [intros; lia|].
    split; [intros; lia|]. intros; lia.
  Qed.
End Merge.

(* ------------------------------------------------------------------ *)
(* pass, sort_loop, msort                                              *)
(* ------------------------------------------------------------------ *)

Lemma mod2_mod : forall a w : Z, (0 < w)%Z -> (a mod (2 * w) = 0)%Z -> (a mod w = 0)%Z.
Proof.
  intros a w Hw H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|].
  eapply Z.divide_trans; [|exact H]. exists 2%Z. lia.
Qed.

Lemma mod_add_self : forall a w : Z, (0 < w)%Z -> (a mod w = 0)%Z -> ((a + w) mod w = 0)%Z.
Proof.
  intros a w Hw H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|].
  apply Z.divide_add_r; [exact H | apply Z.divide_refl].
Qed.

Lemma mod_between : forall a w x : Z, (0 < w)%Z -> (a mod w = 0)%Z ->
  (a < x < a + w)%Z -> (x mod w <> 0)%Z.
Proof.
  intros a w x Hw Ha Hx Hx0.
  apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hx0; [|lia].
  assert (D : (w | x - a)%Z) by (apply Z.divide_sub_r; assumption).
  apply Z.divide_pos_le in D; lia.
Qed.

Lemma mid_of_val : forall m w lo : int, ((φ lo) <= (φ m))%Z ->
  (φ (mid_of m w lo)) = Z.min ((φ lo) + (φ w)) (φ m).
Proof.
  intros m w lo H. unfold mid_of.
  destruct (w <? m - lo) eqn:E;
    [rewrite ltb_spec in E | rewrite <- Bool.not_true_iff_false, ltb_spec in E]; sia.
Qed.

Definition runs (a : array int) (m : int) (w : Z) : Prop :=
  forall t : int, ((φ t) + 1 < (φ m))%Z -> (((φ t) + 1) mod w <> 0)%Z ->
    ((φ (a.[t])) <= (φ (a.[t + 1])))%Z.

Definition subm (a b : array int) (m : int) : Prop :=
  forall t : int, ((φ t) < (φ m))%Z -> exists t', ((φ t') < (φ m))%Z /\ a.[t] = b.[t'].

Lemma pass_eq : forall src m w lo dst Hw H,
  pass src m w lo dst Hw H =
  match bdec (lo <? m) with
  | left Hl =>
      let mid := mid_of m w lo in
      let hi := mid_of m w mid in
      pass src m w hi
        (merge src mid hi lo mid lo dst (Zwf_well_founded 0 (mgap mid hi lo mid)))
        Hw (Acc_inv H (pdec m w lo Hw Hl))
  | right _ => dst
  end.
Proof. intros. destruct H. reflexivity. Qed.

Section Pass.
  Variables (src : array int) (m w : int).
  Hypothesis Hm : ((φ m) <= 4194303)%Z.
  Hypothesis Hw : (0 < (φ w))%Z.
  Hypothesis Hrun : runs src m (φ w).

  Definition PInv (lo : int) (dst : array int) : Prop :=
    (((φ lo) mod (2 * (φ w)) = 0)%Z \/ (φ lo) = (φ m)) /\ ((φ lo) <= (φ m))%Z /\
    (φ (PArray.length dst)) = (φ m) /\
    (forall t, ((φ t) + 1 < (φ lo))%Z -> (((φ t) + 1) mod (2 * (φ w)) <> 0)%Z ->
       ((φ (dst.[t])) <= (φ (dst.[t + 1])))%Z) /\
    (forall t, ((φ t) < (φ lo))%Z -> exists t', ((φ t') < (φ m))%Z /\ dst.[t] = src.[t']) /\
    (forall t', ((φ t') < (φ lo))%Z -> exists t, ((φ t) < (φ lo))%Z /\ dst.[t] = src.[t']).

  Lemma pass_spec_aux : forall z lo dst Hw' H, gap m lo = z -> PInv lo dst ->
    PInv m (pass src m w lo dst Hw' H).
  Proof.
    intro z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros lo dst Hw' H Hz HP. rewrite pass_eq.
    destruct (bdec (lo <? m)) as [Hl | Hl].
    2:{ rewrite <- Bool.not_true_iff_false, ltb_spec in Hl.
        destruct HP as (H1 & H2 & HP). assert (Em : lo = m) by (apply to_Z_inj; lia).
        subst lo. split; [right; reflexivity|]. split; [lia|]. exact HP. }
    cbv zeta. pose proof Hl as Hl'. rewrite ltb_spec in Hl'.
    destruct HP as (Hmod & Hle & Hlen & Hso & Hf & Hb).
    destruct Hmod as [Hmod | Hmod]; [|lia].
    set (mid := mid_of m w lo). set (hi := mid_of m w mid).
    assert (Emid : (φ mid) = Z.min ((φ lo) + (φ w)) (φ m)) by (apply mid_of_val; lia).
    assert (Ehi : (φ hi) = Z.min ((φ mid) + (φ w)) (φ m)) by (apply mid_of_val; lia).
    assert (Hlow : ((φ lo) mod (φ w) = 0)%Z) by (apply (mod2_mod _ _ Hw Hmod)).
    pose proof (merge_spec src dst lo mid hi ltac:(lia) ltac:(lia)) as MS.
    assert (S1 : forall t : int, ((φ lo) <= (φ t))%Z -> ((φ t) + 1 < (φ mid))%Z ->
      ((φ (src.[t])) <= (φ (src.[t + 1])))%Z).
    { intros t Ht1 Ht2. apply Hrun; [lia|]. apply (mod_between (φ lo)); lia. }
    assert (S2 : forall t : int, ((φ mid) <= (φ t))%Z -> ((φ t) + 1 < (φ hi))%Z ->
      ((φ (src.[t])) <= (φ (src.[t + 1])))%Z).
    { intros t Ht1 Ht2. apply Hrun; [lia|].
      assert ((φ mid) = ((φ lo) + (φ w))%Z) by lia.
      apply (mod_between (φ mid)); [lia | | lia].
      rewrite H0. apply mod_add_self; lia. }
    destruct (MS S1 S2 (Zwf_well_founded 0 (mgap mid hi lo mid)))
      as (Ml & Mlo & Mso & Mf & Mb).
    eapply IH; [rewrite <- Hz; apply (pdec m w lo Hw' Hl) | reflexivity |].
    fold mid hi.
    split.
    { destruct (Z.eq_dec (φ hi) (φ m)) as [E | E]; [right; exact E | left].
      assert ((φ hi) = ((φ lo) + 2 * (φ w))%Z) by lia. rewrite H0.
      replace ((φ lo) + 2 * (φ w))%Z with ((φ lo) + (2 * (φ w)))%Z by lia.
      apply mod_add_self; lia. }
    split; [lia|]. split; [rewrite Ml; exact Hlen|].
    split.
    { intros t Ht1 Ht2. pose proof (to_Z_bounded t).
      destruct (Z_lt_le_dec ((φ t) + 1) (φ lo)) as [C | C].
      - rewrite !Mlo by sia. apply Hso; lia.
      - destruct (Z.eq_dec ((φ t) + 1) (φ lo)) as [C' | C']; [rewrite C' in Ht2; contradiction|].
        apply Mso; lia. }
    split.
    { intros t Ht. destruct (Z_lt_le_dec (φ t) (φ lo)) as [C | C].
      - rewrite Mlo by exact C. apply Hf; exact C.
      - destruct (Mf t ltac:(lia)) as (t' & Ht' & E). exists t'. split; [lia | exact E]. }
    { intros t' Ht'. destruct (Z_lt_le_dec (φ t') (φ lo)) as [C | C].
      - destruct (Hb t' C) as (t & Ht & E). exists t. split; [lia|].
        rewrite Mlo by exact Ht. exact E.
      - destruct (Mb t' ltac:(lia)) as (t & Ht & E). exists t. split; [lia | exact E]. }
  Qed.
End Pass.

Lemma sort_loop_eq : forall m w src dst Hm Hw H,
  sort_loop m w src dst Hm Hw H =
  match bdec (w <? m) with
  | left Hl =>
      sort_loop m (w + w)
        (pass src m w 0 dst Hw (Zwf_well_founded 0 (gap m 0))) src
        Hm (spos m w Hm Hw Hl) (Acc_inv H (sdec m w Hm Hw Hl))
  | right _ => src
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition sorted_upto (r : array int) (m : int) : Prop :=
  forall t1 t2 : int, ((φ t1) <= (φ t2) < (φ m))%Z -> ((φ (r.[t1])) <= (φ (r.[t2])))%Z.

Lemma adjacent_sorted : forall (r : array int) (m : int),
  (forall t : int, ((φ t) + 1 < (φ m))%Z -> ((φ (r.[t])) <= (φ (r.[t + 1])))%Z) ->
  sorted_upto r m.
Proof.
  intros r m Hadj t1 t2 Ht.
  assert (Hgen : forall d : nat, forall t : int, ((φ t) + Z.of_nat d < (φ m))%Z ->
            ((φ (r.[t])) <= (φ (r.[of_Z ((φ t) + Z.of_nat d)])))%Z).
  { induction d as [| d IH]; intros t H.
    - rewrite Z.add_0_r, of_to_Z. lia.
    - pose proof (to_Z_bounded t). pose proof (to_Z_bounded m).
      eapply Z.le_trans; [apply (IH t); lia|].
      set (u := of_Z ((φ t) + Z.of_nat d)).
      assert (Eu : (φ u) = ((φ t) + Z.of_nat d)%Z)
        by (unfold u; rewrite of_Z_spec; apply Z.mod_small; lia).
      replace (of_Z ((φ t) + Z.of_nat (S d))) with (u + 1)
        by (apply to_Z_inj; rewrite of_Z_spec, Z.mod_small by lia; sia).
      apply Hadj. lia. }
  pose proof (Hgen (Z.to_nat ((φ t2) - (φ t1))) t1 ltac:(lia)) as G.
  replace (of_Z ((φ t1) + Z.of_nat (Z.to_nat ((φ t2) - (φ t1))))) with t2 in G; [exact G|].
  rewrite Z2Nat.id by lia. replace ((φ t1) + ((φ t2) - (φ t1)))%Z with (φ t2) by lia.
  symmetry. apply of_to_Z.
Qed.

Lemma sort_loop_spec_aux : forall (a0 : array int) (m : int) z w src dst Hm Hw H,
  gap m w = z ->
  (φ (PArray.length src)) = (φ m) -> (φ (PArray.length dst)) = (φ m) ->
  runs src m (φ w) -> subm src a0 m -> subm a0 src m ->
  let r := sort_loop m w src dst Hm Hw H in
  (φ (PArray.length r)) = (φ m) /\ sorted_upto r m /\ subm r a0 m /\ subm a0 r m.
Proof.
  intros a0 m z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros w src dst Hm Hw H Hz Ls Ld Hr S1 S2. cbv zeta. rewrite sort_loop_eq.
  pose proof Hm as Hm'. rewrite leb_spec in Hm'. change (φ PArray.max_length) with 4194303%Z in Hm'.
  pose proof Hw as Hw'. rewrite ltb_spec in Hw'. change (φ 0) with 0%Z in Hw'.
  destruct (bdec (w <? m)) as [Hl | Hl].
  - pose proof Hl as Hl'. rewrite ltb_spec in Hl'.
    pose proof (pass_spec_aux src m w Hw' Hr _ 0 dst Hw
                  (Zwf_well_founded 0 (gap m 0)) eq_refl) as P.
    destruct P as (_ & _ & Pl & Pso & Pf & Pb).
    { split; [left; reflexivity|]. change (φ 0) with 0%Z. pose proof (to_Z_bounded m).
      split; [lia|]. split; [exact Ld|].
      split; [intros t Ht; pose proof (to_Z_bounded t); lia|].
      split; intros t Ht; pose proof (to_Z_bounded t); lia. }
    eapply IH; [rewrite <- Hz; apply (sdec m w Hm Hw Hl) | reflexivity | exact Pl | exact Ls | | | ].
    + intros t Ht1 Ht2. assert ((φ (w + w)) = (2 * (φ w))%Z) by sia. rewrite H0 in Ht2.
      apply Pso; lia.
    + intros t Ht. destruct (Pf t Ht) as (t' & Ht' & E).
      destruct (S1 t' Ht') as (t'' & Ht'' & E'). exists t''. split; [exact Ht''|]. congruence.
    + intros t Ht. destruct (S2 t Ht) as (t' & Ht' & E).
      destruct (Pb t' Ht') as (t'' & Ht'' & E'). exists t''. split; [lia|]. congruence.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hl.
    split; [exact Ls|]. split; [|split; assumption].
    apply adjacent_sorted. intros t Ht. apply Hr; [exact Ht|].
    pose proof (to_Z_bounded t). rewrite Z.mod_small by lia. lia.
Qed.

Lemma msort_spec : forall a : array int,
  let r := msort a in
  PArray.length@{Set} r = PArray.length@{Set} a /\ sorted_upto r (PArray.length@{Set} a) /\
  subm r a (PArray.length@{Set} a) /\ subm a r (PArray.length@{Set} a).
Proof.
  intros a. cbv zeta. unfold msort.
  pose proof (alength_bound a) as Ba.
  destruct (sort_loop_spec_aux a (PArray.length a) _ 1 a
     (PArray.make (PArray.length a) 0) (leb_length int a) eq_refl
     (Zwf_well_founded 0 (gap (PArray.length a) 1)) eq_refl)
     as (L1 & L2 & L3 & L4).
  - reflexivity.
  - rewrite alength_make. rewrite (leb_length int a). reflexivity.
  - intros t _ Ht. exfalso. apply Ht. change (φ 1) with 1%Z. apply Z.mod_1_r.
  - intros t Ht. exists t. split; [exact Ht | reflexivity].
  - intros t Ht. exists t. split; [exact Ht | reflexivity].
  - split; [apply to_Z_inj; exact L1|]. split; [exact L2|]. split; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* keys_loop, bnd_loop, st_loop                                        *)
(* ------------------------------------------------------------------ *)

Lemma keys_loop_eq : forall xla L i K H,
  keys_loop xla L i K H =
  match bdec (i <? L) with
  | left Hi =>
      keys_loop xla L (i + 1) K.[i <- (xla.[i] << 13) + i]
        (Acc_inv H (dec_step L i Hi))
  | right _ => K
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma keys_loop_spec : forall xla L z i K H, gap L i = z ->
  ((φ i) <= (φ L))%Z -> PArray.length K = L ->
  (forall t, ((φ t) < (φ i))%Z -> K.[t] = (xla.[t] << 13) + t) ->
  PArray.length (keys_loop xla L i K H) = L /\
  (forall t, ((φ t) < (φ L))%Z -> (keys_loop xla L i K H).[t] = (xla.[t] << 13) + t).
Proof.
  intros xla L z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i K H Hz Hi HK Hc. rewrite keys_loop_eq.
  destruct (bdec (i <? L)) as [Hl | Hl].
  - pose proof Hl as Hl'. rewrite ltb_spec in Hl'.
    eapply IH; [rewrite <- Hz; apply dec_step; exact Hl | reflexivity | sia | | ].
    + rewrite alength_set. exact HK.
    + intros t Ht. destruct (int_cases t i) as [E | E].
      * subst t. apply aget_set_same. rewrite HK. exact Hl.
      * rewrite aget_set_other by neq_tac. apply Hc. sia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hl.
    split; [exact HK|]. intros t Ht. apply Hc. lia.
Qed.

Lemma bnd_loop_eq : forall xlx xly L i B H,
  bnd_loop xlx xly L i B H =
  match bdec (i <? L) with
  | left Hi =>
      bnd_loop xlx xly L (i + 1)
        B.[i + i + 2 <- xlx.[i]].[i + i + 3 <- xly.[i] + 1]
        (Acc_inv H (dec_step L i Hi))
  | right _ => B
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma bnd_loop_spec : forall xlx xly L (c0 c1 : int) z i B H, gap L i = z ->
  ((φ L) <= 5000)%Z -> ((φ i) <= (φ L))%Z ->
  (φ (PArray.length B)) = (2 * (φ L) + 2)%Z ->
  B.[0] = c0 -> B.[1] = c1 ->
  (forall t, ((φ t) < (φ i))%Z -> B.[t + t + 2] = xlx.[t] /\ B.[t + t + 3] = xly.[t] + 1) ->
  let r := bnd_loop xlx xly L i B H in
  (φ (PArray.length r)) = (2 * (φ L) + 2)%Z /\ r.[0] = c0 /\ r.[1] = c1 /\
  (forall t, ((φ t) < (φ L))%Z -> r.[t + t + 2] = xlx.[t] /\ r.[t + t + 3] = xly.[t] + 1).
Proof.
  intros xlx xly L c0 c1 z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i B H Hz HL Hi HB H0 H1 Hc. cbv zeta. rewrite bnd_loop_eq.
  destruct (bdec (i <? L)) as [Hl | Hl].
  - pose proof Hl as Hl'. rewrite ltb_spec in Hl'.
    assert (In2 : (i + i + 2 <? PArray.length B) = true) by (rewrite ltb_spec; sia).
    assert (In3 : (i + i + 3 <? PArray.length B.[i + i + 2 <- xlx.[i]]) = true)
      by (rewrite alength_set, ltb_spec; sia).
    eapply IH; [rewrite <- Hz; apply dec_step; exact Hl | reflexivity | exact HL | sia | | | | ].
    + rewrite !alength_set. exact HB.
    + rewrite !aget_set_other by neq_tac. exact H0.
    + rewrite !aget_set_other by neq_tac. exact H1.
    + intros t Ht. destruct (int_cases t i) as [E | E].
      * subst t. rewrite aget_set_same by exact In3. split; [|reflexivity].
        rewrite aget_set_other by neq_tac. apply aget_set_same. exact In2.
      * destruct (Hc t ltac:(sia)) as [E2 E3].
        rewrite !(aget_set_other _ (i + i + 3)) by neq_tac.
        rewrite !(aget_set_other _ (i + i + 2)) by neq_tac. split; assumption.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hl.
    split; [exact HB|]. split; [exact H0|]. split; [exact H1|].
    intros t Ht. apply Hc. lia.
Qed.

Lemma st_loop_eq : forall K p st H,
  st_loop K p st H =
  match bdec (0 <? p) with
  | left Hp =>
      st_loop K (p - 1) st.[src_of K.[p - 1] <- p - 1]
        (Acc_inv H (dec_down p Hp))
  | right _ => st
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma st_loop_spec : forall (K : array int) (L : int) (st0 : array int),
  (forall q, ((φ q) < (φ L))%Z -> (src_of K.[q] <? PArray.length st0) = true) ->
  forall z p st H, (φ p) = z ->
  ((φ p) <= (φ L))%Z -> PArray.length st = PArray.length st0 ->
  (forall q, ((φ p) <= (φ q) < (φ L))%Z ->
     ((φ p) <= (φ (st.[src_of K.[q]])) <= (φ q))%Z /\
     src_of K.[st.[src_of K.[q]]] = src_of K.[q]) ->
  forall q, ((φ q) < (φ L))%Z ->
     ((φ ((st_loop K p st H).[src_of K.[q]])) <= (φ q))%Z /\
     src_of K.[(st_loop K p st H).[src_of K.[q]]] = src_of K.[q].
Proof.
  intros K L st0 Hsrc z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros p st H Hz Hp Hl Hc. rewrite st_loop_eq.
  destruct (bdec (0 <? p)) as [Hq | Hq].
  - pose proof Hq as Hq'. rewrite ltb_spec in Hq'. change (φ 0) with 0%Z in Hq'.
    assert (Ep : (φ (p - 1)) = ((φ p) - 1)%Z) by sia.
    eapply IH; [rewrite <- Hz; apply dec_down; exact Hq | reflexivity | lia | | ].
    + rewrite alength_set. exact Hl.
    + intros q Hq2. rewrite Ep in Hq2.
      assert (Inb : (src_of K.[p - 1] <? PArray.length st) = true)
        by (rewrite Hl; apply Hsrc; lia).
      destruct (int_cases (src_of K.[q]) (src_of K.[p - 1])) as [E | E].
      * rewrite E, aget_set_same by exact Inb. rewrite Ep.
        split; [|reflexivity].
        destruct (int_cases q (p - 1)) as [E2 | E2]; [subst q; lia|].
        assert ((φ p) <= (φ q))%Z by sia. lia.
      * rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity).
        destruct (int_cases q (p - 1)) as [E2 | E2]; [subst q; exfalso; apply E; reflexivity|].
        destruct (Hc q ltac:(sia)) as [C1 C2]. split; [lia | exact C2].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hq. change (φ 0) with 0%Z in Hq.
    intros q Hq2. destruct (Hc q ltac:(pose proof (to_Z_bounded q); lia)) as [C1 C2].
    split; [lia | exact C2].
Qed.

(* ------------------------------------------------------------------ *)
(* The search                                                          *)
(* ------------------------------------------------------------------ *)

Lemma dfs_eq : forall K st xlb xlx xly L k stamp vis stk sp H,
  dfs K st xlb xlx xly L k stamp vis stk sp H =
  match bdec (0 <? sp) with
  | left Hs =>
      let u := stk.[sp - 1] in
      let r := scan K xlb xlx xly L u k stamp st.[u] vis stk (sp - 1)
                 (Zwf_well_founded 0 (gap L st.[u])) in
      dfs K st xlb xlx xly L k stamp (fst (fst r)) (snd (fst r)) (snd r)
        (Acc_inv H (ddec K st xlb xlx xly L k stamp vis stk sp Hs))
  | right _ => (vis, stk)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma mark_mono : forall (vis : array int) v w stamp,
  (v <? PArray.length vis) = true -> vis.[w] = stamp -> vis.[v <- stamp].[w] = stamp.
Proof.
  intros vis v w stamp Hv Hw. destruct (int_cases v w) as [E | E].
  - subst. apply aget_set_same. exact Hv.
  - rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity). exact Hw.
Qed.

Section Search.
  Variables (K st xla xlb xlx xly : array int) (L N1 k stamp s : int).
  Hypothesis HN1 : ((φ N1) <= 4194303)%Z.
  Hypothesis E1 : forall q, ((φ q) < (φ L))%Z -> exists i, ((φ i) < (φ L))%Z /\
    src_of K.[q] = xla.[i] /\ idx_of K.[q] = i.
  Hypothesis E2 : forall i, ((φ i) < (φ L))%Z -> exists q, ((φ q) < (φ L))%Z /\
    src_of K.[q] = xla.[i] /\ idx_of K.[q] = i.
  Hypothesis E3 : forall q1 q2, ((φ q1) <= (φ q2) < (φ L))%Z ->
    ((φ (src_of K.[q1])) <= (φ (src_of K.[q2])))%Z.
  Hypothesis E4 : forall q, ((φ q) < (φ L))%Z ->
    ((φ (st.[src_of K.[q]])) <= (φ q))%Z /\
    src_of K.[st.[src_of K.[q]]] = src_of K.[q].
  Hypothesis Hlb : forall i, ((φ i) < (φ L))%Z -> ((φ (xlb.[i])) < (φ N1))%Z.

  Definition opn (i : int) : Prop := ((φ (xlx.[i])) <= (φ k) <= (φ (xly.[i])))%Z.

  Definition mstep (u w : int) : Prop :=
    exists t, ((φ t) < (φ L))%Z /\ xla.[t] = u /\ xlb.[t] = w /\ opn t.

  Definition reach (v : int) : Prop := clos_refl_trans int mstep s v.

  Definition instack (stk : array int) (sp v : int) : Prop :=
    exists t, ((φ t) < (φ sp))%Z /\ stk.[t] = v.

  Definition closed (vis : array int) (v : int) : Prop :=
    forall w, mstep v w -> vis.[w] = stamp.

  Definition CI (vis stk : array int) (sp : int) : Prop :=
    (φ (PArray.length vis)) = (φ N1) /\ (φ (PArray.length stk)) = (φ N1) /\
    (forall v, vis.[v] = stamp -> reach v) /\
    (forall t, ((φ t) < (φ sp))%Z -> vis.[stk.[t]] = stamp) /\
    ((φ sp) + unm stamp vis <= (φ N1))%Z /\
    (forall v, ((φ (vis.[v])) <= (φ stamp))%Z).

  Section Scan.
    Variables (u p0 : int).

    Definition SInv (p : int) (vis stk : array int) (sp : int) : Prop :=
      CI vis stk sp /\ vis.[u] = stamp /\ vis.[s] = stamp /\
      (forall v, vis.[v] = stamp -> v = u \/ instack stk sp v \/ closed vis v) /\
      ((φ p0) <= (φ p))%Z /\
      (forall q, ((φ p0) <= (φ q) < (φ p))%Z -> src_of K.[q] = u /\
         (opn (idx_of K.[q]) -> vis.[xlb.[idx_of K.[q]]] = stamp)).

    Lemma scan_spec_aux : forall z p vis stk sp H, gap L p = z ->
      SInv p vis stk sp ->
      exists pe, SInv pe
        (fst (fst (scan K xlb xlx xly L u k stamp p vis stk sp H)))
        (snd (fst (scan K xlb xlx xly L u k stamp p vis stk sp H)))
        (snd (scan K xlb xlx xly L u k stamp p vis stk sp H)) /\
      (((φ L) <= (φ pe))%Z \/ src_of K.[pe] <> u).
    Proof.
      intro z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
      intros p vis stk sp H Hz HS. rewrite scan_eq.
      destruct (bdec (p <? L)) as [Hp | Hp].
      2:{ rewrite <- Bool.not_true_iff_false, ltb_spec in Hp.
          exists p. split; [exact HS | left; lia]. }
      pose proof Hp as Hp'. rewrite ltb_spec in Hp'. cbv zeta.
      destruct (src_of K.[p] =? u) eqn:Hu.
      2:{ exists p. split; [exact HS|]. right. intro F. rewrite F, eqb_refl in Hu.
          discriminate. }
      rewrite eqb_spec in Hu.
      destruct (E1 p Hp') as (i & Hi & Ei & Ii).
      rewrite Ii.
      pose proof (Hlb i Hi) as Hv.
      destruct HS as (HC & Hmu & Hms & Hcl & Hp0 & Hpr).
      pose proof HC as (Lv & Ls & Hre & Hst & Hun & Hval).
      assert (Ep : (φ (p + 1)) = ((φ p) + 1)%Z) by sia.
      destruct ((xlx.[i] <=? k) && (k <=? xly.[i]) && negb (vis.[xlb.[i]] =? stamp)
                && (xlb.[i] <? PArray.length vis)) eqn:Ok.
      - rewrite !Bool.andb_true_iff, Bool.negb_true_iff in Ok.
        destruct Ok as [[[O1 O2] O3] O4].
        rewrite leb_spec in O1, O2.
        set (v := xlb.[i]) in *.
        pose proof (unm_pos stamp vis v O4 O3) as Up.
        pose proof (unm_set stamp vis v O4 O3) as Us.
        pose proof (unm_nonneg stamp vis).
        pose proof (to_Z_bounded sp).
        assert (Insp : (sp <? PArray.length stk) = true) by (rewrite ltb_spec; lia).
        assert (Esp : (φ (sp + 1)) = ((φ sp) + 1)%Z) by sia.
        assert (Vneq : vis.[v] <> stamp) by (intro F; rewrite F, eqb_refl in O3; discriminate).
        assert (Mv : vis.[v <- stamp].[v] = stamp) by (apply aget_set_same; exact O4).
        assert (Rv : reach v).
        { eapply rt_trans; [apply Hre; exact Hmu|]. apply rt_step.
          exists i. split; [exact Hi|]. split; [rewrite <- Ei; exact Hu|].
          split; [reflexivity|]. unfold opn. lia. }
        eapply IH; [rewrite <- Hz; apply dec_step; exact Hp | reflexivity |].
        split; [split|].
        { rewrite alength_set. exact Lv. }
        split; [rewrite alength_set; exact Ls|].
        split.
        { intros w Hw. destruct (int_cases v w) as [E | E]; [subst w; exact Rv|].
          rewrite aget_set_other in Hw by (intro F; apply E; rewrite F; reflexivity).
          apply Hre; exact Hw. }
        split.
        { intros t Ht. rewrite Esp in Ht. destruct (int_cases t sp) as [E | E].
          - subst t. rewrite aget_set_same by exact Insp. exact Mv.
          - rewrite (aget_set_other stk sp t v) by neq_tac.
            apply mark_mono; [exact O4|]. apply Hst. lia. }
        split; [rewrite Esp, Us; lia|].
        { intros w. destruct (int_cases v w) as [E | E].
          - subst w. rewrite Mv. lia.
          - rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity). apply Hval. }
        split; [apply mark_mono; assumption|].
        split; [apply mark_mono; assumption|].
        split.
        { intros w Hw. destruct (int_cases v w) as [E | E].
          - subst w. right; left. exists sp. split; [lia|].
            apply aget_set_same. exact Insp.
          - rewrite aget_set_other in Hw by (intro F; apply E; rewrite F; reflexivity).
            destruct (Hcl w Hw) as [Hw1 | [(t & Ht & Et) | Hw3]].
            + left; exact Hw1.
            + right; left. exists t. split; [lia|].
              rewrite aget_set_other by neq_tac. exact Et.
            + right; right. intros x Hx. apply mark_mono; [exact O4|]. apply Hw3; exact Hx. }
        split; [lia|].
        { intros q Hq. rewrite Ep in Hq. destruct (int_cases q p) as [E | E].
          - subst q. split; [exact Hu|]. rewrite Ii. intros _. exact Mv.
          - destruct (Hpr q ltac:(lia)) as [Q1 Q2]. split; [exact Q1|].
            intros Ho. apply mark_mono; [exact O4|]. apply Q2; exact Ho. }
      - eapply IH; [rewrite <- Hz; apply dec_step; exact Hp | reflexivity |].
        split; [exact HC|]. split; [exact Hmu|]. split; [exact Hms|]. split; [exact Hcl|].
        split; [lia|].
        intros q Hq. rewrite Ep in Hq. destruct (int_cases q p) as [E | E].
        + subst q. split; [exact Hu|]. rewrite Ii. intros [Ho1 Ho2].
          destruct (vis.[xlb.[i]] =? stamp) eqn:Em; [apply eqb_spec; exact Em|].
          exfalso. assert (Hlt : (xlb.[i] <? PArray.length vis) = true)
            by (rewrite ltb_spec; lia).
          rewrite Hlt in Ok.
          assert (B1 : (xlx.[i] <=? k) = true) by (rewrite leb_spec; exact Ho1).
          assert (B2 : (k <=? xly.[i]) = true) by (rewrite leb_spec; exact Ho2).
          rewrite B1, B2 in Ok. discriminate.
        + apply Hpr. lia.
    Qed.
  End Scan.

  Definition DInv (vis stk : array int) (sp : int) : Prop :=
    CI vis stk sp /\ vis.[s] = stamp /\
    (forall v, vis.[v] = stamp -> instack stk sp v \/ closed vis v).

  Lemma dfs_spec_aux : forall z vis stk sp H, meas stamp vis sp = z ->
    DInv vis stk sp ->
    let r := dfs K st xlb xlx xly L k stamp vis stk sp H in
    (forall v, (fst r).[v] = stamp <-> reach v) /\
    (φ (PArray.length (fst r))) = (φ N1) /\ (φ (PArray.length (snd r))) = (φ N1) /\
    (forall v, ((φ ((fst r).[v])) <= (φ stamp))%Z).
  Proof.
    intro z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros vis stk sp H Hz HD. cbv zeta. rewrite dfs_eq.
    destruct HD as (HC & Hms & Hcl).
    pose proof HC as (Lv & Ls & Hre & Hst & Hun & Hval).
    destruct (bdec (0 <? sp)) as [Hs | Hs].
    - pose proof Hs as Hs'. rewrite ltb_spec in Hs'. change (φ 0) with 0%Z in Hs'.
      cbv zeta.
      set (u := stk.[sp - 1]).
      assert (Esp : (φ (sp - 1)) = ((φ sp) - 1)%Z) by sia.
      assert (Hmu : vis.[u] = stamp) by (apply Hst; lia).
      destruct (scan_spec_aux u st.[u] _ st.[u] vis stk (sp - 1)
                 (Zwf_well_founded 0 (gap L st.[u])) eq_refl) as (pe & HS & Hend).
      { split; [|split; [exact Hmu|split; [exact Hms|]]].
        - split; [exact Lv|]. split; [exact Ls|]. split; [exact Hre|].
          split; [intros t Ht; apply Hst; lia|]. split; [lia | exact Hval].
        - split; [|split; [lia | intros q Hq; lia]].
          intros v Hv. destruct (Hcl v Hv) as [(t & Ht & Et) | Hc].
          + destruct (int_cases t (sp - 1)) as [E | E].
            * left. subst t. rewrite <- Et. reflexivity.
            * right; left. exists t. split; [sia | exact Et].
          + right; right; exact Hc. }
      set (r := scan K xlb xlx xly L u k stamp st.[u] vis stk (sp - 1)
                  (Zwf_well_founded 0 (gap L st.[u]))) in *.
      destruct HS as (HC' & Hmu' & Hms' & Hcl' & Hp0 & Hpr).
      eapply IH; [rewrite <- Hz; apply ddec; exact Hs | reflexivity |].
      split; [exact HC'|]. split; [exact Hms'|].
      intros v Hv. destruct (Hcl' v Hv) as [Ev | [Hv2 | Hv3]];
        [ | left; exact Hv2 | right; exact Hv3].
      right. subst v. intros w (t & Ht & Eu & Ew & Ho).
      destruct (E2 t Ht) as (q & Hq & Sq & Iq).
      rewrite Eu in Sq.
      destruct (E4 q Hq) as [Q1 Q2]. rewrite Sq in Q1, Q2.
      destruct (Z_lt_le_dec (φ q) (φ pe)) as [C | C].
      + destruct (Hpr q ltac:(lia)) as [_ P2]. rewrite Iq in P2.
        rewrite <- Ew. apply P2. exact Ho.
      + destruct Hend as [Hend | Hend]; [lia|]. exfalso. apply Hend.
        apply to_Z_inj. pose proof (E3 st.[u] pe ltac:(lia)) as M1.
        pose proof (E3 pe q ltac:(lia)) as M2. rewrite Q2 in M1. rewrite Sq in M2. lia.
    - rewrite <- Bool.not_true_iff_false, ltb_spec in Hs. change (φ 0) with 0%Z in Hs.
      simpl. split; [|split; [exact Lv | split; [exact Ls | exact Hval]]].
      intros v. split; [apply Hre|].
      assert (Gen : forall x y, clos_refl_trans int mstep x y -> vis.[x] = stamp ->
                vis.[y] = stamp).
      { intros x y Hxy. induction Hxy as [x y Hxy | x | x y z' _ IH1 _ IH2].
        - intros Hx. destruct (Hcl x Hx) as [(t & Ht & _) | Hc]; [lia|].
          apply Hc. exact Hxy.
        - auto.
        - auto. }
      intros Hv. apply (Gen s v Hv Hms).
  Qed.
End Search.

(* ------------------------------------------------------------------ *)
(* The interval loop                                                   *)
(* ------------------------------------------------------------------ *)

Lemma count_loop_eq : forall K st xlb xlx xly S L m s d j vis stk acc H,
  count_loop K st xlb xlx xly S L m s d j vis stk acc H =
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
Proof. intros. destruct H. reflexivity. Qed.

Lemma unm_full : forall stamp (vis : array int),
  (forall v, vis.[v] <> stamp) -> unm stamp vis = (φ (PArray.length vis)).
Proof.
  intros stamp vis Hv. unfold unm.
  rewrite (csum_ext _ (fun _ => 1%Z)).
  - rewrite csum_const. pose proof (to_Z_bounded (PArray.length vis)). lia.
  - intros t _. destruct (vis.[of_Z (Z.of_nat t)] =? stamp) eqn:E; [|reflexivity].
    rewrite eqb_spec in E. exfalso. exact (Hv _ E).
Qed.

Definition mstepZ (xla xlb xlx xly : array int) (L : int) (kk : Z) (u w : int) : Prop :=
  exists t, ((φ t) < (φ L))%Z /\ xla.[t] = u /\ xlb.[t] = w /\
    ((φ (xlx.[t])) <= kk <= (φ (xly.[t])))%Z.

Lemma crt_iff : forall (R R' : int -> int -> Prop),
  (forall u w, R u w -> R' u w) ->
  forall x y, clos_refl_trans int R x y -> clos_refl_trans int R' x y.
Proof.
  intros R R' HR x y H. induction H as [x y H | x | x y z _ IH1 _ IH2].
  - apply rt_step. apply HR. exact H.
  - apply rt_refl.
  - eapply rt_trans; eassumption.
Qed.

Definition rangeN (p q : Z) : list N :=
  map N.of_nat (seq (Z.to_nat p) (Z.to_nat (q - p))).

Lemma rangeN_in : forall p q x, (0 <= p)%Z ->
  In x (rangeN p q) <-> (p <= Z.of_N x < q)%Z.
Proof.
  intros p q x Hp. unfold rangeN. rewrite in_map_iff. split.
  - intros (y & Ey & Hy). apply in_seq in Hy. subst x. lia.
  - intros Hx. exists (N.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

Lemma rangeN_nodup : forall p q, NoDup (rangeN p q).
Proof.
  intros p q. unfold rangeN. apply NoDup_map_inv with (f := N.to_nat).
  rewrite map_map. rewrite (map_ext _ (fun x => x)) by (intros; lia).
  rewrite map_id. apply seq_NoDup.
Qed.

Lemma rangeN_length : forall p q, List.length (rangeN p q) = Z.to_nat (q - p).
Proof. intros. unfold rangeN. rewrite length_map, length_seq. reflexivity. Qed.

Section Count.
  Variables (K st xla xlb xlx xly S : array int) (L m N1 s d : int).
  Hypothesis HN1 : ((φ N1) <= 4194303)%Z.
  Hypothesis E1 : forall q, ((φ q) < (φ L))%Z -> exists i, ((φ i) < (φ L))%Z /\
    src_of K.[q] = xla.[i] /\ idx_of K.[q] = i.
  Hypothesis E2 : forall i, ((φ i) < (φ L))%Z -> exists q, ((φ q) < (φ L))%Z /\
    src_of K.[q] = xla.[i] /\ idx_of K.[q] = i.
  Hypothesis E3 : forall q1 q2, ((φ q1) <= (φ q2) < (φ L))%Z ->
    ((φ (src_of K.[q1])) <= (φ (src_of K.[q2])))%Z.
  Hypothesis E4 : forall q, ((φ q) < (φ L))%Z ->
    ((φ (st.[src_of K.[q]])) <= (φ q))%Z /\
    src_of K.[st.[src_of K.[q]]] = src_of K.[q].
  Hypothesis Hlb : forall i, ((φ i) < (φ L))%Z -> ((φ (xlb.[i])) < (φ N1))%Z.
  Hypothesis Hs : ((φ s) < (φ N1))%Z.
  Hypothesis HN1pos : (0 < (φ N1))%Z.
  Hypothesis Hm : (1 <= (φ m) <= 4194303)%Z.
  Hypothesis F1 : sorted_upto S m.
  Hypothesis F2 : forall c, ((φ c) < (φ m))%Z -> (1 <= (φ (S.[c])) <= 1000000001)%Z.
  Hypothesis F4x : forall t, ((φ t) < (φ L))%Z -> exists c, ((φ c) < (φ m))%Z /\ S.[c] = xlx.[t].
  Hypothesis F4y : forall t, ((φ t) < (φ L))%Z -> exists c, ((φ c) < (φ m))%Z /\
    (φ (S.[c])) = ((φ (xly.[t])) + 1)%Z.

  Definition W (x : N) : Prop :=
    clos_refl_trans int (mstepZ xla xlb xlx xly L (Z.of_N x)) s d.

  Definition CLI (j : int) (vis stk : array int) (acc : int) : Prop :=
    (1 <= (φ j) <= (φ m))%Z /\
    (φ (PArray.length vis)) = (φ N1) /\ (φ (PArray.length stk)) = (φ N1) /\
    (forall v, ((φ (vis.[v])) < (φ j))%Z) /\
    ((φ acc) <= (φ (S.[j - 1])) - 1)%Z /\
    exists ks : list N, NoDup ks /\
      (forall x, In x ks <-> (1 <= x)%N /\ (Z.of_N x < (φ (S.[j - 1])))%Z /\ W x) /\
      (φ acc) = Z.of_nat (List.length ks).

  (* no boundary strictly inside [S[j-1], S[j]) *)
  Lemma flat_interval : forall j kk, (1 <= (φ j) < (φ m))%Z ->
    ((φ (S.[j - 1])) <= kk < (φ (S.[j])))%Z ->
    forall u w, mstepZ xla xlb xlx xly L kk u w <->
                mstepZ xla xlb xlx xly L (φ (S.[j - 1])) u w.
  Proof.
    intros j kk Hj Hk u w.
    assert (Ej : (φ (j - 1)) = ((φ j) - 1)%Z) by sia.
    unfold mstepZ. split; intros (t & Ht & E1' & E2' & Hx & Hy);
      exists t; (split; [exact Ht|]); (split; [exact E1'|]); (split; [exact E2'|]);
      destruct (F4x t Ht) as (c1 & Hc1 & Ec1);
      destruct (F4y t Ht) as (c2 & Hc2 & Ec2);
      rewrite <- Ec1 in *;
      (destruct (Z_lt_le_dec (φ c1) (φ j)) as [C1 | C1];
        [pose proof (F1 c1 (j - 1) ltac:(lia)) | pose proof (F1 j c1 ltac:(lia))]);
      (destruct (Z_lt_le_dec (φ c2) (φ j)) as [C2 | C2];
        [pose proof (F1 c2 (j - 1) ltac:(lia)) | pose proof (F1 j c2 ltac:(lia))]);
      lia.
  Qed.

  Lemma count_spec_aux : forall z j vis stk acc H, gap m j = z ->
    CLI j vis stk acc ->
    exists ks : list N, NoDup ks /\
      (forall x, In x ks <-> (1 <= x)%N /\ (Z.of_N x < (φ (S.[m - 1])))%Z /\ W x) /\
      (φ (count_loop K st xlb xlx xly S L m s d j vis stk acc H))
      = Z.of_nat (List.length ks).
  Proof.
    intro z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros j vis stk acc H Hz HI. rewrite count_loop_eq.
    destruct HI as (Hj & Lv & Ls & Hval & Hacc & ks & Nks & Iks & Aks).
    destruct (bdec (j <? m)) as [Hjm | Hjm].
    2:{ rewrite <- Bool.not_true_iff_false, ltb_spec in Hjm.
        assert (j = m) by (apply to_Z_inj; lia). subst j.
        exists ks. split; [exact Nks|]. split; [exact Iks | exact Aks]. }
    pose proof Hjm as Hjm'. rewrite ltb_spec in Hjm'. cbv zeta.
    assert (Ej : (φ (j - 1)) = ((φ j) - 1)%Z) by sia.
    assert (Ej1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    assert (Ej1' : j + 1 - 1 = j) by apply add_sub1.
    set (p := S.[j - 1]). set (q := S.[j]).
    pose proof (F1 (j - 1) j ltac:(lia)) as Hpq. fold p q in Hpq.
    pose proof (F2 (j - 1) ltac:(lia)) as Bp. pose proof (F2 j Hjm') as Bq.
    fold p in Bp. fold q in Bq.
    destruct (p <? q) eqn:Cpq.
    - rewrite ltb_spec in Cpq.
      set (vis1 := vis.[s <- j]). set (stk1 := stk.[0 <- s]).
      assert (Ins : (s <? PArray.length vis) = true) by (rewrite ltb_spec; lia).
      assert (In0 : (0 <? PArray.length stk) = true) by (rewrite ltb_spec; change (φ 0) with 0%Z; lia).
      assert (M1 : forall v, vis1.[v] = j -> v = s).
      { intros v Hv. destruct (int_cases s v) as [E | E]; [symmetry; exact E|].
        unfold vis1 in Hv. rewrite aget_set_other in Hv by (intro F; apply E; rewrite F; reflexivity).
        specialize (Hval v). rewrite Hv in Hval. lia. }
      assert (Ms : vis1.[s] = j) by (apply aget_set_same; exact Ins).
      assert (HD : DInv xla xlb xlx xly L N1 p j s vis1 stk1 1).
      { split; [split|].
        - unfold vis1. rewrite alength_set. exact Lv.
        - split; [unfold stk1; rewrite alength_set; exact Ls|].
          split; [intros v Hv; rewrite (M1 v Hv); apply rt_refl|].
          split.
          { intros t Ht. change (φ 1) with 1%Z in Ht.
            assert (t = 0) by (apply to_Z_inj; change (φ 0) with 0%Z; pose proof (to_Z_bounded t); lia).
            subst t. unfold stk1. rewrite aget_set_same by exact In0. exact Ms. }
          split.
          { unfold vis1. rewrite unm_set; [ | exact Ins | ].
            - rewrite unm_full; [change (φ 1) with 1%Z; lia|].
              intros v Ev. specialize (Hval v). rewrite Ev in Hval. lia.
            - destruct (vis.[s] =? j) eqn:E; [|reflexivity].
              rewrite eqb_spec in E. specialize (Hval s). rewrite E in Hval. lia. }
          { intros v. destruct (int_cases s v) as [E | E].
            - subst v. rewrite Ms. lia.
            - unfold vis1. rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity).
              specialize (Hval v). lia. }
        - split; [exact Ms|]. intros v Hv. left. exists 0. split; [change (φ 0) with 0%Z; change (φ 1) with 1%Z; lia|].
          rewrite (M1 v Hv). unfold stk1. apply aget_set_same. exact In0. }
      destruct (dfs_spec_aux K st xla xlb xlx xly L N1 p j s HN1 E1 E2 E3 E4 Hlb _
                 vis1 stk1 1 (Zwf_well_founded 0 (meas j vis1 1)) eq_refl HD)
        as (R1 & R2 & R3 & R4).
      set (r := dfs K st xlb xlx xly L p j vis1 stk1 1 (Zwf_well_founded 0 (meas j vis1 1))) in *.
      (* W x on the interval is the reachability computed *)
      assert (WI : forall x, ((φ p) <= Z.of_N x < (φ q))%Z ->
                 W x <-> reach xla xlb xlx xly L p s d).
      { intros x Hx. unfold W, reach. split; apply crt_iff; intros u w Huw.
        - apply (flat_interval j (Z.of_N x) ltac:(lia) Hx). exact Huw.
        - apply (flat_interval j (Z.of_N x) ltac:(lia) Hx). exact Huw. }
      destruct ((fst r).[d] =? j) eqn:Rd.
      + rewrite eqb_spec in Rd. apply R1 in Rd.
        eapply IH; [rewrite <- Hz; apply dec_step; exact Hjm | reflexivity |].
        unfold CLI. rewrite Ej1'. fold q.
        split; [lia|]. split; [exact R2|]. split; [exact R3|].
        split; [intros v; specialize (R4 v); lia|].
        split; [sia|].
        exists (ks ++ rangeN (φ p) (φ q)). split; [|split].
        * apply NoDup_app; [exact Nks | apply rangeN_nodup |].
          intros x H1 H2. apply Iks in H1. apply rangeN_in in H2; lia.
        * intros x. rewrite in_app_iff, rangeN_in by lia. rewrite Iks. split.
          { intros [(X1 & X2 & X3) | X]; [split; [lia|]; split; [lia | exact X3]|].
            split; [lia|]. split; [lia|]. apply (WI x X). exact Rd. }
          { intros (X1 & X2 & X3). destruct (Z_lt_le_dec (Z.of_N x) (φ p)) as [C | C].
            - left. split; [exact X1|]. split; [exact C | exact X3].
            - right. lia. }
        * rewrite length_app, rangeN_length. sia.
      + eapply IH; [rewrite <- Hz; apply dec_step; exact Hjm | reflexivity |].
        unfold CLI. rewrite Ej1'. fold q.
        split; [lia|]. split; [exact R2|]. split; [exact R3|].
        split; [intros v; specialize (R4 v); lia|].
        split; [lia|].
        exists ks. split; [exact Nks|]. split; [|exact Aks].
        intros x. rewrite Iks. split.
        { intros (X1 & X2 & X3). split; [exact X1|]. split; [lia | exact X3]. }
        { intros (X1 & X2 & X3). split; [exact X1|]. split; [|exact X3].
          destruct (Z_lt_le_dec (Z.of_N x) (φ p)) as [C | C]; [exact C|].
          exfalso. apply (WI x ltac:(lia)) in X3. apply R1 in X3.
          rewrite X3, eqb_refl in Rd. discriminate. }
    - rewrite <- Bool.not_true_iff_false, ltb_spec in Cpq.
      eapply IH; [rewrite <- Hz; apply dec_step; exact Hjm | reflexivity |].
      unfold CLI. rewrite Ej1'. fold q.
      split; [lia|]. split; [exact Lv|]. split; [exact Ls|].
      split; [intros v; specialize (Hval v); lia|].
      split; [lia|].
      exists ks. split; [exact Nks|]. split; [|exact Aks].
      intros x. rewrite Iks. split; intros (X1 & X2 & X3); (split; [exact X1|]);
        (split; [lia | exact X3]).
  Qed.
End Count.

(* ------------------------------------------------------------------ *)
(* From the math side to the machine side                              *)
(* ------------------------------------------------------------------ *)

Lemma repr_len : forall (x : array int) (a : list N), @repr (array uint) (list N) _ x a ->
  (φ (PArray.length@{Set} x)) = Z.of_nat (List.length a).
Proof. intros x a [Hl _]. symmetry. exact Hl. Qed.

Lemma repr_cell : forall (x : array int) (a : list N), @repr (array uint) (list N) _ x a ->
  forall t : int, ((φ t) < Z.of_nat (List.length a))%Z ->
  Z.to_N (φ (PArray.get@{Set} x t)) = Prelude.get a (Z.to_N (φ t)).
Proof.
  intros x a [Hl Hc] t Ht.
  destruct (Hc (Z.to_nat (φ t)) ltac:(lia)) as (v & Hv & Hr).
  unfold repr, repr_uint in Hr. rewrite of_Z_nat_to in Hr.
  change (Z.to_N (φ (PArray.get@{Set} x t)) = v) in Hr. rewrite Hr.
  unfold Prelude.get. rewrite Z_N_nat. symmetry.
  apply nth_error_nth. exact Hv.
Qed.

Lemma repr_cell_Z : forall (x : array int) (a : list N), @repr (array uint) (list N) _ x a ->
  forall t : int, ((φ t) < Z.of_nat (List.length a))%Z ->
  (φ (PArray.get@{Set} x t)) = Z.of_N (Prelude.get a (Z.to_N (φ t))).
Proof.
  intros x a Hr t Ht. rewrite <- (repr_cell x a Hr t Ht).
  pose proof (to_Z_bounded (PArray.get@{Set} x t)). lia.
Qed.

Lemma repr_N : forall (x : uint) (n : N), repr x n -> (φ x) = Z.of_N n.
Proof. intros x n H. unfold repr, repr_uint in H. pose proof (to_Z_bounded x). lia. Qed.

Section Bridge.
  Variables (la lb lx ly : list N) (xla xlb xlx xly : array int).
  Hypothesis Ra : @repr (array uint) (list N) _ xla la.
  Hypothesis Rb : @repr (array uint) (list N) _ xlb lb.
  Hypothesis Rx : @repr (array uint) (list N) _ xlx lx.
  Hypothesis Ry : @repr (array uint) (list N) _ xly ly.
  Hypothesis Lb : len lb = len la.
  Hypothesis Lx : len lx = len la.
  Hypothesis Ly : len ly = len la.

  Lemma step_iff : forall x (u w : int),
    Prelude.step la lb lx ly x (Z.to_N (φ u)) (Z.to_N (φ w)) <->
    mstepZ xla xlb xlx xly (PArray.length xla) (Z.of_N x) u w.
  Proof.
    pose proof (repr_len _ _ Ra) as HLa. unfold len in *.
    assert (HLb : List.length lb = List.length la) by lia.
    assert (HLx : List.length lx = List.length la) by lia.
    assert (HLy : List.length ly = List.length la) by lia.
    pose proof (alength_bound xla).
    intros x u w. unfold Prelude.step, mstepZ. split.
    - intros (i & Hi & Ea & Eb & Ex). unfold len in Hi.
      set (t := of_Z (Z.of_N i)).
      assert (Et : (φ t) = Z.of_N i) by (unfold t; rewrite of_Z_spec, Z.mod_small; lia).
      assert (Nt : Z.to_N (φ t) = i) by lia.
      exists t. split; [lia|].
      pose proof (repr_cell_Z _ _ Ra t ltac:(lia)) as Ca.
      pose proof (repr_cell_Z _ _ Rb t ltac:(lia)) as Cb.
      pose proof (repr_cell_Z _ _ Rx t ltac:(lia)) as Cx.
      pose proof (repr_cell_Z _ _ Ry t ltac:(lia)) as Cy.
      rewrite Nt in Ca, Cb, Cx, Cy.
      pose proof (to_Z_bounded u). pose proof (to_Z_bounded w).
      split; [apply to_Z_inj; rewrite Ca, Ea; lia|].
      split; [apply to_Z_inj; rewrite Cb, Eb; lia|].
      rewrite Cx, Cy. lia.
    - intros (t & Ht & Ea & Eb & Ex).
      exists (Z.to_N (φ t)).
      pose proof (repr_cell _ _ Ra t ltac:(lia)) as Ca.
      pose proof (repr_cell _ _ Rb t ltac:(lia)) as Cb.
      pose proof (repr_cell_Z _ _ Rx t ltac:(lia)) as Cx.
      pose proof (repr_cell_Z _ _ Ry t ltac:(lia)) as Cy.
      split; [unfold len; lia|]. rewrite <- Ca, <- Cb, Ea, Eb.
      split; [reflexivity|]. split; [reflexivity|]. lia.
  Qed.

  Lemma walks_iff : forall x (u w : int),
    walks la lb lx ly x (Z.to_N (φ u)) (Z.to_N (φ w)) <->
    clos_refl_trans int (mstepZ xla xlb xlx xly (PArray.length xla) (Z.of_N x)) u w.
  Proof.
    intros x u w. unfold walks. split.
    - intros H. apply clos_rt_rt1n_iff in H.
      remember (Z.to_N (φ u)) as a eqn:Ea. remember (Z.to_N (φ w)) as c eqn:Ec.
      revert u w Ea Ec.
      induction H as [a | a y c Hay Hyc IH]; intros u w Ea Ec.
      + assert (u = w) by (apply to_Z_inj; pose proof (to_Z_bounded u);
                           pose proof (to_Z_bounded w); lia).
        subst. apply rt_refl.
      + destruct Hay as (i & Hi & Ea' & Eb' & Ex').
        unfold len in Hi.
        pose proof (repr_len _ _ Ra) as HLa. unfold len in *.
        pose proof (alength_bound xla).
        set (t := of_Z (Z.of_N i)).
        assert (Et : (φ t) = Z.of_N i) by (unfold t; rewrite of_Z_spec, Z.mod_small; lia).
        set (v := xlb.[t]).
        assert (Ev : Z.to_N (φ v) = y).
        { unfold v. rewrite (repr_cell _ _ Rb t ltac:(lia)).
          rewrite <- Eb'. f_equal. lia. }
        eapply rt_trans; [apply rt_step | apply (IH v w); [symmetry; exact Ev | exact Ec]].
        apply step_iff. rewrite <- Ea, Ev. exists i. split; [unfold len; lia|].
        split; [exact Ea'|]. split; [exact Eb' | exact Ex'].
    - intros H. induction H as [u w H | u | u v w _ IH1 _ IH2].
      + apply rt_step. apply step_iff. exact H.
      + apply rt_refl.
      + eapply rt_trans; eassumption.
  Qed.
End Bridge.

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma decode : forall a t : int, ((φ a) < 2 ^ 40)%Z -> ((φ t) < 8192)%Z ->
  src_of ((a << 13) + t) = a /\ idx_of ((a << 13) + t) = t.
Proof.
  intros a t Ha Ht. pose proof (to_Z_bounded a). pose proof (to_Z_bounded t).
  assert (E1 : (φ (a << 13)) = ((φ a) * 8192)%Z).
  { rewrite lsl_spec. change (2 ^ (φ 13))%Z with 8192%Z. apply Z.mod_small. rewrite wB_val. lia. }
  assert (E2 : (φ ((a << 13) + t)) = ((φ a) * 8192 + (φ t))%Z).
  { rewrite add_spec, E1. apply Z.mod_small. rewrite wB_val. lia. }
  assert (E3 : src_of ((a << 13) + t) = a).
  { apply to_Z_inj. unfold src_of. rewrite lsr_spec, E2. change (2 ^ (φ 13))%Z with 8192%Z.
    Z.to_euclidean_division_equations; lia. }
  split; [exact E3|].
  apply to_Z_inj. unfold idx_of. fold (src_of ((a << 13) + t)). rewrite E3.
  rewrite sub_spec, E2, E1. rewrite Z.mod_small; [lia|]. rewrite wB_val. lia.
Qed.

Lemma bnd_cells : forall (xlx xly B : array int) (L c0 c1 : int),
  ((φ L) <= 5000)%Z -> B.[0] = c0 -> B.[1] = c1 ->
  (forall t, ((φ t) < (φ L))%Z -> B.[t + t + 2] = xlx.[t] /\ B.[t + t + 3] = xly.[t] + 1) ->
  forall c, ((φ c) < 2 * (φ L) + 2)%Z ->
  B.[c] = c0 \/ B.[c] = c1 \/
  exists t, ((φ t) < (φ L))%Z /\ (B.[c] = xlx.[t] \/ B.[c] = xly.[t] + 1).
Proof.
  intros xlx xly B L c0 c1 HL H0 H1 Hc c Hcl. pose proof (to_Z_bounded c).
  destruct (Z.eq_dec (φ c) 0) as [E | E].
  { left. replace c with 0 by (apply to_Z_inj; exact (eq_sym E)). exact H0. }
  destruct (Z.eq_dec (φ c) 1) as [E' | E'].
  { right; left. replace c with 1 by (apply to_Z_inj; exact (eq_sym E')). exact H1. }
  right; right. set (t := of_Z (((φ c) - 2) / 2)).
  assert (Et : (φ t) = (((φ c) - 2) / 2)%Z).
  { unfold t. rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val.
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  exists t. split; [rewrite Et; apply Z.div_lt_upper_bound; lia|].
  destruct (Hc t ltac:(rewrite Et; apply Z.div_lt_upper_bound; lia)) as [C2 C3].
  destruct (Z.even (φ c)) eqn:Ev.
  - left. replace c with (t + t + 2); [exact C2|].
    apply to_Z_inj. apply Z.even_spec in Ev. destruct Ev as [h Eh].
    rewrite Eh in Et. sia.
  - right. replace c with (t + t + 3); [exact C3|].
    apply to_Z_inj. assert (Od : Z.odd (φ c) = true) by (rewrite <- Z.negb_even, Ev; reflexivity).
    apply Z.odd_spec in Od. destruct Od as [h Eh].
    rewrite Eh in Et. sia.
Qed.

Theorem securitybadge_core_correct :
  forall (n b s d : N) (la lb lx ly : list N)
         (xn xb xs xd : int) (xla xlb xlx xly : array int),
  valid_input n b s d la lb lx ly ->
  @repr uint N _ xn n -> @repr uint N _ xb b -> @repr uint N _ xs s -> @repr uint N _ xd d ->
  @repr (array uint) (list N) _ xla la -> @repr (array uint) (list N) _ xlb lb ->
  @repr (array uint) (list N) _ xlx lx -> @repr (array uint) (list N) _ xly ly ->
  exists o : N, @repr uint N _ (securitybadge_core xn xb xs xd xla xlb xlx xly) o /\
    securitybadge_spec n b s d la lb lx ly o.
Proof.
  intros n b s d la lb lx ly xn xb xs xd xla xlb xlx xly Hv Rn Rb' Rs Rd Ra Rb Rx Ry.
  pose proof Hv as [VLb VLx VLy Vn Vl Vb Vs Vd Vsd Vlock Vpairs].
  apply repr_N in Rn, Rb', Rs, Rd.
  pose proof (repr_len _ _ Ra) as HLa.
  unfold len in VLb, VLx, VLy, Vl.
  assert (Hlen : forall l : list N, N.of_nat (List.length l) = N.of_nat (List.length la) ->
            List.length l = List.length la) by (intros; lia).
  apply Hlen in VLb, VLx, VLy. clear Hlen.
  unfold securitybadge_core. cbv zeta.
  set (L := PArray.length xla) in *.
  assert (BL : (1 <= (φ L) <= 5000)%Z) by lia.
  assert (CA : forall t, ((φ t) < (φ L))%Z ->
     (1 <= (φ (xla.[t])) <= (φ xn))%Z /\ (1 <= (φ (xlb.[t])) <= (φ xn))%Z /\
     (1 <= (φ (xlx.[t])) <= (φ xb))%Z /\ (1 <= (φ (xly.[t])) <= (φ xb))%Z).
  { intros t Ht. pose proof (to_Z_bounded t).
    destruct (Vlock (Z.to_N (φ t)) ltac:(unfold len; lia)) as (A1 & A2 & _ & A4 & A5 & _).
    rewrite (repr_cell_Z _ _ Ra t ltac:(lia)), (repr_cell_Z _ _ Rb t ltac:(lia)),
      (repr_cell_Z _ _ Rx t ltac:(lia)), (repr_cell_Z _ _ Ry t ltac:(lia)).
    lia. }
  (* the sorted keys *)
  assert (MkL : PArray.length (PArray.make L 0) = L).
  { rewrite alength_make. replace (L <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec. change (φ PArray.max_length) with 4194303%Z. lia. }
  destruct (keys_loop_spec xla L _ 0 (PArray.make L 0) (Zwf_well_founded 0 (gap L 0))
              eq_refl ltac:(change (φ 0) with 0%Z; lia) MkL
              ltac:(intros t Ht; change (φ 0) with 0%Z in Ht; pose proof (to_Z_bounded t); lia))
    as [KL KC].
  set (K0 := keys_loop xla L 0 (PArray.make L 0) (Zwf_well_founded 0 (gap L 0))) in *.
  destruct (msort_spec K0) as (ML & MS & MS1 & MS2).
  set (K := msort K0) in *. rewrite KL in MS, MS1, MS2.
  assert (Dk : forall t, ((φ t) < (φ L))%Z ->
            src_of K0.[t] = xla.[t] /\ idx_of K0.[t] = t).
  { intros t Ht. rewrite (KC t Ht). apply decode; [|lia].
    destruct (CA t Ht) as (C1 & _). lia. }
  assert (E1 : forall q, ((φ q) < (φ L))%Z -> exists i, ((φ i) < (φ L))%Z /\
            src_of K.[q] = xla.[i] /\ idx_of K.[q] = i).
  { intros q Hq. destruct (MS1 q Hq) as (t & Ht & Et). exists t.
    split; [exact Ht|]. rewrite Et. apply Dk. exact Ht. }
  assert (E2 : forall i, ((φ i) < (φ L))%Z -> exists q, ((φ q) < (φ L))%Z /\
            src_of K.[q] = xla.[i] /\ idx_of K.[q] = i).
  { intros i Hi. destruct (MS2 i Hi) as (q & Hq & Eq). exists q.
    split; [exact Hq|]. rewrite <- Eq. apply Dk. exact Hi. }
  assert (E3 : forall q1 q2, ((φ q1) <= (φ q2) < (φ L))%Z ->
            ((φ (src_of K.[q1])) <= (φ (src_of K.[q2])))%Z).
  { intros q1 q2 Hq. unfold src_of. rewrite !lsr_spec. apply Z.div_le_mono; [lia|].
    apply MS. exact Hq. }
  assert (SrcB : forall q, ((φ q) < (φ L))%Z -> (1 <= (φ (src_of K.[q])) <= (φ xn))%Z).
  { intros q Hq. destruct (E1 q Hq) as (i & Hi & Ei & _). rewrite Ei.
    destruct (CA i Hi) as (C1 & _). exact C1. }
  (* the first positions *)
  assert (MkN : (φ (PArray.length (PArray.make (xn + 2) L))) = ((φ xn) + 2)%Z).
  { rewrite alength_make. replace (xn + 2 <=? PArray.max_length) with true; [sia|].
    symmetry. rewrite leb_spec. change (φ PArray.max_length) with 4194303%Z. sia. }
  pose proof (st_loop_spec K L (PArray.make (xn + 2) L)
                ltac:(intros q Hq; rewrite ltb_spec, MkN; specialize (SrcB q Hq); lia)
                _ L (PArray.make (xn + 2) L) (Zwf_well_founded 0 (φ L)) eq_refl
                ltac:(lia) eq_refl ltac:(intros q Hq; lia)) as E4.
  set (st := st_loop K L (PArray.make (xn + 2) L) (Zwf_well_founded 0 (φ L))) in *.
  (* the sorted boundaries *)
  set (m := L + L + 2).
  assert (Em : (φ m) = (2 * (φ L) + 2)%Z) by (unfold m; sia).
  assert (MkM : (φ (PArray.length (PArray.make m 0))) = (φ m)).
  { rewrite alength_make. replace (m <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec. change (φ PArray.max_length) with 4194303%Z. lia. }
  assert (In0 : (0 <? PArray.length (PArray.make m 0)) = true)
    by (rewrite ltb_spec, MkM; change (φ 0) with 0%Z; lia).
  assert (In1 : (1 <? PArray.length (PArray.make m 0).[0 <- 1]) = true)
    by (rewrite alength_set, ltb_spec, MkM; change (φ 1) with 1%Z; lia).
  destruct (bnd_loop_spec xlx xly L 1 (xb + 1) _ 0 (PArray.make m 0).[0 <- 1].[1 <- xb + 1]
              (Zwf_well_founded 0 (gap L 0)) eq_refl ltac:(lia)
              ltac:(change (φ 0) with 0%Z; lia)
              ltac:(rewrite !alength_set, MkM; exact Em)
              ltac:(rewrite aget_set_other by neq_tac;
                    apply aget_set_same; exact In0)
              ltac:(apply aget_set_same; exact In1)
              ltac:(intros t Ht; change (φ 0) with 0%Z in Ht; pose proof (to_Z_bounded t); lia))
    as (BLn & B0 & B1 & BC).
  set (B := bnd_loop xlx xly L 0 (PArray.make m 0).[0 <- 1].[1 <- xb + 1]
              (Zwf_well_founded 0 (gap L 0))) in *.
  destruct (msort_spec B) as (SL & SS & SS1 & SS2).
  set (S := msort B) in *.
  assert (EBm : (φ (PArray.length B)) = (φ m)) by lia.
  assert (Lm : PArray.length B = m) by (apply to_Z_inj; exact EBm).
  rewrite Lm in SS, SS1, SS2.
  assert (Bv : forall c, ((φ c) < (φ m))%Z -> (1 <= (φ (B.[c])) <= (φ xb) + 1)%Z).
  { intros c Hc.
    destruct (bnd_cells xlx xly B L 1 (xb + 1) ltac:(lia) B0 B1 BC c ltac:(lia))
      as [E | [E | (t & Ht & [E | E])]]; rewrite E.
    - change (φ 1) with 1%Z. lia.
    - sia.
    - destruct (CA t Ht) as (_ & _ & C3 & _). lia.
    - destruct (CA t Ht) as (_ & _ & _ & C4). sia. }
  assert (F2 : forall c, ((φ c) < (φ m))%Z -> (1 <= (φ (S.[c])) <= (φ xb) + 1)%Z).
  { intros c Hc. destruct (SS1 c Hc) as (c' & Hc' & E). rewrite E. apply Bv. exact Hc'. }
  assert (F4x : forall t, ((φ t) < (φ L))%Z -> exists c, ((φ c) < (φ m))%Z /\ S.[c] = xlx.[t]).
  { intros t Ht. destruct (BC t Ht) as [C _].
    destruct (SS2 (t + t + 2) ltac:(sia)) as (c & Hc & E). exists c.
    split; [exact Hc|]. rewrite <- E. exact C. }
  assert (F4y : forall t, ((φ t) < (φ L))%Z -> exists c, ((φ c) < (φ m))%Z /\
            (φ (S.[c])) = ((φ (xly.[t])) + 1)%Z).
  { intros t Ht. destruct (BC t Ht) as [_ C].
    destruct (SS2 (t + t + 3) ltac:(sia)) as (c & Hc & E). exists c.
    split; [exact Hc|]. rewrite <- E, C. destruct (CA t Ht) as (_ & _ & _ & C4). sia. }
  assert (S0 : (φ (S.[0])) = 1%Z).
  { destruct (SS2 0 ltac:(change (φ 0) with 0%Z; lia)) as (c & Hc & E).
    rewrite B0 in E. pose proof (SS 0 c ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded c); lia)).
    rewrite <- E in H. change (φ 1) with 1%Z in H.
    pose proof (F2 0 ltac:(change (φ 0) with 0%Z; lia)). lia. }
  assert (Sl : (φ (S.[m - 1])) = ((φ xb) + 1)%Z).
  { destruct (SS2 1 ltac:(change (φ 1) with 1%Z; lia)) as (c & Hc & E).
    rewrite B1 in E. pose proof (SS c (m - 1) ltac:(sia)).
    rewrite <- E in H. pose proof (F2 (m - 1) ltac:(sia)). sia. }
  (* the interval loop *)
  assert (MkN1 : (φ (PArray.length (PArray.make (xn + 1) 0))) = (φ (xn + 1))).
  { rewrite alength_make. replace (xn + 1 <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec. change (φ PArray.max_length) with 4194303%Z. sia. }
  assert (EN1 : (φ (xn + 1)) = ((φ xn) + 1)%Z) by sia.
  assert (HN1 : ((φ (xn + 1)) <= 4194303)%Z) by (rewrite EN1; lia).
  assert (Hlb : forall i, ((φ i) < (φ L))%Z -> ((φ (xlb.[i])) < (φ (xn + 1)))%Z)
    by (intros i Hi; destruct (CA i Hi) as (_ & C2 & _); lia).
  assert (Hxs : ((φ xs) < (φ (xn + 1)))%Z) by (rewrite EN1; lia).
  assert (HN1p : (0 < (φ (xn + 1)))%Z) by (rewrite EN1; lia).
  assert (Hm1 : (1 <= (φ m) <= 4194303)%Z) by lia.
  destruct (count_spec_aux K st xla xlb xlx xly S L m (xn + 1) xs xd
              HN1 E1 E2 E3 E4 Hlb Hxs Hm1 SS
              ltac:(intros c Hc; specialize (F2 c Hc); lia) F4x F4y
              _ 1 (PArray.make (xn + 1) 0) (PArray.make (xn + 1) 0) 0
              (Zwf_well_founded 0 (gap m 1)) eq_refl)
    as (ks & Nks & Iks & Aks).
  { split; [change (φ 1) with 1%Z; lia|]. split; [exact MkN1|]. split; [exact MkN1|].
    split; [intros v; rewrite aget_make; change (φ 0) with 0%Z; change (φ 1) with 1%Z; lia|].
    replace (1 - 1) with 0 by reflexivity. rewrite S0.
    split; [change (φ 0) with 0%Z; lia|].
    exists []. split; [constructor|]. split; [|reflexivity].
    intros x. simpl. lia. }
  exists (N.of_nat (List.length ks)). split.
  - unfold repr, repr_uint. rewrite Aks. lia.
  - exists ks. split; [exact Nks|]. split; [|reflexivity].
    intros x. rewrite Iks. unfold good, W.
    assert (Es : s = Z.to_N (φ xs)) by lia. assert (Ed : d = Z.to_N (φ xd)) by lia.
    rewrite Es, Ed, (walks_iff la lb lx ly xla xlb xlx xly Ra Rb Rx Ry).
    + rewrite Sl. fold L.
      split.
      * intros (X1 & X2 & X3). split; [lia | exact X3].
      * intros (X1 & X3). split; [lia|]. split; [lia | exact X3].
    + unfold len. rewrite VLb. reflexivity.
    + unfold len. rewrite VLx. reflexivity.
    + unfold len. rewrite VLy. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition securitybadge : uint -> uint -> uint -> uint -> array uint ->
  array uint -> array uint -> array uint -> uint := securitybadge_impl.
Elpi complexity securitybadge.

Definition securitybadge_correct :
  forall (n b s d : N) (la lb lx ly : list N)
         (xn xb xs xd : uint) (xla xlb xlx xly : array uint),
  valid_input n b s d la lb lx ly ->
  repr xn n -> repr xb b -> repr xs s -> repr xd d ->
  repr xla la -> repr xlb lb -> repr xlx lx -> repr xly ly ->
  exists o : N, repr (securitybadge xn xb xs xd xla xlb xlx xly) o /\
    securitybadge_spec n b s d la lb lx ly o
  := securitybadge_core_correct.

(* ================================================================== *)
(* Cost                                                                *)
(* ================================================================== *)

(* The cost translations are next to the definitions (Elpi complexity:
   sumbool, bdec, andb, negb, fst, snd, merge, mid_of, pass, sort_loop,
   msort, src_of, idx_of, keys_loop, st_loop, bnd_loop, scan, dfs,
   count_loop, securitybadge_core, securitybadge_impl, securitybadge).
   Each loop's cost twin hides its fix under the layers of its arguments;
   [cost_fix_def] names that fix (merge_F, ..., count_loop_F, plain
   definitions, no *_cost) so that cost_simpl unfolds it once with its
   recursive calls folded.  Loop bounds (by induction on a nat bound of
   the measure): merge <= 100 mgap + 30, pass <= 300 (m - lo) + 30,
   sort_loop <= k (300 m + 100) + 30 when m <= 2^k w, msort <=
   (log2 m + 1)(300 m + 100) + 60, keys_loop / st_loop / bnd_loop <=
   100 L + 30, scan from p <= 200 cnt_from + 40 (the keys of room u from
   p on), dfs <= 300 Pot + 30 with the potential Pot = SW + Uv + 2 unm
   (stack weight: 1 + the keys of each stacked room; Uv: the keys whose
   room is unvisited; unm: the unvisited rooms), each push lowering Pot
   by one and each pop paying for its scan; count_loop <= (m - j)
   ((2 L + 2 N1 + 1) 300 + 300) + 30; securitybadge_core <=
   20000 (L + 1)(n + L + log2 L + 1) + 20000. *)

From elpi Require Import elpi.
From Stdlib Require Import Arith.
From KattisLib Require Import Cost.
Open Scope uint63_scope.
Arguments to_Z : simpl never.

Arguments gap : simpl never.
Arguments mgap : simpl never.
Arguments meas : simpl never.

Ltac gen_bound T X L :=
  let Hc := fresh "Hc" in
  pose proof (L : (@cost T X <= _)%nat) as Hc;
  revert Hc; generalize (@cost T X); intros ? Hc.

Ltac zl := repeat match goal with |- context [@cost ?T ?X] =>
  change (@cost T X) with 0%nat end.

Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; cbv [bdec_cost]; cbn; lia. Qed.
Lemma negb_time b (w : bool_cost stepsCM b) : (cost (negb_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; cbv [negb_cost]; cbn; lia. Qed.
Lemma andb_time b (w : bool_cost stepsCM b) c cC : (cost (extract (andb_cost stepsCM b w) c cC) <= 2)%nat.
Proof. destruct w; cbv [andb_cost]; cbn; lia. Qed.
Lemma src_of_time k kC : (cost (src_of_cost stepsCM k kC) <= 3)%nat.
Proof. cbv [src_of_cost]; cost_simpl. lia. Qed.
Lemma idx_of_time k kC : (cost (idx_of_cost stepsCM k kC) <= 10)%nat.
Proof. cbv [idx_of_cost]; cost_simpl. lia. Qed.
Lemma mid_of_time m mC w wC lo loC : (cost (extract (extract (mid_of_cost stepsCM m mC) w wC) lo loC) <= 10)%nat.
Proof. cbv [mid_of_cost]; cost_simpl. cost_destruct (w <? m - lo); cost_simpl; lia. Qed.

Elpi Command cost_fix_def.
Elpi Accumulate lp:{{
  pred find-fix i:term, o:term.
  find-fix (fix _ _ _ _ as F) F :- !.
  find-fix (fun _ _ B) F :- pi x\ find-fix (B x) F, !.
  find-fix (app L) F :- std.mem L T, find-fix T F, !.
  find-fix (let _ _ V B) F :- (find-fix V F ; pi x\ find-fix (B x) F), !.
  main [str Name, str C] :-
    coq.locate C (const K), coq.env.const K (some (fun _ _ Bo)) _,
    coq.locate "stepsCM" GR, T = Bo (global GR),
    find-fix T F, std.assert-ok! (coq.typecheck F Ty) "ill-typed",
    coq.env.add-const Name F Ty _ _.
}}.
Elpi cost_fix_def "merge_F" "merge_cost".
Elpi cost_fix_def "pass_F" "pass_cost".
Elpi cost_fix_def "sort_loop_F" "sort_loop_cost".
Elpi cost_fix_def "keys_loop_F" "keys_loop_cost".
Elpi cost_fix_def "st_loop_F" "st_loop_cost".
Elpi cost_fix_def "bnd_loop_F" "bnd_loop_cost".
Elpi cost_fix_def "scan_F" "scan_cost".
Elpi cost_fix_def "dfs_F" "dfs_cost".
Elpi cost_fix_def "count_loop_F" "count_loop_cost".

Ltac head_of t := match t with ?f _ => head_of f | _ => t end.

(* the costs of a call of F in the goal, bounded by tac, generalized *)
Ltac gen_call F B tac :=
  match goal with |- context [@cost ?T ?X] =>
    let h := head_of X in constr_eq h F;
    let Hc := fresh "Hc" in
    assert (Hc : (@cost T X <= B)%nat) by tac;
    revert Hc; generalize (@cost T X); intros ? Hc end.

Ltac prim_simpl :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | set_cost _ _ _ => change (@cost T X) with 0%nat
    | extract (set_cost _ _ _) _ _ => change (@cost T X) with 0%nat
    | extract (extract (set_cost _ _ _) _ _) _ _ => change (@cost T X) with 0%nat
    | extract (extract (extract (set_cost _ _ _) _ _) _ _) _ _ => change (@cost T X) with 1%nat
    | make_cost _ _ _ => change (@cost T X) with 0%nat
    | extract (make_cost _ _ _) _ _ => change (@cost T X) with 0%nat
    | extract (extract (make_cost _ _ _) _ _) _ _ => change (@cost T X) with 1%nat
    end end.

Ltac gen_small :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | bdec_cost stepsCM ?b ?w => gen_bound T X (bdec_time b w)
    | negb_cost stepsCM ?b ?w => gen_bound T X (negb_time b w)
    | andb_cost stepsCM ?b ?w => change (@cost T X) with 0%nat
    | extract (andb_cost stepsCM ?b ?w) ?c ?cC => gen_bound T X (andb_time b w c cC)
    | src_of_cost stepsCM ?k ?kC => gen_bound T X (src_of_time k kC)
    | idx_of_cost stepsCM ?k ?kC => gen_bound T X (idx_of_time k kC)
    | mid_of_cost stepsCM ?m ?mC => change (@cost T X) with 0%nat
    | extract (mid_of_cost stepsCM ?m ?mC) ?w ?wC => change (@cost T X) with 0%nat
    | extract (extract (mid_of_cost stepsCM ?m ?mC) ?w ?wC) ?l ?lC => gen_bound T X (mid_of_time m mC w wC l lC)
    end end.

Ltac bdestruct b :=
  let HB := fresh "HB" in
  pose proof (bdec_time b (bool_w b)) as HB;
  cost_destruct (bdec b); cost_simpl.

Lemma mgap_nonneg mid hi i j : (0 <= mgap mid hi i j)%Z.
Proof. unfold mgap. lia. Qed.
Lemma mgap_i mid hi i j : (i <? mid) = true -> (Z.to_nat (mgap mid hi (i + 1) j) < Z.to_nat (mgap mid hi i j))%nat.
Proof. intros H. pose proof (mdec_i mid hi i j H) as X. unfold Zwf in X. pose proof (mgap_nonneg mid hi (i + 1) j). pose proof (mgap_nonneg mid hi i (j + 1)). lia. Qed.
Lemma mgap_j mid hi i j : (j <? hi) = true -> (Z.to_nat (mgap mid hi i (j + 1)) < Z.to_nat (mgap mid hi i j))%nat.
Proof. intros H. pose proof (mdec_j mid hi i j H) as X. unfold Zwf in X. pose proof (mgap_nonneg mid hi (i + 1) j). pose proof (mgap_nonneg mid hi i (j + 1)). lia. Qed.

Lemma merge_F_time : forall n src srcC mid midC hi hiC i iC j jC k kC dst dstC H HC,
  (Z.to_nat (mgap mid hi i j) <= n)%nat ->
  (cost (merge_F src srcC mid midC hi hiC i iC j jC k kC dst dstC H HC) <= n * 100 + 30)%nat.
Proof.
  induction n as [|n IH]; intros src srcC mid midC hi hiC i iC j jC k kC dst dstC [g] HC Hn.
  all: cost_simpl.
  all: bdestruct (i <? mid).
  all: bdestruct (j <? hi).
  all: try (pose proof (mgap_i mid hi i j e); lia).
  all: try (pose proof (mgap_j mid hi i j e); lia).
  all: try (pose proof (mgap_j mid hi i j e0); lia).
  all: try (cost_destruct (src.[i] <=? src.[j]); cost_simpl).
  all: prim_simpl; gen_small.
  all: try (gen_call merge_F (n * 100 + 30)%nat ltac:(apply IH;
     first [pose proof (mgap_i mid hi i j e); lia | pose proof (mgap_j mid hi i j e0); lia | pose proof (mgap_j mid hi i j e); lia])).
  all: lia.
Qed.

Lemma merge_time src srcC mid midC hi hiC i iC j jC k kC dst dstC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (merge_cost stepsCM src srcC) mid midC) hi hiC) i iC) j jC) k kC) dst dstC) H HC) <= Z.to_nat (mgap mid hi i j) * 100 + 30)%nat.
Proof. exact (merge_F_time _ src srcC mid midC hi hiC i iC j jC k kC dst dstC H HC (le_n _)). Qed.

Ltac gen_merge := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (extract (extract (merge_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC) ?h ?hC =>
    gen_bound T X (merge_time a aC b bC c cC d dC e eC f fC g gC h hC) end end.

Lemma gap_nonneg_to m lo : (φ lo <= φ m)%Z -> Z.to_nat (gap m lo) = Z.to_nat (φ m - φ lo).
Proof. intros. unfold gap. reflexivity. Qed.

Lemma gap_pos m lo : (lo <? m) = true -> (0 < Z.to_nat (gap m lo))%nat.
Proof. intros H. rewrite ltb_spec in H. unfold gap. lia. Qed.

Lemma gap_wf_le a b n : Zwf 0 a b -> (Z.to_nat b <= S n)%nat -> (Z.to_nat a <= n)%nat.
Proof. unfold Zwf. lia. Qed.

Lemma pass_arith m w lo : (lo <? m) = true -> (0 <? w) = true ->
  (Z.to_nat (mgap (mid_of m w lo) (mid_of m w (mid_of m w lo)) lo (mid_of m w lo))
   + Z.to_nat (gap m (mid_of m w (mid_of m w lo))) = Z.to_nat (gap m lo))%nat /\
  (1 <= Z.to_nat (mgap (mid_of m w lo) (mid_of m w (mid_of m w lo)) lo (mid_of m w lo)))%nat.
Proof.
  intros H1 H2. rewrite ltb_spec in H1, H2. change (φ 0) with 0%Z in H2.
  pose proof (mid_of_val m w lo ltac:(lia)) as E1.
  pose proof (mid_of_val m w (mid_of m w lo) ltac:(lia)) as E2.
  unfold mgap, gap. rewrite E2, E1. rewrite E1 in E2. clear E1 E2.
  pose proof (to_Z_bounded lo). pose proof (to_Z_bounded w). pose proof (to_Z_bounded m). lia.
Qed.

Lemma pass_F_time : forall n src srcC m mC w wC lo loC dst dstC Hw HwC H HC,
  (Z.to_nat (gap m lo) <= n)%nat ->
  (cost (pass_F src srcC m mC w wC lo loC dst dstC Hw HwC H HC) <= Z.to_nat (gap m lo) * 300 + 30)%nat.
Proof.
  induction n as [|n IH]; intros src srcC m mC w wC lo loC dst dstC Hw HwC [g] HC Hn.
  all: cost_simpl.
  all: bdestruct (lo <? m).
  all: try (exfalso; pose proof (gap_pos m lo e); lia).
  all: try lia.
  all: zl; gen_small; gen_merge.
  all: match goal with |- context [@cost ?T (pass_F _ _ _ _ _ _ ?hi _ _ _ _ _ _ _)] =>
    gen_call pass_F (Z.to_nat (gap m hi) * 300 + 30)%nat
      ltac:(apply IH; exact (gap_wf_le _ _ _ (pdec m w lo Hw e) Hn)) end.
  all: destruct (pass_arith m w lo e Hw). 
  all: lia.
Qed.

Definition zn (x : int) : nat := Z.to_nat (φ x).
Arguments zn : simpl never.

Ltac gen_pass := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (extract (pass_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC =>
    gen_bound T X (pass_F_time _ a aC b bC c cC d dC e eC f fC g gC (le_n _)) end end.

Lemma gap0 m : Z.to_nat (gap m 0) = zn m.
Proof. unfold gap, zn. change (φ 0) with 0%Z. rewrite Z.sub_0_r. reflexivity. Qed.

Lemma sort_arith m w k : (m <=? PArray.max_length) = true -> (w <? m) = true ->
  (zn m <= 2 ^ S k * zn w)%nat -> (zn m <= 2 ^ k * zn (w + w))%nat.
Proof.
  intros Hm Hw H. unfold zn in *. rewrite leb_spec in Hm. rewrite ltb_spec in Hw.
  change (φ PArray.max_length) with 4194303%Z in Hm.
  assert (E : φ (w + w) = (2 * φ w)%Z).
  { rewrite add_spec. rewrite Z.mod_small; [lia|]. pose proof (to_Z_bounded w). lia. }
  rewrite E. rewrite Nat.pow_succ_r' in H. pose proof (to_Z_bounded w).
  replace (Z.to_nat (2 * φ w)) with (2 * Z.to_nat (φ w))%nat by lia. lia.
Qed.

Lemma sort_contra m w : (w <? m) = true -> (zn m <= 2 ^ 0 * zn w)%nat -> False.
Proof. intros H1 H2. unfold zn in *. rewrite ltb_spec in H1. simpl in H2. lia. Qed.

Lemma sort_loop_F_time : forall k m mC w wC src srcC dst dstC Hm HmC Hw HwC H HC,
  (zn m <= 2 ^ k * zn w)%nat ->
  (cost (sort_loop_F m mC w wC src srcC dst dstC Hm HmC Hw HwC H HC) <= k * (zn m * 300 + 100) + 30)%nat.
Proof.
  induction k as [|k IH]; intros m mC w wC src srcC dst dstC Hm HmC Hw HwC [g] HC Hk.
  all: cost_simpl.
  all: bdestruct (w <? m).
  all: try (exfalso; exact (sort_contra m w e Hk)).
  all: try lia.
  all: zl; gen_small; gen_pass.
  all: rewrite ?gap0 in *.
  all: gen_call sort_loop_F (k * (zn m * 300 + 100) + 30)%nat
      ltac:(apply IH; exact (sort_arith m w k Hm e Hk)).
  all: lia.
Qed.

Lemma log2_cover m : (m <= 2 ^ (Nat.log2 m + 1) * 1)%nat.
Proof.
  rewrite Nat.mul_1_r. destruct m as [|m]; [simpl; lia|].
  pose proof (Nat.log2_spec (S m) ltac:(lia)) as [_ H]. rewrite Nat.add_1_r. lia.
Qed.

Lemma msort_time a aC :
  (cost (msort_cost stepsCM a aC) <= (Nat.log2 (zn (PArray.length a)) + 1) * (zn (PArray.length a) * 300 + 100) + 60)%nat.
Proof.
  unfold msort_cost. cost_simpl.
  zl. prim_simpl.
  match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (extract (sort_loop_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC =>
    gen_bound T X (sort_loop_F_time (Nat.log2 (zn a) + 1) a aC b bC c cC d dC e eC f fC g gC (log2_cover (zn a))) end end.
  lia.
Qed.

Fixpoint fsum (f : Z -> Z) (a : Z) (c : nat) : Z :=
  match c with
  | O => 0%Z
  | S c' => (f a + fsum f (a + 1) c')%Z
  end.

Lemma fsum_nonneg f a c : (forall x, 0 <= f x)%Z -> (0 <= fsum f a c)%Z.
Proof. intros Hf. revert a. induction c as [|c IH]; intros a; simpl; [lia|]. specialize (Hf a). specialize (IH (a + 1)%Z). lia. Qed.

Lemma fsum_le1 f a c : (forall x, f x <= 1)%Z -> (fsum f a c <= Z.of_nat c)%Z.
Proof. intros Hf. revert a. induction c as [|c IH]; intros a; simpl; [lia|]. specialize (Hf a). specialize (IH (a + 1)%Z). lia. Qed.

Lemma fsum_ext f g a c : (forall x, (a <= x < a + Z.of_nat c)%Z -> f x = g x) -> fsum f a c = fsum g a c.
Proof.
  revert a. induction c as [|c IH]; intros a E; simpl; [reflexivity|].
  rewrite (E a) by lia. rewrite (IH (a + 1)%Z) by (intros x Hx; apply E; lia). reflexivity.
Qed.

Lemma fsum_sub f g h a c : (forall x, f x = g x - h x)%Z -> fsum f a c = (fsum g a c - fsum h a c)%Z.
Proof. intros E. revert a. induction c as [|c IH]; intros a; simpl; [reflexivity|]. rewrite E, IH. lia. Qed.

Lemma fsum_last f a c : fsum f a (S c) = (fsum f a c + f (a + Z.of_nat c))%Z.
Proof.
  revert a. induction c as [|c IH]; intros a.
  - simpl. rewrite !Z.add_0_r. lia.
  - remember (S c) as c'. simpl. subst c'. rewrite IH.
    replace (a + Z.of_nat (S c))%Z with (a + 1 + Z.of_nat c)%Z by lia. simpl. lia.
Qed.

Lemma fsum_app f a c1 c2 : fsum f a (c1 + c2) = (fsum f a c1 + fsum f (a + Z.of_nat c1) c2)%Z.
Proof.
  revert a. induction c1 as [|c1 IH]; intros a; simpl.
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH. replace (a + 1 + Z.of_nat c1)%Z with (a + Z.pos (Pos.of_succ_nat c1))%Z by lia. lia.
Qed.

Definition cnt_from (K : array int) (L u p : int) : Z :=
  fsum (fun q => if src_of K.[of_Z q] =? u then 1%Z else 0%Z) (φ p) (Z.to_nat (φ L - φ p)).
Definition cnt (K : array int) (L u : int) : Z := cnt_from K L u 0.
Definition Uv (K : array int) (L stamp : int) (vis : array int) : Z :=
  fsum (fun q => if vis.[src_of K.[of_Z q]] =? stamp then 0%Z else 1%Z) 0 (Z.to_nat (φ L)).
Definition SW (K : array int) (L : int) (stk : array int) (sp : int) : Z :=
  fsum (fun i => 1 + cnt K L stk.[of_Z i])%Z 0 (Z.to_nat (φ sp)).
Definition Pot (K : array int) (L stamp : int) (vis stk : array int) (sp : int) : Z :=
  (SW K L stk sp + Uv K L stamp vis + 2 * unm stamp vis)%Z.

Lemma cnt_from_nonneg K L u p : (0 <= cnt_from K L u p)%Z.
Proof. apply fsum_nonneg. intros x. destruct (_ =? _); lia. Qed.

Lemma cnt_nonneg K L u : (0 <= cnt K L u)%Z.
Proof. apply cnt_from_nonneg. Qed.

Lemma cnt_le K L u : (cnt K L u <= φ L)%Z.
Proof.
  unfold cnt, cnt_from. change (φ 0) with 0%Z. rewrite Z.sub_0_r.
  eapply Z.le_trans; [apply fsum_le1; intros x; destruct (_ =? _); lia|].
  pose proof (to_Z_bounded L). lia.
Qed.

Lemma cnt_from_le K L u p : (cnt_from K L u p <= cnt K L u)%Z.
Proof.
  unfold cnt, cnt_from. change (φ 0) with 0%Z. rewrite Z.sub_0_r.
  pose proof (to_Z_bounded L). pose proof (to_Z_bounded p).
  destruct (Z_le_gt_dec (φ p) (φ L)) as [Hle | Hgt].
  - replace (Z.to_nat (φ L)) with (Z.to_nat (φ p) + Z.to_nat (φ L - φ p))%nat by lia.
    rewrite fsum_app. rewrite Z2Nat.id by lia. rewrite ?Z.add_0_l.
    match goal with |- (_ <= ?A + _)%Z => assert (0 <= A)%Z by (apply fsum_nonneg; intros x; destruct (_ =? _); lia) end.
    lia.
  - replace (Z.to_nat (φ L - φ p)) with O by lia. simpl.
    apply fsum_nonneg; intros x; destruct (_ =? _); lia.
Qed.

Lemma succ_val (p L : int) : (φ p < φ L)%Z -> φ (p + 1) = (φ p + 1)%Z.
Proof.
  intros H. rewrite add_spec. change (φ 1) with 1%Z. rewrite Z.mod_small; [lia|].
  pose proof (to_Z_bounded L). pose proof (to_Z_bounded p). lia.
Qed.

Lemma cnt_from_step K L u p : (φ p < φ L)%Z ->
  cnt_from K L u p = ((if (src_of K.[p] =? u)%uint63 then 1 else 0) + cnt_from K L u (p + 1))%Z.
Proof.
  intros H. unfold cnt_from. rewrite (succ_val p L H).
  replace (Z.to_nat (φ L - φ p)) with (S (Z.to_nat (φ L - (φ p + 1)))) by lia.
  simpl. rewrite of_to_Z. reflexivity.
Qed.

Lemma Uv_nonneg K L stamp vis : (0 <= Uv K L stamp vis)%Z.
Proof. apply fsum_nonneg. intros x. destruct (_ =? _); lia. Qed.

Lemma Uv_le K L stamp vis : (Uv K L stamp vis <= φ L)%Z.
Proof.
  unfold Uv. eapply Z.le_trans; [apply fsum_le1; intros x; destruct (_ =? _); lia|].
  pose proof (to_Z_bounded L). lia.
Qed.

Lemma Uv_set K L stamp (vis : array int) v :
  (v <? PArray.length vis) = true -> (vis.[v] =? stamp) = false ->
  Uv K L stamp vis.[v <- stamp] = (Uv K L stamp vis - cnt K L v)%Z.
Proof.
  intros Hv Hs. unfold Uv, cnt, cnt_from. change (φ 0) with 0%Z. rewrite Z.sub_0_r.
  apply fsum_sub. intros x. destruct (int_cases (src_of K.[of_Z x]) v) as [E | E].
  - rewrite E, aget_set_same by exact Hv. rewrite eqb_refl, Hs, eqb_refl. lia.
  - rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity).
    replace (src_of K.[of_Z x] =? v) with false.
    + lia.
    + symmetry. rewrite <- Bool.not_true_iff_false, eqb_spec. intro F. apply E. rewrite F. reflexivity.
Qed.

Lemma SW_nonneg K L stk sp : (0 <= SW K L stk sp)%Z.
Proof. apply fsum_nonneg. intros x. pose proof (cnt_nonneg K L stk.[of_Z x]). lia. Qed.

Lemma SW_push K L (stk : array int) sp v :
  (sp <? PArray.length stk) = true ->
  SW K L stk.[sp <- v] (sp + 1) = (SW K L stk sp + 1 + cnt K L v)%Z.
Proof.
  intros Hsp. pose proof Hsp as Hsp'. rewrite ltb_spec in Hsp'. unfold SW.
  rewrite (succ_val sp (PArray.length stk) Hsp').
  pose proof (to_Z_bounded sp).
  replace (Z.to_nat (φ sp + 1)) with (S (Z.to_nat (φ sp))) by lia.
  rewrite fsum_last. rewrite Z2Nat.id by lia. rewrite ?Z.add_0_l.
  rewrite of_to_Z, aget_set_same by exact Hsp.
  rewrite (fsum_ext _ (fun i => 1 + cnt K L stk.[of_Z i])%Z); [lia|].
  intros x Hx. rewrite aget_set_other; [reflexivity|].
  intros F. rewrite F in Hx. rewrite of_Z_spec in Hx. rewrite Z.mod_small in Hx; lia.
Qed.

Lemma SW_pop K L (stk : array int) sp :
  (0 <? sp) = true ->
  SW K L stk sp = (SW K L stk (sp - 1) + 1 + cnt K L stk.[sp - 1])%Z.
Proof.
  intros H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H. unfold SW.
  assert (E : φ (sp - 1) = (φ sp - 1)%Z).
  { rewrite sub_spec. change (φ 1) with 1%Z. rewrite Z.mod_small; [lia|]. pose proof (to_Z_bounded sp). lia. }
  rewrite E. replace (Z.to_nat (φ sp)) with (S (Z.to_nat (φ sp - 1))) by lia.
  rewrite fsum_last. rewrite Z2Nat.id by lia. rewrite ?Z.add_0_l.
  replace (of_Z (φ sp - 1)) with (sp - 1); [lia|].
  rewrite <- E. rewrite of_to_Z. reflexivity.
Qed.

Lemma csum_le1 f c : (forall t, f t <= 1)%Z -> (csum f c <= Z.of_nat c)%Z.
Proof. intros H. induction c as [|c IH]; cbn [csum]; [simpl; lia|rewrite Nat2Z.inj_succ]. specialize (H c). lia. Qed.

Lemma csum_le_minus f c v : (v < c)%nat -> f v = 0%Z -> (forall t, f t <= 1)%Z -> (csum f c <= Z.of_nat c - 1)%Z.
Proof.
  intros Hv Hf H1. induction c as [|c IH]; [lia|]. cbn [csum]. rewrite Nat2Z.inj_succ.
  destruct (Nat.eq_dec c v) as [-> | Ne].
  - rewrite Hf. pose proof (csum_le1 f v H1). lia.
  - pose proof (H1 c). specialize (IH ltac:(lia)). lia.
Qed.

Lemma unm_le stamp vis : (unm stamp vis <= φ (PArray.length vis))%Z.
Proof.
  unfold unm. eapply Z.le_trans; [apply csum_le1; intros t; destruct (_ =? _); lia|].
  pose proof (to_Z_bounded (PArray.length vis)). lia.
Qed.

Lemma unm_set_le stamp (vis : array int) v : (v <? PArray.length vis) = true ->
  (unm stamp vis.[v <- stamp] <= φ (PArray.length vis) - 1)%Z.
Proof.
  intros Hv. unfold unm. rewrite alength_set.
  pose proof Hv as Hv'. rewrite ltb_spec in Hv'. pose proof (to_Z_bounded v).
  eapply Z.le_trans; [apply (csum_le_minus _ _ (Z.to_nat (φ v)))|].
  - lia.
  - cbv beta. rewrite of_Z_nat_to, aget_set_same, eqb_refl by exact Hv. reflexivity.
  - intros t. destruct (_ =? _); lia.
  - pose proof (to_Z_bounded (PArray.length vis)). lia.
Qed.

Lemma scan_pot_aux : forall K xlb xlx xly L u k stamp z p vis stk sp H,
  gap L p = z ->
  (φ sp + unm stamp vis <= φ (PArray.length stk))%Z ->
  let r := scan K xlb xlx xly L u k stamp p vis stk sp H in
  (φ (snd r) + unm stamp (fst (fst r)) <= φ (PArray.length (snd (fst r))))%Z /\
  PArray.length (snd (fst r)) = PArray.length stk /\
  PArray.length (fst (fst r)) = PArray.length vis /\
  (Pot K L stamp (fst (fst r)) (snd (fst r)) (snd r) <= Pot K L stamp vis stk sp)%Z.
Proof.
  intros K xlb xlx xly L u k stamp z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros p vis stk sp H Hz Hinv. cbv zeta.
  rewrite scan_eq. destruct (bdec (p <? L)) as [Hp | Hp]; [ | simpl; lia].
  cbv zeta. destruct (src_of K.[p] =? u); [ | simpl; lia].
  destruct ((xlx.[idx_of K.[p]] <=? k) && (k <=? xly.[idx_of K.[p]])
            && negb (vis.[xlb.[idx_of K.[p]]] =? stamp)
            && (xlb.[idx_of K.[p]] <? PArray.length vis)) eqn:E.
  - rewrite !Bool.andb_true_iff, Bool.negb_true_iff in E.
    destruct E as [[[_ _] E1] E2].
    set (v := xlb.[idx_of K.[p]]) in *.
    pose proof (unm_pos stamp vis v E2 E1) as Up.
    pose proof (unm_set stamp vis v E2 E1) as Us.
    pose proof (to_Z_bounded sp).
    assert (Insp : (sp <? PArray.length stk) = true) by (rewrite ltb_spec; lia).
    pose proof Insp as Insp'. rewrite ltb_spec in Insp'.
    pose proof (succ_val sp (PArray.length stk) Insp') as Esp.
    assert (Hinv' : (φ (sp + 1) + unm stamp vis.[v <- stamp] <= φ (PArray.length stk.[sp <- v]))%Z).
    { rewrite alength_set, Esp, Us. lia. }
    pose proof (IH (gap L (p + 1)) ltac:(rewrite <- Hz; apply (dec_step L p Hp)) (p + 1)
      vis.[v <- stamp] stk.[sp <- v] (sp + 1) (Acc_inv H (dec_step L p Hp)) eq_refl Hinv')
      as (I1 & I2 & I3 & I4).
    rewrite alength_set in I2, I3.
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
    eapply Z.le_trans; [exact I4|].
    unfold Pot. rewrite SW_push by exact Insp. rewrite Uv_set by assumption. rewrite Us. lia.
  - exact (IH (gap L (p + 1)) ltac:(rewrite <- Hz; apply (dec_step L p Hp)) (p + 1)
      vis stk sp (Acc_inv H (dec_step L p Hp)) eq_refl Hinv).
Qed.

Lemma scan_pot : forall K xlb xlx xly L u k stamp p vis stk sp H,
  (φ sp + unm stamp vis <= φ (PArray.length stk))%Z ->
  let r := scan K xlb xlx xly L u k stamp p vis stk sp H in
  (φ (snd r) + unm stamp (fst (fst r)) <= φ (PArray.length (snd (fst r))))%Z /\
  PArray.length (snd (fst r)) = PArray.length stk /\
  PArray.length (fst (fst r)) = PArray.length vis /\
  (Pot K L stamp (fst (fst r)) (snd (fst r)) (snd r) <= Pot K L stamp vis stk sp)%Z.
Proof. intros. eapply scan_pot_aux; [reflexivity | assumption]. Qed.

Lemma scan_len_aux : forall K xlb xlx xly L u k stamp z p vis stk sp H,
  gap L p = z ->
  let r := scan K xlb xlx xly L u k stamp p vis stk sp H in
  PArray.length (snd (fst r)) = PArray.length stk /\
  PArray.length (fst (fst r)) = PArray.length vis.
Proof.
  intros K xlb xlx xly L u k stamp z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros p vis stk sp H Hz. cbv zeta.
  rewrite scan_eq. destruct (bdec (p <? L)) as [Hp | Hp]; [ | simpl; auto].
  cbv zeta. destruct (src_of K.[p] =? u); [ | simpl; auto].
  destruct (_ && _).
  - pose proof (IH (gap L (p + 1)) ltac:(rewrite <- Hz; apply (dec_step L p Hp)) (p + 1)
      vis.[xlb.[idx_of K.[p]] <- stamp] stk.[sp <- xlb.[idx_of K.[p]]] (sp + 1) (Acc_inv H (dec_step L p Hp)) eq_refl)
      as (I1 & I2).
    rewrite alength_set in I1, I2. auto.
  - exact (IH (gap L (p + 1)) ltac:(rewrite <- Hz; apply (dec_step L p Hp)) (p + 1)
      vis stk sp (Acc_inv H (dec_step L p Hp)) eq_refl).
Qed.

Lemma dfs_len_aux : forall K st xlb xlx xly L k stamp z vis stk sp H,
  meas stamp vis sp = z ->
  let r := dfs K st xlb xlx xly L k stamp vis stk sp H in
  PArray.length (fst r) = PArray.length vis /\ PArray.length (snd r) = PArray.length stk.
Proof.
  intros K st xlb xlx xly L k stamp z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros vis stk sp H Hz. cbv zeta. rewrite dfs_eq.
  destruct (bdec (0 <? sp)) as [Hs | Hs]; [ | simpl; auto].
  cbv zeta.
  edestruct (scan_len_aux K xlb xlx xly L stk.[sp - 1] k stamp _ st.[stk.[sp - 1]] vis stk (sp - 1)
     (Zwf_well_founded 0 (gap L st.[stk.[sp - 1]])) eq_refl) as [S1 S2].
  pose proof (IH _ ltac:(rewrite <- Hz; apply (ddec K st xlb xlx xly L k stamp vis stk sp Hs))
    _ (snd (fst (scan K xlb xlx xly L stk.[sp - 1] k stamp st.[stk.[sp - 1]] vis stk (sp - 1)
     (Zwf_well_founded 0 (gap L st.[stk.[sp - 1]]))))) _ (Acc_inv H (ddec K st xlb xlx xly L k stamp vis stk sp Hs)) eq_refl) as [D1 D2].
  rewrite D1, D2, S1, S2. auto.
Qed.

Lemma dfs_len : forall K st xlb xlx xly L k stamp vis stk sp H,
  let r := dfs K st xlb xlx xly L k stamp vis stk sp H in
  PArray.length (fst r) = PArray.length vis /\ PArray.length (snd r) = PArray.length stk.
Proof. intros. eapply dfs_len_aux. reflexivity. Qed.

Lemma gap_succ_eq L i : (i <? L) = true -> (Z.to_nat (gap L (i + 1)) + 1 = Z.to_nat (gap L i))%nat.
Proof.
  intros H. rewrite ltb_spec in H. unfold gap.
  assert (E : φ (i + 1) = (φ i + 1)%Z).
  { rewrite add_spec. change (φ 1) with 1%Z. rewrite Z.mod_small; [lia|].
    pose proof (to_Z_bounded L). pose proof (to_Z_bounded i). lia. }
  rewrite E. lia.
Qed.

Lemma keys_loop_F_time : forall n xla xlaC L LC i iC K KC H HC,
  (Z.to_nat (gap L i) <= n)%nat ->
  (cost (keys_loop_F xla xlaC L LC i iC K KC H HC) <= Z.to_nat (gap L i) * 100 + 30)%nat.
Proof.
  induction n as [|n IH]; intros xla xlaC L LC i iC K KC [g] HC Hn.
  all: cost_simpl.
  all: bdestruct (i <? L).
  all: try (exfalso; pose proof (gap_pos L i e); lia).
  all: try lia.
  all: zl; prim_simpl; gen_small.
  all: gen_call keys_loop_F (Z.to_nat (gap L (i + 1)) * 100 + 30)%nat
      ltac:(apply IH; exact (gap_wf_le _ _ _ (dec_step L i e) Hn)).
  all: pose proof (gap_succ_eq L i e).
  all: lia.
Qed.

Lemma zn_pred p : (0 <? p) = true -> (zn (p - 1) + 1 = zn p)%nat.
Proof.
  intros H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H. unfold zn.
  rewrite sub_spec. change (φ 1) with 1%Z. rewrite Z.mod_small; [lia|].
  pose proof (to_Z_bounded p). lia.
Qed.

Lemma st_loop_F_time : forall n K KC p pC st stC H HC,
  (zn p <= n)%nat ->
  (cost (st_loop_F K KC p pC st stC H HC) <= zn p * 100 + 30)%nat.
Proof.
  induction n as [|n IH]; intros K KC p pC st stC [g] HC Hn.
  all: cost_simpl.
  all: bdestruct (0 <? p).
  all: try (exfalso; pose proof (zn_pred p e); lia).
  all: try lia.
  all: zl; prim_simpl; gen_small.
  all: gen_call st_loop_F (zn (p - 1) * 100 + 30)%nat
      ltac:(apply IH; pose proof (zn_pred p e); lia).
  all: pose proof (zn_pred p e).
  all: lia.
Qed.

Lemma bnd_loop_F_time : forall n xlx xlxC xly xlyC L LC i iC B BC H HC,
  (Z.to_nat (gap L i) <= n)%nat ->
  (cost (bnd_loop_F xlx xlxC xly xlyC L LC i iC B BC H HC) <= Z.to_nat (gap L i) * 100 + 30)%nat.
Proof.
  induction n as [|n IH]; intros xlx xlxC xly xlyC L LC i iC B BC [g] HC Hn.
  all: cost_simpl.
  all: bdestruct (i <? L).
  all: try (exfalso; pose proof (gap_pos L i e); lia).
  all: try lia.
  all: zl; prim_simpl; gen_small.
  all: gen_call bnd_loop_F (Z.to_nat (gap L (i + 1)) * 100 + 30)%nat
      ltac:(apply IH; exact (gap_wf_le _ _ _ (dec_step L i e) Hn)).
  all: pose proof (gap_succ_eq L i e).
  all: lia.
Qed.

Arguments cnt_from : simpl never.
Arguments cnt : simpl never.
Arguments Uv : simpl never.
Arguments SW : simpl never.
Arguments Pot : simpl never.
Arguments unm : simpl never.
Arguments src_of : simpl never.
Arguments idx_of : simpl never.

Lemma scan_F_time : forall n K KC xlb xlbC xlx xlxC xly xlyC L LC u uC k kC stamp stampC p pC vis visC stk stkC sp spC H HC,
  (Z.to_nat (gap L p) <= n)%nat ->
  (cost (scan_F K KC xlb xlbC xlx xlxC xly xlyC L LC u uC k kC stamp stampC p pC vis visC stk stkC sp spC H HC)
    <= Z.to_nat (cnt_from K L u p) * 200 + 40)%nat.
Proof.
  induction n as [|n IH]; intros K KC xlb xlbC xlx xlxC xly xlyC L LC u uC k kC stamp stampC p pC vis visC stk stkC sp spC [g] HC Hn.
  all: cost_simpl.
  all: bdestruct (p <? L).
  all: try (exfalso; pose proof (gap_pos L p e); lia).
  all: try lia.
  all: zl; prim_simpl; gen_small.
  all: cost_destruct_eqn (src_of K.[p] =? u) Esrc; cost_simpl.
  all: zl; prim_simpl; gen_small.
  all: try (rewrite ltb_spec in e; pose proof (cnt_from_nonneg K L u p); lia).
  all: try (cost_destruct_eqn ((xlx.[idx_of K.[p]] <=? k) && (k <=? xly.[idx_of K.[p]]) && negb (vis.[xlb.[idx_of K.[p]]] =? stamp) && (xlb.[idx_of K.[p]] <? PArray.length vis)) Econd; cost_simpl).
  all: zl; prim_simpl; gen_small.
  all: try (gen_call scan_F (Z.to_nat (cnt_from K L u (p + 1)) * 200 + 40)%nat
      ltac:(apply IH; exact (gap_wf_le _ _ _ (dec_step L p e) Hn))).
  all: pose proof (cnt_from_nonneg K L u p).
  all: try lia.
  all: pose proof e as e'; rewrite ltb_spec in e'; rewrite (cnt_from_step K L u p e'), Esrc in *.
  all: pose proof (cnt_from_nonneg K L u (p + 1)).
  all: lia.
Qed.

Arguments fst_cost : simpl never.
Arguments snd_cost : simpl never.

Lemma fst_time A AC B BC p pC : (cost (extract (extract (fst_cost stepsCM A AC) B BC) p pC) <= 2)%nat.
Proof. destruct pC. cbv. lia. Qed.
Lemma snd_time A AC B BC p pC : (cost (extract (extract (snd_cost stepsCM A AC) B BC) p pC) <= 2)%nat.
Proof. destruct pC. cbv. lia. Qed.

Ltac gen_proj := repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | fst_cost _ _ _ => change (@cost T X) with 0%nat
    | extract (fst_cost _ _ _) _ _ => change (@cost T X) with 0%nat
    | extract (extract (fst_cost stepsCM ?A ?AC) ?B ?BC) ?p ?pC => gen_bound T X (fst_time A AC B BC p pC)
    | snd_cost _ _ _ => change (@cost T X) with 0%nat
    | extract (snd_cost _ _ _) _ _ => change (@cost T X) with 0%nat
    | extract (extract (snd_cost stepsCM ?A ?AC) ?B ?BC) ?p ?pC => gen_bound T X (snd_time A AC B BC p pC)
    end end.

Ltac gen_scan := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (scan_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC) ?h ?hC) ?i ?iC) ?j ?jC) ?k ?kC) ?l ?lC) ?m ?mC =>
    gen_bound T X (scan_F_time _ a aC b bC c cC d dC e eC f fC g gC h hC i iC j jC k kC l lC m mC (le_n _)) end end.

Lemma meas_pos stamp vis sp : (0 <? sp) = true -> (0 < Z.to_nat (meas stamp vis sp))%nat.
Proof.
  intros H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H. unfold meas.
  pose proof (unm_nonneg stamp vis). lia.
Qed.

Lemma Pot_nonneg K L stamp vis stk sp : (0 <= Pot K L stamp vis stk sp)%Z.
Proof.
  unfold Pot. pose proof (SW_nonneg K L stk sp). pose proof (Uv_nonneg K L stamp vis).
  pose proof (unm_nonneg stamp vis). lia.
Qed.

Lemma Pot_pop K L stamp vis (stk : array int) sp : (0 <? sp) = true ->
  Pot K L stamp vis stk sp = (Pot K L stamp vis stk (sp - 1) + 1 + cnt K L stk.[sp - 1])%Z.
Proof. intros H. unfold Pot. rewrite (SW_pop K L stk sp H). lia. Qed.

Lemma sp_pred_inv stamp vis (stk : array int) sp : (0 <? sp) = true ->
  (φ sp + unm stamp vis <= φ (PArray.length stk))%Z ->
  (φ (sp - 1) + unm stamp vis <= φ (PArray.length stk))%Z.
Proof.
  intros H1 H2. rewrite ltb_spec in H1. change (φ 0) with 0%Z in H1.
  rewrite sub_spec. change (φ 1) with 1%Z. rewrite Z.mod_small; [lia|]. pose proof (to_Z_bounded sp). lia.
Qed.

Lemma dfs_F_time : forall n K KC st stC xlb xlbC xlx xlxC xly xlyC L LC k kC stamp stampC vis visC stk stkC sp spC H HC,
  (Z.to_nat (meas stamp vis sp) <= n)%nat ->
  (φ sp + unm stamp vis <= φ (PArray.length stk))%Z ->
  (cost (dfs_F K KC st stC xlb xlbC xlx xlxC xly xlyC L LC k kC stamp stampC vis visC stk stkC sp spC H HC)
    <= Z.to_nat (Pot K L stamp vis stk sp) * 300 + 30)%nat.
Proof.
  induction n as [|n IH]; intros K KC st stC xlb xlbC xlx xlxC xly xlyC L LC k kC stamp stampC vis visC stk stkC sp spC [g] HC Hn Hinv.
  all: cost_simpl.
  all: bdestruct (0 <? sp).
  all: try (exfalso; pose proof (meas_pos stamp vis sp e); lia).
  all: try lia.
  all: zl; prim_simpl; gen_small; gen_scan; gen_proj.
  all: pose proof (sp_pred_inv stamp vis stk sp e Hinv) as Hinv'.
  all: destruct (scan_pot K xlb xlx xly L stk.[sp - 1] k stamp st.[stk.[sp - 1]] vis stk (sp - 1)
     (Zwf_well_founded 0 (gap L st.[stk.[sp - 1]])) Hinv') as (P1 & _ & _ & P4).
  all: gen_call dfs_F (Z.to_nat (Pot K L stamp
       (fst (fst (scan K xlb xlx xly L stk.[sp - 1] k stamp st.[stk.[sp - 1]] vis stk (sp - 1) (Zwf_well_founded 0 (gap L st.[stk.[sp - 1]])))))
       (snd (fst (scan K xlb xlx xly L stk.[sp - 1] k stamp st.[stk.[sp - 1]] vis stk (sp - 1) (Zwf_well_founded 0 (gap L st.[stk.[sp - 1]])))))
       (snd (scan K xlb xlx xly L stk.[sp - 1] k stamp st.[stk.[sp - 1]] vis stk (sp - 1) (Zwf_well_founded 0 (gap L st.[stk.[sp - 1]]))))) * 300 + 30)%nat
     ltac:(apply IH; [exact (gap_wf_le _ _ _ (ddec K st xlb xlx xly L k stamp vis stk sp e) Hn) | exact P1]).
  all: set (r := scan K xlb xlx xly L stk.[sp - 1] k stamp st.[stk.[sp - 1]] vis stk (sp - 1) (Zwf_well_founded 0 (gap L st.[stk.[sp - 1]]))) in *.
  all: rewrite (Pot_pop K L stamp vis stk sp e) in *.
  all: pose proof (cnt_from_le K L stk.[sp - 1] st.[stk.[sp - 1]]).
  all: pose proof (cnt_from_nonneg K L stk.[sp - 1] st.[stk.[sp - 1]]).
  all: pose proof (Pot_nonneg K L stamp (fst (fst r)) (snd (fst r)) (snd r)).
  all: lia.
Qed.

Ltac gen_bound_imp T X L :=
  let Hc := fresh "Hc" in
  pose proof (L : _ -> (@cost T X <= _)%nat) as Hc;
  revert Hc; generalize (@cost T X); intros ? Hc.

Ltac gen_dfs := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (dfs_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC) ?h ?hC) ?i ?iC) ?j ?jC) ?k ?kC) ?l ?lC =>
    gen_bound_imp T X (dfs_F_time _ a aC b bC c cC d dC e eC f fC g gC h hC i iC j jC k kC l lC (le_n _)) end end.

Lemma SW_one K L stk : SW K L stk 1 = (1 + cnt K L stk.[0])%Z.
Proof. unfold SW. change (Z.to_nat (φ 1)) with 1%nat. cbn [fsum]. rewrite Z.add_0_r. reflexivity. Qed.

Lemma Pot_start K L stamp (vis stk : array int) s N1 :
  φ (PArray.length vis) = N1 -> (Pot K L stamp vis.[s <- stamp] stk.[0 <- s] 1 <= 2 * φ L + 1 + 2 * N1)%Z.
Proof.
  intros E. unfold Pot. rewrite SW_one. pose proof (cnt_le K L stk.[0 <- s].[0]).
  pose proof (Uv_le K L stamp vis.[s <- stamp]). pose proof (unm_le stamp vis.[s <- stamp]).
  rewrite alength_set in *. lia.
Qed.

Lemma inv_start stamp (vis stk : array int) s N1 :
  φ (PArray.length vis) = N1 -> φ (PArray.length stk) = N1 -> (φ s < N1)%Z ->
  (φ 1 + unm stamp vis.[s <- stamp] <= φ (PArray.length stk.[0 <- s]))%Z.
Proof.
  intros E1 E2 Hs. rewrite alength_set. change (φ 1) with 1%Z.
  assert (Hv : (s <? PArray.length vis) = true) by (rewrite ltb_spec; lia).
  pose proof (unm_set_le stamp vis s Hv). lia.
Qed.

Lemma Pot_start_nat K L stamp (vis stk : array int) s N1 :
  φ (PArray.length vis) = N1 ->
  (Z.to_nat (Pot K L stamp vis.[s <- stamp] stk.[0 <- s] 1) <= 2 * zn L + 2 * Z.to_nat N1 + 1)%nat.
Proof.
  intros E. pose proof (Pot_start K L stamp vis stk s N1 E). unfold zn.
  pose proof (to_Z_bounded L). pose proof (to_Z_bounded (PArray.length vis)). lia.
Qed.

Definition alen (t : array int) : Z := φ (PArray.length t).

Lemma alen_set (t : array int) i b N1 : alen t = N1 -> alen t.[i <- b] = N1.
Proof. unfold alen. rewrite alength_set. auto. Qed.

Lemma dfs_alen1 K st xlb xlx xly L k stamp (vis stk : array int) sp H N1 :
  alen vis = N1 -> alen (fst (dfs K st xlb xlx xly L k stamp vis stk sp H)) = N1.
Proof. unfold alen. intros E. destruct (dfs_len K st xlb xlx xly L k stamp vis stk sp H) as [D _]. rewrite D. exact E. Qed.

Lemma dfs_alen2 K st xlb xlx xly L k stamp (vis stk : array int) sp H N1 :
  alen stk = N1 -> alen (snd (dfs K st xlb xlx xly L k stamp vis stk sp H)) = N1.
Proof. unfold alen. intros E. destruct (dfs_len K st xlb xlx xly L k stamp vis stk sp H) as [_ D]. rewrite D. exact E. Qed.

Lemma dfs_len1 K st xlb xlx xly L k stamp (vis stk : array int) sp H N1 :
  φ (PArray.length vis) = N1 ->
  φ (PArray.length (fst (dfs K st xlb xlx xly L k stamp vis stk sp H))) = N1.
Proof. intros E. destruct (dfs_len K st xlb xlx xly L k stamp vis stk sp H) as [D _]. rewrite D. exact E. Qed.

Lemma dfs_len2 K st xlb xlx xly L k stamp (vis stk : array int) sp H N1 :
  φ (PArray.length stk) = N1 ->
  φ (PArray.length (snd (dfs K st xlb xlx xly L k stamp vis stk sp H))) = N1.
Proof. intros E. destruct (dfs_len K st xlb xlx xly L k stamp vis stk sp H) as [_ D]. rewrite D. exact E. Qed.

Lemma count_loop_F_time : forall n N1 K KC st stC xlb xlbC xlx xlxC xly xlyC SS SSC L LC m mC s sC d dC j jC (vis : array int) visC (stk : array int) stkC acc accC H HC,
  (Z.to_nat (gap m j) <= n)%nat ->
  alen vis = N1 -> alen stk = N1 -> (φ s < N1)%Z ->
  (cost (count_loop_F K KC st stC xlb xlbC xlx xlxC xly xlyC SS SSC L LC m mC s sC d dC j jC vis visC stk stkC acc accC H HC)
    <= Z.to_nat (gap m j) * ((2 * zn L + 2 * Z.to_nat N1 + 1) * 300 + 300) + 30)%nat.
Proof.
  induction n as [|n IH]; intros N1 K KC st stC xlb xlbC xlx xlxC xly xlyC SS SSC L LC m mC s sC d dC j jC vis visC stk stkC acc accC [g] HC Hn E1 E2 Hs.
  all: cost_simpl.
  all: bdestruct (j <? m).
  all: try (exfalso; pose proof (gap_pos m j e); lia).
  all: try lia.
  all: zl; prim_simpl; gen_small.
  all: (cost_destruct (SS.[j - 1] <? SS.[j]); cost_simpl).
  all: zl; prim_simpl; gen_small; gen_dfs; gen_proj.
  all: try (cost_destruct ((fst (dfs K st xlb xlx xly L SS.[j - 1] j vis.[s <- j] stk.[0 <- s] 1 (Zwf_well_founded 0 (meas j vis.[s <- j] 1)))).[d] =? j); cost_simpl).
  all: zl; prim_simpl; gen_small; gen_proj.
  all: pose proof (gap_succ_eq m j e) as Eg.
  all: try (specialize (Hc (inv_start j vis stk s N1 E1 E2 Hs));
            pose proof (Pot_start_nat K L j vis stk s N1 E1)).
  all: match goal with |- context [@cost ?T ?X] =>
    let h := head_of X in constr_eq h count_loop_F;
    let B := constr:((Z.to_nat (gap m (j + 1)) * ((2 * zn L + 2 * Z.to_nat N1 + 1) * 300 + 300) + 30)%nat) in
    assert (Hc9 : (@cost T X <= B)%nat); [ apply IH | revert Hc9; generalize (@cost T X); intros ? Hc9 ] end.
  all: try first [ exact (gap_wf_le _ _ _ (dec_step m j e) Hn) | exact Hs | exact E1 | exact E2
             | (apply dfs_alen1; apply alen_set; exact E1)
             | (apply dfs_alen2; apply alen_set; exact E2) ].
  all: nia.
Qed.

Lemma keys_len : forall n xla L i K H, (Z.to_nat (gap L i) <= n)%nat ->
  PArray.length (keys_loop xla L i K H) = PArray.length K.
Proof.
  induction n as [|n IH]; intros xla L i K H Hn; rewrite keys_loop_eq;
    destruct (bdec (i <? L)) as [Hi | Hi]; try reflexivity.
  - exfalso. pose proof (gap_pos L i Hi). lia.
  - rewrite IH; [apply alength_set|]. exact (gap_wf_le _ _ _ (dec_step L i Hi) Hn).
Qed.

Lemma bnd_len : forall n xlx xly L i B H, (Z.to_nat (gap L i) <= n)%nat ->
  PArray.length (bnd_loop xlx xly L i B H) = PArray.length B.
Proof.
  induction n as [|n IH]; intros xlx xly L i B H Hn; rewrite bnd_loop_eq;
    destruct (bdec (i <? L)) as [Hi | Hi]; try reflexivity.
  - exfalso. pose proof (gap_pos L i Hi). lia.
  - rewrite IH; [rewrite !alength_set; reflexivity|]. exact (gap_wf_le _ _ _ (dec_step L i Hi) Hn).
Qed.

Lemma len_make (n b : int) : (φ n <= 4194303)%Z -> φ (PArray.length (PArray.make n b)) = φ n.
Proof.
  intros H. rewrite alength_make. replace (n <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec. exact H.
Qed.

Lemma keys_zn xla H :
  zn (PArray.length (keys_loop xla (PArray.length xla) 0 (PArray.make (PArray.length xla) 0) H)) = zn (PArray.length xla).
Proof.
  unfold zn. rewrite (keys_len _ _ _ _ _ _ (le_n _)). rewrite len_make by apply alength_bound. reflexivity.
Qed.

Lemma bnd_zn xlx xly L b H : (φ L <= 5000)%Z ->
  zn (PArray.length (bnd_loop xlx xly L 0 (PArray.make (L + L + 2) 0).[0 <- 1].[1 <- b + 1] H)) = (2 * zn L + 2)%nat.
Proof.
  intros HL. unfold zn. rewrite (bnd_len _ _ _ _ _ _ _ (le_n _)). rewrite !alength_set.
  assert (E : φ (L + L + 2) = (2 * φ L + 2)%Z).
  { sia. }
  rewrite len_make by lia. rewrite E. pose proof (to_Z_bounded L). lia.
Qed.

Lemma gap_m1 L : (φ L <= 5000)%Z -> Z.to_nat (gap (L + L + 2) 1) = (2 * zn L + 1)%nat.
Proof.
  intros HL. unfold gap, zn. change (φ 1) with 1%Z.
  assert (E : φ (L + L + 2) = (2 * φ L + 2)%Z) by sia. rewrite E. pose proof (to_Z_bounded L). lia.
Qed.

Lemma alen_make1 (n : int) : (φ n <= 1000)%Z -> alen (PArray.make (n + 1) 0) = (φ n + 1)%Z.
Proof.
  intros H. unfold alen. pose proof (to_Z_bounded n).
  assert (E : φ (n + 1) = (φ n + 1)%Z) by sia.
  rewrite len_make by lia. exact E.
Qed.

Lemma log2_double L : (Nat.log2 (2 * L + 2) <= Nat.log2 L + 2)%nat.
Proof.
  replace (2 * L + 2)%nat with (2 * (L + 1))%nat by lia.
  destruct L as [|L]; [cbv; lia|].
  rewrite Nat.log2_double by lia.
  pose proof (Nat.log2_succ_le (S L)). rewrite Nat.add_1_r. lia.
Qed.

Ltac gen_loops := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with
  | extract (extract (extract (extract (keys_loop_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC =>
      gen_bound T X (keys_loop_F_time _ a aC b bC c cC d dC e eC (le_n _))
  | extract (extract (extract (st_loop_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC =>
      gen_bound T X (st_loop_F_time _ a aC b bC c cC d dC (le_n _))
  | extract (extract (extract (extract (extract (bnd_loop_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC =>
      gen_bound T X (bnd_loop_F_time _ a aC b bC c cC d dC e eC f fC (le_n _))
  | msort_cost stepsCM ?a ?aC => gen_bound T X (msort_time a aC)
  end end.

Ltac gen_count N1 := match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (count_loop_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC) ?h ?hC) ?i ?iC) ?j ?jC) ?k ?kC) ?l ?lC) ?m ?mC) ?n ?nC) ?o ?oC =>
    let Hc := fresh "Hcount" in
    pose proof (count_loop_F_time _ N1 a aC b bC c cC d dC e eC f fC g gC h hC i iC j jC k kC l lC m mC n nC o oC (le_n _)
      : _ -> _ -> _ -> (@cost T X <= _)%nat) as Hc;
    revert Hc; generalize (@cost T X); intros ? Hc end end.

Lemma core_time n nC b bC s sC d dC xla xlaC xlb xlbC xlx xlxC xly xlyC :
  (φ n <= 1000)%Z -> (φ (PArray.length xla) <= 5000)%Z -> (φ s <= φ n)%Z ->
  (cost (extract (extract (extract (extract (extract (extract (extract (securitybadge_core_cost stepsCM n nC) b bC) s sC) d dC) xla xlaC) xlb xlbC) xlx xlxC) xly xlyC)
   <= ((zn (PArray.length xla) + 1) * (zn n + zn (PArray.length xla) + Nat.log2 (zn (PArray.length xla)) + 1)) * 20000 + 20000)%nat.
Proof.
  intros Hn HL Hs.
  unfold securitybadge_core_cost. cost_simpl.
  zl; prim_simpl.
  gen_loops. gen_count (φ n + 1)%Z.
  specialize (Hcount (alen_make1 n Hn) (alen_make1 n Hn) ltac:(lia)).
  rewrite gap_m1 in Hcount by exact HL.
  rewrite gap0 in *.
  rewrite keys_zn in *.
  rewrite bnd_zn in * by exact HL.
  assert (EN : Z.to_nat (φ n + 1) = (zn n + 1)%nat) by (unfold zn; pose proof (to_Z_bounded n); lia).
  rewrite EN in Hcount.
  pose proof (log2_double (zn (PArray.length xla))) as Hlg.
  set (Lz := zn (PArray.length xla)) in *. set (Nz := zn n) in *. set (lg := Nat.log2 Lz) in *.
  set (lg2 := Nat.log2 (2 * Lz + 2)) in *.
  assert (Hc3' : (n4 <= (lg + 3) * ((2 * Lz + 2) * 300 + 100) + 60)%nat).
  { eapply Nat.le_trans; [exact Hc3|]. apply Nat.add_le_mono_r. apply Nat.mul_le_mono_r. lia. }
  clear Hc3 EN Hn HL Hs. clearbody Lz Nz lg lg2.
  nia.
Qed.

Lemma len_bridge (x : array int) : φ (PArray.length@{Set} x) = φ (PArray.length@{array_u} x).
Proof. reflexivity. Qed.

Theorem securitybadge_time : exists c1 c2 : nat,
  forall (room_count badge_count start destination : N)
  (lock_sources lock_targets lowest_badges
  highest_badges : list N )
  (room_count_int badge_count_int start_int
  destination_int : uint)
  (lock_sources_arr lock_targets_arr : array uint)
  (lowest_badges_arr highest_badges_arr : array uint
  ),
  valid_input room_count badge_count start destination
  lock_sources lock_targets lowest_badges highest_badges
  ->
  repr room_count_int room_count -> repr badge_count_int
  badge_count ->
  repr start_int start -> repr destination_int destination
  ->
  repr lock_sources_arr lock_sources -> repr
  lock_targets_arr lock_targets ->
  repr lowest_badges_arr lowest_badges ->
  repr highest_badges_arr highest_badges ->
  (cost8 securitybadge_cost room_count_int badge_count_int start_int destination_int lock_sources_arr lock_targets_arr lowest_badges_arr highest_badges_arr <= c1 * ((size lock_sources_arr + 1) * (size room_count_int + size lock_sources_arr + Nat.log2 (size lock_sources_arr) + 1)) + c2)%nat.
Proof.
  exists 20000%nat, 20100%nat.
  intros n b s d la lb lx ly xn xb xs xd xla xlb xlx xly VI Rn Rb Rs Rd Ra Rlb Rx Ry.
  destruct VI as [_ _ _ Vn Vl _ Vs _ _ _ _].
  pose proof (repr_N _ _ Rn) as En. pose proof (repr_N _ _ Rs) as Es.
  pose proof (repr_len _ _ Ra) as EL. unfold len in Vl.
  assert (H1 : (φ xn <= 1000)%Z) by lia.
  pose proof (len_bridge xla) as EB.
  assert (H2 : (φ (@PArray.length@{array_u} int xla) <= 5000)%Z) by lia.
  assert (H3 : (φ xs <= φ xn)%Z) by lia.
  clear -H1 H2 H3.
  match goal with |- (_ <= ?R)%nat => remember R as RHS eqn:ER end.
  unfold cost8, securitybadge_cost, securitybadge_impl_cost. cost_simpl.
  zl.
  match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (extract (extract (securitybadge_core_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC) ?h ?hC =>
    gen_bound T X (core_time a aC b bC c cC d dC e eC f fC g gC h hC H1 H2 H3) end end.
  assert (Ez : size xla = zn (@PArray.length@{array_u} int xla)) by reflexivity.
  assert (En : size xn = zn xn) by reflexivity.
  subst RHS. rewrite Ez, En.
  match type of Hc with (_ <= ?P * _ + _)%nat =>
    match goal with |- (_ <= _ * ?Q + _)%nat => replace Q with P by reflexivity end end.
  set (c := 20000%nat) in *. set (c' := 20100%nat) in *.
  assert (Hcc : (c + 8 <= c')%nat) by (unfold c, c'; apply Nat.leb_le; vm_compute; reflexivity).
  clearbody c c'. nia.
Qed.
