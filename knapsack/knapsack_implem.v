(* Implementation of knapsack (knapsack.spec): the textbook 0/1 knapsack
   dynamic program with a rolling value row and one flat decision table.

   Code.  [knapsack C values weights] (n items, C1 = C + 1):
   - [row] : array int of C1 cells, initially 0 ; [dec] : array bool of
     n * C1 cells, initially false ;
   - for i = 0 .. n-1 ([items_loop]), for c = C down to w_i ([item_loop],
     driven by k = c + 1 while w_i < k): if row[c - w_i] + v_i > row[c]
     then row[c] := row[c - w_i] + v_i and dec[i * C1 + c] := true.  The
     descending scan keeps row[c - w_i] at its value for the first i items;
   - the answer value is row[C] ;
   - [walk] goes back from (i, c) = (n, C): for i = n-1 down to 0, when
     dec[i * C1 + c] holds, i is written at the next free cell of an
     [array int] of n cells and c -= w_i ; the k cells written are then
     copied into an array of exactly k cells ([copy_loop]).
   All arrays are threaded linearly; everything is Uint63 [int].

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) measure] proof (the shape of template/polymul1).

   Proof.  The math side ([Math] section) defines the DP [best i c] (best
   value with the first i items and capacity c), the decision [take i c]
   and the reconstruction [recon i c]; [recon] is a selection that fits,
   its value is [best], and [best] is optimal ([best_opt], by removing the
   last item from any selection).  The machine side ([Proofs] section)
   proves one invariant lemma per loop. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Bool.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma aget_make : forall (n i : int) (b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

Lemma blength_set : forall (t : array bool) (i : int) (b : bool),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set bool t i b). Qed.

Lemma bget_set_same : forall (t : array bool) (i : int) (b : bool),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same bool t i b H). Qed.

Lemma bget_set_other : forall (t : array bool) (i j : int) (b : bool),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other bool t i j b H). Qed.

Lemma blength_make : forall (n : int) (b : bool),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make bool n b). Qed.

Lemma bget_make : forall (n i : int) (b : bool), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make bool b n i). Qed.

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

Lemma down_step : forall w k : int,
  (w <? k) = true -> Zwf 0 (φ (k - 1)) (φ k).
Proof.
  intros w k H. rewrite ltb_spec in H.
  pose proof (to_Z_bounded w).
  assert (H1 : (φ (k - 1)) = ((φ k) - 1)%Z) by sia.
  unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Item (v, w), row base [base] of the decision table: capacities
   c = k-1, k-2, ..., w (descending). *)
Fixpoint item_loop (v w base k : int) (row : array int) (dec : array bool)
    (H : Acc (Zwf 0) (φ k)) {struct H} : array int * array bool :=
  match bdec (w <? k) with
  | left Hk =>
      let c := k - 1 in
      let cand := row.[c - w] + v in
      if row.[c] <? cand
      then item_loop v w base c row.[c <- cand] dec.[base + c <- true]
             (Acc_inv H (down_step w k Hk))
      else item_loop v w base c row dec (Acc_inv H (down_step w k Hk))
  | right _ => (row, dec)
  end.

Lemma item_loop_eq : forall v w base k row dec H,
  item_loop v w base k row dec H =
  match bdec (w <? k) with
  | left Hk =>
      let c := k - 1 in
      let cand := row.[c - w] + v in
      if row.[c] <? cand
      then item_loop v w base c row.[c <- cand] dec.[base + c <- true]
             (Acc_inv H (down_step w k Hk))
      else item_loop v w base c row dec (Acc_inv H (down_step w k Hk))
  | right _ => (row, dec)
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* Items i, i+1, ..., n-1. *)
Fixpoint items_loop (xv xw : array int) (n C1 i : int) (row : array int)
    (dec : array bool) (H : Acc (Zwf 0) (gap n i)) {struct H}
    : array int * array bool :=
  match bdec (i <? n) with
  | left Hi =>
      let rd := item_loop xv.[i] xw.[i] (i * C1) C1 row dec
                  (Zwf_well_founded 0 (φ C1)) in
      items_loop xv xw n C1 (i + 1) (fst rd) (snd rd)
        (Acc_inv H (dec_step n i Hi))
  | right _ => (row, dec)
  end.

Lemma items_loop_eq : forall xv xw n C1 i row dec H,
  items_loop xv xw n C1 i row dec H =
  match bdec (i <? n) with
  | left Hi =>
      let rd := item_loop xv.[i] xw.[i] (i * C1) C1 row dec
                  (Zwf_well_founded 0 (φ C1)) in
      items_loop xv xw n C1 (i + 1) (fst rd) (snd rd)
        (Acc_inv H (dec_step n i Hi))
  | right _ => (row, dec)
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* The walk back: items i-1, ..., 0 at remaining capacity c; k cells of
   out are written. *)
Fixpoint walk (xw : array int) (dec : array bool) (C1 i c k : int)
    (out : array int) (H : Acc (Zwf 0) (φ i)) {struct H} : int * array int :=
  match bdec (0 <? i) with
  | left Hi =>
      let j := i - 1 in
      if dec.[j * C1 + c]
      then walk xw dec C1 j (c - xw.[j]) (k + 1) out.[k <- j]
             (Acc_inv H (down_step 0 i Hi))
      else walk xw dec C1 j c k out (Acc_inv H (down_step 0 i Hi))
  | right _ => (k, out)
  end.

Lemma walk_eq : forall xw dec C1 i c k out H,
  walk xw dec C1 i c k out H =
  match bdec (0 <? i) with
  | left Hi =>
      let j := i - 1 in
      if dec.[j * C1 + c]
      then walk xw dec C1 j (c - xw.[j]) (k + 1) out.[k <- j]
             (Acc_inv H (down_step 0 i Hi))
      else walk xw dec C1 j c k out (Acc_inv H (down_step 0 i Hi))
  | right _ => (k, out)
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* dst[j .. m-1] := src[j .. m-1]. *)
Fixpoint copy_loop (src dst : array int) (m j : int)
    (H : Acc (Zwf 0) (gap m j)) {struct H} : array int :=
  match bdec (j <? m) with
  | left Hj => copy_loop src dst.[j <- src.[j]] m (j + 1)
                 (Acc_inv H (dec_step m j Hj))
  | right _ => dst
  end.

Lemma copy_loop_eq : forall src dst m j H,
  copy_loop src dst m j H =
  match bdec (j <? m) with
  | left Hj => copy_loop src dst.[j <- src.[j]] m (j + 1)
                 (Acc_inv H (dec_step m j Hj))
  | right _ => dst
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition knapsack_impl (Cw : int) (xv xw : array int) : int * array int :=
  let n := PArray.length xv in
  let C1 := Cw + 1 in
  let rd := items_loop xv xw n C1 0 (PArray.make C1 0)
              (PArray.make (n * C1) false) (Zwf_well_founded 0 (gap n 0)) in
  let bestv := (fst rd).[Cw] in
  let ko := walk xw (snd rd) C1 n Cw 0 (PArray.make n 0)
              (Zwf_well_founded 0 (φ n)) in
  let k := fst ko in
  (bestv, copy_loop (snd ko) (PArray.make k 0) k 0
            (Zwf_well_founded 0 (gap k 0))).

(* ------------------------------------------------------------------ *)
(* Math side: the dynamic program on lists                             *)
(* ------------------------------------------------------------------ *)

Section Math.
Open Scope N_scope.
Variables (vs ws : list N).

Definition V (j : nat) : N := get_list_N vs (N.of_nat j).
Definition W (j : nat) : N := get_list_N ws (N.of_nat j).

(* best value with items 0 .. i-1 and capacity c *)
Fixpoint best (i : nat) (c : N) : N :=
  match i with
  | O => 0
  | S j => if (W j <=? c) && (best j c <? best j (c - W j) + V j)
           then best j (c - W j) + V j else best j c
  end.

(* item j is taken at capacity c *)
Definition take (j : nat) (c : N) : bool :=
  (W j <=? c) && (best j c <? best j (c - W j) + V j).

Lemma best_S : forall j c,
  best (S j) c = if take j c then best j (c - W j) + V j else best j c.
Proof. reflexivity. Qed.

Fixpoint recon (i : nat) (c : N) : list N :=
  match i with
  | O => []
  | S j => if take j c then N.of_nat j :: recon j (c - W j) else recon j c
  end.

Lemma recon_S : forall j c,
  recon (S j) c = if take j c then N.of_nat j :: recon j (c - W j) else recon j c.
Proof. reflexivity. Qed.

Lemma take_true : forall j c, take j c = true ->
  W j <= c /\ best j c < best j (c - W j) + V j.
Proof.
  intros j c H. unfold take in H. rewrite andb_true_iff, N.leb_le, N.ltb_lt in H.
  exact H.
Qed.

Lemma take_false : forall j c, take j c = false -> W j <= c ->
  best j (c - W j) + V j <= best j c.
Proof.
  intros j c H Hw. unfold take in H. apply N.leb_le in Hw. rewrite Hw in H.
  simpl in H. apply N.ltb_ge in H. exact H.
Qed.

Lemma take_small : forall j c, c < W j -> take j c = false.
Proof.
  intros j c H. unfold take.
  replace (W j <=? c) with false by (symmetry; apply N.leb_gt; exact H).
  reflexivity.
Qed.

Lemma best_mono : forall j c, best j c <= best (S j) c.
Proof.
  intros j c. rewrite best_S. destruct (take j c) eqn:E; [|lia].
  apply take_true in E. lia.
Qed.

Lemma best_bound : (forall j, V j <= 10000) ->
  forall i c, best i c <= 10000 * N.of_nat i.
Proof.
  intros HV. induction i as [|j IH]; intros c; [simpl; lia|].
  rewrite best_S. destruct (take j c).
  - pose proof (IH (c - W j)). pose proof (HV j). lia.
  - pose proof (IH c). lia.
Qed.

Lemma recon_bound : forall i c, Forall (fun x => x < N.of_nat i) (recon i c).
Proof.
  induction i as [|j IH]; intros c; [constructor|]. rewrite recon_S.
  destruct (take j c).
  - constructor; [lia|]. eapply Forall_impl; [|apply IH]. intros x Hx; cbv beta in *; lia.
  - eapply Forall_impl; [|apply IH]. intros x Hx; cbv beta in *; lia.
Qed.

Lemma recon_nodup : forall i c, NoDup (recon i c).
Proof.
  induction i as [|j IH]; intros c; [constructor|]. rewrite recon_S.
  destruct (take j c); [|apply IH].
  constructor; [|apply IH]. intro Hin.
  pose proof (recon_bound j (c - W j)) as Hb. rewrite Forall_forall in Hb.
  apply Hb in Hin. lia.
Qed.

Lemma recon_weight : forall i c, total ws (recon i c) <= c.
Proof.
  induction i as [|j IH]; intros c; [simpl; lia|]. rewrite recon_S.
  destruct (take j c) eqn:E; [|apply IH].
  apply take_true in E. cbn [total]. fold (W j).
  pose proof (IH (c - W j)). lia.
Qed.

Lemma recon_value : forall i c, total vs (recon i c) = best i c.
Proof.
  induction i as [|j IH]; intros c; [reflexivity|]. rewrite recon_S, best_S.
  destruct (take j c); [|apply IH].
  cbn [total]. fold (V j). rewrite IH. lia.
Qed.

Lemma recon_length : forall i c, (List.length (recon i c) <= i)%nat.
Proof.
  induction i as [|j IH]; intros c; [simpl; lia|]. rewrite recon_S.
  destruct (take j c); simpl; [specialize (IH (c - W j)) | specialize (IH c)]; lia.
Qed.

Lemma total_remove : forall a l x, NoDup l -> In x l ->
  total a l = get_list_N a x + total a (remove N.eq_dec x l).
Proof.
  intros a l. induction l as [|y l IH]; intros x Hnd Hin; [destruct Hin|].
  inversion Hnd as [|? ? Hy Hl]; subst. cbn [remove].
  destruct (N.eq_dec x y) as [E|E].
  - subst. rewrite notin_remove by exact Hy. reflexivity.
  - destruct Hin as [Hin|Hin]; [congruence|]. cbn [total].
    rewrite (IH x Hl Hin). lia.
Qed.

Lemma nodup_remove : forall x l, NoDup l -> NoDup (remove N.eq_dec x l).
Proof.
  intros x l. induction l as [|y l IH]; intros Hnd; [constructor|].
  inversion Hnd as [|? ? Hy Hl]; subst. cbn [remove].
  destruct (N.eq_dec x y); [auto|].
  constructor; [|auto]. intro Hin. apply in_remove in Hin. tauto.
Qed.

Lemma best_opt : forall i l c, NoDup l -> Forall (fun x => x < N.of_nat i) l ->
  total ws l <= c -> total vs l <= best i c.
Proof.
  induction i as [|j IH]; intros l c Hnd Hb Hw.
  - destruct l as [|x l]; [simpl; lia|]. inversion Hb; subst. lia.
  - destruct (in_dec N.eq_dec (N.of_nat j) l) as [Hin|Hnin].
    + pose proof (total_remove ws l _ Hnd Hin) as Ew.
      pose proof (total_remove vs l _ Hnd Hin) as Ev.
      fold (W j) in Ew. fold (V j) in Ev.
      assert (Hl' : Forall (fun x => x < N.of_nat j) (remove N.eq_dec (N.of_nat j) l)).
      { rewrite Forall_forall in *. intros x Hx. apply in_remove in Hx.
        destruct Hx as [Hx Hne]. apply Hb in Hx. lia. }
      pose proof (IH _ (c - W j) (nodup_remove _ _ Hnd) Hl' ltac:(lia)) as H1.
      rewrite best_S. destruct (take j c) eqn:E; [lia|].
      pose proof (take_false j c E ltac:(lia)). lia.
    + assert (Hl : Forall (fun x => x < N.of_nat j) l).
      { rewrite Forall_forall in *. intros x Hx.
        assert (x <> N.of_nat j) by (intro; subst; tauto). apply Hb in Hx. lia. }
      pose proof (IH l c Hnd Hl Hw). pose proof (best_mono j c). lia.
Qed.

(* The expected decision table while item ni is processed down to
   capacity kz: rows < ni done, row ni done on capacities >= kz. *)
Definition dexp (ni : nat) (kz : N) (i' : nat) (c : N) : bool :=
  if (i' <? ni)%nat then take i' c
  else if (i' =? ni)%nat && (kz <=? c) then take ni c else false.

Lemma dexp_init : forall kz i' c, c < kz -> dexp 0 kz i' c = false.
Proof.
  intros kz i' c H. unfold dexp. destruct (Nat.ltb_spec i' 0); [lia|].
  replace (kz <=? c) with false by (symmetry; apply N.leb_gt; exact H).
  rewrite andb_false_r. reflexivity.
Qed.

Lemma dexp_other : forall ni kz i' c, 0 < kz ->
  ~ (i' = ni /\ c = kz - 1) -> dexp ni (kz - 1) i' c = dexp ni kz i' c.
Proof.
  intros ni kz i' c Hk Hn. unfold dexp.
  destruct (Nat.ltb_spec i' ni); [reflexivity|].
  destruct (Nat.eqb_spec i' ni); simpl; [|reflexivity].
  destruct (N.leb_spec (kz - 1) c), (N.leb_spec kz c); try reflexivity; lia.
Qed.

Lemma dexp_here : forall ni kz, dexp ni kz ni kz = take ni kz.
Proof.
  intros ni kz. unfold dexp. rewrite Nat.ltb_irrefl, Nat.eqb_refl, N.leb_refl.
  reflexivity.
Qed.

Lemma dexp_here_old : forall ni kz, 0 < kz -> dexp ni kz ni (kz - 1) = false.
Proof.
  intros ni kz H. unfold dexp. rewrite Nat.ltb_irrefl, Nat.eqb_refl.
  replace (kz <=? kz - 1) with false by (symmetry; apply N.leb_gt; lia).
  reflexivity.
Qed.

Lemma dexp_end : forall ni kz C1 i' c, c < C1 ->
  (c < kz -> take ni c = false) -> dexp ni kz i' c = dexp (S ni) C1 i' c.
Proof.
  intros ni kz C1 i' c HC Ht. unfold dexp.
  destruct (Nat.ltb_spec i' ni), (Nat.ltb_spec i' (S ni)); try reflexivity; try lia.
  - assert (i' = ni) by lia. subst. rewrite Nat.eqb_refl. simpl.
    destruct (N.leb_spec kz c); [reflexivity|]. symmetry. apply Ht. lia.
  - destruct (Nat.eqb_spec i' ni); [lia|].
    replace (C1 <=? c) with false by (symmetry; apply N.leb_gt; lia).
    rewrite andb_false_r. reflexivity.
Qed.

End Math.

(* ------------------------------------------------------------------ *)
(* Index arithmetic of the flat table                                  *)
(* ------------------------------------------------------------------ *)

Lemma idx_spec : forall iw c C1 : int,
  ((φ iw) * (φ C1) + (φ c) < wB)%Z -> (φ (iw * C1 + c)) = ((φ iw) * (φ C1) + (φ c))%Z.
Proof.
  intros iw c C1 H.
  pose proof (to_Z_bounded iw). pose proof (to_Z_bounded C1). pose proof (to_Z_bounded c).
  rewrite add_spec, mul_spec.
  rewrite (Z.mod_small ((φ iw) * (φ C1))) by nia.
  apply Z.mod_small. lia.
Qed.

Lemma idx_inj : forall a a' c c' m : Z,
  (0 <= c < m -> 0 <= c' < m -> 0 <= a -> 0 <= a' ->
   a * m + c = a' * m + c' -> a = a' /\ c = c')%Z.
Proof.
  intros a a' c c' m Hc Hc' Ha Ha' E.
  assert (a = a').
  { destruct (Z.lt_trichotomy a a') as [H|[H|H]]; [exfalso; nia | exact H | exfalso; nia]. }
  subst. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Machine side                                                        *)
(* ------------------------------------------------------------------ *)

Section Proofs.
(* the machine inputs are read at [int]: the code is written on [int], and
   lia treats [@get uint] and [@get int] as different atoms *)
Variables (C : N) (values weights : list N) (Cw : int) (xv xw : array int).
Hypothesis Hvi : valid_input C values weights.
Hypothesis HC : @repr uint N _ Cw C.
Hypothesis Hxv : @repr (array uint) (list N) _ xv values.
Hypothesis Hxw : @repr (array uint) (list N) _ xw weights.

Local Notation nN := (List.length values).
Local Notation LEN := (PArray.length xv).
Local Notation C1 := (Cw + 1)%uint63.
Local Notation B := (best values weights).

Lemma Cz_val : (φ Cw) = Z.of_N C.
Proof. unfold repr, repr_uint in HC. pose proof (to_Z_bounded Cw). lia. Qed.

Lemma C_bounds : (1 <= Z.of_N C <= 2000)%Z.
Proof. destruct Hvi as [H _ _ _ _]. lia. Qed.

Lemma nN_bounds : (1 <= Z.of_nat nN <= 2000)%Z.
Proof. destruct Hvi as [_ H _ _ _]. unfold len in H. lia. Qed.

Lemma nW : List.length weights = nN.
Proof. destruct Hvi as [_ _ H _ _]. unfold len in H. lia. Qed.

Lemma LEN_val : (φ LEN) = Z.of_nat nN.
Proof. destruct Hxv as [Hl _]. symmetry. exact Hl. Qed.

Lemma LENw_val : (φ (PArray.length xw)) = Z.of_nat nN.
Proof. destruct Hxw as [Hl _]. rewrite <- nW. symmetry. exact Hl. Qed.

Lemma C1_val : (φ C1) = ((φ Cw) + 1)%Z.
Proof. pose proof Cz_val. pose proof C_bounds. sia. Qed.

Lemma LC_val : (φ (LEN * C1)) = (Z.of_nat nN * ((φ Cw) + 1))%Z.
Proof.
  pose proof Cz_val. pose proof C_bounds. pose proof nN_bounds.
  pose proof LEN_val. pose proof C1_val.
  rewrite mul_spec. rewrite H2, H3. apply Z.mod_small. rewrite wB_val. nia.
Qed.

Lemma V_le : forall j, (V values j <= 10000)%N.
Proof.
  intros j. destruct Hvi as [_ _ _ HV _]. unfold V, get_list_N.
  destruct (nth_in_or_default (N.to_nat (N.of_nat j)) values 0%N) as [Hin|E].
  - rewrite Forall_forall in HV. apply HV in Hin. lia.
  - rewrite E. lia.
Qed.

Lemma best_le : forall i c, (i <= nN)%nat -> (Z.of_N (B i c) <= 20000000)%Z.
Proof.
  intros i c Hi. pose proof (best_bound values weights V_le i c). pose proof nN_bounds. lia.
Qed.

Lemma get_v : forall iw : int, ((φ iw) < Z.of_nat nN)%Z ->
  (φ (xv.[iw])) = Z.of_N (V values (Z.to_nat (φ iw))).
Proof.
  intros iw Hi. destruct Hxv as [_ Hc].
  destruct (Hc (Z.to_nat (φ iw)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded iw); lia).
  rewrite of_to_Z in Hr. unfold V, get_list_N. rewrite Nat2N.id.
  rewrite (nth_error_nth _ _ _ Hm).
  rewrite <- Hr. rewrite Z2N.id; [reflexivity|]. apply to_Z_bounded.
Qed.

Lemma get_w : forall iw : int, ((φ iw) < Z.of_nat nN)%Z ->
  (φ (xw.[iw])) = Z.of_N (W weights (Z.to_nat (φ iw))).
Proof.
  intros iw Hi. destruct Hxw as [_ Hc].
  destruct (Hc (Z.to_nat (φ iw)) ltac:(rewrite nW; lia)) as (m & Hm & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded iw); lia).
  rewrite of_to_Z in Hr. unfold W, get_list_N. rewrite Nat2N.id.
  rewrite (nth_error_nth _ _ _ Hm).
  rewrite <- Hr. rewrite Z2N.id; [reflexivity|]. apply to_Z_bounded.
Qed.

Lemma idx_val : forall iw c : int, ((φ iw) < Z.of_nat nN)%Z -> ((φ c) <= (φ Cw))%Z ->
  (φ (iw * C1 + c)) = ((φ iw) * ((φ Cw) + 1) + (φ c))%Z /\
  ((φ iw) * ((φ Cw) + 1) + (φ c) < Z.of_nat nN * ((φ Cw) + 1))%Z.
Proof.
  intros iw c Hi Hc. pose proof Cz_val. pose proof C_bounds. pose proof nN_bounds.
  pose proof (to_Z_bounded iw). pose proof (to_Z_bounded c). pose proof C1_val.
  split; [|nia].
  rewrite idx_spec; rewrite H4; [reflexivity|]. rewrite wB_val. nia.
Qed.

Lemma idx_neq : forall iw c iw' c' : int,
  ((φ iw) < Z.of_nat nN)%Z -> ((φ c) <= (φ Cw))%Z ->
  ((φ iw') < Z.of_nat nN)%Z -> ((φ c') <= (φ Cw))%Z ->
  ~ ((φ iw) = (φ iw') /\ (φ c) = (φ c'))%Z -> iw * C1 + c <> iw' * C1 + c'.
Proof.
  intros iw c iw' c' H1 H2 H3 H4 Hn E. apply Hn.
  apply (f_equal to_Z) in E.
  destruct (idx_val iw c H1 H2) as [E1 _]. destruct (idx_val iw' c' H3 H4) as [E2 _].
  rewrite E1, E2 in E.
  pose proof (to_Z_bounded iw). pose proof (to_Z_bounded c).
  pose proof (to_Z_bounded iw'). pose proof (to_Z_bounded c').
  apply (idx_inj _ _ _ _ ((φ Cw) + 1)); lia.
Qed.

Lemma idx_in : forall iw c : int, ((φ iw) < Z.of_nat nN)%Z -> ((φ c) <= (φ Cw))%Z ->
  (iw * C1 + c <? LEN * C1) = true.
Proof.
  intros iw c H1 H2. rewrite ltb_spec, LC_val.
  destruct (idx_val iw c H1 H2) as [E1 E2]. lia.
Qed.

Definition row_inv (row : array int) (ni : nat) : Prop :=
  forall c : int, ((φ c) <= (φ Cw))%Z -> (φ (row.[c])) = Z.of_N (B ni (Z.to_N (φ c))).

Definition dec_inv (dec : array bool) (ni : nat) (kz : N) : Prop :=
  forall iw c : int, ((φ iw) < Z.of_nat nN)%Z -> ((φ c) <= (φ Cw))%Z ->
  dec.[iw * C1 + c] = dexp values weights ni kz (Z.to_nat (φ iw)) (Z.to_N (φ c)).

(* The inner loop: item iw, capacities k-1 down to w. *)
Lemma item_loop_spec : forall iw : int, ((φ iw) < Z.of_nat nN)%Z ->
  forall (row' : array int) (dec' : array bool) z (k : int) (row : array int)
         (dec : array bool) (H : Acc (Zwf 0) (φ k)),
  item_loop xv.[iw] xw.[iw] (iw * C1) k row dec H = (row', dec') ->
  (φ k) = z -> ((φ k) <= (φ Cw) + 1)%Z ->
  PArray.length row = C1 -> PArray.length dec = LEN * C1 ->
  (forall c : int, ((φ c) < (φ k))%Z ->
     (φ (row.[c])) = Z.of_N (B (Z.to_nat (φ iw)) (Z.to_N (φ c)))) ->
  (forall c : int, ((φ k) <= (φ c) <= (φ Cw))%Z ->
     (φ (row.[c])) = Z.of_N (B (S (Z.to_nat (φ iw))) (Z.to_N (φ c)))) ->
  dec_inv dec (Z.to_nat (φ iw)) (Z.to_N (φ k)) ->
  PArray.length row' = C1 /\ PArray.length dec' = LEN * C1 /\
  row_inv row' (S (Z.to_nat (φ iw))) /\
  dec_inv dec' (S (Z.to_nat (φ iw))) (Z.to_N ((φ Cw) + 1)).
Proof.
  intros iw Hiw row' dec' z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k row dec H Heq Hz Hk Hrl Hdl Hlo Hhi Hdec. subst z.
  pose proof Cz_val as HCz. pose proof C_bounds as HCb. pose proof nN_bounds as Hnb.
  pose proof C1_val as HC1.
  pose proof (get_v iw Hiw) as Hv. pose proof (get_w iw Hiw) as Hw.
  pose proof (V_le (Z.to_nat (φ iw))) as HVle.
  pose proof (to_Z_bounded k) as Bk. pose proof (to_Z_bounded iw) as Biw.
  rewrite item_loop_eq in Heq.
  destruct (bdec (xw.[iw] <? k)) as [Hk'|Hk'].
  - cbv beta iota zeta in Heq.
    pose proof Hk' as Hlt. rewrite ltb_spec in Hlt.
    pose proof (to_Z_bounded (xw.[iw])) as Bw.
    assert (Ec : (φ (k - 1)) = ((φ k) - 1)%Z) by sia.
    assert (Ecw : (φ (k - 1 - xw.[iw])) = ((φ k) - 1 - (φ (xw.[iw])))%Z) by sia.
    assert (EkN : Z.to_N (φ (k - 1)) = (Z.to_N (φ k) - 1)%N) by lia.
    pose proof (Hlo (k - 1 - xw.[iw]) ltac:(lia)) as Hr1.
    pose proof (Hlo (k - 1) ltac:(lia)) as Hr2.
    assert (EN : Z.to_N (φ (k - 1 - xw.[iw]))
                 = (Z.to_N (φ (k - 1)) - W weights (Z.to_nat (φ iw)))%N) by lia.
    rewrite EN in Hr1.
    pose proof (best_le (Z.to_nat (φ iw))
                  (Z.to_N (φ (k - 1)) - W weights (Z.to_nat (φ iw))) ltac:(lia)) as Hb1.
    assert (Hcand : (φ (row.[k - 1 - xw.[iw]] + xv.[iw]))
                    = ((φ (row.[k - 1 - xw.[iw]])) + (φ (xv.[iw])))%Z).
    { rewrite add_spec. apply Z.mod_small. rewrite wB_val.
      pose proof (to_Z_bounded (row.[k - 1 - xw.[iw]])). lia. }
    assert (Etake : take values weights (Z.to_nat (φ iw)) (Z.to_N (φ (k - 1)))
                    = (row.[k - 1] <? row.[k - 1 - xw.[iw]] + xv.[iw])).
    { unfold take.
      replace (W weights (Z.to_nat (φ iw)) <=? Z.to_N (φ (k - 1)))%N with true
        by (symmetry; apply N.leb_le; lia).
      simpl. apply eq_true_iff_eq. rewrite N.ltb_lt, ltb_spec, Hcand, Hr1, Hr2, Hv.
      lia. }
    assert (Hset : (k - 1 <? PArray.length row) = true)
      by (rewrite ltb_spec, Hrl, HC1; lia).
    destruct (row.[k - 1] <? row.[k - 1 - xw.[iw]] + xv.[iw]) eqn:Ecmp.
    + refine (IH (φ (k - 1)) _ _ _ _ _ Heq eq_refl _ _ _ _ _ _).
      * unfold Zwf. lia.
      * lia.
      * rewrite alength_set. exact Hrl.
      * rewrite blength_set. exact Hdl.
      * intros c Hc. rewrite aget_set_other by (intro E; subst c; lia).
        apply Hlo. lia.
      * intros c Hc. destruct (Z.eq_dec (φ c) ((φ k) - 1)) as [E|E].
        -- assert (c = k - 1) by (apply to_Z_inj; lia). subst c.
           rewrite aget_set_same by exact Hset.
           rewrite Hcand, Hr1, Hv, best_S, Etake. lia.
        -- rewrite aget_set_other by (intro E'; subst c; lia). apply Hhi. lia.
      * intros iw' c Hiw' Hc.
        destruct (Z.eq_dec (φ iw') (φ iw)) as [E1|E1];
          [destruct (Z.eq_dec (φ c) ((φ k) - 1)) as [E2|E2]|].
        -- assert (iw' = iw) by (apply to_Z_inj; exact E1).
           assert (c = k - 1) by (apply to_Z_inj; lia). subst iw' c.
           rewrite bget_set_same by (rewrite Hdl; apply idx_in; lia).
           rewrite dexp_here, Etake. reflexivity.
        -- rewrite bget_set_other by (apply idx_neq; lia).
           rewrite Hdec by lia. rewrite EkN.
           rewrite dexp_other; [reflexivity | lia | lia].
        -- rewrite bget_set_other by (apply idx_neq; lia).
           rewrite Hdec by lia. rewrite EkN.
           rewrite dexp_other; [reflexivity | lia | lia].
    + refine (IH (φ (k - 1)) _ _ _ _ _ Heq eq_refl _ _ _ _ _ _).
      * unfold Zwf. lia.
      * lia.
      * exact Hrl.
      * exact Hdl.
      * intros c Hc. apply Hlo. lia.
      * intros c Hc. destruct (Z.eq_dec (φ c) ((φ k) - 1)) as [E|E].
        -- assert (c = k - 1) by (apply to_Z_inj; lia). subst c.
           rewrite best_S, Etake. exact Hr2.
        -- apply Hhi. lia.
      * intros iw' c Hiw' Hc. rewrite (Hdec iw' c Hiw' Hc).
        destruct (Z.eq_dec (φ iw') (φ iw)) as [E1|E1];
          [destruct (Z.eq_dec (φ c) ((φ k) - 1)) as [E2|E2]|].
        -- assert (iw' = iw) by (apply to_Z_inj; exact E1).
           assert (c = k - 1) by (apply to_Z_inj; lia). subst iw' c.
           rewrite dexp_here, Etake. rewrite EkN.
           apply dexp_here_old. lia.
        -- rewrite EkN. rewrite dexp_other; [reflexivity | lia | lia].
        -- rewrite EkN. rewrite dexp_other; [reflexivity | lia | lia].
  - cbv beta iota zeta in Heq. injection Heq as <- <-.
    rewrite <- not_true_iff_false, ltb_spec in Hk'.
    split; [exact Hrl|]. split; [exact Hdl|]. split.
    + intros c Hc. destruct (Z_lt_le_dec (φ c) (φ k)).
      * rewrite Hlo by lia. rewrite best_S, take_small by lia. reflexivity.
      * apply Hhi. lia.
    + intros iw' c Hiw' Hc. rewrite Hdec by lia.
      apply dexp_end; [lia|]. intro Hck. apply take_small. lia.
Qed.

(* The outer loop: items iw .. n-1. *)
Lemma items_loop_spec : forall z (iw : int) (row : array int) (dec : array bool)
    (H : Acc (Zwf 0) (gap LEN iw)),
  gap LEN iw = z -> ((φ iw) <= Z.of_nat nN)%Z ->
  PArray.length row = C1 -> PArray.length dec = LEN * C1 ->
  row_inv row (Z.to_nat (φ iw)) -> dec_inv dec (Z.to_nat (φ iw)) (Z.to_N ((φ Cw) + 1)) ->
  row_inv (fst (items_loop xv xw LEN C1 iw row dec H)) nN /\
  dec_inv (snd (items_loop xv xw LEN C1 iw row dec H)) nN (Z.to_N ((φ Cw) + 1)).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros iw row dec H Hz Hi Hrl Hdl Hrow Hdec.
  pose proof LEN_val as HL. pose proof C1_val as HC1. pose proof nN_bounds.
  pose proof (to_Z_bounded iw) as Biw.
  rewrite items_loop_eq. destruct (bdec (iw <? LEN)) as [Hi'|Hi'].
  - cbv beta iota zeta. pose proof Hi' as Hlt. rewrite ltb_spec, HL in Hlt.
    assert (Hi1 : (φ (iw + 1)) = ((φ iw) + 1)%Z) by sia.
    pose proof (item_loop_spec iw Hlt _ _ _ C1 row dec (Zwf_well_founded 0 (φ C1))
                  (surjective_pairing _) eq_refl
                  ltac:(lia) Hrl Hdl
                  ltac:(intros c Hc; apply Hrow; lia)
                  ltac:(intros c Hc; lia)
                  ltac:(rewrite HC1; exact Hdec)) as (Hrl1 & Hdl1 & Hrow1 & Hdec1).
    assert (En : Z.to_nat (φ (iw + 1)) = S (Z.to_nat (φ iw))) by lia.
    apply (IH (gap LEN (iw + 1)));
      [ rewrite <- Hz; apply dec_step; exact Hi' | reflexivity | lia
      | exact Hrl1 | exact Hdl1 | rewrite En; exact Hrow1 | rewrite En; exact Hdec1 ].
  - rewrite <- not_true_iff_false, ltb_spec, HL in Hi'. cbn [fst snd].
    replace (Z.to_nat (φ iw)) with nN in * by lia. split; assumption.
Qed.

(* The walk back. *)
Lemma walk_spec : forall dec : array bool, dec_inv dec nN (Z.to_N ((φ Cw) + 1)) ->
  forall (k' : int) (out' : array int) z (i c k : int) (out : array int)
         (H : Acc (Zwf 0) (φ i)),
  walk xw dec C1 i c k out H = (k', out') ->
  (φ i) = z -> ((φ i) <= Z.of_nat nN)%Z -> ((φ c) <= (φ Cw))%Z ->
  ((φ k) + (φ i) <= Z.of_nat nN)%Z ->
  PArray.length out = LEN ->
  (φ k') = ((φ k) + Z.of_nat (List.length (recon values weights (Z.to_nat (φ i)) (Z.to_N (φ c)))))%Z /\
  PArray.length out' = LEN /\
  (forall j : int, ((φ j) < (φ k))%Z -> out'.[j] = out.[j]) /\
  (forall j : int, ((φ k) <= (φ j) < (φ k'))%Z ->
     Z.to_N (φ (out'.[j]))
     = nth (Z.to_nat ((φ j) - (φ k))) (recon values weights (Z.to_nat (φ i)) (Z.to_N (φ c))) 0%N).
Proof.
  intros dec Hdec k' out' z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i c k out H Heq Hz Hi Hc Hk Hol. subst z.
  pose proof LEN_val as HL. pose proof nN_bounds. pose proof Cz_val. pose proof C_bounds.
  pose proof (to_Z_bounded i) as Bi. pose proof (to_Z_bounded k) as Bk.
  pose proof (to_Z_bounded c) as Bc.
  rewrite walk_eq in Heq. destruct (bdec (0 <? i)) as [Hi'|Hi'].
  - cbv beta iota zeta in Heq. pose proof Hi' as Hlt. rewrite ltb_spec in Hlt.
    change (φ 0) with 0%Z in Hlt.
    assert (Ei : (φ (i - 1)) = ((φ i) - 1)%Z) by sia.
    assert (En : Z.to_nat (φ i) = S (Z.to_nat (φ (i - 1)))) by lia.
    rewrite En, recon_S.
    rewrite (Hdec (i - 1) c ltac:(lia) Hc) in Heq.
    unfold dexp in Heq. rewrite (proj2 (Nat.ltb_lt (Z.to_nat (φ (i - 1))) nN) ltac:(lia)) in Heq.
    cbv beta iota in Heq.
    pose proof (get_w (i - 1) ltac:(lia)) as Hw.
    destruct (take values weights (Z.to_nat (φ (i - 1))) (Z.to_N (φ c))) eqn:Et.
    + apply take_true in Et. destruct Et as [Etw _].
      pose proof (to_Z_bounded (xw.[i - 1])) as Bw.
      assert (Ecw : (φ (c - xw.[i - 1])) = ((φ c) - (φ (xw.[i - 1])))%Z) by sia.
      assert (EcN : Z.to_N (φ (c - xw.[i - 1]))
                    = (Z.to_N (φ c) - W weights (Z.to_nat (φ (i - 1))))%N) by lia.
      assert (Ek1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
      destruct (IH (φ (i - 1)) ltac:(unfold Zwf; lia) _ _ _ _ _ Heq eq_refl
                  ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(rewrite alength_set; exact Hol)) as (Hk' & Hl' & Hpre & Hpost).
      rewrite EcN in Hk', Hpost.
      split; [rewrite Hk', Ek1; cbn [List.length]; lia|].
      split; [exact Hl'|].
      split.
      * intros j Hj. rewrite Hpre by lia. apply aget_set_other. intro E; subst j; lia.
      * intros j Hj. destruct (Z.eq_dec (φ j) (φ k)) as [E|E].
        -- assert (j = k) by (apply to_Z_inj; exact E). subst j.
           rewrite Hpre by lia. rewrite aget_set_same by (rewrite ltb_spec, Hol, HL; lia).
           replace ((φ k) - (φ k))%Z with 0%Z by lia. simpl. lia.
        -- rewrite Hpost by lia.
           replace (Z.to_nat ((φ j) - (φ k))) with (S (Z.to_nat ((φ j) - (φ (k + 1))))) by lia.
           reflexivity.
    + destruct (IH (φ (i - 1)) ltac:(unfold Zwf; lia) _ _ _ _ _ Heq eq_refl
                  ltac:(lia) ltac:(lia) ltac:(lia) Hol) as (Hk' & Hl' & Hpre & Hpost).
      split; [exact Hk'|]. split; [exact Hl'|]. split; [exact Hpre | exact Hpost].
  - cbv beta iota zeta in Heq. injection Heq as <- <-.
    rewrite <- not_true_iff_false, ltb_spec in Hi'. change (φ 0) with 0%Z in Hi'.
    replace (Z.to_nat (φ i)) with 0%nat by lia. cbn [recon List.length].
    split; [lia|]. split; [exact Hol|]. split; [reflexivity|]. intros j Hj; lia.
Qed.

(* The final copy. *)
Lemma copy_loop_spec : forall (src : array int) (m : int) z (j : int)
    (dst : array int) (H : Acc (Zwf 0) (gap m j)),
  gap m j = z -> ((φ j) <= (φ m))%Z -> PArray.length dst = m ->
  (forall j' : int, ((φ j') < (φ j))%Z -> dst.[j'] = src.[j']) ->
  PArray.length (copy_loop src dst m j H) = m /\
  forall j' : int, ((φ j') < (φ m))%Z -> (copy_loop src dst m j H).[j'] = src.[j'].
Proof.
  intros src m z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j dst H Hz Hjm Hl Hinv.
  rewrite copy_loop_eq. destruct (bdec (j <? m)) as [Hj|Hj].
  - pose proof Hj as Hj'. rewrite ltb_spec in Hj'.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    eapply IH; [ | reflexivity | | | ].
    + rewrite <- Hz. apply dec_step. exact Hj.
    + lia.
    + rewrite alength_set. exact Hl.
    + intros j' Hj''. destruct (Z.eq_dec (φ j') (φ j)) as [E|E].
      * assert (j' = j) by (apply to_Z_inj; exact E). subst j'.
        apply aget_set_same. rewrite Hl. exact Hj.
      * rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity).
        apply Hinv. lia.
  - rewrite <- not_true_iff_false, ltb_spec in Hj.
    split; [exact Hl|]. intros j' Hj'. apply Hinv. lia.
Qed.

Lemma knapsack_impl_correct_sec : exists r : N * list N,
  @repr (uint * array uint) (N * list N) _ (knapsack_impl Cw xv xw) r /\
  knapsack_spec C values weights r.
Proof.
  pose proof Cz_val as HCz. pose proof C_bounds as HCb. pose proof nN_bounds as Hnb.
  pose proof LEN_val as HL. pose proof C1_val as HC1. pose proof LC_val as HLC.
  assert (HmR : PArray.length (PArray.make C1 0) = C1).
  { rewrite alength_make. replace (C1 <=? max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  assert (HmD : PArray.length (PArray.make (LEN * C1) false) = LEN * C1).
  { rewrite blength_make. replace (LEN * C1 <=? max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val, HLC. nia. }
  assert (Hrow0 : row_inv (PArray.make C1 0) (Z.to_nat (φ 0))).
  { intros c Hc. rewrite aget_make. reflexivity. }
  assert (Hdec0 : dec_inv (PArray.make (LEN * C1) false) (Z.to_nat (φ 0)) (Z.to_N ((φ Cw) + 1))).
  { intros iw c Hiw Hc. rewrite bget_make. symmetry.
    change (Z.to_nat (φ 0)) with O. apply dexp_init. lia. }
  pose proof (items_loop_spec _ 0 (PArray.make C1 0) (PArray.make (LEN * C1) false)
                (Zwf_well_founded 0 (gap LEN 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; lia) HmR HmD Hrow0 Hdec0) as [Hrow Hdec].
  unfold knapsack_impl. cbv zeta.
  revert Hrow Hdec.
  destruct (items_loop xv xw LEN C1 0 (PArray.make C1 0) (PArray.make (LEN * C1) false)
              (Zwf_well_founded 0 (gap LEN 0))) as [row dec].
  cbn [fst snd]. intros Hrow Hdec.
  assert (HmO : PArray.length (PArray.make LEN 0) = LEN).
  { rewrite alength_make. replace (LEN <=? max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  destruct (walk xw dec C1 LEN Cw 0 (PArray.make LEN 0) (Zwf_well_founded 0 (φ LEN)))
    as [k' out'] eqn:Ew.
  destruct (walk_spec dec Hdec k' out' _ LEN Cw 0 (PArray.make LEN 0) _ Ew eq_refl
              ltac:(lia) ltac:(lia) ltac:(change (φ 0) with 0%Z; lia) HmO)
    as (Hk' & _ & _ & Hpost).
  change (φ 0) with 0%Z in Hk', Hpost.
  replace (Z.to_nat (φ LEN)) with nN in Hk', Hpost by lia.
  replace (Z.to_N (φ Cw)) with C in Hk', Hpost by lia.
  cbn [fst snd].
  pose proof (recon_length values weights nN C) as Hrlen.
  assert (HmK : PArray.length (PArray.make k' 0) = k').
  { rewrite alength_make. replace (k' <=? max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  destruct (copy_loop_spec out' k' _ 0 (PArray.make k' 0) (Zwf_well_founded 0 (gap k' 0))
              eq_refl ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded k'); lia) HmK
              ltac:(intros j' Hj'; change (φ 0) with 0%Z in Hj';
                    pose proof (to_Z_bounded j'); lia)) as [Hrl Hrc].
  set (res := copy_loop out' (PArray.make k' 0) k' 0 (Zwf_well_founded 0 (gap k' 0))) in *.
  exists (B nN C, recon values weights nN C).
  split.
  - split.
    + cbn [fst]. unfold repr, repr_uint.
      rewrite (Hrow Cw ltac:(lia)). replace (Z.to_N (φ Cw)) with C by lia. lia.
    + cbn [snd]. split.
      * transitivity (φ k'); [lia|]. f_equal. symmetry. exact Hrl.
      * intros m Hm. exists (nth m (recon values weights nN C) 0%N).
        split; [apply nth_error_nth'; exact Hm|].
        assert (Hm' : (φ (of_Z (Z.of_nat m))) = Z.of_nat m).
        { rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia. }
        assert (G : Z.to_N (φ (res.[of_Z (Z.of_nat m)])) = nth m (recon values weights nN C) 0%N).
        { rewrite Hrc by lia. rewrite Hpost by lia. rewrite Hm'. f_equal. lia. }
        exact G.
  - unfold knapsack_spec. cbn [fst snd]. split; [|split; [|split]].
    + split; [apply recon_nodup|].
      eapply Forall_impl; [|apply recon_bound]. unfold len. intros x Hx; cbv beta in *; lia.
    + apply recon_weight.
    + symmetry. apply recon_value.
    + intros l [Hnd Hb] Hw. apply best_opt; [exact Hnd | exact Hb | exact Hw].
Qed.

End Proofs.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition knapsack : uint -> array uint -> array uint -> uint * array uint
  := knapsack_impl.

Definition knapsack_correct :
  forall (C : N) (values weights : list N)
         (xC : uint) (xv xw : array uint),
  valid_input C values weights ->
  repr xC C -> repr xv values -> repr xw weights ->
  exists r : N * list N,
    repr (knapsack xC xv xw) r /\ knapsack_spec C values weights r
  := knapsack_impl_correct_sec.
