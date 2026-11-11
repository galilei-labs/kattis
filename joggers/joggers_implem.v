(* Implementation of joggers (joggers.spec).  See README.md, section
   Implementation, for the algorithm and the structure of the proof. *)

From Joggers.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Reals Lra Permutation.
Import ListNotations.

Notation getl := Prelude.get.

Open Scope bool_scope.
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

Lemma dec_lt : forall i j : int,
  (i <? j) = true -> Zwf 0 (gap max_int (i + 1)) (gap max_int i).
Proof.
  intros i j H. rewrite ltb_spec in H.
  pose proof (to_Z_bounded j). change (φ max_int) with (wB - 1)%Z.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_down : forall i : int, (0 <? i) = true -> Zwf 0 (φ (i - 1)) (φ i).
Proof.
  intros i H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  assert (H1 : (φ (i - 1)) = ((φ i) - 1)%Z) by sia.
  unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Half-edge k (0 <= k < 2m): trail k seen from a_k when k < m, trail
   k - m seen from b_{k-m} otherwise.  [ep] is its tail, [oth] its head,
   [eid] its trail. *)
Definition ep (xa xb : array int) (m k : int) : int :=
  if k <? m then xa.[k] else xb.[k - m].
Definition oth (xa xb : array int) (m k : int) : int :=
  if k <? m then xb.[k] else xa.[k - m].
Definition eid (m k : int) : int := if k <? m then k else k - m.

(* inl.[x] := true for every lamp x of xl *)
Fixpoint lamp_loop (xl : array int) (L i : int) (inl : array bool)
    (H : Acc (Zwf 0) (gap L i)) {struct H} : array bool :=
  match bdec (i <? L) with
  | left Hi => lamp_loop xl L (i + 1) inl.[xl.[i] <- true]
                 (Acc_inv H (dec_step L i Hi))
  | right _ => inl
  end.

(* degree count: cnt.[w] = number of half-edges with tail w *)
Fixpoint cnt_loop (xa xb : array int) (m K i : int) (cnt : array int)
    (H : Acc (Zwf 0) (gap K i)) {struct H} : array int :=
  match bdec (i <? K) with
  | left Hi =>
      let w := ep xa xb m i in
      cnt_loop xa xb m K (i + 1) cnt.[w <- cnt.[w] + 1]
        (Acc_inv H (dec_step K i Hi))
  | right _ => cnt
  end.

(* CSR offsets (prefix sums) and a copy of them as fill cursors *)
Fixpoint off_loop (cnt : array int) (V v : int) (off cur : array int)
    (H : Acc (Zwf 0) (gap V v)) {struct H} : array int * array int :=
  match bdec (v <? V) with
  | left Hv =>
      let o := off.[v] in
      off_loop cnt V (v + 1) off.[v + 1 <- o + cnt.[v]] cur.[v <- o]
        (Acc_inv H (dec_step V v Hv))
  | right _ => (off, cur)
  end.

(* CSR targets: the half-edges of w at slots off.[w] .. off.[w+1]-1 *)
Fixpoint fill_loop (xa xb : array int) (m K i : int) (cur adj : array int)
    (H : Acc (Zwf 0) (gap K i)) {struct H} : array int :=
  match bdec (i <? K) with
  | left Hi =>
      let w := ep xa xb m i in
      let c := cur.[w] in
      fill_loop xa xb m K (i + 1) cur.[w <- c + 1] adj.[c <- i]
        (Acc_inv H (dec_step K i Hi))
  | right _ => adj
  end.

(* The state of the traversal from the campus. *)
Record bst : Type := Bst {
  vis : array bool;   (* visited *)
  dst : array int;    (* distance from the campus *)
  par : array int;    (* parent intersection *)
  pe  : array int;    (* trail to the parent *)
  ord : array int;    (* visit order (the queue) *)
  tl  : int           (* queue tail *)
}.

(* Scan the slots i .. hi-1 of intersection u (at distance du). *)
Fixpoint scan_loop (xa xb xd : array int) (m : int) (adj : array int)
    (u du hi i : int) (st : bst) (H : Acc (Zwf 0) (gap hi i)) {struct H} : bst :=
  match bdec (i <? hi) with
  | left Hi =>
      let k := adj.[i] in
      let w := oth xa xb m k in
      let st' :=
        if (vis st).[w] then st
        else
          let e := eid m k in
          Bst ((vis st).[w <- true]) ((dst st).[w <- du + xd.[e]])
              ((par st).[w <- u]) ((pe st).[w <- e])
              ((ord st).[tl st <- w]) (tl st + 1) in
      scan_loop xa xb xd m adj u du hi (i + 1) st' (Acc_inv H (dec_step hi i Hi))
  | right _ => st
  end.

(* Breadth-first traversal: pop the queue at h. *)
Fixpoint bfs_loop (xa xb xd : array int) (m : int) (adj off : array int)
    (h : int) (st : bst) (H : Acc (Zwf 0) (gap max_int h)) {struct H} : bst :=
  match bdec (h <? tl st) with
  | left Hh =>
      let u := (ord st).[h] in
      let st' := scan_loop xa xb xd m adj u ((dst st).[u]) off.[u + 1] off.[u] st
                   (Zwf_well_founded 0 _) in
      bfs_loop xa xb xd m adj off (h + 1) st' (Acc_inv H (dec_lt h (tl st) Hh))
  | right _ => st
  end.

(* Bottom-up sweep, in reverse visit order: a used trail from v to its
   parent p with neither end lit gets a new lamp at p. *)
Fixpoint sweep_loop (s : int) (inl : array bool) (ord par dst : array int)
    (i : int) (ch : array bool) (c : int) (H : Acc (Zwf 0) (φ i)) {struct H} : int :=
  match bdec (0 <? i) with
  | left Hi =>
      let v := ord.[i] in
      let p := par.[v] in
      let dp := dst.[p] in
      if (dp + dp <? s) && negb (inl.[v] || ch.[v]) && negb (inl.[p] || ch.[p])
      then sweep_loop s inl ord par dst (i - 1) ch.[p <- true] (c + 1)
             (Acc_inv H (dec_down i Hi))
      else sweep_loop s inl ord par dst (i - 1) ch c (Acc_inv H (dec_down i Hi))
  | right _ => c
  end.

Definition joggers_impl (n s : int) (xa xb xd xl : array int) : int :=
  let m := PArray.length xa in
  let K := m + m in
  let V := n + 1 in
  let inl := lamp_loop xl (PArray.length xl) 0 (PArray.make V false)
               (Zwf_well_founded 0 _) in
  let cnt := cnt_loop xa xb m K 0 (PArray.make V 0) (Zwf_well_founded 0 _) in
  let oc := off_loop cnt V 0 (PArray.make (V + 1) 0) (PArray.make V 0)
              (Zwf_well_founded 0 _) in
  let adj := fill_loop xa xb m K 0 (snd oc) (PArray.make K 0)
               (Zwf_well_founded 0 _) in
  let st0 := Bst ((PArray.make V false).[1 <- true]) (PArray.make V 0)
                 (PArray.make V 0) (PArray.make V 0)
                 ((PArray.make n 0).[0 <- 1]) 1 in
  let st := bfs_loop xa xb xd m adj (fst oc) 0 st0 (Zwf_well_founded 0 _) in
  sweep_loop s inl (ord st) (par st) (dst st) (tl st - 1) (PArray.make V false) 0
    (Zwf_well_founded 0 _).

(* Unfolding equations *)
Lemma lamp_loop_eq : forall xl L i inl H,
  lamp_loop xl L i inl H =
  match bdec (i <? L) with
  | left Hi => lamp_loop xl L (i + 1) inl.[xl.[i] <- true]
                 (Acc_inv H (dec_step L i Hi))
  | right _ => inl
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma cnt_loop_eq : forall xa xb m K i cnt H,
  cnt_loop xa xb m K i cnt H =
  match bdec (i <? K) with
  | left Hi =>
      let w := ep xa xb m i in
      cnt_loop xa xb m K (i + 1) cnt.[w <- cnt.[w] + 1]
        (Acc_inv H (dec_step K i Hi))
  | right _ => cnt
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma off_loop_eq : forall cnt V v off cur H,
  off_loop cnt V v off cur H =
  match bdec (v <? V) with
  | left Hv =>
      let o := off.[v] in
      off_loop cnt V (v + 1) off.[v + 1 <- o + cnt.[v]] cur.[v <- o]
        (Acc_inv H (dec_step V v Hv))
  | right _ => (off, cur)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma fill_loop_eq : forall xa xb m K i cur adj H,
  fill_loop xa xb m K i cur adj H =
  match bdec (i <? K) with
  | left Hi =>
      let w := ep xa xb m i in
      let c := cur.[w] in
      fill_loop xa xb m K (i + 1) cur.[w <- c + 1] adj.[c <- i]
        (Acc_inv H (dec_step K i Hi))
  | right _ => adj
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma scan_loop_eq : forall xa xb xd m adj u du hi i st H,
  scan_loop xa xb xd m adj u du hi i st H =
  match bdec (i <? hi) with
  | left Hi =>
      let k := adj.[i] in
      let w := oth xa xb m k in
      let st' :=
        if (vis st).[w] then st
        else
          let e := eid m k in
          Bst ((vis st).[w <- true]) ((dst st).[w <- du + xd.[e]])
              ((par st).[w <- u]) ((pe st).[w <- e])
              ((ord st).[tl st <- w]) (tl st + 1) in
      scan_loop xa xb xd m adj u du hi (i + 1) st' (Acc_inv H (dec_step hi i Hi))
  | right _ => st
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma bfs_loop_eq : forall xa xb xd m adj off h st H,
  bfs_loop xa xb xd m adj off h st H =
  match bdec (h <? tl st) with
  | left Hh =>
      let u := (ord st).[h] in
      let st' := scan_loop xa xb xd m adj u ((dst st).[u]) off.[u + 1] off.[u] st
                   (Zwf_well_founded 0 _) in
      bfs_loop xa xb xd m adj off (h + 1) st' (Acc_inv H (dec_lt h (tl st) Hh))
  | right _ => st
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma sweep_loop_eq : forall s inl ord par dst i ch c H,
  sweep_loop s inl ord par dst i ch c H =
  match bdec (0 <? i) with
  | left Hi =>
      let v := ord.[i] in
      let p := par.[v] in
      let dp := dst.[p] in
      if (dp + dp <? s) && negb (inl.[v] || ch.[v]) && negb (inl.[p] || ch.[p])
      then sweep_loop s inl ord par dst (i - 1) ch.[p <- true] (c + 1)
             (Acc_inv H (dec_down i Hi))
      else sweep_loop s inl ord par dst (i - 1) ch c (Acc_inv H (dec_down i Hi))
  | right _ => c
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Finite sums                                                         *)
(* ------------------------------------------------------------------ *)

Fixpoint sumN (f : nat -> Z) (k : nat) : Z :=
  match k with O => 0%Z | S k' => (sumN f k' + f k')%Z end.

Lemma sumN_ext : forall f g k, (forall i, (i < k)%nat -> f i = g i) ->
  sumN f k = sumN g k.
Proof.
  intros f g k; induction k as [|k IH]; intros E; simpl; [reflexivity|].
  rewrite IH by (intros; apply E; lia). rewrite E by lia. reflexivity.
Qed.

Lemma sumN_add : forall f g k,
  sumN (fun i => f i + g i)%Z k = (sumN f k + sumN g k)%Z.
Proof. intros f g k; induction k as [|k IH]; simpl; lia. Qed.

Lemma sumN_nonneg : forall f k, (forall i, 0 <= f i)%Z -> (0 <= sumN f k)%Z.
Proof. intros f k Hf; induction k as [|k IH]; simpl; [lia|]. specialize (Hf k); lia. Qed.

Lemma sumN_mono : forall f k1 k2, (forall i, 0 <= f i)%Z -> (k1 <= k2)%nat ->
  (sumN f k1 <= sumN f k2)%Z.
Proof.
  intros f k1 k2 Hf Hk. induction Hk as [|k2 Hk IH]; [lia|]. simpl.
  specialize (Hf k2); lia.
Qed.

Lemma sumN_le : forall f g k, (forall i, (i < k)%nat -> f i <= g i)%Z ->
  (sumN f k <= sumN g k)%Z.
Proof.
  intros f g k; induction k as [|k IH]; intros E; simpl; [lia|].
  specialize (IH ltac:(intros; apply E; lia)). specialize (E k ltac:(lia)). lia.
Qed.

Lemma sumN_indicator : forall (e : Z) k,
  sumN (fun w => if Z.eqb e (Z.of_nat w) then 1 else 0)%Z k
  = (if (0 <=? e)%Z && (e <? Z.of_nat k)%Z then 1 else 0)%Z.
Proof.
  intros e k; induction k as [|k IH]; simpl.
  - destruct (Z.leb_spec 0 e); destruct (Z.ltb_spec e 0); simpl; lia.
  - rewrite IH, Zpos_P_of_succ_nat. destruct (Z.eqb_spec e (Z.of_nat k)) as [E|E];
    destruct (Z.leb_spec 0 e); destruct (Z.ltb_spec e (Z.of_nat k));
    destruct (Z.ltb_spec e (Z.succ (Z.of_nat k))); simpl; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The CSR adjacency                                                   *)
(* ------------------------------------------------------------------ *)

Section CSR.
Variables (xa xb : array int) (m V : int).
Hypothesis Hm : ((φ m) <= 100000)%Z.
Hypothesis HV : (1 <= (φ V) <= 100000)%Z.
Hypothesis Hep : forall k : int, ((φ k) < 2 * (φ m))%Z ->
  (1 <= (φ (ep xa xb m k)) < (φ V))%Z.

Definition epz (i : nat) : Z := (φ (ep xa xb m (of_Z (Z.of_nat i)))).
Definition cntN (k : nat) (w : Z) : Z :=
  sumN (fun i => if Z.eqb (epz i) w then 1 else 0)%Z k.
Definition K2 : nat := Z.to_nat (2 * (φ m)).
Definition offZ (w : Z) : Z := sumN (fun v => cntN K2 (Z.of_nat v)) (Z.to_nat w).

Lemma epz_int : forall i : int, epz (Z.to_nat (φ i)) = (φ (ep xa xb m i)).
Proof.
  intros i. unfold epz. rewrite Z2Nat.id by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z. reflexivity.
Qed.

Lemma K_val : (φ (m + m)) = (2 * (φ m))%Z.
Proof. pose proof (to_Z_bounded m). sia. Qed.

Lemma cntN_S : forall k w,
  cntN (S k) w = (cntN k w + if Z.eqb (epz k) w then 1 else 0)%Z.
Proof. reflexivity. Qed.

Lemma cntN_mono : forall k1 k2 w, (k1 <= k2)%nat -> (cntN k1 w <= cntN k2 w)%Z.
Proof.
  intros. unfold cntN. apply sumN_mono; [|lia].
  intros i; destruct (Z.eqb _ _); lia.
Qed.

Lemma cntN_le : forall k w, (0 <= cntN k w <= Z.of_nat k)%Z.
Proof.
  intros k w; induction k as [|k IH]; [change (cntN 0 w) with 0%Z; simpl; lia|].
  rewrite cntN_S. destruct (Z.eqb _ _); lia.
Qed.

Lemma offZ_S : forall w, (0 <= w)%Z -> offZ (w + 1) = (offZ w + cntN K2 w)%Z.
Proof.
  intros w Hw. unfold offZ. rewrite Z2Nat.inj_add by lia.
  rewrite Nat.add_1_r. simpl. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma offZ_mono : forall w1 w2, (w1 <= w2)%Z -> (offZ w1 <= offZ w2)%Z.
Proof.
  intros. unfold offZ. apply sumN_mono; [|lia].
  intros; apply cntN_le.
Qed.

Lemma offZ_nonneg : forall w, (0 <= offZ w)%Z.
Proof. intros. unfold offZ. apply sumN_nonneg. intros; apply cntN_le. Qed.

Lemma offZ_total_gen : forall k v,
  (sumN (fun w => cntN k (Z.of_nat w)) v <= Z.of_nat k)%Z.
Proof.
  intros k v; induction k as [|k IH].
  - simpl. rewrite (sumN_ext _ (fun _ => 0%Z)) by (intros; reflexivity).
    clear. induction v; simpl; lia.
  - rewrite (sumN_ext _ (fun w => cntN k (Z.of_nat w) +
        (if Z.eqb (epz k) (Z.of_nat w) then 1 else 0))%Z)
      by (intros; apply cntN_S).
    rewrite sumN_add, sumN_indicator.
    destruct (_ && _); lia.
Qed.

Lemma offZ_total : forall w, (offZ w <= 2 * (φ m))%Z.
Proof.
  intros w. unfold offZ. eapply Z.le_trans; [apply offZ_total_gen|].
  unfold K2. pose proof (to_Z_bounded m). lia.
Qed.

(* the cells of the slots of distinct intersections are disjoint *)
Lemma slot_disj : forall w1 w2 x y : Z, (0 <= w1)%Z -> (0 <= w2)%Z -> w1 <> w2 ->
  (offZ w1 <= x < offZ (w1 + 1))%Z -> (offZ w2 <= y < offZ (w2 + 1))%Z -> x <> y.
Proof.
  intros w1 w2 x y H1 H2 Hne Hx Hy.
  destruct (Z.lt_total w1 w2) as [L|[L|L]]; [|contradiction|].
  - pose proof (offZ_mono (w1 + 1) w2 ltac:(lia)). lia.
  - pose proof (offZ_mono (w2 + 1) w1 ltac:(lia)). lia.
Qed.

Lemma cnt_loop_spec : forall z (i : int) (cnt : array int) H,
  gap (m + m) i = z ->
  ((φ i) <= (φ (m + m)))%Z ->
  PArray.length cnt = V ->
  (forall w : int, ((φ w) < (φ V))%Z -> (φ (cnt.[w])) = cntN (Z.to_nat (φ i)) (φ w)) ->
  PArray.length (cnt_loop xa xb m (m + m) i cnt H) = V /\
  forall w : int, ((φ w) < (φ V))%Z ->
    (φ ((cnt_loop xa xb m (m + m) i cnt H).[w])) = cntN K2 (φ w).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i cnt H Hz Hi Hl Hc.
  rewrite cnt_loop_eq. destruct (bdec (i <? m + m)) as [Hk|Hk].
  - pose proof Hk as Hk'. rewrite ltb_spec in Hk'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    pose proof (to_Z_bounded i) as Bi.
    pose proof (Hep i ltac:(rewrite K_val in Hk'; lia)) as Hw.
    cbv zeta.
    eapply IH; [ | reflexivity | lia | | ].
    + rewrite <- Hz. apply dec_step. exact Hk.
    + rewrite alength_set. exact Hl.
    + intros w Hw'. rewrite Hi1, Z2Nat.inj_add, Nat.add_1_r by lia.
      rewrite cntN_S, epz_int.
      destruct (eqs (ep xa xb m i) w) as [E|E].
      * subst w. rewrite aget_set_same by (rewrite Hl; rewrite ltb_spec; lia).
        rewrite Z.eqb_refl.
        pose proof (cntN_le (Z.to_nat (φ i)) (φ (ep xa xb m i))).
        rewrite add_spec, Hc by lia. change (φ 1) with 1%Z.
        rewrite Z.mod_small; [lia|]. rewrite wB_val. lia.
      * rewrite aget_set_other by exact E. rewrite Hc by exact Hw'.
        destruct (Z.eqb_spec (φ (ep xa xb m i)) (φ w)) as [E'|E'];
          [apply to_Z_inj in E'; contradiction | lia].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk.
    split; [exact Hl|]. intros w Hw. rewrite Hc by exact Hw.
    unfold K2. rewrite <- K_val. f_equal. lia.
Qed.

Section Off.
Variable cnt : array int.
Hypothesis Hcl : PArray.length cnt = V.
Hypothesis Hcc : forall w : int, ((φ w) < (φ V))%Z -> (φ (cnt.[w])) = cntN K2 (φ w).

Lemma off_loop_spec : forall z (v : int) (off cur : array int) H,
  gap V v = z ->
  ((φ v) <= (φ V))%Z ->
  PArray.length off = V + 1 -> PArray.length cur = V ->
  (forall w : int, ((φ w) <= (φ v))%Z -> (φ (off.[w])) = offZ (φ w)) ->
  (forall w : int, ((φ w) < (φ v))%Z -> (φ (cur.[w])) = offZ (φ w)) ->
  let r := off_loop cnt V v off cur H in
  PArray.length (fst r) = V + 1 /\ PArray.length (snd r) = V /\
  (forall w : int, ((φ w) <= (φ V))%Z -> (φ ((fst r).[w])) = offZ (φ w)) /\
  (forall w : int, ((φ w) < (φ V))%Z -> (φ ((snd r).[w])) = offZ (φ w)).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros v off cur H Hz Hv Hlo Hlc Ho Hc.
  rewrite off_loop_eq. destruct (bdec (v <? V)) as [Hk|Hk].
  - pose proof Hk as Hk'. rewrite ltb_spec in Hk'.
    assert (Hv1 : (φ (v + 1)) = ((φ v) + 1)%Z) by sia.
    assert (HV1 : (φ (V + 1)) = ((φ V) + 1)%Z) by sia.
    pose proof (to_Z_bounded v) as Bv.
    cbv zeta.
    eapply IH; [ | reflexivity | lia | | | | ].
    + rewrite <- Hz. apply dec_step. exact Hk.
    + rewrite alength_set. exact Hlo.
    + rewrite alength_set. exact Hlc.
    + intros w Hw. rewrite Hv1 in Hw.
      destruct (eqs (v + 1) w) as [E|E].
      * subst w. rewrite aget_set_same by (rewrite Hlo, ltb_spec; lia).
        rewrite Hv1, offZ_S by lia.
        pose proof (offZ_total (φ v)). pose proof (offZ_nonneg (φ v)).
        pose proof (cntN_le K2 (φ v)).
        rewrite add_spec, Ho, Hcc by lia.
        rewrite Z.mod_small; [lia|]. rewrite wB_val. unfold K2 in *.
        pose proof (to_Z_bounded m). lia.
      * rewrite aget_set_other by exact E. apply Ho.
        assert ((φ w) <> (φ (v + 1))) by (intro F; apply E; apply to_Z_inj; auto).
        lia.
    + intros w Hw. rewrite Hv1 in Hw.
      destruct (eqs v w) as [E|E].
      * subst w. rewrite aget_set_same by (rewrite Hlc, ltb_spec; lia).
        apply Ho. lia.
      * rewrite aget_set_other by exact E. apply Hc.
        assert ((φ w) <> (φ v)) by (intro F; apply E; apply to_Z_inj; auto).
        lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk.
    simpl. split; [exact Hlo|]. split; [exact Hlc|].
    split; intros w Hw; [apply Ho | apply Hc]; lia.
Qed.
End Off.

Section Fill.
Variable off : array int.
Hypothesis Hoff : forall w : int, ((φ w) <= (φ V))%Z -> (φ (off.[w])) = offZ (φ w).

Lemma fill_loop_spec : forall z (i : int) (cur adj : array int) H,
  gap (m + m) i = z ->
  ((φ i) <= (φ (m + m)))%Z ->
  PArray.length cur = V -> PArray.length adj = m + m ->
  (forall w : int, ((φ w) < (φ V))%Z ->
     (φ (cur.[w])) = (offZ (φ w) + cntN (Z.to_nat (φ i)) (φ w))%Z) ->
  (forall (w sl : int), ((φ w) < (φ V))%Z -> (offZ (φ w) <= (φ sl) < (φ (cur.[w])))%Z ->
     ep xa xb m adj.[sl] = w /\ ((φ (adj.[sl])) < (φ i))%Z) ->
  (forall k : int, ((φ k) < (φ i))%Z -> exists sl : int,
     (offZ (φ (ep xa xb m k)) <= (φ sl) < (φ (cur.[ep xa xb m k])))%Z /\ adj.[sl] = k) ->
  let r := fill_loop xa xb m (m + m) i cur adj H in
  (forall (w sl : int), ((φ w) < (φ V))%Z ->
     ((φ (off.[w])) <= (φ sl) < (φ (off.[w + 1])))%Z ->
     ep xa xb m r.[sl] = w /\ ((φ (r.[sl])) < 2 * (φ m))%Z) /\
  (forall k : int, ((φ k) < 2 * (φ m))%Z -> exists sl : int,
     ((φ (off.[ep xa xb m k])) <= (φ sl) < (φ (off.[ep xa xb m k + 1])))%Z /\ r.[sl] = k).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i cur adj H Hz Hi Hlc Hla Hcur Hsound Hcomp.
  rewrite fill_loop_eq. destruct (bdec (i <? m + m)) as [Hk|Hk].
  - pose proof Hk as Hk'. rewrite ltb_spec, K_val in Hk'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    pose proof (to_Z_bounded i) as Bi.
    set (w := ep xa xb m i).
    pose proof (Hep i ltac:(lia)) as Hw. fold w in Hw.
    (* the write position *)
    assert (Hc : (φ (cur.[w])) = (offZ (φ w) + cntN (Z.to_nat (φ i)) (φ w))%Z)
      by (apply Hcur; lia).
    assert (HS : cntN (S (Z.to_nat (φ i))) (φ w) = (cntN (Z.to_nat (φ i)) (φ w) + 1)%Z).
    { rewrite cntN_S, epz_int. fold w. rewrite Z.eqb_refl. reflexivity. }
    assert (HSle : (cntN (S (Z.to_nat (φ i))) (φ w) <= cntN K2 (φ w))%Z).
    { apply cntN_mono. unfold K2. lia. }
    assert (Hw1 : offZ ((φ w) + 1) = (offZ (φ w) + cntN K2 (φ w))%Z)
      by (apply offZ_S; lia).
    assert (Hcw : ((φ (cur.[w])) < offZ ((φ w) + 1))%Z) by lia.
    pose proof (offZ_total ((φ w) + 1)).
    pose proof (offZ_nonneg (φ w)).
    pose proof (cntN_le (Z.to_nat (φ i)) (φ w)).
    assert (Hc1 : (φ (cur.[w] + 1)) = ((φ (cur.[w])) + 1)%Z).
    { rewrite add_spec. change (φ 1) with 1%Z. apply Z.mod_small.
      rewrite wB_val. lia. }
    assert (Hcin : (cur.[w] <? PArray.length adj) = true).
    { rewrite Hla, ltb_spec, K_val. lia. }
    (* bound on any cursor *)
    assert (Hcb : forall w' : int, ((φ w') < (φ V))%Z ->
              (offZ (φ w') <= (φ (cur.[w'])) <= offZ ((φ w') + 1))%Z).
    { intros w' Hw'. rewrite Hcur by exact Hw'.
      rewrite offZ_S by (pose proof (to_Z_bounded w'); lia).
      pose proof (cntN_mono (Z.to_nat (φ i)) K2 (φ w') ltac:(unfold K2; lia)).
      pose proof (cntN_le (Z.to_nat (φ i)) (φ w')). lia. }
    cbv zeta. fold w.
    eapply IH; [ | reflexivity | lia | | | | | ].
    + rewrite <- Hz. apply dec_step. exact Hk.
    + rewrite alength_set. exact Hlc.
    + rewrite alength_set. exact Hla.
    + intros w' Hw'. rewrite Hi1, Z2Nat.inj_add, Nat.add_1_r by lia.
      destruct (eqs w w') as [E|E].
      * subst w'. rewrite aget_set_same by (rewrite Hlc, ltb_spec; lia).
        rewrite Hc1, Hc, HS. lia.
      * rewrite aget_set_other by exact E. rewrite Hcur by exact Hw'.
        rewrite cntN_S, epz_int. fold w.
        destruct (Z.eqb_spec (φ w) (φ w')) as [E'|E'];
          [apply to_Z_inj in E'; contradiction | lia].
    + intros w' sl Hw' Hsl.
      destruct (eqs cur.[w] sl) as [Es|Es].
      * subst sl. rewrite aget_set_same by exact Hcin.
        destruct (eqs w w') as [E|E]; [split; [exact E | lia]|].
        exfalso.
        rewrite aget_set_other in Hsl by exact E.
        pose proof (Hcb w' Hw').
        apply (slot_disj (φ w) (φ w') (φ (cur.[w])) (φ (cur.[w])));
          try (pose proof (to_Z_bounded w); pose proof (to_Z_bounded w'); lia).
        all: try (intro F; apply E; apply to_Z_inj; exact F).
      * rewrite aget_set_other by exact Es.
        assert (Hsl' : (offZ (φ w') <= (φ sl) < (φ (cur.[w'])))%Z).
        { destruct (eqs w w') as [E|E].
          - subst w'. rewrite aget_set_same in Hsl by (rewrite Hlc, ltb_spec; lia).
            rewrite Hc1 in Hsl.
            assert ((φ sl) <> (φ (cur.[w]))) by (intro F; apply Es; apply to_Z_inj; auto).
            lia.
          - rewrite aget_set_other in Hsl by exact E. exact Hsl. }
        destruct (Hsound w' sl Hw' Hsl') as [S1 S2]. split; [exact S1 | lia].
    + intros k Hk2. rewrite Hi1 in Hk2.
      destruct (eqs k i) as [Ek|Ek].
      * subst k. fold w. exists (cur.[w]).
        rewrite aget_set_same by (rewrite Hlc, ltb_spec; lia).
        rewrite aget_set_same by exact Hcin. rewrite Hc1. split; [lia | reflexivity].
      * assert (Hk3 : ((φ k) < (φ i))%Z)
          by (assert ((φ k) <> (φ i)) by (intro F; apply Ek; apply to_Z_inj; auto); lia).
        destruct (Hcomp k Hk3) as (sl & Hsl & Ha).
        pose proof (Hep k ltac:(lia)) as Hwk.
        exists sl.
        assert (Es : sl <> cur.[w]).
        { intro F. subst sl.
          destruct (eqs (ep xa xb m k) w) as [E|E].
          - rewrite E in Hsl. lia.
          - pose proof (Hcb (ep xa xb m k) ltac:(lia)).
            apply (slot_disj (φ w) (φ (ep xa xb m k)) (φ (cur.[w])) (φ (cur.[w])));
              try lia.
            all: try (intro F; apply E; apply to_Z_inj; auto). }
        rewrite (aget_set_other adj (cur.[w]) sl i) by (intro F; apply Es; auto).
        split; [|exact Ha].
        destruct (eqs w (ep xa xb m k)) as [E|E].
        -- rewrite <- E in *. rewrite aget_set_same by (rewrite Hlc, ltb_spec; lia).
           lia.
        -- rewrite aget_set_other by exact E. exact Hsl.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk.
    assert (Hfin : forall w : int, ((φ w) < (φ V))%Z -> (φ (cur.[w])) = offZ ((φ w) + 1)).
    { intros w Hw. rewrite Hcur by exact Hw.
      rewrite offZ_S by (pose proof (to_Z_bounded w); lia).
      f_equal. f_equal. unfold K2. rewrite <- K_val. lia. }
    assert (Hoff1 : forall w : int, ((φ w) < (φ V))%Z ->
              (φ (off.[w + 1])) = offZ ((φ w) + 1)).
    { intros w Hw. assert ((φ (w + 1)) = ((φ w) + 1)%Z) by sia.
      rewrite Hoff by lia. f_equal. lia. }
    cbv zeta. split.
    + intros w sl Hw Hsl. rewrite Hoff in Hsl by lia. rewrite Hoff1 in Hsl by exact Hw.
      rewrite <- Hfin in Hsl by exact Hw.
      destruct (Hsound w sl Hw Hsl) as [S1 S2]. split; [exact S1|].
      rewrite K_val in Hi. lia.
    + intros k Hk2. rewrite K_val in Hk. destruct (Hcomp k ltac:(lia)) as (sl & Hsl & Ha).
      pose proof (Hep k Hk2) as Hwk.
      exists sl. rewrite Hoff by lia. rewrite Hoff1 by lia.
      rewrite <- Hfin by lia. split; [exact Hsl | exact Ha].
Qed.
End Fill.
End CSR.

(* ------------------------------------------------------------------ *)
(* Pigeonholes                                                         *)
(* ------------------------------------------------------------------ *)

Lemma map_inj_NoDup : forall (g : nat -> Z) T,
  (forall t1 t2, (t1 < T)%nat -> (t2 < T)%nat -> g t1 = g t2 -> t1 = t2) ->
  NoDup (map g (seq 0 T)).
Proof.
  intros g T Hi. apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
  intros x y Hx Hy E. apply in_seq in Hx, Hy. apply Hi; lia.
Qed.

Lemma pigeon_le : forall (g : nat -> Z) T (lo hi : Z), (lo <= hi)%Z ->
  (forall t, (t < T)%nat -> (lo <= g t < hi)%Z) ->
  (forall t1 t2, (t1 < T)%nat -> (t2 < T)%nat -> g t1 = g t2 -> t1 = t2) ->
  (Z.of_nat T <= hi - lo)%Z.
Proof.
  intros g T lo hi Hlh Hr Hi.
  assert (Hlen := @NoDup_incl_length _ (map g (seq 0 T))
            (map (fun i => lo + Z.of_nat i)%Z (seq 0 (Z.to_nat (hi - lo))))
            (map_inj_NoDup g T Hi)).
  rewrite !length_map, !length_seq in Hlen.
  destruct T as [|T']; [lia|].
  assert (hi - lo >= 1)%Z by (specialize (Hr 0%nat ltac:(lia)); lia).
  enough (Z.of_nat (S T') <= Z.of_nat (Z.to_nat (hi - lo)))%Z by lia.
  apply Nat2Z.inj_le. apply Hlen.
  intros y Hy. apply in_map_iff in Hy. destruct Hy as (t & <- & Ht).
  apply in_seq in Ht. specialize (Hr t ltac:(lia)).
  apply in_map_iff. exists (Z.to_nat (g t - lo)). split; [lia|].
  apply in_seq. lia.
Qed.

Lemma cover_le : forall (g : nat -> Z) T (lo : Z) M,
  (forall i, (i < M)%nat -> exists t, (t < T)%nat /\ g t = (lo + Z.of_nat i)%Z) ->
  (M <= T)%nat.
Proof.
  intros g T lo M H.
  assert (Hn : NoDup (map (fun i => lo + Z.of_nat i)%Z (seq 0 M))).
  { apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
    intros x y _ _ E. lia. }
  pose proof (@NoDup_incl_length _ _ (map g (seq 0 T)) Hn) as L.
  rewrite !length_map, !length_seq in L. apply L.
  intros y Hy. apply in_map_iff in Hy. destruct Hy as (i & <- & Hi).
  apply in_seq in Hi. destruct (H i ltac:(lia)) as (t & Ht & E).
  apply in_map_iff. exists t. split; [exact E|]. apply in_seq. lia.
Qed.

Lemma pigeon_surj : forall (g : nat -> Z) T M,
  (forall t, (t < T)%nat -> (0 <= g t < Z.of_nat M)%Z) ->
  (forall t1 t2, (t1 < T)%nat -> (t2 < T)%nat -> g t1 = g t2 -> t1 = t2) ->
  (M <= T)%nat ->
  forall e, (0 <= e < Z.of_nat M)%Z -> exists t, (t < T)%nat /\ g t = e.
Proof.
  intros g T M Hr Hi HM e He.
  assert (Hincl := @NoDup_length_incl _ (map g (seq 0 T))
            (map Z.of_nat (seq 0 M)) (map_inj_NoDup g T Hi)).
  rewrite !length_map, !length_seq in Hincl.
  assert (Hin : In e (map Z.of_nat (seq 0 M))).
  { apply in_map_iff. exists (Z.to_nat e). split; [lia|]. apply in_seq. lia. }
  apply Hincl in Hin; [| exact HM |].
  - apply in_map_iff in Hin. destruct Hin as (t & E & Ht). apply in_seq in Ht.
    exists t. split; [lia | exact E].
  - intros y Hy. apply in_map_iff in Hy. destruct Hy as (t & <- & Ht).
    apply in_seq in Ht. specialize (Hr t ltac:(lia)).
    apply in_map_iff. exists (Z.to_nat (g t)). split; [lia|]. apply in_seq. lia.
Qed.

Lemma neq_lt : forall x y : int, ((φ x) < (φ y) \/ (φ y) < (φ x))%Z -> x <> y.
Proof. intros x y H E. subst. lia. Qed.

Lemma phi_ofZ : forall z, (0 <= z < wB)%Z -> (φ (of_Z z)) = z.
Proof. intros z Hz. rewrite of_Z_spec. apply Z.mod_small. exact Hz. Qed.

Lemma bset_mono : forall (t : array bool) (w x : int),
  (w <? PArray.length t) = true -> t.[x] = true -> t.[w <- true].[x] = true.
Proof.
  intros t w x Hw Hx. destruct (eqs w x) as [E|E].
  - subst. apply bget_set_same. exact Hw.
  - rewrite bget_set_other by exact E. exact Hx.
Qed.

(* ------------------------------------------------------------------ *)
(* The traversal from the campus                                       *)
(* ------------------------------------------------------------------ *)

Section BFS.
Variables (xa xb xd : array int) (m n : int) (adj off : array int).
Hypothesis Hn : (2 <= (φ n) <= 50000)%Z.
Hypothesis Hmn : (φ m) = ((φ n) - 1)%Z.
Hypothesis HA : forall k : int, ((φ k) < (φ m))%Z -> (1 <= (φ (xa.[k])) <= (φ n))%Z.
Hypothesis HB : forall k : int, ((φ k) < (φ m))%Z -> (1 <= (φ (xb.[k])) <= (φ n))%Z.
Hypothesis HD : forall k : int, ((φ k) < (φ m))%Z -> (1 <= (φ (xd.[k])) <= 100)%Z.
Hypothesis HC1 : forall u sl : int, (1 <= (φ u) <= (φ n))%Z ->
  ((φ (off.[u])) <= (φ sl) < (φ (off.[u + 1])))%Z ->
  ep xa xb m (adj.[sl]) = u /\ ((φ (adj.[sl])) < 2 * (φ m))%Z.
Hypothesis HC2 : forall k : int, ((φ k) < 2 * (φ m))%Z -> exists sl : int,
  ((φ (off.[ep xa xb m k])) <= (φ sl) < (φ (off.[ep xa xb m k + 1])))%Z /\ adj.[sl] = k.

Definition rel (e p w : int) : Prop :=
  (xa.[e] = p /\ xb.[e] = w) \/ (xb.[e] = p /\ xa.[e] = w).

Lemma n1_val : (φ (n + 1)) = ((φ n) + 1)%Z.
Proof. sia. Qed.

Lemma he_facts : forall k : int, ((φ k) < 2 * (φ m))%Z ->
  ((φ (eid m k)) < (φ m))%Z /\ rel (eid m k) (ep xa xb m k) (oth xa xb m k) /\
  (1 <= (φ (oth xa xb m k)) <= (φ n))%Z /\ (1 <= (φ (ep xa xb m k)) <= (φ n))%Z.
Proof.
  intros k Hk. unfold eid, oth, ep, rel.
  destruct (k <? m) eqn:E.
  - rewrite ltb_spec in E. repeat split; auto; try apply HA; try apply HB; auto.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E.
    assert ((φ (k - m)) = ((φ k) - (φ m))%Z) by sia.
    repeat split; [lia | | apply HA; lia | apply HA; lia | apply HB; lia | apply HB; lia].
    right; split; reflexivity.
Qed.

Record Inv (h : int) (st : bst) : Prop := {
  iv_lv : PArray.length (vis st) = n + 1;
  iv_ld : PArray.length (dst st) = n + 1;
  iv_lp : PArray.length (par st) = n + 1;
  iv_le : PArray.length (pe st) = n + 1;
  iv_lo : PArray.length (ord st) = n;
  iv_tl : (1 <= (φ (tl st)) <= (φ n))%Z;
  iv_h : ((φ h) <= (φ (tl st)))%Z;
  iv_o0 : (ord st).[0] = 1;
  iv_ord : forall t : int, ((φ t) < (φ (tl st)))%Z ->
     (1 <= (φ ((ord st).[t])) <= (φ n))%Z /\ (vis st).[(ord st).[t]] = true;
  iv_vis : forall v : int, (1 <= (φ v) <= (φ n))%Z -> (vis st).[v] = true ->
     exists t : int, ((φ t) < (φ (tl st)))%Z /\ (ord st).[t] = v;
  iv_inj : forall t1 t2 : int, ((φ t1) < (φ (tl st)))%Z -> ((φ t2) < (φ (tl st)))%Z ->
     (ord st).[t1] = (ord st).[t2] -> t1 = t2;
  iv_d1 : (dst st).[1] = 0;
  iv_tree : forall t : int, (0 < (φ t) < (φ (tl st)))%Z ->
     ((φ ((pe st).[(ord st).[t]])) < (φ m))%Z /\
     rel ((pe st).[(ord st).[t]]) ((par st).[(ord st).[t]]) ((ord st).[t]) /\
     (exists t' : int, ((φ t') < (φ t))%Z /\ (ord st).[t'] = (par st).[(ord st).[t]]) /\
     (φ ((dst st).[(ord st).[t]])) =
       ((φ ((dst st).[(par st).[(ord st).[t]]])) + (φ (xd.[(pe st).[(ord st).[t]]])))%Z;
  iv_db : forall t : int, ((φ t) < (φ (tl st)))%Z ->
     ((φ ((dst st).[(ord st).[t]])) <= 100 * (φ t))%Z;
  iv_done : forall t : int, ((φ t) < (φ h))%Z -> forall k : int, ((φ k) < 2 * (φ m))%Z ->
     ep xa xb m k = (ord st).[t] -> (vis st).[oth xa xb m k] = true
}.

Lemma push_inv : forall h V0 D0 P0 E0 O0 T0 u du w e,
  Inv h (Bst V0 D0 P0 E0 O0 T0) -> ((φ h) < (φ T0))%Z -> O0.[h] = u -> D0.[u] = du ->
  (1 <= (φ w) <= (φ n))%Z -> V0.[w] = false -> ((φ e) < (φ m))%Z -> rel e u w ->
  Inv h (Bst V0.[w <- true] D0.[w <- du + xd.[e]] P0.[w <- u] E0.[w <- e]
             O0.[T0 <- w] (T0 + 1)).
Proof.
  intros h V0 D0 P0 E0 O0 T0 u du w e Hinv Hh Hu Hdu Hw Hvw He Hrel.
  destruct Hinv as [Lv Ld Lp Le Lo Tl Hh' O0eq Ord Vis Inj D1 Tree Db Done].
  cbn [vis dst par pe ord tl] in *.
  pose proof n1_val as N1.
  destruct (Ord h Hh) as [Hu1 Hvu]. rewrite Hu in Hu1, Hvu.
  assert (Hwne : forall t : int, ((φ t) < (φ T0))%Z -> O0.[t] <> w).
  { intros t Ht E. destruct (Ord t Ht) as [_ V1]. rewrite E, Hvw in V1. discriminate. }
  assert (Huw : u <> w) by (rewrite <- Hu; apply Hwne; exact Hh).
  assert (HT : ((φ T0) < (φ n))%Z).
  { pose (g := fun t : nat => if Nat.ltb t (Z.to_nat (φ T0))
                 then (φ (O0.[of_Z (Z.of_nat t)])) else (φ w)).
    assert (Hg : forall t, (t < Z.to_nat (φ T0))%nat ->
               g t = (φ (O0.[of_Z (Z.of_nat t)])) /\ ((φ (of_Z (Z.of_nat t))) = Z.of_nat t)%Z).
    { intros t Ht. unfold g. destruct (Nat.ltb_spec t (Z.to_nat (φ T0))); [|lia].
      split; [reflexivity|]. apply phi_ofZ. rewrite wB_val. lia. }
    assert (Hg' : forall t, (t >= Z.to_nat (φ T0))%nat -> g t = (φ w)).
    { intros t Ht. unfold g. destruct (Nat.ltb_spec t (Z.to_nat (φ T0))); [lia|].
      reflexivity. }
    pose proof (pigeon_le g (S (Z.to_nat (φ T0))) 1 ((φ n) + 1) ltac:(lia)) as P.
    enough (Z.of_nat (S (Z.to_nat (φ T0))) <= (φ n) + 1 - 1)%Z by lia.
    apply P.
    - intros t Ht. destruct (Nat.ltb_spec t (Z.to_nat (φ T0))) as [L|L].
      + destruct (Hg t L) as [-> P2]. destruct (Ord (of_Z (Z.of_nat t)) ltac:(lia)). lia.
      + rewrite Hg' by lia. lia.
    - intros t1 t2 H1 H2 E.
      destruct (Nat.ltb_spec t1 (Z.to_nat (φ T0))) as [L1|L1];
      destruct (Nat.ltb_spec t2 (Z.to_nat (φ T0))) as [L2|L2].
      + destruct (Hg t1 L1) as [G1 P1]. destruct (Hg t2 L2) as [G2 P2].
        rewrite G1, G2 in E. apply to_Z_inj in E.
        apply Inj in E; [|lia|lia]. apply (f_equal to_Z) in E. lia.
      + destruct (Hg t1 L1) as [G1 P1]. rewrite G1, (Hg' t2) in E by lia.
        apply to_Z_inj in E. exfalso. revert E. apply Hwne. lia.
      + destruct (Hg t2 L2) as [G2 P2]. rewrite G2, (Hg' t1) in E by lia.
        apply to_Z_inj in E. exfalso. symmetry in E. revert E. apply Hwne. lia.
      + lia. }
  assert (T1 : (φ (T0 + 1)) = ((φ T0) + 1)%Z) by sia.
  assert (Bw : (w <? n + 1) = true) by (rewrite ltb_spec; lia).
  assert (BT : (T0 <? n) = true) by (rewrite ltb_spec; lia).
  assert (Hdu_b : ((φ du) <= 100 * (φ h))%Z) by (rewrite <- Hdu, <- Hu; apply Db; lia).
  assert (Hde : (φ (du + xd.[e])) = ((φ du) + (φ (xd.[e])))%Z).
  { pose proof (HD e He). rewrite add_spec. apply Z.mod_small. rewrite wB_val.
    pose proof (to_Z_bounded du). lia. }
  assert (O0T : forall t : int, ((φ t) < (φ T0))%Z -> O0.[T0 <- w].[t] = O0.[t]).
  { intros t Ht. apply aget_set_other. apply neq_lt. lia. }
  split; cbn [vis dst par pe ord tl].
  - rewrite blength_set; exact Lv.
  - rewrite alength_set; exact Ld.
  - rewrite alength_set; exact Lp.
  - rewrite alength_set; exact Le.
  - rewrite alength_set; exact Lo.
  - lia.
  - lia.
  - rewrite O0T by (change (φ 0) with 0%Z; lia). exact O0eq.
  - intros t Ht. destruct (eqs T0 t) as [E|E].
    + subst t. rewrite aget_set_same by (rewrite Lo; exact BT).
      rewrite bget_set_same by (rewrite Lv; exact Bw). split; [lia | reflexivity].
    + assert (Ht' : ((φ t) < (φ T0))%Z)
        by (assert ((φ T0) <> (φ t)) by (intro F; apply E; apply to_Z_inj; exact F); lia).
      rewrite O0T by exact Ht'. destruct (Ord t Ht') as [O1 O2].
      split; [exact O1|]. apply bset_mono; [rewrite Lv; exact Bw | exact O2].
  - intros v Hv HV. destruct (eqs w v) as [E|E].
    + subst v. exists T0. split; [lia|].
      apply aget_set_same. rewrite Lo; exact BT.
    + rewrite bget_set_other in HV by exact E.
      destruct (Vis v Hv HV) as (t & Ht & Ot). exists t. split; [lia|].
      rewrite O0T by exact Ht. exact Ot.
  - intros t1 t2 H1 H2 E.
    destruct (eqs T0 t1) as [E1|E1]; destruct (eqs T0 t2) as [E2|E2].
    + congruence.
    + subst t1. rewrite aget_set_same in E by (rewrite Lo; exact BT).
      assert (Ht2 : ((φ t2) < (φ T0))%Z)
        by (assert ((φ T0) <> (φ t2)) by (intro F; apply E2; apply to_Z_inj; exact F); lia).
      rewrite O0T in E by exact Ht2. exfalso. symmetry in E. revert E. apply Hwne. exact Ht2.
    + subst t2. rewrite (aget_set_same O0) in E by (rewrite Lo; exact BT).
      assert (Ht1 : ((φ t1) < (φ T0))%Z)
        by (assert ((φ T0) <> (φ t1)) by (intro F; apply E1; apply to_Z_inj; exact F); lia).
      rewrite O0T in E by exact Ht1. exfalso. revert E. apply Hwne. exact Ht1.
    + assert (Ht1 : ((φ t1) < (φ T0))%Z)
        by (assert ((φ T0) <> (φ t1)) by (intro F; apply E1; apply to_Z_inj; exact F); lia).
      assert (Ht2 : ((φ t2) < (φ T0))%Z)
        by (assert ((φ T0) <> (φ t2)) by (intro F; apply E2; apply to_Z_inj; exact F); lia).
      rewrite !O0T in E by assumption. apply Inj; assumption.
  - rewrite aget_set_other; [exact D1|].
    intro F. apply (Hwne 0 ltac:(change (φ 0) with 0%Z; lia)). rewrite O0eq. symmetry; exact F.
  - intros t Ht. destruct (eqs T0 t) as [E|E].
    + subst t. rewrite aget_set_same by (rewrite Lo; exact BT).
      rewrite (aget_set_same E0) by (rewrite Le; exact Bw).
      rewrite (aget_set_same P0) by (rewrite Lp; exact Bw).
      rewrite (aget_set_same D0) by (rewrite Ld; exact Bw).
      rewrite (aget_set_other D0 w u) by (intro F; apply Huw; symmetry; exact F).
      split; [exact He|]. split; [exact Hrel|]. split.
      * exists h. split; [lia|]. rewrite O0T by exact Hh. exact Hu.
      * rewrite Hdu. exact Hde.
    + assert (Ht' : ((φ t) < (φ T0))%Z)
        by (assert ((φ T0) <> (φ t)) by (intro F; apply E; apply to_Z_inj; exact F); lia).
      rewrite O0T by exact Ht'.
      assert (Hx : w <> O0.[t]) by (intro F; symmetry in F; revert F; apply Hwne; exact Ht').
      rewrite (aget_set_other E0 w) by exact Hx.
      rewrite (aget_set_other P0 w) by exact Hx.
      rewrite (aget_set_other D0 w (O0.[t])) by exact Hx.
      destruct (Tree t ltac:(lia)) as (T1' & T2 & (t' & Ht'' & Ot') & T4).
      assert (Hp : w <> P0.[O0.[t]])
        by (rewrite <- Ot'; intro F; symmetry in F; revert F; apply Hwne; lia).
      rewrite (aget_set_other D0 w (P0.[O0.[t]])) by exact Hp.
      split; [exact T1'|]. split; [exact T2|]. split; [|exact T4].
      exists t'. split; [exact Ht''|]. rewrite O0T by lia. exact Ot'.
  - intros t Ht. destruct (eqs T0 t) as [E|E].
    + subst t. rewrite aget_set_same by (rewrite Lo; exact BT).
      rewrite (aget_set_same D0) by (rewrite Ld; exact Bw).
      rewrite Hde. pose proof (HD e He). lia.
    + assert (Ht' : ((φ t) < (φ T0))%Z)
        by (assert ((φ T0) <> (φ t)) by (intro F; apply E; apply to_Z_inj; exact F); lia).
      rewrite O0T by exact Ht'.
      assert (Hx : w <> O0.[t]) by (intro F; symmetry in F; revert F; apply Hwne; exact Ht').
      rewrite (aget_set_other D0 w) by exact Hx. apply Db. exact Ht'.
  - intros t Ht k Hk Ek. rewrite O0T in Ek by lia.
    apply bset_mono; [rewrite Lv; exact Bw|]. exact (Done t Ht k Hk Ek).
Qed.

Lemma scan_spec : forall h u du hi z i st H,
  gap hi i = z -> Inv h st -> ((φ h) < (φ (tl st)))%Z -> (ord st).[h] = u ->
  (dst st).[u] = du -> hi = off.[u + 1] -> ((φ (off.[u])) <= (φ i))%Z ->
  (forall sl : int, ((φ (off.[u])) <= (φ sl) < (φ i))%Z ->
     (vis st).[oth xa xb m (adj.[sl])] = true) ->
  let r := scan_loop xa xb xd m adj u du hi i st H in
  Inv h r /\ ((φ h) < (φ (tl r)))%Z /\ (ord r).[h] = u /\ (dst r).[u] = du /\
  (forall sl : int, ((φ (off.[u])) <= (φ sl) < (φ hi))%Z ->
     (vis r).[oth xa xb m (adj.[sl])] = true).
Proof.
  intros h u du hi z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i st H Hz Hinv Hh Hu Hdu Hhi Hi Hsl.
  rewrite scan_loop_eq. destruct (bdec (i <? hi)) as [Hk|Hk].
  - pose proof Hk as Hk'. rewrite ltb_spec in Hk'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    pose proof (iv_ord h st Hinv h Hh) as [Hu1 Hvu]. rewrite Hu in Hu1, Hvu.
    destruct (HC1 u i Hu1 ltac:(subst hi; lia)) as [Hep Hk2].
    destruct (he_facts (adj.[i]) Hk2) as (He & Hrel & Hw & _).
    rewrite Hep in Hrel.
    cbv zeta.
    destruct st as [V0 D0 P0 E0 O0 T0]. cbn [vis dst par pe ord tl] in *.
    destruct (V0.[oth xa xb m (adj.[i])]) eqn:Hv.
    + eapply IH; [ | reflexivity | exact Hinv | exact Hh | exact Hu | exact Hdu
                 | exact Hhi | lia | ].
      * rewrite <- Hz. apply dec_step. exact Hk.
      * intros sl Hs. cbn [vis].
        destruct (eqs sl i) as [E|E]; [subst sl; exact Hv|].
        apply Hsl. assert ((φ sl) <> (φ i)) by (intro F; apply E; apply to_Z_inj; exact F).
        lia.
    + set (w := oth xa xb m (adj.[i])) in *.
      set (e := eid m (adj.[i])) in *.
      pose proof (push_inv h V0 D0 P0 E0 O0 T0 u du w e Hinv Hh Hu Hdu Hw Hv He Hrel)
        as Hinv'.
      pose proof (iv_lv h _ Hinv) as Lv. pose proof (iv_lo h _ Hinv) as Lo.
      pose proof (iv_tl h _ Hinv) as Tl. cbn [vis ord tl] in Lv, Lo, Tl.
      pose proof (iv_tl h _ Hinv') as Tl'. cbn [tl] in Tl'.
      pose proof n1_val as N1.
      assert (Huw : u <> w) by (intro F; rewrite F in Hvu; congruence).
      eapply IH; [ | reflexivity | exact Hinv' | | | | exact Hhi | lia | ];
        cbn [vis dst par pe ord tl].
      * rewrite <- Hz. apply dec_step. exact Hk.
      * assert ((φ (T0 + 1)) = ((φ T0) + 1)%Z) by sia. lia.
      * rewrite aget_set_other by (apply neq_lt; lia). exact Hu.
      * rewrite aget_set_other by (intro F; apply Huw; symmetry; exact F). exact Hdu.
      * intros sl Hs.
        destruct (eqs sl i) as [E|E].
        { subst sl. fold w. apply bget_set_same. rewrite Lv, ltb_spec; lia. }
        apply bset_mono; [rewrite Lv, ltb_spec; lia|].
        apply Hsl. assert ((φ sl) <> (φ i)) by (intro F; apply E; apply to_Z_inj; exact F).
        lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk.
    cbv zeta. split; [exact Hinv|]. split; [exact Hh|]. split; [exact Hu|].
    split; [exact Hdu|].
    intros sl Hs. apply Hsl. lia.
Qed.

Lemma inv_next : forall h st u, Inv h st -> ((φ h) < (φ (tl st)))%Z -> (ord st).[h] = u ->
  (forall sl : int, ((φ (off.[u])) <= (φ sl) < (φ (off.[u + 1])))%Z ->
     (vis st).[oth xa xb m (adj.[sl])] = true) ->
  Inv (h + 1) st.
Proof.
  intros h st u Hinv Hh Hu Hsl.
  assert (H1 : (φ (h + 1)) = ((φ h) + 1)%Z) by (pose proof (iv_tl h st Hinv); sia).
  destruct Hinv as [Lv Ld Lp Le Lo Tl Hh' O0eq Ord Vis Inj D1 Tree Db Done].
  split; try assumption.
  - lia.
  - intros t Ht k Hk Ek. destruct (eqs t h) as [E|E].
    + subst t. rewrite Hu in Ek. destruct (HC2 k Hk) as (sl & Hs & Ha).
      rewrite <- Ha. apply Hsl. rewrite Ek in Hs. exact Hs.
    + apply (Done t) with (k := k); try assumption.
      assert ((φ t) <> (φ h)) by (intro F; apply E; apply to_Z_inj; exact F). lia.
Qed.

Lemma bfs_spec : forall z h st H, gap max_int h = z -> Inv h st ->
  Inv (tl (bfs_loop xa xb xd m adj off h st H)) (bfs_loop xa xb xd m adj off h st H).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros h st H Hz Hinv.
  rewrite bfs_loop_eq. destruct (bdec (h <? tl st)) as [Hk|Hk].
  - pose proof Hk as Hk'. rewrite ltb_spec in Hk'.
    cbv zeta.
    set (u := (ord st).[h]).
    destruct (scan_spec h u ((dst st).[u]) (off.[u + 1]) _ (off.[u]) st
                (Zwf_well_founded 0 (gap (off.[u + 1]) (off.[u])))
                eq_refl Hinv Hk' eq_refl eq_refl eq_refl ltac:(lia)
                ltac:(intros; lia)) as (Hi' & Hh' & Hu' & _ & Hsl).
    eapply IH; [ | reflexivity | ].
    + rewrite <- Hz. eapply dec_lt. exact Hk.
    + eapply inv_next; eassumption.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk.
    pose proof (iv_h h st Hinv).
    assert (E : h = tl st) by (apply to_Z_inj; lia).
    rewrite <- E. exact Hinv.
Qed.

Lemma init_inv :
  Inv 0 (Bst ((PArray.make (n + 1) false).[1 <- true]) (PArray.make (n + 1) 0)
             (PArray.make (n + 1) 0) (PArray.make (n + 1) 0)
             ((PArray.make n 0).[0 <- 1]) 1).
Proof.
  pose proof n1_val as N1.
  assert (LV : PArray.length (PArray.make (n + 1) 0) = n + 1).
  { rewrite alength_make. replace (n + 1 <=? max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  assert (LB : PArray.length (PArray.make (n + 1) false) = n + 1).
  { rewrite blength_make. replace (n + 1 <=? max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  assert (LN : PArray.length (PArray.make n 0) = n).
  { rewrite alength_make. replace (n <=? max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  assert (O0 : ((PArray.make n 0).[0 <- 1]).[0] = 1).
  { apply aget_set_same. rewrite LN, ltb_spec. change (φ 0) with 0%Z. lia. }
  assert (T0 : forall t : int, ((φ t) < (φ 1))%Z -> t = 0).
  { intros t Ht. change (φ 1) with 1%Z in Ht. pose proof (to_Z_bounded t).
    apply to_Z_inj. change (φ 0) with 0%Z. lia. }
  split; cbn [vis dst par pe ord tl].
  - rewrite blength_set. exact LB.
  - exact LV.
  - exact LV.
  - exact LV.
  - rewrite alength_set. exact LN.
  - change (φ 1) with 1%Z. lia.
  - change (φ 1) with 1%Z. change (φ 0) with 0%Z. lia.
  - exact O0.
  - intros t Ht. rewrite (T0 t Ht), O0. change (φ 1) with 1%Z. split; [lia|].
    apply bget_set_same. rewrite LB, ltb_spec. change (φ 1) with 1%Z. lia.
  - intros v Hv HV. destruct (eqs 1 v) as [E|E].
    + subst v. exists 0. split; [reflexivity | exact O0].
    + rewrite bget_set_other, bget_make in HV by exact E. discriminate.
  - intros t1 t2 H1 H2 _. rewrite (T0 t1 H1), (T0 t2 H2). reflexivity.
  - apply aget_make.
  - intros t Ht. change (φ 1) with 1%Z in Ht. lia.
  - intros t Ht. rewrite (T0 t Ht), aget_make. change (φ 0) with 0%Z. lia.
  - intros t Ht. change (φ 0) with 0%Z in Ht. pose proof (to_Z_bounded t). lia.
Qed.
End BFS.

(* ------------------------------------------------------------------ *)
(* The bottom-up sweep                                                 *)
(* ------------------------------------------------------------------ *)

Lemma NoDup_middle : forall (A : Type) (l l' : list A) (a : A),
  NoDup (a :: l ++ l') -> NoDup (l ++ a :: l').
Proof.
  intros A l l' a H. eapply Permutation_NoDup; [|exact H].
  apply Permutation_middle.
Qed.

Section Sweep.
Variables (s : int) (inl : array bool) (O P D : array int) (T n : int).
Hypothesis Hn : (2 <= (φ n) <= 50000)%Z.
Hypothesis HT : (1 <= (φ T) <= (φ n))%Z.
Hypothesis HO : forall t : int, ((φ t) < (φ T))%Z -> (1 <= (φ (O.[t])) <= (φ n))%Z.
Hypothesis Hinj : forall t1 t2 : int, ((φ t1) < (φ T))%Z -> ((φ t2) < (φ T))%Z ->
  O.[t1] = O.[t2] -> t1 = t2.
Hypothesis HP : forall t : int, (0 < (φ t) < (φ T))%Z ->
  exists t' : int, ((φ t') < (φ t))%Z /\ O.[t'] = P.[O.[t]].
Hypothesis HDb : forall t : int, ((φ t) < (φ T))%Z -> ((φ (D.[O.[t]])) <= 100 * (φ t))%Z.

Definition lit (ch : array bool) (x : int) : bool := inl.[x] || ch.[x].

Definition used_m (x : int) : Prop := ((φ (D.[P.[x]])) + (φ (D.[P.[x]])) < (φ s))%Z.

Record SInv (i : int) (ch : array bool) (c : int) (ms : list int) : Prop := {
  si_len : PArray.length ch = n + 1;
  si_ch : forall x : int, ((φ x) <= (φ n))%Z ->
    (ch.[x] = true <-> In x (map (fun y => P.[y]) ms));
  si_nodup : NoDup (ms ++ map (fun y => P.[y]) ms);
  si_c : (φ c) = Z.of_nat (List.length ms);
  si_ci : ((φ c) + (φ i) < (φ T))%Z;
  si_pos : forall x, In x ms -> exists t : int, ((φ i) < (φ t) < (φ T))%Z /\ O.[t] = x;
  si_ok : forall x, In x ms -> inl.[x] = false /\ inl.[P.[x]] = false /\ used_m x;
  si_cover : forall t : int, ((φ i) < (φ t) < (φ T))%Z -> used_m (O.[t]) ->
    lit ch (O.[t]) = true \/ lit ch (P.[O.[t]]) = true
}.

Lemma sweep_spec : forall z i ch c ms H, (φ i) = z -> SInv i ch c ms ->
  exists chf msf, SInv 0 chf (sweep_loop s inl O P D i ch c H) msf.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i ch c ms H Hz Hinv.
  rewrite sweep_loop_eq. destruct (bdec (0 <? i)) as [Hk|Hk].
  - pose proof Hk as Hk'. rewrite ltb_spec in Hk'. change (φ 0) with 0%Z in Hk'.
    pose proof (si_ci i ch c ms Hinv) as Hci.
    pose proof (to_Z_bounded c) as Bc.
    assert (Hi1 : (φ (i - 1)) = ((φ i) - 1)%Z) by sia.
    assert (HiT : (0 < (φ i) < (φ T))%Z) by lia.
    assert (N1 : (φ (n + 1)) = ((φ n) + 1)%Z) by sia.
    destruct (HP i HiT) as (t' & Ht' & Ot').
    cbv zeta.
    set (v := O.[i]) in *. set (p := P.[v]) in *.
    pose proof (HO i ltac:(lia)) as Hv. pose proof (HO t' ltac:(lia)) as Hp.
    rewrite Ot' in Hp.
    assert (Hdp : ((φ (D.[p])) <= 100 * (φ t'))%Z) by (rewrite <- Ot'; apply HDb; lia).
    assert (Hdp2 : (φ (D.[p] + D.[p])) = ((φ (D.[p])) + (φ (D.[p])))%Z).
    { pose proof (to_Z_bounded (D.[p])). rewrite add_spec. apply Z.mod_small.
      rewrite wB_val. pose proof (to_Z_bounded t'). lia. }
    assert (Hvp : v <> p).
    { intro F. rewrite <- Ot' in F. apply Hinj in F; [|lia|lia].
      subst. lia. }
    assert (Hvms : ~ In v ms).
    { intro F. destruct (si_pos i ch c ms Hinv v F) as (t & Ht & Ot).
      unfold v in Ot. apply Hinj in Ot; [|lia|lia]. subst. lia. }
    assert (Hpms : ~ In p ms).
    { intro F. destruct (si_pos i ch c ms Hinv p F) as (t & Ht & Ot).
      rewrite <- Ot' in Ot. apply Hinj in Ot; [|lia|lia]. subst. lia. }
    destruct Hinv as [Lc Ch ND Cc Ci Pos Ok Cov].
    destruct ((D.[p] + D.[p] <? s) && negb (inl.[v] || ch.[v])
               && negb (inl.[p] || ch.[p])) eqn:Ec.
    + rewrite !Bool.andb_true_iff, !Bool.negb_true_iff, !Bool.orb_false_iff in Ec.
      destruct Ec as [[Eu [Iv Cv]] [Ip Cp]].
      rewrite ltb_spec, Hdp2 in Eu.
      assert (Bp : (p <? PArray.length ch) = true) by (rewrite Lc, ltb_spec; lia).
      eapply (IH (φ (i - 1)) ltac:(rewrite <- Hz; apply dec_down; exact Hk) (i - 1) _ _ (v :: ms) _ eq_refl).
      * split.
        -- rewrite blength_set. exact Lc.
        -- intros x Hx. cbn [map]. destruct (eqs p x) as [E|E].
           ++ subst x. rewrite bget_set_same by exact Bp. split; [intros _; simpl; left; reflexivity | intros _; reflexivity].
           ++ rewrite bget_set_other by exact E. rewrite Ch by exact Hx.
              split; [intros F; right; exact F|].
              intros [F|F]; [exfalso; apply E; exact F | exact F].
        -- cbn [map app]. apply NoDup_cons.
           ++ intro F. apply in_app_or in F. destruct F as [F|[F|F]].
              ** contradiction.
              ** symmetry in F. contradiction.
              ** apply (Ch v ltac:(lia)) in F. congruence.
           ++ apply NoDup_middle. apply NoDup_cons; [|exact ND].
              intro F. apply in_app_or in F. destruct F as [F|F]; [contradiction|].
              apply (Ch p ltac:(lia)) in F. congruence.
        -- cbn [List.length]. rewrite Nat2Z.inj_succ, <- Cc.
           rewrite add_spec. change (φ 1) with 1%Z. rewrite Z.mod_small; [lia|].
           rewrite wB_val. lia.
        -- assert ((φ (c + 1)) = ((φ c) + 1)%Z) by (rewrite add_spec; change (φ 1) with 1%Z;
             apply Z.mod_small; rewrite wB_val; lia). lia.
        -- intros x [F|F].
           ++ subst x. exists i. split; [lia | reflexivity].
           ++ destruct (Pos x F) as (t & Ht & Ot). exists t. split; [lia | exact Ot].
        -- intros x [F|F].
           ++ subst x. split; [exact Iv|]. split; [exact Ip|]. unfold used_m. fold p. lia.
           ++ apply Ok. exact F.
        -- intros t Ht Hu. unfold lit. destruct (eqs t i) as [E|E].
           ++ subst t. fold v p. right.
              rewrite bget_set_same by exact Bp. apply Bool.orb_true_r.
           ++ assert (Ht2 : ((φ i) < (φ t) < (φ T))%Z)
                by (assert ((φ t) <> (φ i)) by (intro F; apply E; apply to_Z_inj; exact F); lia).
              destruct (Cov t Ht2 Hu) as [L|L]; unfold lit in L;
                apply Bool.orb_true_iff in L; destruct L as [L|L];
                [left | left | right | right]; apply Bool.orb_true_iff;
                [left; exact L | right; apply bset_mono; [exact Bp | exact L]
                | left; exact L | right; apply bset_mono; [exact Bp | exact L]].
    + eapply (IH (φ (i - 1)) ltac:(rewrite <- Hz; apply dec_down; exact Hk) (i - 1) _ _ ms _ eq_refl).
      * split; try assumption.
        -- lia.
        -- intros x F. destruct (Pos x F) as (t & Ht & Ot). exists t. split; [lia | exact Ot].
        -- intros t Ht Hu. destruct (eqs t i) as [E|E].
           ++ subst t. fold v p. fold v p in Hu. unfold used_m in Hu. fold p in Hu.
              unfold lit.
              assert (Eu : (D.[p] + D.[p] <? s) = true) by (rewrite ltb_spec, Hdp2; exact Hu).
              rewrite Eu in Ec. cbn [andb] in Ec.
              destruct (inl.[v] || ch.[v]) eqn:E1; [left; reflexivity|].
              cbn [negb andb] in Ec.
              destruct (inl.[p] || ch.[p]) eqn:E2; [right; reflexivity|].
              discriminate.
           ++ apply Cov; [|exact Hu].
              assert ((φ t) <> (φ i)) by (intro F; apply E; apply to_Z_inj; exact F). lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk. change (φ 0) with 0%Z in Hk.
    pose proof (to_Z_bounded i).
    assert (E : i = 0) by (apply to_Z_inj; change (φ 0) with 0%Z; lia).
    subst i. exists ch, ms. exact Hinv.
Qed.

Lemma sweep_init : forall i : int, (φ i) = ((φ T) - 1)%Z ->
  SInv i (PArray.make (n + 1) false) 0 [].
Proof.
  intros i Hi.
  assert (LB : PArray.length (PArray.make (n + 1) false) = n + 1).
  { rewrite blength_make. replace (n + 1 <=? max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. sia. }
  split; cbn [map app List.length In].
  - exact LB.
  - intros x _. rewrite bget_make. split; [discriminate | intros []].
  - constructor.
  - reflexivity.
  - change (φ 0) with 0%Z. lia.
  - intros x [].
  - intros x [].
  - intros t Ht. lia.
Qed.
End Sweep.

(* ------------------------------------------------------------------ *)
(* The joggers on the math side: a trail is used iff its end nearer    *)
(* to the campus is less than s/2 away                                 *)
(* ------------------------------------------------------------------ *)

Lemma rN_add : forall x y : N, rN (x + y)%N = (rN x + rN y)%R.
Proof. intros. unfold rN. rewrite N2Z.inj_add, plus_IZR. reflexivity. Qed.

Lemma rN_nonneg : forall x : N, (0 <= rN x)%R.
Proof. intros. unfold rN. apply IZR_le. lia. Qed.

Lemma rN_lt : forall x y : N, (rN x < rN y)%R -> (x < y)%N.
Proof. intros x y H. unfold rN in H. apply lt_IZR in H. lia. Qed.

Lemma rN_le1 : forall x : N, (1 <= x)%N -> (1 <= rN x)%R.
Proof. intros x H. unfold rN. apply IZR_le. lia. Qed.

Lemma last_nonempty : forall (A : Type) (l : list A) (x z : A),
  l <> [] -> last l x = last l z.
Proof.
  intros A l. induction l as [|u l IH]; intros x z H; [contradiction|].
  destruct l as [|v l]; [reflexivity|]. simpl. apply IH. discriminate.
Qed.

Lemma last_cons : forall (A : Type) (x : A) (l : list A) (z : A),
  last (x :: l) z = last l x.
Proof.
  intros A x l z. destruct l as [|u l]; [reflexivity|].
  change (last (x :: u :: l) z) with (last (u :: l) z).
  apply last_nonempty. discriminate.
Qed.

Lemma last_In : forall (A : Type) (l : list A) (z : A), l <> [] -> In (last l z) l.
Proof.
  intros A l z. induction l as [|u l IH]; intros H; [contradiction|].
  rewrite last_cons. destruct l as [|v l]; [left; reflexivity|].
  right. rewrite <- (last_nonempty A (v :: l) z u) by discriminate. apply IH. discriminate.
Qed.

Lemma last_app : forall (A : Type) (l1 l2 : list A) (z : A),
  last (l1 ++ l2) z = last l2 (last l1 z).
Proof.
  intros A l1. induction l1 as [|x l1 IH]; intros l2 z; [reflexivity|].
  cbn [app]. rewrite !last_cons. apply IH.
Qed.

Section Jog.
Variables (n s : N) (a b d : list N) (dist : N -> N).
Hypothesis Hlb : len b = len a.
Hypothesis Hld : len d = len a.
Hypothesis Hd : forall j, (j < len a)%N -> (1 <= getl d j)%N.
Hypothesis Hedge : forall j, (j < len a)%N ->
  dist (getl b j) = (dist (getl a j) + getl d j)%N \/
  dist (getl a j) = (dist (getl b j) + getl d j)%N.
Hypothesis Hd1 : dist 1%N = 0%N.
Hypothesis Hup : forall v, inter n v -> v <> 1%N -> exists e p,
  (e < len a)%N /\ inter n p /\
  ((getl a e = p /\ getl b e = v) \/ (getl b e = p /\ getl a e = v)) /\
  dist v = (dist p + getl d e)%N.

Local Open Scope R_scope.

Definition Dp (q : place) : R :=
  if N.eqb (dist (getl b (fst q))) (dist (getl a (fst q)) + getl d (fst q))%N
  then rN (dist (getl a (fst q))) + snd q
  else rN (dist (getl a (fst q))) - snd q.

Lemma Dp_inter : forall q v, in_woods d q -> at_inter a b d q v -> Dp q = rN (dist v).
Proof.
  intros [j x] v [Hj _] Hat. unfold Dp. cbn [fst snd] in *.
  rewrite Hld in Hj.
  destruct Hat as [[Hx Ha]|[Hx Hb]]; cbn [fst snd] in *; subst.
  - destruct (N.eqb _ _); lra.
  - destruct (N.eqb_spec (dist (getl b j)) (dist (getl a j) + getl d j)%N) as [E|E].
    + rewrite <- rN_add, <- E. reflexivity.
    + destruct (Hedge j Hj) as [E'|E']; [contradiction|].
      rewrite E', rN_add. lra.
Qed.

Lemma leg_len_nonneg : forall p q, 0 <= leg_len p q.
Proof. intros. unfold leg_len. destruct (N.eqb _ _); [apply Rabs_pos | lra]. Qed.

Lemma leg_D : forall p q, in_woods d p -> in_woods d q -> leg_ok a b d p q ->
  Rabs (Dp p - Dp q) <= leg_len p q.
Proof.
  intros p q Hp Hq [E|(v & Hpv & Hqv)].
  - unfold leg_len. rewrite E, N.eqb_refl. unfold Dp. rewrite E.
    destruct (N.eqb _ _).
    + replace (rN (dist (getl a (fst q))) + snd p - (rN (dist (getl a (fst q))) + snd q))
        with (snd p - snd q) by ring. lra.
    + replace (rN (dist (getl a (fst q))) - snd p - (rN (dist (getl a (fst q))) - snd q))
        with (- (snd p - snd q)) by ring. rewrite Rabs_Ropp. lra.
  - rewrite (Dp_inter p v Hp Hpv), (Dp_inter q v Hq Hqv).
    replace (rN (dist v) - rN (dist v)) with 0 by ring. rewrite Rabs_R0.
    apply leg_len_nonneg.
Qed.

Lemma run_D : forall ps p, Forall (in_woods d) (p :: ps) -> legs_ok a b d p ps ->
  forall q, In q (p :: ps) -> 2 * Dp q - Dp p - Dp (last ps p) <= run_len p ps.
Proof.
  induction ps as [|r ps IH]; intros p Hf Hl q Hq.
  - destruct Hq as [<-|[]]. simpl. lra.
  - rewrite last_cons. cbn [run_len]. cbn [legs_ok] in Hl. destruct Hl as [Hpr Hl].
    inversion Hf as [|? ? Hp Hf']. subst.
    inversion Hf' as [|? ? Hr _]. subst.
    pose proof (leg_D p r Hp Hr Hpr) as L.
    pose proof (IH r Hf' Hl r (or_introl eq_refl)) as I1.
    destruct Hq as [<-|Hq].
    + pose proof (Rle_abs (Dp p - Dp r)). lra.
    + pose proof (IH r Hf' Hl q Hq) as I2.
      pose proof (Rle_abs (- (Dp p - Dp r))). rewrite Rabs_Ropp in *. lra.
Qed.

Lemma runs_on_in : forall j ps p, runs_on j p ps -> exists q r,
  In q (p :: ps) /\ In r (p :: ps) /\ fst q = j /\ fst r = j /\ snd q <> snd r.
Proof.
  intros j ps. induction ps as [|r ps IH]; intros p H; [destruct H|].
  destruct H as [(E1 & E2 & E3)|H].
  - exists p, r. repeat split; auto; [left; reflexivity | right; left; reflexivity].
  - destruct (IH r H) as (q1 & q2 & I1 & I2 & F1 & F2 & N12).
    exists q1, q2. repeat split; auto; right; assumption.
Qed.

Lemma used_nec : forall j pp c, (j < len a)%N ->
  ((getl a j = pp /\ getl b j = c) \/ (getl b j = pp /\ getl a j = c)) ->
  dist c = (dist pp + getl d j)%N ->
  used a b d s j -> (2 * dist pp < s)%N.
Proof.
  intros j pp c Hj Hor Hc (p0 & ps & (Hf & H0 & Hlast & Hl & Hlen) & Hrun).
  destruct (runs_on_in j ps p0 Hrun) as (q & r & Iq & Ir & Fq & Fr & Nqr).
  assert (Wq : in_woods d q) by (rewrite Forall_forall in Hf; apply Hf; exact Iq).
  assert (Wr : in_woods d r) by (rewrite Forall_forall in Hf; apply Hf; exact Ir).
  pose proof (run_D ps p0 Hf Hl q Iq) as Rq.
  pose proof (run_D ps p0 Hf Hl r Ir) as Rr.
  assert (W0 : in_woods d p0) by (rewrite Forall_forall in Hf; apply Hf; left; reflexivity).
  assert (WL : in_woods d (last ps p0)).
  { rewrite Forall_forall in Hf; apply Hf. destruct ps as [|x ps];
      [left; reflexivity | right; apply last_In; discriminate]. }
  assert (Z0 : rN (dist 1%N) = 0) by (rewrite Hd1; unfold rN; change (Z.of_N 0) with 0%Z; reflexivity).
  rewrite (Dp_inter p0 1%N W0 H0), (Dp_inter (last ps p0) 1%N WL Hlast), Z0 in Rq, Rr.
  rewrite Hlen in Rq, Rr.
  assert (Hdj : 1 <= rN (getl d j)) by (apply rN_le1; apply Hd; exact Hj).
  destruct Wq as [_ Wq]. destruct Wr as [_ Wr]. rewrite Fq in Wq. rewrite Fr in Wr.
  assert (Key : rN (dist pp) < Dp q \/ rN (dist pp) < Dp r).
  { unfold Dp. rewrite Fq, Fr.
    destruct Hor as [[Ea Eb]|[Eb Ea]]; rewrite Ea, Eb.
    - rewrite Hc, N.eqb_refl. destruct (Rlt_dec 0 (snd q)); [left; lra|].
      right. assert (snd q = 0) by lra. lra.
    - assert (Ne : (dist pp =? dist c + getl d j)%N = false).
      { apply N.eqb_neq. rewrite Hc. pose proof (Hd j Hj). lia. }
      rewrite Ne, Hc, rN_add.
      destruct (Rlt_dec (snd q) (rN (getl d j))); [left; lra|].
      right. assert (snd q = rN (getl d j)) by lra. lra. }
  apply rN_lt. replace (rN (2 * dist pp)%N) with (2 * rN (dist pp)).
  - destruct Key; lra.
  - replace (2 * dist pp)%N with (dist pp + dist pp)%N by lia. rewrite rN_add. ring.
Qed.

(* ---- sufficiency: an explicit run ---- *)

Lemma legs_ok_app : forall l1 l2 p,
  legs_ok a b d p (l1 ++ l2) <-> legs_ok a b d p l1 /\ legs_ok a b d (last l1 p) l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2 p; cbn [app legs_ok].
  - simpl. tauto.
  - rewrite last_cons, IH. tauto.
Qed.

Lemma run_len_app : forall l1 l2 p,
  run_len p (l1 ++ l2) = run_len p l1 + run_len (last l1 p) l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2 p; cbn [app run_len].
  - simpl. ring.
  - rewrite last_cons, IH. ring.
Qed.

Lemma runs_on_app : forall j l1 l2 p, runs_on j p l1 -> runs_on j p (l1 ++ l2).
Proof.
  intros j l1. induction l1 as [|x l1 IH]; intros l2 p H; [destruct H|].
  destruct H as [H|H]; [left; exact H | right; apply IH; exact H].
Qed.

Lemma leg_len_inter0 : forall p q v, at_inter a b d p v -> at_inter a b d q v ->
  (fst p = fst q -> getl a (fst p) <> getl b (fst p)) -> leg_len p q = 0.
Proof.
  intros p q v Hp Hq Hne. unfold leg_len.
  destruct (N.eqb_spec (fst p) (fst q)) as [E|E]; [|reflexivity].
  specialize (Hne E). unfold at_inter in Hp, Hq. rewrite <- E in Hq.
  destruct Hp as [[P1 P2]|[P1 P2]]; destruct Hq as [[Q1 Q2]|[Q1 Q2]];
    try (exfalso; apply Hne; congruence);
    rewrite P1, Q1; replace (_ - _) with 0 by ring; apply Rabs_R0.
Qed.

Lemma ends_of : forall e p v, (e < len a)%N ->
  ((getl a e = p /\ getl b e = v) \/ (getl b e = p /\ getl a e = v)) ->
  exists xp xv, at_inter a b d (e, xp) p /\ at_inter a b d (e, xv) v /\
    in_woods d (e, xp) /\ in_woods d (e, xv) /\ Rabs (xp - xv) = rN (getl d e).
Proof.
  intros e p v He Hor.
  assert (W0 : in_woods d (e, 0)).
  { split; cbn [fst snd]; [rewrite Hld; exact He|]. pose proof (rN_nonneg (getl d e)); lra. }
  assert (Wd : in_woods d (e, rN (getl d e))).
  { split; cbn [fst snd]; [rewrite Hld; exact He|]. pose proof (rN_nonneg (getl d e)); lra. }
  destruct Hor as [[Ea Eb]|[Eb Ea]].
  - exists 0, (rN (getl d e)). split; [left; split; [reflexivity | exact Ea]|].
    split; [right; split; [reflexivity | exact Eb]|]. split; [exact W0|]. split; [exact Wd|].
    replace (0 - rN (getl d e)) with (- rN (getl d e)) by ring. rewrite Rabs_Ropp.
    apply Rabs_right. pose proof (rN_nonneg (getl d e)); lra.
  - exists (rN (getl d e)), 0. split; [right; split; [reflexivity | exact Eb]|].
    split; [left; split; [reflexivity | exact Ea]|]. split; [exact Wd|]. split; [exact W0|].
    replace (rN (getl d e) - 0) with (rN (getl d e)) by ring.
    apply Rabs_right. pose proof (rN_nonneg (getl d e)); lra.
Qed.

Lemma climb : forall (k : nat) v, (N.to_nat (dist v) < k)%nat -> inter n v ->
  forall j z ms, in_woods d z -> at_inter a b d z v -> Forall (in_woods d) ms ->
  legs_ok a b d z ms -> at_inter a b d (last ms z) v ->
  exists p0 ps, at_inter a b d p0 1%N /\ at_inter a b d (last ps p0) 1%N /\
    Forall (in_woods d) (p0 :: ps) /\ legs_ok a b d p0 ps /\
    run_len p0 ps = 2 * rN (dist v) + run_len z ms /\
    (runs_on j z ms -> runs_on j p0 ps).
Proof.
  induction k as [|k IH]; intros v Hk Hv j z ms Wz Az Wms Lms Alast; [lia|].
  destruct (N.eq_dec v 1%N) as [E|E].
  - subst v. exists z, ms. split; [exact Az|]. split; [exact Alast|].
    split; [constructor; assumption|]. split; [exact Lms|].
    split; [rewrite Hd1; unfold rN; simpl; ring | auto].
  - destruct (Hup v Hv E) as (e & p & He & Hp & Hor & Hdv).
    assert (Hde : (1 <= getl d e)%N) by (apply Hd; exact He).
    assert (Hne : getl a e <> getl b e).
    { intro F. destruct Hor as [[A1 B1]|[B1 A1]]; rewrite A1, B1 in F; rewrite F in Hdv; lia. }
    destruct (ends_of e p v He Hor) as (xp & xv & Ap & Av & Wp & Wv & Hx).
    set (zp := (e, xp)) in *. set (zv := (e, xv)) in *.
    assert (L1 : leg_len zp zv = rN (getl d e)).
    { unfold leg_len. cbn [fst snd zp zv]. rewrite N.eqb_refl. exact Hx. }
    assert (L2 : leg_len zv zp = rN (getl d e)).
    { unfold leg_len. cbn [fst snd zp zv]. rewrite N.eqb_refl.
      rewrite Rabs_minus_sym. exact Hx. }
    assert (L3 : leg_len zv z = 0).
    { apply (leg_len_inter0 zv z v Av Az). intros _. exact Hne. }
    assert (L4 : leg_len (last ms z) zv = 0).
    { apply (leg_len_inter0 (last ms z) zv v Alast Av).
      intros F. rewrite F. exact Hne. }
    assert (Hlast_ms : in_woods d (last ms z)).
    { destruct ms as [|x ms']; [exact Wz|].
      rewrite Forall_forall in Wms. apply Wms. apply last_In. discriminate. }
    set (ms' := zv :: z :: (ms ++ [zv; zp])).
    assert (Hlt : (N.to_nat (dist p) < k)%nat) by lia.
    destruct (IH p Hlt Hp j zp ms') as (p0 & ps & A0 & Al & W & L & R & Ru).
    + exact Wp.
    + exact Ap.
    + unfold ms'. constructor; [exact Wv|]. constructor; [exact Wz|].
      apply Forall_app. split; [exact Wms|].
      constructor; [exact Wv|]. constructor; [exact Wp | constructor].
    + unfold ms'. cbn [legs_ok]. split; [left; reflexivity|].
      split; [right; exists v; split; assumption|].
      apply legs_ok_app. split; [exact Lms|]. cbn [legs_ok].
      split; [right; exists v; split; assumption|].
      split; [left; reflexivity | exact I].
    + unfold ms'. rewrite !last_cons, last_app. simpl. exact Ap.
    + exists p0, ps. split; [exact A0|]. split; [exact Al|]. split; [exact W|].
      split; [exact L|]. split.
      * rewrite R. unfold ms'. cbn [run_len]. rewrite run_len_app. cbn [run_len].
        rewrite L1, L2, L3, L4, Hdv, rN_add. ring.
      * intros Hr. apply Ru. unfold ms'. right. right. apply runs_on_app. exact Hr.
Qed.

Fixpoint osc (q r : place) (k : nat) : list place :=
  match k with O => [] | S k' => r :: q :: osc q r k' end.

Lemma osc_props : forall q r k, in_woods d q -> in_woods d r ->
  leg_ok a b d q r -> leg_ok a b d r q ->
  Forall (in_woods d) (osc q r k) /\ legs_ok a b d q (osc q r k) /\
  last (osc q r k) q = q /\
  run_len q (osc q r k) = INR k * (leg_len q r + leg_len r q).
Proof.
  intros q r k Wq Wr Lqr Lrq. induction k as [|k (IH1 & IH2 & IH3 & IH4)].
  - cbn. repeat split; [constructor | ring].
  - cbn [osc]. split; [constructor; [exact Wr|]; constructor; [exact Wq | exact IH1]|].
    split; [cbn [legs_ok]; tauto|]. split.
    + rewrite !last_cons. exact IH3.
    + cbn [run_len]. rewrite IH4, S_INR. ring.
Qed.

Lemma used_suf : forall j pp c, (j < len a)%N ->
  ((getl a j = pp /\ getl b j = c) \/ (getl b j = pp /\ getl a j = c)) ->
  inter n pp -> (1 <= s)%N -> (2 * dist pp < s)%N -> used a b d s j.
Proof.
  intros j pp c Hj Hor Hpp Hs1 Hs.
  destruct (ends_of j pp c Hj Hor) as (xp & xc & Ap & _ & Wp & _ & _).
  set (t := (rN s - 2 * rN (dist pp)) / (2 * rN s)).
  assert (Hrs : 1 <= rN s) by (apply rN_le1; exact Hs1).
  assert (H2 : 2 * rN (dist pp) < rN s).
  { replace (2 * rN (dist pp)) with (rN (2 * dist pp)%N).
    - unfold rN. apply IZR_lt. lia.
    - replace (2 * dist pp)%N with (dist pp + dist pp)%N by lia. rewrite rN_add. ring. }
  pose proof (rN_nonneg (dist pp)) as Hd0.
  assert (Ht0 : 0 < t) by (unfold t; apply Rdiv_lt_0_compat; lra).
  assert (Ht1 : t <= 1).
  { unfold t. apply Rmult_le_reg_r with (2 * rN s); [lra|].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  assert (Hdj : 1 <= rN (getl d j)) by (apply rN_le1; apply Hd; exact Hj).
  destruct Wp as [Wj Wx]. cbn [fst snd] in Wj, Wx.
  (* the turning point y, t metres into trail j from the end pp *)
  assert (Hy : exists y, 0 <= y <= rN (getl d j) /\ Rabs (xp - y) = t).
  { destruct Ap as [[X _]|[X _]]; cbn [fst snd] in X; subst xp.
    - exists t. split; [lra|]. replace (0 - t) with (- t) by ring.
      rewrite Rabs_Ropp. apply Rabs_right. lra.
    - exists (rN (getl d j) - t). split; [lra|].
      replace (rN (getl d j) - (rN (getl d j) - t)) with t by ring. apply Rabs_right. lra. }
  destruct Hy as (y & Wy & Hty).
  set (q := (j, xp)). set (r := (j, y)).
  assert (Wq : in_woods d q) by (split; assumption).
  assert (Wr : in_woods d r) by (split; assumption).
  destruct (osc_props q r (N.to_nat s) Wq Wr (or_introl eq_refl) (or_introl eq_refl))
    as (Wo & Lo & Lao & Ro).
  assert (Llen : leg_len q r = t /\ leg_len r q = t).
  { unfold leg_len. cbn [fst snd q r]. rewrite N.eqb_refl. split; [exact Hty|].
    rewrite Rabs_minus_sym. exact Hty. }
  assert (Hk : INR (N.to_nat s) = rN s).
  { rewrite INR_IZR_INZ. unfold rN. f_equal. lia. }
  assert (Ho : run_len q (osc q r (N.to_nat s)) = rN s - 2 * rN (dist pp)).
  { rewrite Ro, Hk. destruct Llen as [-> ->]. unfold t. field. lra. }
  destruct (climb (S (N.to_nat (dist pp))) pp ltac:(lia) Hpp j q (osc q r (N.to_nat s))
              Wq Ap Wo Lo ltac:(rewrite Lao; exact Ap))
    as (p0 & ps & A0 & Al & W & L & R & Ru).
  exists p0, ps. split.
  - split; [exact W|]. split; [exact A0|]. split; [exact Al|]. split; [exact L|].
    rewrite R, Ho. ring.
  - apply Ru. destruct (N.to_nat s) as [|k] eqn:Ek; [lia|].
    cbn [osc runs_on]. left. cbn [fst snd q r]. split; [reflexivity|]. split; [reflexivity|].
    intro F. rewrite F in Hty. replace (y - y) with 0 in Hty by ring.
    rewrite Rabs_R0 in Hty. lra.
Qed.
End Jog.

(* ------------------------------------------------------------------ *)
(* The lamps                                                           *)
(* ------------------------------------------------------------------ *)

Lemma lamp_loop_spec : forall (xl : array int) (L V : int),
  (forall t : int, ((φ t) < (φ L))%Z -> ((φ (xl.[t])) < (φ V))%Z) ->
  forall z i inl H, gap L i = z -> ((φ i) <= (φ L))%Z -> PArray.length inl = V ->
  (forall x : int, ((φ x) < (φ V))%Z ->
     (inl.[x] = true <-> exists t : int, ((φ t) < (φ i))%Z /\ xl.[t] = x)) ->
  forall x : int, ((φ x) < (φ V))%Z ->
    ((lamp_loop xl L i inl H).[x] = true <->
     exists t : int, ((φ t) < (φ L))%Z /\ xl.[t] = x).
Proof.
  intros xl L V Hxl z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i inl H Hz Hi Hl Hinv.
  rewrite lamp_loop_eq. destruct (bdec (i <? L)) as [Hk|Hk].
  - pose proof Hk as Hk'. rewrite ltb_spec in Hk'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    eapply IH; [ | reflexivity | lia | rewrite blength_set; exact Hl | ].
    + rewrite <- Hz. apply dec_step. exact Hk.
    + intros x Hx. rewrite Hi1. destruct (eqs (xl.[i]) x) as [E|E].
      * subst x. rewrite bget_set_same by (rewrite Hl, ltb_spec; apply Hxl; lia).
        split; [intros _; exists i; split; [lia | reflexivity] | intros _; reflexivity].
      * rewrite bget_set_other by exact E. rewrite Hinv by exact Hx.
        split; intros (t & Ht & Et).
        -- exists t. split; [lia | exact Et].
        -- exists t. split; [|exact Et].
           destruct (eqs t i) as [E'|E']; [subst t; contradiction|].
           assert ((φ t) <> (φ i)) by (intro F; apply E'; apply to_Z_inj; exact F). lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk.
    intros x Hx. rewrite Hinv by exact Hx.
    split; intros (t & Ht & Et); exists t; (split; [lia | exact Et]).
Qed.

(* ------------------------------------------------------------------ *)
(* repr bridges                                                        *)
(* ------------------------------------------------------------------ *)

Lemma repr_get_u : forall (x : array uint) (l : list N), repr x l ->
  forall k : int, ((φ k) < Z.of_nat (List.length l))%Z ->
  (φ (x.[k])) = Z.of_N (getl l (Z.to_N (φ k))).
Proof.
  intros x l [Hl Hc] k Hk.
  destruct (Hc (Z.to_nat (φ k)) ltac:(lia)) as (v & Hv & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded k); lia).
  rewrite of_to_Z in Hr.
  unfold getl, Prelude.get.
  replace (N.to_nat (Z.to_N (φ k))) with (Z.to_nat (φ k)) by lia.
  rewrite (nth_error_nth l _ 0%N Hv).
  pose proof (to_Z_bounded (x.[k])). lia.
Qed.

Lemma repr_len_u : forall (x : array uint) (l : list N), repr x l ->
  (φ (PArray.length x)) = Z.of_nat (List.length l).
Proof. intros x l [Hl _]. symmetry. exact Hl. Qed.

Lemma Forall_getl : forall (P : N -> Prop) l j, Forall P l -> (j < len l)%N ->
  P (getl l j).
Proof.
  intros P l j H Hj. rewrite Forall_forall in H. apply H.
  unfold getl, Prelude.get. apply nth_In. unfold len in Hj. lia.
Qed.

Definition toN (x : int) : N := Z.to_N (φ x).
Definition ofN (v : N) : int := of_Z (Z.of_N v).

Lemma ofN_toN : forall x : int, ofN (toN x) = x.
Proof.
  intros x. unfold ofN, toN. pose proof (to_Z_bounded x).
  rewrite Z2N.id by lia. apply of_to_Z.
Qed.

Lemma phi_ofN : forall v : N, (Z.of_N v < wB)%Z -> (φ (ofN v)) = Z.of_N v.
Proof. intros v H. unfold ofN. apply phi_ofZ. lia. Qed.

Lemma toN_inj : forall x y : int, toN x = toN y -> x = y.
Proof.
  intros x y H. unfold toN in H. apply to_Z_inj.
  pose proof (to_Z_bounded x). pose proof (to_Z_bounded y). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The main proof                                                      *)
(* ------------------------------------------------------------------ *)

Section Main.
Variables (n s : N) (a b d l : list N) (xn xs : int) (xa xb xd xl : array int).
Hypothesis Hv : valid_input n s a b d l.
Hypothesis Rn : repr (xn : uint) n.
Hypothesis Rs : repr (xs : uint) s.
Hypothesis Ra : repr (xa : array uint) a.
Hypothesis Rb : repr (xb : array uint) b.
Hypothesis Rd : repr (xd : array uint) d.
Hypothesis Rl : repr (xl : array uint) l.

Let m := PArray.length xa.
Let V := xn + 1.
Let inl := lamp_loop xl (PArray.length xl) 0 (PArray.make V false) (Zwf_well_founded 0 _).
Let cnt := cnt_loop xa xb m (m + m) 0 (PArray.make V 0) (Zwf_well_founded 0 _).
Let oc := off_loop cnt V 0 (PArray.make (V + 1) 0) (PArray.make V 0) (Zwf_well_founded 0 _).
Let adj := fill_loop xa xb m (m + m) 0 (snd oc) (PArray.make (m + m) 0)
             (Zwf_well_founded 0 _).
Let st0 := Bst ((PArray.make V false).[1 <- true]) (PArray.make V 0)
               (PArray.make V 0) (PArray.make V 0)
               ((PArray.make xn 0).[0 <- 1]) 1.
Let st := bfs_loop xa xb xd m adj (fst oc) 0 st0 (Zwf_well_founded 0 _).

Lemma M_n : (φ xn) = Z.of_N n.
Proof. unfold repr, repr_uint in Rn. pose proof (to_Z_bounded xn). lia. Qed.

Lemma M_s : (φ xs) = Z.of_N s.
Proof. unfold repr, repr_uint in Rs. pose proof (to_Z_bounded xs). lia. Qed.

Lemma M_nb : (2 <= (φ xn) <= 50000)%Z.
Proof. rewrite M_n. destruct Hv as [[H1 H2] _ _ _ _ _ _ _ _ _ _]. lia. Qed.

Lemma M_lens : (φ m) = ((φ xn) - 1)%Z /\ (φ (PArray.length xb)) = (φ m) /\
  (φ (PArray.length xd)) = (φ m) /\ Z.of_N (len a) = (φ m).
Proof.
  destruct Hv as [[H1 H2] _ [T1 [T2 T3]] _ _ _ _ _ _ _ _].
  pose proof (repr_len_u xa a Ra) as La. pose proof (repr_len_u xb b Rb) as Lb.
  pose proof (repr_len_u xd d Rd) as Ld. unfold len in *. unfold m.
  rewrite M_n. split; [|split; [|split]].
  - transitivity (Z.of_nat (List.length a)); [exact La | lia].
  - transitivity (Z.of_nat (List.length b)); [exact Lb|].
    transitivity (Z.of_nat (List.length a)); [lia|]. symmetry; exact La.
  - transitivity (Z.of_nat (List.length d)); [exact Ld|].
    transitivity (Z.of_nat (List.length a)); [lia|]. symmetry; exact La.
  - transitivity (Z.of_nat (List.length a)); [lia|]. symmetry; exact La.
Qed.

Lemma GA : forall k : int, ((φ k) < (φ m))%Z -> (φ (xa.[k])) = Z.of_N (getl a (toN k)).
Proof.
  intros k Hk. pose proof M_lens as (_ & _ & _ & L).
  exact (repr_get_u xa a Ra k ltac:(unfold len in L; lia)).
Qed.

Lemma GB : forall k : int, ((φ k) < (φ m))%Z -> (φ (xb.[k])) = Z.of_N (getl b (toN k)).
Proof.
  intros k Hk. pose proof M_lens as (_ & _ & _ & L).
  destruct Hv as [_ _ [_ [T2 _]] _ _ _ _ _ _ _ _].
  exact (repr_get_u xb b Rb k ltac:(unfold len in *; lia)).
Qed.

Lemma GD : forall k : int, ((φ k) < (φ m))%Z -> (φ (xd.[k])) = Z.of_N (getl d (toN k)).
Proof.
  intros k Hk. pose proof M_lens as (_ & _ & _ & L).
  destruct Hv as [_ _ [_ [_ T3]] _ _ _ _ _ _ _ _].
  exact (repr_get_u xd d Rd k ltac:(unfold len in *; lia)).
Qed.

Lemma toN_lt : forall k : int, ((φ k) < Z.of_N (len a))%Z -> (toN k < len a)%N.
Proof. intros k Hk. unfold toN. lia. Qed.

Lemma HA : forall k : int, ((φ k) < (φ m))%Z -> (1 <= (φ (xa.[k])) <= (φ xn))%Z.
Proof.
  intros k Hk. rewrite GA by exact Hk. rewrite M_n.
  pose proof M_lens as (_ & _ & _ & L).
  destruct Hv as [_ _ _ Va _ _ _ _ _ _ _].
  pose proof (Forall_getl _ a (toN k) Va (toN_lt k ltac:(lia))) as [I1 I2]. lia.
Qed.

Lemma HB : forall k : int, ((φ k) < (φ m))%Z -> (1 <= (φ (xb.[k])) <= (φ xn))%Z.
Proof.
  intros k Hk. rewrite GB by exact Hk. rewrite M_n.
  pose proof M_lens as (_ & _ & _ & L).
  destruct Hv as [_ _ [_ [T2 _]] _ Vb _ _ _ _ _ _].
  pose proof (Forall_getl _ b (toN k) Vb ltac:(rewrite T2; apply toN_lt; lia)) as [I1 I2].
  lia.
Qed.

Lemma HD : forall k : int, ((φ k) < (φ m))%Z -> (1 <= (φ (xd.[k])) <= 100)%Z.
Proof.
  intros k Hk. rewrite GD by exact Hk.
  pose proof M_lens as (_ & _ & _ & L).
  destruct Hv as [_ _ [_ [_ T3]] _ _ Vd _ _ _ _ _].
  pose proof (Forall_getl _ d (toN k) Vd ltac:(rewrite T3; apply toN_lt; lia)) as [I1 I2].
  lia.
Qed.

Lemma M_L : (φ (PArray.length xl)) = Z.of_nat (List.length l) /\
  (Z.of_nat (List.length l) <= (φ xn))%Z.
Proof.
  pose proof (repr_len_u xl l Rl) as L. split; [exact L|].
  destruct Hv as [_ _ _ _ _ _ _ _ VL _ _]. unfold len in VL. rewrite M_n. lia.
Qed.

Lemma GL : forall t : int, ((φ t) < (φ (PArray.length xl)))%Z ->
  (φ (xl.[t])) = Z.of_N (getl l (toN t)).
Proof.
  intros t Ht. pose proof M_L as [L _].
  exact (repr_get_u xl l Rl t ltac:(lia)).
Qed.

Lemma HL : forall t : int, ((φ t) < (φ (PArray.length xl)))%Z -> (1 <= (φ (xl.[t])) <= (φ xn))%Z.
Proof.
  intros t Ht. rewrite GL by exact Ht. rewrite M_n. pose proof M_L as [L _].
  destruct Hv as [_ _ _ _ _ _ _ _ _ VL _].
  pose proof (Forall_getl _ l (toN t) VL ltac:(unfold len, toN; lia)) as [I1 I2]. lia.
Qed.

Lemma M_V : (φ V) = ((φ xn) + 1)%Z.
Proof. pose proof M_nb. unfold V. sia. Qed.

Lemma M_inl : forall x : int, ((φ x) < (φ V))%Z ->
  (inl.[x] = true <-> exists t : int, ((φ t) < (φ (PArray.length xl)))%Z /\ xl.[t] = x).
Proof.
  pose proof M_V as MV. pose proof M_nb as MB.
  assert (LB : PArray.length (PArray.make V false) = V).
  { rewrite blength_make. replace (V <=? max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  assert (Hxl : forall t : int, ((φ t) < (φ (PArray.length xl)))%Z -> ((φ (xl.[t])) < (φ V))%Z)
    by (intros t Ht; pose proof (HL t Ht); lia).
  intros y Hy.
  apply (lamp_loop_spec xl (PArray.length xl) V Hxl _ 0 (PArray.make V false) _ eq_refl);
    [ | | | exact Hy].
  - pose proof (to_Z_bounded (PArray.length xl)). change (φ 0) with 0%Z. lia.
  - exact LB.
  - intros x Hx. rewrite bget_make. split; [discriminate|].
    intros (t & Ht & _). change (φ 0) with 0%Z in Ht. pose proof (to_Z_bounded t). lia.
Qed.

Lemma Hep : forall k : int, ((φ k) < 2 * (φ m))%Z -> (1 <= (φ (ep xa xb m k)) < (φ V))%Z.
Proof.
  intros k Hk. destruct (he_facts xa xb m xn HA HB k Hk) as (_ & _ & _ & H).
  rewrite M_V. lia.
Qed.

Lemma Hm : ((φ m) <= 100000)%Z.
Proof. pose proof M_lens as [L _]. pose proof M_nb. lia. Qed.

Lemma HVb : (1 <= (φ V) <= 100000)%Z.
Proof. rewrite M_V. pose proof M_nb. lia. Qed.

Lemma M_cnt : PArray.length cnt = V /\
  forall w : int, ((φ w) < (φ V))%Z -> (φ (cnt.[w])) = cntN xa xb m (K2 m) (φ w).
Proof.
  pose proof HVb as HV.
  assert (LV : PArray.length (PArray.make V 0) = V).
  { rewrite alength_make. replace (V <=? max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  apply (cnt_loop_spec xa xb m V Hm Hep _ 0 (PArray.make V 0) _ eq_refl).
  - change (φ 0) with 0%Z. pose proof (to_Z_bounded (m + m)). lia.
  - exact LV.
  - intros w _. rewrite aget_make. reflexivity.
Qed.

Lemma M_off : PArray.length (fst oc) = V + 1 /\ PArray.length (snd oc) = V /\
  (forall w : int, ((φ w) <= (φ V))%Z -> (φ ((fst oc).[w])) = offZ xa xb m (φ w)) /\
  (forall w : int, ((φ w) < (φ V))%Z -> (φ ((snd oc).[w])) = offZ xa xb m (φ w)).
Proof.
  pose proof HVb as HV. destruct M_cnt as [Lc Cc].
  assert (V1 : (φ (V + 1)) = ((φ V) + 1)%Z) by sia.
  assert (LV : PArray.length (PArray.make V 0) = V).
  { rewrite alength_make. replace (V <=? max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  assert (LV1 : PArray.length (PArray.make (V + 1) 0) = V + 1).
  { rewrite alength_make. replace (V + 1 <=? max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  apply (off_loop_spec xa xb m V Hm HV cnt Lc Cc _ 0 _ _ _ eq_refl).
  - change (φ 0) with 0%Z. lia.
  - exact LV1.
  - exact LV.
  - intros w Hw. change (φ 0) with 0%Z in Hw. pose proof (to_Z_bounded w).
    replace (φ w) with 0%Z by lia. rewrite aget_make. reflexivity.
  - intros w Hw. change (φ 0) with 0%Z in Hw. pose proof (to_Z_bounded w). lia.
Qed.

Lemma M_adj :
  (forall (w sl : int), ((φ w) < (φ V))%Z ->
     ((φ ((fst oc).[w])) <= (φ sl) < (φ ((fst oc).[w + 1])))%Z ->
     ep xa xb m (adj.[sl]) = w /\ ((φ (adj.[sl])) < 2 * (φ m))%Z) /\
  (forall k : int, ((φ k) < 2 * (φ m))%Z -> exists sl : int,
     ((φ ((fst oc).[ep xa xb m k])) <= (φ sl) < (φ ((fst oc).[ep xa xb m k + 1])))%Z /\
     adj.[sl] = k).
Proof.
  pose proof HVb as HV. destruct M_off as (L1 & L2 & O1 & O2).
  assert (LK : PArray.length (PArray.make (m + m) 0) = m + m).
  { rewrite alength_make. replace (m + m <=? max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. pose proof Hm.
    assert ((φ (m + m)) = (2 * (φ m))%Z) by sia. lia. }
  apply (fill_loop_spec xa xb m V Hm HV Hep (fst oc) O1 _ 0 (snd oc) _ _ eq_refl).
  - change (φ 0) with 0%Z. pose proof (to_Z_bounded (m + m)). lia.
  - exact L2.
  - exact LK.
  - intros w Hw. rewrite O2 by exact Hw. change (cntN xa xb m (Z.to_nat (φ 0)) (φ w)) with 0%Z.
    lia.
  - intros w sl Hw Hs. rewrite O2 in Hs by exact Hw. lia.
  - intros k Hk. change (φ 0) with 0%Z in Hk. pose proof (to_Z_bounded k). lia.
Qed.

Lemma M_HC1 : forall u sl : int, (1 <= (φ u) <= (φ xn))%Z ->
  ((φ ((fst oc).[u])) <= (φ sl) < (φ ((fst oc).[u + 1])))%Z ->
  ep xa xb m (adj.[sl]) = u /\ ((φ (adj.[sl])) < 2 * (φ m))%Z.
Proof. intros u sl Hu Hs. apply (proj1 M_adj); [rewrite M_V; lia | exact Hs]. Qed.

Lemma M_bfs : Inv xa xb xd m xn (tl st) st.
Proof.
  unfold st. pose proof M_lens as [Lm _].
  apply (bfs_spec xa xb xd m xn adj (fst oc) M_nb HA HB HD M_HC1 (proj2 M_adj) _ 0 st0 _ eq_refl).
  apply init_inv. exact M_nb.
Qed.

Lemma M_small : forall v : N, inter n v -> (φ (ofN v)) = Z.of_N v.
Proof.
  intros v [H1 H2]. apply phi_ofN. pose proof M_nb. rewrite M_n in *. rewrite wB_val. lia.
Qed.

Lemma toN_ofN : forall j : N, (Z.of_N j < wB)%Z -> toN (ofN j) = j.
Proof. intros j H. unfold toN. rewrite phi_ofN by exact H. lia. Qed.

Lemma ep_lo : forall j : N, (j < len a)%N ->
  ep xa xb m (ofN j) = ofN (getl a j) /\ oth xa xb m (ofN j) = ofN (getl b j).
Proof.
  intros j Hj. pose proof M_lens as (L1 & _ & _ & L4). pose proof M_nb.
  assert (Pj : (φ (ofN j)) = Z.of_N j) by (apply phi_ofN; rewrite wB_val; lia).
  assert (Tj : toN (ofN j) = j) by (apply toN_ofN; rewrite wB_val; lia).
  unfold ep, oth. replace (ofN j <? m) with true by (symmetry; rewrite ltb_spec; lia).
  destruct Hv as [_ _ [_ [T2 _]] Va Vb _ _ _ _ _ _].
  pose proof (Forall_getl _ a j Va Hj) as [A1 A2].
  pose proof (Forall_getl _ b j Vb ltac:(rewrite T2; exact Hj)) as [B1 B2].
  split; apply to_Z_inj; [rewrite GA by lia | rewrite GB by lia]; rewrite Tj;
    symmetry; apply phi_ofN; rewrite wB_val; rewrite M_n in *; lia.
Qed.

Lemma ep_hi : forall j : N, (j < len a)%N ->
  ep xa xb m (ofN j + m) = ofN (getl b j) /\ oth xa xb m (ofN j + m) = ofN (getl a j).
Proof.
  intros j Hj. pose proof M_lens as (L1 & _ & _ & L4). pose proof M_nb.
  assert (Pj : (φ (ofN j)) = Z.of_N j) by (apply phi_ofN; rewrite wB_val; lia).
  assert (Tj : toN (ofN j) = j) by (apply toN_ofN; rewrite wB_val; lia).
  assert (Pk : (φ (ofN j + m)) = (Z.of_N j + (φ m))%Z) by (rewrite <- Pj; sia).
  assert (Ek : ofN j + m - m = ofN j).
  { apply to_Z_inj. rewrite sub_spec, Pk, Pj.
    replace (Z.of_N j + (φ m) - (φ m))%Z with (Z.of_N j) by ring.
    apply Z.mod_small. rewrite wB_val. lia. }
  unfold ep, oth. replace (ofN j + m <? m) with false
    by (symmetry; rewrite <- Bool.not_true_iff_false, ltb_spec; lia).
  rewrite Ek.
  destruct Hv as [_ _ [_ [T2 _]] Va Vb _ _ _ _ _ _].
  pose proof (Forall_getl _ a j Va Hj) as [A1 A2].
  pose proof (Forall_getl _ b j Vb ltac:(rewrite T2; exact Hj)) as [B1 B2].
  split; apply to_Z_inj; [rewrite GB by lia | rewrite GA by lia]; rewrite Tj;
    symmetry; apply phi_ofN; rewrite wB_val; rewrite M_n in *; lia.
Qed.

Lemma M_closure : forall u : int, (1 <= (φ u) <= (φ xn))%Z -> (vis st).[u] = true ->
  forall k : int, ((φ k) < 2 * (φ m))%Z -> ep xa xb m k = u ->
  (vis st).[oth xa xb m k] = true.
Proof.
  intros u Hu Hvu k Hk Ek. pose proof M_bfs as I.
  destruct (iv_vis _ _ _ _ _ _ _ I u Hu Hvu) as (t & Ht & Ot).
  apply (iv_done _ _ _ _ _ _ _ I t Ht k Hk). rewrite Ot. exact Ek.
Qed.

Lemma M_chain : forall js u v, inter n u -> (vis st).[ofN u] = true ->
  chain a b u js v -> (vis st).[ofN v] = true.
Proof.
  induction js as [|j js IH]; intros u v Hu Hvu Hc.
  - cbn in Hc. subst. exact Hvu.
  - destruct Hc as [Hj [[Ea Hc]|[Eb Hc]]].
    + destruct Hv as [_ _ [_ [T2 _]] _ Vb _ _ _ _ _ _].
      apply (IH (getl b j) v); [| | exact Hc].
      * apply (Forall_getl _ b j Vb). rewrite T2. exact Hj.
      * destruct (ep_lo j Hj) as [E1 E2]. rewrite <- E2.
        apply (M_closure (ofN u)); [rewrite M_small by exact Hu; rewrite M_n; unfold inter in Hu; lia | exact Hvu | | ].
        -- pose proof M_lens as (L1 & _ & _ & L4). pose proof M_nb.
           rewrite phi_ofN by (rewrite wB_val; lia). lia.
        -- rewrite E1, Ea. reflexivity.
    + destruct Hv as [_ _ _ Va _ _ _ _ _ _ _].
      apply (IH (getl a j) v); [| | exact Hc].
      * apply (Forall_getl _ a j Va). exact Hj.
      * destruct (ep_hi j Hj) as [E1 E2]. rewrite <- E2.
        apply (M_closure (ofN u)); [rewrite M_small by exact Hu; rewrite M_n; unfold inter in Hu; lia | exact Hvu | | ].
        -- pose proof M_lens as (L1 & _ & _ & L4). pose proof M_nb.
           assert (Pj : (φ (ofN j)) = Z.of_N j) by (apply phi_ofN; rewrite wB_val; lia).
           assert ((φ (ofN j + m)) = (Z.of_N j + (φ m))%Z) by (rewrite <- Pj; sia). lia.
        -- rewrite E1, Eb. reflexivity.
Qed.

Lemma M_allvis : forall v : N, inter n v -> (vis st).[ofN v] = true.
Proof.
  intros v Hvv.
  assert (H1 : inter n 1%N) by (destruct Hv as [[H1 H2] _ _ _ _ _ _ _ _ _ _]; split; lia).
  destruct Hv as [_ _ _ _ _ _ Vr _ _ _ _].
  destruct (Vr 1%N v H1 Hvv) as (js & Hc & _).
  apply (M_chain js 1%N v H1); [| exact Hc].
  pose proof M_bfs as I. pose proof (iv_ord _ _ _ _ _ _ _ I 0 ltac:(pose proof (iv_tl _ _ _ _ _ _ _ I); change (φ 0) with 0%Z; lia)) as [_ O1].
  rewrite (iv_o0 _ _ _ _ _ _ _ I) in O1. exact O1.
Qed.

Lemma M_tl : (φ (tl st)) = (φ xn).
Proof.
  pose proof M_bfs as I. pose proof (iv_tl _ _ _ _ _ _ _ I) as Tl. pose proof M_nb.
  enough (Z.to_nat (φ xn) <= Z.to_nat (φ (tl st)))%nat by lia.
  apply (cover_le (fun t => (φ ((ord st).[of_Z (Z.of_nat t)]))) _ 1%Z).
  intros i Hi.
  set (v := N.of_nat (S i)).
  assert (Hvv : inter n v) by (unfold v, inter; rewrite M_n in *; lia).
  destruct (iv_vis _ _ _ _ _ _ _ I (ofN v) ltac:(rewrite M_small by exact Hvv; unfold inter in Hvv; rewrite M_n; lia) (M_allvis v Hvv))
    as (t & Ht & Ot).
  exists (Z.to_nat (φ t)). split; [lia|].
  rewrite Z2Nat.id by (pose proof (to_Z_bounded t); lia). rewrite of_to_Z, Ot.
  rewrite M_small by exact Hvv. unfold v. lia.
Qed.

Lemma M_edges : forall e : int, ((φ e) < (φ m))%Z ->
  exists t : int, (0 < (φ t) < (φ (tl st)))%Z /\ (pe st).[(ord st).[t]] = e.
Proof.
  intros e He. pose proof M_bfs as I. pose proof M_tl as Tl. pose proof M_nb.
  pose proof M_lens as (L1 & _).
  set (g := fun t : nat => (φ ((pe st).[(ord st).[of_Z (Z.of_nat (S t))]]))).
  assert (Hg : forall t, (t < Z.to_nat (φ (tl st)) - 1)%nat ->
             (φ (of_Z (Z.of_nat (S t)))) = Z.of_nat (S t)).
  { intros t Ht. apply phi_ofZ. rewrite wB_val. lia. }
  destruct (pigeon_surj g (Z.to_nat (φ (tl st)) - 1) (Z.to_nat (φ m))) with (e := (φ e))
    as (t & Ht & Gt).
  - intros t Ht. unfold g.
    destruct (iv_tree _ _ _ _ _ _ _ I (of_Z (Z.of_nat (S t))) ltac:(rewrite Hg by exact Ht; lia))
      as (T1 & _).
    pose proof (to_Z_bounded ((pe st).[(ord st).[of_Z (Z.of_nat (S t))]])). lia.
  - intros t1 t2 H1 H2 E. unfold g in E. apply to_Z_inj in E.
    set (u1 := of_Z (Z.of_nat (S t1))) in *. set (u2 := of_Z (Z.of_nat (S t2))) in *.
    pose proof (Hg t1 H1) as P1. pose proof (Hg t2 H2) as P2. fold u1 in P1. fold u2 in P2.
    destruct (iv_tree _ _ _ _ _ _ _ I u1 ltac:(lia)) as (_ & R1 & (s1 & S1 & O1) & _).
    destruct (iv_tree _ _ _ _ _ _ _ I u2 ltac:(lia)) as (_ & R2 & (s2 & S2 & O2) & _).
    rewrite E in R1. unfold rel in R1, R2.
    assert (Inj := iv_inj _ _ _ _ _ _ _ I).
    destruct (Nat.eq_dec t1 t2) as [Et|Et]; [exact Et|]. exfalso.
    assert (Nw : (ord st).[u1] <> (ord st).[u2]).
    { intro F. apply Inj in F; [|lia|lia]. apply (f_equal to_Z) in F. lia. }
    destruct R1 as [[A1 B1]|[B1 A1]]; destruct R2 as [[A2 B2]|[B2 A2]].
    + apply Nw. congruence.
    + (* par u1 = u2's vertex, par u2 = u1's vertex *)
      assert (X1 : (ord st).[s1] = (ord st).[u2]) by congruence.
      assert (X2 : (ord st).[s2] = (ord st).[u1]) by congruence.
      apply Inj in X1; [|lia|lia]. apply Inj in X2; [|lia|lia].
      subst. lia.
    + assert (X1 : (ord st).[s1] = (ord st).[u2]) by congruence.
      assert (X2 : (ord st).[s2] = (ord st).[u1]) by congruence.
      apply Inj in X1; [|lia|lia]. apply Inj in X2; [|lia|lia].
      subst. lia.
    + apply Nw. congruence.
  - lia.
  - pose proof (to_Z_bounded e). lia.
  - exists (of_Z (Z.of_nat (S t))). rewrite Hg by exact Ht. split; [lia|].
    apply to_Z_inj. exact Gt.
Qed.

Definition distM (v : N) : N := toN ((dst st).[ofN v]).

Lemma toN_inter : forall x : int, (1 <= (φ x) <= (φ xn))%Z -> inter n (toN x).
Proof. intros x Hx. unfold inter, toN. rewrite M_n in Hx. lia. Qed.

Lemma edge_math : forall t : int, (0 < (φ t) < (φ (tl st)))%Z ->
  (toN ((pe st).[(ord st).[t]]) < len a)%N /\
  ((getl a (toN ((pe st).[(ord st).[t]])) = toN ((par st).[(ord st).[t]]) /\
    getl b (toN ((pe st).[(ord st).[t]])) = toN ((ord st).[t])) \/
   (getl b (toN ((pe st).[(ord st).[t]])) = toN ((par st).[(ord st).[t]]) /\
    getl a (toN ((pe st).[(ord st).[t]])) = toN ((ord st).[t]))) /\
  distM (toN ((ord st).[t])) =
    (distM (toN ((par st).[(ord st).[t]])) + getl d (toN ((pe st).[(ord st).[t]])))%N /\
  inter n (toN ((par st).[(ord st).[t]])) /\ inter n (toN ((ord st).[t])).
Proof.
  intros t Ht. pose proof M_bfs as I.
  destruct (iv_tree _ _ _ _ _ _ _ I t Ht) as (Te & R & (t' & Ht' & Ot') & Dst).
  pose proof (iv_ord _ _ _ _ _ _ _ I t ltac:(lia)) as [Iw _].
  pose proof (iv_ord _ _ _ _ _ _ _ I t' ltac:(lia)) as [Ip _]. rewrite Ot' in Ip.
  set (w := (ord st).[t]) in *. set (e := (pe st).[w]) in *. set (p := (par st).[w]) in *.
  pose proof M_lens as (_ & _ & _ & L4).
  split; [unfold toN; lia|].
  split.
  - unfold rel in R. destruct R as [[A B]|[B A]]; [left | right]; split.
    + apply (f_equal to_Z) in A. rewrite GA in A by exact Te. unfold toN in *. lia.
    + apply (f_equal to_Z) in B. rewrite GB in B by exact Te. unfold toN in *. lia.
    + apply (f_equal to_Z) in B. rewrite GB in B by exact Te. unfold toN in *. lia.
    + apply (f_equal to_Z) in A. rewrite GA in A by exact Te. unfold toN in *. lia.
  - split; [|split; apply toN_inter; assumption].
    unfold distM. rewrite !ofN_toN. rewrite GD in Dst by exact Te.
    pose proof (to_Z_bounded ((dst st).[p])). unfold toN in *. lia.
Qed.

Lemma J_lb : len b = len a.
Proof. destruct Hv as [_ _ [_ [T2 _]] _ _ _ _ _ _ _ _]. exact T2. Qed.

Lemma J_ld : len d = len a.
Proof. destruct Hv as [_ _ [_ [_ T3]] _ _ _ _ _ _ _ _]. exact T3. Qed.

Lemma J_d : forall j, (j < len a)%N -> (1 <= getl d j)%N.
Proof.
  intros j Hj. destruct Hv as [_ _ [_ [_ T3]] _ _ Vd _ _ _ _ _].
  apply (Forall_getl _ d j Vd). rewrite T3. exact Hj.
Qed.

Lemma J_edge : forall j, (j < len a)%N ->
  distM (getl b j) = (distM (getl a j) + getl d j)%N \/
  distM (getl a j) = (distM (getl b j) + getl d j)%N.
Proof.
  intros j Hj. pose proof M_lens as (_ & _ & _ & L4). pose proof M_nb.
  assert (Pj : (φ (ofN j)) = Z.of_N j) by (apply phi_ofN; rewrite wB_val; lia).
  destruct (M_edges (ofN j) ltac:(lia)) as (t & Ht & Et).
  destruct (edge_math t Ht) as (_ & Hor & Hd' & _).
  rewrite Et, toN_ofN in Hor, Hd' by (rewrite wB_val; lia).
  destruct Hor as [[A B]|[B A]]; rewrite A, B; [left | right]; exact Hd'.
Qed.

Lemma J_d1 : distM 1%N = 0%N.
Proof.
  unfold distM. pose proof M_bfs as I. change (ofN 1%N) with 1.
  rewrite (iv_d1 _ _ _ _ _ _ _ I). reflexivity.
Qed.

Lemma J_up : forall v, inter n v -> v <> 1%N -> exists e p,
  (e < len a)%N /\ inter n p /\
  ((getl a e = p /\ getl b e = v) \/ (getl b e = p /\ getl a e = v)) /\
  distM v = (distM p + getl d e)%N.
Proof.
  intros v Hvv Hv1. pose proof M_bfs as I.
  destruct (iv_vis _ _ _ _ _ _ _ I (ofN v)
              ltac:(rewrite M_small by exact Hvv; unfold inter in Hvv; rewrite M_n; lia)
              (M_allvis v Hvv)) as (t & Ht & Ot).
  assert (Ht0 : (0 < (φ t))%Z).
  { destruct (Z.eq_dec (φ t) 0) as [E|E]; [|pose proof (to_Z_bounded t); lia].
    exfalso. apply Hv1. assert (t = 0) by (apply to_Z_inj; exact E). subst t.
    rewrite (iv_o0 _ _ _ _ _ _ _ I) in Ot. apply (f_equal to_Z) in Ot.
    rewrite M_small in Ot by exact Hvv. change (φ 1) with 1%Z in Ot. lia. }
  destruct (edge_math t ltac:(lia)) as (He & Hor & Hd' & Hp & _).
  rewrite Ot in Hor, Hd'. unfold ofN in Hor, Hd' at 1.
  assert (Tv : toN (ofN v) = v) by (apply toN_ofN; pose proof M_nb; rewrite M_n in *;
    unfold inter in Hvv; rewrite wB_val; lia).
  unfold ofN in Tv. rewrite Tv in Hor, Hd'.
  exists (toN ((pe st).[(ord st).[t]])), (toN ((par st).[(ord st).[t]])).
  split; [exact He|]. split; [exact Hp|]. rewrite Ot. split; [exact Hor | exact Hd'].
Qed.

Lemma nodup_choice : forall (A B : Type) (g1 g2 f : A -> B) (ms : list A),
  NoDup (map g1 ms ++ map g2 ms) ->
  (forall x, In x ms -> f x = g1 x \/ f x = g2 x) -> NoDup (map f ms).
Proof.
  intros A B g1 g2 f ms. induction ms as [|x r IH]; intros ND Hf; [constructor|].
  cbn [map app] in ND. apply NoDup_cons_iff in ND. destruct ND as [N1 ND].
  apply NoDup_remove in ND. destruct ND as [ND N2].
  cbn [map]. apply NoDup_cons.
  - intro F. apply in_map_iff in F. destruct F as (y & Ey & Iy).
    assert (Hy : In (f y) (map g1 r ++ map g2 r)).
    { apply in_or_app. destruct (Hf y (or_intror Iy)) as [E|E]; rewrite E;
        [left | right]; apply in_map; exact Iy. }
    rewrite Ey in Hy. destruct (Hf x (or_introl eq_refl)) as [E|E]; rewrite E in Hy.
    + apply N1. apply in_app_or in Hy. apply in_or_app.
      destruct Hy as [Hy|Hy]; [left; exact Hy | right; right; exact Hy].
    + apply N2. exact Hy.
  - apply IH; [exact ND|]. intros y Iy. apply Hf. right. exact Iy.
Qed.

Lemma NoDup_toN : forall l0 : list int, NoDup l0 -> NoDup (map toN l0).
Proof.
  intros l0 H. apply NoDup_map_NoDup_ForallPairs; [|exact H].
  intros x y _ _ E. apply toN_inj. exact E.
Qed.

Lemma impl_eq : joggers_impl xn xs xa xb xd xl =
  sweep_loop xs inl (ord st) (par st) (dst st) (tl st - 1) (PArray.make V false) 0
    (Zwf_well_founded 0 _).
Proof. reflexivity. Qed.

Lemma M_sweep : exists chf ms,
  SInv xs inl (ord st) (par st) (dst st) (tl st) xn 0 chf
    (sweep_loop xs inl (ord st) (par st) (dst st) (tl st - 1) (PArray.make V false) 0
       (Zwf_well_founded 0 _)) ms.
Proof.
  pose proof M_bfs as I. pose proof (iv_tl _ _ _ _ _ _ _ I) as Tl.
  assert (HO : forall t : int, ((φ t) < (φ (tl st)))%Z -> (1 <= (φ ((ord st).[t])) <= (φ xn))%Z)
    by (intros t Ht; apply (iv_ord _ _ _ _ _ _ _ I t Ht)).
  assert (HP : forall t : int, (0 < (φ t) < (φ (tl st)))%Z ->
     exists t' : int, ((φ t') < (φ t))%Z /\ (ord st).[t'] = (par st).[(ord st).[t]])
    by (intros t Ht; apply (iv_tree _ _ _ _ _ _ _ I t Ht)).
  apply (sweep_spec xs inl (ord st) (par st) (dst st) (tl st) xn M_nb Tl HO
           (iv_inj _ _ _ _ _ _ _ I) HP (iv_db _ _ _ _ _ _ _ I) _ (tl st - 1) _ 0 [] _ eq_refl).
  apply sweep_init; [exact M_nb|]. sia.
Qed.

Lemma Linl1 : forall x : int, (1 <= (φ x) <= (φ xn))%Z -> inl.[x] = true -> In (toN x) l.
Proof.
  intros x Hx Hi. apply M_inl in Hi; [|rewrite M_V; lia].
  destruct Hi as (t & Ht & Et). pose proof (GL t Ht) as G. rewrite Et in G.
  assert (E : toN x = getl l (toN t)) by (unfold toN in *; lia).
  rewrite E. unfold getl, Prelude.get. apply nth_In.
  pose proof M_L as [L _]. unfold toN. lia.
Qed.

Lemma Linl2 : forall x : int, (1 <= (φ x) <= (φ xn))%Z -> In (toN x) l -> inl.[x] = true.
Proof.
  intros x Hx Hin. apply In_nth with (d := 0%N) in Hin. destruct Hin as (k & Hk & Ek).
  pose proof M_L as [L1 L2]. pose proof M_nb.
  apply M_inl; [rewrite M_V; lia|].
  exists (of_Z (Z.of_nat k)).
  assert (Pk : (φ (of_Z (Z.of_nat k))) = Z.of_nat k) by (apply phi_ofZ; rewrite wB_val; lia).
  split; [lia|].
  apply to_Z_inj. rewrite GL by lia. unfold getl, Prelude.get.
  replace (N.to_nat (toN (of_Z (Z.of_nat k)))) with k by (unfold toN; lia).
  rewrite Ek. unfold toN. pose proof (to_Z_bounded x). lia.
Qed.

Theorem M_correct : exists o : N,
  repr (joggers_impl xn xs xa xb xd xl : uint) o /\ joggers_spec n s a b d l o.
Proof.
  pose proof M_bfs as I. pose proof M_tl as Tl. pose proof M_nb as Nb.
  pose proof M_lens as (Lm & _ & _ & La).
  destruct M_sweep as (chf & ms & SI). rewrite impl_eq.
  set (c := sweep_loop xs inl (ord st) (par st) (dst st) (tl st - 1) (PArray.make V false) 0
              (Zwf_well_founded 0 _)) in *.
  exists (toN c). split; [reflexivity|].
  destruct SI as [Lc Ch ND Cc Ci Pos Ok Cov].
  change (φ 0) with 0%Z in Pos, Cov.
  set (P := par st) in *. set (O := ord st) in *.
  assert (Ord : forall t : int, ((φ t) < (φ (tl st)))%Z -> (1 <= (φ (O.[t])) <= (φ xn))%Z)
    by (intros t Ht; apply (iv_ord _ _ _ _ _ _ _ I t Ht)).
  assert (ParR : forall t : int, (0 < (φ t) < (φ (tl st)))%Z -> (1 <= (φ (P.[O.[t]])) <= (φ xn))%Z).
  { intros t Ht. destruct (iv_tree _ _ _ _ _ _ _ I t Ht) as (_ & _ & (t' & Ht' & Ot') & _).
    fold O P in Ot'. rewrite <- Ot'. apply Ord. lia. }
  set (xs' := map (fun x => toN (P.[x])) ms).
  assert (Hlit : forall x : int, (1 <= (φ x) <= (φ xn))%Z -> lit inl chf x = true ->
            In (toN x) l \/ In (toN x) xs').
  { intros x Hx Hl. unfold lit in Hl. apply Bool.orb_true_iff in Hl. destruct Hl as [Hl|Hl].
    - left. apply Linl1; assumption.
    - right. apply Ch in Hl; [|lia]. unfold xs'. rewrite <- map_map with (f := fun y => P.[y]).
      apply in_map. exact Hl. }
  assert (Hus : forall x : int, used_m xs P (dst st) x <->
            (2 * distM (toN (P.[x])) < s)%N).
  { intros x. unfold used_m, distM. rewrite ofN_toN. rewrite M_s.
    pose proof (to_Z_bounded ((dst st).[P.[x]])). unfold toN. lia. }
  split.
  - exists xs'. split; [split|split].
    + unfold xs'. rewrite <- map_map with (f := fun y => P.[y]).
      apply NoDup_toN. apply NoDup_app_remove_l in ND. exact ND.
    + unfold xs'. apply Forall_forall. intros v Hin. apply in_map_iff in Hin.
      destruct Hin as (x & <- & Hx). destruct (Pos x Hx) as (t & Ht & <-).
      apply toN_inter. apply ParR. exact Ht.
    + intros j Hj Hu.
      assert (Pj : (φ (ofN j)) = Z.of_N j) by (apply phi_ofN; rewrite wB_val; lia).
      destruct (M_edges (ofN j) ltac:(lia)) as (t & Ht & Et).
      destruct (edge_math t Ht) as (_ & Hor & Hd' & _ & _).
      fold O P in Hor, Hd'. fold O in Et. rewrite Et, toN_ofN in Hor, Hd' by (rewrite wB_val; lia).
      pose proof (used_nec s a b d distM J_lb J_ld J_d J_edge J_d1 j _ _ Hj Hor Hd' Hu) as U.
      apply Hus in U.
      unfold Prelude.lit.
      destruct (Cov t Ht U) as [L|L].
      * apply Hlit in L; [|apply Ord; lia].
        destruct Hor as [[A B]|[B A]]; rewrite A, B; [right | left]; exact L.
      * apply Hlit in L; [|apply ParR; exact Ht].
        destruct Hor as [[A B]|[B A]]; rewrite A, B; [left | right]; exact L.
    + unfold xs', len. rewrite length_map. unfold toN. rewrite Cc. lia.
  - intros ys [NDy Fy] Sy.
    assert (Hcl : forall x, In x ms -> In (toN x) ys \/ In (toN (P.[x])) ys).
    { intros x Hx. destruct (Pos x Hx) as (t & Ht & Ot).
      destruct (edge_math t Ht) as (Hj & Hor & Hd' & Hp & Hc).
      fold O P in Hj, Hor, Hd', Hp, Hc. rewrite Ot in Hj, Hor, Hd', Hp, Hc.
      destruct (Ok x Hx) as (I1 & I2 & U).
      apply Hus in U.
      assert (Hs1 : (1 <= s)%N) by (destruct Hv as [_ [S1 _] _ _ _ _ _ _ _ _ _]; exact S1).
      pose proof (used_suf n s a b d distM J_lb J_ld J_d J_d1 J_up _ _ _ Hj Hor Hp Hs1 U)
        as Hu.
      pose proof (Sy _ Hj Hu) as Hlit2.
      assert (Nx : ~ In (toN x) l).
      { intro F. apply Linl2 in F; [congruence|]. rewrite <- Ot. apply Ord. lia. }
      assert (Np : ~ In (toN (P.[x])) l).
      { intro F. apply Linl2 in F; [congruence|]. rewrite <- Ot. apply ParR. exact Ht. }
      unfold Prelude.lit in Hlit2.
      destruct Hor as [[A B]|[B A]]; rewrite A, B in Hlit2;
        destruct Hlit2 as [[H|H]|[H|H]];
        first [ exfalso; solve [auto] | left; exact H | right; exact H ]. }
    set (f := fun x => if in_dec N.eq_dec (toN x) ys then toN x else toN (P.[x])).
    assert (Hf : NoDup (map f ms)).
    { apply (nodup_choice _ _ toN (fun x => toN (P.[x])) f ms).
      - rewrite <- map_map with (f := fun y => P.[y]). rewrite <- map_app.
        apply NoDup_toN. exact ND.
      - intros x _. unfold f. destruct (in_dec N.eq_dec (toN x) ys); [left | right]; reflexivity. }
    assert (Hi : incl (map f ms) ys).
    { intros v Hin. apply in_map_iff in Hin. destruct Hin as (x & <- & Hx). unfold f.
      destruct (in_dec N.eq_dec (toN x) ys) as [Y|Y]; [exact Y|].
      destruct (Hcl x Hx) as [Z|Z]; [contradiction | exact Z]. }
    pose proof (NoDup_incl_length Hf Hi) as Le. rewrite length_map in Le.
    unfold len. unfold toN. rewrite Cc. lia.
Qed.

End Main.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition joggers : uint -> uint -> array uint -> array uint ->
  array uint -> array uint -> uint := joggers_impl.

Definition joggers_correct :
  forall (n s : N) (a b d l : list N) (xn xs : uint)
         (xa xb xd xl : array uint),
  valid_input n s a b d l ->
  repr xn n -> repr xs s -> repr xa a -> repr xb b -> repr xd d ->
  repr xl l ->
  exists o : N, repr (joggers xn xs xa xb xd xl) o /\
    joggers_spec n s a b d l o
  := M_correct.
