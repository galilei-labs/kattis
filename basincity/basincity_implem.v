(* Executable implementation and its required termination dependencies.
   Correctness proofs are in basincity_proofs.v. *)
From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.
Open Scope bool_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* Abstract graph lemmas (Prop side)                                   *)
(* ------------------------------------------------------------------ *)

Section Graph.
  Variable Eb : int -> int -> bool.
  Hypothesis Esym : forall a b, Eb a b = true -> Eb b a = true.
  Hypothesis Eirr : forall a, Eb a a = false.

  Definition closedNb (u x : int) : bool := (x =? u) || Eb u x.

  Definition minus (P : int -> Prop) (u : int) : int -> Prop :=
    fun x => P x /\ closedNb u x = false.

  Definition indep (P : int -> Prop) (S : list int) : Prop :=
    NoDup S /\ (forall x, In x S -> P x) /\
    (forall x y, In x S -> In y S -> Eb x y = false).

  Definition has (P : int -> Prop) (k : nat) : Prop :=
    exists S, List.length S = k /\ indep P S.

  Lemma has_ext : forall P Q k, (forall x, P x <-> Q x) -> has P k -> has Q k.
  Proof.
    intros P Q k HPQ (S & HS & HN & HP & HE). exists S; repeat split; auto.
    intros x Hx. apply HPQ, HP, Hx.
  Qed.

  Lemma has_iff : forall P Q k, (forall x, P x <-> Q x) -> (has P k <-> has Q k).
  Proof.
    intros P Q k H; split; apply has_ext; intro x; specialize (H x); tauto.
  Qed.

  Lemma has_zero : forall P, has P 0.
  Proof.
    intros P. exists []. repeat split; simpl; try tauto. constructor.
  Qed.

  Lemma has_nonempty : forall P k, has P (S k) -> exists x, P x.
  Proof.
    intros P k ([| s S] & HS & _ & HP & _); [discriminate|].
    exists s. apply HP. left. reflexivity.
  Qed.

  Lemma closed_self : forall u, closedNb u u = true.
  Proof. intros u. unfold closedNb. rewrite eqb_refl. reflexivity. Qed.

  (* taking u *)
  Lemma has_take : forall P u k, P u -> has (minus P u) k -> has P (S k).
  Proof.
    intros P u k Hu (S & HS & HN & HP & HE).
    exists (u :: S). split; [simpl; congruence|].
    repeat split.
    - constructor; [|exact HN]. intro Hin. destruct (HP u Hin) as [_ Hc].
      rewrite closed_self in Hc. discriminate.
    - intros x [<- | Hx]; [exact Hu | apply HP, Hx].
    - assert (Hux : forall x, In x S -> Eb u x = false).
      { intros x Hx. destruct (HP x Hx) as [_ Hc]. unfold closedNb in Hc.
        apply Bool.orb_false_iff in Hc. tauto. }
      intros x y [<- | Hx] [<- | Hy].
      + apply Eirr.
      + apply Hux, Hy.
      + destruct (Eb x u) eqn:E; [|reflexivity].
        apply Esym in E. rewrite Hux in E by exact Hx. discriminate.
      + apply HE; assumption.
  Qed.

  Lemma in_split_nodup : forall (T : list int) u, NoDup T -> In u T ->
    exists T', List.length T' = (List.length T - 1)%nat /\ NoDup T' /\
      (forall x, In x T' -> In x T /\ x <> u).
  Proof.
    intros T u HN Hu. destruct (in_split u T Hu) as (l1 & l2 & ->).
    exists (l1 ++ l2). rewrite !length_app. simpl. split; [lia|].
    split; [eapply NoDup_remove_1; eauto|].
    intros x Hx. split.
    - apply in_app_or in Hx. apply in_or_app. simpl. tauto.
    - intros ->. eapply NoDup_remove_2; eauto.
  Qed.

  (* branching over the closed neighbourhood of v *)
  Lemma has_branch : forall P v k, P v -> has P (S k) ->
    exists u, closedNb v u = true /\ P u /\ has (minus P u) k.
  Proof.
    intros P v k Hv (S & HS & HN & HP & HE).
    destruct (existsb (closedNb v) S) eqn:Ex.
    - apply existsb_exists in Ex. destruct Ex as (u & Hu & Hc).
      exists u. split; [exact Hc|]. split; [apply HP, Hu|].
      destruct (in_split_nodup S u HN Hu) as (S' & HS' & HN' & Hin).
      exists S'. split; [rewrite HS', HS; simpl; lia|].
      unfold indep, minus. split; [exact HN'|]. split.
      + intros x Hx. split; [apply HP, Hin, Hx|].
        unfold closedNb. apply Bool.orb_false_iff. split.
        * apply eqb_false_spec. apply Hin, Hx.
        * apply HE; [exact Hu | apply Hin, Hx].
      + intros x y Hx Hy. apply HE; apply Hin; assumption.
    - destruct S as [| s S0]; [discriminate|].
      exists v. split; [apply closed_self|]. split; [exact Hv|].
      exists S0. split; [simpl in HS; congruence|].
      repeat split.
      + inversion HN; assumption.
      + apply HP. right. exact H.
      + destruct (closedNb v x) eqn:Ec; [|reflexivity].
        assert (existsb (closedNb v) (s :: S0) = true) as F
          by (apply existsb_exists; exists x; split; [right; exact H | exact Ec]).
        rewrite F in Ex. discriminate.
      + intros x y Hx Hy. apply HE; right; assumption.
  Qed.

  Definition simplicial (P : int -> Prop) (v : int) : Prop :=
    forall a b, P a -> P b -> Eb v a = true -> Eb v b = true -> a <> b ->
      Eb a b = true.

  (* a simplicial vertex can be taken without branching *)
  Lemma has_simplicial : forall P v k, P v -> simplicial P v -> has P (S k) ->
    has (minus P v) k.
  Proof.
    intros P v k Hv Hs Hh.
    destruct (has_branch P v k Hv Hh) as (u & Hc & Hu & S & HS & HN & HP & HE).
    unfold closedNb in Hc. apply Bool.orb_true_iff in Hc.
    destruct Hc as [Hc | Hc].
    - apply eqb_correct in Hc. subst u. exists S; split; [exact HS|].
      exact (conj HN (conj HP HE)).
    - exists S. repeat split; auto.
      + apply HP, H.
      + destruct (HP x H) as [Px Cx]. unfold closedNb in Cx |- *.
        apply Bool.orb_false_iff in Cx. destruct Cx as [Cx1 Cx2].
        apply Bool.orb_false_iff. split.
        * apply eqb_false_spec. intros ->. apply Esym in Hc. congruence.
        * destruct (Eb v x) eqn:E; [|reflexivity].
          assert (Eb u x = true); [|congruence].
          apply Hs; auto. apply eqb_false_spec in Cx1. congruence.
  Qed.

  (* the degree-4 kernel *)
  Hypothesis Edeg : forall x, exists M, (List.length M <= 4)%nat /\
    forall y, Eb x y = true -> In y M.

  Lemma has_kernel : forall k (L : list int) P, NoDup L ->
    (forall x, P x <-> In x L) -> (5 * k <= List.length L)%nat -> has P k.
  Proof.
    induction k as [| k IH]; intros L P HN HPL HL; [apply has_zero|].
    destruct L as [| x L0]; [simpl in HL; lia|].
    assert (Px : P x) by (apply HPL; left; reflexivity).
    apply (has_take P x); [exact Px|].
    set (L' := filter (fun y => negb (closedNb x y)) (x :: L0)).
    apply (IH L').
    - apply NoDup_filter. exact HN.
    - intros y. unfold minus, L'. rewrite filter_In, HPL.
      rewrite Bool.negb_true_iff. tauto.
    - destruct (Edeg x) as (M & HM & HMy).
      assert (Hc : (List.length (filter (closedNb x) (x :: L0)) <= 5)%nat).
      { change 5%nat with (S 4).
        apply (Nat.le_trans _ (List.length (x :: M))); [| simpl; lia].
        apply NoDup_incl_length; [apply NoDup_filter, HN|].
        intros y Hy. apply filter_In in Hy. destruct Hy as [_ Hy].
        unfold closedNb in Hy. apply Bool.orb_true_iff in Hy.
        destruct Hy as [Hy | Hy]; [apply eqb_correct in Hy; left; congruence|].
        right. apply HMy, Hy. }
      pose proof (filter_length (closedNb x) (x :: L0)) as Hf.
      unfold L'. lia.
  Qed.
End Graph.

(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
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

Lemma eqb_true_iff' : forall a b : int, (a =? b) = true <-> a = b.
Proof. intros a b. apply eqb_spec. Qed.

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

Lemma dec_k : forall k : int, (k =? 0) = false -> Zwf 0 (φ (k - 1)) (φ k).
Proof.
  intros k H. rewrite eqb_false_spec in H.
  assert ((φ k) <> 0%Z) by (intro E; apply H, to_Z_inj; exact E).
  pose proof (to_Z_bounded k). unfold Zwf. sia.
Qed.

(* ------------------------------------------------------------------ *)
(* Four-slot combinators (a vertex has at most four neighbours)        *)
(* ------------------------------------------------------------------ *)

Definition exists4 (f : int -> bool) (d : int) : bool :=
  ((0 <? d) && f 0) || ((1 <? d) && f 1) || ((2 <? d) && f 2) || ((3 <? d) && f 3).

Definition forall4 (f : int -> bool) (d : int) : bool :=
  (negb (0 <? d) || f 0) && (negb (1 <? d) || f 1) &&
  (negb (2 <? d) || f 2) && (negb (3 <? d) || f 3).

Definition b2i (b : bool) : int := if b then 1 else 0.

Definition count4 (f : int -> bool) (d : int) : int :=
  b2i ((0 <? d) && f 0) + b2i ((1 <? d) && f 1) +
  b2i ((2 <? d) && f 2) + b2i ((3 <? d) && f 3).

Lemma small4 : forall j : int, ((φ j) < 4)%Z -> j = 0 \/ j = 1 \/ j = 2 \/ j = 3.
Proof.
  intros j H. pose proof (to_Z_bounded j).
  assert ((φ j) = 0 \/ (φ j) = 1 \/ (φ j) = 2 \/ (φ j) = 3)%Z as [E|[E|[E|E]]] by lia;
    [left | right; left | right; right; left | right; right; right];
    apply to_Z_inj; exact E.
Qed.

Lemma ltb_Z : forall a b : int, (a <? b) = true <-> ((φ a) < (φ b))%Z.
Proof. intros. apply ltb_spec. Qed.

Lemma exists4_spec : forall f d, ((φ d) <= 4)%Z ->
  (exists4 f d = true <-> exists j, ((φ j) < (φ d))%Z /\ f j = true).
Proof.
  intros f d Hd. unfold exists4. split.
  - intros H. repeat rewrite Bool.orb_true_iff in H.
    repeat rewrite Bool.andb_true_iff in H. rewrite !ltb_Z in H.
    destruct H as [[[H|H]|H]|H]; eexists; exact (conj (proj1 H) (proj2 H)).
  - intros (j & Hj & Hf). pose proof (to_Z_bounded j).
    destruct (small4 j ltac:(lia)) as [-> | [-> | [-> | ->]]];
      rewrite Hf; rewrite (proj2 (ltb_Z _ _) Hj); simpl;
      rewrite ?Bool.orb_true_r; reflexivity.
Qed.

Lemma forall4_true : forall f d, forall4 f d = true ->
  forall j, ((φ j) < (φ d))%Z -> ((φ j) < 4)%Z -> f j = true.
Proof.
  intros f d H j Hj H4. unfold forall4 in H.
  repeat rewrite Bool.andb_true_iff in H.
  destruct (small4 j H4) as [-> | [-> | [-> | ->]]];
    [destruct H as [[[H _] _] _] | destruct H as [[[_ H] _] _]
    | destruct H as [[_ H] _] | destruct H as [_ H]];
    rewrite (proj2 (ltb_Z _ _) Hj) in H; exact H.
Qed.

Lemma count4_le : forall f d, ((φ (count4 f d)) <= 4)%Z.
Proof.
  intros f d. unfold count4, b2i.
  destruct (andb (0 <? d) (f 0)), (andb (1 <? d) (f 1)), (andb (2 <? d) (f 2)), (andb (3 <? d) (f 3));
    cbv; congruence.
Qed.

(* ------------------------------------------------------------------ *)
(* The search                                                          *)
(* ------------------------------------------------------------------ *)

Section Machine.
  (* n vertices 0..n-1; the neighbours of v are nb.[4v+j], j < dg.[v] *)
  Variable n : int.
  Variables nb dg : array int.

  Definition nbr (v j : int) : int := nb.[4 * v + j].

  (* x is listed among the neighbours of a *)
  Definition adjb (a x : int) : bool := exists4 (fun j => x =? nbr a j) dg.[a].

  Definition Eb (a x : int) : bool := (a <? n) && adjb a x.

  Definition alive (rm : array int) (x : int) : bool := rm.[x] =? 0.

  (* closed neighbourhood of u, read off the slots *)
  Definition inNb (u x : int) : bool := (x =? u) || adjb u x.

  Definition mark1 (w k : int) (rm : array int) : array int :=
    if rm.[w] =? 0 then rm.[w <- k] else rm.

  Definition unmark1 (w k : int) (rm : array int) : array int :=
    if rm.[w] =? k then rm.[w <- 0] else rm.

  (* remove the alive part of the closed neighbourhood of u, stamped k *)
  Definition mark (u k : int) (rm : array int) : array int :=
    let d := dg.[u] in
    let rm := mark1 u k rm in
    let rm := if 0 <? d then mark1 (nbr u 0) k rm else rm in
    let rm := if 1 <? d then mark1 (nbr u 1) k rm else rm in
    let rm := if 2 <? d then mark1 (nbr u 2) k rm else rm in
    if 3 <? d then mark1 (nbr u 3) k rm else rm.

  (* put back what [mark u k] removed *)
  Definition unmark (u k : int) (rm : array int) : array int :=
    let d := dg.[u] in
    let rm := unmark1 u k rm in
    let rm := if 0 <? d then unmark1 (nbr u 0) k rm else rm in
    let rm := if 1 <? d then unmark1 (nbr u 1) k rm else rm in
    let rm := if 2 <? d then unmark1 (nbr u 2) k rm else rm in
    if 3 <? d then unmark1 (nbr u 3) k rm else rm.

  (* remaining degree of v *)
  Definition deg (rm : array int) (v : int) : int :=
    count4 (fun j => alive rm (nbr v j)) dg.[v].

  (* the alive neighbours of v are pairwise adjacent *)
  Definition simp (rm : array int) (v : int) : bool :=
    let d := dg.[v] in
    forall4 (fun j1 => forall4 (fun j2 =>
      (j2 <=? j1) || negb (alive rm (nbr v j1)) || negb (alive rm (nbr v j2))
      || adjb (nbr v j1) (nbr v j2))%bool d) d.

  (* number of alive vertices in [i, n), plus acc *)
  Fixpoint cnt_loop (rm : array int) (i acc : int)
      (H : Acc (Zwf 0) (gap n i)) {struct H} : int :=
    match bdec (i <? n) with
    | left Hi =>
        cnt_loop rm (i + 1) (if alive rm i then acc + 1 else acc)
          (Acc_inv H (dec_step n i Hi))
    | right _ => acc
    end.

  (* the first simplicial alive vertex (v, true), otherwise an alive vertex
     of minimum remaining degree (v, false), otherwise (n, false) *)
  Fixpoint sel_loop (rm : array int) (i best bd : int)
      (H : Acc (Zwf 0) (gap n i)) {struct H} : int * bool :=
    match bdec (i <? n) with
    | left Hi =>
        if alive rm i then
          if simp rm i then (i, true)
          else
            let d := deg rm i in
            if d <? bd then sel_loop rm (i + 1) i d (Acc_inv H (dec_step n i Hi))
            else sel_loop rm (i + 1) best bd (Acc_inv H (dec_step n i Hi))
        else sel_loop rm (i + 1) best bd (Acc_inv H (dec_step n i Hi))
    | right _ => (best, false)
    end.

  (* take u: remove its closed neighbourhood, search with k-1, restore *)
  Definition child (rec : array int -> bool * array int) (k u : int)
      (rm : array int) : bool * array int :=
    let rm1 := mark u k rm in
    let (b, rm2) := rec rm1 in
    (b, unmark u k rm2).

  (* the child of slot j of v, unless an earlier child succeeded *)
  Definition try_slot (rec : array int -> bool * array int) (k v j : int)
      (r : bool * array int) : bool * array int :=
    let (b, rm) := r in
    if b then (true, rm)
    else if j <? dg.[v] then
      let u := nbr v j in
      if alive rm u then child rec k u rm else (false, rm)
    else (false, rm).

  (* one node of the search tree, k >= 1 *)
  Definition node (rec : array int -> bool * array int) (k : int)
      (rm : array int) : bool * array int :=
    if 5 * k <=? cnt_loop rm 0 0 (Zwf_well_founded 0 (gap n 0)) then (true, rm)
    else
      let (v, s) := sel_loop rm 0 n 5 (Zwf_well_founded 0 (gap n 0)) in
      if s then child rec k v rm
      else if v <? n then
        try_slot rec k v 3 (try_slot rec k v 2 (try_slot rec k v 1
          (try_slot rec k v 0 (child rec k v rm))))
      else (false, rm).

  Fixpoint search (k : int) (rm : array int) (H : Acc (Zwf 0) (φ k)) {struct H}
      : bool * array int :=
    match bdec (k =? 0) with
    | left _ => (true, rm)
    | right Hk =>
        node (fun rm' => search (k - 1) rm' (Acc_inv H (dec_k k Hk))) k rm
    end.

  Lemma search_eq : forall k rm H, search k rm H =
    match bdec (k =? 0) with
    | left _ => (true, rm)
    | right Hk =>
        node (fun rm' => search (k - 1) rm' (Acc_inv H (dec_k k Hk))) k rm
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Lemma cnt_loop_eq : forall rm i acc H, cnt_loop rm i acc H =
    match bdec (i <? n) with
    | left Hi =>
        cnt_loop rm (i + 1) (if alive rm i then acc + 1 else acc)
          (Acc_inv H (dec_step n i Hi))
    | right _ => acc
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Lemma sel_loop_eq : forall rm i best bd H, sel_loop rm i best bd H =
    match bdec (i <? n) with
    | left Hi =>
        if alive rm i then
          if simp rm i then (i, true)
          else
            let d := deg rm i in
            if d <? bd then sel_loop rm (i + 1) i d (Acc_inv H (dec_step n i Hi))
            else sel_loop rm (i + 1) best bd (Acc_inv H (dec_step n i Hi))
        else sel_loop rm (i + 1) best bd (Acc_inv H (dec_step n i Hi))
    | right _ => (best, false)
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  (* ---------------- marking, cell by cell ---------------- *)

  Lemma mark1_len : forall w k rm, PArray.length (mark1 w k rm) = PArray.length rm.
  Proof. intros. unfold mark1. destruct (_ =? 0); [apply alength_set | reflexivity]. Qed.

  Lemma unmark1_len : forall w k rm, PArray.length (unmark1 w k rm) = PArray.length rm.
  Proof. intros. unfold unmark1. destruct (_ =? k); [apply alength_set | reflexivity]. Qed.

  Lemma ifmark_len : forall (c : bool) w k rm,
    PArray.length (if c then mark1 w k rm else rm) = PArray.length rm.
  Proof. intros [|]; intros; [apply mark1_len | reflexivity]. Qed.

  Lemma ifunmark_len : forall (c : bool) w k rm,
    PArray.length (if c then unmark1 w k rm else rm) = PArray.length rm.
  Proof. intros [|]; intros; [apply unmark1_len | reflexivity]. Qed.

  Lemma mark_len : forall u k rm, PArray.length (mark u k rm) = PArray.length rm.
  Proof. intros. unfold mark. rewrite !ifmark_len, mark1_len. reflexivity. Qed.

  Lemma unmark_len : forall u k rm, PArray.length (unmark u k rm) = PArray.length rm.
  Proof. intros. unfold unmark. rewrite !ifunmark_len, unmark1_len. reflexivity. Qed.

  Lemma ifmark_cell : forall (c : bool) w k rm x,
    (x <? PArray.length rm) = true ->
    (if c then mark1 w k rm else rm).[x]
    = if (c && (x =? w)) && (rm.[x] =? 0) then k else rm.[x].
  Proof.
    intros c w k rm x Hx. destruct c; simpl; [|reflexivity].
    unfold mark1. destruct (x =? w) eqn:E.
    - apply eqb_spec in E. subst x. destruct (rm.[w] =? 0) eqn:E0.
      + apply aget_set_same. exact Hx.
      + reflexivity.
    - apply eqb_false_spec in E. simpl.
      destruct (rm.[w] =? 0); [apply aget_set_other; congruence | reflexivity].
  Qed.

  Lemma ifunmark_cell : forall (c : bool) w k rm x,
    (x <? PArray.length rm) = true ->
    (if c then unmark1 w k rm else rm).[x]
    = if (c && (x =? w)) && (rm.[x] =? k) then 0 else rm.[x].
  Proof.
    intros c w k rm x Hx. destruct c; simpl; [|reflexivity].
    unfold unmark1. destruct (x =? w) eqn:E.
    - apply eqb_spec in E. subst x. destruct (rm.[w] =? k) eqn:E0.
      + apply aget_set_same. exact Hx.
      + reflexivity.
    - apply eqb_false_spec in E. simpl.
      destruct (rm.[w] =? k); [apply aget_set_other; congruence | reflexivity].
  Qed.

  Lemma mark1_cell : forall w k rm x, (x <? PArray.length rm) = true ->
    (mark1 w k rm).[x] = if (x =? w) && (rm.[x] =? 0) then k else rm.[x].
  Proof. intros w k rm x Hx. exact (ifmark_cell true w k rm x Hx). Qed.

  Lemma unmark1_cell : forall w k rm x, (x <? PArray.length rm) = true ->
    (unmark1 w k rm).[x] = if (x =? w) && (rm.[x] =? k) then 0 else rm.[x].
  Proof. intros w k rm x Hx. exact (ifunmark_cell true w k rm x Hx). Qed.

  Lemma comb_mark : forall (b1 b2 : bool) (c k : int), (k =? 0) = false ->
    (if b2 && ((if b1 && (c =? 0) then k else c) =? 0) then k
     else (if b1 && (c =? 0) then k else c))
    = if (b1 || b2) && (c =? 0) then k else c.
  Proof.
    intros b1 b2 c k Hk. destruct b1, b2, (c =? 0) eqn:E; simpl;
      rewrite ?Hk, ?E; reflexivity.
  Qed.

  Lemma comb_unmark : forall (b1 b2 : bool) (c k : int), (k =? 0) = false ->
    (if b2 && ((if b1 && (c =? k) then 0 else c) =? k) then 0
     else (if b1 && (c =? k) then 0 else c))
    = if (b1 || b2) && (c =? k) then 0 else c.
  Proof.
    intros b1 b2 c k Hk0.
    assert (Hk : (0 =? k) = false) by (rewrite eqb_false_spec in *; congruence).
    destruct b1, b2, (c =? k) eqn:E; simpl; rewrite ?Hk, ?E; reflexivity.
  Qed.

  Lemma mark_cell : forall u k rm x, (k =? 0) = false ->
    (x <? PArray.length rm) = true ->
    (mark u k rm).[x] = if inNb u x && (rm.[x] =? 0) then k else rm.[x].
  Proof.
    intros u k rm x Hk Hx. unfold mark.
    rewrite !ifmark_cell by (rewrite ?ifmark_len, ?mark1_len; exact Hx).
    rewrite mark1_cell by exact Hx.
    rewrite !comb_mark by exact Hk.
    unfold inNb, adjb, exists4. rewrite !Bool.orb_assoc. reflexivity.
  Qed.

  Lemma unmark_cell : forall u k rm x, (k =? 0) = false ->
    (x <? PArray.length rm) = true ->
    (unmark u k rm).[x] = if inNb u x && (rm.[x] =? k) then 0 else rm.[x].
  Proof.
    intros u k rm x Hk Hx. unfold unmark.
    rewrite !ifunmark_cell by (rewrite ?ifunmark_len, ?unmark1_len; exact Hx).
    rewrite unmark1_cell by exact Hx.
    rewrite !comb_unmark by exact Hk.
    unfold inNb, adjb, exists4. rewrite !Bool.orb_assoc. reflexivity.
  Qed.

  (* ---------------- the graph the arrays describe ---------------- *)

  Hypothesis Hn : ((φ n) <= 100000)%Z.
  Hypothesis Hdeg : forall v, ((φ v) < (φ n))%Z -> ((φ (dg.[v])) <= 4)%Z.
  Hypothesis Hrange : forall v j, ((φ v) < (φ n))%Z -> ((φ j) < (φ (dg.[v])))%Z ->
    ((φ (nbr v j)) < (φ n))%Z.
  Hypothesis Hsym : forall a b, Eb a b = true -> Eb b a = true.
  Hypothesis Hirr : forall a, Eb a a = false.

  Lemma adjb_spec : forall a x, ((φ a) < (φ n))%Z ->
    (adjb a x = true <-> exists j, ((φ j) < (φ (dg.[a])))%Z /\ x = nbr a j).
  Proof.
    intros a x Ha. unfold adjb. rewrite exists4_spec by (apply Hdeg, Ha).
    split; intros (j & Hj & E); exists j; split; auto; apply eqb_spec; auto.
  Qed.

  Lemma Eb_spec : forall a x, Eb a x = true <->
    ((φ a) < (φ n))%Z /\ exists j, ((φ j) < (φ (dg.[a])))%Z /\ x = nbr a j.
  Proof.
    intros a x. unfold Eb. rewrite Bool.andb_true_iff, ltb_Z.
    split; intros [Ha H]; split; auto; apply adjb_spec; auto.
  Qed.

  Lemma Edeg : forall x, exists M, (List.length M <= 4)%nat /\
    forall y, Eb x y = true -> In y M.
  Proof.
    intros x. exists [nbr x 0; nbr x 1; nbr x 2; nbr x 3]. split; [simpl; lia|].
    intros y Hy. apply Eb_spec in Hy. destruct Hy as (Hx & j & Hj & ->).
    pose proof (Hdeg x Hx).
    destruct (small4 j ltac:(lia)) as [-> | [-> | [-> | ->]]]; simpl; tauto.
  Qed.

  Lemma closed_inNb : forall u x, ((φ u) < (φ n))%Z -> closedNb Eb u x = inNb u x.
  Proof.
    intros u x Hu. unfold closedNb, inNb, Eb.
    rewrite (proj2 (ltb_Z u n) Hu). reflexivity.
  Qed.

  Definition Pr (rm : array int) (x : int) : Prop := ((φ x) < (φ n))%Z /\ rm.[x] = 0.

  Definition ceq (r1 r2 : array int) : Prop :=
    PArray.length r1 = PArray.length r2 /\
    forall x, ((φ x) < (φ n))%Z -> r1.[x] = r2.[x].

  Definition Inv (k : int) (rm : array int) : Prop :=
    PArray.length rm = n /\
    forall x, ((φ x) < (φ n))%Z -> rm.[x] = 0 \/ ((φ k) < (φ (rm.[x])))%Z.

  Lemma ceq_refl : forall r, ceq r r.
  Proof. intros r. split; auto. Qed.

  Lemma ceq_sym : forall r1 r2, ceq r1 r2 -> ceq r2 r1.
  Proof. intros r1 r2 [H1 H2]. split; auto. intros; symmetry; auto. Qed.

  Lemma ceq_trans : forall r1 r2 r3, ceq r1 r2 -> ceq r2 r3 -> ceq r1 r3.
  Proof. intros r1 r2 r3 [H1 H2] [H3 H4]. split; [congruence|]. intros; rewrite H2; auto. Qed.

  Lemma Inv_ceq : forall k r1 r2, ceq r1 r2 -> Inv k r2 -> Inv k r1.
  Proof.
    intros k r1 r2 [H1 H2] [H3 H4]. split; [congruence|].
    intros x Hx. rewrite H2 by exact Hx. auto.
  Qed.

  Lemma Pr_ceq : forall r1 r2, ceq r1 r2 -> forall x, Pr r1 x <-> Pr r2 x.
  Proof.
    intros r1 r2 [_ H] x. unfold Pr. split; intros [Hx E]; split; auto;
      [rewrite <- H | rewrite H]; auto.
  Qed.

  Lemma inbound : forall (rm : array int) x, PArray.length rm = n -> ((φ x) < (φ n))%Z ->
    (x <? PArray.length rm) = true.
  Proof. intros rm x H Hx. rewrite H. apply ltb_Z, Hx. Qed.

  Lemma k_nz : forall k : int, (k =? 0) = false -> (1 <= (φ k))%Z.
  Proof.
    intros k H. rewrite eqb_false_spec in H. pose proof (to_Z_bounded k).
    assert ((φ k) <> 0%Z) by (intro E; apply H, to_Z_inj; exact E). lia.
  Qed.

  Lemma km1 : forall k : int, (k =? 0) = false -> (φ (k - 1)) = ((φ k) - 1)%Z.
  Proof. intros k H. pose proof (k_nz k H). sia. Qed.

  Lemma Pr_mark : forall u k rm, (k =? 0) = false -> PArray.length rm = n ->
    ((φ u) < (φ n))%Z ->
    forall x, Pr (mark u k rm) x <-> minus Eb (Pr rm) u x.
  Proof.
    intros u k rm Hk Hl Hu x. unfold Pr, minus. rewrite closed_inNb by exact Hu.
    split.
    - intros [Hx E]. rewrite mark_cell in E by (auto; apply inbound; auto).
      destruct (inNb u x && (rm.[x] =? 0)) eqn:B.
      + subst k. discriminate.
      + destruct (inNb u x); simpl in B; auto.
        rewrite E, eqb_refl in B. discriminate.
    - intros [[Hx E] B]. split; auto.
      rewrite mark_cell by (auto; apply inbound; auto). rewrite B. exact E.
  Qed.

  Lemma Inv_mark : forall u k rm, (k =? 0) = false -> Inv k rm ->
    Inv (k - 1) (mark u k rm).
  Proof.
    intros u k rm Hk [Hl Hc]. split; [rewrite mark_len; exact Hl|].
    intros x Hx. rewrite mark_cell by (auto; apply inbound; auto).
    rewrite km1 by exact Hk.
    destruct (inNb u x && (rm.[x] =? 0)); [right; lia|].
    destruct (Hc x Hx); [left; auto | right; lia].
  Qed.

  Lemma restore : forall u k rm rm2, (k =? 0) = false -> Inv k rm ->
    ceq rm2 (mark u k rm) -> ceq (unmark u k rm2) rm.
  Proof.
    intros u k rm rm2 Hk [Hl Hc] [H1 H2]. rewrite mark_len in H1.
    split; [rewrite unmark_len; exact H1|].
    intros x Hx. rewrite unmark_cell by (auto; apply inbound; congruence).
    rewrite H2 by exact Hx. rewrite mark_cell by (auto; apply inbound; auto).
    destruct (inNb u x) eqn:B; simpl; [|reflexivity].
    destruct (rm.[x] =? 0) eqn:E0.
    - rewrite eqb_refl. symmetry. apply eqb_true_iff', E0.
    - destruct (rm.[x] =? k) eqn:Ek; [|reflexivity].
      apply eqb_true_iff' in Ek. destruct (Hc x Hx) as [Z | Z].
      + rewrite Z in E0. discriminate.
      + rewrite Ek in Z. lia.
  Qed.

  Definition RecSpec (k : int) (rec : array int -> bool * array int) : Prop :=
    forall rm, Inv k rm ->
      ceq (snd (rec rm)) rm /\
      (fst (rec rm) = true <-> has Eb (Pr rm) (Z.to_nat (φ k))).

  Lemma child_spec : forall rec k u rm, (k =? 0) = false ->
    RecSpec (k - 1) rec -> Inv k rm -> ((φ u) < (φ n))%Z ->
    ceq (snd (child rec k u rm)) rm /\
    (fst (child rec k u rm) = true <->
       has Eb (minus Eb (Pr rm) u) (Z.to_nat (φ (k - 1)))).
  Proof.
    intros rec k u rm Hk Hrec HI Hu. unfold child.
    destruct (Hrec (mark u k rm) (Inv_mark u k rm Hk HI)) as [Hc Hb].
    destruct (rec (mark u k rm)) as [b rm2] eqn:E. simpl in *.
    split; [apply restore; auto|].
    rewrite Hb. apply has_iff. apply Pr_mark; auto. apply HI.
  Qed.

  (* ---------------- counting the alive vertices ---------------- *)

  Fixpoint alive_upto (rm : array int) (m : nat) : list int :=
    match m with
    | O => []
    | S m' => alive_upto rm m' ++
        (if rm.[of_Z (Z.of_nat m')] =? 0 then [of_Z (Z.of_nat m')] else [])
    end.

  Lemma of_Z_small : forall z, (0 <= z <= (φ n))%Z -> (φ (of_Z z)) = z.
  Proof.
    intros z Hz. rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia.
  Qed.

  Lemma alive_upto_in : forall rm m, (Z.of_nat m <= (φ n))%Z ->
    forall x, In x (alive_upto rm m) <-> ((φ x) < Z.of_nat m)%Z /\ rm.[x] = 0.
  Proof.
    intros rm m. induction m as [| m IH]; intros Hm x; simpl.
    - pose proof (to_Z_bounded x). split; [tauto | lia].
    - rewrite in_app_iff, IH by lia.
      assert (Hm' : (φ (of_Z (Z.of_nat m))) = Z.of_nat m) by (apply of_Z_small; lia).
      split.
      + intros [[H1 H2] | H]; [split; [lia | exact H2]|].
        destruct (rm.[of_Z (Z.of_nat m)] =? 0) eqn:E; [|destruct H].
        destruct H as [<- | []]. split; [lia|]. apply eqb_true_iff', E.
      + intros [H1 H2].
        destruct (Z.eq_dec (φ x) (Z.of_nat m)) as [E | E]; [right | left; split; [lia | exact H2]].
        assert (x = of_Z (Z.of_nat m)) as -> by (apply to_Z_inj; lia).
        rewrite H2, eqb_refl. left. reflexivity.
  Qed.

  Lemma alive_upto_nodup : forall rm m, (Z.of_nat m <= (φ n))%Z -> NoDup (alive_upto rm m).
  Proof.
    intros rm m. induction m as [| m IH]; intros Hm; simpl; [constructor|].
    apply NoDup_app; [apply IH; lia | |].
    - destruct (_ =? 0); repeat constructor. simpl; tauto.
    - intros a Ha Hb. apply alive_upto_in in Ha; [|lia].
      destruct (_ =? 0); [|destruct Hb]. destruct Hb as [<- | []].
      rewrite of_Z_small in Ha by lia. lia.
  Qed.

  Lemma alive_upto_len : forall rm m, (List.length (alive_upto rm m) <= m)%nat.
  Proof.
    intros rm m. induction m as [| m IH]; simpl; [lia|].
    rewrite length_app. destruct (_ =? 0); simpl; lia.
  Qed.

  Lemma cnt_loop_spec : forall rm z i acc H, gap n i = z -> ((φ i) <= (φ n))%Z ->
    (φ acc) = Z.of_nat (List.length (alive_upto rm (Z.to_nat (φ i)))) ->
    (φ (cnt_loop rm i acc H)) = Z.of_nat (List.length (alive_upto rm (Z.to_nat (φ n)))).
  Proof.
    intros rm z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros i acc H Hz Hi Hacc. rewrite cnt_loop_eq.
    destruct (bdec (i <? n)) as [Hlt | Hlt].
    - pose proof Hlt as Hlt'. rewrite ltb_Z in Hlt'.
      assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
      eapply IH; [rewrite <- Hz; apply dec_step, Hlt | reflexivity | lia |].
      rewrite Hi1, Z2Nat.inj_add, Nat.add_1_r by (pose proof (to_Z_bounded i); lia).
      simpl. rewrite length_app.
      rewrite Z2Nat.id by (pose proof (to_Z_bounded i); lia). rewrite of_to_Z.
      pose proof (alive_upto_len rm (Z.to_nat (φ i))).
      unfold alive. destruct (rm.[i] =? 0); simpl.
      + rewrite add_spec, Hacc. rewrite Z.mod_small; [lia|].
        rewrite wB_val. pose proof (to_Z_bounded i). lia.
      + rewrite Hacc. lia.
    - rewrite <- Bool.not_true_iff_false, ltb_Z in Hlt.
      replace (φ n) with (φ i) by lia. exact Hacc.
  Qed.

  (* ---------------- choosing the vertex ---------------- *)

  Lemma simp_pair : forall rm v j1 j2, simp rm v = true -> ((φ v) < (φ n))%Z ->
    ((φ j1) < (φ j2))%Z -> ((φ j2) < (φ (dg.[v])))%Z ->
    alive rm (nbr v j1) = true -> alive rm (nbr v j2) = true ->
    adjb (nbr v j1) (nbr v j2) = true.
  Proof.
    intros rm v j1 j2 Hs Hv H12 H2 A1 A2. pose proof (Hdeg v Hv) as Hd.
    unfold simp in Hs.
    pose proof (forall4_true _ _ Hs j1 ltac:(lia) ltac:(lia)) as Hs1. cbv beta in Hs1.
    pose proof (forall4_true _ _ Hs1 j2 ltac:(lia) ltac:(lia)) as Hs2. cbv beta in Hs2.
    rewrite A1, A2 in Hs2.
    assert (E : (j2 <=? j1) = false) by (apply Bool.not_true_iff_false; rewrite leb_spec; lia).
    rewrite E in Hs2. exact Hs2.
  Qed.

  Lemma simp_spec : forall rm v, simp rm v = true -> ((φ v) < (φ n))%Z ->
    simplicial Eb (Pr rm) v.
  Proof.
    intros rm v Hs Hv a b [Ha Pa] [Hb Pb] Ea Eb' Hab.
    apply Eb_spec in Ea. destruct Ea as (_ & j1 & Hj1 & ->).
    apply Eb_spec in Eb'. destruct Eb' as (_ & j2 & Hj2 & ->).
    assert (A1 : alive rm (nbr v j1) = true) by (unfold alive; rewrite Pa; apply eqb_refl).
    assert (A2 : alive rm (nbr v j2) = true) by (unfold alive; rewrite Pb; apply eqb_refl).
    destruct (Z.lt_total (φ j1) (φ j2)) as [L | [L | L]].
    - unfold Eb. rewrite (proj2 (ltb_Z _ _) Ha). simpl. apply (simp_pair rm v); auto.
    - assert (j1 = j2) by (apply to_Z_inj; exact L). subst. congruence.
    - apply Hsym. unfold Eb. rewrite (proj2 (ltb_Z _ _) Hb). simpl.
      apply (simp_pair rm v); auto.
  Qed.

  Definition SelInv (rm : array int) (i best bd : int) : Prop :=
    (best = n /\ (φ bd) = 5%Z /\ forall x, ((φ x) < (φ i))%Z -> rm.[x] <> 0) \/
    (Pr rm best /\ ((φ bd) <= 4)%Z).

  Lemma sel_loop_spec : forall rm z i best bd H, gap n i = z -> ((φ i) <= (φ n))%Z ->
    SelInv rm i best bd ->
    let r := sel_loop rm i best bd H in
    (snd r = true -> Pr rm (fst r) /\ simplicial Eb (Pr rm) (fst r)) /\
    (snd r = false -> (fst r = n /\ forall x, ~ Pr rm x) \/ Pr rm (fst r)).
  Proof.
    intros rm z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros i best bd H Hz Hi HS. rewrite sel_loop_eq.
    destruct (bdec (i <? n)) as [Hlt | Hlt].
    - pose proof Hlt as Hlt'. rewrite ltb_Z in Hlt'.
      assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
      assert (Hdec : Zwf 0 (gap n (i + 1)) z) by (rewrite <- Hz; apply dec_step, Hlt).
      destruct (alive rm i) eqn:Ai.
      + assert (Pi : Pr rm i) by (split; [exact Hlt' | apply eqb_true_iff', Ai]).
        destruct (simp rm i) eqn:Si.
        * simpl. split; [|discriminate]. intros _. split; [exact Pi|].
          apply simp_spec; auto.
        * cbv zeta. assert (Hd : ((φ (deg rm i)) <= 4)%Z) by apply count4_le.
          destruct (deg rm i <? bd) eqn:Lt.
          -- eapply IH; [exact Hdec | reflexivity | lia |]. right. split; auto.
          -- eapply IH; [exact Hdec | reflexivity | lia |].
             destruct HS as [(_ & Hb & _) | HS]; [|right; exact HS].
             exfalso. apply Bool.not_true_iff_false in Lt. apply Lt, ltb_Z. lia.
      + eapply IH; [exact Hdec | reflexivity | lia |].
        destruct HS as [(Hb & Hd & Hx) | HS]; [left | right; exact HS].
        split; [exact Hb|]. split; [exact Hd|]. intros x Hx'.
        destruct (Z.eq_dec (φ x) (φ i)) as [E | E].
        * assert (x = i) as -> by (apply to_Z_inj; exact E).
          intro Z0. unfold alive in Ai. rewrite Z0, eqb_refl in Ai. discriminate.
        * apply Hx. lia.
    - rewrite <- Bool.not_true_iff_false, ltb_Z in Hlt. simpl.
      split; [discriminate|]. intros _.
      destruct HS as [(Hb & _ & Hx) | HS]; [left | right; exact (proj1 HS)].
      split; [exact Hb|]. intros x [Hx1 Hx2]. apply (Hx x); [lia | exact Hx2].
  Qed.

  (* ---------------- one node ---------------- *)

  Lemma try_slot_spec : forall rec k v j rm0 r, (k =? 0) = false ->
    RecSpec (k - 1) rec -> Inv k rm0 -> ((φ v) < (φ n))%Z -> ceq (snd r) rm0 ->
    ceq (snd (try_slot rec k v j r)) rm0 /\
    (fst (try_slot rec k v j r) = true <->
       fst r = true \/
       (((φ j) < (φ (dg.[v])))%Z /\ Pr rm0 (nbr v j) /\
        has Eb (minus Eb (Pr rm0) (nbr v j)) (Z.to_nat (φ (k - 1))))).
  Proof.
    intros rec k v j rm0 [b rm] Hk Hrec HI Hv Hc. simpl in Hc. unfold try_slot.
    destruct b; simpl; [split; [exact Hc | tauto]|].
    destruct (j <? dg.[v]) eqn:Ej.
    2:{ simpl. split; [exact Hc|]. rewrite <- Bool.not_true_iff_false, ltb_Z in Ej.
        split; [discriminate|]. intros [F | (F & _)]; [discriminate | lia]. }
    rewrite ltb_Z in Ej.
    assert (Hu : ((φ (nbr v j)) < (φ n))%Z) by (apply Hrange; auto).
    assert (HPu : Pr rm (nbr v j) <-> Pr rm0 (nbr v j)) by (apply Pr_ceq, Hc).
    destruct (alive rm (nbr v j)) eqn:A.
    - assert (HI' : Inv k rm) by (eapply Inv_ceq; eauto).
      destruct (child_spec rec k (nbr v j) rm Hk Hrec HI' Hu) as [Hc' Hb'].
      split; [eapply ceq_trans; eauto|].
      rewrite Hb'. split.
      + intros Hh. right. split; [exact Ej|]. split.
        * apply HPu. split; [exact Hu | apply eqb_true_iff', A].
        * revert Hh. apply has_ext. intros x. unfold minus.
          rewrite (Pr_ceq _ _ Hc x). tauto.
      + intros [F | (_ & _ & Hh)]; [discriminate|].
        revert Hh. apply has_ext. intros x. unfold minus.
        rewrite (Pr_ceq _ _ Hc x). tauto.
    - simpl. split; [exact Hc|]. split; [discriminate|].
      intros [F | (_ & Pu & _)]; [discriminate|].
      apply HPu in Pu. destruct Pu as [_ Pu].
      unfold alive in A. rewrite Pu, eqb_refl in A. discriminate.
  Qed.

  Lemma node_spec : forall rec k rm, (k =? 0) = false -> ((φ k) <= 15)%Z ->
    RecSpec (k - 1) rec -> Inv k rm ->
    ceq (snd (node rec k rm)) rm /\
    (fst (node rec k rm) = true <-> has Eb (Pr rm) (Z.to_nat (φ k))).
  Proof.
    intros rec k rm Hk Hk15 Hrec HI.
    pose proof (k_nz k Hk) as Hk1. pose proof (km1 k Hk) as Hkm.
    assert (HkS : Z.to_nat (φ k) = S (Z.to_nat (φ (k - 1)))) by lia.
    unfold node.
    set (L := alive_upto rm (Z.to_nat (φ n))).
    assert (HL : forall x, Pr rm x <-> In x L).
    { intros x. unfold L. rewrite alive_upto_in by lia. unfold Pr.
      rewrite Z2Nat.id by (pose proof (to_Z_bounded n); lia). tauto. }
    pose proof (cnt_loop_spec rm _ 0 0 (Zwf_well_founded 0 (gap n 0)) eq_refl
                  ltac:(pose proof (to_Z_bounded n); change (φ 0) with 0%Z; lia)
                  ltac:(change (φ 0) with 0%Z; reflexivity)) as Hcnt.
    fold L in Hcnt.
    destruct (5 * k <=? cnt_loop rm 0 0 (Zwf_well_founded 0 (gap n 0))) eqn:Ek.
    - simpl. split; [apply ceq_refl|]. split; [intros _ | reflexivity].
      apply (has_kernel Eb Hsym Hirr Edeg _ L); [apply alive_upto_nodup; lia | exact HL |].
      rewrite leb_spec, Hcnt in Ek.
      assert ((φ (5 * k)) = (5 * (φ k))%Z) by sia. lia.
    - pose proof (sel_loop_spec rm _ 0 n 5 (Zwf_well_founded 0 (gap n 0)) eq_refl
                   ltac:(pose proof (to_Z_bounded n); change (φ 0) with 0%Z; lia)
                   ltac:(left; split; [reflexivity|]; split; [reflexivity|];
                         intros x Hx; change (φ 0) with 0%Z in Hx;
                         pose proof (to_Z_bounded x); lia)) as Hsel.
      destruct (sel_loop rm 0 n 5 (Zwf_well_founded 0 (gap n 0))) as [v s].
      simpl in Hsel. destruct Hsel as [Hs1 Hs2].
      destruct s.
      + destruct (Hs1 eq_refl) as [Pv Sv].
        destruct (child_spec rec k v rm Hk Hrec HI (proj1 Pv)) as [Hc Hb].
        split; [exact Hc|]. rewrite Hb, HkS. split.
        * apply (has_take Eb Hsym Hirr). exact Pv.
        * apply (has_simplicial Eb Hsym); assumption.
      + destruct (v <? n) eqn:Ev.
        2:{ simpl. split; [apply ceq_refl|]. split; [discriminate|].
            destruct (Hs2 eq_refl) as [[_ Hno] | Pv].
            - rewrite HkS. intros Hh. destruct (has_nonempty _ _ _ Hh) as [x Px].
              destruct (Hno x Px).
            - destruct Pv as [Pv _]. apply ltb_Z in Pv. congruence. }
        assert (Pv : Pr rm v).
        { destruct (Hs2 eq_refl) as [[-> _] | Pv]; [|exact Pv].
          rewrite ltb_Z in Ev. lia. }
        destruct (child_spec rec k v rm Hk Hrec HI (proj1 Pv)) as [Hc0 Hb0].
        destruct (try_slot_spec rec k v 0 rm _ Hk Hrec HI (proj1 Pv) Hc0) as [Hc1 Hb1].
        destruct (try_slot_spec rec k v 1 rm _ Hk Hrec HI (proj1 Pv) Hc1) as [Hc2 Hb2].
        destruct (try_slot_spec rec k v 2 rm _ Hk Hrec HI (proj1 Pv) Hc2) as [Hc3 Hb3].
        destruct (try_slot_spec rec k v 3 rm _ Hk Hrec HI (proj1 Pv) Hc3) as [Hc4 Hb4].
        split; [exact Hc4|]. rewrite Hb4, Hb3, Hb2, Hb1, Hb0, HkS.
        split.
        * intros [[[[H | H] | H] | H] | H];
            [apply (has_take Eb Hsym Hirr _ v); assumption
            | destruct H as (_ & Pu & H); apply (has_take Eb Hsym Hirr _ _ _ Pu H) ..].
        * intros Hh. destruct (has_branch Eb _ v _ Pv Hh) as (u & Hcu & Pu & Hu).
          rewrite closed_inNb in Hcu by exact (proj1 Pv). unfold inNb in Hcu.
          apply Bool.orb_true_iff in Hcu. destruct Hcu as [Hcu | Hcu].
          { apply eqb_true_iff' in Hcu. subst u. left; left; left; left. exact Hu. }
          apply adjb_spec in Hcu; [|exact (proj1 Pv)].
          destruct Hcu as (j & Hj & ->).
          pose proof (Hdeg v (proj1 Pv)).
          destruct (small4 j ltac:(lia)) as [-> | [-> | [-> | ->]]];
            [left; left; left; right | left; left; right | left; right | right];
            auto.
  Qed.

  Lemma search_spec : forall z k rm H, (φ k) = z -> ((φ k) <= 15)%Z -> Inv k rm ->
    ceq (snd (search k rm H)) rm /\
    (fst (search k rm H) = true <-> has Eb (Pr rm) (Z.to_nat (φ k))).
  Proof.
    intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros k rm H Hz Hk15 HI. rewrite search_eq.
    destruct (bdec (k =? 0)) as [Hk | Hk].
    - simpl. split; [apply ceq_refl|]. apply eqb_true_iff' in Hk. subst k.
      split; [intros _; apply has_zero | reflexivity].
    - apply node_spec; auto.
      intros rm' HI'. simpl. apply (IH (φ (k - 1))); auto.
      + rewrite <- Hz. apply dec_k, Hk.
      + pose proof (km1 k Hk). lia.
  Qed.

End Machine.

(* ------------------------------------------------------------------ *)
(* From the input rows to the flat tables                              *)
(* ------------------------------------------------------------------ *)

(* dg.[v] := the number of neighbours on line v+1 *)
Fixpoint fill_dg (y : array (array int)) (n i : int) (dg : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi => fill_dg y n (i + 1) dg.[i <- PArray.length y.[i]]
                 (Acc_inv H (dec_step n i Hi))
  | right _ => dg
  end.

Definition put_slot (row : array int) (b j : int) (nb : array int) : array int :=
  if j <? PArray.length row then nb.[b + j <- row.[j] - 1] else nb.

(* nb.[4v+j] := the j-th neighbour of line v+1, minus one (0-based) *)
Fixpoint fill_nb (y : array (array int)) (n i : int) (nb : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi =>
      let row := y.[i] in
      let b := 4 * i in
      fill_nb y n (i + 1)
        (put_slot row b 3 (put_slot row b 2 (put_slot row b 1 (put_slot row b 0 nb))))
        (Acc_inv H (dec_step n i Hi))
  | right _ => nb
  end.

Definition basincity_impl (k : uint) (y : array (array uint)) : bool :=
  let n := PArray.length y in
  let dg := fill_dg y n 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)) in
  let nb := fill_nb y n 0 (PArray.make (4 * n) 0) (Zwf_well_founded 0 (gap n 0)) in
  fst (search n nb dg k (PArray.make n 0) (Zwf_well_founded 0 (φ k))).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition basincity : uint -> array (array uint) -> bool := basincity_impl.
