From Shortestpath3.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63 ListDec.
From Stdlib Require Import Permutation.
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

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_lt : forall a b : int, (a <? b) = true -> Zwf 0 (φ a) (φ b).
Proof.
  intros a b H. rewrite ltb_spec in H. pose proof (to_Z_bounded a).
  unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* The "unreached" state of the distance table: the largest signed word. *)
Definition INF : int := 4611686018427387903.

(* Relaxation of edge j on the table d; ch records a change. *)
Definition relax (us vs ws : array int) (j : int) (d : array int) (ch : bool)
  : array int * bool :=
  let du := d.[us.[j]] in
  if du =? INF then (d, ch) else
  let v := vs.[j] in
  let nd := du + ws.[j] in
  if ltsb nd d.[v] then (d.[v <- nd], true) else (d, ch).

(* One round: edges j, j+1, ..., m-1 relaxed in order. *)
Fixpoint edges_loop (us vs ws : array int) (m j : int) (d : array int) (ch : bool)
    (H : Acc (Zwf 0) (gap m j)) {struct H} : array int * bool :=
  match bdec (j <? m) with
  | left Hj =>
      let (d', ch') := relax us vs ws j d ch in
      edges_loop us vs ws m (j + 1) d' ch' (Acc_inv H (dec_step m j Hj))
  | right _ => (d, ch)
  end.

(* Rounds k, k+1, ..., R-1, stopping after a round that changed nothing. *)
Fixpoint rounds_loop (us vs ws : array int) (m R k : int) (d : array int)
    (H : Acc (Zwf 0) (gap R k)) {struct H} : array int :=
  match bdec (k <? R) with
  | left Hk =>
      let (d', ch) := edges_loop us vs ws m 0 d false
                        (Zwf_well_founded 0 (gap m 0)) in
      if ch then rounds_loop us vs ws m R (k + 1) d' (Acc_inv H (dec_step R k Hk))
      else d'
  | right _ => d
  end.

(* The check round: the target of every edge that still relaxes is marked
   and enqueued (once). *)
Fixpoint seed_loop (us vs ws d : array int) (m j : int) (mk q : array int) (tl : int)
    (H : Acc (Zwf 0) (gap m j)) {struct H} : array int * array int * int :=
  match bdec (j <? m) with
  | left Hj =>
      let du := d.[us.[j]] in
      let v := vs.[j] in
      if (negb (du =? INF) && ltsb (du + ws.[j]) d.[v] && (mk.[v] =? 0))%bool then
        seed_loop us vs ws d m (j + 1) mk.[v <- 1] q.[tl <- v] (tl + 1)
          (Acc_inv H (dec_step m j Hj))
      else seed_loop us vs ws d m (j + 1) mk q tl (Acc_inv H (dec_step m j Hj))
  | right _ => (mk, q, tl)
  end.

(* The adjacency, a forward star: hd.[u] is 1 + the last edge out of u (0:
   none), nx.[j] is 1 + the previous edge with the same source as j. *)
Fixpoint build_loop (us : array int) (m j : int) (hd nx : array int)
    (H : Acc (Zwf 0) (gap m j)) {struct H} : array int * array int :=
  match bdec (j <? m) with
  | left Hj =>
      let u := us.[j] in
      let h := hd.[u] in
      build_loop us m (j + 1) hd.[u <- j + 1] nx.[j <- h]
        (Acc_inv H (dec_step m j Hj))
  | right _ => (hd, nx)
  end.

(* The out-edges of one node, from the chain cell e on: their unmarked
   targets are marked and enqueued. *)
Fixpoint adj_loop (vs nx : array int) (e : int) (mk q : array int) (tl : int)
    (H : Acc (Zwf 0) (φ e)) {struct H} : array int * array int * int :=
  match bdec (0 <? e) with
  | left _ =>
      let j := e - 1 in
      let v := vs.[j] in
      let e' := nx.[j] in
      match bdec (e' <? e) with
      | left Hd =>
          if mk.[v] =? 0 then
            adj_loop vs nx e' mk.[v <- 1] q.[tl <- v] (tl + 1)
              (Acc_inv H (dec_lt e' e Hd))
          else adj_loop vs nx e' mk q tl (Acc_inv H (dec_lt e' e Hd))
      | right _ => (mk, q, tl)
      end
  | right _ => (mk, q, tl)
  end.

(* The breadth-first search: queue cells h, h+1, ... are processed. *)
Fixpoint bfs_loop (vs hd nx : array int) (n h : int) (mk q : array int) (tl : int)
    (H : Acc (Zwf 0) (gap n h)) {struct H} : array int :=
  match bdec (h <? tl) with
  | left _ =>
      match bdec (h <? n) with
      | left Hh =>
          let x := q.[h] in
          let '(mk', q', tl') :=
            adj_loop vs nx hd.[x] mk q tl (Zwf_well_founded 0 (φ (hd.[x]))) in
          bfs_loop vs hd nx n (h + 1) mk' q' tl' (Acc_inv H (dec_step n h Hh))
      | right _ => mk
      end
  | right _ => mk
  end.

(* The answer of one query node t. *)
Definition answer_of (d mk : array int) (t : int) : answer int :=
  let x := d.[t] in
  if x =? INF then Impossible
  else if mk.[t] =? 0 then Dist x else MinusInfinity.

Fixpoint ans_loop (d mk qs : array int) (Q i : int) (out : array (answer int))
    (H : Acc (Zwf 0) (gap Q i)) {struct H} : array (answer int) :=
  match bdec (i <? Q) with
  | left Hi =>
      let a := answer_of d mk qs.[i] in
      ans_loop d mk qs Q (i + 1) out.[i <- a] (Acc_inv H (dec_step Q i Hi))
  | right _ => out
  end.

Definition shortestpath3_impl (n s : int) (us vs ws qs : array int)
  : array (answer int) :=
  let m := PArray.length us in
  let d0 := (PArray.make n INF).[s <- 0] in
  let d := rounds_loop us vs ws m (n - 1) 0 d0 (Zwf_well_founded 0 (gap (n - 1) 0)) in
  let '(mk, q, tl) := seed_loop us vs ws d m 0 (PArray.make n 0) (PArray.make n 0) 0
                        (Zwf_well_founded 0 (gap m 0)) in
  let '(hd, nx) := build_loop us m 0 (PArray.make n 0) (PArray.make m 0)
                     (Zwf_well_founded 0 (gap m 0)) in
  let mk' := bfs_loop vs hd nx n 0 mk q tl (Zwf_well_founded 0 (gap n 0)) in
  let Q := PArray.length qs in
  ans_loop d mk' qs Q 0 (PArray.make Q Impossible) (Zwf_well_founded 0 (gap Q 0)).

(* Unfolding equations *)
Lemma edges_loop_eq : forall us vs ws m j d ch H,
  edges_loop us vs ws m j d ch H =
  match bdec (j <? m) with
  | left Hj =>
      let (d', ch') := relax us vs ws j d ch in
      edges_loop us vs ws m (j + 1) d' ch' (Acc_inv H (dec_step m j Hj))
  | right _ => (d, ch)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma rounds_loop_eq : forall us vs ws m R k d H,
  rounds_loop us vs ws m R k d H =
  match bdec (k <? R) with
  | left Hk =>
      let (d', ch) := edges_loop us vs ws m 0 d false
                        (Zwf_well_founded 0 (gap m 0)) in
      if ch then rounds_loop us vs ws m R (k + 1) d' (Acc_inv H (dec_step R k Hk))
      else d'
  | right _ => d
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma seed_loop_eq : forall us vs ws d m j mk q tl H,
  seed_loop us vs ws d m j mk q tl H =
  match bdec (j <? m) with
  | left Hj =>
      let du := d.[us.[j]] in
      let v := vs.[j] in
      if (negb (du =? INF) && ltsb (du + ws.[j]) d.[v] && (mk.[v] =? 0))%bool then
        seed_loop us vs ws d m (j + 1) mk.[v <- 1] q.[tl <- v] (tl + 1)
          (Acc_inv H (dec_step m j Hj))
      else seed_loop us vs ws d m (j + 1) mk q tl (Acc_inv H (dec_step m j Hj))
  | right _ => (mk, q, tl)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma build_loop_eq : forall us m j hd nx H,
  build_loop us m j hd nx H =
  match bdec (j <? m) with
  | left Hj =>
      let u := us.[j] in
      let h := hd.[u] in
      build_loop us m (j + 1) hd.[u <- j + 1] nx.[j <- h]
        (Acc_inv H (dec_step m j Hj))
  | right _ => (hd, nx)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma adj_loop_eq : forall vs nx e mk q tl H,
  adj_loop vs nx e mk q tl H =
  match bdec (0 <? e) with
  | left _ =>
      let j := e - 1 in
      let v := vs.[j] in
      let e' := nx.[j] in
      match bdec (e' <? e) with
      | left Hd =>
          if mk.[v] =? 0 then
            adj_loop vs nx e' mk.[v <- 1] q.[tl <- v] (tl + 1)
              (Acc_inv H (dec_lt e' e Hd))
          else adj_loop vs nx e' mk q tl (Acc_inv H (dec_lt e' e Hd))
      | right _ => (mk, q, tl)
      end
  | right _ => (mk, q, tl)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma bfs_loop_eq : forall vs hd nx n h mk q tl H,
  bfs_loop vs hd nx n h mk q tl H =
  match bdec (h <? tl) with
  | left _ =>
      match bdec (h <? n) with
      | left Hh =>
          let x := q.[h] in
          let '(mk', q', tl') :=
            adj_loop vs nx hd.[x] mk q tl (Zwf_well_founded 0 (φ (hd.[x]))) in
          bfs_loop vs hd nx n (h + 1) mk' q' tl' (Acc_inv H (dec_step n h Hh))
      | right _ => mk
      end
  | right _ => mk
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma ans_loop_eq : forall d mk qs Q i out H,
  ans_loop d mk qs Q i out H =
  match bdec (i <? Q) with
  | left Hi =>
      let a := answer_of d mk qs.[i] in
      ans_loop d mk qs Q (i + 1) out.[i <- a] (Acc_inv H (dec_step Q i Hi))
  | right _ => out
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Graph theory on the math side: explicit paths, the reduction of a  *)
(* walk to a short one or a negative cycle, and the classification of  *)
(* a node from a distance view D and a mark view Mk.                   *)
(* ------------------------------------------------------------------ *)

(* The list accessor of the spec (PArray.get shadows the name). *)
Notation lget := Prelude.get.

Section Graph.
Local Open Scope Z_scope.

Variables (us vs : list N) (ws : list Z) (n s : N).

(* Following the edges es (indices) from x leads to t. *)
Fixpoint ok_path (x : N) (es : list N) (t : N) : Prop :=
  match es with
  | [] => x = t
  | j :: es' => (j < len us)%N /\ lget us 0%N j = x /\ ok_path (lget vs 0%N j) es' t
  end.

Fixpoint pw (es : list N) : Z :=
  match es with
  | [] => 0
  | j :: es' => lget ws 0 j + pw es'
  end.

Lemma ok_path_app : forall e1 e2 x t,
  ok_path x (e1 ++ e2) t <-> exists y, ok_path x e1 y /\ ok_path y e2 t.
Proof.
  induction e1 as [| j e1 IH]; simpl; intros e2 x t.
  - split; [intros H; exists x; auto | intros (y & -> & H); exact H].
  - rewrite IH. split.
    + intros (H1 & H2 & y & H3 & H4). exists y. auto.
    + intros (y & (H1 & H2 & H3) & H4). split; [exact H1|]. split; [exact H2|].
      exists y. auto.
Qed.

Lemma pw_app : forall e1 e2, pw (e1 ++ e2) = pw e1 + pw e2.
Proof. induction e1 as [| j e1 IH]; simpl; intros; [reflexivity|]. rewrite IH. lia. Qed.

Lemma walk_path : forall x t c, walk us vs ws x t c ->
  exists es, ok_path x es t /\ pw es = c.
Proof.
  intros x t c H. induction H as [x | j t c Hj Hw IH].
  - exists []. simpl. auto.
  - destruct IH as (es & H1 & H2). exists (j :: es). simpl.
    split; [auto | rewrite H2; reflexivity].
Qed.

Lemma path_walk : forall es x t, ok_path x es t -> walk us vs ws x t (pw es).
Proof.
  induction es as [| j es IH]; simpl; intros x t H.
  - subst. constructor.
  - destruct H as (H1 & H2 & H3). subst x. constructor; auto.
Qed.

Lemma get_P : forall {A} (P : A -> Prop) (l : list A) (d : A) (j : N),
  Forall P l -> (j < len l)%N -> P (lget l d j).
Proof.
  intros A P l d j Hf Hj. unfold Prelude.get, len in *. rewrite Forall_forall in Hf.
  apply Hf. apply nth_In. lia.
Qed.

Fixpoint nodes (x : N) (es : list N) : list N :=
  match es with
  | [] => [x]
  | j :: es' => x :: nodes (lget vs 0%N j) es'
  end.

Lemma nodes_length : forall es x, List.length (nodes x es) = S (List.length es).
Proof. induction es as [| j es IH]; simpl; intros; [reflexivity | rewrite IH; reflexivity]. Qed.

Hypothesis Hlen : len vs = len us.
Hypothesis Hlenw : len ws = len us.
Hypothesis Hvr : Forall (fun v => (v < n)%N) vs.
Hypothesis Hwr : Forall (fun w => -2000 <= w <= 2000) ws.
Hypothesis Hsn : (s < n)%N.

Lemma nodes_bound : forall es x t, ok_path x es t -> (x < n)%N ->
  Forall (fun v => (v < n)%N) (nodes x es).
Proof.
  induction es as [| j es IH]; simpl; intros x t Hp Hx.
  - constructor; auto.
  - destruct Hp as (H1 & H2 & H3). constructor; [exact Hx|].
    eapply IH; [exact H3|]. apply (get_P (fun v => (v < n)%N)); [exact Hvr|].
    rewrite Hlen. exact H1.
Qed.

Lemma nodes_split : forall l1 y r es x t, ok_path x es t ->
  nodes x es = l1 ++ y :: r ->
  exists e1 e2, es = e1 ++ e2 /\ List.length e1 = List.length l1 /\ ok_path x e1 y /\
    ok_path y e2 t /\ nodes y e2 = y :: r.
Proof.
  induction l1 as [| a l1 IH]; intros y r es x t Hp Hn.
  - destruct es as [| j es]; simpl in Hn; injection Hn as Hxy Hr; subst.
    + exists [], []. simpl. auto.
    + exists [], (j :: es). simpl. auto.
  - destruct es as [| j es]; simpl in Hn; injection Hn as Hxa Hr.
    + destruct l1; discriminate.
    + destruct Hp as (H1 & H2 & H3).
      destruct (IH y r es _ t H3 Hr) as (e1 & e2 & E & L & P1 & P2 & N2).
      exists (j :: e1), e2. subst es. simpl. auto 10.
Qed.

Lemma long_dup : forall l : list N, Forall (fun v => (v < n)%N) l ->
  (N.to_nat n < List.length l)%nat -> exists a l1 l2 l3, l = l1 ++ a :: l2 ++ a :: l3.
Proof.
  intros l Hf Hl. apply ListDec.not_NoDup.
  { intros x y. unfold Decidable.decidable. destruct (N.eq_dec x y); auto. }
  intro Hnd.
  assert (Hi : incl l (map N.of_nat (seq 0 (N.to_nat n)))).
  { intros v Hv. rewrite Forall_forall in Hf. specialize (Hf v Hv).
    apply in_map_iff. exists (N.to_nat v). split; [lia|]. apply in_seq. lia. }
  pose proof (NoDup_incl_length Hnd Hi) as H. rewrite length_map, length_seq in H.
  lia.
Qed.

(* A walk with a negative cycle on it, from s to t. *)
Definition negcyc (t : N) : Prop :=
  exists x e1 e2 e3, ok_path s e1 x /\ ok_path x e2 x /\ pw e2 < 0 /\ ok_path x e3 t.

Lemma reduce : forall k es t, List.length es = k -> ok_path s es t ->
  exists es', ok_path s es' t /\ (List.length es' < N.to_nat n)%nat /\
              (pw es' <= pw es \/ negcyc t).
Proof.
  induction k as [k IH] using lt_wf_ind. intros es t Hk Hp.
  destruct (Nat.lt_ge_cases (List.length es) (N.to_nat n)) as [Hs | Hl].
  - exists es. split; [exact Hp|]. split; [exact Hs|]. left. lia.
  - pose proof (nodes_bound es s t Hp Hsn) as Hb.
    destruct (long_dup _ Hb ltac:(rewrite nodes_length; lia)) as (a & l1 & l2 & l3 & Hn).
    destruct (nodes_split l1 a (l2 ++ a :: l3) es s t Hp Hn)
      as (e1 & e' & E1 & L1 & P1 & P' & N').
    destruct (nodes_split (a :: l2) a l3 e' a t P' N')
      as (e2 & e3 & E2 & L2 & P2 & P3 & _).
    assert (P13 : ok_path s (e1 ++ e3) t) by (apply ok_path_app; eauto).
    assert (Hlt : (List.length (e1 ++ e3) < k)%nat).
    { subst. rewrite !length_app in *. simpl in L2. lia. }
    destruct (IH _ Hlt _ t eq_refl P13) as (es' & Q1 & Q2 & Q3).
    exists es'. split; [exact Q1|]. split; [exact Q2|].
    destruct (Z_lt_le_dec (pw e2) 0) as [Hneg | Hpos].
    + right. exists a, e1, e2, e3. auto.
    + destruct Q3 as [Q3 | Q3]; [left | right; exact Q3].
      subst es e'. rewrite !pw_app in *. lia.
Qed.

Fixpoint rep (k : nat) (e : list N) : list N :=
  match k with O => [] | S k => e ++ rep k e end.

Lemma rep_path : forall k e x, ok_path x e x -> ok_path x (rep k e) x.
Proof.
  induction k as [| k IH]; simpl; intros e x H; [reflexivity|].
  apply ok_path_app. exists x. auto.
Qed.

Lemma rep_pw : forall k e, pw (rep k e) = Z.of_nat k * pw e.
Proof.
  induction k as [| k IH]; intros e; cbn [rep]; [reflexivity|].
  rewrite pw_app, IH, Nat2Z.inj_succ. lia.
Qed.

Lemma negcyc_short : forall t, negcyc t -> arbitrarily_short us vs ws s t.
Proof.
  intros t (x & e1 & e2 & e3 & H1 & H2 & H3 & H4) b.
  set (k := Z.to_nat (pw e1 + pw e3 - b + 1)).
  exists (pw (e1 ++ rep k e2 ++ e3)). split.
  - apply path_walk. apply ok_path_app. exists x. split; [exact H1|].
    apply ok_path_app. exists x. split; [apply rep_path; exact H2 | exact H4].
  - rewrite !pw_app, rep_pw.
    assert (Hk : pw e1 + pw e3 - b + 1 <= Z.of_nat k) by lia.
    nia.
Qed.

Lemma pw_lower : forall es x t, ok_path x es t ->
  - 2000 * Z.of_nat (List.length es) <= pw es.
Proof.
  induction es as [| j es IH]; simpl; intros x t H; [lia|].
  destruct H as (Hj & _ & Hp).
  pose proof (get_P _ ws 0 j Hwr ltac:(rewrite Hlenw; exact Hj)) as Hw.
  specialize (IH _ _ Hp). simpl in Hw. lia.
Qed.

Lemma short_negcyc : forall t, arbitrarily_short us vs ws s t -> negcyc t.
Proof.
  intros t Ha. destruct (Ha (-2000 * Z.of_N n)) as (c & Hw & Hc).
  apply walk_path in Hw as (es & Hp & <-).
  destruct (reduce _ es t eq_refl Hp) as (es' & Hp' & Hl & [Hle | Hn]); [|exact Hn].
  pose proof (pw_lower es' s t Hp'). exfalso. lia.
Qed.

(* The classification, from a distance view D and a mark view Mk. *)
Variable D : N -> option Z.
Variable Mk : N -> bool.

Definition seed (v : N) : Prop :=
  exists j, (j < len us)%N /\ lget vs 0%N j = v /\
    exists du, D (lget us 0%N j) = Some du /\
      (D v = None \/ exists dv, D v = Some dv /\ du + lget ws 0 j < dv).

Definition reach (x t : N) : Prop := exists es, ok_path x es t.

Hypothesis HS : forall t d, D t = Some d -> exists es, ok_path s es t /\ pw es = d.
Hypothesis HC : forall es t, ok_path s es t -> (List.length es < N.to_nat n)%nat ->
  exists d, D t = Some d /\ d <= pw es.
Hypothesis HM : forall t, Mk t = true <-> exists v, seed v /\ reach v t.

Lemma reach_D : forall es t, ok_path s es t -> exists d, D t = Some d.
Proof.
  intros es t Hp. destruct (reduce _ es t eq_refl Hp) as (es' & Hp' & Hl & _).
  destruct (HC es' t Hp' Hl) as (d & Hd & _). eauto.
Qed.

Lemma seed_short : forall v, seed v -> arbitrarily_short us vs ws s v.
Proof.
  intros v (j & Hj & <- & du & Hdu & Hc).
  destruct (HS _ _ Hdu) as (eu & Hpu & Hwu).
  assert (Hp : ok_path s (eu ++ [j]) (lget vs 0%N j)).
  { apply ok_path_app. exists (lget us 0%N j). split; [exact Hpu|]. simpl. auto. }
  destruct (reduce _ _ _ eq_refl Hp) as (es' & Hp' & Hl & [Hle | Hn]).
  - exfalso. destruct (HC es' _ Hp' Hl) as (d' & Hd' & Hle').
    rewrite pw_app in Hle. simpl in Hle.
    destruct Hc as [Hc | (dv & Hdv & Hlt)]; [congruence|].
    rewrite Hd' in Hdv. injection Hdv as <-. lia.
  - apply negcyc_short. exact Hn.
Qed.

Lemma path_D : forall es a y, ok_path a es y -> forall da, D a = Some da ->
  (exists dy, D y = Some dy /\ dy <= da + pw es) \/ (exists v, seed v /\ reach v y).
Proof.
  induction es as [| j es IH]; simpl; intros a y Hp da Ha.
  - left. subst. exists da. split; [exact Ha | lia].
  - destruct Hp as (Hj & Hu & Hp).
    assert (Hseed : (D (lget vs 0%N j) = None \/
              exists dv, D (lget vs 0%N j) = Some dv /\ da + lget ws 0 j < dv) ->
              exists v, seed v /\ reach v y).
    { intros Hc. exists (lget vs 0%N j). split.
      - exists j. split; [exact Hj|]. split; [reflexivity|].
        exists da. rewrite Hu. split; [exact Ha | exact Hc].
      - exists es. exact Hp. }
    destruct (D (lget vs 0%N j)) as [dv |] eqn:Ev.
    + destruct (Z_lt_le_dec (da + lget ws 0 j) dv) as [Hlt | Hge].
      * right. apply Hseed. right. eauto.
      * destruct (IH _ _ Hp dv Ev) as [(dy & Hdy & Hle) | Hr].
        -- left. exists dy. split; [exact Hdy | lia].
        -- right. exact Hr.
    + right. apply Hseed. left. reflexivity.
Qed.

Lemma negcyc_mark : forall t, negcyc t -> exists v, seed v /\ reach v t.
Proof.
  intros t (x & e1 & e2 & e3 & H1 & H2 & H3 & H4).
  destruct (reach_D _ _ H1) as (dx & Hdx).
  destruct (path_D e2 x x H2 dx Hdx) as [(dy & Hdy & Hle) | (v & Hv & es & Hr)].
  - rewrite Hdx in Hdy. injection Hdy as <-. lia.
  - exists v. split; [exact Hv|]. exists (es ++ e3). apply ok_path_app. eauto.
Qed.

Lemma reach_short : forall v t, arbitrarily_short us vs ws s v -> reach v t ->
  arbitrarily_short us vs ws s t.
Proof.
  intros v t Ha (es & Hp) b. destruct (Ha (b - pw es)) as (c & Hw & Hc).
  apply walk_path in Hw as (es0 & Hp0 & <-).
  exists (pw (es0 ++ es)). split.
  - apply path_walk. apply ok_path_app. eauto.
  - rewrite pw_app. lia.
Qed.

Definition ans_math (t : N) : answer Z :=
  match D t with
  | None => Impossible
  | Some d => if Mk t then MinusInfinity else Dist d
  end.

Lemma arb_reach : forall t, arbitrarily_short us vs ws s t -> reachable us vs ws s t.
Proof. intros t Ha. destruct (Ha 0) as (c & Hw & _). exists c. exact Hw. Qed.

Lemma min_reach : forall t d, min_distance us vs ws s t d -> reachable us vs ws s t.
Proof. intros t d (Hw & _). exists d. exact Hw. Qed.

Lemma arb_min : forall t d, arbitrarily_short us vs ws s t ->
  min_distance us vs ws s t d -> False.
Proof.
  intros t d Ha (Hw & Hm). destruct (Ha d) as (c & Hc & Hlt).
  specialize (Hm c Hc). lia.
Qed.

Lemma ans_correct : forall t,
  (ans_math t = Impossible <-> ~ reachable us vs ws s t) /\
  (ans_math t = MinusInfinity <-> arbitrarily_short us vs ws s t) /\
  (forall d, ans_math t = Dist d <-> min_distance us vs ws s t d).
Proof.
  intros t. unfold ans_math.
  destruct (D t) as [d |] eqn:Ed.
  - destruct (Mk t) eqn:Em.
    + assert (Ha : arbitrarily_short us vs ws s t).
      { apply HM in Em as (v & Hv & Hr). eapply reach_short; [|exact Hr].
        apply seed_short. exact Hv. }
      split; [|split].
      * split; [discriminate | intros Hn; exfalso; apply Hn; apply arb_reach; exact Ha].
      * split; auto.
      * intros d0. split; [discriminate | intros Hm; exfalso; eapply arb_min; eauto].
    + assert (Hna : ~ arbitrarily_short us vs ws s t).
      { intros Ha. apply short_negcyc, negcyc_mark in Ha.
        apply HM in Ha. congruence. }
      assert (Hmin : min_distance us vs ws s t d).
      { destruct (HS _ _ Ed) as (es & Hp & Hw). split.
        - rewrite <- Hw. apply path_walk. exact Hp.
        - intros c Hc. apply walk_path in Hc as (es0 & Hp0 & <-).
          destruct (reduce _ es0 t eq_refl Hp0) as (es' & Hp' & Hl & [Hle | Hn]).
          + destruct (HC es' t Hp' Hl) as (d' & Hd' & Hle').
            rewrite Ed in Hd'. injection Hd' as <-. lia.
          + exfalso. apply Hna. apply negcyc_short. exact Hn. }
      split; [|split].
      * split; [discriminate | intros Hn; exfalso; apply Hn; eapply min_reach; eauto].
      * split; [discriminate | intros Ha; contradiction].
      * intros d0. split.
        -- intros E. injection E as <-. exact Hmin.
        -- intros Hm0. f_equal. destruct Hmin as (Hw1 & Hm1). destruct Hm0 as (Hw2 & Hm2).
           specialize (Hm1 _ Hw2). specialize (Hm2 _ Hw1). lia.
  - assert (Hnr : ~ reachable us vs ws s t).
    { intros (c & Hw). apply walk_path in Hw as (es & Hp & _).
      destruct (reach_D _ _ Hp) as (d & Hd). congruence. }
    split; [|split].
    + split; auto.
    + split; [discriminate | intros Ha; exfalso; apply Hnr; apply arb_reach; exact Ha].
    + intros d0. split; [discriminate | intros Hm; exfalso; apply Hnr; eapply min_reach; eauto].
Qed.

End Graph.

(* ------------------------------------------------------------------ *)
(* Uint63 / Sint63 / PArray plumbing                                   *)
(* ------------------------------------------------------------------ *)

(* The array index of a node. *)
Definition idx (v : N) : int := of_Z (Z.of_N v).

Lemma idx_spec : forall v : N, (Z.of_N v < wB)%Z -> (φ (idx v)) = Z.of_N v.
Proof. intros v H. unfold idx. rewrite of_Z_spec. apply Z.mod_small. lia. Qed.

Lemma idx_of : forall x : int, idx (Z.to_N (φ x)) = x.
Proof.
  intros x. unfold idx. pose proof (to_Z_bounded x).
  rewrite Z2N.id by lia. apply of_to_Z.
Qed.

Lemma idx_inj : forall v w : N, (Z.of_N v < wB)%Z -> (Z.of_N w < wB)%Z ->
  idx v = idx w -> v = w.
Proof.
  intros v w Hv Hw E. apply (f_equal to_Z) in E. rewrite !idx_spec in E by lia. lia.
Qed.

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma INF_val : Sint63.to_Z INF = 4611686018427387903%Z.
Proof. reflexivity. Qed.

Lemma sadd : forall a b : int,
  (- 10 ^ 12 <= Sint63.to_Z a <= 10 ^ 12)%Z -> (- 10 ^ 12 <= Sint63.to_Z b <= 10 ^ 12)%Z ->
  Sint63.to_Z (a + b) = (Sint63.to_Z a + Sint63.to_Z b)%Z.
Proof.
  intros a b Ha Hb. apply Sint63.to_Z_add.
  change (Sint63.to_Z Sint63.min_int) with (-4611686018427387904)%Z.
  change (Sint63.to_Z Sint63.max_int) with 4611686018427387903%Z. lia.
Qed.

Lemma not_INF : forall x : int, (Sint63.to_Z x <= 10 ^ 12)%Z -> (x =? INF) = false.
Proof.
  intros x H. apply eqb_false_spec. intros ->. rewrite INF_val in H. lia.
Qed.

Lemma ltsb_iff : forall x y : int, ltsb x y = true <-> (Sint63.to_Z x < Sint63.to_Z y)%Z.
Proof. intros x y. destruct (Sint63.ltbP x y); split; auto; discriminate. Qed.

Lemma alength_bound : forall A (t : array A), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros A t. pose proof (leb_length A t) as H.
  rewrite leb_spec in H. change (φ PArray.max_length) with 4194303%Z in H. exact H.
Qed.

Lemma alength_make : forall A (k : int) (a : A), ((φ k) <= 4194303)%Z ->
  PArray.length (PArray.make k a) = k.
Proof.
  intros A k a H. rewrite length_make.
  replace (k <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec. change (φ PArray.max_length) with 4194303%Z. exact H.
Qed.

(* The PArray lemmas at the universe of this file's arrays. *)
Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma aget_make : forall (k i b : int), (PArray.make k b).[i] = b.
Proof. intros k i b. exact (get_make int b k i). Qed.

Lemma alength_make_int : forall (k : int) (b : int), ((φ k) <= 4194303)%Z ->
  PArray.length (PArray.make k b) = k.
Proof. intros k b H. exact (alength_make int k b H). Qed.

Lemma bget_set_same : forall (t : array (answer int)) (i : int) (b : answer int),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same (answer int) t i b H). Qed.

Lemma bget_set_other : forall (t : array (answer int)) (i j : int) (b : answer int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other (answer int) t i j b H). Qed.

Lemma blength_set : forall (t : array (answer int)) (i : int) (b : answer int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set (answer int) t i b). Qed.

(* Reading the inputs. *)
Lemma repr_len : forall A M `{Repr A M} (x : array A) (l : list M), repr x l ->
  (φ (PArray.length x)) = Z.of_N (len l).
Proof. intros A M R x l [Hl _]. unfold len. rewrite nat_N_Z. symmetry. exact Hl. Qed.

Lemma repr_get_uint : forall (x : array uint) (l : list N), repr x l ->
  forall i : int, ((φ i) < Z.of_N (len l))%Z ->
  (φ (x.[i])) = Z.of_N (lget l 0%N (Z.to_N (φ i))).
Proof.
  intros x l [Hl Hc] i Hi. unfold len in Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m0 & Hm & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id, of_to_Z in Hr by (pose proof (to_Z_bounded i); lia).
  unfold Prelude.get. rewrite Z_N_nat. rewrite (nth_error_nth _ _ _ Hm).
  rewrite <- Hr. rewrite Z2N.id by (pose proof (to_Z_bounded (x.[i])); lia).
  reflexivity.
Qed.

Lemma repr_get_sint : forall (x : array sint) (l : list Z), repr x l ->
  forall i : int, ((φ i) < Z.of_N (len l))%Z ->
  Sint63.to_Z (x.[i]) = lget l 0%Z (Z.to_N (φ i)).
Proof.
  intros x l [Hl Hc] i Hi. unfold len in Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m0 & Hm & Hr).
  unfold repr, repr_sint in Hr.
  rewrite Z2Nat.id, of_to_Z in Hr by (pose proof (to_Z_bounded i); lia).
  unfold Prelude.get. rewrite Z_N_nat. rewrite (nth_error_nth _ _ _ Hm).
  rewrite <- Hr. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The machine side, for fixed inputs                                  *)
(* ------------------------------------------------------------------ *)

Section Machine.

Variables (n s : N) (us vs : list N) (ws : list Z).
Variables (xn xs : int) (xus xvs xws : array int).

Hypothesis Hn : (1 <= n <= 1000)%N.
Hypothesis Hm : (len us <= 5000)%N.
Hypothesis Hlv : len vs = len us.
Hypothesis Hlw : len ws = len us.
Hypothesis Hsn : (s < n)%N.
Hypothesis Hur : Forall (fun u => (u < n)%N) us.
Hypothesis Hvr : Forall (fun v => (v < n)%N) vs.
Hypothesis Hwr : Forall (fun w => (-2000 <= w <= 2000)%Z) ws.
Hypothesis Hxn : (φ xn) = Z.of_N n.
Hypothesis Hxs : (φ xs) = Z.of_N s.
Hypothesis HLu : (φ (PArray.length xus)) = Z.of_N (len us).
Hypothesis Hus : forall i : int, ((φ i) < Z.of_N (len us))%Z ->
  (φ (xus.[i])) = Z.of_N (lget us 0%N (Z.to_N (φ i))).
Hypothesis Hvs : forall i : int, ((φ i) < Z.of_N (len us))%Z ->
  (φ (xvs.[i])) = Z.of_N (lget vs 0%N (Z.to_N (φ i))).
Hypothesis Hws : forall i : int, ((φ i) < Z.of_N (len us))%Z ->
  Sint63.to_Z (xws.[i]) = lget ws 0%Z (Z.to_N (φ i)).

(* The edge with index k (a Z). *)
Definition U (k : Z) : N := lget us 0%N (Z.to_N k).
Definition V (k : Z) : N := lget vs 0%N (Z.to_N k).
Definition W (k : Z) : Z := lget ws 0%Z (Z.to_N k).

(* The distance table and the marks, read as math values. *)
Definition DV (d : array int) (v : N) : option Z :=
  if (v <? n)%N then
    if d.[idx v] =? INF then None else Some (Sint63.to_Z d.[idx v])
  else None.

Definition MK (mk : array int) (v : N) : bool :=
  ((v <? n)%N && negb (mk.[idx v] =? 0))%bool.

Local Open Scope Z_scope.

Lemma idx_lt : forall v : N, (v < n)%N -> (φ (idx v)) = Z.of_N v.
Proof. intros v Hv. apply idx_spec. rewrite wB_val. lia. Qed.

Lemma edge_facts : forall j : int, (φ j) < Z.of_N (len us) ->
  xus.[j] = idx (U (φ j)) /\ xvs.[j] = idx (V (φ j)) /\ (U (φ j) < n)%N /\ (V (φ j) < n)%N /\
  Sint63.to_Z (xws.[j]) = W (φ j) /\ -2000 <= W (φ j) <= 2000.
Proof.
  intros j Hj. pose proof (to_Z_bounded j) as Bj.
  assert (Hj' : (Z.to_N (φ j) < len us)%N) by lia.
  split; [|split; [|split; [|split; [|split]]]].
  - rewrite <- (idx_of (xus.[j])). rewrite (Hus j Hj), N2Z.id. reflexivity.
  - rewrite <- (idx_of (xvs.[j])). rewrite (Hvs j Hj), N2Z.id. reflexivity.
  - unfold U. apply (get_P (fun u => (u < n)%N)); auto.
  - unfold V. apply (get_P (fun u => (u < n)%N)); [auto | rewrite Hlv; exact Hj'].
  - apply Hws. exact Hj.
  - unfold W. apply (get_P (fun w => -2000 <= w <= 2000)); [auto | rewrite Hlw; exact Hj'].
Qed.

Lemma path_lt : forall es x t, ok_path us vs x es t -> (x < n)%N -> (t < n)%N.
Proof.
  induction es as [| j es IH]; simpl; intros x t Hp Hx; [subst; exact Hx|].
  destruct Hp as (Hj & _ & Hp). eapply IH; [exact Hp|].
  apply (get_P (fun u => (u < n)%N)); [auto | rewrite Hlv; exact Hj].
Qed.

Lemma DV_some : forall d v x, DV d v = Some x ->
  (v < n)%N /\ (d.[idx v] =? INF)%uint63 = false /\ x = Sint63.to_Z d.[idx v].
Proof.
  intros d v x H. unfold DV in H. destruct (N.ltb_spec v n); [|discriminate].
  destruct (d.[idx v] =? INF)%uint63; [discriminate|]. injection H as <-. auto.
Qed.

Lemma DV_eq : forall d v, (v < n)%N -> (d.[idx v] =? INF)%uint63 = false ->
  DV d v = Some (Sint63.to_Z d.[idx v]).
Proof.
  intros d v Hv E. unfold DV. destruct (N.ltb_spec v n); [|lia]. rewrite E. reflexivity.
Qed.

Lemma DV_none : forall d v, (d.[idx v] =? INF)%uint63 = true -> DV d v = None.
Proof.
  intros d v E. unfold DV. destruct (v <? n)%N; [rewrite E|]; reflexivity.
Qed.

Lemma DV_set : forall d v x w, (φ (PArray.length d)) = Z.of_N n -> (v < n)%N ->
  DV d.[idx v <- x] w =
  if N.eqb w v then (if (x =? INF)%uint63 then None else Some (Sint63.to_Z x))
  else DV d w.
Proof.
  intros d v x w Hl Hv. unfold DV.
  destruct (N.eqb_spec w v) as [-> | Hne].
  - destruct (N.ltb_spec v n); [|lia].
    rewrite aget_set_same; [reflexivity|]. rewrite ltb_spec, idx_lt by exact Hv. lia.
  - destruct (N.ltb_spec w n); [|reflexivity].
    rewrite aget_set_other; [reflexivity|].
    intro E. apply idx_inj in E; [congruence| |]; rewrite wB_val; lia.
Qed.

(* The invariants of the relaxation rounds. *)
Definition Sound (B : Z) (d : array int) : Prop :=
  (φ (PArray.length d)) = Z.of_N n /\
  forall v x, DV d v = Some x ->
    (exists es, ok_path us vs s es v /\ pw ws es = x) /\ - B <= x <= B.

Definition Compl (K : nat) (d : array int) : Prop :=
  forall es t, ok_path us vs s es t -> (List.length es <= K)%nat ->
    exists x, DV d t = Some x /\ x <= pw ws es.

Definition LeD (d' d : array int) : Prop :=
  forall v x, DV d v = Some x -> exists y, DV d' v = Some y /\ y <= x.

Definition Proc (d0 d : array int) (J : Z) : Prop :=
  forall j, 0 <= j < J -> forall du, DV d0 (U j) = Some du ->
    exists dv, DV d (V j) = Some dv /\ dv <= du + W j.

Lemma Sound_mono : forall B B' d, Sound B d -> B <= B' -> Sound B' d.
Proof.
  intros B B' d (Hl & H) Hle. split; [exact Hl|].
  intros v x Hx. destruct (H v x Hx) as (H1 & H2). split; [exact H1 | lia].
Qed.

Lemma LeD_refl : forall d, LeD d d.
Proof. intros d v x H. exists x. split; [exact H | lia]. Qed.

Lemma LeD_trans : forall d1 d2 d3, LeD d1 d2 -> LeD d2 d3 -> LeD d1 d3.
Proof.
  intros d1 d2 d3 H12 H23 v x H. destruct (H23 v x H) as (y & Hy & Hle).
  destruct (H12 v y Hy) as (z & Hz & Hle'). exists z. split; [exact Hz | lia].
Qed.

Lemma Proc_le : forall d0 d d' J, Proc d0 d J -> LeD d' d -> Proc d0 d' J.
Proof.
  intros d0 d d' J HP HL j Hj du Hdu. destruct (HP j Hj du Hdu) as (dv & Hdv & Hle).
  destruct (HL _ _ Hdv) as (y & Hy & Hle'). exists y. split; [exact Hy | lia].
Qed.

Lemma Compl_le : forall K d d', Compl K d -> LeD d' d -> Compl K d'.
Proof.
  intros K d d' HC HL es t Hp Hl. destruct (HC es t Hp Hl) as (x & Hx & Hle).
  destruct (HL _ _ Hx) as (y & Hy & Hle'). exists y. split; [exact Hy | lia].
Qed.

Lemma relax_spec : forall (j : int) d ch B,
  (φ j) < Z.of_N (len us) -> Sound B d -> 0 <= B <= 10 ^ 11 ->
  let r := relax xus xvs xws j d ch in
  Sound (B + 2000) (fst r) /\ LeD (fst r) d /\
  (forall du, DV d (U (φ j)) = Some du ->
     exists dv, DV (fst r) (V (φ j)) = Some dv /\ dv <= du + W (φ j)) /\
  ((fst r = d /\ snd r = ch) \/ snd r = true).
Proof.
  intros j d ch B Hj HS HB r.
  destruct (edge_facts j Hj) as (Eu & Ev & Hu & Hv & Ew & Hw).
  pose proof HS as (Hl & Hd).
  unfold r, relax. rewrite Eu, Ev.
  destruct (d.[idx (U (φ j))] =? INF)%uint63 eqn:Einf.
  - cbn [fst snd]. split; [eapply Sound_mono; [exact HS | lia]|].
    split; [apply LeD_refl|]. split; [|left; auto].
    intros du Hdu. rewrite DV_none in Hdu by exact Einf. discriminate.
  - pose proof (DV_eq d _ Hu Einf) as Hdu.
    destruct (Hd _ _ Hdu) as ((eu & Hpu & Hwu) & Hbu).
    set (du := d.[idx (U (φ j))]) in *.
    assert (Hnd : Sint63.to_Z (du + xws.[j])%uint63 = Sint63.to_Z du + W (φ j))
      by (rewrite sadd; [rewrite Ew; reflexivity | lia | lia]).
    assert (Hpath : ok_path us vs s (eu ++ [Z.to_N (φ j)]) (V (φ j)) /\
                    pw ws (eu ++ [Z.to_N (φ j)]) = Sint63.to_Z du + W (φ j)).
    { split.
      - apply ok_path_app. exists (U (φ j)). split; [exact Hpu|]. simpl.
        split; [pose proof (to_Z_bounded j); lia|]. split; reflexivity.
      - rewrite pw_app. simpl. rewrite Hwu. unfold W. lia. }
    destruct (ltsb (du + xws.[j])%uint63 d.[idx (V (φ j))]) eqn:Elt.
    + cbn [fst snd]. apply ltsb_iff in Elt.
      assert (Hni : ((du + xws.[j])%uint63 =? INF)%uint63 = false)
        by (apply not_INF; lia).
      split; [split|split; [|split]].
      * rewrite alength_set. exact Hl.
      * intros w x Hx. rewrite DV_set in Hx by assumption.
        destruct (N.eqb_spec w (V (φ j))) as [-> | Hne].
        -- rewrite Hni in Hx. injection Hx as <-. split; [|lia].
           exists (eu ++ [Z.to_N (φ j)]). destruct Hpath as (P1 & P2). split; [exact P1 | lia].
        -- destruct (Hd w x Hx) as (H1 & H2). split; [exact H1 | lia].
      * intros w x Hx. rewrite DV_set by assumption.
        destruct (N.eqb_spec w (V (φ j))) as [-> | Hne].
        -- rewrite Hni. eexists; split; [reflexivity|].
           apply DV_some in Hx as (_ & _ & ->). lia.
        -- exists x. split; [exact Hx | lia].
      * intros du' Hdu'. rewrite Hdu in Hdu'. injection Hdu' as <-.
        rewrite DV_set by assumption. rewrite N.eqb_refl, Hni.
        eexists; split; [reflexivity | lia].
      * right. reflexivity.
    + cbn [fst snd]. split; [eapply Sound_mono; [exact HS | lia]|].
      split; [apply LeD_refl|]. split; [|left; auto].
      intros du' Hdu'. rewrite Hdu in Hdu'. injection Hdu' as <-.
      assert (Elt' : ~ Sint63.to_Z (du + xws.[j])%uint63 < Sint63.to_Z d.[idx (V (φ j))])
        by (rewrite <- ltsb_iff; congruence).
      destruct (d.[idx (V (φ j))] =? INF)%uint63 eqn:Ei.
      * apply eqb_correct in Ei. rewrite Ei, INF_val in Elt'. lia.
      * rewrite (DV_eq d _ Hv Ei). eexists; split; [reflexivity | lia].
Qed.


Lemma U_of : forall j : N, U (Z.of_N j) = lget us 0%N j.
Proof. intros j. unfold U. rewrite N2Z.id. reflexivity. Qed.
Lemma V_of : forall j : N, V (Z.of_N j) = lget vs 0%N j.
Proof. intros j. unfold V. rewrite N2Z.id. reflexivity. Qed.
Lemma W_of : forall j : N, W (Z.of_N j) = lget ws 0%Z j.
Proof. intros j. unfold W. rewrite N2Z.id. reflexivity. Qed.

Lemma edges_spec : forall d0 B0, 0 <= B0 -> B0 + 2000 * Z.of_N (len us) <= 10 ^ 11 ->
  forall z j d ch H, gap (PArray.length xus) j = z ->
  (φ j) <= Z.of_N (len us) -> Sound (B0 + 2000 * (φ j)) d -> LeD d d0 -> Proc d0 d (φ j) ->
  (ch = false -> d = d0) ->
  match edges_loop xus xvs xws (PArray.length xus) j d ch H with
  | (d', ch') =>
    Sound (B0 + 2000 * Z.of_N (len us)) d' /\ LeD d' d0 /\
    Proc d0 d' (Z.of_N (len us)) /\ (ch' = false -> d' = d0)
  end.
Proof.
  intros d0 B0 HB0 HB z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j d ch H Hz Hj HS HL HP Hch. rewrite edges_loop_eq.
  destruct (bdec (j <? PArray.length xus)%uint63) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec, HLu in Hlt'.
    pose proof (to_Z_bounded j) as Bj.
    assert (Hj1 : (φ (j + 1))%uint63 = (φ j) + 1) by sia.
    destruct (relax_spec j d ch (B0 + 2000 * (φ j)) Hlt' HS ltac:(lia))
      as (S1 & L1 & E1 & C1).
    destruct (relax xus xvs xws j d ch) as [d' ch'] eqn:Er. cbn [fst snd] in *.
    apply (IH (gap (PArray.length xus) (j + 1)%uint63)); [ | reflexivity | lia | | | | ].
    + rewrite <- Hz. apply dec_step. exact Hlt.
    + rewrite Hj1. replace (B0 + 2000 * ((φ j) + 1)) with (B0 + 2000 * (φ j) + 2000) by ring.
      exact S1.
    + eapply LeD_trans; eauto.
    + rewrite Hj1. intros j' Hj' du Hdu.
      destruct (Z.eq_dec j' (φ j)) as [-> | Hne].
      * destruct (HL _ _ Hdu) as (du1 & Hdu1 & Hle).
        destruct (E1 _ Hdu1) as (dv & Hdv & Hle').
        exists dv. split; [exact Hdv | lia].
      * eapply Proc_le; [exact HP | exact L1 | lia | exact Hdu].
    + intros Hc. destruct C1 as [(-> & ->) | ->]; [auto | discriminate].
  - rewrite <- Bool.not_true_iff_false, ltb_spec, HLu in Hge.
    replace (φ j) with (Z.of_N (len us)) in * by lia. auto.
Qed.

Lemma round_spec : forall B K d d' ch, Sound B d -> Compl K d -> 0 <= B ->
  B + 2000 * Z.of_N (len us) <= 10 ^ 11 ->
  edges_loop xus xvs xws (PArray.length xus) 0 d false
    (Zwf_well_founded 0 (gap (PArray.length xus) 0)) = (d', ch) ->
  Sound (B + 2000 * Z.of_N (len us)) d' /\ Compl (S K) d' /\
  (ch = false -> d' = d /\ Proc d d (Z.of_N (len us))).
Proof.
  intros B K d d' ch HS HC HB0 HB E.
  pose proof (edges_spec d B HB0 HB _ 0 d false
                (Zwf_well_founded 0 (gap (PArray.length xus) 0)) eq_refl) as X.
  rewrite E in X. change (φ 0) with 0 in X.
  destruct X as (S1 & L1 & P1 & C1).
  - lia.
  - rewrite Z.mul_0_r, Z.add_0_r. exact HS.
  - apply LeD_refl.
  - intros j Hj. lia.
  - auto.
  - split; [exact S1|]. split.
    + intros es t Hp Hl.
      destruct (Nat.le_gt_cases (List.length es) K) as [Hle | Hgt].
      * eapply Compl_le; [exact HC | exact L1 | exact Hp | exact Hle].
      * destruct (exists_last (l := es) ltac:(intros ->; simpl in Hgt; lia))
          as (es' & j & ->).
        rewrite length_app in Hl, Hgt. simpl in Hl, Hgt.
        apply ok_path_app in Hp as (y & Hp1 & Hp2). simpl in Hp2.
        destruct Hp2 as (Hj & Hu & <-).
        destruct (HC es' y Hp1 ltac:(lia)) as (x & Hx & Hle).
        destruct (P1 (Z.of_N j) ltac:(lia) x) as (dv & Hdv & Hle').
        { rewrite U_of, Hu. exact Hx. }
        rewrite V_of in Hdv. rewrite W_of in Hle'.
        exists dv. split; [exact Hdv|]. rewrite pw_app. simpl. lia.
    + intros Hc. specialize (C1 Hc). subst d'. split; [reflexivity | exact P1].
Qed.

Lemma stable_compl : forall d x, Proc d d (Z.of_N (len us)) -> DV d s = Some x -> x <= 0 ->
  forall es t, ok_path us vs s es t -> exists y, DV d t = Some y /\ y <= pw ws es.
Proof.
  intros d x HP Hs Hx es. induction es as [| j es IH] using rev_ind; intros t Hp.
  - simpl in Hp. subst t. exists x. simpl. auto.
  - apply ok_path_app in Hp as (y & Hp1 & Hp2). simpl in Hp2.
    destruct Hp2 as (Hj & Hu & <-).
    destruct (IH y Hp1) as (dy & Hdy & Hle).
    destruct (HP (Z.of_N j) ltac:(lia) dy) as (dv & Hdv & Hle').
    { rewrite U_of, Hu. exact Hdy. }
    rewrite V_of in Hdv. rewrite W_of in Hle'.
    exists dv. split; [exact Hdv|]. rewrite pw_app. simpl. lia.
Qed.

Lemma rounds_spec : forall R, (φ R) = Z.of_N n - 1 ->
  forall z k d H, gap R k = z -> (φ k) <= (φ R) ->
  Sound (2000 * Z.of_N (len us) * (φ k)) d -> Compl (Z.to_nat (φ k)) d ->
  Sound (2000 * Z.of_N (len us) * (Z.of_N n - 1))
        (rounds_loop xus xvs xws (PArray.length xus) R k d H) /\
  Compl (N.to_nat n - 1) (rounds_loop xus xvs xws (PArray.length xus) R k d H).
Proof.
  intros R HR z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k d H Hz Hk HS HC. rewrite rounds_loop_eq.
  destruct (bdec (k <? R)%uint63) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    pose proof (to_Z_bounded k) as Bk.
    assert (Hk1 : (φ (k + 1))%uint63 = (φ k) + 1) by sia.
    destruct (edges_loop xus xvs xws (PArray.length xus) 0 d false
                (Zwf_well_founded 0 (gap (PArray.length xus) 0))) as [d' ch] eqn:E.
    assert (HB0 : 0 <= 2000 * Z.of_N (len us) * (φ k)) by nia.
    assert (HB : 2000 * Z.of_N (len us) * (φ k) + 2000 * Z.of_N (len us) <= 10 ^ 11) by nia.
    destruct (round_spec _ _ d d' ch HS HC HB0 HB E) as (S1 & C1 & St).
    destruct ch.
    + apply (IH (gap R (k + 1)%uint63)); [ | reflexivity | lia | | ].
      * rewrite <- Hz. apply dec_step. exact Hlt.
      * rewrite Hk1. replace (2000 * Z.of_N (len us) * ((φ k) + 1))
          with (2000 * Z.of_N (len us) * (φ k) + 2000 * Z.of_N (len us)) by ring.
        exact S1.
      * rewrite Hk1, Z2Nat.inj_add, Nat.add_1_r by lia. exact C1.
    + destruct (St eq_refl) as (Ed & HP). subst d'.
      split.
      * eapply Sound_mono; [exact S1 | nia].
      * destruct (HC [] s eq_refl ltac:(simpl; lia)) as (x & Hx & Hle).
        intros es t Hp _. eapply stable_compl; [exact HP | exact Hx | exact Hle | exact Hp].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
    replace (φ k) with (Z.of_N n - 1) in * by lia.
    split; [exact HS|].
    replace (N.to_nat n - 1)%nat with (Z.to_nat (Z.of_N n - 1)) by lia. exact HC.
Qed.


Lemma init_spec :
  Sound 0 ((PArray.make xn INF).[xs <- 0%uint63]) /\
  Compl 0 ((PArray.make xn INF).[xs <- 0%uint63]).
Proof.
  assert (Exs : xs = idx s) by (rewrite <- (idx_of xs), Hxs, N2Z.id; reflexivity).
  assert (Hl : (φ (PArray.length (PArray.make xn INF))) = Z.of_N n)
    by (rewrite alength_make_int by lia; exact Hxn).
  assert (HD : forall w, DV (PArray.make xn INF).[xs <- 0%uint63] w =
                         if N.eqb w s then Some 0 else None).
  { intros w. rewrite Exs, DV_set by assumption.
    destruct (N.eqb w s); [reflexivity|].
    apply DV_none. rewrite aget_make. reflexivity. }
  split.
  - split; [rewrite alength_set; exact Hl|]. intros v x Hx. rewrite HD in Hx.
    destruct (N.eqb_spec v s) as [-> |]; [|discriminate]. injection Hx as <-.
    split; [exists []; simpl; auto | lia].
  - intros es t Hp Hle. destruct es; [|simpl in Hle; lia]. simpl in Hp. subst t.
    rewrite HD, N.eqb_refl. exists 0. simpl. split; [reflexivity | lia].
Qed.

(* The queue: its first tl cells, as a list of nodes. *)
Definition qlist (q : array int) (tl : int) : list N :=
  map (fun k => Z.to_N (φ (q.[of_Z (Z.of_nat k)]))) (seq 0 (Z.to_nat (φ tl))).

Definition QI (mk q : array int) (tl : int) : Prop :=
  (φ (PArray.length mk)) = Z.of_N n /\ (φ (PArray.length q)) = Z.of_N n /\
  (φ tl) <= Z.of_N n /\ NoDup (qlist q tl) /\ Forall (fun v => (v < n)%N) (qlist q tl) /\
  forall v, MK mk v = true <-> In v (qlist q tl).

Lemma MK_set : forall mk v x w, (φ (PArray.length mk)) = Z.of_N n -> (v < n)%N ->
  MK mk.[idx v <- x] w = if N.eqb w v then negb (x =? 0)%uint63 else MK mk w.
Proof.
  intros mk v x w Hl Hv. unfold MK.
  destruct (N.eqb_spec w v) as [-> | Hne].
  - destruct (N.ltb_spec v n); [|lia].
    rewrite aget_set_same; [reflexivity|]. rewrite ltb_spec, idx_lt by exact Hv. lia.
  - destruct (N.ltb_spec w n); [|reflexivity].
    rewrite aget_set_other; [reflexivity|].
    intro E. apply idx_inj in E; [congruence| |]; rewrite wB_val; lia.
Qed.

Lemma qlist_length : forall q tl, List.length (qlist q tl) = Z.to_nat (φ tl).
Proof. intros q tl. unfold qlist. rewrite length_map, length_seq. reflexivity. Qed.

Lemma qlist_snoc : forall q tl x, (φ tl) < (φ (PArray.length q)) ->
  qlist q.[tl <- x] (tl + 1)%uint63 = qlist q tl ++ [Z.to_N (φ x)].
Proof.
  intros q tl x Hlt. unfold qlist.
  pose proof (alength_bound _ q) as Bq. pose proof (to_Z_bounded tl) as Bt.
  assert (E1 : Z.to_nat (φ (tl + 1))%uint63 = S (Z.to_nat (φ tl))) by sia.
  rewrite E1, seq_S, map_app. simpl. f_equal.
  - apply map_ext_in. intros k Hk. apply in_seq in Hk.
    rewrite aget_set_other; [reflexivity|]. intro E.
    apply (f_equal to_Z) in E. rewrite of_Z_spec, Z.mod_small in E by (rewrite wB_val; lia).
    lia.
  - rewrite Z2Nat.id, of_to_Z by lia. rewrite aget_set_same; [reflexivity|].
    rewrite ltb_spec. lia.
Qed.

Lemma enqueue : forall mk q tl v, QI mk q tl -> (v < n)%N -> MK mk v = false ->
  QI mk.[idx v <- 1%uint63] q.[tl <- idx v] (tl + 1)%uint63 /\
  (φ (tl + 1))%uint63 = (φ tl) + 1 /\
  (forall w, MK mk.[idx v <- 1%uint63] w = true <-> w = v \/ MK mk w = true) /\
  (forall k, (φ k) < (φ tl) -> q.[tl <- idx v].[k] = q.[k]).
Proof.
  intros mk q tl v (Hlm & Hlq & Htl & Hnd & Hf & Hiff) Hv Hmv.
  assert (Hnin : ~ In v (qlist q tl)) by (rewrite <- Hiff; congruence).
  pose proof (to_Z_bounded tl) as Btl.
  assert (Hlt : (φ tl) < Z.of_N n).
  { assert (Hnd' : NoDup (v :: qlist q tl)) by (constructor; assumption).
    assert (Hi : incl (v :: qlist q tl) (map N.of_nat (seq 0 (N.to_nat n)))).
    { intros w Hw.
      assert (Hwn : (w < n)%N).
      { destruct Hw as [<- | Hw]; [exact Hv|].
        rewrite Forall_forall in Hf. apply Hf. exact Hw. }
      apply in_map_iff. exists (N.to_nat w). split; [lia|]. apply in_seq. lia. }
    pose proof (NoDup_incl_length Hnd' Hi) as H. simpl in H.
    rewrite length_map, length_seq, qlist_length in H. lia. }
  assert (Htl1 : (φ (tl + 1))%uint63 = (φ tl) + 1) by sia.
  assert (Hsn' : qlist q.[tl <- idx v] (tl + 1)%uint63 = qlist q tl ++ [v]).
  { rewrite qlist_snoc by lia. rewrite idx_lt by exact Hv. rewrite N2Z.id. reflexivity. }
  assert (Hmk : forall w, MK mk.[idx v <- 1%uint63] w = true <-> w = v \/ MK mk w = true).
  { intros w. rewrite MK_set by assumption. destruct (N.eqb_spec w v) as [-> | Hne].
    - split; [auto | reflexivity].
    - split; [auto | intros [E | E]; [congruence | exact E]]. }
  split; [|split; [exact Htl1 | split; [exact Hmk|]]].
  - split; [rewrite alength_set; exact Hlm|]. split; [rewrite alength_set; exact Hlq|].
    split; [lia|]. rewrite Hsn'. split; [|split].
    + apply (Permutation_NoDup (Permutation_cons_append (qlist q tl) v)).
      constructor; assumption.
    + apply Forall_app. split; [exact Hf | constructor; auto].
    + intros w. rewrite Hmk, Hiff, in_app_iff. simpl. split.
      * intros [-> | H]; [right; left; reflexivity | left; exact H].
      * intros [H | [<- | []]]; [right; exact H | left; reflexivity].
  - intros k Hk. apply aget_set_other. intro E. subst. lia.
Qed.

(* The seeds among the first J edges. *)
Definition seed_upto (d : array int) (J : Z) (v : N) : Prop :=
  exists j, Z.of_N j < J /\ (j < len us)%N /\ lget vs 0%N j = v /\
    exists du, DV d (lget us 0%N j) = Some du /\
      (DV d v = None \/ exists dv, DV d v = Some dv /\ du + lget ws 0 j < dv).

Definition seed_cond (d : array int) (J : Z) : Prop :=
  exists du, DV d (U J) = Some du /\
    (DV d (V J) = None \/ exists dv, DV d (V J) = Some dv /\ du + W J < dv).

Lemma seed_upto_S : forall d J v, 0 <= J < Z.of_N (len us) ->
  seed_upto d (J + 1) v <-> seed_upto d J v \/ (v = V J /\ seed_cond d J).
Proof.
  intros d J v HJ. split.
  - intros (j & Hj & Hjm & Hv & Hc). destruct (Z.eq_dec (Z.of_N j) J) as [E | E].
    + right. subst J. subst v. rewrite V_of. split; [reflexivity|].
      unfold seed_cond. rewrite U_of, V_of, W_of. exact Hc.
    + left. exists j. split; [lia|]. auto.
  - intros [(j & Hj & Hrest) | (-> & Hc)].
    + exists j. split; [lia | exact Hrest].
    + exists (Z.to_N J). split; [lia|]. split; [lia|]. split; [reflexivity|]. exact Hc.
Qed.

Lemma seed_upto_all : forall d v,
  seed_upto d (Z.of_N (len us)) v <-> seed us vs ws (DV d) v.
Proof.
  intros d v. unfold seed_upto, seed. split.
  - intros (j & _ & H). exists j. exact H.
  - intros (j & H). exists j. split; [destruct H; lia | exact H].
Qed.

Lemma seed_test : forall d B (j : int), Sound B d -> 0 <= B <= 10 ^ 11 ->
  (φ j) < Z.of_N (len us) ->
  (negb (d.[idx (U (φ j))] =? INF)%uint63 &&
   ltsb (d.[idx (U (φ j))] + xws.[j])%uint63 d.[idx (V (φ j))])%bool = true <-> seed_cond d (φ j).
Proof.
  intros d B j HS HB Hj. destruct (edge_facts j Hj) as (Eu & Ev & Hu & Hv & Ew & Hw).
  destruct HS as (Hl & Hd). unfold seed_cond.
  destruct (d.[idx (U (φ j))] =? INF)%uint63 eqn:Einf; simpl.
  - split; [discriminate|]. intros (du & Hdu & _).
    rewrite DV_none in Hdu by exact Einf. discriminate.
  - pose proof (DV_eq d _ Hu Einf) as Hdu. destruct (Hd _ _ Hdu) as (_ & Hbu).
    rewrite ltsb_iff, sadd by lia. rewrite Ew.
    destruct (d.[idx (V (φ j))] =? INF)%uint63 eqn:Ev2.
    + rewrite (DV_none d _ Ev2). apply eqb_correct in Ev2. rewrite Ev2, INF_val.
      split; [intros _ | intros _; lia].
      exists (Sint63.to_Z d.[idx (U (φ j))]). split; [exact Hdu | left; reflexivity].
    + rewrite (DV_eq d _ Hv Ev2). split.
      * intros Hlt. eexists; split; [exact Hdu|]. right. eexists; split; [reflexivity | exact Hlt].
      * intros (du & Hdu' & [Hc | (dv & Hdv & Hlt)]); [discriminate|].
        rewrite Hdu in Hdu'. injection Hdu' as <-. injection Hdv as <-. exact Hlt.
Qed.

Lemma seed_spec : forall d B, Sound B d -> 0 <= B <= 10 ^ 11 ->
  forall z j mk q tl H, gap (PArray.length xus) j = z -> (φ j) <= Z.of_N (len us) ->
  QI mk q tl -> (forall v, MK mk v = true <-> seed_upto d (φ j) v) ->
  match seed_loop xus xvs xws d (PArray.length xus) j mk q tl H with
  | (mk', q', tl') =>
      QI mk' q' tl' /\ forall v, MK mk' v = true <-> seed us vs ws (DV d) v
  end.
Proof.
  intros d B HS HB z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j mk q tl H Hz Hj HQ HM. rewrite seed_loop_eq.
  destruct (bdec (j <? PArray.length xus)%uint63) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec, HLu in Hlt'.
    pose proof (to_Z_bounded j) as Bj.
    assert (Hj1 : (φ (j + 1))%uint63 = (φ j) + 1) by sia.
    destruct (edge_facts j Hlt') as (Eu & Ev & Hu & Hv & Ew & Hw).
    cbv zeta. rewrite Eu, Ev.
    pose proof (seed_test d B j HS HB Hlt') as Ht.
    destruct (negb (d.[idx (U (φ j))] =? INF)%uint63 &&
              ltsb (d.[idx (U (φ j))] + xws.[j])%uint63 d.[idx (V (φ j))])%bool eqn:Ec.
    + assert (Hc : seed_cond d (φ j)) by (apply Ht; reflexivity).
      destruct (mk.[idx (V (φ j))] =? 0)%uint63 eqn:Em; cbn [andb].
      * assert (Hmv : MK mk (V (φ j)) = false)
          by (unfold MK; rewrite Em; destruct (V (φ j) <? n)%N; reflexivity).
        destruct (enqueue mk q tl (V (φ j)) HQ Hv Hmv) as (HQ' & _ & Hmk & _).
        apply (IH (gap (PArray.length xus) (j + 1)%uint63));
          [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | lia | exact HQ' |].
        intros w. rewrite Hmk, Hj1, seed_upto_S by lia. rewrite HM. tauto.
      * assert (Hmv : MK mk (V (φ j)) = true).
        { unfold MK. rewrite Em. destruct (N.ltb_spec (V (φ j)) n); [reflexivity | lia]. }
        apply (IH (gap (PArray.length xus) (j + 1)%uint63));
          [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | lia | exact HQ |].
        intros w. rewrite Hj1, seed_upto_S by lia. rewrite <- HM. split; [tauto|].
        intros [A | (-> & _)]; [exact A | exact Hmv].
    + assert (Hc : ~ seed_cond d (φ j)) by (rewrite <- Ht; discriminate).
      cbn [andb].
      apply (IH (gap (PArray.length xus) (j + 1)%uint63));
        [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | lia | exact HQ |].
      intros w. rewrite Hj1, seed_upto_S by lia. rewrite HM. tauto.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, HLu in Hge.
    split; [exact HQ|]. intros v. rewrite HM, <- seed_upto_all.
    replace (φ j) with (Z.of_N (len us)) by lia. reflexivity.
Qed.

(* The forward star. *)
Definition Hprop (hd : array int) (J : Z) : Prop :=
  (φ (PArray.length hd)) = Z.of_N n /\
  forall x, (x < n)%N -> 0 <= (φ (hd.[idx x])) <= J /\
    ((φ (hd.[idx x])) = 0 \/ U ((φ (hd.[idx x])) - 1) = x) /\
    forall k, (φ (hd.[idx x])) <= k < J -> U k <> x.

Definition Nprop (nx : array int) (J : Z) : Prop :=
  (φ (PArray.length nx)) = Z.of_N (len us) /\
  forall j : int, (φ j) < J -> (φ (nx.[j])) <= (φ j) /\
    ((φ (nx.[j])) = 0 \/ U ((φ (nx.[j])) - 1) = U (φ j)) /\
    forall k, (φ (nx.[j])) <= k < (φ j) -> U k <> U (φ j).

Lemma build_spec : forall z j hd nx H, gap (PArray.length xus) j = z ->
  (φ j) <= Z.of_N (len us) -> Hprop hd (φ j) -> Nprop nx (φ j) ->
  match build_loop xus (PArray.length xus) j hd nx H with
  | (hd', nx') => Hprop hd' (Z.of_N (len us)) /\ Nprop nx' (Z.of_N (len us))
  end.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j hd nx H Hz Hj (Hlh & Hh) (Hln & Hnx). rewrite build_loop_eq.
  destruct (bdec (j <? PArray.length xus)%uint63) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec, HLu in Hlt'.
    pose proof (to_Z_bounded j) as Bj.
    assert (Hj1 : (φ (j + 1))%uint63 = (φ j) + 1) by sia.
    destruct (edge_facts j Hlt') as (Eu & _ & Hu & _ & _ & _).
    cbv zeta. rewrite Eu.
    destruct (Hh _ Hu) as (Hh1 & Hh2 & Hh3).
    apply (IH (gap (PArray.length xus) (j + 1)%uint63));
      [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | lia | |].
    + split; [rewrite alength_set; exact Hlh|]. intros x Hx. rewrite Hj1.
      destruct (N.eq_dec x (U (φ j))) as [-> | Hne].
      * rewrite aget_set_same by (rewrite ltb_spec, idx_lt by exact Hu; lia).
        rewrite Hj1. split; [lia|]. split.
        -- right. replace ((φ j) + 1 - 1) with (φ j) by lia. reflexivity.
        -- intros k Hk. lia.
      * rewrite aget_set_other
          by (intro E; apply idx_inj in E; [congruence | |]; rewrite wB_val; lia).
        destruct (Hh _ Hx) as (A1 & A2 & A3). split; [lia|]. split; [exact A2|].
        intros k Hk. destruct (Z.eq_dec k (φ j)) as [-> | Hk'].
        -- intro E. apply Hne. symmetry. exact E.
        -- apply A3. lia.
    + split; [rewrite alength_set; exact Hln|]. intros j' Hj'. rewrite Hj1 in Hj'.
      destruct (Z.eq_dec (φ j') (φ j)) as [E | E].
      * assert (j' = j) by (apply to_Z_inj; exact E). subst j'.
        rewrite aget_set_same by (rewrite ltb_spec, Hln; lia).
        split; [lia|]. split; [exact Hh2 | exact Hh3].
      * rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity).
        apply Hnx. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, HLu in Hge.
    replace (φ j) with (Z.of_N (len us)) in * by lia.
    split; split; assumption.
Qed.

(* The marks reached so far come from a seed. *)
Definition ReachI (d mk : array int) : Prop :=
  forall w, MK mk w = true -> exists v, seed us vs ws (DV d) v /\ reach us vs v w.

Lemma adj_spec : forall d (nx : array int) (x : N),
  Nprop nx (Z.of_N (len us)) -> (x < n)%N ->
  forall z e mk q tl H, (φ e) = z -> (φ e) <= Z.of_N (len us) ->
  ((φ e) = 0 \/ U ((φ e) - 1) = x) -> QI mk q tl -> ReachI d mk -> MK mk x = true ->
  (forall k, (φ e) <= k < Z.of_N (len us) -> U k = x -> MK mk (V k) = true) ->
  match adj_loop xvs nx e mk q tl H with
  | (mk', q', tl') => QI mk' q' tl' /\ ReachI d mk' /\
     (forall k, 0 <= k < Z.of_N (len us) -> U k = x -> MK mk' (V k) = true) /\
     (forall w, MK mk w = true -> MK mk' w = true) /\ (φ tl) <= (φ tl') /\
     (forall k : int, (φ k) < (φ tl) -> q'.[k] = q.[k])
  end.
Proof.
  intros d nx x (Hln & Hnx) Hx z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros e mk q tl H Hz He Hex HQ HR Hmx Htodo. rewrite adj_loop_eq.
  destruct (bdec (0 <? e)%uint63) as [Hpos | Hzero].
  - rewrite ltb_spec in Hpos. change ((φ 0)%uint63) with 0 in Hpos.
    pose proof (to_Z_bounded e) as Be.
    assert (Hj : (φ (e - 1))%uint63 = (φ e) - 1) by sia.
    assert (Hjm : (φ (e - 1))%uint63 < Z.of_N (len us)) by lia.
    destruct (edge_facts _ Hjm) as (_ & Ev & _ & Hv & _ & _).
    destruct (Hnx _ Hjm) as (N1 & N2 & N3).
    assert (Hux : U (φ (e - 1))%uint63 = x)
      by (destruct Hex as [E | E]; [lia | rewrite Hj; exact E]).
    cbv zeta. rewrite Ev.
    destruct (bdec (nx.[(e - 1)%uint63] <? e)%uint63) as [Hd | Hd].
    2: { exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hd. lia. }
    pose proof (to_Z_bounded (nx.[(e - 1)%uint63])) as Be'.
    assert (Hex' : (φ (nx.[(e - 1)%uint63])) = 0 \/ U ((φ (nx.[(e - 1)%uint63])) - 1) = x)
      by (rewrite <- Hux; exact N2).
    assert (Hrv : forall v0, reach us vs v0 x ->
              reach us vs v0 (V (φ (e - 1))%uint63)).
    { intros v0 (es & Hp). exists (es ++ [Z.to_N (φ (e - 1))%uint63]).
      apply ok_path_app. exists x. split; [exact Hp|]. simpl.
      split; [lia|]. split; [exact Hux | reflexivity]. }
    destruct (mk.[idx (V (φ (e - 1))%uint63)] =? 0)%uint63 eqn:Em.
    + assert (Hmv : MK mk (V (φ (e - 1))%uint63) = false)
        by (unfold MK; rewrite Em; destruct (V (φ (e - 1))%uint63 <? n)%N; reflexivity).
      destruct (enqueue mk q tl _ HQ Hv Hmv) as (HQ' & Htl1 & Hmk & Hpre).
      generalize (IH (φ (nx.[(e - 1)%uint63])) ltac:(unfold Zwf; lia)
        (nx.[(e - 1)%uint63]) _ _ _ (Acc_inv H (dec_lt _ e Hd)) eq_refl ltac:(lia)
        Hex' HQ').
      destruct (adj_loop xvs nx nx.[(e - 1)%uint63] _ _ _ (Acc_inv H (dec_lt _ e Hd)))
        as [[mk' q'] tl'].
      intros X. destruct X as (Q' & R' & T' & M' & L' & P').
      * intros w Hw. apply Hmk in Hw as [-> | Hw].
        -- destruct (HR x Hmx) as (v0 & Hs & Hr). exists v0. split; [exact Hs|].
           apply Hrv. exact Hr.
        -- apply HR. exact Hw.
      * apply Hmk. right. exact Hmx.
      * intros k Hk Huk. apply Hmk.
        destruct (Z_lt_le_dec k ((φ e) - 1)) as [Hk1 | Hk1].
        -- exfalso. apply (N3 k); [lia | rewrite Hux; exact Huk].
        -- destruct (Z.eq_dec k ((φ e) - 1)) as [Hk2 | Hk2].
           ++ left. rewrite Hk2, <- Hj. reflexivity.
           ++ right. apply Htodo; [lia | exact Huk].
      * split; [exact Q'|]. split; [exact R'|]. split; [exact T'|].
        split; [intros w Hw; apply M'; apply Hmk; right; exact Hw|].
        split; [lia|].
        intros k Hk. rewrite P' by lia. apply Hpre. exact Hk.
    + assert (Hmv : MK mk (V (φ (e - 1))%uint63) = true).
      { unfold MK. rewrite Em. destruct (N.ltb_spec (V (φ (e - 1))%uint63) n); [reflexivity | lia]. }
      generalize (IH (φ (nx.[(e - 1)%uint63])) ltac:(unfold Zwf; lia)
        (nx.[(e - 1)%uint63]) mk q tl (Acc_inv H (dec_lt _ e Hd)) eq_refl ltac:(lia)
        Hex' HQ HR Hmx).
      destruct (adj_loop xvs nx nx.[(e - 1)%uint63] mk q tl (Acc_inv H (dec_lt _ e Hd)))
        as [[mk' q'] tl'].
      intros X. destruct X as (Q' & R' & T' & M' & L' & P').
      * intros k Hk Huk.
        destruct (Z_lt_le_dec k ((φ e) - 1)) as [Hk1 | Hk1].
        -- exfalso. apply (N3 k); [lia | rewrite Hux; exact Huk].
        -- destruct (Z.eq_dec k ((φ e) - 1)) as [Hk2 | Hk2].
           ++ rewrite Hk2, <- Hj. exact Hmv.
           ++ apply Htodo; [lia | exact Huk].
      * auto 10.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hzero. change ((φ 0)%uint63) with 0 in Hzero.
    split; [exact HQ|]. split; [exact HR|]. split; [|split; [auto | split; [lia | auto]]].
    intros k Hk Huk. apply Htodo; [lia | exact Huk].
Qed.

Definition Closed (mk q : array int) (h : Z) : Prop :=
  forall k : int, (φ k) < h -> forall i, 0 <= i < Z.of_N (len us) ->
    U i = Z.to_N (φ (q.[k])) -> MK mk (V i) = true.

Lemma In_qlist : forall q tl v, In v (qlist q tl) ->
  exists k : int, (φ k) < (φ tl) /\ v = Z.to_N (φ (q.[k])).
Proof.
  intros q tl v Hv. unfold qlist in Hv. apply in_map_iff in Hv as (k & <- & Hk).
  apply in_seq in Hk. pose proof (to_Z_bounded tl).
  exists (of_Z (Z.of_nat k)). split; [|reflexivity].
  rewrite of_Z_spec, Z.mod_small by lia. lia.
Qed.

Lemma bfs_spec : forall d hd nx,
  Hprop hd (Z.of_N (len us)) -> Nprop nx (Z.of_N (len us)) ->
  forall z h mk q tl H, gap xn h = z -> (φ h) <= (φ tl) -> QI mk q tl -> ReachI d mk ->
  (forall v, seed us vs ws (DV d) v -> MK mk v = true) -> Closed mk q (φ h) ->
  forall t, MK (bfs_loop xvs hd nx xn h mk q tl H) t = true <->
            exists v, seed us vs ws (DV d) v /\ reach us vs v t.
Proof.
  intros d hd nx (Hlh & Hh) HN z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros h mk q tl H Hz Hht HQ HR HSd HCl. rewrite bfs_loop_eq.
  pose proof HQ as (Hlm & Hlq & Htl & Hnd & Hf & Hiff).
  pose proof (to_Z_bounded h) as Bh.
  destruct (bdec (h <? tl)%uint63) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    destruct (bdec (h <? xn)%uint63) as [Hhn | Hhn].
    2: { exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec, Hxn in Hhn. lia. }
    assert (Hh1 : (φ (h + 1))%uint63 = (φ h) + 1) by sia.
    cbv zeta.
    assert (Hin : In (Z.to_N (φ (q.[h]))) (qlist q tl)).
    { unfold qlist. apply in_map_iff. exists (Z.to_nat (φ h)).
      split; [rewrite Z2Nat.id, of_to_Z by lia; reflexivity | apply in_seq; lia]. }
    assert (Hmx : MK mk (Z.to_N (φ (q.[h]))) = true) by (apply Hiff; exact Hin).
    assert (Hxn' : (Z.to_N (φ (q.[h])) < n)%N)
      by (rewrite Forall_forall in Hf; apply Hf; exact Hin).
    destruct (Hh _ Hxn') as (A1 & A2 & A3). rewrite idx_of in A1, A2, A3.
    generalize (adj_spec d nx _ HN Hxn' _ (hd.[q.[h]]) mk q tl
                  (Zwf_well_founded 0 (φ (hd.[q.[h]]))) eq_refl ltac:(lia) A2 HQ HR Hmx).
    destruct (adj_loop xvs nx hd.[q.[h]] mk q tl (Zwf_well_founded 0 (φ (hd.[q.[h]]))))
      as [[mk' q'] tl'].
    intros X. destruct X as (Q' & R' & T' & M' & L' & P').
    { intros k Hk Huk. exfalso. apply (A3 k); [lia | exact Huk]. }
    apply (IH (gap xn (h + 1)%uint63));
      [rewrite <- Hz; apply dec_step; exact Hhn | reflexivity | lia | exact Q' | exact R'
      | intros v Hv; apply M'; apply HSd; exact Hv |].
    intros k Hk i Hi Hu. rewrite Hh1 in Hk.
    destruct (Z.eq_dec (φ k) (φ h)) as [E | E].
    + assert (k = h) by (apply to_Z_inj; exact E). subst k.
      rewrite P' in Hu by lia. apply T'; [exact Hi | exact Hu].
    + rewrite P' in Hu by lia. apply M'. apply (HCl k); [lia | exact Hi | exact Hu].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
    intros t. split; [apply HR|].
    intros (v & Hs & es & Hp). pose proof (HSd v Hs) as Hmv. clear Hs.
    revert v Hp Hmv. induction es as [| j es IHes]; simpl; intros v Hp Hmv.
    + subst. exact Hmv.
    + destruct Hp as (Hj & Hu & Hp). apply (IHes _ Hp).
      apply Hiff in Hmv. apply In_qlist in Hmv as (k & Hk & Ek).
      rewrite <- V_of. apply (HCl k); [lia | lia | rewrite U_of, Hu; exact Ek].
Qed.

Lemma ans_spec : forall (d mk qa : array int) (Q : int) z i (out : array (answer int)) H,
  gap Q i = z -> (φ i) <= (φ Q) -> (φ (PArray.length out)) = (φ Q) ->
  (forall k, (φ k) < (φ i) -> out.[k] = answer_of d mk qa.[k]) ->
  (φ (PArray.length (ans_loop d mk qa Q i out H))) = (φ Q) /\
  forall k, (φ k) < (φ Q) -> (ans_loop d mk qa Q i out H).[k] = answer_of d mk qa.[k].
Proof.
  intros d mk qa Q z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i out H Hz Hi Hl Hc. rewrite ans_loop_eq.
  destruct (bdec (i <? Q)%uint63) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    pose proof (to_Z_bounded i) as Bi.
    assert (Hi1 : (φ (i + 1))%uint63 = (φ i) + 1) by sia.
    cbv zeta.
    apply (IH (gap Q (i + 1)%uint63));
      [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | lia
      | rewrite blength_set; exact Hl |].
    intros k Hk. rewrite Hi1 in Hk.
    destruct (Z.eq_dec (φ k) (φ i)) as [E | E].
    + assert (k = i) by (apply to_Z_inj; exact E). subst k.
      apply bget_set_same. rewrite ltb_spec. lia.
    + rewrite bget_set_other by (intro F; apply E; rewrite F; reflexivity).
      apply Hc. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
    split; [exact Hl|]. intros k Hk. apply Hc. lia.
Qed.

Lemma blength_make : forall (k : int) (b : answer int), (φ k) <= 4194303 ->
  PArray.length (PArray.make k b) = k.
Proof. intros k b H. exact (alength_make (answer int) k b H). Qed.

Lemma ans_repr : forall d mk t, (t < n)%N ->
  repr (answer_of d mk (idx t) : answer sint) (ans_math (DV d) (MK mk) t).
Proof.
  intros d mk t Ht. unfold answer_of, ans_math, DV, MK.
  destruct (N.ltb_spec t n); [|lia].
  destruct (d.[idx t] =? INF)%uint63; [exact I|].
  destruct (mk.[idx t] =? 0)%uint63; cbn [andb negb]; [reflexivity | exact I].
Qed.

Lemma main_correct : forall (qs : list N) (xqs : array uint),
  Forall (fun t => (t < n)%N) qs -> repr xqs qs ->
  exists o : list (answer Z),
    repr (shortestpath3_impl xn xs xus xvs xws xqs : array (answer sint)) o /\
    shortestpath3_spec n s us vs ws qs o.
Proof.
  intros qs xqs Hqr Hq.
  pose proof (repr_len _ _ xqs qs Hq) as HLq.
  pose proof init_spec as (S0 & C0).
  assert (HR : (φ (xn - 1))%uint63 = Z.of_N n - 1) by sia.
  destruct (rounds_spec (xn - 1)%uint63 HR _ 0%uint63 _
              (Zwf_well_founded 0 (gap (xn - 1) 0)) eq_refl ltac:(change ((φ 0)%uint63) with 0; lia)
              ltac:(change ((φ 0)%uint63) with 0; rewrite Z.mul_0_r; exact S0) C0)
    as (S1 & C1).
  set (d := rounds_loop xus xvs xws (PArray.length xus) (xn - 1) 0
              ((PArray.make xn INF).[xs <- 0%uint63])
              (Zwf_well_founded 0 (gap (xn - 1) 0))) in *.
  assert (HBf : 0 <= 2000 * Z.of_N (len us) * (Z.of_N n - 1) <= 10 ^ 11) by nia.
  assert (Hlmk : (φ (PArray.length (PArray.make xn 0%uint63))) = Z.of_N n)
    by (rewrite alength_make_int by lia; exact Hxn).
  assert (HQ0 : QI (PArray.make xn 0%uint63) (PArray.make xn 0%uint63) 0%uint63).
  { assert (Eq0 : qlist (PArray.make xn 0%uint63) 0%uint63 = []) by reflexivity.
    split; [exact Hlmk|]. split; [exact Hlmk|]. change ((φ 0)%uint63) with 0.
    split; [lia|]. rewrite Eq0. split; [constructor|]. split; [constructor|].
    intros v. unfold MK. rewrite aget_make. simpl. rewrite Bool.andb_false_r.
    split; [discriminate | intros []]. }
  generalize (seed_spec d _ S1 HBf _ 0%uint63 (PArray.make xn 0%uint63) (PArray.make xn 0%uint63)
                0%uint63 (Zwf_well_founded 0 (gap (PArray.length xus) 0)) eq_refl
                ltac:(change ((φ 0)%uint63) with 0; lia) HQ0).
  unfold shortestpath3_impl. cbv zeta. fold d.
  destruct (seed_loop xus xvs xws d (PArray.length xus) 0 (PArray.make xn 0%uint63)
              (PArray.make xn 0%uint63) 0 (Zwf_well_founded 0 (gap (PArray.length xus) 0)))
    as [[mk q] tl].
  intros X. destruct X as (HQ & HMs).
  { intros v. unfold MK. rewrite aget_make. simpl. rewrite Bool.andb_false_r.
    split; [discriminate|]. intros (j & Hj & _). change ((φ 0)%uint63) with 0 in Hj. lia. }
  assert (Hp0 : Hprop (PArray.make xn 0%uint63) (φ 0)%uint63).
  { split; [exact Hlmk|]. intros x Hx. rewrite aget_make. change ((φ 0)%uint63) with 0.
    split; [lia|]. split; [left; reflexivity | intros k Hk; lia]. }
  assert (Np0 : Nprop (PArray.make (PArray.length xus) 0%uint63) (φ 0)%uint63).
  { split; [rewrite alength_make_int by lia; exact HLu|].
    intros j Hj. change ((φ 0)%uint63) with 0 in Hj. pose proof (to_Z_bounded j). lia. }
  generalize (build_spec _ 0%uint63 (PArray.make xn 0%uint63)
                (PArray.make (PArray.length xus) 0%uint63)
                (Zwf_well_founded 0 (gap (PArray.length xus) 0)) eq_refl
                ltac:(change ((φ 0)%uint63) with 0; lia) Hp0 Np0).
  destruct (build_loop xus (PArray.length xus) 0 (PArray.make xn 0%uint63)
              (PArray.make (PArray.length xus) 0%uint63)
              (Zwf_well_founded 0 (gap (PArray.length xus) 0)))
    as [hd nx].
  intros (HH & HN).
  assert (HMf : forall t, MK (bfs_loop xvs hd nx xn 0 mk q tl (Zwf_well_founded 0 (gap xn 0))) t = true
                <-> exists v, seed us vs ws (DV d) v /\ reach us vs v t).
  { apply (bfs_spec d hd nx HH HN _ 0%uint63 mk q tl _ eq_refl).
    - change ((φ 0)%uint63) with 0. pose proof (to_Z_bounded tl). lia.
    - exact HQ.
    - intros w Hw. exists w. split; [apply HMs; exact Hw | exists []; reflexivity].
    - intros v Hv. apply HMs. exact Hv.
    - intros k Hk. change ((φ 0)%uint63) with 0 in Hk. pose proof (to_Z_bounded k). lia. }
  set (mkf := bfs_loop xvs hd nx xn 0 mk q tl (Zwf_well_founded 0 (gap xn 0))) in *.
  pose proof (alength_bound _ xqs) as Bq.
  destruct (ans_spec d mkf xqs (PArray.length xqs) _ 0%uint63
              (PArray.make (PArray.length xqs) Impossible)
              (Zwf_well_founded 0 (gap (PArray.length xqs) 0)) eq_refl
              ltac:(change ((φ 0)%uint63) with 0; lia)
              ltac:(rewrite blength_make by lia; reflexivity)
              ltac:(intros k Hk; change ((φ 0)%uint63) with 0 in Hk;
                    pose proof (to_Z_bounded k); lia))
    as (Lo & Co).
  set (out := ans_loop d mkf xqs (PArray.length xqs) 0
                (PArray.make (PArray.length xqs) Impossible)
                (Zwf_well_founded 0 (gap (PArray.length xqs) 0))) in *.
  exists (map (ans_math (DV d) (MK mkf)) qs).
  assert (Hcell : forall k : nat, (k < List.length qs)%nat ->
            out.[of_Z (Z.of_nat k)] = answer_of d mkf (idx (nth k qs 0%N)) /\
            (nth k qs 0%N < n)%N).
  { intros k Hk.
    assert (Hk' : (φ (of_Z (Z.of_nat k))) = Z.of_nat k)
      by (rewrite of_Z_spec, Z.mod_small; [reflexivity | rewrite wB_val; unfold len in HLq; lia]).
    split.
    - rewrite Co by (rewrite Hk'; unfold len in HLq; lia). f_equal.
      assert (E2 : (φ (@PArray.get int xqs (of_Z (Z.of_nat k)))) = Z.of_N (nth k qs 0%N)).
      { pose proof (repr_get_uint xqs qs Hq (of_Z (Z.of_nat k)) ltac:(rewrite Hk'; unfold len; lia))
          as E.
        rewrite Hk' in E. unfold Prelude.get in E.
        replace (N.to_nat (Z.to_N (Z.of_nat k))) with k in E by lia. exact E. }
      apply to_Z_inj. etransitivity; [exact E2|]. rewrite idx_lt; [reflexivity|].
      rewrite Forall_forall in Hqr. apply Hqr. apply nth_In. exact Hk.
    - rewrite Forall_forall in Hqr. apply Hqr. apply nth_In. exact Hk. }
  split.
  - split.
    + rewrite length_map.
      assert (E : Z.of_nat (List.length qs) = (φ (PArray.length out)))
        by (rewrite Lo, HLq; unfold len; lia).
      exact E.
    + intros k Hk. rewrite length_map in Hk.
      exists (ans_math (DV d) (MK mkf) (nth k qs 0%N)). split.
      * rewrite nth_error_map, (nth_error_nth' qs 0%N Hk). reflexivity.
      * destruct (Hcell k Hk) as (E & Ht).
        pose proof (ans_repr d mkf _ Ht) as R. rewrite <- E in R. exact R.
  - split.
    + unfold len. rewrite length_map. reflexivity.
    + intros i Hi. unfold Prelude.get at 1 2 3 4.
      unfold len in Hi.
      rewrite (nth_indep (map (ans_math (DV d) (MK mkf)) qs) (n := N.to_nat i) Impossible (ans_math (DV d) (MK mkf) 0%N))
        by (rewrite length_map; lia).
      rewrite map_nth.
      apply (ans_correct us vs ws n s Hlv Hlw Hvr Hwr Hsn (DV d) (MK mkf)).
      * intros t x Hx. destruct S1 as (_ & S1). apply (S1 t x Hx).
      * intros es t Hp Hl. apply C1; [exact Hp | lia].
      * exact HMf.
Qed.

End Machine.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma shortestpath3_impl_correct :
  forall (n s : N) (us vs : list N) (ws : list Z) (qs : list N)
         (xn xs : uint) (xus xvs : array uint) (xws : array sint)
         (xqs : array uint),
  valid_input n s us vs ws qs ->
  repr xn n -> repr xs s -> repr xus us -> repr xvs vs -> repr xws ws ->
  repr xqs qs ->
  exists o : list (answer Z),
    repr (shortestpath3_impl xn xs xus xvs xws xqs : array (answer sint)) o /\
    shortestpath3_spec n s us vs ws qs o.
Proof.
  intros n s us vs ws qs xn xs xus xvs xws xqs Hv Hrn Hrs Hrus Hrvs Hrws Hrqs.
  destruct Hv as [Hn Hm Hlv Hlw Hq Hsn Hur Hvr Hqr Hw].
  assert (Hxn : (φ xn) = Z.of_N n).
  { unfold repr, repr_uint in Hrn. rewrite <- Hrn, Z2N.id; [reflexivity|].
    pose proof (to_Z_bounded xn). lia. }
  assert (Hxs : (φ xs) = Z.of_N s).
  { unfold repr, repr_uint in Hrs. rewrite <- Hrs, Z2N.id; [reflexivity|].
    pose proof (to_Z_bounded xs). lia. }
  pose proof (repr_len _ _ xus us Hrus) as HLu.
  assert (Hus : forall i : int, ((φ i) < Z.of_N (len us))%Z ->
            (φ (xus.[i])) = Z.of_N (lget us 0%N (Z.to_N (φ i))))
    by (intros i Hi; apply (repr_get_uint xus us Hrus); exact Hi).
  assert (Hvs : forall i : int, ((φ i) < Z.of_N (len us))%Z ->
            (φ (xvs.[i])) = Z.of_N (lget vs 0%N (Z.to_N (φ i))))
    by (intros i Hi; apply (repr_get_uint xvs vs Hrvs); rewrite Hlv; exact Hi).
  assert (Hws : forall i : int, ((φ i) < Z.of_N (len us))%Z ->
            Sint63.to_Z (xws.[i]) = lget ws 0%Z (Z.to_N (φ i)))
    by (intros i Hi; apply (repr_get_sint xws ws Hrws); rewrite Hlw; exact Hi).
  eapply main_correct; eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition shortestpath3 :
  uint -> uint -> array uint -> array uint -> array sint -> array uint ->
  array (answer sint) := shortestpath3_impl.

Definition shortestpath3_correct :
  forall (n s : N) (us vs : list N) (ws : list Z) (qs : list N)
         (xn xs : uint) (xus xvs : array uint) (xws : array sint)
         (xqs : array uint),
  valid_input n s us vs ws qs ->
  repr xn n -> repr xs s -> repr xus us -> repr xvs vs -> repr xws ws ->
  repr xqs qs ->
  exists o : list (answer Z),
    repr (shortestpath3 xn xs xus xvs xws xqs) o /\
    shortestpath3_spec n s us vs ws qs o
  := shortestpath3_impl_correct.
