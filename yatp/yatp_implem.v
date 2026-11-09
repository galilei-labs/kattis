(* Executable implementation and its required termination dependencies.
   Correctness proofs are in yatp_proofs.v. *)
(* Implementation of yatp (yatp.spec): centroid decomposition, a Li Chao
   tree per component (lines y = p_v * x + dist(c, v), queried at x = p_u).

   Code.  CSR adjacency built from the half-edges (counting sort); then the
   nodes r = 1..n in turn: while r is alive, a BFS from r over the alive
   nodes gives its component, subtree sizes along the BFS order give the
   centroid c, a BFS from c gives the distances d (with a consistency flag;
   a relaxation loop, never run on a tree, repairs d otherwise), the lines
   (p_v, d_v) of the component go into a Li Chao tree on the abscissae
   0..max p (stamped per round, never cleared), and every node u of the
   component takes best[u] := min(best[u], d_u + query(p_u)); c is removed.
   The answer is the sum of best[1..n].  Every loop is a Fixpoint on an
   erased Acc (Zwf 0) argument; no nat, N or Z in the extracted code.

   Proof.  Graph side over arbitrary walks (no acyclicity needed):
   invariant MI of the main loop -- best[u] is at most the cost of every
   walk from u that touches a removed node, and at least the cost of some
   walk from u; at the end every node is removed and shortcut turns the
   witness walk into a simple path.  See README.md, "Implementation". *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Bool.
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

Lemma dec_down : forall i : int,
  (0 <? i) = true -> Zwf 0 (φ (i - 1)) (φ i).
Proof. intros i H. rewrite ltb_spec in H. unfold Zwf. sia. Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Definition INF : int := 4611686018427387904.

(* the largest cell of a.[i..n-1], or acc *)
Fixpoint max_loop (a : array int) (n i acc : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : int :=
  match bdec (i <? n) with
  | left Hi =>
      max_loop a n (i + 1) (if acc <? a.[i] then a.[i] else acc)
        (Acc_inv H (dec_step n i Hi))
  | right _ => acc
  end.

(* cells 1 .. n1-1 set to true *)
Fixpoint true_loop (n1 i : int) (a : array bool)
    (H : Acc (Zwf 0) (gap n1 i)) {struct H} : array bool :=
  match bdec (i <? n1) with
  | left Hi => true_loop n1 (i + 1) a.[i <- true] (Acc_inv H (dec_step n1 i Hi))
  | right _ => a
  end.

(* half-edge h: edge h/2, from eu to ev when h is even, back otherwise *)
Definition hsrc (xu xv : array int) (h : int) : int :=
  if h mod 2 =? 0 then xu.[h / 2] else xv.[h / 2].
Definition hdst (xu xv : array int) (h : int) : int :=
  if h mod 2 =? 0 then xv.[h / 2] else xu.[h / 2].

(* the degree count *)
Fixpoint deg_loop (xu xv : array int) (hh h : int) (deg : array int)
    (H : Acc (Zwf 0) (gap hh h)) {struct H} : array int :=
  match bdec (h <? hh) with
  | left Hh =>
      let x := hsrc xu xv h in
      deg_loop xu xv hh (h + 1) deg.[x <- deg.[x] + 1]
        (Acc_inv H (dec_step hh h Hh))
  | right _ => deg
  end.

(* the prefix sums: sa.[x+1] = sa.[x] + deg.[x], and a copy into pos *)
Fixpoint start_loop (deg : array int) (n1 x : int) (sa pos : array int)
    (H : Acc (Zwf 0) (gap n1 x)) {struct H} : array int * array int :=
  match bdec (x <? n1) with
  | left Hx =>
      let s := sa.[x] in
      start_loop deg n1 (x + 1) sa.[x + 1 <- s + deg.[x]] pos.[x <- s]
        (Acc_inv H (dec_step n1 x Hx))
  | right _ => (sa, pos)
  end.

(* the CSR fill *)
Fixpoint fill_loop (xu xv xw : array int) (hh h : int) (pos nbr wt : array int)
    (H : Acc (Zwf 0) (gap hh h)) {struct H} : array int * array int :=
  match bdec (h <? hh) with
  | left Hh =>
      let x := hsrc xu xv h in
      let i := pos.[x] in
      fill_loop xu xv xw hh (h + 1) pos.[x <- i + 1]
        nbr.[i <- hdst xu xv h] wt.[i <- xw.[h / 2]]
        (Acc_inv H (dec_step hh h Hh))
  | right _ => (nbr, wt)
  end.

(* The breadth-first traversal of the alive nodes from a root.  The state:
   the stamps, the queue (the visited nodes in order), the BFS parent, the
   distance along the BFS tree, the queue's tail and the consistency flag
   (every scanned edge to an alive node y satisfies d.[y] <= d.[x] + w). *)
Record bst := mkB {
  b_vis : array int; b_comp : array int; b_par : array int; b_d : array int;
  b_tail : int; b_flag : bool }.

Definition scan_step (alive : array bool) (s x dx y w : int) (b : bst) : bst :=
  if alive.[y] then
    if (b_vis b).[y] =? s then
      mkB (b_vis b) (b_comp b) (b_par b) (b_d b) (b_tail b)
          (b_flag b && ((b_d b).[y] <=? dx + w))
    else
      mkB (b_vis b).[y <- s] (b_comp b).[b_tail b <- y] (b_par b).[y <- x]
          (b_d b).[y <- dx + w] (b_tail b + 1) (b_flag b)
  else b.

Fixpoint scan_loop (nbr wt : array int) (alive : array bool) (s x dx e j : int)
    (b : bst) (H : Acc (Zwf 0) (gap e j)) {struct H} : bst :=
  match bdec (j <? e) with
  | left Hj =>
      scan_loop nbr wt alive s x dx e (j + 1)
        (scan_step alive s x dx nbr.[j] wt.[j] b)
        (Acc_inv H (dec_step e j Hj))
  | right _ => b
  end.

Fixpoint bfs_loop (sa nbr wt : array int) (alive : array bool) (s L head : int)
    (b : bst) (H : Acc (Zwf 0) (gap L head)) {struct H} : bst :=
  match bdec (head <? b_tail b) with
  | left _ =>
      match bdec (head <? L) with
      | left Hh =>
          let x := (b_comp b).[head] in
          bfs_loop sa nbr wt alive s L (head + 1)
            (scan_loop nbr wt alive s x (b_d b).[x] sa.[x + 1] sa.[x] b
               (Zwf_well_founded 0 (gap sa.[x + 1] sa.[x])))
            (Acc_inv H (dec_step L head Hh))
      | right _ => b
      end
  | right _ => b
  end.

Definition bfs_init (s root : int) (vis comp par d : array int) : bst :=
  mkB vis.[root <- s] comp.[0 <- root] par.[root <- root] d.[root <- 0] 1 true.

Definition bfs (sa nbr wt : array int) (alive : array bool) (s root : int)
    (vis comp par d : array int) : bst :=
  bfs_loop sa nbr wt alive s (PArray.length comp) 0
    (bfs_init s root vis comp par d)
    (Zwf_well_founded 0 (gap (PArray.length comp) 0)).

(* The relaxation fallback (never changes anything on a tree). *)
Fixpoint rscan (nbr wt : array int) (alive : array bool) (dx e j : int)
    (d : array int) (ch : bool) (H : Acc (Zwf 0) (gap e j)) {struct H}
    : array int * bool :=
  match bdec (j <? e) with
  | left Hj =>
      let y := nbr.[j] in
      let nv := dx + wt.[j] in
      if alive.[y] && (y <? PArray.length d) && (nv <? d.[y]) then
        rscan nbr wt alive dx e (j + 1) d.[y <- nv] true (Acc_inv H (dec_step e j Hj))
      else
        rscan nbr wt alive dx e (j + 1) d ch (Acc_inv H (dec_step e j Hj))
  | right _ => (d, ch)
  end.

Fixpoint rpass (sa nbr wt : array int) (alive : array bool) (comp : array int)
    (t i : int) (d : array int) (ch : bool) (H : Acc (Zwf 0) (gap t i)) {struct H}
    : array int * bool :=
  match bdec (i <? t) with
  | left Hi =>
      let x := comp.[i] in
      let r := rscan nbr wt alive d.[x] sa.[x + 1] sa.[x] d ch
                 (Zwf_well_founded 0 (gap sa.[x + 1] sa.[x])) in
      rpass sa nbr wt alive comp t (i + 1) (fst r) (snd r) (Acc_inv H (dec_step t i Hi))
  | right _ => (d, ch)
  end.

Fixpoint zsum (f : nat -> Z) (k : nat) : Z :=
  match k with
  | O => 0%Z
  | S k' => (zsum f k' + f k')%Z
  end.

Definition dsum (d : array int) : Z :=
  zsum (fun i => (φ (d.[of_Z (Z.of_nat i)]))) (Z.to_nat (φ (PArray.length d))).

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

Lemma blength_set : forall (t : array bool) (i : int) (b : bool),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set bool t i b). Qed.

Lemma bget_set_same : forall (t : array bool) (i : int) (b : bool),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same bool t i b H). Qed.

Lemma bget_set_other : forall (t : array bool) (i j : int) (b : bool),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other bool t i j b H). Qed.

Lemma aget_set : forall (t : array int) (i j : int) (b : int),
  (i <? PArray.length t) = true ->
  t.[i <- b].[j] = if i =? j then b else t.[j].
Proof.
  intros t i j b H. destruct (i =? j) eqn:E.
  - rewrite Uint63.eqb_spec in E. subst. apply aget_set_same; auto.
  - rewrite eqb_false_spec in E. apply aget_set_other; auto.
Qed.

Lemma bget_set : forall (t : array bool) (i j : int) (b : bool),
  (i <? PArray.length t) = true ->
  t.[i <- b].[j] = if i =? j then b else t.[j].
Proof.
  intros t i j b H. destruct (i =? j) eqn:E.
  - rewrite Uint63.eqb_spec in E. subst. apply bget_set_same; auto.
  - rewrite eqb_false_spec in E. apply bget_set_other; auto.
Qed.

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma blength_bound : forall (t : array bool), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length bool t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma ltb_true : forall a b : int, (a <? b) = true <-> ((φ a) < (φ b))%Z.
Proof. intros. apply ltb_spec. Qed.
Lemma eqb_true : forall a b : int, (a =? b) = true <-> a = b.
Proof. intros. apply Uint63.eqb_spec. Qed.
Lemma eqb_false : forall a b : int, (a =? b) = false <-> a <> b.
Proof. intros. apply eqb_false_spec. Qed.

(* ------------------------------------------------------------------ *)
(* zsum                                                                *)
(* ------------------------------------------------------------------ *)

Lemma zsum_le : forall f g K, (forall i, (i < K)%nat -> (f i <= g i)%Z) ->
  (zsum f K <= zsum g K)%Z.
Proof.
  intros f g K. induction K; intros H; simpl; [lia|].
  pose proof (H K ltac:(lia)). pose proof (IHK ltac:(intros; apply H; lia)). lia.
Qed.

Lemma zsum_lt : forall f g K, (forall i, (i < K)%nat -> (f i <= g i)%Z) ->
  (exists i, (i < K)%nat /\ (f i < g i)%Z) ->
  (zsum f K < zsum g K)%Z.
Proof.
  intros f g K. induction K; intros H [i [Hi Hlt]]; [lia|]. simpl.
  destruct (Nat.eq_dec i K).
  - subst. pose proof (zsum_le f g K ltac:(intros; apply H; lia)). lia.
  - pose proof (H K ltac:(lia)).
    pose proof (IHK ltac:(intros; apply H; lia) ltac:(exists i; split; [lia|auto])). lia.
Qed.

Lemma zsum_nonneg : forall f K, (forall i, (i < K)%nat -> (0 <= f i)%Z) ->
  (0 <= zsum f K)%Z.
Proof.
  intros f K. induction K; intros H; simpl; [lia|].
  pose proof (H K ltac:(lia)). pose proof (IHK ltac:(intros; apply H; lia)). lia.
Qed.

Lemma of_Z_nat_phi : forall i : nat, (Z.of_nat i < wB)%Z -> (φ (of_Z (Z.of_nat i))) = Z.of_nat i.
Proof. intros i H. rewrite of_Z_spec. apply Z.mod_small. lia. Qed.

Lemma dsum_nonneg : forall d, (0 <= dsum d)%Z.
Proof.
  intros d. unfold dsum. apply zsum_nonneg. intros i _. pose proof (to_Z_bounded (d.[of_Z (Z.of_nat i)])). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The relaxation pass                                                 *)
(* ------------------------------------------------------------------ *)

Definition dle (d' d : array int) : Prop :=
  PArray.length d' = PArray.length d /\
  forall i, ((φ i) < (φ (PArray.length d)))%Z -> ((φ (d'.[i])) <= (φ (d.[i])))%Z.

Definition dlt (d' d : array int) : Prop :=
  exists i, ((φ i) < (φ (PArray.length d)))%Z /\ ((φ (d'.[i])) < (φ (d.[i])))%Z.

Lemma dle_refl : forall d, dle d d.
Proof. intros d. split; [reflexivity|]. intros; lia. Qed.

Lemma dle_trans : forall a b c, dle a b -> dle b c -> dle a c.
Proof.
  intros a b c [L1 H1] [L2 H2]. split; [congruence|].
  intros i Hi. pose proof (H2 i Hi). rewrite <- L2 in Hi. pose proof (H1 i Hi). lia.
Qed.

Lemma dlt_trans_l : forall a b c, dle a b -> dle b c -> dlt b c -> dlt a c.
Proof.
  intros a b c [L1 H1] [L2 H2] [i [Hi Hl]]. exists i. split; auto.
  rewrite <- L2 in Hi. pose proof (H1 i Hi). lia.
Qed.

Lemma dlt_trans_r : forall a b c, dle a b -> dle b c -> dlt a b -> dlt a c.
Proof.
  intros a b c [L1 H1] [L2 H2] [i [Hi Hl]]. exists i. split; [congruence|].
  rewrite L2 in Hi. pose proof (H2 i Hi). lia.
Qed.

Lemma dle_set : forall d y v, ((φ y) < (φ (PArray.length d)))%Z -> ((φ v) < (φ (d.[y])))%Z ->
  dle d.[y <- v] d /\ dlt d.[y <- v] d.
Proof.
  intros d y v Hy Hv. assert (Hyb : (y <? PArray.length d) = true) by (apply ltb_true; auto).
  split.
  - split; [apply alength_set|]. intros i Hi. rewrite aget_set by auto.
    destruct (y =? i) eqn:E; [apply eqb_true in E; subst; lia | lia].
  - exists y. split; auto. rewrite aget_set_same by auto. lia.
Qed.

Lemma rscan_eq : forall nbr wt alive dx e j d ch H,
  rscan nbr wt alive dx e j d ch H =
  match bdec (j <? e) with
  | left Hj =>
      let y := nbr.[j] in
      let nv := dx + wt.[j] in
      if alive.[y] && (y <? PArray.length d) && (nv <? d.[y]) then
        rscan nbr wt alive dx e (j + 1) d.[y <- nv] true (Acc_inv H (dec_step e j Hj))
      else
        rscan nbr wt alive dx e (j + 1) d ch (Acc_inv H (dec_step e j Hj))
  | right _ => (d, ch)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma rpass_eq : forall sa nbr wt alive comp t i d ch H,
  rpass sa nbr wt alive comp t i d ch H =
  match bdec (i <? t) with
  | left Hi =>
      let x := comp.[i] in
      let r := rscan nbr wt alive d.[x] sa.[x + 1] sa.[x] d ch
                 (Zwf_well_founded 0 (gap sa.[x + 1] sa.[x])) in
      rpass sa nbr wt alive comp t (i + 1) (fst r) (snd r) (Acc_inv H (dec_step t i Hi))
  | right _ => (d, ch)
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* the measure facts: the result is pointwise below, strictly somewhere when
   the flag was raised *)
Lemma rscan_dec : forall nbr wt alive dx e z j d ch H,
  gap e j = z ->
  dle (fst (rscan nbr wt alive dx e j d ch H)) d /\
  (snd (rscan nbr wt alive dx e j d ch H) = true ->
     ch = true \/ dlt (fst (rscan nbr wt alive dx e j d ch H)) d).
Proof.
  intros nbr wt alive dx e z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j d ch H Hz. rewrite rscan_eq.
  destruct (bdec (j <? e)) as [Hj | Hj]; simpl.
  - destruct (alive.[nbr.[j]] && (nbr.[j] <? PArray.length d) && (dx + wt.[j] <? d.[nbr.[j]])) eqn:C.
    + apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
      apply ltb_true in C2, C3.
      destruct (dle_set d _ _ C2 C3) as [Hle Hlt].
      edestruct IH as [A B]; [rewrite <- Hz; apply dec_step; exact Hj | reflexivity | ].
      split; [eapply dle_trans; eauto|].
      intros Ht. right. eapply dlt_trans_l; eauto.
    + destruct (IH (gap e (j+1)) ltac:(rewrite <- Hz; apply dec_step; exact Hj) (j+1) d ch
        (Acc_inv H (dec_step e j Hj)) eq_refl) as [A B].
      split; [exact A | exact B].
  - split; [apply dle_refl|]. intros; left; auto.
Qed.

Lemma rpass_dec : forall sa nbr wt alive comp t z i d ch H,
  gap t i = z ->
  dle (fst (rpass sa nbr wt alive comp t i d ch H)) d /\
  (snd (rpass sa nbr wt alive comp t i d ch H) = true ->
     ch = true \/ dlt (fst (rpass sa nbr wt alive comp t i d ch H)) d).
Proof.
  intros sa nbr wt alive comp t z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i d ch H Hz. rewrite rpass_eq.
  destruct (bdec (i <? t)) as [Hi | Hi]; simpl.
  - match goal with |- context [rscan ?a ?b ?c ?dd ?ee ?ff ?gg ?hh ?ii] =>
      destruct (rscan_dec a b c dd ee _ ff gg hh ii eq_refl) as [A1 B1];
      set (r := rscan a b c dd ee ff gg hh ii) in * end.
    edestruct IH as [A B]; [rewrite <- Hz; apply dec_step; exact Hi | reflexivity | ].
    split; [eapply dle_trans; eauto|].
    intros Ht. destruct (B Ht) as [B' | B'].
    + destruct (B1 B') as [B'' | B'']; [left; auto | right; eapply dlt_trans_l; eauto].
    + right. eapply dlt_trans_r; eauto.
  - split; [apply dle_refl|]. intros; left; auto.
Qed.

Lemma dsum_lt : forall d' d, dle d' d -> dlt d' d -> (dsum d' < dsum d)%Z.
Proof.
  intros d' d [L H] [i [Hi Hl]]. unfold dsum. rewrite L.
  pose proof (alength_bound d) as Bd.
  apply zsum_lt.
  - intros k Hk. apply H. rewrite of_Z_nat_phi; rewrite ?wB_val; lia.
  - exists (Z.to_nat (φ i)). pose proof (to_Z_bounded i). split; [lia|].
    rewrite Z2Nat.id by lia. rewrite of_to_Z. exact Hl.
Qed.

Lemma rloop_step : forall sa nbr wt alive comp t d H,
  snd (rpass sa nbr wt alive comp t 0 d false H) = true ->
  Zwf 0 (dsum (fst (rpass sa nbr wt alive comp t 0 d false H))) (dsum d).
Proof.
  intros. destruct (rpass_dec sa nbr wt alive comp t _ 0 d false H eq_refl) as [A B].
  destruct (B H0) as [B' | B']; [discriminate|].
  unfold Zwf. split; [apply dsum_nonneg | apply dsum_lt; auto].
Qed.

Fixpoint rloop (sa nbr wt : array int) (alive : array bool) (comp : array int)
    (t : int) (d : array int) (H : Acc (Zwf 0) (dsum d)) {struct H} : array int :=
  let pr := rpass sa nbr wt alive comp t 0 d false (Zwf_well_founded 0 (gap t 0)) in
  match bdec (snd pr) with
  | left Hc =>
      rloop sa nbr wt alive comp t (fst pr)
        (Acc_inv H (rloop_step sa nbr wt alive comp t d _ Hc))
  | right _ => fst pr
  end.

Definition relax (sa nbr wt : array int) (alive : array bool) (comp : array int)
    (t : int) (b : bst) : array int :=
  if b_flag b then b_d b
  else rloop sa nbr wt alive comp t (b_d b) (Zwf_well_founded 0 (dsum (b_d b))).

(* The centroid search: subtree sizes along the BFS order, then the node
   whose largest remaining part is smallest.  Only the choice of the node
   depends on it, not the correctness. *)
Fixpoint sz_init (comp : array int) (t i : int) (sz big : array int)
    (H : Acc (Zwf 0) (gap t i)) {struct H} : array int * array int :=
  match bdec (i <? t) with
  | left Hi =>
      let x := comp.[i] in
      sz_init comp t (i + 1) sz.[x <- 1] big.[x <- 0] (Acc_inv H (dec_step t i Hi))
  | right _ => (sz, big)
  end.

Fixpoint sz_acc (comp par : array int) (i : int) (sz big : array int)
    (H : Acc (Zwf 0) (φ i)) {struct H} : array int * array int :=
  match bdec (0 <? i) with
  | left Hi =>
      let x := comp.[i] in
      let p := par.[x] in
      let v := sz.[x] in
      sz_acc comp par (i - 1) sz.[p <- sz.[p] + v]
        (if big.[p] <? v then big.[p <- v] else big) (Acc_inv H (dec_down i Hi))
  | right _ => (sz, big)
  end.

Fixpoint argmin (comp sz big : array int) (t i bi bv : int)
    (H : Acc (Zwf 0) (gap t i)) {struct H} : int :=
  match bdec (i <? t) with
  | left Hi =>
      let x := comp.[i] in
      let up := t - sz.[x] in
      let v := if big.[x] <? up then up else big.[x] in
      if v <? bv then argmin comp sz big t (i + 1) i v (Acc_inv H (dec_step t i Hi))
      else argmin comp sz big t (i + 1) bi bv (Acc_inv H (dec_step t i Hi))
  | right _ => bi
  end.

Definition centroid (comp par sz big : array int) (t : int) : int * (array int * array int) :=
  let sb := sz_init comp t 0 sz big (Zwf_well_founded 0 (gap t 0)) in
  let sb' := sz_acc comp par (t - 1) (fst sb) (snd sb) (Zwf_well_founded 0 (φ (t - 1))) in
  (comp.[argmin comp (fst sb') (snd sb') t 0 0 t (Zwf_well_founded 0 (gap t 0))], sb').

(* The Li Chao tree on the abscissae lo..hi (0..X-1 at the root).  A range
   lo < hi keeps its line at key (lo+hi)/2 + 1, a leaf lo = hi at key X+lo;
   a key is in use in this round when its stamp is s. *)
Record lct := mkL { l_st : array int; l_m : array int; l_b : array int }.

Definition lkey (X lo hi : int) : int :=
  if lo =? hi then X + lo else (lo + (hi - lo) / 2) + 1.

Lemma lc_left : forall lo hi : int, (lo <? hi) = true ->
  Zwf 0 (gap ((lo + (hi - lo) / 2)) lo) (gap hi lo).
Proof. intros lo hi H. apply ltb_true in H. unfold Zwf, gap. sia. Qed.

Lemma lc_right : forall lo hi : int, (lo <? hi) = true ->
  Zwf 0 (gap hi ((lo + (hi - lo) / 2) + 1)) (gap hi lo).
Proof. intros lo hi H. apply ltb_true in H. unfold Zwf, gap. sia. Qed.

Fixpoint lc_insert (X s lo hi m b : int) (T : lct)
    (H : Acc (Zwf 0) (gap hi lo)) {struct H} : lct :=
  let k := lkey X lo hi in
  if (l_st T).[k] =? s then
    let cm := (l_m T).[k] in
    let cb := (l_b T).[k] in
    let mid := (lo + (hi - lo) / 2) in
    let nb := m * mid + b <? cm * mid + cb in
    let wm := if nb then m else cm in
    let wb := if nb then b else cb in
    let om := if nb then cm else m in
    let ob := if nb then cb else b in
    let T1 := if nb then mkL (l_st T) (l_m T).[k <- m] (l_b T).[k <- b] else T in
    match bdec (lo <? hi) with
    | left Hlh =>
        if om * lo + ob <? wm * lo + wb then
          lc_insert X s lo mid om ob T1 (Acc_inv H (lc_left lo hi Hlh))
        else
          lc_insert X s (mid + 1) hi om ob T1 (Acc_inv H (lc_right lo hi Hlh))
    | right _ => T1
    end
  else mkL (l_st T).[k <- s] (l_m T).[k <- m] (l_b T).[k <- b].

Fixpoint lc_query (X s lo hi x : int) (T : lct)
    (H : Acc (Zwf 0) (gap hi lo)) {struct H} : int :=
  let k := lkey X lo hi in
  let v := if (l_st T).[k] =? s then (l_m T).[k] * x + (l_b T).[k] else INF in
  match bdec (lo <? hi) with
  | left Hlh =>
      let mid := (lo + (hi - lo) / 2) in
      let r := if x <=? mid then lc_query X s lo mid x T (Acc_inv H (lc_left lo hi Hlh))
               else lc_query X s (mid + 1) hi x T (Acc_inv H (lc_right lo hi Hlh)) in
      if r <? v then r else v
  | right _ => v
  end.

(* the lines (p_v, d_v) of the component, then the queries at p_u *)
Fixpoint ins_loop (xp comp d : array int) (X s t i : int) (T : lct)
    (H : Acc (Zwf 0) (gap t i)) {struct H} : lct :=
  match bdec (i <? t) with
  | left Hi =>
      let v := comp.[i] in
      ins_loop xp comp d X s t (i + 1)
        (lc_insert X s 0 (X - 1) xp.[v - 1] d.[v] T (Zwf_well_founded 0 (gap (X - 1) 0)))
        (Acc_inv H (dec_step t i Hi))
  | right _ => T
  end.

Fixpoint qry_loop (xp comp d : array int) (X s t i : int) (T : lct) (best : array int)
    (H : Acc (Zwf 0) (gap t i)) {struct H} : array int :=
  match bdec (i <? t) with
  | left Hi =>
      let u := comp.[i] in
      let q := d.[u] + lc_query X s 0 (X - 1) xp.[u - 1] T (Zwf_well_founded 0 (gap (X - 1) 0)) in
      qry_loop xp comp d X s t (i + 1) T
        (if q <? best.[u] then best.[u <- q] else best)
        (Acc_inv H (dec_step t i Hi))
  | right _ => best
  end.

(* The main loop: the nodes r = 1..n in turn; while r is alive, its
   component is processed at its centroid c, which is then removed. *)
Fixpoint bcount (a : array bool) (k : nat) : Z :=
  match k with
  | O => 0%Z
  | S k' => (bcount a k' + if a.[of_Z (Z.of_nat k')] then 1 else 0)%Z
  end.

Definition mmeasure (alive : array bool) (r : int) : Z :=
  (bcount alive (Z.to_nat (φ (PArray.length alive))) + ((φ (PArray.length alive)) - (φ r)))%Z.

Record mst := mkM {
  m_vis : array int; m_comp : array int; m_par : array int; m_d : array int;
  m_sz : array int; m_big : array int; m_T : lct; m_best : array int }.

Definition pick (alive : array bool) (c r : int) : int :=
  if (c <? PArray.length alive) && alive.[c] then c else r.

(* one component: the BFS from r, the centroid c, the BFS from c with the
   distances, the fallback, the Li Chao round *)
Definition process (sa nbr wt xp : array int) (X : int) (alive : array bool)
    (r rnd : int) (S : mst) : int * mst :=
  let b1 := bfs sa nbr wt alive (2 * rnd) r (m_vis S) (m_comp S) (m_par S) (m_d S) in
  let cr := centroid (b_comp b1) (b_par b1) (m_sz S) (m_big S) (b_tail b1) in
  let c := pick alive (fst cr) r in
  let b2 := bfs sa nbr wt alive (2 * rnd + 1) c (b_vis b1) (b_comp b1) (b_par b1) (b_d b1) in
  let t := b_tail b2 in
  let d := relax sa nbr wt alive (b_comp b2) t b2 in
  let T := ins_loop xp (b_comp b2) d X rnd t 0 (m_T S) (Zwf_well_founded 0 (gap t 0)) in
  let best := qry_loop xp (b_comp b2) d X rnd t 0 T (m_best S) (Zwf_well_founded 0 (gap t 0)) in
  (c, mkM (b_vis b2) (b_comp b2) (b_par b2) d (fst (snd cr)) (snd (snd cr)) T best).

Lemma bcount_nonneg : forall a k, (0 <= bcount a k)%Z.
Proof. intros a k. induction k; simpl; [lia|]. destruct (a.[_]); lia. Qed.

Lemma bcount_kill : forall (a : array bool) (c : int) k,
  (c <? PArray.length a) = true -> a.[c] = true ->
  (Z.of_nat k <= (φ (PArray.length a)))%Z ->
  bcount a.[c <- false] k = (bcount a k - if ((φ c) <? Z.of_nat k)%Z then 1 else 0)%Z.
Proof.
  intros a c k Hc Ha Hk. pose proof (blength_bound a) as B. apply ltb_true in Hc as Hc'.
  induction k; simpl.
  { pose proof (to_Z_bounded c). destruct ((φ c) <? 0)%Z eqn:E; rewrite ?Z.ltb_lt in E; lia. }
  rewrite IHk by lia.
  rewrite bget_set by auto.
  assert (Hkk : (φ (of_Z (Z.of_nat k))) = Z.of_nat k) by (apply of_Z_nat_phi; rewrite wB_val; lia).
  destruct (c =? of_Z (Z.of_nat k)) eqn:E.
  - apply eqb_true in E. rewrite <- E, Ha.
    assert ((φ c) = Z.of_nat k) by (rewrite E; exact Hkk).
    rewrite ?Zpos_P_of_succ_nat in *;
    destruct ((φ c) <? Z.of_nat k)%Z eqn:E1; destruct ((φ c) <? Z.succ (Z.of_nat k))%Z eqn:E2;
      rewrite ?Z.ltb_lt, ?Z.ltb_ge in *; lia.
  - apply eqb_false in E.
    assert ((φ c) <> Z.of_nat k).
    { intro F. apply E. apply to_Z_inj. rewrite F, Hkk; auto. }
    destruct (a.[of_Z (Z.of_nat k)]);
    rewrite ?Zpos_P_of_succ_nat in *;
    destruct ((φ c) <? Z.of_nat k)%Z eqn:E1; destruct ((φ c) <? Z.succ (Z.of_nat k))%Z eqn:E2;
      rewrite ?Z.ltb_lt, ?Z.ltb_ge in *; rewrite ?wB_val in *; lia.
Qed.

Lemma kill_dec : forall (alive : array bool) (r c : int),
  (r <? PArray.length alive) = true ->
  (c <? PArray.length alive) = true -> alive.[c] = true ->
  Zwf 0 (mmeasure alive.[c <- false] r) (mmeasure alive r).
Proof.
  intros alive r c Hr Hc Ha. unfold Zwf, mmeasure. rewrite blength_set.
  rewrite bcount_kill by (auto; pose proof (to_Z_bounded (PArray.length alive)); lia).
  apply ltb_true in Hr, Hc.
  replace ((φ c) <? Z.of_nat (Z.to_nat (φ (PArray.length alive))))%Z with true
    by (symmetry; apply Z.ltb_lt; lia).
  pose proof (bcount_nonneg alive.[c <- false] (Z.to_nat (φ (PArray.length alive)))).
  rewrite bcount_kill in H by (auto; try (apply ltb_true; auto); lia).
  replace ((φ c) <? Z.of_nat (Z.to_nat (φ (PArray.length alive))))%Z with true in H
    by (symmetry; apply Z.ltb_lt; lia).
  lia.
Qed.

Lemma next_dec : forall (alive : array bool) (r : int),
  (r <? PArray.length alive) = true ->
  Zwf 0 (mmeasure alive (r + 1)) (mmeasure alive r).
Proof.
  intros alive r Hr. apply ltb_true in Hr. unfold Zwf, mmeasure.
  pose proof (bcount_nonneg alive (Z.to_nat (φ (PArray.length alive)))).
  assert ((φ (r + 1)) = (φ r) + 1)%Z by sia. lia.
Qed.

Lemma pick_ok : forall (alive : array bool) (c r : int),
  (r <? PArray.length alive) = true -> alive.[r] = true ->
  (pick alive c r <? PArray.length alive) = true /\ alive.[pick alive c r] = true.
Proof.
  intros alive c r H1 H2. unfold pick.
  destruct ((c <? PArray.length alive) && alive.[c]) eqn:E; [apply andb_prop in E|]; tauto.
Qed.

Lemma process_pick : forall sa nbr wt xp X (alive : array bool) r rnd S,
  (r <? PArray.length alive) = true -> alive.[r] = true ->
  (fst (process sa nbr wt xp X alive r rnd S) <? PArray.length alive) = true /\
  alive.[fst (process sa nbr wt xp X alive r rnd S)] = true.
Proof. intros. unfold process; simpl. apply pick_ok; auto. Qed.

Fixpoint main_loop (sa nbr wt xp : array int) (X r rnd : int) (alive : array bool)
    (S : mst) (H : Acc (Zwf 0) (mmeasure alive r)) {struct H} : array int :=
  match bdec (r <? PArray.length alive) with
  | left Hr =>
      match bdec alive.[r] with
      | left Ha =>
          let cS := process sa nbr wt xp X alive r rnd S in
          main_loop sa nbr wt xp X r (rnd + 1) alive.[fst cS <- false] (snd cS)
            (Acc_inv H (kill_dec alive r (fst cS) Hr
               (proj1 (process_pick sa nbr wt xp X alive r rnd S Hr Ha))
               (proj2 (process_pick sa nbr wt xp X alive r rnd S Hr Ha))))
      | right _ =>
          main_loop sa nbr wt xp X (r + 1) rnd alive S (Acc_inv H (next_dec alive r Hr))
      end
  | right _ => m_best S
  end.

Fixpoint sum_loop (best : array int) (n1 i acc : int)
    (H : Acc (Zwf 0) (gap n1 i)) {struct H} : int :=
  match bdec (i <? n1) with
  | left Hi => sum_loop best n1 (i + 1) (acc + best.[i]) (Acc_inv H (dec_step n1 i Hi))
  | right _ => acc
  end.

Definition yatp_impl (xp xu xv xw : array int) : int :=
  let n := PArray.length xp in
  let n1 := n + 1 in
  let hh := PArray.length xu + PArray.length xu in
  let deg := deg_loop xu xv hh 0 (PArray.make n1 0) (Zwf_well_founded 0 (gap hh 0)) in
  let sp := start_loop deg n1 0 (PArray.make (n1 + 1) 0) (PArray.make n1 0)
              (Zwf_well_founded 0 (gap n1 0)) in
  let nw := fill_loop xu xv xw hh 0 (snd sp) (PArray.make hh 0) (PArray.make hh 0)
              (Zwf_well_founded 0 (gap hh 0)) in
  let X := max_loop xp n 0 0 (Zwf_well_founded 0 (gap n 0)) + 1 in
  let alive := true_loop n1 1 (PArray.make n1 false) (Zwf_well_founded 0 (gap n1 1)) in
  let S := mkM (PArray.make n1 0) (PArray.make n1 0) (PArray.make n1 0)
             (PArray.make n1 0) (PArray.make n1 0) (PArray.make n1 0)
             (mkL (PArray.make (X + X) 0) (PArray.make (X + X) 0) (PArray.make (X + X) 0))
             (PArray.make n1 INF) in
  let best := main_loop (fst sp) (fst nw) (snd nw) xp X 1 1 alive S
                (Zwf_well_founded 0 (mmeasure alive 1)) in
  sum_loop best n1 1 0 (Zwf_well_founded 0 (gap n1 1)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition yatp : array uint -> array uint -> array uint -> array uint -> uint := yatp_impl.
