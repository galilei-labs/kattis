(* Executable implementation and its required termination dependencies.
   Correctness proofs are in chesstournament_proofs.v. *)
(* Implementation of chesstournament (chesstournament.spec): union-find
   over the draws, then Kahn's topological sort of the win graph contracted
   onto the class representatives.

   Code (chess_impl), all on Uint63 ints and flat PArrays, no nat, no Z:
   1. iota: parent p[x] = x; rank array rk = 0.
   2. uf_loop: for every draw j, unite: two finds (path compression, find
      is recursive, depth O(log n) under union by rank) and a union by
      rank of the two roots.
   3. rep_loop: rep[x] = find x for every player (compressing further).
   4. deg_loop: out- and in-degree of rep[k_j] -> rep[l_j] for every win.
   5. pre_loop: CSR offsets st (prefix sums of the out-degrees, n+1 cells)
      and the fill cursors pos.
   6. fill_loop: adj[pos[rep k_j]++] = rep l_j for every win, in match order.
   7. init_loop + kahn/inner: the queue q (one flat array) receives every
      node whose in-degree is 0, then every node whose in-degree drops to 0
      while popping; the answer is (number of nodes queued = n).
   Termination: every loop recurses on an erased Acc (Zwf 0) (meas i),
   meas i = 2^63 - i, the counter i growing below a bound tested at every
   step; find recurses on an erased Acc (child p) x, the accessibility of
   x in the parent forest, which every phase carries as a Prop argument
   (forest_ok p) and re-establishes after each find / union (find_ok,
   unite_ok, uf_loop_ok).

   Proof: generic forest theory (anc, root_of, compress_*, link_root,
   union_roots); phase 1 keeps the roots inside draw classes (UF.uf_deq)
   and the two players of every processed draw in one class (UF.uf_draw);
   the graph section proves the degrees, offsets and CSR segments as
   counts / filters of the edge list EM, and Kahn's invariant (KI, II):
   in-degree = number of edges from not-yet-popped sources, queued iff
   in-degree 0, every edge into a queued node comes from an earlier
   popped node.  Queue complete -> the negated queue position is a skill
   function; queue incomplete -> every unqueued node has an unqueued
   stronger predecessor under any skill function, impossible on a finite
   set (no_ascent). *)

From Chesstournament.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Relations Wellfounded.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

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

Lemma aget_oob : forall (t : array int) (i : int),
  (i <? PArray.length t) = false -> t.[i] = default t.
Proof. intros t i H. exact (get_out_of_bounds int t i H). Qed.

Lemma adefault_set : forall (t : array int) (i b : int), default t.[i <- b] = default t.
Proof. intros. exact (default_set int t i b). Qed.

Lemma adefault_make : forall (n b : int), default (PArray.make n b) = b.
Proof. intros. exact (default_make int b n). Qed.

Lemma aget_set_cases : forall (t : array int) (i j b : int),
  t.[i <- b].[j] = if andb (i =? j) (i <? PArray.length t) then b else t.[j].
Proof.
  intros t i j b.
  destruct (i =? j) eqn:E.
  - apply eqb_spec in E. subst j. simpl.
    destruct (i <? PArray.length t) eqn:L.
    + apply aget_set_same. exact L.
    + assert (L' : (i <? PArray.length t.[i<-b]) = false)
        by (pose proof (length_set int t i b) as E'; rewrite E'; exact L).
      pose proof (get_out_of_bounds int (t.[i<-b]) i L') as A1.
      pose proof (get_out_of_bounds int t i L) as A2.
      etransitivity; [exact A1|]. etransitivity; [|symmetry; exact A2].
      apply default_set.
  - simpl. apply aget_set_other. intro F. subst. rewrite eqb_refl in E. discriminate.
Qed.

Lemma ltb_true : forall a b : int, (a <? b) = true <-> ((φ a) < (φ b))%Z.
Proof. intros. apply ltb_spec. Qed.

Lemma ltb_false : forall a b : int, (a <? b) = false <-> ((φ b) <= (φ a))%Z.
Proof.
  intros a b. rewrite <- Bool.not_true_iff_false, ltb_spec. lia.
Qed.

Lemma eqb_false : forall a b : int, (a =? b) = false <-> a <> b.
Proof. intros. apply eqb_false_spec. Qed.

(* ------------------------------------------------------------------ *)
(* The termination device                                              *)
(* ------------------------------------------------------------------ *)

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

(* The measure of a counter that only grows, below a (possibly moving)
   bound tested at every step. *)
Definition meas (i : int) : Z := (wB - (φ i))%Z.

Lemma dec_step : forall i b : int,
  (i <? b) = true -> Zwf 0 (meas (i + 1)) (meas i).
Proof.
  intros i b H. rewrite ltb_spec in H.
  pose proof (to_Z_bounded b).
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, meas. pose proof (to_Z_bounded i). lia.
Qed.

Lemma succ_spec : forall i b : int, ((φ i) < (φ b))%Z -> (φ (i + 1)) = ((φ i) + 1)%Z.
Proof. intros i b H. pose proof (to_Z_bounded b). sia. Qed.

(* ------------------------------------------------------------------ *)
(* The union-find forest: parent array p, a root is a fixed point.     *)
(* ------------------------------------------------------------------ *)

(* y is the parent of the non-root x *)
Definition child (p : array int) (y x : int) : Prop := p.[x] <> x /\ y = p.[x].

Definition forest_ok (p : array int) : Prop := forall x, Acc (child p) x.

Lemma child_step : forall p x, (p.[x] =? x) = false -> child p p.[x] x.
Proof. intros p x E. split; [apply eqb_false; exact E | reflexivity]. Qed.

(* y follows the parent pointers up to z *)
Definition anc (p : array int) : int -> int -> Prop :=
  clos_refl_trans_1n int (fun a b => b = p.[a]).

Definition root_of (p : array int) (x r : int) : Prop := anc p x r /\ p.[r] = r.

Lemma anc_refl : forall p x, anc p x x.
Proof. intros. apply rt1n_refl. Qed.

Lemma anc_step : forall p x z, anc p p.[x] z -> anc p x z.
Proof. intros p x z H. eapply Relation_Operators.rt1n_trans; [reflexivity | exact H]. Qed.

Lemma anc_child : forall p x y, anc p x y -> x = y \/ clos_trans int (child p) y x.
Proof.
  intros p x y H. induction H as [x | x z y Hs H IH]; [left; reflexivity|].
  subst z.
  destruct (bdec (p.[x] =? x)) as [E | E].
  - apply eqb_spec in E. rewrite E in IH. exact IH.
  - right. destruct IH as [IH | IH].
    + subst y. apply t_step. apply child_step. exact E.
    + eapply t_trans; [exact IH | apply t_step; apply child_step; exact E].
Qed.

(* A rewiring of the parent pointers that keeps the roots and points every
   node to one of its ancestors (path compression) keeps the forest. *)
Lemma compress_ok : forall p p',
  forest_ok p ->
  (forall y, p'.[y] = y <-> p.[y] = y) ->
  (forall y, anc p y p'.[y]) ->
  forest_ok p'.
Proof.
  intros p p' Hp Hfix Hanc.
  assert (Hw : well_founded (clos_trans int (child p)))
    by (apply wf_clos_trans; exact Hp).
  apply (wf_incl int (child p') (clos_trans int (child p))); [|exact Hw].
  intros y x [Hne Hy]. subst y.
  destruct (anc_child p x (p'.[x]) (Hanc x)) as [E | E]; [|exact E].
  exfalso. apply Hne. symmetry. exact E.
Qed.

(* ------------------------------------------------------------------ *)
(* find, with path compression                                         *)
(* ------------------------------------------------------------------ *)

Fixpoint find (p : array int) (x : int) (H : Acc (child p) x) {struct H}
    : array int * int :=
  let y := p.[x] in
  match bdec (y =? x) with
  | left _ => (p, x)
  | right E =>
      let f := find p y (Acc_inv H (child_step p x E)) in
      ((fst f).[x <- snd f], snd f)
  end.

Lemma find_eq : forall p x H,
  find p x H =
  match bdec (p.[x] =? x) with
  | left _ => (p, x)
  | right E =>
      let f := find p p.[x] (Acc_inv H (child_step p x E)) in
      ((fst f).[x <- snd f], snd f)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma find_spec : forall p x (H : Acc (child p) x),
  root_of p x (snd (find p x H)) /\
  (forall y, (fst (find p x H)).[y] = y <-> p.[y] = y) /\
  (forall y, anc p y (fst (find p x H)).[y]) /\
  PArray.length (fst (find p x H)) = PArray.length p.
Proof.
  intros p x H0. pose proof H0 as Hx. revert H0.
  induction Hx as [x _ IH]. intros H0.
  rewrite find_eq. destruct (bdec (p.[x] =? x)) as [E | E]; simpl.
  - split; [split; [apply anc_refl | apply eqb_spec; exact E]|].
    split; [intros; reflexivity|]. split; [intros; apply anc_step; apply anc_refl | reflexivity].
  - destruct (IH _ (child_step p x E) (Acc_inv H0 (child_step p x E)))
      as [[Ha Hr] [Hfix [Hanc Hlen]]].
    set (f := find p p.[x] (Acc_inv H0 (child_step p x E))) in *.
    assert (Hrx : snd f <> x).
    { intro F. rewrite F in Hr. exact (proj1 (eqb_false _ _) E Hr). }
    split; [split; [apply anc_step; exact Ha | exact Hr]|].
    split; [|split].
    + intros y. rewrite aget_set_cases.
      destruct (andb (x =? y) (x <? PArray.length (fst f))) eqn:C.
      * apply andb_prop in C. destruct C as [C _]. apply eqb_spec in C. subst y.
        split; intro F; [exfalso; exact (Hrx F)|].
        exfalso. exact (proj1 (eqb_false _ _) E F).
      * apply Hfix.
    + intros y. rewrite aget_set_cases.
      destruct (andb (x =? y) (x <? PArray.length (fst f))) eqn:C.
      * apply andb_prop in C. destruct C as [C _]. apply eqb_spec in C. subst y.
        apply anc_step. exact Ha.
      * apply Hanc.
    + rewrite alength_set. exact Hlen.
Qed.

Lemma find_ok : forall p x (H : Acc (child p) x),
  forest_ok p -> forest_ok (fst (find p x H)).
Proof.
  intros p x H Hp. destruct (find_spec p x H) as [_ [Hfix [Hanc _]]].
  exact (compress_ok p _ Hp Hfix Hanc).
Qed.

Lemma find_fix : forall p x (H : Acc (child p) x) y,
  p.[y] = y -> (fst (find p x H)).[y] = y.
Proof.
  intros p x H y Hy. destruct (find_spec p x H) as [_ [Hfix _]].
  apply Hfix. exact Hy.
Qed.

Lemma find_root_new : forall p x (H : Acc (child p) x),
  (fst (find p x H)).[snd (find p x H)] = snd (find p x H).
Proof.
  intros p x H. destruct (find_spec p x H) as [[_ Hr] [Hfix _]].
  apply Hfix. exact Hr.
Qed.

(* ------------------------------------------------------------------ *)
(* union by rank                                                       *)
(* ------------------------------------------------------------------ *)

Lemma link_ok : forall p a b, forest_ok p -> p.[b] = b -> a <> b ->
  forest_ok p.[a <- b].
Proof.
  intros p a b Hp Hb Hab.
  assert (Hb' : p.[a <- b].[b] = b) by (rewrite aget_set_other by exact Hab; exact Hb).
  assert (Accb : Acc (child p.[a <- b]) b).
  { constructor. intros z [Hne _]. exfalso. exact (Hne Hb'). }
  intros y. induction (Hp y) as [y _ IH].
  constructor. intros z [Hne Hz].
  rewrite aget_set_cases in Hne, Hz.
  destruct (andb (a =? y) (a <? PArray.length p)) eqn:C.
  - subst z. exact Accb.
  - apply IH. split; assumption.
Qed.

Definition union (p rk : array int) (a b : int) : array int * array int :=
  if a =? b then (p, rk) else
  let ra := rk.[a] in
  let rb := rk.[b] in
  if ra <? rb then (p.[a <- b], rk)
  else if rb <? ra then (p.[b <- a], rk)
  else (p.[b <- a], rk.[a <- ra + 1]).

Lemma union_ok : forall p rk a b, forest_ok p -> p.[a] = a -> p.[b] = b ->
  forest_ok (fst (union p rk a b)).
Proof.
  intros p rk a b Hp Ha Hb. unfold union.
  destruct (a =? b) eqn:E; [exact Hp|]. apply eqb_false in E.
  destruct (rk.[a] <? rk.[b]); [apply link_ok; assumption|].
  destruct (rk.[b] <? rk.[a]); apply link_ok; try assumption; intro F; apply E; symmetry; exact F.
Qed.

(* ------------------------------------------------------------------ *)
(* The two finds and the union of one draw                             *)
(* ------------------------------------------------------------------ *)

Definition unite (p rk : array int) (k l : int) (Hp : forest_ok p)
    : array int * array int :=
  let f1 := find p k (Hp k) in
  let f2 := find (fst f1) l (find_ok p k (Hp k) Hp l) in
  union (fst f2) rk (snd f1) (snd f2).

Lemma unite_ok : forall p rk k l (Hp : forest_ok p),
  forest_ok (fst (unite p rk k l Hp)).
Proof.
  intros p rk k l Hp. unfold unite.
  apply union_ok.
  - apply find_ok. apply find_ok. exact Hp.
  - apply find_fix. apply find_root_new.
  - apply find_root_new.
Qed.

(* ------------------------------------------------------------------ *)
(* The initial forest: every player is its own root                    *)
(* ------------------------------------------------------------------ *)

Fixpoint iota_loop (n x : int) (p : array int) (H : Acc (Zwf 0) (meas x))
    {struct H} : array int :=
  match bdec (x <? n) with
  | left Hx => iota_loop n (x + 1) p.[x <- x] (Acc_inv H (dec_step x n Hx))
  | right _ => p
  end.

Lemma iota_loop_eq : forall n x p H,
  iota_loop n x p H =
  match bdec (x <? n) with
  | left Hx => iota_loop n (x + 1) p.[x <- x] (Acc_inv H (dec_step x n Hx))
  | right _ => p
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition iota (n : int) : array int :=
  iota_loop n 0 (PArray.make n 0) (Zwf_well_founded 0 (meas 0)).

Lemma iota_loop_spec : forall n z x p H, meas x = z ->
  default p = 0 ->
  (forall y, ((φ y) < (φ x))%Z -> ((φ y) < (φ (PArray.length p)))%Z -> p.[y] = y) ->
  let p' := iota_loop n x p H in
  PArray.length p' = PArray.length p /\ default p' = 0 /\
  (forall y, ((φ y) < (φ n))%Z -> ((φ y) < (φ (PArray.length p)))%Z -> p'.[y] = y).
Proof.
  intros n z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros x p H Hz Hd Hinv p'. unfold p'. rewrite iota_loop_eq.
  destruct (bdec (x <? n)) as [Hx | Hx].
  - pose proof (succ_spec x n (proj1 (ltb_true _ _) Hx)) as Hs.
    destruct (IH (meas (x + 1)) ltac:(rewrite <- Hz; apply (dec_step x n Hx))
                (x + 1) p.[x <- x] (Acc_inv H (dec_step x n Hx)) eq_refl
                ltac:(rewrite adefault_set; exact Hd)) as [A [B C]].
    + intros y Hy Hyl. rewrite alength_set in Hyl. rewrite aget_set_cases.
      destruct (andb (x =? y) (x <? PArray.length p)) eqn:E.
      * apply andb_prop in E. destruct E as [E _]. apply eqb_spec in E. exact E.
      * destruct (Z.eq_dec (φ y) (φ x)) as [F | F].
        -- apply to_Z_inj in F. subst y. rewrite eqb_refl in E. simpl in E.
           apply ltb_false in E. lia.
        -- apply Hinv; lia.
    + rewrite alength_set in A, C. split; [exact A|]. split; [exact B|]. exact C.
  - apply ltb_false in Hx. split; [reflexivity|]. split; [exact Hd|].
    intros y Hy Hyl. apply Hinv; lia.
Qed.

Lemma fixed_forest : forall p,
  (forall y, ((φ y) < (φ (PArray.length p)))%Z -> p.[y] = y) ->
  p.[default p] = default p -> forest_ok p.
Proof.
  intros p Hin Hd.
  assert (R : forall y, p.[y] = y -> Acc (child p) y).
  { intros y Hy. constructor. intros z [Hne _]. exfalso. exact (Hne Hy). }
  intros y. destruct (bdec (y <? PArray.length p)) as [E | E].
  - apply R. apply Hin. apply ltb_true. exact E.
  - constructor. intros z [Hne Hz].
    rewrite (aget_oob p y E) in Hz. subst z. apply R. exact Hd.
Qed.

Lemma iota_spec : forall n,
  PArray.length (iota n) = PArray.length (PArray.make n 0) /\
  default (iota n) = 0 /\
  (forall y, ((φ y) < (φ (PArray.length (iota n))))%Z -> (iota n).[y] = y).
Proof.
  intros n. unfold iota.
  destruct (iota_loop_spec n _ 0 (PArray.make n 0) (Zwf_well_founded 0 (meas 0)) eq_refl
              (adefault_make n 0)
              ltac:(intros y Hy; change (φ 0) with 0%Z in Hy; pose proof (to_Z_bounded y); lia))
    as [A [B C]].
  split; [exact A|]. split; [exact B|].
  intros y Hy. rewrite A in Hy. apply C; [|exact Hy].
  rewrite alength_make in Hy.
  destruct (n <=? PArray.max_length) eqn:E; [exact Hy|].
  rewrite <- Bool.not_true_iff_false, leb_spec in E. lia.
Qed.

Lemma iota_ok : forall n, forest_ok (iota n).
Proof.
  intros n. destruct (iota_spec n) as [A [B C]].
  apply fixed_forest; [exact C|]. rewrite B.
  destruct (bdec (0 <? PArray.length (iota n))) as [E | E].
  - apply C. apply ltb_true. exact E.
  - rewrite (aget_oob _ 0 E). exact B.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Phase 1: union-find over the draws. *)
Fixpoint uf_loop (ks : array int) (wins : array bool) (ls : array int) (m j : int)
    (p rk : array int) (Hp : forest_ok p) (H : Acc (Zwf 0) (meas j)) {struct H}
    : array int :=
  match bdec (j <? m) with
  | left Hj =>
      if wins.[j] then
        uf_loop ks wins ls m (j + 1) p rk Hp (Acc_inv H (dec_step j m Hj))
      else
        let u := unite p rk ks.[j] ls.[j] Hp in
        uf_loop ks wins ls m (j + 1) (fst u) (snd u)
          (unite_ok p rk ks.[j] ls.[j] Hp) (Acc_inv H (dec_step j m Hj))
  | right _ => p
  end.

Lemma uf_loop_eq : forall ks wins ls m j p rk Hp H,
  uf_loop ks wins ls m j p rk Hp H =
  match bdec (j <? m) with
  | left Hj =>
      if wins.[j] then
        uf_loop ks wins ls m (j + 1) p rk Hp (Acc_inv H (dec_step j m Hj))
      else
        let u := unite p rk ks.[j] ls.[j] Hp in
        uf_loop ks wins ls m (j + 1) (fst u) (snd u)
          (unite_ok p rk ks.[j] ls.[j] Hp) (Acc_inv H (dec_step j m Hj))
  | right _ => p
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma uf_loop_ok : forall ks wins ls m z j p rk Hp H, meas j = z ->
  forest_ok (uf_loop ks wins ls m j p rk Hp H).
Proof.
  intros ks wins ls m z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j p rk Hp H Hz. rewrite uf_loop_eq.
  destruct (bdec (j <? m)) as [Hj | Hj]; [|exact Hp].
  destruct (wins.[j]); (eapply IH; [rewrite <- Hz; apply (dec_step j m Hj) | reflexivity]).
Qed.

(* Phase 2: the representative of every player (finds, compressing). *)
Fixpoint rep_loop (n x : int) (p rep : array int) (Hp : forest_ok p)
    (H : Acc (Zwf 0) (meas x)) {struct H} : array int :=
  match bdec (x <? n) with
  | left Hx =>
      let f := find p x (Hp x) in
      rep_loop n (x + 1) (fst f) rep.[x <- snd f] (find_ok p x (Hp x) Hp)
        (Acc_inv H (dec_step x n Hx))
  | right _ => rep
  end.

(* Phase 3: out- and in-degrees of the contracted win graph. *)
Fixpoint deg_loop (rep ks : array int) (wins : array bool) (ls : array int)
    (m j : int) (od id : array int) (H : Acc (Zwf 0) (meas j)) {struct H}
    : array int * array int :=
  match bdec (j <? m) with
  | left Hj =>
      if wins.[j] then
        let a := rep.[ks.[j]] in
        let b := rep.[ls.[j]] in
        deg_loop rep ks wins ls m (j + 1) od.[a <- od.[a] + 1] id.[b <- id.[b] + 1]
          (Acc_inv H (dec_step j m Hj))
      else deg_loop rep ks wins ls m (j + 1) od id (Acc_inv H (dec_step j m Hj))
  | right _ => (od, id)
  end.

(* Phase 4: CSR offsets st (prefix sums of od) and fill cursors pos. *)
Fixpoint pre_loop (od : array int) (n u s : int) (st pos : array int)
    (H : Acc (Zwf 0) (meas u)) {struct H} : array int * array int :=
  match bdec (u <? n) with
  | left Hu =>
      let s' := s + od.[u] in
      pre_loop od n (u + 1) s' st.[u + 1 <- s'] pos.[u <- s]
        (Acc_inv H (dec_step u n Hu))
  | right _ => (st, pos)
  end.

(* Phase 5: the CSR targets. *)
Fixpoint fill_loop (rep ks : array int) (wins : array bool) (ls : array int)
    (m j : int) (pos adj : array int) (H : Acc (Zwf 0) (meas j)) {struct H}
    : array int :=
  match bdec (j <? m) with
  | left Hj =>
      if wins.[j] then
        let a := rep.[ks.[j]] in
        let pa := pos.[a] in
        fill_loop rep ks wins ls m (j + 1) pos.[a <- pa + 1] adj.[pa <- rep.[ls.[j]]]
          (Acc_inv H (dec_step j m Hj))
      else fill_loop rep ks wins ls m (j + 1) pos adj (Acc_inv H (dec_step j m Hj))
  | right _ => adj
  end.

(* Phase 6: Kahn's topological sort, the queue q holding every node whose
   in-degree reached 0, popped from h, pushed at t. *)
Fixpoint init_loop (id : array int) (n v : int) (q : array int) (t : int)
    (H : Acc (Zwf 0) (meas v)) {struct H} : array int * int :=
  match bdec (v <? n) with
  | left Hv =>
      if id.[v] =? 0 then init_loop id n (v + 1) q.[t <- v] (t + 1) (Acc_inv H (dec_step v n Hv))
      else init_loop id n (v + 1) q t (Acc_inv H (dec_step v n Hv))
  | right _ => (q, t)
  end.

(* The out-edges adj[e], e in [e, hi), of the node being popped. *)
Fixpoint inner (adj : array int) (hi e : int) (d q : array int) (t : int)
    (H : Acc (Zwf 0) (meas e)) {struct H} : (array int * array int) * int :=
  match bdec (e <? hi) with
  | left He =>
      let v := adj.[e] in
      let dv := d.[v] - 1 in
      if dv =? 0 then
        inner adj hi (e + 1) d.[v <- dv] q.[t <- v] (t + 1) (Acc_inv H (dec_step e hi He))
      else inner adj hi (e + 1) d.[v <- dv] q t (Acc_inv H (dec_step e hi He))
  | right _ => ((d, q), t)
  end.

Fixpoint kahn (adj st : array int) (h : int) (d q : array int) (t : int)
    (H : Acc (Zwf 0) (meas h)) {struct H} : int :=
  match bdec (h <? t) with
  | left Hh =>
      let u := q.[h] in
      let r := inner adj st.[u + 1] st.[u] d q t (Zwf_well_founded 0 (meas st.[u])) in
      kahn adj st (h + 1) (fst (fst r)) (snd (fst r)) (snd r) (Acc_inv H (dec_step h t Hh))
  | right _ => t
  end.

Definition chess_impl (n : uint) (ks : array uint) (wins : array bool)
    (ls : array uint) : bool :=
  let m := PArray.length ks in
  let p0 := iota n in
  let p1 := uf_loop ks wins ls m 0 p0 (PArray.make n 0) (iota_ok n)
              (Zwf_well_founded 0 (meas 0)) in
  let Hp1 := uf_loop_ok ks wins ls m _ 0 p0 (PArray.make n 0) (iota_ok n)
              (Zwf_well_founded 0 (meas 0)) eq_refl in
  let rep := rep_loop n 0 p1 (PArray.make n 0) Hp1 (Zwf_well_founded 0 (meas 0)) in
  let dg := deg_loop rep ks wins ls m 0 (PArray.make n 0) (PArray.make n 0)
              (Zwf_well_founded 0 (meas 0)) in
  let sp := pre_loop (fst dg) n 0 0 (PArray.make (n + 1) 0) (PArray.make n 0)
              (Zwf_well_founded 0 (meas 0)) in
  let adj := fill_loop rep ks wins ls m 0 (snd sp) (PArray.make m 0)
              (Zwf_well_founded 0 (meas 0)) in
  let qi := init_loop (snd dg) n 0 (PArray.make n 0) 0 (Zwf_well_founded 0 (meas 0)) in
  let t := kahn adj (fst sp) 0 (snd dg) (fst qi) (snd qi) (Zwf_well_founded 0 (meas 0)) in
  t =? n.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition chess_consistent :
  uint -> array uint -> array bool -> array uint -> bool := chess_impl.
