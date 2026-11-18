(* Implementation of chatter (chatter.spec): see README.md, section
   Implementation. *)

From Chatter.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Arith.
From Stdlib Require Import Relations Sorted.
From KattisLib Require Import Cost.
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
Elpi complexity sumbool.
Elpi complexity bdec.

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_cnt : forall k : int,
  (0 <? k) = true -> Zwf 0 (φ (k - 1)) (φ k).
Proof.
  intros k H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  unfold Zwf. sia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* one step of the generator *)
Definition nx (a b c r : int) : int := (r * a + b) mod c.
Elpi complexity nx.
#[global] Arguments nx_cost : simpl never.

(* Draws the next chat from generator state r: returns the new state and
   the two people.  At most [bud] attempts; the proof shows that bud = c+1
   is never exhausted on a valid input. *)
Fixpoint redraw (n a b c r bud : int) (H : Acc (Zwf 0) (φ bud)) {struct H}
    : int * int * int :=
  match bdec (0 <? bud) with
  | left Hb =>
      let r1 := nx a b c r in
      let r2 := nx a b c r1 in
      let x := r1 mod n in
      let y := r2 mod n in
      if x =? y then redraw n a b c r2 (bud - 1) (Acc_inv H (dec_cnt bud Hb))
      else (r2, x, y)
  | right _ => (r, 0, 0)
  end.
Elpi complexity redraw.
#[global] Arguments redraw_cost : simpl never.

(* Walks [cnt] members of a list from [q] along [nxt], pointing each to
   [big]. *)
Fixpoint relabel (nxt : array int) (big q cnt : int) (rep : array int)
    (H : Acc (Zwf 0) (φ cnt)) {struct H} : array int :=
  match bdec (0 <? cnt) with
  | left Hc =>
      relabel nxt big (nxt.[q]) (cnt - 1) (rep.[q <- big])
        (Acc_inv H (dec_cnt cnt Hc))
  | right _ => rep
  end.
Elpi complexity relabel.
#[global] Arguments relabel_cost : simpl never.

(* Appends the list of root [small] to the list of root [big]. *)
Definition merge (big small : int) (rep nxt tl sz : array int)
    : array int * array int * array int * array int :=
  let rep' := relabel nxt big small (sz.[small]) rep
                (Zwf_well_founded 0 (φ (sz.[small]))) in
  let nxt' := nxt.[tl.[big] <- small] in
  let tl' := tl.[big <- tl.[small]] in
  let sz' := sz.[big <- sz.[big] + sz.[small]] in
  (rep', nxt', tl', sz').
Elpi complexity merge.
#[global] Arguments merge_cost : simpl never.

(* Weighted union of the sets of x and y. *)
Definition union (x y : int) (rep nxt tl sz : array int)
    : array int * array int * array int * array int :=
  let px := rep.[x] in
  let py := rep.[y] in
  if px =? py then (rep, nxt, tl, sz)
  else if sz.[py] <? sz.[px] then merge px py rep nxt tl sz
  else merge py px rep nxt tl sz.
Elpi complexity union.
#[global] Arguments union_cost : simpl never.

(* The k remaining chats of the day. *)
Fixpoint sim (n a b c r k : int) (rep nxt tl sz : array int)
    (H : Acc (Zwf 0) (φ k)) {struct H} : array int * array int :=
  match bdec (0 <? k) with
  | left Hk =>
      let '(r', x, y) := redraw n a b c r (c + 1)
                           (Zwf_well_founded 0 (φ (c + 1))) in
      let '(rep', nxt', tl', sz') := union x y rep nxt tl sz in
      sim n a b c r' (k - 1) rep' nxt' tl' sz' (Acc_inv H (dec_cnt k Hk))
  | right _ => (rep, sz)
  end.
Elpi complexity sim.
#[global] Arguments sim_cost : simpl never.

(* rep and tl start as the identity. *)
Fixpoint init (n i : int) (rep tl : array int) (H : Acc (Zwf 0) (gap n i))
    {struct H} : array int * array int :=
  match bdec (i <? n) with
  | left Hi => init n (i + 1) (rep.[i <- i]) (tl.[i <- i]) (Acc_inv H (dec_step n i Hi))
  | right _ => (rep, tl)
  end.
Elpi complexity init.
#[global] Arguments init_cost : simpl never.

(* Counts the groups (their first member in index order) and tallies their
   sizes into cnt. *)
Fixpoint tally (n i : int) (rep sz seen cnt : array int) (g : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : int * array int :=
  match bdec (i <? n) with
  | left Hi =>
      let ro := rep.[i] in
      if seen.[ro] =? 0 then
        let s := sz.[ro] in
        tally n (i + 1) rep sz (seen.[ro <- 1]) (cnt.[s <- cnt.[s] + 1]) (g + 1)
          (Acc_inv H (dec_step n i Hi))
      else tally n (i + 1) rep sz seen cnt g (Acc_inv H (dec_step n i Hi))
  | right _ => (g, cnt)
  end.
Elpi complexity tally.
#[global] Arguments tally_cost : simpl never.

(* The number of sizes n-i, i < n, with a nonzero count. *)
Fixpoint countd (n i : int) (cnt : array int) (d : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : int :=
  match bdec (i <? n) with
  | left Hi =>
      countd n (i + 1) cnt (if 0 <? cnt.[n - i] then d + 1 else d)
        (Acc_inv H (dec_step n i Hi))
  | right _ => d
  end.
Elpi complexity countd.
#[global] Arguments countd_cost : simpl never.

(* Writes (s, cnt.[s]) for the sizes s = n, n-1, ..., 1 of nonzero count. *)
Fixpoint fill (n i j : int) (cnt : array int) (out : array (int * int))
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array (int * int) :=
  match bdec (i <? n) with
  | left Hi =>
      let s := n - i in
      let v := cnt.[s] in
      if 0 <? v then
        fill n (i + 1) (j + 1) cnt (out.[j <- (s, v)]) (Acc_inv H (dec_step n i Hi))
      else fill n (i + 1) j cnt out (Acc_inv H (dec_step n i Hi))
  | right _ => out
  end.
Elpi complexity fill.
#[global] Arguments fill_cost : simpl never.

Definition chatter_impl (n r a b c : uint) : uint * array (uint * uint) :=
  let '(rep0, tl0) := init n 0 (PArray.make n 0) (PArray.make n 0)
                        (Zwf_well_founded 0 (gap n 0)) in
  let '(rep, sz) := sim n a b c r n rep0 (PArray.make n 0) tl0 (PArray.make n 1)
                      (Zwf_well_founded 0 (φ n)) in
  let '(g, cnt) := tally n 0 rep sz (PArray.make n 0) (PArray.make (n + 1) 0) 0
                     (Zwf_well_founded 0 (gap n 0)) in
  let d := countd n 0 cnt 0 (Zwf_well_founded 0 (gap n 0)) in
  (g, fill n 0 0 cnt (PArray.make d (0, 0)) (Zwf_well_founded 0 (gap n 0))).
Elpi complexity chatter_impl.
#[global] Arguments chatter_impl_cost : simpl never.

(* ------------------------------------------------------------------ *)
(* Unfolding equations                                                 *)
(* ------------------------------------------------------------------ *)

Lemma redraw_eq : forall n a b c r bud H,
  redraw n a b c r bud H =
  match bdec (0 <? bud) with
  | left Hb =>
      let r1 := nx a b c r in
      let r2 := nx a b c r1 in
      let x := r1 mod n in
      let y := r2 mod n in
      if x =? y then redraw n a b c r2 (bud - 1) (Acc_inv H (dec_cnt bud Hb))
      else (r2, x, y)
  | right _ => (r, 0, 0)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma relabel_eq : forall nxt big q cnt rep H,
  relabel nxt big q cnt rep H =
  match bdec (0 <? cnt) with
  | left Hc =>
      relabel nxt big (nxt.[q]) (cnt - 1) (rep.[q <- big])
        (Acc_inv H (dec_cnt cnt Hc))
  | right _ => rep
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma sim_eq : forall n a b c r k rep nxt tl sz H,
  sim n a b c r k rep nxt tl sz H =
  match bdec (0 <? k) with
  | left Hk =>
      let '(r', x, y) := redraw n a b c r (c + 1)
                           (Zwf_well_founded 0 (φ (c + 1))) in
      let '(rep', nxt', tl', sz') := union x y rep nxt tl sz in
      sim n a b c r' (k - 1) rep' nxt' tl' sz' (Acc_inv H (dec_cnt k Hk))
  | right _ => (rep, sz)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma init_eq : forall n i rep tl H,
  init n i rep tl H =
  match bdec (i <? n) with
  | left Hi => init n (i + 1) (rep.[i <- i]) (tl.[i <- i]) (Acc_inv H (dec_step n i Hi))
  | right _ => (rep, tl)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma tally_eq : forall n i rep sz seen cnt g H,
  tally n i rep sz seen cnt g H =
  match bdec (i <? n) with
  | left Hi =>
      let ro := rep.[i] in
      if seen.[ro] =? 0 then
        let s := sz.[ro] in
        tally n (i + 1) rep sz (seen.[ro <- 1]) (cnt.[s <- cnt.[s] + 1]) (g + 1)
          (Acc_inv H (dec_step n i Hi))
      else tally n (i + 1) rep sz seen cnt g (Acc_inv H (dec_step n i Hi))
  | right _ => (g, cnt)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma countd_eq : forall n i cnt d H,
  countd n i cnt d H =
  match bdec (i <? n) with
  | left Hi =>
      countd n (i + 1) cnt (if 0 <? cnt.[n - i] then d + 1 else d)
        (Acc_inv H (dec_step n i Hi))
  | right _ => d
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma fill_eq : forall n i j cnt out H,
  fill n i j cnt out H =
  match bdec (i <? n) with
  | left Hi =>
      let s := n - i in
      let v := cnt.[s] in
      if 0 <? v then
        fill n (i + 1) (j + 1) cnt (out.[j <- (s, v)]) (Acc_inv H (dec_step n i Hi))
      else fill n (i + 1) j cnt out (Acc_inv H (dec_step n i Hi))
  | right _ => out
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Machine words and N                                                 *)
(* ------------------------------------------------------------------ *)

Lemma wB_value : wB = 9223372036854775808%Z.
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

Definition tN (x : int) : N := Z.to_N (φ x).

Lemma tN_inj : forall u v : int, tN u = tN v -> u = v.
Proof.
  intros u v H. unfold tN in H. apply to_Z_inj.
  pose proof (to_Z_bounded u). pose proof (to_Z_bounded v). lia.
Qed.

Lemma eqb_tN : forall u v : int, (u =? v) = true <-> tN u = tN v.
Proof.
  intros u v. rewrite eqb_spec. split; [intros ->; reflexivity | apply tN_inj].
Qed.

Lemma eqb_false_tN : forall u v : int, (u =? v) = false <-> tN u <> tN v.
Proof.
  intros u v. rewrite <- Bool.not_true_iff_false, eqb_tN. tauto.
Qed.

Lemma tN_Z : forall u : int, Z.of_N (tN u) = (φ u).
Proof. intros u. unfold tN. pose proof (to_Z_bounded u). lia. Qed.

Lemma tN_mod : forall u v : int, tN (u mod v) = (tN u mod tN v)%N.
Proof.
  intros u v. unfold tN. rewrite mod_spec.
  pose proof (to_Z_bounded u). pose proof (to_Z_bounded v).
  apply Z2N.inj_mod; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The generator                                                       *)
(* ------------------------------------------------------------------ *)

Section Generator.

Variables n a b c : int.
Hypothesis Hn : (2 <= (φ n) <= 10000)%Z.
Hypothesis Ha : (1 <= (φ a) <= 10000)%Z.
Hypothesis Hb : (1 <= (φ b) <= 10000)%Z.
Hypothesis Hc : (2 <= (φ c) <= 50000)%Z.

Let nN := tN n.
Let aN := tN a.
Let bN := tN b.
Let cN := tN c.

Lemma nx_Z : forall r, ((φ r) <= 50000)%Z ->
  (φ (nx a b c r)) = (((φ r) * (φ a) + (φ b)) mod (φ c))%Z.
Proof.
  intros r Hr. pose proof (to_Z_bounded r).
  assert (0 <= (φ r) * (φ a) <= 50000 * 10000)%Z by nia.
  unfold nx. rewrite mod_spec, add_spec, mul_spec.
  rewrite (Z.mod_small ((φ r) * (φ a))) by (rewrite wB_value; lia).
  rewrite (Z.mod_small ((φ r) * (φ a) + (φ b))) by (rewrite wB_value; lia).
  reflexivity.
Qed.

Lemma nx_lt : forall r, ((φ r) <= 50000)%Z -> ((φ (nx a b c r)) < (φ c))%Z.
Proof.
  intros r Hr. rewrite nx_Z by exact Hr. apply Z.mod_pos_bound. lia.
Qed.

Lemma tN_nx : forall r, ((φ r) <= 50000)%Z ->
  tN (nx a b c r) = next aN bN cN (tN r).
Proof.
  intros r Hr. pose proof (to_Z_bounded r).
  apply N2Z.inj. rewrite tN_Z, nx_Z by exact Hr.
  unfold next, aN, bN, cN. rewrite N2Z.inj_mod, N2Z.inj_add, N2Z.inj_mul.
  rewrite !tN_Z. reflexivity.
Qed.

Definition fN (s : N) : N := next aN bN cN (next aN bN cN s).
Definition againN (s : N) : Prop :=
  (next aN bN cN s mod nN = next aN bN cN (next aN bN cN s) mod nN)%N.

(* from s, exactly k redraws, then a distinct pair *)
Definition drawn (s : N) (k : nat) : Prop :=
  (forall i, (i < k)%nat -> againN (Nat.iter i fN s)) /\
  ~ againN (Nat.iter k fN s).

Lemma draw_drawn : forall s r' x y, draw nN aN bN cN s r' x y ->
  exists k, drawn s k.
Proof.
  intros s r' x y Hd. induction Hd as [s Hne | s r' x y Heq _ [k [Hk1 Hk2]]].
  - exists O. split; [intros i Hi; lia | exact Hne].
  - exists (S k). split.
    + intros [| i] Hi; [exact Heq |]. rewrite Nat.iter_succ_r. apply Hk1. lia.
    + rewrite Nat.iter_succ_r. exact Hk2.
Qed.

Lemma fN_lt : forall s, (fN s < cN)%N.
Proof.
  intros s. unfold fN, next. apply N.mod_lt.
  unfold cN, tN. lia.
Qed.

Lemma drawn_le : forall s k, drawn s k -> (k <= N.to_nat cN)%nat.
Proof using Hn Ha Hb Hc.
  intros s k [Hk1 Hk2].
  set (l := map (fun i => Nat.iter i fN s) (seq 1 k)).
  assert (Hnd : NoDup l).
  { apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
    assert (Hlt : forall i j, In i (seq 1 k) -> In j (seq 1 k) -> (i < j)%nat ->
              Nat.iter i fN s <> Nat.iter j fN s).
    { intros i j Hi Hj Hij E. apply in_seq in Hi, Hj. apply Hk2.
      replace k with ((k - j) + j)%nat by lia.
      rewrite Nat.iter_add, <- E, <- Nat.iter_add. apply Hk1. lia. }
    intros i j Hi Hj E.
    destruct (Nat.lt_trichotomy i j) as [H | [H | H]]; [| exact H |].
    - exfalso. exact (Hlt i j Hi Hj H E).
    - exfalso. exact (Hlt j i Hj Hi H (eq_sym E)). }
  assert (Hincl : incl l (map N.of_nat (seq 0 (N.to_nat cN)))).
  { intros v Hv. unfold l in Hv. apply in_map_iff in Hv as [i [<- Hi]].
    apply in_seq in Hi. destruct i as [| i]; [lia |].
    simpl. pose proof (fN_lt (Nat.iter i fN s)) as Hl.
    apply in_map_iff. exists (N.to_nat (fN (Nat.iter i fN s))).
    split; [apply N2Nat.id |]. apply in_seq. lia. }
  pose proof (NoDup_incl_length Hnd Hincl) as HL.
  unfold l in HL. rewrite !length_map, !length_seq in HL. exact HL.
Qed.

Lemma draw_det : forall s r1 x1 y1, draw nN aN bN cN s r1 x1 y1 ->
  forall r2 x2 y2, draw nN aN bN cN s r2 x2 y2 -> r1 = r2 /\ x1 = x2 /\ y1 = y2.
Proof.
  intros s r1 x1 y1 Hd. induction Hd as [s Hne | s r' x y Heq _ IH];
    intros r2 x2 y2 Hd2; inversion Hd2; subst.
  - auto.
  - contradiction.
  - contradiction.
  - apply IH. assumption.
Qed.

Lemma redraw_spec : forall k s r bud H,
  drawn s k -> tN r = s -> ((φ r) <= 50000)%Z -> (Z.of_nat k < (φ bud))%Z ->
  let res := redraw n a b c r bud H in
  draw nN aN bN cN s (tN (fst (fst res))) (tN (snd (fst res))) (tN (snd res)) /\
  ((φ (fst (fst res))) < (φ c))%Z.
Proof using Hn Ha Hb Hc.
  induction k as [| k IH]; intros s r bud H Hd Hr Hrb Hk; rewrite redraw_eq;
    (destruct (bdec (0 <? bud)) as [Hb0 | Hb0];
     [| exfalso; rewrite <- Bool.not_true_iff_false, ltb_spec in Hb0;
        change (φ 0) with 0%Z in Hb0; lia]);
    cbv zeta;
    assert (E1 : tN (nx a b c r) = next aN bN cN s) by (rewrite tN_nx; congruence);
    assert (B1 : ((φ (nx a b c r)) <= 50000)%Z) by (pose proof (nx_lt r Hrb); lia);
    assert (E2 : tN (nx a b c (nx a b c r)) = next aN bN cN (next aN bN cN s))
      by (rewrite tN_nx by exact B1; congruence);
    assert (B2 : ((φ (nx a b c (nx a b c r))) < (φ c))%Z) by (apply nx_lt; exact B1);
    destruct (nx a b c r mod n =? nx a b c (nx a b c r) mod n) eqn:Exy.
  - exfalso. apply eqb_tN in Exy. rewrite !tN_mod, E1, E2 in Exy.
    destruct Hd as [_ Hd]. apply Hd. exact Exy.
  - apply eqb_false_tN in Exy. rewrite !tN_mod, E1, E2 in Exy.
    simpl. rewrite !tN_mod, E1, E2. split; [| exact B2].
    apply draw_distinct. exact Exy.
  - apply eqb_tN in Exy. rewrite !tN_mod, E1, E2 in Exy.
    assert (Hd' : drawn (fN s) k).
    { destruct Hd as [Hd1 Hd2]. split.
      - intros i Hi. rewrite <- Nat.iter_succ_r. apply Hd1. lia.
      - rewrite <- Nat.iter_succ_r. exact Hd2. }
    assert (Hb1 : (φ (bud - 1)) = ((φ bud) - 1)%Z)
      by (rewrite ltb_spec in Hb0; change (φ 0) with 0%Z in Hb0; sia).
    destruct (IH (fN s) _ (bud - 1) (Acc_inv H (dec_cnt bud Hb0)) Hd' E2
                ltac:(lia) ltac:(lia)) as [IH1 IH2].
    split; [| exact IH2].
    apply draw_again; [exact Exy | exact IH1].
  - apply eqb_false_tN in Exy. rewrite !tN_mod, E1, E2 in Exy.
    simpl. rewrite !tN_mod, E1, E2. split; [| exact B2].
    apply draw_distinct. exact Exy.
Qed.

End Generator.

(* ------------------------------------------------------------------ *)
(* Linked lists along nxt                                              *)
(* ------------------------------------------------------------------ *)

(* consecutive members of l are linked by nxt *)
Fixpoint chain (nxt : array int) (l : list int) : Prop :=
  match l with
  | v :: t => match t with
              | w :: _ => nxt.[v] = w /\ chain nxt t
              | [] => True
              end
  | [] => True
  end.

Lemma chain_set : forall nxt z u l, chain nxt l -> ~ In z l -> chain (nxt.[z <- u]) l.
Proof.
  intros nxt z u l. induction l as [| v l IH]; intros Hc Hz; [exact I |].
  destruct l as [| w l]; [exact I |].
  destruct Hc as [Hv Hc]. split.
  - rewrite aget_set_other; [exact Hv |]. intros E; apply Hz; left; auto.
  - apply IH; [exact Hc |]. intros H; apply Hz; right; exact H.
Qed.

Lemma chain_set_last : forall nxt z u l,
  chain nxt (l ++ [z]) -> ~ In z l -> chain (nxt.[z <- u]) (l ++ [z]).
Proof.
  intros nxt z u l. induction l as [| v l IH]; intros Hc Hz; [exact I |].
  simpl in Hc |- *.
  destruct l as [| w l]; simpl in Hc |- *.
  - destruct Hc as [Hv _]. split; [| exact I].
    rewrite aget_set_other; [exact Hv |]. intros E; apply Hz; left; auto.
  - destruct Hc as [Hv Hc]. split.
    + rewrite aget_set_other; [exact Hv |]. intros E; apply Hz; left; auto.
    + apply IH; [exact Hc |]. intros H; apply Hz; right; exact H.
Qed.

Lemma chain_app : forall nxt l1 u v l2,
  chain nxt (l1 ++ [u]) -> nxt.[u] = v -> chain nxt (v :: l2) ->
  chain nxt (l1 ++ u :: v :: l2).
Proof.
  intros nxt l1 u v l2. induction l1 as [| w l1 IH]; intros H1 Hu H2.
  - simpl. split; assumption.
  - simpl in H1 |- *. destruct l1 as [| w' l1]; simpl in H1 |- *.
    + destruct H1 as [Hw _]. split; [exact Hw |]. split; assumption.
    + destruct H1 as [Hw H1]. split; [exact Hw |]. apply IH; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* relabel                                                             *)
(* ------------------------------------------------------------------ *)

Lemma relabel_spec : forall nxt big L q cnt rep H,
  chain nxt L -> (L = [] \/ hd_error L = Some q) ->
  (φ cnt) = Z.of_nat (List.length L) ->
  (forall v, In v L -> ((φ v) < (φ (PArray.length rep)))%Z) ->
  PArray.length (relabel nxt big q cnt rep H) = PArray.length rep /\
  (forall j, In j L -> (relabel nxt big q cnt rep H).[j] = big) /\
  (forall j, ~ In j L -> (relabel nxt big q cnt rep H).[j] = rep.[j]).
Proof.
  intros nxt big L. induction L as [| v L IH]; intros q cnt rep H Hc Hq Hcnt Hb;
    rewrite relabel_eq.
  - destruct (bdec (0 <? cnt)) as [Hc0 | Hc0].
    + exfalso. rewrite ltb_spec in Hc0. simpl in Hcnt.
      change (φ 0) with 0%Z in Hc0. lia.
    + split; [reflexivity |]. split; [intros j [] | intros; reflexivity].
  - destruct Hq as [Hq | Hq]; [discriminate |]. simpl in Hq. injection Hq as <-.
    destruct (bdec (0 <? cnt)) as [Hc0 | Hc0].
    2:{ exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hc0.
        simpl in Hcnt. change (φ 0) with 0%Z in Hc0. lia. }
    assert (Hvb : (v <? PArray.length rep) = true)
      by (rewrite ltb_spec; apply Hb; left; reflexivity).
    assert (Hc1 : (φ (cnt - 1)) = Z.of_nat (List.length L))
      by (rewrite ltb_spec in Hc0; change (φ 0) with 0%Z in Hc0; simpl in Hcnt; sia).
    assert (HcL : chain nxt L) by (destruct L; [exact I | exact (proj2 Hc)]).
    assert (HqL : L = [] \/ hd_error L = Some (nxt.[v]))
      by (destruct L as [| w L]; [left; reflexivity | right; simpl; f_equal;
          symmetry; exact (proj1 Hc)]).
    destruct (IH (nxt.[v]) (cnt - 1) (rep.[v <- big]) (Acc_inv H (dec_cnt cnt Hc0))
                HcL HqL Hc1) as [IH1 [IH2 IH3]].
    { intros w Hw. rewrite alength_set. apply Hb. right; exact Hw. }
    split; [rewrite IH1, alength_set; reflexivity |]. split.
    + intros j [<- | Hj].
      * destruct (In_dec eqs v L) as [Hj | Hj]; [apply IH2; exact Hj |].
        rewrite IH3 by exact Hj. apply aget_set_same. exact Hvb.
      * apply IH2. exact Hj.
    + intros j Hj. rewrite IH3 by (intros H'; apply Hj; right; exact H').
      apply aget_set_other. intros E; apply Hj; left; exact E.
Qed.

(* ------------------------------------------------------------------ *)
(* The disjoint-set invariant                                          *)
(* ------------------------------------------------------------------ *)

Section DSU.

Variable n : int.
Hypothesis Hn : (2 <= (φ n) <= 10000)%Z.

(* L is the member list of root ρ *)
Definition mlist (rep nxt tl sz : array int) (ρ : int) (L : list int) : Prop :=
  hd_error L = Some ρ /\ chain nxt L /\ NoDup L /\
  (forall q, In q L <-> ((φ q) < (φ n))%Z /\ rep.[q] = ρ) /\
  last L ρ = tl.[ρ] /\ Z.of_nat (List.length L) = (φ (sz.[ρ])).

Record DInv (rep nxt tl sz : array int) : Prop := {
  d_lrep : PArray.length rep = n;
  d_lnxt : PArray.length nxt = n;
  d_ltl : PArray.length tl = n;
  d_lsz : PArray.length sz = n;
  d_rng : forall p, ((φ p) < (φ n))%Z -> ((φ (rep.[p])) < (φ n))%Z;
  d_idem : forall p, ((φ p) < (φ n))%Z -> rep.[rep.[p]] = rep.[p];
  d_list : forall ρ, ((φ ρ) < (φ n))%Z -> rep.[ρ] = ρ ->
           exists L, mlist rep nxt tl sz ρ L
}.

Lemma nodup_len : forall L : list int, NoDup L ->
  (forall q, In q L -> ((φ q) < (φ n))%Z) -> (Z.of_nat (List.length L) <= (φ n))%Z.
Proof.
  intros L Hnd Hb.
  assert (Hnd' : NoDup (map (fun q => Z.to_nat (φ q)) L)).
  { apply NoDup_map_NoDup_ForallPairs; [| exact Hnd].
    intros u v _ _ E. apply to_Z_inj.
    pose proof (to_Z_bounded u). pose proof (to_Z_bounded v). lia. }
  assert (Hi : incl (map (fun q => Z.to_nat (φ q)) L) (seq 0 (Z.to_nat (φ n)))).
  { intros k Hk. apply in_map_iff in Hk as [q [<- Hq]]. apply in_seq.
    pose proof (Hb q Hq). pose proof (to_Z_bounded q). lia. }
  pose proof (NoDup_incl_length Hnd' Hi) as HL.
  rewrite length_map, length_seq in HL. lia.
Qed.

Lemma mlist_size : forall rep nxt tl sz ρ L, mlist rep nxt tl sz ρ L ->
  (1 <= (φ (sz.[ρ])) <= (φ n))%Z.
Proof.
  intros rep nxt tl sz ρ L (Hh & _ & Hnd & Hin & _ & Hl).
  rewrite <- Hl. split.
  - destruct L; [discriminate | simpl; lia].
  - apply nodup_len; [exact Hnd |]. intros q Hq. apply Hin. exact Hq.
Qed.

Definition hfun (big small u : int) : int := if u =? small then big else u.

Lemma merge_spec : forall rep nxt tl sz big small,
  DInv rep nxt tl sz -> ((φ big) < (φ n))%Z -> ((φ small) < (φ n))%Z ->
  rep.[big] = big -> rep.[small] = small -> big <> small ->
  let res := merge big small rep nxt tl sz in
  DInv (fst (fst (fst res))) (snd (fst (fst res))) (snd (fst res)) (snd res) /\
  forall p, ((φ p) < (φ n))%Z -> (fst (fst (fst res))).[p] = hfun big small (rep.[p]).
Proof.
  intros rep nxt tl sz big small D Hbn Hsn Hbr Hsr Hbs.
  destruct (d_list _ _ _ _ D big Hbn Hbr) as [Lb (Hbh & Hbc & Hbd & Hbi & Hbl & Hbz)].
  destruct (d_list _ _ _ _ D small Hsn Hsr) as [Ls (Hsh & Hsc & Hsd & Hsi & Hsl & Hsz)].
  pose proof (mlist_size _ _ _ _ _ _ (conj Hbh (conj Hbc (conj Hbd (conj Hbi (conj Hbl Hbz))))))
    as Bb.
  pose proof (mlist_size _ _ _ _ _ _ (conj Hsh (conj Hsc (conj Hsd (conj Hsi (conj Hsl Hsz))))))
    as Bs.
  pose proof (d_lrep _ _ _ _ D) as Lr. pose proof (d_lnxt _ _ _ _ D) as Ln.
  pose proof (d_ltl _ _ _ _ D) as Lt. pose proof (d_lsz _ _ _ _ D) as Lz.
  destruct (relabel_spec nxt big Ls small (sz.[small]) rep
              (Zwf_well_founded 0 (φ (sz.[small]))) Hsc (or_intror Hsh)
              (eq_sym Hsz)) as [R1 [R2 R3]].
  { intros v Hv. rewrite Lr. apply Hsi. exact Hv. }
  set (rep' := relabel nxt big small (sz.[small]) rep
                 (Zwf_well_founded 0 (φ (sz.[small])))) in *.
  assert (Hh : forall p, ((φ p) < (φ n))%Z -> rep'.[p] = hfun big small (rep.[p])).
  { intros p Hp. unfold hfun. destruct (rep.[p] =? small) eqn:E.
    - apply eqb_spec in E. apply R2. apply Hsi. split; assumption.
    - apply R3. intros Hi. apply Hsi in Hi as [_ Hi]. rewrite Hi, eqb_refl in E.
      discriminate. }
  assert (hb : hfun big small big = big)
    by (unfold hfun; destruct (big =? small) eqn:E; [apply eqb_spec in E |]; congruence).
  assert (hs : hfun big small small = big) by (unfold hfun; rewrite eqb_refl; reflexivity).
  assert (ho : forall u, u <> small -> hfun big small u = u)
    by (intros u Hu; unfold hfun; destruct (u =? small) eqn:E;
        [apply eqb_spec in E; contradiction | reflexivity]).
  (* the last member of the big list *)
  assert (HLb : Lb <> []) by (intros E; rewrite E in Hbh; discriminate).
  destruct (exists_last HLb) as [Lb0 [t Et]].
  assert (Htl : t = tl.[big]) by (rewrite <- Hbl, Et, last_last; reflexivity).
  assert (Hti : In t Lb) by (rewrite Et; apply in_or_app; right; left; reflexivity).
  assert (Htn : ((φ t) < (φ n))%Z /\ rep.[t] = big) by (apply Hbi; exact Hti).
  assert (Hdisj : forall w, In w Lb -> ~ In w Ls).
  { intros w Hw1 Hw2. apply Hbi in Hw1 as [_ E1]. apply Hsi in Hw2 as [_ E2]. congruence. }
  destruct Ls as [| s0 Ls']; [discriminate |].
  simpl in Hsh. injection Hsh as Hs0. subst s0.
  unfold merge. cbn [fst snd].
  fold rep'.
  split; [| exact Hh].
  split.
  - rewrite R1. exact Lr.
  - rewrite alength_set. exact Ln.
  - rewrite alength_set. exact Lt.
  - rewrite alength_set. exact Lz.
  - intros p Hp. rewrite Hh by exact Hp. unfold hfun.
    destruct (rep.[p] =? small); [exact Hbn | apply (d_rng _ _ _ _ D); exact Hp].
  - intros p Hp. rewrite (Hh p Hp).
    pose proof (d_rng _ _ _ _ D p Hp) as Hpr.
    destruct (eqs (rep.[p]) small) as [E | E].
    + rewrite E, hs. rewrite Hh by exact Hbn. rewrite Hbr. exact hb.
    + rewrite (ho _ E). rewrite Hh by exact Hpr.
      rewrite (d_idem _ _ _ _ D p Hp). apply ho. exact E.
  - intros ρ Hρ Hρr. rewrite Hh in Hρr by exact Hρ.
    destruct (eqs (rep.[ρ]) small) as [E | E].
    { exfalso. rewrite E, hs in Hρr. subst ρ. congruence. }
    rewrite (ho _ E) in Hρr.
    destruct (eqs ρ big) as [Eb | Eb].
    + subst ρ. exists (Lb ++ small :: Ls').
      assert (Hsb : (small <? PArray.length tl) = true)
        by (rewrite ltb_spec, Lt; exact Hsn).
      assert (Hbb : (big <? PArray.length tl) = true)
        by (rewrite ltb_spec, Lt; exact Hbn).
      split; [| split; [| split; [| split; [| split]]]].
      * destruct Lb; [contradiction | exact Hbh].
      * rewrite Et, <- app_assoc. simpl.
        rewrite <- Htl.
        destruct Ls' as [| s1 Ls''].
        -- apply chain_app with (l2 := []) (v := small) (u := t) (l1 := Lb0) (nxt := nxt.[t <- small]) .
           ++ apply chain_set_last.
              ** rewrite <- Et. exact Hbc.
              ** intros Hin. rewrite Et in Hbd. apply NoDup_remove_2 in Hbd.
                 rewrite app_nil_r in Hbd. contradiction.
           ++ apply aget_set_same. rewrite ltb_spec, Ln. apply Htn.
           ++ exact I.
        -- apply chain_app.
           ++ apply chain_set_last.
              ** rewrite <- Et. exact Hbc.
              ** intros Hin. rewrite Et in Hbd. apply NoDup_remove_2 in Hbd.
                 rewrite app_nil_r in Hbd. contradiction.
           ++ apply aget_set_same. rewrite ltb_spec, Ln. apply Htn.
           ++ apply chain_set; [exact Hsc |]. apply Hdisj. exact Hti.
      * apply NoDup_app; [exact Hbd | exact Hsd | exact Hdisj].
      * intros q. rewrite in_app_iff. split.
        -- intros [Hq | Hq].
           ++ apply Hbi in Hq as [Hq1 Hq2]. split; [exact Hq1 |].
              rewrite Hh by exact Hq1. rewrite Hq2. exact hb.
           ++ apply Hsi in Hq as [Hq1 Hq2]. split; [exact Hq1 |].
              rewrite Hh by exact Hq1. rewrite Hq2. exact hs.
        -- intros [Hq1 Hq2]. rewrite Hh in Hq2 by exact Hq1.
           destruct (eqs (rep.[q]) small) as [E' | E'].
           ++ right. apply Hsi. split; assumption.
           ++ left. apply Hbi. rewrite (ho _ E') in Hq2. split; assumption.
      * rewrite aget_set_same by exact Hbb.
        assert (HLs : small :: Ls' <> []) by discriminate.
        destruct (exists_last HLs) as [Ls0 [t' Et']].
        rewrite Et' in Hsl |- *. rewrite app_assoc, last_last.
        rewrite last_last in Hsl. exact Hsl.
      * rewrite length_app.
        assert (Hbz' : (sz.[big] <? PArray.length sz) = true \/ True) by (right; exact I).
        rewrite aget_set_same by (rewrite ltb_spec, Lz; exact Hbn).
        rewrite add_spec, Z.mod_small by (rewrite wB_value; lia).
        rewrite <- Hbz, <- Hsz. lia.
    + assert (Hρs : ρ <> small) by congruence.
      destruct (d_list _ _ _ _ D ρ Hρ Hρr) as [L (Hh1 & Hc1 & Hd1 & Hi1 & Hl1 & Hz1)].
      exists L. split; [exact Hh1 | split; [| split; [exact Hd1 | split; [| split]]]].
      * rewrite <- Htl. apply chain_set; [exact Hc1 |].
        intros Hin. apply Hi1 in Hin as [_ Hin]. apply Eb. rewrite <- Hin. apply Htn.
      * intros q. rewrite Hi1. split; intros [Hq1 Hq2]; split; try exact Hq1.
        -- rewrite Hh by exact Hq1. rewrite Hq2. apply ho. exact Hρs.
        -- rewrite Hh in Hq2 by exact Hq1.
           destruct (eqs (rep.[q]) small) as [E' | E'].
           ++ rewrite E', hs in Hq2. congruence.
           ++ rewrite (ho _ E') in Hq2. exact Hq2.
      * rewrite aget_set_other by (intros E'; apply Eb; symmetry; exact E'). exact Hl1.
      * rewrite aget_set_other by (intros E'; apply Eb; symmetry; exact E'). exact Hz1.
Qed.

End DSU.

Lemma eqb_false_neq : forall u v : int, (u =? v) = false -> u <> v.
Proof. intros u v E F. subst. rewrite eqb_refl in E. discriminate. Qed.

Lemma hfun_eq : forall big small u v, big <> small ->
  hfun big small u = hfun big small v <->
  u = v \/ (u = big /\ v = small) \/ (u = small /\ v = big).
Proof.
  intros big small u v Hbs. unfold hfun.
  assert (Hf : forall w, w <> small -> (w =? small) = false)
    by (intros w Hw; apply Bool.not_true_iff_false; rewrite eqb_spec; exact Hw).
  destruct (eqs u small) as [E1 | E1]; destruct (eqs v small) as [E2 | E2];
    subst; rewrite ?eqb_refl, ?Hf by assumption; intuition congruence.
Qed.

Lemma union_spec : forall n, (2 <= (φ n) <= 10000)%Z ->
  forall rep nxt tl sz x y,
  DInv n rep nxt tl sz -> ((φ x) < (φ n))%Z -> ((φ y) < (φ n))%Z ->
  let res := union x y rep nxt tl sz in
  DInv n (fst (fst (fst res))) (snd (fst (fst res))) (snd (fst res)) (snd res) /\
  forall p q, ((φ p) < (φ n))%Z -> ((φ q) < (φ n))%Z ->
    ((fst (fst (fst res))).[p] = (fst (fst (fst res))).[q] <->
     rep.[p] = rep.[q] \/ (rep.[p] = rep.[x] /\ rep.[q] = rep.[y]) \/
     (rep.[p] = rep.[y] /\ rep.[q] = rep.[x])).
Proof.
  intros n Hn rep nxt tl sz x y D Hx Hy. unfold union. cbv zeta.
  destruct (rep.[x] =? rep.[y]) eqn:E.
  - apply eqb_spec in E. cbn [fst snd]. split; [exact D |].
    intros p q _ _. split; [tauto |]. intros [H | [[H1 H2] | [H1 H2]]]; congruence.
  - apply eqb_false_neq in E.
    pose proof (d_rng _ _ _ _ _ D x Hx) as Rx. pose proof (d_rng _ _ _ _ _ D y Hy) as Ry.
    pose proof (d_idem _ _ _ _ _ D x Hx) as Ix. pose proof (d_idem _ _ _ _ _ D y Hy) as Iy.
    destruct (sz.[rep.[y]] <? sz.[rep.[x]]).
    + destruct (merge_spec n Hn rep nxt tl sz (rep.[x]) (rep.[y]) D Rx Ry Ix Iy E)
        as [D' Hh].
      split; [exact D' |]. intros p q Hp Hq. rewrite (Hh p Hp), (Hh q Hq).
      rewrite hfun_eq by exact E. tauto.
    + assert (E' : rep.[y] <> rep.[x]) by congruence.
      destruct (merge_spec n Hn rep nxt tl sz (rep.[y]) (rep.[x]) D Ry Rx Iy Ix E')
        as [D' Hh].
      split; [exact D' |]. intros p q Hp Hq. rewrite (Hh p Hp), (Hh q Hq).
      rewrite hfun_eq by exact E'. tauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Groups                                                              *)
(* ------------------------------------------------------------------ *)

Lemma sg_mono : forall es es' p q, (forall e, In e es -> In e es') ->
  same_group es p q -> same_group es' p q.
Proof.
  intros es es' p q Hi H. induction H.
  - apply rst_step. apply Hi. assumption.
  - apply rst_refl.
  - apply rst_sym. assumption.
  - eapply rst_trans; eassumption.
Qed.

Lemma sg_nil : forall p q, same_group [] p q <-> p = q.
Proof.
  intros p q. split.
  - intros H. induction H; [contradiction | reflexivity | congruence | congruence].
  - intros ->. apply rst_refl.
Qed.

Lemma sg_step : forall es x y (f f' : N -> N),
  (forall p q, same_group es p q <-> f p = f q) ->
  (forall p q, f' p = f' q <->
     f p = f q \/ (f p = f x /\ f q = f y) \/ (f p = f y /\ f q = f x)) ->
  forall p q, same_group (es ++ [(x, y)]) p q <-> f' p = f' q.
Proof.
  intros es x y f f' Hf Hf' p q. split.
  - intros H. induction H as [p q H | p | p q _ IH | p q w _ IH1 _ IH2].
    + apply in_app_or in H as [H | [H | []]].
      * apply Hf'. left. apply Hf. apply rst_step. exact H.
      * injection H as <- <-. apply Hf'. right; left; split; reflexivity.
    + reflexivity.
    + congruence.
    + congruence.
  - assert (Hm : forall u v, same_group es u v -> same_group (es ++ [(x, y)]) u v)
      by (intros u v; apply sg_mono; intros e He; apply in_or_app; left; exact He).
    assert (He : same_group (es ++ [(x, y)]) x y)
      by (apply rst_step; apply in_or_app; right; left; reflexivity).
    intros H. apply Hf' in H as [H | [[H1 H2] | [H1 H2]]].
    + apply Hm, Hf. exact H.
    + eapply rst_trans; [apply Hm, Hf; exact H1 |].
      eapply rst_trans; [exact He |]. apply Hm, Hf. symmetry. exact H2.
    + eapply rst_trans; [apply Hm, Hf; exact H1 |].
      eapply rst_trans; [apply rst_sym; exact He |]. apply Hm, Hf. symmetry. exact H2.
Qed.

(* the group label of a person: its root, or itself outside 0..n-1 *)
Definition F (n : int) (rep : array int) (p : N) : N :=
  if (p <? tN n)%N then tN (rep.[of_Z (Z.of_N p)]) else p.

Definition GInv (n : int) (rep : array int) (es : list (N * N)) : Prop :=
  forall p q, same_group es p q <-> F n rep p = F n rep q.

Lemma tN_eq_iff : forall u v : int, tN u = tN v <-> u = v.
Proof. intros u v. split; [apply tN_inj | intros ->; reflexivity]. Qed.

Lemma of_tN : forall u : int, of_Z (Z.of_N (tN u)) = u.
Proof. intros u. rewrite tN_Z. apply of_to_Z. Qed.

Lemma phi_ofN : forall n p, (p < tN n)%N -> (φ (of_Z (Z.of_N p))) = Z.of_N p.
Proof.
  intros n p Hp. rewrite of_Z_spec. apply Z.mod_small.
  pose proof (tN_Z n). pose proof (to_Z_bounded n). rewrite wB_value in *. lia.
Qed.

Lemma F_lt : forall n rep p, (forall p, ((φ p) < (φ n))%Z -> ((φ (rep.[p])) < (φ n))%Z) ->
  (p < tN n)%N -> F n rep p = tN (rep.[of_Z (Z.of_N p)]) /\
  (tN (rep.[of_Z (Z.of_N p)]) < tN n)%N.
Proof.
  intros n rep p Hr Hp. unfold F. rewrite (proj2 (N.ltb_lt _ _) Hp). split; [reflexivity |].
  pose proof (Hr (of_Z (Z.of_N p)) ltac:(rewrite (phi_ofN n p Hp), <- tN_Z; lia)).
  apply N2Z.inj_lt. rewrite !tN_Z. lia.
Qed.

Lemma F_ge : forall n rep p, (tN n <= p)%N -> F n rep p = p.
Proof.
  intros n rep p Hp. unfold F. destruct (N.ltb_spec p (tN n)); [lia | reflexivity].
Qed.

Lemma F_step : forall n rep rep' x y,
  (forall p, ((φ p) < (φ n))%Z -> ((φ (rep.[p])) < (φ n))%Z) ->
  (forall p, ((φ p) < (φ n))%Z -> ((φ (rep'.[p])) < (φ n))%Z) ->
  ((φ x) < (φ n))%Z -> ((φ y) < (φ n))%Z ->
  (forall p q, ((φ p) < (φ n))%Z -> ((φ q) < (φ n))%Z ->
    (rep'.[p] = rep'.[q] <->
     rep.[p] = rep.[q] \/ (rep.[p] = rep.[x] /\ rep.[q] = rep.[y]) \/
     (rep.[p] = rep.[y] /\ rep.[q] = rep.[x]))) ->
  forall p q, F n rep' p = F n rep' q <->
    F n rep p = F n rep q \/
    (F n rep p = F n rep (tN x) /\ F n rep q = F n rep (tN y)) \/
    (F n rep p = F n rep (tN y) /\ F n rep q = F n rep (tN x)).
Proof.
  intros n rep rep' x y Hr Hr' Hx Hy Hu p q.
  assert (Hxn : (tN x < tN n)%N) by (apply N2Z.inj_lt; rewrite !tN_Z; exact Hx).
  assert (Hyn : (tN y < tN n)%N) by (apply N2Z.inj_lt; rewrite !tN_Z; exact Hy).
  destruct (F_lt n rep (tN x) Hr Hxn) as [Fx Bx]. rewrite of_tN in Fx, Bx.
  destruct (F_lt n rep (tN y) Hr Hyn) as [Fy By]. rewrite of_tN in Fy, By.
  rewrite Fx, Fy.
  destruct (N.ltb_spec p (tN n)) as [Hp | Hp]; destruct (N.ltb_spec q (tN n)) as [Hq | Hq].
  - destruct (F_lt n rep p Hr Hp) as [Fp _]. destruct (F_lt n rep q Hr Hq) as [Fq _].
    destruct (F_lt n rep' p Hr' Hp) as [Fp' _]. destruct (F_lt n rep' q Hr' Hq) as [Fq' _].
    rewrite Fp, Fq, Fp', Fq', !tN_eq_iff.
    apply Hu.
    + rewrite (phi_ofN n p Hp), <- tN_Z. lia.
    + rewrite (phi_ofN n q Hq), <- tN_Z. lia.
  - destruct (F_lt n rep p Hr Hp) as [Fp Bp]. destruct (F_lt n rep' p Hr' Hp) as [Fp' Bp'].
    rewrite Fp, Fp', !(F_ge n _ q Hq). split; intros; lia.
  - destruct (F_lt n rep q Hr Hq) as [Fq Bq]. destruct (F_lt n rep' q Hr' Hq) as [Fq' Bq'].
    rewrite Fq, Fq', !(F_ge n _ p Hp). split; intros; lia.
  - rewrite !(F_ge n _ p Hp), !(F_ge n _ q Hq). split; intros; lia.
Qed.

Lemma draw_lt : forall nN aN bN cN s r' x y, draw nN aN bN cN s r' x y ->
  (0 < nN)%N -> (x < nN)%N /\ (y < nN)%N.
Proof.
  intros nN aN bN cN s r' x y Hd Hn. induction Hd as [s _ | s r' x y _ _ IH].
  - split; apply N.mod_lt; lia.
  - exact IH.
Qed.

Lemma make_length : forall n (v : int), (0 <= (φ n) <= 4194303)%Z ->
  PArray.length (PArray.make n v) = n.
Proof.
  intros n v Hn. rewrite alength_make.
  replace (n <=? PArray.max_length) with true; [reflexivity |].
  symmetry. rewrite leb_spec. change (φ PArray.max_length) with 4194303%Z. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The simulation                                                      *)
(* ------------------------------------------------------------------ *)

Section Sim.

Variables n a b c : int.
Hypothesis Hn : (2 <= (φ n) <= 10000)%Z.
Hypothesis Ha : (1 <= (φ a) <= 10000)%Z.
Hypothesis Hb : (1 <= (φ b) <= 10000)%Z.
Hypothesis Hc : (2 <= (φ c) <= 50000)%Z.

Lemma sim_spec : forall kN s es, rounds (tN n) (tN a) (tN b) (tN c) kN s es ->
  forall r k rep nxt tl sz H es0,
  tN r = s -> ((φ r) <= 50000)%Z -> (φ k) = Z.of_nat kN ->
  DInv n rep nxt tl sz -> GInv n rep es0 ->
  (exists nxt' tl', DInv n (fst (sim n a b c r k rep nxt tl sz H)) nxt' tl'
                       (snd (sim n a b c r k rep nxt tl sz H))) /\
  GInv n (fst (sim n a b c r k rep nxt tl sz H)) (es0 ++ es).
Proof.
  intros kN s es Hr. induction Hr as [s | kN s s' x0 y0 es Hd Hr IH];
    intros r k rep nxt tl sz H es0 Es Br Ek D G; rewrite sim_eq.
  - destruct (bdec (0 <? k)) as [Hk | Hk].
    + exfalso. rewrite ltb_spec in Hk. change (φ 0) with 0%Z in Hk. simpl in Ek. lia.
    + cbn [fst snd]. split; [exists nxt, tl; exact D | rewrite app_nil_r; exact G].
  - destruct (bdec (0 <? k)) as [Hk | Hk].
    2:{ exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hk.
        change (φ 0) with 0%Z in Hk. lia. }
    destruct (draw_drawn n a b c _ _ _ _ Hd) as [k0 Hk0].
    pose proof (drawn_le n a b c Hn Ha Hb Hc _ _ Hk0) as Hk0le.
    assert (Hc1 : (φ (c + 1)) = ((φ c) + 1)%Z) by sia.
    assert (Hk0c : (Z.of_nat k0 < (φ (c + 1)))%Z).
    { rewrite Hc1. unfold tN in Hk0le. lia. }
    pose proof (redraw_spec n a b c Hn Ha Hb Hc k0 s r (c + 1)
                  (Zwf_well_founded 0 (φ (c + 1))) Hk0 Es Br Hk0c) as RS.
    cbv zeta in RS.
    destruct (redraw n a b c r (c + 1) (Zwf_well_founded 0 (φ (c + 1))))
      as [[r' x] y] eqn:Er.
    cbn [fst snd] in RS. destruct RS as [RS1 RS2].
    destruct (draw_det n a b c _ _ _ _ Hd _ _ _ RS1) as [-> [-> ->]].
    destruct (draw_lt _ _ _ _ _ _ _ _ RS1) as [Hxn Hyn].
    { apply N2Z.inj_lt. rewrite tN_Z. lia. }
    assert (Hx : ((φ x) < (φ n))%Z) by (rewrite <- !tN_Z; lia).
    assert (Hy : ((φ y) < (φ n))%Z) by (rewrite <- !tN_Z; lia).
    pose proof (union_spec n Hn rep nxt tl sz x y D Hx Hy) as US. cbv zeta in US.
    destruct (union x y rep nxt tl sz) as [[[rep1 nxt1] tl1] sz1] eqn:Eu.
    cbn [fst snd] in US. destruct US as [D1 U1].
    cbv beta iota zeta.
    replace (es0 ++ (tN x, tN y) :: es) with ((es0 ++ [(tN x, tN y)]) ++ es)
      by (rewrite <- app_assoc; reflexivity).
    apply IH.
    + reflexivity.
    + lia.
    + rewrite ltb_spec in Hk. change (φ 0) with 0%Z in Hk. sia.
    + exact D1.
    + intros p q. apply (sg_step es0 (tN x) (tN y) (F n rep) (F n rep1) G).
      apply (F_step n rep rep1 x y (d_rng _ _ _ _ _ D) (d_rng _ _ _ _ _ D1) Hx Hy U1).
Qed.

End Sim.

Lemma init_spec : forall n, (2 <= (φ n) <= 10000)%Z ->
  forall z i rep tl H, gap n i = z ->
  PArray.length rep = n -> PArray.length tl = n -> ((φ i) <= (φ n))%Z ->
  (forall j, ((φ j) < (φ i))%Z -> rep.[j] = j /\ tl.[j] = j) ->
  PArray.length (fst (init n i rep tl H)) = n /\
  PArray.length (snd (init n i rep tl H)) = n /\
  forall j, ((φ j) < (φ n))%Z ->
    (fst (init n i rep tl H)).[j] = j /\ (snd (init n i rep tl H)).[j] = j.
Proof.
  intros n Hn z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i rep tl H Hz Lr Lt Hi Hid. rewrite init_eq.
  destruct (bdec (i <? n)) as [Hin | Hin].
  - pose proof Hin as Hin'. rewrite ltb_spec in Hin'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    eapply IH; [ | reflexivity | rewrite alength_set; exact Lr
               | rewrite alength_set; exact Lt | lia | ].
    + rewrite <- Hz. apply dec_step. exact Hin.
    + intros j Hj. destruct (eqs j i) as [-> | Ne].
      * rewrite !aget_set_same by (rewrite ltb_spec; congruence). split; reflexivity.
      * rewrite !aget_set_other by congruence. apply Hid.
        assert ((φ j) <> (φ i)) by (intros E; apply Ne; apply to_Z_inj; exact E). lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hin.
    cbn [fst snd]. split; [exact Lr | split; [exact Lt |]].
    intros j Hj. apply Hid. lia.
Qed.

Lemma start_spec : forall n, (2 <= (φ n) <= 10000)%Z -> forall rep tl,
  PArray.length rep = n -> PArray.length tl = n ->
  (forall j, ((φ j) < (φ n))%Z -> rep.[j] = j /\ tl.[j] = j) ->
  DInv n rep (PArray.make n 0) tl (PArray.make n 1) /\ GInv n rep [].
Proof.
  intros n Hn rep tl Lr Lt Hid. split.
  - split.
    + exact Lr.
    + apply make_length. lia.
    + exact Lt.
    + apply make_length. lia.
    + intros p Hp. rewrite (proj1 (Hid p Hp)). exact Hp.
    + intros p Hp. rewrite (proj1 (Hid p Hp)). apply Hid. exact Hp.
    + intros ρ Hρ _. exists [ρ].
      split; [reflexivity | split; [exact I | split; [| split; [| split]]]].
      * constructor; [intros [] | constructor].
      * intros q. split.
        -- intros [<- | []]. split; [exact Hρ | apply Hid; exact Hρ].
        -- intros [Hq E]. rewrite (proj1 (Hid q Hq)) in E. left. symmetry. exact E.
      * simpl. symmetry. apply Hid. exact Hρ.
      * rewrite aget_make. reflexivity.
  - intros p q. rewrite sg_nil.
    assert (HF : forall p, F n rep p = p).
    { intros u. unfold F. destruct (N.ltb_spec u (tN n)) as [Hu | Hu]; [| reflexivity].
      rewrite (proj1 (Hid _ ltac:(rewrite (phi_ofN n u Hu), <- tN_Z; lia))).
      apply N2Z.inj. rewrite tN_Z, (phi_ofN n u Hu). reflexivity. }
    rewrite !HF. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The tally                                                           *)
(* ------------------------------------------------------------------ *)

Lemma phi_of_nat : forall k : nat, (Z.of_nat k < wB)%Z -> (φ (of_nat k)) = Z.of_nat k.
Proof. intros k Hk. rewrite of_Z_spec. apply Z.mod_small. lia. Qed.

Lemma of_nat_phi : forall i : int, of_nat (Z.to_nat (φ i)) = i.
Proof.
  intros i. apply to_Z_inj. pose proof (to_Z_bounded i).
  rewrite phi_of_nat; lia.
Qed.

Section Tally.

Variables (n : int) (rep sz : array int).
Hypothesis Hn : (2 <= (φ n) <= 10000)%Z.
Hypothesis Hrng : forall p, ((φ p) < (φ n))%Z -> ((φ (rep.[p])) < (φ n))%Z.
Hypothesis Hsz : forall p, ((φ p) < (φ n))%Z -> (1 <= (φ (sz.[rep.[p]])) <= (φ n))%Z.

(* j is the first member of its group in index order *)
Definition firstb (j : nat) : bool :=
  forallb (fun i => negb (rep.[of_nat i] =? rep.[of_nat j])) (seq 0 j).

Definition szof (j : nat) : int := sz.[rep.[of_nat j]].

Definition gl (m : nat) : nat := List.length (filter firstb (seq 0 m)).

Definition cntl (s : int) (m : nat) : nat :=
  List.length (filter (fun j => andb (firstb j) (szof j =? s)) (seq 0 m)).

Lemma firstb_iff : forall j, firstb j = true <->
  forall i, (i < j)%nat -> rep.[of_nat i] <> rep.[of_nat j].
Proof.
  intros j. unfold firstb. rewrite forallb_forall. split.
  - intros H i Hi E. specialize (H i ltac:(apply in_seq; lia)).
    rewrite E, eqb_refl in H. discriminate.
  - intros H i Hi. apply in_seq in Hi.
    destruct (rep.[of_nat i] =? rep.[of_nat j]) eqn:E; [| reflexivity].
    apply eqb_spec in E. exfalso. exact (H i ltac:(lia) E).
Qed.

Lemma gl_S : forall m, gl (S m) = (gl m + if firstb m then 1 else 0)%nat.
Proof.
  intros m. unfold gl. rewrite seq_S, filter_app, length_app. simpl.
  destruct (firstb m); reflexivity.
Qed.

Lemma cntl_S : forall s m, cntl s (S m) =
  (cntl s m + if andb (firstb m) (szof m =? s)%uint63 then 1 else 0)%nat.
Proof.
  intros s m. unfold cntl. rewrite seq_S, filter_app, length_app. simpl.
  destruct (andb (firstb m) (szof m =? s)); reflexivity.
Qed.

Lemma cntl_le : forall s m, (cntl s m <= m)%nat.
Proof.
  intros s m. unfold cntl. etransitivity; [apply filter_length_le |].
  rewrite length_seq. lia.
Qed.

Lemma gl_le : forall m, (gl m <= m)%nat.
Proof.
  intros m. unfold gl. etransitivity; [apply filter_length_le |].
  rewrite length_seq. lia.
Qed.

Lemma tally_spec : forall z i seen cnt g H, gap n i = z ->
  ((φ i) <= (φ n))%Z -> PArray.length seen = n -> PArray.length cnt = n + 1 ->
  (forall ρ, ((φ ρ) < (φ n))%Z ->
     (seen.[ρ] = 0 <-> forall j, (j < Z.to_nat (φ i))%nat -> rep.[of_nat j] <> ρ)) ->
  (φ g) = Z.of_nat (gl (Z.to_nat (φ i))) ->
  (forall s, ((φ s) <= (φ n))%Z -> (φ (cnt.[s])) = Z.of_nat (cntl s (Z.to_nat (φ i)))) ->
  (φ (fst (tally n i rep sz seen cnt g H))) = Z.of_nat (gl (Z.to_nat (φ n))) /\
  PArray.length (snd (tally n i rep sz seen cnt g H)) = n + 1 /\
  forall s, ((φ s) <= (φ n))%Z ->
    (φ ((snd (tally n i rep sz seen cnt g H)).[s])) = Z.of_nat (cntl s (Z.to_nat (φ n))).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i seen cnt g H Hz Hi Ls Lc Hseen Hg Hcnt. rewrite tally_eq.
  destruct (bdec (i <? n)) as [Hin | Hin].
  2:{ rewrite <- Bool.not_true_iff_false, ltb_spec in Hin.
      replace (φ i) with (φ n) in * by lia. cbn [fst snd].
      split; [exact Hg | split; [exact Lc | exact Hcnt]]. }
  pose proof Hin as Hin'. rewrite ltb_spec in Hin'.
  pose proof (to_Z_bounded i) as Bi.
  assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  assert (Hni : Z.to_nat (φ (i + 1)) = S (Z.to_nat (φ i))) by lia.
  set (ni := Z.to_nat (φ i)) in *.
  assert (Eni : of_nat ni = i) by apply of_nat_phi.
  assert (Hc1 : (φ (n + 1)) = ((φ n) + 1)%Z) by sia.
  pose proof (Hrng i Hin') as Hro.
  pose proof (Hsz i Hin') as Hso.
  assert (Hfirst : (seen.[rep.[i]] =? 0) = firstb ni).
  { destruct (seen.[rep.[i]] =? 0) eqn:E; symmetry.
    - apply eqb_spec in E. apply firstb_iff. rewrite Eni.
      apply (Hseen _ Hro). exact E.
    - apply Bool.not_true_iff_false. rewrite firstb_iff. rewrite Eni.
      intros Hf. apply eqb_false_neq in E. apply E. apply (Hseen _ Hro). exact Hf. }
  cbv zeta. rewrite Hfirst.
  destruct (firstb ni) eqn:Ef.
  - eapply IH; [ | reflexivity | lia | rewrite alength_set; exact Ls
               | rewrite alength_set; exact Lc | | | ].
    + rewrite <- Hz. apply dec_step. exact Hin.
    + intros ρ Hρ. rewrite Hni. destruct (eqs ρ (rep.[i])) as [-> | Ne].
      * rewrite aget_set_same by (rewrite ltb_spec, Ls; exact Hro). split.
        -- intros E. exfalso. apply (eqb_false_neq 1 0); [reflexivity | exact E].
        -- intros Hf. exfalso. apply (Hf ni ltac:(lia)). rewrite Eni. reflexivity.
      * rewrite aget_set_other by congruence. rewrite (Hseen ρ Hρ). split.
        -- intros Hf j Hj. destruct (Nat.eq_dec j ni) as [-> | Nj].
           ++ rewrite Eni. congruence.
           ++ apply Hf. lia.
        -- intros Hf j Hj. apply Hf. lia.
    + rewrite Hni, gl_S, Ef. pose proof (gl_le ni).
      rewrite add_spec, Z.mod_small; change (φ 1) with 1%Z; [lia |].
      rewrite wB_value. lia.
    + intros s Hs. rewrite Hni, cntl_S, Ef. simpl andb. unfold szof. rewrite Eni.
      destruct (eqs s (sz.[rep.[i]])) as [-> | Ne].
      * rewrite eqb_refl.
        rewrite aget_set_same by (rewrite ltb_spec, Lc, Hc1; lia).
        pose proof (cntl_le (sz.[rep.[i]]) ni).
        rewrite add_spec, Z.mod_small; change (φ 1) with 1%Z;
          [rewrite (Hcnt _ Hs); lia |].
        rewrite (Hcnt _ Hs), wB_value. lia.
      * rewrite aget_set_other by congruence.
        replace (sz.[rep.[i]] =? s) with false
          by (symmetry; apply Bool.not_true_iff_false; rewrite eqb_spec; congruence).
        rewrite (Hcnt _ Hs). lia.
  - eapply IH; [ | reflexivity | lia | exact Ls | exact Lc | | | ].
    + rewrite <- Hz. apply dec_step. exact Hin.
    + intros ρ Hρ. rewrite Hni, (Hseen ρ Hρ). split.
      * intros Hf j Hj. destruct (Nat.eq_dec j ni) as [-> | Nj]; [| apply Hf; lia].
        rewrite Eni. intros E. subst ρ.
        apply Bool.not_true_iff_false in Ef. apply Ef. apply firstb_iff.
        rewrite Eni. intros i' Hi' E'. apply (Hf i' Hi'). exact E'.
      * intros Hf j Hj. apply Hf. lia.
    + rewrite Hni, gl_S, Ef. rewrite Hg. lia.
    + intros s Hs. rewrite Hni, cntl_S, Ef. simpl andb. rewrite (Hcnt _ Hs). lia.
Qed.

End Tally.

(* ------------------------------------------------------------------ *)
(* The output table                                                    *)
(* ------------------------------------------------------------------ *)

Lemma plength_set : forall (t : array (int * int)) (i : int) (b : int * int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set (int * int) t i b). Qed.

Lemma pget_set_same : forall (t : array (int * int)) (i : int) (b : int * int),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same (int * int) t i b H). Qed.

Lemma pget_set_other : forall (t : array (int * int)) (i j : int) (b : int * int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other (int * int) t i j b H). Qed.

Lemma ltb0_tN : forall v : int, (0 <? v) = (0 <? tN v)%N.
Proof.
  intros v. apply Bool.eq_iff_eq_true. rewrite ltb_spec, N.ltb_lt.
  change (φ 0) with 0%Z. rewrite <- tN_Z. lia.
Qed.

Section Output.

Variables (n : int) (cnt : array int).
Hypothesis Hn : (2 <= (φ n) <= 10000)%Z.

Definition C (s : N) : N := tN (cnt.[of_Z (Z.of_N s)]).

Definition ds (m : nat) : list N := map (fun i => (tN n - N.of_nat i)%N) (seq 0 m).

Definition Tl (m : nat) : list (N * N) :=
  map (fun s => (s, C s)) (filter (fun s => (0 <? C s)%N) (ds m)).

Lemma Tl_S : forall m, Tl (S m) =
  Tl m ++ (if (0 <? C (tN n - N.of_nat m))%N
           then [(tN n - N.of_nat m, C (tN n - N.of_nat m))%N] else []).
Proof.
  intros m. unfold Tl, ds. rewrite seq_S, map_app, filter_app, map_app. simpl.
  destruct (0 <? C (tN n - N.of_nat m))%N; reflexivity.
Qed.

Lemma Tl_len : forall m, (List.length (Tl m) <= m)%nat.
Proof.
  intros m. unfold Tl, ds. rewrite length_map.
  etransitivity; [apply filter_length_le |]. rewrite length_map, length_seq. lia.
Qed.

Lemma Tl_prefix : forall m d, exists rest, Tl (m + d) = Tl m ++ rest.
Proof.
  intros m d. induction d as [| d [rest IH]].
  - exists []. rewrite Nat.add_0_r, app_nil_r. reflexivity.
  - rewrite Nat.add_succ_r, Tl_S, IH, <- app_assoc. eexists. reflexivity.
Qed.

(* the step at index i : size n - i *)
Lemma step_size : forall i : int, ((φ i) < (φ n))%Z ->
  tN (n - i) = (tN n - N.of_nat (Z.to_nat (φ i)))%N /\
  C (tN (n - i)) = tN (cnt.[n - i]).
Proof.
  intros i Hi. pose proof (to_Z_bounded i).
  assert (E : tN (n - i) = (tN n - N.of_nat (Z.to_nat (φ i)))%N).
  { apply N2Z.inj. rewrite tN_Z, N2Z.inj_sub, tN_Z by (apply N2Z.inj_le; rewrite tN_Z; lia).
    rewrite sub_spec, Z.mod_small by lia. lia. }
  split; [exact E |]. unfold C. rewrite of_tN. reflexivity.
Qed.

Lemma countd_spec : forall z i d H, gap n i = z -> ((φ i) <= (φ n))%Z ->
  (φ d) = Z.of_nat (List.length (Tl (Z.to_nat (φ i)))) ->
  (φ (countd n i cnt d H)) = Z.of_nat (List.length (Tl (Z.to_nat (φ n)))).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i d H Hz Hi Hd. rewrite countd_eq.
  destruct (bdec (i <? n)) as [Hin | Hin].
  2:{ rewrite <- Bool.not_true_iff_false, ltb_spec in Hin.
      replace (φ n) with (φ i) by lia. exact Hd. }
  pose proof Hin as Hin'. rewrite ltb_spec in Hin'.
  pose proof (to_Z_bounded i) as Bi.
  assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  assert (Hni : Z.to_nat (φ (i + 1)) = S (Z.to_nat (φ i))) by lia.
  destruct (step_size i Hin') as [Es Ec].
  eapply IH; [ | reflexivity | lia | ].
  - rewrite <- Hz. apply dec_step. exact Hin.
  - rewrite Hni, Tl_S, length_app, <- Es, Ec, <- ltb0_tN.
    pose proof (Tl_len (Z.to_nat (φ i))).
    destruct (0 <? cnt.[n - i]); simpl.
    + rewrite add_spec, Z.mod_small; change (φ 1) with 1%Z; [lia |].
      rewrite wB_value. lia.
    + lia.
Qed.

Lemma fill_spec : forall (D : int), (φ D) = Z.of_nat (List.length (Tl (Z.to_nat (φ n)))) ->
  forall z i j out H, gap n i = z -> ((φ i) <= (φ n))%Z ->
  PArray.length out = D ->
  (φ j) = Z.of_nat (List.length (Tl (Z.to_nat (φ i)))) ->
  (forall m, (m < List.length (Tl (Z.to_nat (φ i))))%nat ->
     (tN (fst (out.[of_nat m])), tN (snd (out.[of_nat m])))
     = nth m (Tl (Z.to_nat (φ i))) (0%N, 0%N)) ->
  PArray.length (fill n i j cnt out H) = D /\
  (forall m, (m < List.length (Tl (Z.to_nat (φ n))))%nat ->
     (tN (fst ((fill n i j cnt out H).[of_nat m])),
      tN (snd ((fill n i j cnt out H).[of_nat m])))
     = nth m (Tl (Z.to_nat (φ n))) (0%N, 0%N)).
Proof.
  intros D HD z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i j out H Hz Hi Lo Hj Hc. rewrite fill_eq.
  destruct (bdec (i <? n)) as [Hin | Hin].
  2:{ rewrite <- Bool.not_true_iff_false, ltb_spec in Hin.
      replace (φ n) with (φ i) by lia. split; [exact Lo | exact Hc]. }
  pose proof Hin as Hin'. rewrite ltb_spec in Hin'.
  pose proof (to_Z_bounded i) as Bi.
  assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  assert (Hni : Z.to_nat (φ (i + 1)) = S (Z.to_nat (φ i))) by lia.
  destruct (step_size i Hin') as [Es Ec].
  set (ni := Z.to_nat (φ i)) in *.
  destruct (Tl_prefix (S ni) (Z.to_nat (φ n) - S ni)) as [rest Hrest].
  replace (S ni + (Z.to_nat (φ n) - S ni))%nat with (Z.to_nat (φ n)) in Hrest by lia.
  cbv zeta. rewrite ltb0_tN, <- Ec.
  pose proof (Tl_S ni) as HS. rewrite <- Es in HS.
  destruct (0 <? C (tN (n - i)))%N eqn:Ep.
  - assert (Hjl : ((φ j) < (φ D))%Z).
    { rewrite HD, Hrest, HS, Hj, !length_app. simpl. lia. }
    assert (Hjb : (j <? PArray.length out) = true) by (rewrite ltb_spec, Lo; exact Hjl).
    eapply IH; [ | reflexivity | lia | rewrite plength_set; exact Lo | | ].
    + rewrite <- Hz. apply dec_step. exact Hin.
    + rewrite Hni, HS, length_app. simpl. rewrite add_spec, Z.mod_small;
        change (φ 1) with 1%Z; [lia |].
      pose proof (to_Z_bounded D). rewrite wB_value in *. lia.
    + intros m Hm. rewrite Hni, HS in Hm |- *. rewrite length_app in Hm. simpl in Hm.
      destruct (Nat.eq_dec m (List.length (Tl ni))) as [-> | Nm].
      * assert (Ej : of_nat (List.length (Tl ni)) = j).
        { apply to_Z_inj. rewrite phi_of_nat; [lia |].
          pose proof (to_Z_bounded j). lia. }
        rewrite Ej, pget_set_same by exact Hjb.
        rewrite app_nth2 by lia. rewrite Nat.sub_diag. simpl.
        rewrite Ec, Es. reflexivity.
      * assert (Ne : j <> of_nat m).
        { intros E. apply Nm. apply Nat2Z.inj. rewrite <- Hj, E.
          rewrite phi_of_nat; [reflexivity |]. pose proof (to_Z_bounded j). lia. }
        rewrite pget_set_other by exact Ne. rewrite app_nth1 by lia. apply Hc. lia.
  - eapply IH; [ | reflexivity | lia | exact Lo | | ].
    + rewrite <- Hz. apply dec_step. exact Hin.
    + rewrite Hni, HS, app_nil_r. exact Hj.
    + rewrite Hni, HS, app_nil_r. exact Hc.
Qed.

Lemma ds_sorted : forall m st, (st + m <= N.to_nat (tN n))%nat ->
  StronglySorted (fun u v => (v < u)%N)
    (map (fun i => (tN n - N.of_nat i)%N) (seq st m)).
Proof.
  intros m. induction m as [| m IH]; intros st Hm; simpl; constructor.
  - apply IH. lia.
  - apply Forall_forall. intros v Hv. apply in_map_iff in Hv as [i [<- Hi]].
    apply in_seq in Hi. lia.
Qed.

Lemma sorted_filter : forall {A} (R : A -> A -> Prop) f l,
  StronglySorted R l -> StronglySorted R (filter f l).
Proof.
  intros A R f l H. induction H as [| x l Hl IH Hf]; simpl; [constructor |].
  destruct (f x); [| exact IH]. constructor; [exact IH |].
  apply Forall_forall. intros y Hy. apply filter_In in Hy as [Hy _].
  rewrite Forall_forall in Hf. apply Hf. exact Hy.
Qed.

Lemma Tl_sorted : StronglySorted (fun e f => (fst f < fst e)%N) (Tl (Z.to_nat (φ n))).
Proof.
  unfold Tl.
  assert (H : StronglySorted (fun u v => (v < u)%N)
                (filter (fun s => (0 <? C s)%N) (ds (Z.to_nat (φ n))))).
  { apply sorted_filter. apply ds_sorted. unfold tN. lia. }
  induction H as [| x l Hl IH Hf]; simpl; constructor; [exact IH |].
  rewrite Forall_forall in Hf |- *. intros y Hy. apply in_map_iff in Hy as [s [<- Hs]].
  simpl. apply Hf. exact Hs.
Qed.

Lemma Tl_in : forall s k, In (s, k) (Tl (Z.to_nat (φ n))) <->
  (1 <= s <= tN n)%N /\ (0 < C s)%N /\ k = C s.
Proof.
  intros s k. unfold Tl, ds. rewrite in_map_iff. split.
  - intros [s' [E Hs']]. injection E as <- <-.
    apply filter_In in Hs' as [Hs' Hp]. apply N.ltb_lt in Hp.
    apply in_map_iff in Hs' as [i [<- Hi]]. apply in_seq in Hi.
    unfold tN in *. split; [lia | split; [exact Hp | reflexivity]].
  - intros [Hs [Hp ->]]. exists s. split; [reflexivity |].
    apply filter_In. split; [| apply N.ltb_lt; exact Hp].
    apply in_map_iff. exists (N.to_nat (tN n - s)). split; [unfold tN in *; lia |].
    apply in_seq. unfold tN in *. lia.
Qed.

End Output.

(* ------------------------------------------------------------------ *)
(* From the final state to the spec                                    *)
(* ------------------------------------------------------------------ *)

Lemma card_unique : forall P k1 k2, card P k1 -> card P k2 -> k1 = k2.
Proof.
  intros P k1 k2 [l1 [N1 [I1 <-]]] [l2 [N2 [I2 <-]]].
  assert (A : (List.length l1 <= List.length l2)%nat)
    by (apply NoDup_incl_length; [exact N1 |]; intros x Hx; apply I2, I1, Hx).
  assert (B : (List.length l2 <= List.length l1)%nat)
    by (apply NoDup_incl_length; [exact N2 |]; intros x Hx; apply I1, I2, Hx).
  unfold len. f_equal. lia.
Qed.

Lemma cntl_pos : forall rep sz si m, (0 < cntl rep sz si m)%nat ->
  exists j, (j < m)%nat /\ firstb rep j = true /\ szof rep sz j = si.
Proof.
  intros rep sz si m H. unfold cntl in H.
  destruct (filter (fun j => andb (firstb rep j) (szof rep sz j =? si)) (seq 0 m))
    as [| j l] eqn:E; [simpl in H; lia |].
  assert (Hj : In j (filter (fun j => andb (firstb rep j) (szof rep sz j =? si)) (seq 0 m)))
    by (rewrite E; left; reflexivity).
  apply filter_In in Hj as [Hj Hb]. apply andb_prop in Hb as [Hb1 Hb2].
  apply in_seq in Hj. apply eqb_spec in Hb2. exists j. split; [lia | auto].
Qed.

Section Final.

Variables (n : int) (rep nxt tl sz : array int) (es : list (N * N)).
Hypothesis Hn : (2 <= (φ n) <= 10000)%Z.
Hypothesis D : DInv n rep nxt tl sz.
Hypothesis G : GInv n rep es.

Let nn := Z.to_nat (φ n).

Lemma F_nat : forall j, (j < nn)%nat ->
  F n rep (N.of_nat j) = tN (rep.[of_nat j]) /\ (tN (rep.[of_nat j]) < tN n)%N.
Proof.
  intros j Hj. assert (Hjn : (N.of_nat j < tN n)%N) by (unfold nn, tN in *; lia).
  destruct (F_lt n rep (N.of_nat j) (d_rng _ _ _ _ _ D) Hjn) as [E B].
  rewrite nat_N_Z in E, B. split; assumption.
Qed.

Lemma of_nat_lt : forall j, (j < nn)%nat -> ((φ (of_nat j)) < (φ n))%Z.
Proof.
  intros j Hj. rewrite phi_of_nat; [unfold nn in Hj; lia |].
  rewrite wB_value. unfold nn in Hj. lia.
Qed.

Lemma leader_iff : forall j, (j < nn)%nat ->
  (leader (tN n) es (N.of_nat j) <-> firstb rep j = true).
Proof.
  intros j Hj. split.
  - intros [_ Hmin]. apply (firstb_iff n). intros i Hi E.
    assert (Hs : same_group es (N.of_nat j) (N.of_nat i)).
    { apply G. rewrite (proj1 (F_nat j Hj)), (proj1 (F_nat i ltac:(lia))), E.
      reflexivity. }
    apply Hmin in Hs. lia.
  - intros Hf. split; [unfold nn, tN in *; lia |].
    intros q Hq. apply G in Hq. rewrite (proj1 (F_nat j Hj)) in Hq.
    pose proof (proj2 (F_nat j Hj)) as Bj.
    destruct (N.ltb_spec q (tN n)) as [Hqn | Hqn].
    + set (i := N.to_nat q). replace q with (N.of_nat i) in * by (unfold i; lia).
      assert (Hi : (i < nn)%nat) by (unfold nn, tN in *; lia).
      rewrite (proj1 (F_nat i Hi)), tN_eq_iff in Hq.
      destruct (Nat.lt_ge_cases i j) as [Lt | Ge]; [| lia].
      exfalso. rewrite (firstb_iff n) in Hf. exact (Hf i Lt (eq_sym Hq)).
    + rewrite F_ge in Hq by exact Hqn. lia.
Qed.

Lemma gsize : forall j, (j < nn)%nat ->
  group_size (tN n) es (N.of_nat j) (tN (szof rep sz j)) /\
  (1 <= (φ (szof rep sz j)) <= (φ n))%Z.
Proof.
  intros j Hj. pose proof (of_nat_lt j Hj) as Hjn.
  set (ρ := rep.[of_nat j]).
  pose proof (d_rng _ _ _ _ _ D _ Hjn) as Hρ. pose proof (d_idem _ _ _ _ _ D _ Hjn) as Iρ.
  fold ρ in Hρ, Iρ.
  destruct (d_list _ _ _ _ _ D ρ Hρ Iρ) as [L HL].
  pose proof (mlist_size n Hn rep nxt tl sz ρ L HL) as Bs.
  destruct HL as (_ & _ & Hnd & Hin & _ & Hlen).
  split; [| exact Bs].
  exists (map tN L). split; [| split].
  - apply NoDup_map_NoDup_ForallPairs; [| exact Hnd].
    intros u v _ _. apply tN_inj.
  - intros x. rewrite in_map_iff. split.
    + intros [v [<- Hv]]. apply Hin in Hv as [Hv1 Hv2]. split.
      * apply N2Z.inj_lt. rewrite !tN_Z. exact Hv1.
      * apply G. rewrite (proj1 (F_nat j Hj)).
        assert (Hvn : (tN v < tN n)%N) by (apply N2Z.inj_lt; rewrite !tN_Z; exact Hv1).
        rewrite (proj1 (F_lt n rep (tN v) (d_rng _ _ _ _ _ D) Hvn)), of_tN, Hv2.
        reflexivity.
    + intros [Hx Hs]. apply G in Hs. rewrite (proj1 (F_nat j Hj)) in Hs.
      rewrite (proj1 (F_lt n rep x (d_rng _ _ _ _ _ D) Hx)), tN_eq_iff in Hs.
      exists (of_Z (Z.of_N x)). split.
      * apply N2Z.inj. rewrite tN_Z, (phi_ofN n x Hx). reflexivity.
      * apply Hin. split; [rewrite (phi_ofN n x Hx), <- tN_Z; lia | symmetry; exact Hs].
  - unfold len. rewrite length_map. unfold szof. fold ρ.
    apply N2Z.inj. rewrite tN_Z, <- Hlen. lia.
Qed.

Lemma groups_count : num_groups (tN n) es (N.of_nat (gl rep nn)).
Proof.
  exists (map N.of_nat (filter (firstb rep) (seq 0 nn))). split; [| split].
  - apply NoDup_map_NoDup_ForallPairs.
    + intros u v _ _. apply Nat2N.inj.
    + apply NoDup_filter, seq_NoDup.
  - intros x. rewrite in_map_iff. split.
    + intros [j [<- Hj]]. apply filter_In in Hj as [Hj Hf]. apply in_seq in Hj.
      apply leader_iff; [lia | exact Hf].
    + intros Hl. pose proof (proj1 Hl) as Hx.
      exists (N.to_nat x). split; [lia |].
      assert (Hxn : (N.to_nat x < nn)%nat) by (unfold nn, tN in *; lia).
      apply filter_In. split; [apply in_seq; lia |].
      apply leader_iff; [exact Hxn |]. rewrite N2Nat.id. exact Hl.
  - unfold len, gl. rewrite length_map. reflexivity.
Qed.

Lemma sizes_count : forall s : N, (s <= tN n)%N ->
  num_groups_of_size (tN n) es s (N.of_nat (cntl rep sz (of_Z (Z.of_N s)) nn)).
Proof.
  intros s Hs.
  assert (Hsi : tN (of_Z (Z.of_N s)) = s).
  { apply N2Z.inj. rewrite tN_Z, of_Z_spec, Z.mod_small; [reflexivity |].
    pose proof (tN_Z n). rewrite wB_value. lia. }
  set (si := of_Z (Z.of_N s)) in *.
  exists (map N.of_nat (filter (fun j => andb (firstb rep j) (szof rep sz j =? si))
                          (seq 0 nn))).
  split; [| split].
  - apply NoDup_map_NoDup_ForallPairs.
    + intros u v _ _. apply Nat2N.inj.
    + apply NoDup_filter, seq_NoDup.
  - intros x. rewrite in_map_iff. split.
    + intros [j [<- Hj]]. apply filter_In in Hj as [Hj Hf]. apply in_seq in Hj.
      apply andb_prop in Hf as [Hf1 Hf2]. apply eqb_spec in Hf2.
      split; [apply leader_iff; [lia | exact Hf1] |].
      rewrite <- Hsi, <- Hf2. apply gsize. lia.
    + intros [Hl Hg]. pose proof (proj1 Hl) as Hx.
      assert (Hxn : (N.to_nat x < nn)%nat) by (unfold nn, tN in *; lia).
      exists (N.to_nat x). split; [lia |].
      apply filter_In. split; [apply in_seq; lia |].
      apply andb_true_intro. split; [apply leader_iff; [exact Hxn |]; rewrite N2Nat.id; exact Hl |].
      apply eqb_spec. apply tN_inj. rewrite Hsi.
      apply (card_unique _ _ _ (proj1 (gsize _ Hxn))). rewrite N2Nat.id. exact Hg.
  - unfold len, cntl. rewrite length_map. reflexivity.
Qed.

Lemma sizes_big : forall s k, (tN n < s)%N ->
  num_groups_of_size (tN n) es s k -> k = 0%N.
Proof.
  intros s k Hs Hk.
  assert (H0 : num_groups_of_size (tN n) es s 0).
  { exists []. split; [constructor | split; [| reflexivity]].
    intros x. split; [intros [] |]. intros [Hl Hg]. exfalso.
    pose proof (proj1 Hl) as Hx.
    assert (Hxn : (N.to_nat x < nn)%nat) by (unfold nn, tN in *; lia).
    destruct (gsize _ Hxn) as [Hg' Bs]. rewrite N2Nat.id in Hg'.
    pose proof (card_unique _ _ _ Hg Hg') as E. subst s.
    assert (Z.of_N (tN (szof rep sz (N.to_nat x))) <= Z.of_N (tN n))%Z
      by (rewrite !tN_Z; lia). lia. }
  exact (card_unique _ _ _ Hk H0).
Qed.

End Final.

Lemma pmake_length : forall n (v : int * int), (0 <= (φ n) <= 4194303)%Z ->
  PArray.length (PArray.make n v) = n.
Proof.
  intros n v Hn.
  transitivity (if n <=? PArray.max_length then n else PArray.max_length);
    [exact (length_make (int * int) n v) |].
  replace (n <=? PArray.max_length) with true; [reflexivity |].
  symmetry. rewrite leb_spec. change (φ PArray.max_length) with 4194303%Z. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma chatter_impl_correct :
  forall (nN rN aN bN cN : N) (n r a b c : uint),
  valid_input nN rN aN bN cN ->
  repr n nN -> repr r rN -> repr a aN -> repr b bN -> repr c cN ->
  exists o : N * list (N * N),
    repr (chatter_impl n r a b c) o /\ chatter_spec nN rN aN bN cN o.
Proof.
  intros nN rN aN bN cN n r a b c Hv Rn Rr Ra Rb Rc.
  change (tN n = nN) in Rn. change (tN r = rN) in Rr. change (tN a = aN) in Ra.
  change (tN b = bN) in Rb. change (tN c = cN) in Rc.
  subst nN rN aN bN cN.
  destruct Hv as [Vn Vr Va Vb Vc [es0 Hes0]].
  assert (Hn : (2 <= (φ n) <= 10000)%Z) by (unfold tN in Vn; lia).
  assert (Hr : ((φ r) <= 10000)%Z) by (unfold tN in Vr; lia).
  assert (Ha : (1 <= (φ a) <= 10000)%Z) by (unfold tN in Va; lia).
  assert (Hb : (1 <= (φ b) <= 10000)%Z) by (unfold tN in Vb; lia).
  assert (Hc : (2 <= (φ c) <= 50000)%Z) by (unfold tN in Vc; lia).
  clear Vn Vr Va Vb Vc.
  unfold chatter_impl.
  (* init *)
  pose proof (init_spec n Hn _ 0 (PArray.make n 0) (PArray.make n 0)
                (Zwf_well_founded 0 (gap n 0)) eq_refl
                (make_length n 0 ltac:(lia)) (make_length n 0 ltac:(lia))
                ltac:(change (φ 0) with 0%Z; lia)
                ltac:(intros j Hj; change (φ 0) with 0%Z in Hj;
                      pose proof (to_Z_bounded j); lia)) as [I1 [I2 I3]].
  destruct (init n 0 (PArray.make n 0) (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)))
    as [rep0 tl0] eqn:Ei.
  cbn [fst snd] in I1, I2, I3.
  destruct (start_spec n Hn rep0 tl0 I1 I2 I3) as [D0 G0].
  (* sim *)
  assert (Hk : (φ n) = Z.of_nat (N.to_nat (tN n))) by (unfold tN; lia).
  pose proof (fun es (Hes : day (tN n) (tN r) (tN a) (tN b) (tN c) es) =>
                sim_spec n a b c Hn Ha Hb Hc _ _ es Hes r n rep0 (PArray.make n 0) tl0
                  (PArray.make n 1) (Zwf_well_founded 0 (φ n)) [] eq_refl
                  ltac:(lia) Hk D0 G0) as SS.
  destruct (sim n a b c r n rep0 (PArray.make n 0) tl0 (PArray.make n 1)
              (Zwf_well_founded 0 (φ n))) as [rep sz] eqn:Es.
  cbn [fst snd] in SS.
  destruct (SS es0 Hes0) as [[nxt1 [tl1 D1]] _].
  assert (Hrng := d_rng _ _ _ _ _ D1).
  assert (Hsz : forall p, ((φ p) < (φ n))%Z -> (1 <= (φ (sz.[rep.[p]])) <= (φ n))%Z).
  { intros p Hp. destruct (d_list _ _ _ _ _ D1 (rep.[p]) (Hrng p Hp)
                             (d_idem _ _ _ _ _ D1 p Hp)) as [L HL].
    exact (mlist_size n Hn _ _ _ _ _ _ HL). }
  (* tally *)
  pose proof (tally_spec n rep sz Hn Hrng Hsz _ 0 (PArray.make n 0) (PArray.make (n + 1) 0) 0
                (Zwf_well_founded 0 (gap n 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; lia)
                (make_length n 0 ltac:(lia))
                (make_length (n + 1) 0 ltac:(sia))
                ltac:(intros ρ _; rewrite aget_make; split; [intros _ j Hj; simpl in Hj; lia
                                                           | intros _; reflexivity])
                ltac:(reflexivity)
                ltac:(intros s _; rewrite aget_make; reflexivity)) as [T1 [T2 T3]].
  destruct (tally n 0 rep sz (PArray.make n 0) (PArray.make (n + 1) 0) 0
              (Zwf_well_founded 0 (gap n 0))) as [g cnt] eqn:Et.
  cbn [fst snd] in T1, T2, T3.
  (* the table *)
  pose proof (countd_spec n cnt Hn _ 0 0 (Zwf_well_founded 0 (gap n 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; lia) ltac:(reflexivity)) as CD.
  set (d := countd n 0 cnt 0 (Zwf_well_founded 0 (gap n 0))) in *.
  assert (Bd : (0 <= (φ d) <= 10000)%Z).
  { rewrite CD. pose proof (Tl_len n cnt (Z.to_nat (φ n))). lia. }
  destruct (fill_spec n cnt Hn d CD _ 0 0 (PArray.make d (0, 0))
              (Zwf_well_founded 0 (gap n 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia)
              (pmake_length d (0, 0) ltac:(lia))
              ltac:(reflexivity)
              ltac:(intros m Hm; simpl in Hm; lia)) as [F1 F2].
  set (out := fill n 0 0 cnt (PArray.make d (0, 0)) (Zwf_well_founded 0 (gap n 0))) in *.
  set (nn := Z.to_nat (φ n)) in *.
  exists (tN g, Tl n cnt nn). split.
  - split; [reflexivity |]. cbn [fst snd]. split.
    + rewrite <- CD. exact (f_equal to_Z (eq_sym F1)).
    + intros m Hm. exists (nth m (Tl n cnt nn) (0%N, 0%N)).
      split; [apply nth_error_nth'; exact Hm |].
      pose proof (F2 m Hm) as E.
      split; [exact (f_equal fst E) | exact (f_equal snd E)].
  - unfold chatter_spec. intros es Hes.
    destruct (SS es Hes) as [[nxt2 [tl2 D2]] G2].
    assert (Hg : tN g = N.of_nat (gl rep nn)) by (apply N2Z.inj; rewrite tN_Z, T1; lia).
    assert (HC : forall s, (s <= tN n)%N ->
                 C cnt s = N.of_nat (cntl rep sz (of_Z (Z.of_N s)) nn)).
    { intros s Hs. unfold C. apply N2Z.inj. rewrite tN_Z, T3; [lia |].
      rewrite of_Z_spec, Z.mod_small; [rewrite <- tN_Z; lia |].
      pose proof (tN_Z n). rewrite wB_value. lia. }
    split; [rewrite Hg; exact (groups_count n rep nxt2 tl2 sz es Hn D2 G2) |].
    split; [exact (Tl_sorted n cnt) |].
    intros s k. pose proof (Tl_in n cnt Hn s k) as TI. fold nn in TI. rewrite TI. split.
    + intros [Hs [Hp ->]]. split; [exact Hp |].
      rewrite HC by apply Hs. apply (sizes_count n rep nxt2 tl2 sz es Hn D2 G2). apply Hs.
    + intros [Hk0 Hgs]. destruct (N.le_gt_cases s (tN n)) as [Hs | Hs].
      * pose proof (card_unique _ _ _ Hgs (sizes_count n rep nxt2 tl2 sz es Hn D2 G2 s Hs))
          as Ek.
        rewrite HC by exact Hs. subst k. fold nn in Hk0, Hgs |- *.
        destruct (cntl_pos rep sz (of_Z (Z.of_N s)) nn ltac:(lia)) as [j [Hj [_ Hsj]]].
        destruct (gsize n rep nxt2 tl2 sz es Hn D2 G2 j Hj) as [_ Bj].
        rewrite Hsj, of_Z_spec, Z.mod_small in Bj
          by (pose proof (tN_Z n); rewrite wB_value; lia).
        split; [lia |]. split; [lia | reflexivity].
      * exfalso. pose proof (sizes_big n rep nxt2 tl2 sz es Hn D2 G2 s k Hs Hgs). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition chatter : uint -> uint -> uint -> uint -> uint -> uint * array (uint * uint)
  := chatter_impl.
Elpi complexity chatter.

Definition chatter_correct :
  forall (n r a b c : N) (xn xr xa xb xc : uint),
  valid_input n r a b c ->
  repr xn n -> repr xr r -> repr xa a -> repr xb b -> repr xc c ->
  exists o : N * list (N * N),
    repr (chatter xn xr xa xb xc) o /\ chatter_spec n r a b c o
  := chatter_impl_correct.

(* ------------------------------------------------------------------ *)
(* Cost                                                                *)
(* ------------------------------------------------------------------ *)

(* The cost translation (Elpi complexity, callee first, right after each
   definition): sumbool, bdec, nx, redraw, relabel, merge, union, sim,
   init, tally, countd, fill, chatter_impl, chatter.  Each loop is bounded
   on its twin by induction on a nat bound of its measure:
     redraw   <= bud * 70 + 10            relabel <= cnt * 30 + 10
     merge    <= sz[small] * 30 + 60      union   <= usmall * 30 + 100
     sim      <= k * (c * 70 + 300) + pot * 30 + 10   (amortised)
     init <= (n-i)*30+10, tally <= (n-i)*60+10, countd <= (n-i)*40+10,
     fill <= (n-i)*50+10
   The unions are amortised with the potential [pot]: every person holds
   log2 n - log2 (size of its group) units; a merge re-points the members
   of the smaller group, whose size at least doubles, so each of them
   gives up a unit (merge_pot, union_pot over the invariant DInv); pot is
   at most n log2 n (pot_le). *)

#[local] Arguments Uint63.to_Z : simpl never.
Arguments gap : simpl never.
Arguments nx : simpl never.
Arguments redraw : simpl never.
Arguments relabel : simpl never.
Arguments merge : simpl never.
Arguments union : simpl never.
Arguments sim : simpl never.
Arguments init : simpl never.
Arguments tally : simpl never.
Arguments countd : simpl never.
Arguments fill : simpl never.

Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; cbn; lia. Qed.

Lemma nx_time a aC b bC c cC r rC :
  (cost (extract (extract (extract (nx_cost stepsCM a aC) b bC) c cC) r rC) <= 10)%nat.
Proof. unfold nx_cost. cost_simpl. lia. Qed.

Ltac zero_partials :=
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch T with forall _, _ => change (@cost T X) with 0%nat end end.

Ltac set_simpl :=
  repeat match goal with
  | |- context [cost (extract (extract (extract (set_cost ?a ?b ?c) ?d ?e) ?f ?g) ?h ?i)] =>
      change (cost (extract (extract (extract (set_cost a b c) d e) f g) h i)) with 1%nat
  end.
Ltac make_simpl :=
  repeat match goal with
  | |- context [cost (extract (extract (make_cost ?a ?b ?c) ?d ?e) ?f ?g)] =>
      change (cost (extract (extract (make_cost a b c) d e) f g)) with 1%nat
  end.

Ltac gen_nx := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (nx_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?r ?rC =>
    let Hc := fresh "Hnx" in
    pose proof (nx_time a aC b bC c cC r rC : (@cost T X <= _)%nat) as Hc;
    revert Hc; generalize (@cost T X); intros ? Hc end end.

Lemma cnt_S (k : int) : (0 <? k) = true -> Z.to_nat (φ k) = S (Z.to_nat (φ (k - 1))).
Proof.
  intros Hx. apply ltb_spec in Hx. change (φ 0) with 0%Z in Hx.
  assert (E1 : (φ (k - 1) = φ k - 1)%Z) by (zify; Z.to_euclidean_division_equations; lia).
  rewrite E1. lia.
Qed.

Lemma redraw_time n nC a aC b bC c cC r rC bud budC H HC :
  (cost (extract (extract (extract (extract (extract (extract (redraw_cost stepsCM n nC) a aC) b bC) c cC) r rC) bud budC) H HC)
     <= Z.to_nat (φ bud) * 70 + 10)%nat.
Proof.
  unfold redraw_cost. cbn.
  match goal with |- context [@cost ?T (?G n nC a aC b bC c cC r rC bud budC H HC)] =>
    assert (HG : forall N r rC bud budC H HC, (Z.to_nat (φ bud) <= N)%nat ->
       (cost (G n nC a aC b bC c cC r rC bud budC H HC) <= Z.to_nat (φ bud) * 70 + 10)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros r' rC' bud' budC' [g] HC' HN.
    cost_simpl.
    pose proof (bdec_time (0 <? bud') (bool_w (0 <? bud'))) as HB.
    cost_destruct (bdec (0 <? bud')); cost_simpl.
    - zero_partials. gen_nx.
      assert (E : Z.to_nat (φ bud') = S (Z.to_nat (φ (bud' - 1))))
        by (match goal with Hx : (0 <? bud') = true |- _ => exact (cnt_S _ Hx) end).
      assert (HN2 : (Z.to_nat (φ (bud' - 1)) < N)%nat) by lia.
      cost_destruct (nx a b c r' mod n =? nx a b c (nx a b c r') mod n); cost_simpl.
      + zero_partials.
        match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?r2 ?rC2 ?u2 ?uC2 ?h ?hc)] =>
          pose proof (IH _ HN2 r2 rC2 u2 uC2 h hc (le_n _)
            : (@cost T (G' a1 a2 a3 a4 a5 a6 a7 a8 r2 rC2 u2 uC2 h hc) <= _)%nat) as HI;
          revert HI; generalize (@cost T (G' a1 a2 a3 a4 a5 a6 a7 a8 r2 rC2 u2 uC2 h hc)); intros ? HI
        end.
        lia.
      + lia.
    - lia. }
  match goal with |- context [@cost ?T (?G n nC a aC b bC c cC r rC bud budC H HC)] =>
    exact (HG _ r rC bud budC H HC (le_n _) : (@cost T (G n nC a aC b bC c cC r rC bud budC H HC) <= _)%nat) end.
Qed.

Lemma relabel_time nxt nxtC big bigC q qC cnt cntC rep repC H HC :
  (cost (extract (extract (extract (extract (extract (relabel_cost stepsCM nxt nxtC) big bigC) q qC) cnt cntC) rep repC) H HC)
     <= Z.to_nat (φ cnt) * 30 + 10)%nat.
Proof.
  unfold relabel_cost. cbn.
  match goal with |- context [@cost ?T (?G nxt nxtC big bigC q qC cnt cntC rep repC H HC)] =>
    assert (HG : forall N q qC cnt cntC rep repC H HC, (Z.to_nat (φ cnt) <= N)%nat ->
       (cost (G nxt nxtC big bigC q qC cnt cntC rep repC H HC) <= Z.to_nat (φ cnt) * 30 + 10)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros q' qC' cnt' cntC' rep' repC' [g] HC' HN.
    cost_simpl.
    pose proof (bdec_time (0 <? cnt') (bool_w (0 <? cnt'))) as HB.
    cost_destruct (bdec (0 <? cnt')); cost_simpl.
    - zero_partials.
      assert (E : Z.to_nat (φ cnt') = S (Z.to_nat (φ (cnt' - 1))))
        by (match goal with Hx : (0 <? cnt') = true |- _ => exact (cnt_S _ Hx) end).
      assert (HN2 : (Z.to_nat (φ (cnt' - 1)) < N)%nat) by lia.
      match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?a3 ?a4 ?q2 ?qC2 ?u2 ?uC2 ?r2 ?rC2 ?h ?hc)] =>
        pose proof (IH _ HN2 q2 qC2 u2 uC2 r2 rC2 h hc (le_n _)
          : (@cost T (G' a1 a2 a3 a4 q2 qC2 u2 uC2 r2 rC2 h hc) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' a1 a2 a3 a4 q2 qC2 u2 uC2 r2 rC2 h hc)); intros ? HI
      end.
      set_simpl. lia.
    - lia. }
  match goal with |- context [@cost ?T (?G nxt nxtC big bigC q qC cnt cntC rep repC H HC)] =>
    exact (HG _ q qC cnt cntC rep repC H HC (le_n _) : (@cost T (G nxt nxtC big bigC q qC cnt cntC rep repC H HC) <= _)%nat) end.
Qed.

Ltac gen_relabel := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (relabel_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC =>
    let Hc := fresh "Hrl" in
    pose proof (relabel_time a aC b bC c cC d dC e eC f fC : (@cost T X <= _)%nat) as Hc;
    revert Hc; generalize (@cost T X); intros ? Hc end end.

Lemma merge_time big bigC small smallC rep repC nxt nxtC tl tlC sz szC :
  (cost (extract (extract (extract (extract (extract (merge_cost stepsCM big bigC) small smallC) rep repC) nxt nxtC) tl tlC) sz szC)
     <= Z.to_nat (φ sz.[small]) * 30 + 60)%nat.
Proof.
  unfold merge_cost. cost_simpl. zero_partials. set_simpl. gen_relabel.
  lia.
Qed.

Ltac gen_merge := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (merge_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC =>
    let Hc := fresh "Hmg" in
    pose proof (merge_time a aC b bC c cC d dC e eC f fC : (@cost T X <= _)%nat) as Hc;
    revert Hc; generalize (@cost T X); intros ? Hc end end.

(* the size of the smaller of the two groups a union merges (0 when x and y
   are already together) *)
Definition usmall (x y : int) (rep sz : array int) : nat :=
  if rep.[x] =? rep.[y] then 0
  else if sz.[rep.[y]] <? sz.[rep.[x]] then Z.to_nat (φ sz.[rep.[y]])
  else Z.to_nat (φ sz.[rep.[x]]).

Lemma union_time x xC y yC rep repC nxt nxtC tl tlC sz szC :
  (cost (extract (extract (extract (extract (extract (union_cost stepsCM x xC) y yC) rep repC) nxt nxtC) tl tlC) sz szC)
     <= usmall x y rep sz * 30 + 100)%nat.
Proof.
  unfold union_cost, usmall. cost_simpl. zero_partials.
  cost_destruct (rep.[x] =? rep.[y]); cost_simpl.
  - lia.
  - cost_destruct (sz.[rep.[y]] <? sz.[rep.[x]]); cost_simpl; zero_partials; gen_merge.
    + lia.
    + lia.
Qed.


(* ------------------------------------------------------------------ *)
(* The potential of the weighted unions                                *)
(* ------------------------------------------------------------------ *)

Definition zn (x : int) : nat := Z.to_nat (φ x).

(* every person p < n holds log2 n - log2 (size of its group) units: a
   merge re-points the members of the smaller group, whose size at least
   doubles, so each of them gives up one unit and pays its re-pointing *)
Definition pot (n : int) (rep sz : array int) : nat :=
  list_sum (map (fun i => Nat.log2 (zn n) - Nat.log2 (zn sz.[rep.[of_nat i]]))%nat (seq 0 (zn n))).

Lemma sum_pointwise (l : list nat) (f g : nat -> nat) (h : nat -> bool) :
  (forall i, In i l -> g i + (if h i then 1 else 0) <= f i)%nat ->
  (list_sum (map g l) + List.length (filter h l) <= list_sum (map f l))%nat.
Proof.
  induction l as [|i l IH]; intros Hp; simpl; [lia|].
  specialize (IH (fun j Hj => Hp j (or_intror Hj))).
  pose proof (Hp i (or_introl eq_refl)). destruct (h i); simpl; lia.
Qed.

Lemma sum_le_const (l : list nat) (L : nat) (g : nat -> nat) :
  (list_sum (map (fun i => L - g i)%nat l) <= List.length l * L)%nat.
Proof. induction l as [|i l IH]; simpl; lia. Qed.

Lemma pot_le n rep sz : (pot n rep sz <= zn n * Nat.log2 (zn n))%nat.
Proof.
  unfold pot. pose proof (sum_le_const (seq 0 (zn n)) (Nat.log2 (zn n))
    (fun i => Nat.log2 (zn sz.[rep.[of_nat i]]))) as H.
  rewrite length_seq in H. exact H.
Qed.

Lemma count_small n (Hn : (2 <= φ n <= 10000)%Z) rep nxt tl sz small :
  DInv n rep nxt tl sz -> (φ small < φ n)%Z -> rep.[small] = small ->
  (zn sz.[small] <= List.length (filter (fun i => (rep.[of_nat i] =? small)%uint63) (seq 0 (zn n))))%nat.
Proof.
  intros D Hs Hsr.
  destruct (d_list _ _ _ _ _ D small Hs Hsr) as [Ls (_ & _ & Hnd & Hin & _ & Hz)].
  assert (HM : NoDup (map zn Ls)).
  { apply NoDup_map_NoDup_ForallPairs; [| exact Hnd].
    intros u v _ _ E. apply to_Z_inj. unfold zn in E.
    pose proof (to_Z_bounded u). pose proof (to_Z_bounded v). lia. }
  assert (HI : incl (map zn Ls) (filter (fun i => (rep.[of_nat i] =? small)%uint63) (seq 0 (zn n)))).
  { intros k Hk. apply in_map_iff in Hk as [q [<- Hq]]. apply Hin in Hq as [Hq1 Hq2].
    apply filter_In. split.
    - apply in_seq. unfold zn. pose proof (to_Z_bounded q). lia.
    - unfold zn. rewrite of_nat_phi, Hq2. apply eqb_refl. }
  pose proof (NoDup_incl_length HM HI) as HL. rewrite length_map in HL.
  unfold zn at 1. rewrite <- Hz. lia.
Qed.

Lemma merge_pot n (Hn : (2 <= φ n <= 10000)%Z) rep nxt tl sz big small :
  DInv n rep nxt tl sz -> (φ big < φ n)%Z -> (φ small < φ n)%Z ->
  rep.[big] = big -> rep.[small] = small -> big <> small ->
  (φ sz.[small] <= φ sz.[big])%Z ->
  let res := merge big small rep nxt tl sz in
  (pot n (fst (fst (fst res))) (snd res) + zn sz.[small] <= pot n rep sz)%nat.
Proof.
  intros D Hb Hs Hbr Hsr Hne Hle.
  destruct (merge_spec n Hn rep nxt tl sz big small D Hb Hs Hbr Hsr Hne) as [D' Hh].
  cbv zeta in *.
  set (res := merge big small rep nxt tl sz) in *.
  assert (Esz : snd res = sz.[big <- sz.[big] + sz.[small]]) by reflexivity.
  set (rep' := fst (fst (fst res))) in *. clearbody rep'.
  pose proof (count_small n Hn rep nxt tl sz small D Hs Hsr) as HC.
  destruct (d_list _ _ _ _ _ D big Hb Hbr) as [Lb Mb].
  pose proof (mlist_size n Hn _ _ _ _ _ _ Mb) as Bb.
  destruct (d_list _ _ _ _ _ D small Hs Hsr) as [Ls Ms].
  pose proof (mlist_size n Hn _ _ _ _ _ _ Ms) as Bs.
  assert (Hbig' : rep'.[big] = big).
  { rewrite (Hh big Hb), Hbr. unfold hfun.
    destruct (big =? small) eqn:E; [apply eqb_spec in E; contradiction | reflexivity]. }
  destruct (d_list _ _ _ _ _ D' big Hb Hbig') as [Lb' Mb'].
  pose proof (mlist_size n Hn _ _ _ _ _ _ Mb') as Bb'.
  rewrite Esz in Bb'.
  assert (Lsz : (big <? PArray.length sz) = true)
    by (rewrite ltb_spec, (d_lsz _ _ _ _ _ D); exact Hb).
  rewrite aget_set_same in Bb' by exact Lsz.
  assert (Es : φ (sz.[big] + sz.[small]) = (φ sz.[big] + φ sz.[small])%Z).
  { rewrite add_spec. apply Z.mod_small. rewrite wB_value. lia. }
  rewrite Es in Bb'.
  set (L := Nat.log2 (zn n)).
  set (ss := zn sz.[small]) in *. set (sb := zn sz.[big]).
  assert (Hss : (1 <= ss)%nat) by (unfold ss, zn; lia).
  assert (Hsb : (ss <= sb)%nat) by (unfold ss, sb, zn; lia).
  assert (Hsum : (sb + ss <= zn n)%nat) by (unfold ss, sb, zn; lia).
  assert (Hzs : zn (sz.[big] + sz.[small]) = (sb + ss)%nat) by (unfold sb, ss, zn; rewrite Es; lia).
  assert (HlogL : (Nat.log2 (sb + ss) <= L)%nat) by (apply Nat.log2_le_mono; exact Hsum).
  assert (Hlog2 : (S (Nat.log2 ss) <= Nat.log2 (sb + ss))%nat).
  { rewrite <- Nat.log2_double by lia. apply Nat.log2_le_mono. lia. }
  assert (Hlog3 : (Nat.log2 sb <= Nat.log2 (sb + ss))%nat) by (apply Nat.log2_le_mono; lia).
  unfold pot. rewrite Esz. fold L.
  match goal with |- (list_sum (map ?g ?l) + _ <= list_sum (map ?f _))%nat =>
    assert (HS : (list_sum (map g l) + List.length (filter (fun i => (rep.[of_nat i] =? small)%uint63) l)
                 <= list_sum (map f l))%nat) end.
  2:{ lia. }
  apply sum_pointwise.
  intros i Hi. apply in_seq in Hi.
  assert (Hp : (φ (of_nat i) < φ n)%Z).
  { rewrite phi_of_nat; unfold zn in Hi; [lia | rewrite wB_value; lia]. }
  rewrite (Hh _ Hp). unfold hfun.
  destruct (rep.[of_nat i] =? small) eqn:E.
  + apply eqb_spec in E. rewrite E, aget_set_same by exact Lsz. fold ss.
    rewrite Hzs. lia.
  + destruct (eqs (rep.[of_nat i]) big) as [Eb | Eb].
    * rewrite Eb, aget_set_same by exact Lsz. rewrite Hzs. fold sb. lia.
    * rewrite aget_set_other by (intros F; apply Eb; symmetry; exact F). lia.
Qed.

Lemma union_pot n (Hn : (2 <= φ n <= 10000)%Z) rep nxt tl sz x y :
  DInv n rep nxt tl sz -> (φ x < φ n)%Z -> (φ y < φ n)%Z ->
  let res := union x y rep nxt tl sz in
  (pot n (fst (fst (fst res))) (snd res) + usmall x y rep sz <= pot n rep sz)%nat.
Proof.
  intros D Hx Hy. unfold union, usmall. cbv zeta.
  destruct (rep.[x] =? rep.[y]) eqn:E.
  - cbn [fst snd]. lia.
  - apply eqb_false_neq in E.
    pose proof (d_rng _ _ _ _ _ D x Hx) as Rx. pose proof (d_rng _ _ _ _ _ D y Hy) as Ry.
    pose proof (d_idem _ _ _ _ _ D x Hx) as Ix. pose proof (d_idem _ _ _ _ _ D y Hy) as Iy.
    destruct (sz.[rep.[y]] <? sz.[rep.[x]]) eqn:E2.
    + apply ltb_spec in E2.
      exact (merge_pot n Hn rep nxt tl sz _ _ D Rx Ry Ix Iy E ltac:(lia)).
    + rewrite <- Bool.not_true_iff_false, ltb_spec in E2.
      exact (merge_pot n Hn rep nxt tl sz _ _ D Ry Rx Iy Ix (not_eq_sym E) ltac:(lia)).
Qed.

Lemma redraw_lt n a b c : (0 < φ n)%Z -> forall r bud H,
  let res := redraw n a b c r bud H in
  (φ (snd (fst res)) < φ n)%Z /\ (φ (snd res) < φ n)%Z.
Proof.
  intros Hn.
  assert (HG : forall N r bud H, (Z.to_nat (φ bud) <= N)%nat ->
            let res := redraw n a b c r bud H in
            (φ (snd (fst res)) < φ n)%Z /\ (φ (snd res) < φ n)%Z).
  { induction N as [| N IH]; intros r bud H HN; rewrite redraw_eq;
      destruct (bdec (0 <? bud)) as [Hb | Hb].
    - exfalso. apply ltb_spec in Hb. change (φ 0) with 0%Z in Hb. lia.
    - cbn. change (φ 0) with 0%Z. lia.
    - cbv zeta. destruct (_ =? _).
      + apply IH. rewrite (cnt_S _ Hb) in HN. lia.
      + cbn [fst snd]. rewrite !mod_spec. split; apply Z.mod_pos_bound; exact Hn.
    - cbn. change (φ 0) with 0%Z. lia. }
  intros r bud H. exact (HG _ r bud H (le_n _)).
Qed.

Ltac gen_redraw := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (extract (redraw_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC =>
    let Hc := fresh "Hrd" in
    pose proof (redraw_time a aC b bC c cC d dC e eC f fC g gC : (@cost T X <= _)%nat) as Hc;
    revert Hc; generalize (@cost T X); intros ? Hc end end.
Ltac gen_union := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (union_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC =>
    let Hc := fresh "Hun" in
    pose proof (union_time a aC b bC c cC d dC e eC f fC : (@cost T X <= _)%nat) as Hc;
    revert Hc; generalize (@cost T X); intros ? Hc end end.

Lemma zn_c1 (c : int) : (φ c <= 50000)%Z -> Z.to_nat (φ (c + 1)) = S (zn c).
Proof.
  intros Hc. unfold zn. pose proof (to_Z_bounded c).
  assert (E : φ (c + 1) = (φ c + 1)%Z) by (rewrite add_spec; apply Z.mod_small; rewrite wB_value; change (φ 1) with 1%Z; lia).
  rewrite E. lia.
Qed.

Lemma sim_time n nC a aC b bC c cC r rC k kC rep repC nxt nxtC tl tlC sz szC H HC :
  (2 <= φ n <= 10000)%Z -> (φ c <= 50000)%Z -> DInv n rep nxt tl sz ->
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (sim_cost stepsCM n nC) a aC) b bC) c cC) r rC) k kC) rep repC) nxt nxtC) tl tlC) sz szC) H HC)
     <= Z.to_nat (φ k) * (zn c * 70 + 300) + pot n rep sz * 30 + 10)%nat.
Proof.
  intros Hn Hc.
  unfold sim_cost. cbn.
  match goal with |- context [@cost ?T (?G n nC a aC b bC c cC r rC k kC rep repC nxt nxtC tl tlC sz szC H HC)] =>
    assert (HG : forall N r rC k kC rep repC nxt nxtC tl tlC sz szC H HC, (Z.to_nat (φ k) <= N)%nat ->
       DInv n rep nxt tl sz ->
       (cost (G n nC a aC b bC c cC r rC k kC rep repC nxt nxtC tl tlC sz szC H HC)
          <= Z.to_nat (φ k) * (zn c * 70 + 300) + pot n rep sz * 30 + 10)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros r' rC' k' kC' rep' repC' nxt' nxtC' tl' tlC' sz' szC' [g] HC' HN D.
    cost_simpl.
    pose proof (bdec_time (0 <? k') (bool_w (0 <? k'))) as HB.
    cost_destruct (bdec (0 <? k')); cost_simpl.
    - zero_partials. gen_redraw.
      rewrite (zn_c1 c Hc) in Hrd.
      assert (E : Z.to_nat (φ k') = S (Z.to_nat (φ (k' - 1))))
        by (match goal with Hx : (0 <? k') = true |- _ => exact (cnt_S _ Hx) end).
      assert (HN2 : (Z.to_nat (φ (k' - 1)) < N)%nat) by lia.
      pose proof (redraw_lt n a b c ltac:(lia) r' (c + 1) (Zwf_well_founded 0 (φ (c + 1)))) as RL.
      cbv zeta in RL.
      cost_destruct_witness (redraw n a b c r' (c + 1) (Zwf_well_founded 0 (φ (c + 1)))) as [p pC y yC] eqn:E1.
      destruct pC as [r2 r2C x xC].
      try rewrite E1 in RL. cbn [fst snd] in RL. destruct RL as [Hx Hy].
      cost_simpl. zero_partials. gen_union.
      pose proof (union_pot n Hn rep' nxt' tl' sz' x y D Hx Hy) as UP.
      pose proof (union_spec n Hn rep' nxt' tl' sz' x y D Hx Hy) as [D1 _].
      cbv zeta in UP.
      cost_destruct_witness (union x y rep' nxt' tl' sz') as [q qC s sC] eqn:E2.
      destruct qC as [q2 q2C t tC]. destruct q2C as [rp rpC nx2 nxC2].
      try rewrite E2 in UP. try rewrite E2 in D1. cbn [fst snd] in UP, D1.
      cost_simpl. zero_partials.
      match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?r2 ?rC2 ?k2 ?kC2 ?p2 ?pC2 ?q2 ?qC2 ?t2 ?tC2 ?s2 ?sC2 ?h ?hc)] =>
        pose proof (IH _ HN2 r2 rC2 k2 kC2 p2 pC2 q2 qC2 t2 tC2 s2 sC2 h hc (le_n _) D1
          : (@cost T (G' a1 a2 a3 a4 a5 a6 a7 a8 r2 rC2 k2 kC2 p2 pC2 q2 qC2 t2 tC2 s2 sC2 h hc) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' a1 a2 a3 a4 a5 a6 a7 a8 r2 rC2 k2 kC2 p2 pC2 q2 qC2 t2 tC2 s2 sC2 h hc)); intros ? HI
      end.
      rewrite E. clear -HB Hrd Hun UP HI.
      set (P := pot n rep' sz') in *. set (P' := pot n rp s) in *. set (U := usmall x y rep' sz') in *.
      set (K := Z.to_nat (φ (k' - 1))) in *. set (Z := zn c) in *. clearbody P P' U K Z.
      nia.
    - lia. }
  intros D.
  match goal with |- context [@cost ?T (?G n nC a aC b bC c cC r rC k kC rep repC nxt nxtC tl tlC sz szC H HC)] =>
    exact (HG _ r rC k kC rep repC nxt nxtC tl tlC sz szC H HC (le_n _) D : (@cost T (G n nC a aC b bC c cC r rC k kC rep repC nxt nxtC tl tlC sz szC H HC) <= _)%nat) end.
Qed.


Lemma gap_S (i n : int) : (i <? n) = true -> Z.to_nat (gap n i) = S (Z.to_nat (gap n (i + 1))).
Proof.
  intros Hx. apply ltb_spec in Hx. unfold gap.
  assert (E1 : (φ (i + 1) = φ i + 1)%Z) by (zify; Z.to_euclidean_division_equations; lia).
  rewrite E1. lia.
Qed.

Lemma init_time n nC i iC rep repC tl tlC H HC :
  (cost (extract (extract (extract (extract (init_cost stepsCM n nC) i iC) rep repC) tl tlC) H HC)
     <= Z.to_nat (gap n i) * 30 + 10)%nat.
Proof.
  unfold init_cost. cbn.
  match goal with |- context [@cost ?T (?G n nC i iC rep repC tl tlC H HC)] =>
    assert (HG : forall N i iC rep repC tl tlC H HC, (Z.to_nat (gap n i) <= N)%nat ->
       (cost (G n nC i iC rep repC tl tlC H HC) <= Z.to_nat (gap n i) * 30 + 10)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros i' iC' rep' repC' tl' tlC' [g] HC' HN.
    cost_simpl.
    pose proof (bdec_time (i' <? n) (bool_w (i' <? n))) as HB.
    cost_destruct (bdec (i' <? n)); cost_simpl.
    - zero_partials. set_simpl.
      assert (E : Z.to_nat (gap n i') = S (Z.to_nat (gap n (i' + 1))))
        by (match goal with Hx : (i' <? n) = true |- _ => exact (gap_S _ _ Hx) end).
      assert (HN2 : (Z.to_nat (gap n (i' + 1)) < N)%nat) by lia.
      match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?i2 ?iC2 ?r2 ?rC2 ?t2 ?tC2 ?h ?hc)] =>
        pose proof (IH _ HN2 i2 iC2 r2 rC2 t2 tC2 h hc (le_n _)
          : (@cost T (G' a1 a2 i2 iC2 r2 rC2 t2 tC2 h hc) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' a1 a2 i2 iC2 r2 rC2 t2 tC2 h hc)); intros ? HI
      end.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G n nC i iC rep repC tl tlC H HC)] =>
    exact (HG _ i iC rep repC tl tlC H HC (le_n _) : (@cost T (G n nC i iC rep repC tl tlC H HC) <= _)%nat) end.
Qed.

Lemma tally_time n nC i iC rep repC sz szC seen seenC cnt cntC gg ggC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (tally_cost stepsCM n nC) i iC) rep repC) sz szC) seen seenC) cnt cntC) gg ggC) H HC)
     <= Z.to_nat (gap n i) * 60 + 10)%nat.
Proof.
  unfold tally_cost. cbn.
  match goal with |- context [@cost ?T (?G n nC i iC rep repC sz szC seen seenC cnt cntC gg ggC H HC)] =>
    assert (HG : forall N i iC seen seenC cnt cntC gg ggC H HC, (Z.to_nat (gap n i) <= N)%nat ->
       (cost (G n nC i iC rep repC sz szC seen seenC cnt cntC gg ggC H HC) <= Z.to_nat (gap n i) * 60 + 10)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros i' iC' se' seC' cn' cnC' g' gC' [g] HC' HN.
    cost_simpl.
    pose proof (bdec_time (i' <? n) (bool_w (i' <? n))) as HB.
    cost_destruct (bdec (i' <? n)); cost_simpl.
    - zero_partials. set_simpl.
      assert (E : Z.to_nat (gap n i') = S (Z.to_nat (gap n (i' + 1))))
        by (match goal with Hx : (i' <? n) = true |- _ => exact (gap_S _ _ Hx) end).
      assert (HN2 : (Z.to_nat (gap n (i' + 1)) < N)%nat) by lia.
      cost_destruct (se'.[rep.[i']] =? 0); cost_simpl; zero_partials; set_simpl;
      (match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?i2 ?iC2 ?a3 ?a4 ?a5 ?a6 ?s2 ?sC2 ?c2 ?cC2 ?g2 ?gC2 ?h ?hc)] =>
        pose proof (IH _ HN2 i2 iC2 s2 sC2 c2 cC2 g2 gC2 h hc (le_n _)
          : (@cost T (G' a1 a2 i2 iC2 a3 a4 a5 a6 s2 sC2 c2 cC2 g2 gC2 h hc) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' a1 a2 i2 iC2 a3 a4 a5 a6 s2 sC2 c2 cC2 g2 gC2 h hc)); intros ? HI
      end); lia.
    - lia. }
  match goal with |- context [@cost ?T (?G n nC i iC rep repC sz szC seen seenC cnt cntC gg ggC H HC)] =>
    exact (HG _ i iC seen seenC cnt cntC gg ggC H HC (le_n _) : (@cost T (G n nC i iC rep repC sz szC seen seenC cnt cntC gg ggC H HC) <= _)%nat) end.
Qed.

Lemma countd_time n nC i iC cnt cntC d dC H HC :
  (cost (extract (extract (extract (extract (countd_cost stepsCM n nC) i iC) cnt cntC) d dC) H HC)
     <= Z.to_nat (gap n i) * 40 + 10)%nat.
Proof.
  unfold countd_cost. cbn.
  match goal with |- context [@cost ?T (?G n nC i iC cnt cntC d dC H HC)] =>
    assert (HG : forall N i iC d dC H HC, (Z.to_nat (gap n i) <= N)%nat ->
       (cost (G n nC i iC cnt cntC d dC H HC) <= Z.to_nat (gap n i) * 40 + 10)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros i' iC' d' dC' [g] HC' HN.
    cost_simpl.
    pose proof (bdec_time (i' <? n) (bool_w (i' <? n))) as HB.
    cost_destruct (bdec (i' <? n)); cost_simpl.
    - zero_partials.
      assert (E : Z.to_nat (gap n i') = S (Z.to_nat (gap n (i' + 1))))
        by (match goal with Hx : (i' <? n) = true |- _ => exact (gap_S _ _ Hx) end).
      assert (HN2 : (Z.to_nat (gap n (i' + 1)) < N)%nat) by lia.
      cost_destruct (0 <? cnt.[n - i']); cost_simpl; zero_partials;
      (match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?i2 ?iC2 ?a3 ?a4 ?d2 ?dC2 ?h ?hc)] =>
        pose proof (IH _ HN2 i2 iC2 d2 dC2 h hc (le_n _)
          : (@cost T (G' a1 a2 i2 iC2 a3 a4 d2 dC2 h hc) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' a1 a2 i2 iC2 a3 a4 d2 dC2 h hc)); intros ? HI
      end); lia.
    - lia. }
  match goal with |- context [@cost ?T (?G n nC i iC cnt cntC d dC H HC)] =>
    exact (HG _ i iC d dC H HC (le_n _) : (@cost T (G n nC i iC cnt cntC d dC H HC) <= _)%nat) end.
Qed.

Lemma fill_time n nC i iC j jC cnt cntC out outC H HC :
  (cost (extract (extract (extract (extract (extract (fill_cost stepsCM n nC) i iC) j jC) cnt cntC) out outC) H HC)
     <= Z.to_nat (gap n i) * 50 + 10)%nat.
Proof.
  unfold fill_cost. cbn.
  match goal with |- context [@cost ?T (?G n nC i iC j jC cnt cntC out outC H HC)] =>
    assert (HG : forall N i iC j jC out outC H HC, (Z.to_nat (gap n i) <= N)%nat ->
       (cost (G n nC i iC j jC cnt cntC out outC H HC) <= Z.to_nat (gap n i) * 50 + 10)%nat) end.
  { induction N as [N IH] using lt_wf_ind.
    intros i' iC' j' jC' o' oC' [g] HC' HN.
    cost_simpl.
    pose proof (bdec_time (i' <? n) (bool_w (i' <? n))) as HB.
    cost_destruct (bdec (i' <? n)); cost_simpl.
    - zero_partials.
      assert (E : Z.to_nat (gap n i') = S (Z.to_nat (gap n (i' + 1))))
        by (match goal with Hx : (i' <? n) = true |- _ => exact (gap_S _ _ Hx) end).
      assert (HN2 : (Z.to_nat (gap n (i' + 1)) < N)%nat) by lia.
      cost_destruct (0 <? cnt.[n - i']); cost_simpl; zero_partials; set_simpl;
      (match goal with |- context [@cost ?T (?G' ?a1 ?a2 ?i2 ?iC2 ?j2 ?jC2 ?a3 ?a4 ?o2 ?oC2 ?h ?hc)] =>
        pose proof (IH _ HN2 i2 iC2 j2 jC2 o2 oC2 h hc (le_n _)
          : (@cost T (G' a1 a2 i2 iC2 j2 jC2 a3 a4 o2 oC2 h hc) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' a1 a2 i2 iC2 j2 jC2 a3 a4 o2 oC2 h hc)); intros ? HI
      end); lia.
    - lia. }
  match goal with |- context [@cost ?T (?G n nC i iC j jC cnt cntC out outC H HC)] =>
    exact (HG _ i iC j jC out outC H HC (le_n _) : (@cost T (G n nC i iC j jC cnt cntC out outC H HC) <= _)%nat) end.
Qed.

Ltac gen_init := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (init_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC =>
    let Hc := fresh "Hin" in
    pose proof (init_time a aC b bC c cC d dC e eC : (@cost T X <= _)%nat) as Hc;
    revert Hc; generalize (@cost T X); intros ? Hc end end.

Lemma gap0 (m : int) : Z.to_nat (gap m 0) = zn m.
Proof. unfold gap, zn. change (φ 0) with 0%Z. f_equal. lia. Qed.

Lemma chatter_impl_time n nC r rC a aC b bC c cC :
  (2 <= φ n <= 10000)%Z -> (φ c <= 50000)%Z ->
  (cost (extract (extract (extract (extract (chatter_impl_cost stepsCM n nC) r rC) a aC) b bC) c cC)
     <= zn n * (zn c * 70 + 300) + zn n * Nat.log2 (zn n) * 30 + zn n * 300 + 300)%nat.
Proof.
  intros Hn Hc.
  unfold chatter_impl_cost. cost_simpl. zero_partials. make_simpl. gen_init.
  rewrite gap0 in Hin.
  pose proof (init_spec n Hn _ 0 (PArray.make n 0) (PArray.make n 0)
                (Zwf_well_founded 0 (gap n 0)) eq_refl
                (make_length n 0 ltac:(lia)) (make_length n 0 ltac:(lia))
                ltac:(change (φ 0) with 0%Z; lia)
                ltac:(intros j Hj; change (φ 0) with 0%Z in Hj;
                      pose proof (to_Z_bounded j); lia)) as [I1 [I2 I3]].
  cost_destruct_witness (init n 0 (PArray.make n 0) (PArray.make n 0) (Zwf_well_founded 0 (gap n 0))) as [rep0 rep0C tl0 tl0C] eqn:Ei.
  try rewrite Ei in I1, I2, I3. cbn [fst snd] in I1, I2, I3.
  destruct (start_spec n Hn rep0 tl0 I1 I2 I3) as [D0 _].
  cost_simpl. zero_partials. make_simpl.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (sim_cost stepsCM ?a1 ?b1) ?a2 ?b2) ?a3 ?b3) ?a4 ?b4) ?a5 ?b5) ?a6 ?b6) ?a7 ?b7) ?a8 ?b8) ?a9 ?b9) ?a10 ?b10) ?a11 ?b11 =>
      pose proof (sim_time a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 a8 b8 a9 b9 a10 b10 a11 b11 Hn Hc D0 : (@cost T X <= _)%nat) as Hsim;
      revert Hsim; generalize (@cost T X); intros ? Hsim end end.
  pose proof (pot_le n rep0 (PArray.make n 1)) as HP.
  cost_destruct_witness (sim n a b c r n rep0 (PArray.make n 0) tl0 (PArray.make n 1) (Zwf_well_founded 0 (φ n))) as [rep rC2 sz szC2] eqn:Es.
  cost_simpl. zero_partials. make_simpl.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (extract (extract (extract (extract (tally_cost stepsCM ?a1 ?b1) ?a2 ?b2) ?a3 ?b3) ?a4 ?b4) ?a5 ?b5) ?a6 ?b6) ?a7 ?b7) ?a8 ?b8 =>
      pose proof (tally_time a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 a8 b8 : (@cost T X <= _)%nat) as Hta;
      revert Hta; generalize (@cost T X); intros ? Hta end end.
  rewrite gap0 in Hta.
  cost_destruct_witness (tally n 0 rep sz (PArray.make n 0) (PArray.make (n + 1) 0) 0 (Zwf_well_founded 0 (gap n 0))) as [g gC cnt cntC] eqn:Et.
  cost_simpl. zero_partials. make_simpl.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (extract (countd_cost stepsCM ?a1 ?b1) ?a2 ?b2) ?a3 ?b3) ?a4 ?b4) ?a5 ?b5 =>
      pose proof (countd_time a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 : (@cost T X <= _)%nat) as Hcd;
      revert Hcd; generalize (@cost T X); intros ? Hcd end end.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (extract (extract (fill_cost stepsCM ?a1 ?b1) ?a2 ?b2) ?a3 ?b3) ?a4 ?b4) ?a5 ?b5) ?a6 ?b6 =>
      pose proof (fill_time a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 : (@cost T X <= _)%nat) as Hfi;
      revert Hfi; generalize (@cost T X); intros ? Hfi end end.
  rewrite gap0 in Hcd, Hfi.
  change (Z.to_nat (φ n)) with (zn n) in Hsim.
  clear -Hin Hsim HP Hta Hcd Hfi.
  set (P := pot n rep0 (PArray.make n 1)) in *. set (L := Nat.log2 (zn n)) in *.
  set (N := zn n) in *. set (Cc := zn c) in *. clearbody P L N Cc.
  set (M := (N * L)%nat) in *. set (Q := (N * (Cc * 70 + 300))%nat) in *. clearbody M Q.
  lia.
Qed.

Lemma final_arith (N C L x : nat) :
  (x <= N * (C * 70 + 300) + N * L * 30 + N * 300 + 400)%nat ->
  (x <= 1000 * ((N + 1) * (C + L + 1)) + 1000)%nat.
Proof.
  intros H.
  assert (E : ((N + 1) * (C + L + 1) = N * C + N * L + N + C + L + 1)%nat) by ring.
  rewrite E.
  assert (E2 : (N * (C * 70 + 300) = (N * C) * 70 + N * 300)%nat) by ring.
  rewrite E2 in H. lia.
Qed.

Theorem chatter_time : exists c1 c2 : nat,
  forall (people_count seed multiplier increment modulus : N)
  (people_count_int seed_int multiplier_int increment_int modulus_int : uint),
  valid_input people_count seed multiplier increment modulus ->
  repr people_count_int people_count -> repr seed_int seed ->
  repr multiplier_int multiplier -> repr increment_int increment ->
  repr modulus_int modulus ->
  (cost5 chatter_cost people_count_int seed_int multiplier_int increment_int modulus_int <= c1 * ((size people_count_int + 1) * (size modulus_int + Nat.log2 (size people_count_int) + 1)) + c2)%nat.
Proof.
  exists 1000%nat, 1000%nat.
  intros nN rN aN bN cN n r a b c Hv Rn Rr Ra Rb Rc.
  change (tN n = nN) in Rn. change (tN c = cN) in Rc. subst nN cN.
  destruct Hv as [Vn _ _ _ Vc _].
  assert (Hn : (2 <= (φ n) <= 10000)%Z) by (unfold tN in Vn; lia).
  assert (Hc : ((φ c) <= 50000)%Z) by (unfold tN in Vc; lia).
  clear Vn Vc.
  change (Cost.size n) with (zn n). change (Cost.size c) with (zn c).
  apply final_arith.
  unfold cost5, chatter_cost. cost_simpl. zero_partials.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (extract (chatter_impl_cost stepsCM ?a1 ?b1) ?a2 ?b2) ?a3 ?b3) ?a4 ?b4) ?a5 ?b5 =>
      pose proof (chatter_impl_time a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 Hn Hc : (@cost T X <= _)%nat) as Hci;
      revert Hci; generalize (@cost T X); intros ? Hci end end.
  lia.
Qed.
