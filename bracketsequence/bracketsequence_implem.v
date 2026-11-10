(* Implementation of bracketsequence (bracketsequence.spec): one
   left-to-right pass over the tokens with an explicit stack of
   accumulators.

   Code.  [loop] walks the token array once.  The state is the depth [d]
   (a uint, the index of the top frame), the operator [add] of the top
   level (true: addition, false: multiplication; it flips at every
   bracket) and the stack [stk], one flat [PArray] of uint, threaded
   linearly, frame [j] at cell [j].  A number is folded into the top
   frame, an open bracket pushes the identity of the next level's operator,
   a closing bracket pops the top frame and folds its value into the frame
   below with the operator of that level.  All arithmetic is modulo
   10^9+7 on residues, so no value exceeds 63 bits.  The stack has
   n + 1 cells (the depth never exceeds the number of tokens read).
   A closing bracket at depth 0 (impossible on a bracket sequence) leaves
   the state as is, so the code is total.

   Proof.  The machine state represents a math state (bool, top, below)
   (relation [R]); the math step function [step] and its iteration [run]
   over a token list are the Prop-side model.  [loop_spec] says that the
   loop computes the top of [run] on the remaining tokens.  [item_run] /
   [items_run], by nested induction on the item tree, say that running the
   tokens of an item folds its value (mod 10^9+7) into the top frame;
   hence on [seq_tokens s] the result is [seq_value s mod 10^9+7], for
   every [s] that spells the input.

   Termination: the loop recurses structurally on an erased
   [Acc (Zwf 0) (gap n i)] proof, as in template/polymul1. *)

From Bracketsequence.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
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

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Definition Mi : int := 1000000007.

(* Fold v into the accumulator a with the operator of the level. *)
Definition opm (add : bool) (a v : int) : int :=
  if add then (a + v) mod Mi else (a * v) mod Mi.

(* The identity of the operator. *)
Definition idm (add : bool) : int := if add then 0 else 1.

Fixpoint loop (x : array (token uint)) (n i d : int) (add : bool)
    (stk : array int) (H : Acc (Zwf 0) (gap n i)) {struct H} : int :=
  match bdec (i <? n) with
  | left Hi =>
      match x.[i] with
      | Num v =>
          loop x n (i + 1) d add stk.[d <- opm add stk.[d] v]
            (Acc_inv H (dec_step n i Hi))
      | Open =>
          loop x n (i + 1) (d + 1) (negb add) stk.[d + 1 <- idm (negb add)]
            (Acc_inv H (dec_step n i Hi))
      | Close =>
          if d =? 0 then
            loop x n (i + 1) d add stk (Acc_inv H (dec_step n i Hi))
          else
            loop x n (i + 1) (d - 1) (negb add)
              stk.[d - 1 <- opm (negb add) stk.[d - 1] stk.[d]]
              (Acc_inv H (dec_step n i Hi))
      end
  | right _ => stk.[d]
  end.

Lemma loop_eq : forall x n i d add stk H,
  loop x n i d add stk H =
  match bdec (i <? n) with
  | left Hi =>
      match x.[i] with
      | Num v =>
          loop x n (i + 1) d add stk.[d <- opm add stk.[d] v]
            (Acc_inv H (dec_step n i Hi))
      | Open =>
          loop x n (i + 1) (d + 1) (negb add) stk.[d + 1 <- idm (negb add)]
            (Acc_inv H (dec_step n i Hi))
      | Close =>
          if d =? 0 then
            loop x n (i + 1) d add stk (Acc_inv H (dec_step n i Hi))
          else
            loop x n (i + 1) (d - 1) (negb add)
              stk.[d - 1 <- opm (negb add) stk.[d - 1] stk.[d]]
              (Acc_inv H (dec_step n i Hi))
      end
  | right _ => stk.[d]
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition bracketsequence_impl (x : array (token uint)) : uint :=
  let n := PArray.length x in
  loop x n 0 0 true (PArray.make (n + 1) 0) (Zwf_well_founded 0 (gap n 0)).

(* ------------------------------------------------------------------ *)
(* Prop side: the math model of the pass                               *)
(* ------------------------------------------------------------------ *)

Local Open Scope N_scope.

Definition op (add : bool) (a v : N) : N :=
  if add then (a + v) mod modulus else (a * v) mod modulus.

Definition idv (add : bool) : N := if add then 0 else 1.

(* (operator of the top level, top accumulator, the frames below, top first) *)
Definition state : Type := (bool * N * list N)%type.

Definition step (t : token N) (st : state) : state :=
  let '(add, top, below) := st in
  match t with
  | Num v => (add, op add top v, below)
  | Open => (negb add, idv (negb add), top :: below)
  | Close =>
      match below with
      | [] => (add, top, [])
      | b :: below' => (negb add, op (negb add) b top, below')
      end
  end.

Fixpoint run (ts : list (token N)) (st : state) : state :=
  match ts with
  | [] => st
  | t :: r => run r (step t st)
  end.

Definition top_of (st : state) : N := let '(_, t, _) := st in t.

Lemma run_app : forall a b st, run (a ++ b) st = run b (run a st).
Proof. induction a as [| t a IH]; intros b st; simpl; [reflexivity | apply IH]. Qed.

Lemma modulus_pos : modulus <> 0.
Proof. unfold modulus. lia. Qed.

Lemma op_lt : forall add a v, op add a v < modulus.
Proof. intros [] a v; unfold op; apply N.mod_lt, modulus_pos. Qed.

Lemma op_mod_r : forall add a v, op add a v = op add a (v mod modulus).
Proof.
  intros [] a v; unfold op.
  - rewrite N.add_mod_idemp_r by exact modulus_pos. reflexivity.
  - rewrite N.mul_mod_idemp_r by exact modulus_pos. reflexivity.
Qed.

Lemma op_id : forall add c, op add (idv add) (c mod modulus) = c mod modulus.
Proof.
  intros [] c; unfold op, idv.
  - rewrite N.add_0_l. apply N.mod_mod, modulus_pos.
  - rewrite N.mul_1_l. apply N.mod_mod, modulus_pos.
Qed.

Lemma op_small : forall add t, t < modulus -> op add t (idv add mod modulus) = t.
Proof.
  intros [] t Ht; unfold op, idv.
  - rewrite N.mod_0_l by exact modulus_pos. rewrite N.add_0_r. apply N.mod_small, Ht.
  - rewrite (N.mod_small 1) by (unfold modulus; lia).
    rewrite N.mul_1_r. apply N.mod_small, Ht.
Qed.

Lemma op_assoc : forall add t a c,
  op add (op add t (a mod modulus)) (c mod modulus)
  = op add t ((if add then a + c else a * c) mod modulus).
Proof.
  intros [] t a c; unfold op.
  - rewrite N.add_mod_idemp_l by exact modulus_pos.
    rewrite <- N.add_assoc.
    rewrite <- (N.add_mod_idemp_r t (a mod modulus + c mod modulus)) by exact modulus_pos.
    rewrite <- N.add_mod by exact modulus_pos.
    reflexivity.
  - rewrite N.mul_mod_idemp_l by exact modulus_pos.
    rewrite <- N.mul_assoc.
    rewrite <- (N.mul_mod_idemp_r t (a mod modulus * (c mod modulus))) by exact modulus_pos.
    rewrite <- N.mul_mod by exact modulus_pos.
    reflexivity.
Qed.

(* Nested induction on items. *)
Fixpoint item_ind2 (P : item -> Prop) (Q : list item -> Prop)
    (HL : forall v, P (Leaf v)) (HG : forall l, Q l -> P (Group l))
    (Hnil : Q []) (Hcons : forall it l, P it -> Q l -> Q (it :: l))
    (it : item) {struct it} : P it :=
  match it with
  | Leaf v => HL v
  | Group l =>
      HG l ((fix G (l : list item) : Q l :=
               match l with
               | [] => Hnil
               | it' :: l' => Hcons it' l' (item_ind2 P Q HL HG Hnil Hcons it') (G l')
               end) l)
  end.

Definition items_ind2 (P : item -> Prop) (Q : list item -> Prop)
    (HL : forall v, P (Leaf v)) (HG : forall l, Q l -> P (Group l))
    (Hnil : Q []) (Hcons : forall it l, P it -> Q l -> Q (it :: l)) :
    forall l, Q l :=
  fix G (l : list item) : Q l :=
    match l with
    | [] => Hnil
    | it' :: l' => Hcons it' l' (item_ind2 P Q HL HG Hnil Hcons it') (G l')
    end.

Definition item_claim (it : item) : Prop :=
  forall add top below, top < modulus ->
  run (item_tokens it) (add, top, below)
  = (add, op add top (item_value add it mod modulus), below).

Definition items_claim (l : list item) : Prop :=
  forall add top below, top < modulus ->
  run (flat_map item_tokens l) (add, top, below)
  = (add, op add top (Prelude.combine add (map (item_value add) l) mod modulus), below).

Lemma claim_leaf : forall v, item_claim (Leaf v).
Proof.
  intros v add top below Ht. simpl. rewrite <- op_mod_r. reflexivity.
Qed.

Lemma claim_group : forall l, items_claim l -> item_claim (Group l).
Proof.
  intros l IH add top below Ht. simpl item_tokens. simpl run.
  rewrite run_app.
  rewrite IH by (destruct add; simpl; unfold modulus; lia).
  simpl. rewrite Bool.negb_involutive. rewrite op_id. reflexivity.
Qed.

Lemma claim_nil : items_claim [].
Proof.
  intros add top below Ht. simpl. destruct add.
  - change (Prelude.combine true []) with (idv true).
    rewrite (op_small true top Ht). reflexivity.
  - change (Prelude.combine false []) with (idv false).
    rewrite (op_small false top Ht). reflexivity.
Qed.

Lemma claim_cons : forall it l, item_claim it -> items_claim l -> items_claim (it :: l).
Proof.
  intros it l Hi Hl add top below Ht. simpl flat_map. rewrite run_app.
  rewrite Hi by exact Ht. rewrite Hl by apply op_lt.
  rewrite op_assoc. destruct add; reflexivity.
Qed.

Lemma items_run : forall l, items_claim l.
Proof. exact (items_ind2 item_claim items_claim claim_leaf claim_group claim_nil claim_cons). Qed.

(* The whole sequence. *)
Lemma run_seq : forall s,
  top_of (run (seq_tokens s) (true, 0, [])) = seq_value s mod modulus.
Proof.
  intros s. unfold seq_tokens. rewrite items_run by (unfold modulus; lia).
  simpl. unfold op, seq_value. simpl. apply N.mod_mod, modulus_pos.
Qed.

Close Scope N_scope.

(* ------------------------------------------------------------------ *)
(* Machine state represents math state                                 *)
(* ------------------------------------------------------------------ *)

Definition R (d : int) (add : bool) (stk : array int) (st : state) : Prop :=
  let '(add', top, below) := st in
  add = add' /\ (φ d) = Z.of_nat (List.length below) /\
  (φ (stk.[d])) = Z.of_N top /\ (top < modulus)%N /\
  Forall (fun v => (v < modulus)%N) below /\
  forall j : int, ((φ j) < (φ d))%Z ->
    (φ (stk.[j])) = Z.of_N (nth (Z.to_nat ((φ d) - 1 - (φ j))) below 0%N).

Lemma Z_modulus : Z.of_N modulus = 1000000007%Z.
Proof. reflexivity. Qed.

Lemma opm_spec : forall add (a v : int) (A V : N),
  (φ a) = Z.of_N A -> (φ v) = Z.of_N V -> (A < modulus)%N -> (V < modulus)%N ->
  (φ (opm add a v)) = Z.of_N (op add A V).
Proof.
  intros add a v A V Ha Hv HA HV.
  assert (HA' : (Z.of_N A < 1000000007)%Z) by (rewrite <- Z_modulus; lia).
  assert (HV' : (Z.of_N V < 1000000007)%Z) by (rewrite <- Z_modulus; lia).
  destruct add; unfold opm, op.
  - rewrite mod_spec, add_spec, Ha, Hv. change (φ Mi) with 1000000007%Z.
    rewrite N2Z.inj_mod, N2Z.inj_add, Z_modulus.
    rewrite (Z.mod_small (Z.of_N A + Z.of_N V)) by (rewrite wB_val; lia).
    reflexivity.
  - rewrite mod_spec, mul_spec, Ha, Hv. change (φ Mi) with 1000000007%Z.
    rewrite N2Z.inj_mod, N2Z.inj_mul, Z_modulus.
    rewrite (Z.mod_small (Z.of_N A * Z.of_N V)) by (rewrite wB_val; nia).
    reflexivity.
Qed.

Lemma idm_spec : forall add, (φ (idm add)) = Z.of_N (idv add).
Proof. intros []; reflexivity. Qed.

Lemma R_num : forall d add stk st (v : int) (V : N) (L : int),
  R d add stk st -> PArray.length stk = L -> ((φ d) < (φ L))%Z ->
  (φ v) = Z.of_N V -> (V < modulus)%N ->
  R d add stk.[d <- opm add stk.[d] v] (step (Num V) st).
Proof.
  intros d add stk [[add' top] below] v V L
    (Ha & Hd & Ht & Htm & Hb & Hc) HL HdL Hv HV.
  subst add'. simpl.
  repeat split; auto.
  - rewrite aget_set_same by (rewrite HL, ltb_spec; exact HdL).
    apply opm_spec; auto.
  - apply op_lt.
  - intros j Hj. rewrite aget_set_other.
    + apply Hc, Hj.
    + intro E. subst j. lia.
Qed.

Lemma R_open : forall d add stk st (L : int),
  R d add stk st -> PArray.length stk = L -> ((φ d) + 1 < (φ L))%Z ->
  R (d + 1) (negb add) stk.[d + 1 <- idm (negb add)] (step Open st).
Proof.
  intros d add stk [[add' top] below] L
    (Ha & Hd & Ht & Htm & Hb & Hc) HL HdL.
  subst add'. simpl.
  pose proof (to_Z_bounded L).
  assert (Hd1 : (φ (d + 1)) = ((φ d) + 1)%Z) by sia.
  repeat split; auto.
  - rewrite Hd1, Hd. lia.
  - rewrite aget_set_same by (rewrite HL, ltb_spec; lia).
    apply idm_spec.
  - destruct add; simpl; unfold modulus; lia.
  - intros j Hj. rewrite Hd1 in Hj.
    rewrite aget_set_other by (intro E; subst j; lia).
    destruct (Z.eq_dec (φ j) (φ d)) as [E | E].
    + assert (j = d) by (apply to_Z_inj; exact E). subst j.
      rewrite Hd1. replace (Z.to_nat ((φ d) + 1 - 1 - (φ d))) with 0%nat by lia.
      exact Ht.
    + rewrite Hc by lia. rewrite Hd1.
      replace (Z.to_nat ((φ d) + 1 - 1 - (φ j))) with (S (Z.to_nat ((φ d) - 1 - (φ j)))) by lia.
      reflexivity.
Qed.

Lemma R_close0 : forall d add stk st,
  R d add stk st -> (d =? 0) = true -> step Close st = st.
Proof.
  intros d add stk [[add' top] below] (Ha & Hd & _) H0.
  rewrite eqb_spec in H0. subst d. change (φ 0) with 0%Z in Hd.
  destruct below; [reflexivity | simpl in Hd; lia].
Qed.

Lemma R_close : forall d add stk st (L : int),
  R d add stk st -> (d =? 0) = false -> PArray.length stk = L -> ((φ d) < (φ L))%Z ->
  R (d - 1) (negb add) stk.[d - 1 <- opm (negb add) stk.[d - 1] stk.[d]]
    (step Close st).
Proof.
  intros d add stk [[add' top] below] L
    (Ha & Hd & Ht & Htm & Hb & Hc) H0 HL HdL.
  subst add'.
  rewrite eqb_false_spec in H0.
  assert (Hd0 : (0 < (φ d))%Z).
  { pose proof (to_Z_bounded d).
    destruct (Z.eq_dec (φ d) 0) as [E | E]; [| lia].
    exfalso. apply H0. apply to_Z_inj. exact E. }
  destruct below as [| b below']; [simpl in Hd; lia |].
  simpl.
  assert (Hd1 : (φ (d - 1)) = ((φ d) - 1)%Z) by sia.
  apply Forall_cons_iff in Hb as [Hbm Hb'].
  assert (Hcb : (φ (stk.[d - 1])) = Z.of_N b).
  { rewrite Hc by lia. rewrite Hd1.
    replace (Z.to_nat ((φ d) - 1 - ((φ d) - 1))) with 0%nat by lia. reflexivity. }
  repeat split; auto.
  - rewrite Hd1, Hd. simpl List.length. lia.
  - rewrite aget_set_same by (rewrite HL, ltb_spec; lia).
    apply opm_spec; auto.
  - apply op_lt.
  - intros j Hj. rewrite Hd1 in Hj.
    rewrite aget_set_other by (intro E; subst j; lia).
    rewrite Hc by lia. rewrite Hd1.
    replace (Z.to_nat ((φ d) - 1 - (φ j))) with (S (Z.to_nat ((φ d) - 1 - 1 - (φ j)))) by lia.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The loop                                                            *)
(* ------------------------------------------------------------------ *)

Definition tok_ok (t : token N) : Prop :=
  match t with Num v => (v < 10 ^ 9 + 7)%N | _ => True end.

Lemma skipn_nth_error : forall {A} (l : list A) k m,
  nth_error l k = Some m -> skipn k l = m :: skipn (S k) l.
Proof.
  intros A l. induction l as [| a l IH]; intros k m H; destruct k; simpl in *;
    try discriminate.
  - injection H as ->. reflexivity.
  - apply IH, H.
Qed.

Lemma repr_token_cases : forall (t : token uint) (m : token N), repr t m ->
  (t = Open /\ m = Open) \/ (t = Close /\ m = Close) \/
  exists v V, t = Num v /\ m = Num V /\ (φ v) = Z.of_N V.
Proof.
  intros [| | v] [| | V] H; unfold repr, repr_token in H; try contradiction.
  - left. split; reflexivity.
  - right. left. split; reflexivity.
  - right. right. exists v, V. split; [reflexivity | split; [reflexivity |]].
    unfold repr, repr_uint in H. rewrite <- H. rewrite Z2N.id; [reflexivity |].
    pose proof (to_Z_bounded v). lia.
Qed.

Lemma loop_spec : forall (x : array (token uint)) (ts : list (token N)) (n L : int),
  (φ n) = Z.of_nat (List.length ts) ->
  (forall k : int, ((φ k) < (φ n))%Z ->
     exists m, nth_error ts (Z.to_nat (φ k)) = Some m /\ repr x.[k] m) ->
  Forall tok_ok ts ->
  (φ L) = ((φ n) + 1)%Z ->
  forall (z : Z) (i d : int) (add : bool) (stk : array int) (st : state)
         (H : Acc (Zwf 0) (gap n i)),
  gap n i = z ->
  ((φ i) <= (φ n))%Z -> ((φ d) <= (φ i))%Z ->
  PArray.length stk = L ->
  R d add stk st ->
  (φ (loop x n i d add stk H)) = Z.of_N (top_of (run (skipn (Z.to_nat (φ i)) ts) st)).
Proof.
  intros x ts n L Hn Htok Hok HL z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i d add stk st H Hz Hin Hdi Hlen HR.
  rewrite loop_eq.
  destruct (bdec (i <? n)) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    pose proof (to_Z_bounded i) as Bi. pose proof (to_Z_bounded d) as Bd.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    destruct (Htok i Hi') as (m & Hm & Hr).
    rewrite (skipn_nth_error _ _ _ Hm). cbn [run].
    replace (S (Z.to_nat (φ i))) with (Z.to_nat (φ (i + 1))) by lia.
    assert (Hz' : Zwf 0 (gap n (i + 1)) z) by (rewrite <- Hz; apply dec_step; exact Hi).
    destruct (repr_token_cases _ _ Hr) as [[Et Em] | [[Et Em] | (v & V & Et & Em & Ev)]];
      rewrite Et; subst m.
    + eapply IH; [exact Hz' | reflexivity | lia | | | ].
      * assert ((φ (d + 1)) = ((φ d) + 1)%Z) by sia. lia.
      * rewrite alength_set. exact Hlen.
      * eapply R_open; [exact HR | exact Hlen | lia].
    + destruct (d =? 0) eqn:E0.
      * rewrite (R_close0 _ _ _ _ HR E0).
        eapply IH; [exact Hz' | reflexivity | lia | lia | exact Hlen | exact HR].
      * eapply IH; [exact Hz' | reflexivity | lia | | | ].
        -- assert ((φ (d - 1)) <= (φ d))%Z by sia. lia.
        -- rewrite alength_set. exact Hlen.
        -- eapply R_close; [exact HR | exact E0 | exact Hlen | lia].
    + assert (HV : (V < modulus)%N).
      { rewrite Forall_forall in Hok.
        exact (Hok (Num V) (nth_error_In _ _ Hm)). }
      eapply IH; [exact Hz' | reflexivity | lia | lia | | ].
      * rewrite alength_set. exact Hlen.
      * eapply R_num; [exact HR | exact Hlen | lia | exact Ev | exact HV].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi.
    replace (Z.to_nat (φ i)) with (List.length ts) by lia.
    rewrite skipn_all. simpl.
    destruct st as [[add' top] below]. destruct HR as (_ & _ & Ht & _). exact Ht.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma repr_tokens : forall (x : array (token uint)) (ts : list (token N)),
  repr x ts ->
  (φ (PArray.length x)) = Z.of_nat (List.length ts) /\
  forall k : int, ((φ k) < (φ (PArray.length x)))%Z ->
    exists m, nth_error ts (Z.to_nat (φ k)) = Some m /\ repr x.[k] m.
Proof.
  intros x ts [Hl Hc].
  split; [symmetry; exact Hl |].
  intros k Hk.
  destruct (Hc (Z.to_nat (φ k)) ltac:(pose proof (to_Z_bounded k); lia)) as (m & Hm & Hr).
  exists m. split; [exact Hm |].
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded k); lia).
  rewrite of_to_Z in Hr. exact Hr.
Qed.

Lemma bracketsequence_impl_correct :
  forall (ts : list (token N)) (x : array (token uint)),
  valid_input ts -> repr x ts ->
  exists o : N, repr (bracketsequence_impl x) o /\ bracketsequence_spec ts o.
Proof.
  intros ts x Hv Hx.
  destruct Hv as [Hvn Hvx _].
  unfold len in Hvn.
  destruct (repr_tokens x ts Hx) as [Hn Htok].
  exists (Z.to_N (φ (bracketsequence_impl x))).
  split; [reflexivity |].
  intros s _ Hs.
  rewrite <- run_seq, Hs.
  unfold bracketsequence_impl.
  set (n := PArray.length x) in *.
  assert (HL : (φ (n + 1)) = ((φ n) + 1)%Z) by sia.
  assert (Hlen : PArray.length (PArray.make (n + 1) 0) = n + 1).
  { rewrite alength_make.
    replace (n + 1 <=? PArray.max_length) with true; [reflexivity |].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  rewrite (loop_spec x ts n (n + 1) Hn Htok Hvx HL _ 0 0 true
             (PArray.make (n + 1) 0) (true, 0%N, [])
             (Zwf_well_founded 0 (gap n 0)) eq_refl).
  - apply N2Z.id.
  - change (φ 0) with 0%Z. lia.
  - lia.
  - exact Hlen.
  - simpl. split; [reflexivity |]. split; [reflexivity |].
    split; [rewrite aget_make; reflexivity |].
    split; [unfold modulus; lia |]. split; [constructor |].
    intros j Hj. change (φ 0) with 0%Z in Hj. pose proof (to_Z_bounded j). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition bracketsequence : array (token uint) -> uint := bracketsequence_impl.

Definition bracketsequence_correct :
  forall (ts : list (token N)) (x : array (token uint)),
  valid_input ts -> repr x ts ->
  exists o : N, repr (bracketsequence x) o /\ bracketsequence_spec ts o
  := bracketsequence_impl_correct.
