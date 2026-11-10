(* Implementation of helpfulcurrents (helpfulcurrents.spec): forward
   path counting, row by row, from the bottom row northwards.

   Code.  W(y,x), the number of move sequences taking the ship from its
   start (Y-1, xinit) to (y, x), satisfies
     W(y,x) = [start] + [north] W(y+1,x) + [cell(y,x-1) = '>'] W(y,x-1)
                                         + [cell(y,x+1) = '<'] W(y,x+1)
   (north: the cell below is not the castle and (y,x) is not '#').  One
   array holds a row of counts modulo 1000003, a second one a flag "the
   count is non-zero"; both are updated in place, row y over row y+1.
   Pass 1, west to east, adds the start, the north and the west
   contributions (A); pass 2, east to west, adds the east contribution
   (B = W).  This is exact because a '>' cell has no '<' east of it and a
   '<' cell no '>' west of it.  When pass 2 meets the castle it records
   its (count, flag), the answer.

   Proof.  [counted S n]: the set S of move lists has exactly n elements
   (a NoDup list); [rep S v f]: v is n mod 1000003, f is 0 iff n = 0.
   [pref_decomp] is the recurrence on the sets of prefixes; the loop
   invariants say each cell [rep]s its set.  A route is a prefix ending
   at the castle.

   Termination: erased [Acc (Zwf 0)] on a Z measure, as in polymul1. *)

From Helpfulcurrents.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import String Ascii.
From Stdlib Require PrimString.
Import ListNotations.

Open Scope bool_scope.
Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

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

Lemma dec_down : forall x : int, (0 <? x) = true -> Zwf 0 (φ (x - 1)) (φ x).
Proof.
  intros x H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  assert (H1 : (φ (x - 1)) = ((φ x) - 1)%Z) by sia.
  unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Definition P : int := 1000003.

(* (a + b) mod P, for a, b < P *)
Definition addm (a b : int) : int :=
  let s := a + b in if s <? P then s else s - P.

(* the flag of a union: zero iff both are *)
Definition orf (a b : int) : int := if a =? 0 then b else a.

(* Pass 1 over row y (string s, the row below sb), west to east: cell x
   receives start + north + west, where (wv, wf) is the west
   contribution (the value of cell x-1 when it is '>'). *)
Fixpoint pass1 (s sb : PrimString.string) (Ym Xm xim y : int)
    (x wv wf : int) (cv cf : array int) (H : Acc (Zwf 0) (gap Xm x)) {struct H}
    : array int * array int :=
  match bdec (x <? Xm) with
  | left Hx =>
      let c := PrimString.get s x in
      let st := (y + 1 =? Ym) && (x =? xim) in
      let sv := if st then 1 else 0 in
      let north := (y + 1 <? Ym) && negb (PrimString.get sb x =? 64)
                   && negb (c =? 35) in
      let nv := if north then cv.[x] else 0 in
      let nf := if north then cf.[x] else 0 in
      let av := addm (addm sv nv) wv in
      let af := orf (orf sv nf) wf in
      let w := c =? 62 in
      pass1 s sb Ym Xm xim y (x + 1) (if w then av else 0) (if w then af else 0)
        cv.[x <- av] cf.[x <- af] (Acc_inv H (dec_step Xm x Hx))
  | right _ => (cv, cf)
  end.

Lemma pass1_eq : forall s sb Ym Xm xim y x wv wf cv cf H,
  pass1 s sb Ym Xm xim y x wv wf cv cf H =
  match bdec (x <? Xm) with
  | left Hx =>
      let c := PrimString.get s x in
      let st := (y + 1 =? Ym) && (x =? xim) in
      let sv := if st then 1 else 0 in
      let north := (y + 1 <? Ym) && negb (PrimString.get sb x =? 64)
                   && negb (c =? 35) in
      let nv := if north then cv.[x] else 0 in
      let nf := if north then cf.[x] else 0 in
      let av := addm (addm sv nv) wv in
      let af := orf (orf sv nf) wf in
      let w := c =? 62 in
      pass1 s sb Ym Xm xim y (x + 1) (if w then av else 0) (if w then af else 0)
        cv.[x <- av] cf.[x <- af] (Acc_inv H (dec_step Xm x Hx))
  | right _ => (cv, cf)
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* Pass 2 over row y, east to west: cell x-1 receives the east
   contribution (ev, ef) (the value of cell x when it is '<'); the
   castle's final value is recorded in (av, af). *)
Fixpoint pass2 (s : PrimString.string) (x ev ef : int) (cv cf : array int)
    (av af : int) (H : Acc (Zwf 0) (φ x)) {struct H}
    : (array int * array int) * (int * int) :=
  match bdec (0 <? x) with
  | left Hx =>
      let x' := x - 1 in
      let c := PrimString.get s x' in
      let bv := addm cv.[x'] ev in
      let bf := orf cf.[x'] ef in
      let e := c =? 60 in
      let k := c =? 64 in
      pass2 s x' (if e then bv else 0) (if e then bf else 0)
        cv.[x' <- bv] cf.[x' <- bf]
        (if k then bv else av) (if k then bf else af) (Acc_inv H (dec_down x Hx))
  | right _ => ((cv, cf), (av, af))
  end.

Lemma pass2_eq : forall s x ev ef cv cf av af H,
  pass2 s x ev ef cv cf av af H =
  match bdec (0 <? x) with
  | left Hx =>
      let x' := x - 1 in
      let c := PrimString.get s x' in
      let bv := addm cv.[x'] ev in
      let bf := orf cf.[x'] ef in
      let e := c =? 60 in
      let k := c =? 64 in
      pass2 s x' (if e then bv else 0) (if e then bf else 0)
        cv.[x' <- bv] cf.[x' <- bf]
        (if k then bv else av) (if k then bf else af) (Acc_inv H (dec_down x Hx))
  | right _ => ((cv, cf), (av, af))
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* Rows k-1, k-2, ..., 0; the arrays hold row k. *)
Fixpoint rows (m : array PrimString.string) (Ym Xm xim : int) (k : int)
    (cv cf : array int) (av af : int) (H : Acc (Zwf 0) (φ k)) {struct H}
    : int * int :=
  match bdec (0 <? k) with
  | left Hk =>
      let y := k - 1 in
      let s := m.[y] in
      let r1 := pass1 s m.[k] Ym Xm xim y 0 0 0 cv cf
                  (Zwf_well_founded 0 (gap Xm 0)) in
      let r2 := pass2 s Xm 0 0 (fst r1) (snd r1) av af
                  (Zwf_well_founded 0 (φ Xm)) in
      rows m Ym Xm xim y (fst (fst r2)) (snd (fst r2)) (fst (snd r2))
        (snd (snd r2)) (Acc_inv H (dec_down k Hk))
  | right _ => (av, af)
  end.

Lemma rows_eq : forall m Ym Xm xim k cv cf av af H,
  rows m Ym Xm xim k cv cf av af H =
  match bdec (0 <? k) with
  | left Hk =>
      let y := k - 1 in
      let s := m.[y] in
      let r1 := pass1 s m.[k] Ym Xm xim y 0 0 0 cv cf
                  (Zwf_well_founded 0 (gap Xm 0)) in
      let r2 := pass2 s Xm 0 0 (fst r1) (snd r1) av af
                  (Zwf_well_founded 0 (φ Xm)) in
      rows m Ym Xm xim y (fst (fst r2)) (snd (fst r2)) (fst (snd r2))
        (snd (snd r2)) (Acc_inv H (dec_down k Hk))
  | right _ => (av, af)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition helpfulcurrents_impl (Ym Xm xim : uint) (m : array PrimString.string)
    : option uint :=
  let r := rows m Ym Xm xim Ym (PArray.make Xm 0) (PArray.make Xm 0) 0 0
             (Zwf_well_founded 0 (φ Ym)) in
  if snd r =? 0 then None else Some (fst r).

(* ------------------------------------------------------------------ *)
(* Counting sets of move lists                                         *)
(* ------------------------------------------------------------------ *)

Definition counted (S : list move -> Prop) (n : nat) : Prop :=
  exists rs, NoDup rs /\ List.length rs = n /\ forall r, In r rs <-> S r.

Definition rep (S : list move -> Prop) (v f : int) : Prop :=
  exists n, counted S n /\ (φ v) = (Z.of_nat n mod 1000003)%Z
            /\ ((φ f) = 0%Z <-> n = 0%nat).

Definition snoc_set (S : list move -> Prop) (mv : move) (r : list move) : Prop :=
  exists r', S r' /\ r = r' ++ [mv].

Lemma rep_ext : forall (S T : list move -> Prop) v f,
  (forall r, S r <-> T r) -> rep S v f -> rep T v f.
Proof.
  intros S T v f E (n & (rs & Hd & Hl & Hi) & Hv & Hf).
  exists n. split; [|auto]. exists rs. split; [auto|split; [auto|]].
  intros r. rewrite Hi. apply E.
Qed.

Lemma rep_nil : rep (fun r => r = []) 1 1.
Proof.
  exists 1%nat. split; [|split; [reflexivity|split; [discriminate|discriminate]]].
  exists [[]]. split; [repeat constructor; simpl; tauto|split; [reflexivity|]].
  intros r. simpl. split; [intros [<-|[]]; reflexivity|intros ->; auto].
Qed.

Lemma rep_cond : forall (b : bool) (S : list move -> Prop) v f,
  (b = true -> rep S v f) ->
  rep (fun r => b = true /\ S r) (if b then v else 0) (if b then f else 0).
Proof.
  intros b S v f H. destruct b.
  - apply (rep_ext S); [|auto]. intros r. split; [auto|intros [_ H']; exact H'].
  - exists 0%nat. split; [|split; [reflexivity|split; reflexivity]].
    exists []. split; [constructor|split; [reflexivity|]].
    intros r. simpl. split; [intros []|intros [E _]; discriminate].
Qed.

Lemma rep_snoc : forall S mv v f, rep S v f -> rep (snoc_set S mv) v f.
Proof.
  intros S mv v f (n & (rs & Hd & Hl & Hi) & Hv & Hf).
  exists n. split; [|auto].
  exists (map (fun r => r ++ [mv]) rs). split; [|split].
  - apply NoDup_map_NoDup_ForallPairs; [|exact Hd].
    intros a b _ _ E. apply app_inj_tail in E. tauto.
  - rewrite length_map. exact Hl.
  - intros r. rewrite in_map_iff. unfold snoc_set. split.
    + intros (r' & <- & Hr'). exists r'. split; [apply Hi; exact Hr'|reflexivity].
    + intros (r' & Hr' & ->). exists r'. split; [reflexivity|apply Hi; exact Hr'].
Qed.

Lemma addm_spec : forall a b : int, ((φ a) < 1000003)%Z -> ((φ b) < 1000003)%Z ->
  (φ (addm a b)) = (((φ a) + (φ b)) mod 1000003)%Z.
Proof.
  intros a b Ha Hb. unfold addm, P.
  destruct (a + b <? 1000003) eqn:E;
    [rewrite ltb_spec in E | rewrite <- Bool.not_true_iff_false, ltb_spec in E];
    change (φ 1000003) with 1000003%Z in E; sia.
Qed.

Lemma orf_spec : forall a b : int, (φ (orf a b)) = 0%Z <-> (φ a) = 0%Z /\ (φ b) = 0%Z.
Proof.
  intros a b. unfold orf. destruct (a =? 0) eqn:E.
  - rewrite Uint63.eqb_spec in E. subst a. change (φ 0) with 0%Z. tauto.
  - rewrite <- Bool.not_true_iff_false, Uint63.eqb_spec in E.
    assert ((φ a) <> 0%Z) by (intro F; apply E; apply to_Z_inj; exact F). tauto.
Qed.

Lemma rep_union : forall S T v1 f1 v2 f2,
  rep S v1 f1 -> rep T v2 f2 -> (forall r, S r -> T r -> False) ->
  rep (fun r => S r \/ T r) (addm v1 v2) (orf f1 f2).
Proof.
  intros S T v1 f1 v2 f2 (n1 & (rs1 & Hd1 & Hl1 & Hi1) & Hv1 & Hf1)
    (n2 & (rs2 & Hd2 & Hl2 & Hi2) & Hv2 & Hf2) Hdis.
  exists (n1 + n2)%nat. split; [|split].
  - exists (rs1 ++ rs2). split; [|split].
    + apply NoDup_app; [exact Hd1|exact Hd2|].
      intros a Ha Hb. apply (Hdis a); [apply Hi1|apply Hi2]; assumption.
    + rewrite length_app. lia.
    + intros r. rewrite in_app_iff, Hi1, Hi2. tauto.
  - rewrite addm_spec.
    + rewrite Hv1, Hv2, Nat2Z.inj_add, <- Z.add_mod by lia. reflexivity.
    + rewrite Hv1. apply Z.mod_pos_bound. lia.
    + rewrite Hv2. apply Z.mod_pos_bound. lia.
  - rewrite orf_spec, Hf1, Hf2. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Characters                                                          *)
(* ------------------------------------------------------------------ *)

Lemma code_eqb : forall (k l : int) (c d : ascii),
  (φ k) = Z.of_N (N_of_ascii c) -> (φ l) = Z.of_N (N_of_ascii d) ->
  (k =? l) = Ascii.eqb c d.
Proof.
  intros k l c d Hk Hl. destruct (Ascii.eqb_spec c d) as [<-|Hne].
  - apply Uint63.eqb_spec. apply to_Z_inj. congruence.
  - apply Bool.not_true_iff_false. rewrite Uint63.eqb_spec. intros ->. apply Hne.
    rewrite <- (ascii_N_embedding c), <- (ascii_N_embedding d). f_equal. lia.
Qed.

Lemma code_at : forall (k : int) c, (φ k) = Z.of_N (N_of_ascii c) ->
  (k =? 64) = Ascii.eqb c "@" /\ (k =? 35) = Ascii.eqb c "#" /\
  (k =? 62) = Ascii.eqb c ">" /\ (k =? 60) = Ascii.eqb c "<".
Proof. intros k c H. repeat split; apply code_eqb with (1 := H); reflexivity. Qed.

Lemma string_get_oob : forall (s : string) n,
  (String.length s <= n)%nat -> String.get n s = None.
Proof.
  induction s as [|a s IH]; intros n H; [reflexivity|].
  destruct n; simpl in *; [lia|]. apply IH. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The math side: prefixes and their recurrence                        *)
(* ------------------------------------------------------------------ *)

Section Math.

Variable map : list string.
Variables Y X xinit : N.
Hypothesis Hv : valid_input Y X xinit map.

Lemma cell_oob : forall y x, (Y <= y \/ X <= x)%N -> cell map y x = "#"%char.
Proof.
  intros y x H. unfold cell.
  pose proof (vi_rows _ _ _ _ Hv) as Hr. pose proof (vi_cols _ _ _ _ Hv) as Hc.
  unfold len in Hr.
  destruct (Nat.lt_ge_cases (N.to_nat y) (List.length map)) as [Hy|Hy].
  - destruct H as [H|H]; [lia|].
    rewrite string_get_oob; [reflexivity|].
    rewrite Forall_forall in Hc. specialize (Hc _ (nth_In _ EmptyString Hy)). lia.
  - rewrite nth_overflow by lia. reflexivity.
Qed.

Lemma step_in : forall p mv q, (fst p < Y)%N -> (snd p < X)%N ->
  step map p mv = Some q -> (fst q < Y)%N /\ (snd q < X)%N.
Proof.
  intros [y x] mv [qy qx] Hy Hx Hs. simpl in Hy, Hx |- *.
  cbv beta iota zeta delta [step] in Hs.
  destruct (Ascii.eqb (cell map y x) "@") eqn:E0; [discriminate|].
  destruct mv.
  - destruct (orb _ _); [discriminate|]. injection Hs as <- <-. lia.
  - destruct (Ascii.eqb (cell map y x) ">") eqn:E1.
    + injection Hs as <- <-. apply Ascii.eqb_eq in E1.
      destruct (vi_east _ _ _ _ Hv y x (conj Hy Hx) E1) as [H _]. lia.
    + destruct (Ascii.eqb (cell map y x) "<"); [|discriminate].
      injection Hs as <- <-. lia.
Qed.

Lemma run_in : forall r p q, (fst p < Y)%N -> (snd p < X)%N ->
  run map p r = Some q -> (fst q < Y)%N /\ (snd q < X)%N.
Proof.
  induction r as [|mv r IH]; intros p q Hy Hx H; simpl in H.
  - injection H as <-. auto.
  - destruct (step map p mv) as [p'|] eqn:E; [|discriminate].
    destruct (step_in p mv p' Hy Hx E). eapply IH; eauto.
Qed.

Lemma run_snoc : forall r p mv, run map p (r ++ [mv]) =
  match run map p r with Some q => step map q mv | None => None end.
Proof.
  induction r as [|mv' r IH]; intros p mv; simpl.
  - destruct (step map p mv); reflexivity.
  - destruct (step map p mv'); [apply IH|reflexivity].
Qed.

Definition Pref (p : N * N) (r : list move) : Prop :=
  run map ((Y - 1)%N, xinit) r = Some p.

Lemma pref_in : forall p r, Pref p r -> (fst p < Y)%N /\ (snd p < X)%N.
Proof.
  intros p r H. pose proof (vi_Y _ _ _ _ Hv). pose proof (vi_X _ _ _ _ Hv).
  apply (run_in r ((Y - 1)%N, xinit)); [simpl; lia|simpl; lia|exact H].
Qed.

Definition condS (y x : N) : bool := ((y + 1 =? Y)%N && (x =? xinit)%N).
Definition condN (y x : N) : bool :=
  (y + 1 <? Y)%N && negb (Ascii.eqb (cell map (y + 1) x) "@")
  && negb (Ascii.eqb (cell map y x) "#").
Definition condW (y x : N) : bool :=
  (1 <=? x)%N && Ascii.eqb (cell map y (x - 1)) ">".
Definition condE (y x : N) : bool := Ascii.eqb (cell map y (x + 1)) "<".

Definition pS (y x : N) (r : list move) : Prop := condS y x = true /\ r = [].
Definition pN (y x : N) (r : list move) : Prop :=
  condN y x = true /\ snoc_set (Pref ((y + 1)%N, x)) North r.
Definition pW (y x : N) (r : list move) : Prop :=
  condW y x = true /\ snoc_set (Pref (y, (x - 1)%N)) Current r.
Definition pE (y x : N) (r : list move) : Prop :=
  condE y x = true /\ snoc_set (Pref (y, (x + 1)%N)) Current r.
Definition Aset (y x : N) (r : list move) : Prop :=
  (pS y x r \/ pN y x r) \/ pW y x r.

Lemma pref_decomp : forall y x r, (y < Y)%N -> (x < X)%N ->
  Pref (y, x) r <-> Aset y x r \/ pE y x r.
Proof.
  intros y x r Hy Hx.
  unfold Aset, pS, pN, pW, pE, snoc_set, condS, condN, condW, condE. split.
  - unfold Pref. destruct r as [|mv r' _] using rev_ind.
    + simpl. intros H. injection H as <- <-. left; left; left.
      split; [|reflexivity].
      pose proof (vi_Y _ _ _ _ Hv). apply andb_true_intro.
      split; apply N.eqb_eq; lia.
    + rewrite run_snoc. destruct (run map _ r') as [[qy qx]|] eqn:Er;
        [|discriminate].
      intros Hs.
      destruct (pref_in (qy, qx) r' Er) as [Hqy Hqx]. simpl in Hqy, Hqx.
      cbv beta iota zeta delta [step] in Hs.
      destruct (Ascii.eqb (cell map qy qx) "@") eqn:E0; [discriminate|].
      destruct mv.
      * destruct (orb (qy =? 0)%N (Ascii.eqb (cell map (qy - 1) qx) "#")) eqn:E1;
          [discriminate|].
        injection Hs as <- <-. apply Bool.orb_false_iff in E1 as [E1 E2].
        apply N.eqb_neq in E1.
        replace (qy - 1 + 1)%N with qy by lia.
        left; left; right. split.
        -- assert (E3 : (qy <? Y)%N = true) by (apply N.ltb_lt; exact Hqy).
           rewrite E0, E2, E3. reflexivity.
        -- exists r'. split; [exact Er|reflexivity].
      * destruct (Ascii.eqb (cell map qy qx) ">") eqn:E1.
        -- injection Hs as <- <-. left; right. split.
           ++ replace (qx + 1 - 1)%N with qx by lia. rewrite E1.
              apply andb_true_intro; split; [apply N.leb_le; lia|reflexivity].
           ++ exists r'. split; [|reflexivity].
              replace (qx + 1 - 1)%N with qx by lia. exact Er.
        -- destruct (Ascii.eqb (cell map qy qx) "<") eqn:E2; [|discriminate].
           injection Hs as <- <-. apply Ascii.eqb_eq in E2.
           destruct (vi_west _ _ _ _ Hv qy qx (conj Hqy Hqx) E2) as [Hq1 _].
           right. replace (qx - 1 + 1)%N with qx by lia. split.
           ++ rewrite E2. reflexivity.
           ++ exists r'. split; [exact Er|reflexivity].
  - unfold Pref. intros [[[[HS ->]|[HN (r' & Hr' & ->)]]|[HW (r' & Hr' & ->)]]
                      |[HE (r' & Hr' & ->)]].
    + apply andb_prop in HS as [H1 H2]. apply N.eqb_eq in H1. apply N.eqb_eq in H2.
      simpl. f_equal. f_equal; lia.
    + rewrite run_snoc, Hr'.
      apply andb_prop in HN as [HN H3]. apply andb_prop in HN as [H1 H2].
      apply Bool.negb_true_iff in H2, H3.
      cbv beta iota zeta delta [step]. rewrite H2.
      replace (y + 1 - 1)%N with y by lia. rewrite H3.
      replace (y + 1 =? 0)%N with false by (symmetry; apply N.eqb_neq; lia).
      reflexivity.
    + rewrite run_snoc, Hr'.
      apply andb_prop in HW as [H1 H2]. apply N.leb_le in H1.
      apply Ascii.eqb_eq in H2.
      cbv beta iota zeta delta [step]. rewrite H2. simpl.
      replace (x - 1 + 1)%N with x by lia. reflexivity.
    + rewrite run_snoc, Hr'.
      apply Ascii.eqb_eq in HE.
      cbv beta iota zeta delta [step]. rewrite HE. simpl.
      replace (x + 1 - 1)%N with x by lia. reflexivity.
Qed.

(* disjointness of the four pieces *)
Lemma snoc_nil : forall (r : list move) mv, r ++ [mv] <> [].
Proof. intros r mv H. destruct r; discriminate. Qed.

Lemma disj_SN : forall y x r, pS y x r -> pN y x r -> False.
Proof.
  intros y x r [_ ->] [_ (r' & _ & E)]. symmetry in E. exact (snoc_nil _ _ E).
Qed.

Lemma disj_SNW : forall y x r, pS y x r \/ pN y x r -> pW y x r -> False.
Proof.
  intros y x r [[_ ->]|[_ (r1 & _ & E1)]] [_ (r2 & _ & E2)].
  - symmetry in E2. exact (snoc_nil _ _ E2).
  - rewrite E1 in E2. apply app_inj_tail in E2 as [_ E]. discriminate.
Qed.

Lemma disj_AE : forall y x r, Aset y x r -> pE y x r -> False.
Proof.
  intros y x r [[[_ ->]|[_ (r1 & _ & E1)]]|[_ (r1 & H1 & E1)]] [_ (r2 & H2 & E2)].
  - symmetry in E2. exact (snoc_nil _ _ E2).
  - rewrite E1 in E2. apply app_inj_tail in E2 as [_ E]. discriminate.
  - rewrite E1 in E2. apply app_inj_tail in E2 as [<- _].
    unfold Pref in H1, H2. rewrite H1 in H2. injection H2 as E. lia.
Qed.

Lemma condW_succ : forall y x, condW y (x + 1) = Ascii.eqb (cell map y x) ">".
Proof.
  intros y x. unfold condW. replace (x + 1 - 1)%N with x by lia.
  replace (1 <=? x + 1)%N with true by (symmetry; apply N.leb_le; lia). reflexivity.
Qed.

Lemma condE_pred : forall y x, (1 <= x)%N ->
  condE y (x - 1) = Ascii.eqb (cell map y x) "<".
Proof.
  intros y x H. unfold condE. replace (x - 1 + 1)%N with x by lia. reflexivity.
Qed.

(* a '>' cell: its prefixes are A *)
Lemma pref_east : forall y x r, (y < Y)%N -> (x < X)%N ->
  cell map y x = ">"%char -> Aset y x r <-> Pref (y, x) r.
Proof.
  intros y x r Hy Hx Hc. rewrite pref_decomp by assumption.
  split; [tauto|]. intros [H|[HE _]]; [exact H|].
  destruct (vi_east _ _ _ _ Hv y x (conj Hy Hx) Hc) as [_ [Hn _]].
  unfold condE in HE. apply Ascii.eqb_eq in HE. contradiction.
Qed.

(* the castle *)
Variables y0 x0 : N.
Hypothesis Hc0 : Prelude.in_map Y X y0 x0 /\ cell map y0 x0 = "@"%char /\
  (forall y x, Prelude.in_map Y X y x -> cell map y x = "@"%char ->
     y = y0 /\ x = x0).

Lemma route_pref : forall r, is_route Y xinit map r <-> Pref (y0, x0) r.
Proof.
  intros r. unfold is_route, Pref. destruct Hc0 as (_ & Hc & Hu). split.
  - intros ([qy qx] & Hr & Hq). simpl in Hq.
    destruct (pref_in (qy, qx) r Hr) as [H1 H2]. simpl in H1, H2.
    destruct (Hu qy qx (conj H1 H2) Hq) as [-> ->]. exact Hr.
  - intros Hr. exists (y0, x0). split; [exact Hr|exact Hc].
Qed.

Lemma castle_unique : forall y x, (y < Y)%N -> (x < X)%N ->
  Ascii.eqb (cell map y x) "@" = true -> y = y0 /\ x = x0.
Proof.
  intros y x Hy Hx H. apply Ascii.eqb_eq in H. destruct Hc0 as (_ & _ & Hu).
  apply Hu; [split; assumption|exact H].
Qed.


(* ------------------------------------------------------------------ *)
(* The machine side                                                    *)
(* ------------------------------------------------------------------ *)

Variable m : array PrimString.string.
Variables Ym Xm xim : int.
Hypothesis HY : (φ Ym) = Z.of_N Y.
Hypothesis HX : (φ Xm) = Z.of_N X.
Hypothesis Hxi : (φ xim) = Z.of_N xinit.
Hypothesis Hm : repr m map.

Local Notation nn j := (Z.to_N (φ j)).

Lemma bnds : (0 < Y <= 300)%N /\ (xinit < X <= 50000)%N.
Proof. split; [exact (vi_Y _ _ _ _ Hv)|exact (vi_X _ _ _ _ Hv)]. Qed.

Lemma eqb_N : forall a b : int, (a =? b) = (nn a =? nn b)%N.
Proof.
  intros a b. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  destruct (a =? b) eqn:E; symmetry.
  - apply N.eqb_eq. rewrite Uint63.eqb_spec in E. subst. reflexivity.
  - apply N.eqb_neq. rewrite <- Bool.not_true_iff_false, Uint63.eqb_spec in E.
    intro F. apply E. apply to_Z_inj. lia.
Qed.

Lemma ltb_N : forall a b : int, (a <? b) = (nn a <? nn b)%N.
Proof.
  intros a b. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  destruct (a <? b) eqn:E; symmetry.
  - apply N.ltb_lt. rewrite ltb_spec in E. lia.
  - apply N.ltb_ge. rewrite <- Bool.not_true_iff_false, ltb_spec in E. lia.
Qed.

Lemma nn_succ : forall x : int, ((φ x) < 4611686018427387904)%Z ->
  nn (x + 1) = (nn x + 1)%N.
Proof.
  intros x H. pose proof (to_Z_bounded x).
  assert ((φ (x + 1)) = ((φ x) + 1)%Z) by sia. lia.
Qed.

Definition row_ok (s : PrimString.string) (yy : N) : Prop :=
  forall j : int, ((φ j) < Z.of_N X)%Z ->
  (φ (PrimString.get s j)) = Z.of_N (N_of_ascii (cell map yy (nn j))).

Lemma row_of_m : forall y : int, ((φ y) < Z.of_N Y)%Z -> row_ok m.[y] (nn y).
Proof.
  intros y Hy j Hj.
  destruct Hm as [Hl Hc].
  pose proof (vi_rows _ _ _ _ Hv) as Hr. pose proof (vi_cols _ _ _ _ Hv) as Hcols.
  unfold len in Hr.
  pose proof (to_Z_bounded y) as By. pose proof (to_Z_bounded j) as Bj.
  destruct (Hc (Z.to_nat (φ y)) ltac:(lia)) as (s & Hs & Hrs).
  rewrite Z2Nat.id in Hrs by lia. rewrite of_to_Z in Hrs.
  destruct Hrs as [Hsl Hsc].
  assert (HsX : N.of_nat (String.length s) = X).
  { rewrite Forall_forall in Hcols. apply Hcols. eapply nth_error_In. exact Hs. }
  destruct (Hsc (Z.to_nat (φ j)) ltac:(lia)) as (c & Hgc & Hcode).
  rewrite Z2Nat.id in Hcode by lia. rewrite of_to_Z in Hcode.
  unfold cell. rewrite !Z_N_nat. rewrite (nth_error_nth map _ _ Hs). rewrite Hgc.
  unfold repr, repr_uint in Hcode.
  rewrite <- Hcode.
  pose proof (to_Z_bounded (PrimString.get m.[y] j)).
  rewrite Z2N.id by lia. reflexivity.
Qed.

Lemma condS_m : forall y x : int, ((φ y) < Z.of_N Y)%Z -> ((φ x) < Z.of_N X)%Z ->
  ((y + 1 =? Ym) && (x =? xim)) = condS (nn y) (nn x).
Proof.
  intros y x Hy Hx. pose proof bnds. unfold condS.
  rewrite !eqb_N, nn_succ by lia. rewrite HY, Hxi, !N2Z.id. reflexivity.
Qed.

Lemma north_m : forall (y x : int) s sb,
  ((φ y) < Z.of_N Y)%Z -> ((φ x) < Z.of_N X)%Z ->
  row_ok s (nn y) -> (((φ y) + 1 < Z.of_N Y)%Z -> row_ok sb (nn y + 1)) ->
  ((y + 1 <? Ym) && negb (PrimString.get sb x =? 64)
   && negb (PrimString.get s x =? 35)) = condN (nn y) (nn x).
Proof.
  intros y x s sb Hy Hx Hs Hsb. pose proof bnds. pose proof (to_Z_bounded y).
  unfold condN. rewrite ltb_N, nn_succ by lia. rewrite HY, N2Z.id.
  destruct (nn y + 1 <? Y)%N eqn:E; [|reflexivity].
  apply N.ltb_lt in E.
  destruct (code_at _ _ (Hsb ltac:(lia) x Hx)) as [-> _].
  destruct (code_at _ _ (Hs x Hx)) as [_ [-> _]]. reflexivity.
Qed.

Lemma rep_false : forall (b : bool) (S : list move -> Prop),
  b = false -> rep (fun r => b = true /\ S r) 0 0.
Proof.
  intros b S ->. exact (rep_cond false S 0 0 (fun E => ltac:(discriminate))).
Qed.

(* ---- pass 1 ---- *)

Definition post1 (y : int) (r : array int * array int) : Prop :=
  PArray.length (fst r) = Xm /\ PArray.length (snd r) = Xm /\
  forall j : int, ((φ j) < (φ Xm))%Z -> rep (Aset (nn y) (nn j)) (fst r).[j] (snd r).[j].

Lemma pass1_spec : forall (y : int) (s sb : PrimString.string),
  ((φ y) < Z.of_N Y)%Z -> row_ok s (nn y) ->
  (((φ y) + 1 < Z.of_N Y)%Z -> row_ok sb (nn y + 1)) ->
  forall z (x wv wf : int) (cv cf : array int) (H : Acc (Zwf 0) (gap Xm x)),
  gap Xm x = z -> ((φ x) <= (φ Xm))%Z ->
  PArray.length cv = Xm -> PArray.length cf = Xm ->
  (forall j : int, ((φ j) < (φ x))%Z -> rep (Aset (nn y) (nn j)) cv.[j] cf.[j]) ->
  (forall j : int, ((φ x) <= (φ j) < (φ Xm))%Z -> ((φ y) + 1 < Z.of_N Y)%Z ->
     rep (Pref ((nn y + 1)%N, nn j)) cv.[j] cf.[j]) ->
  (((φ x) < (φ Xm))%Z -> rep (pW (nn y) (nn x)) wv wf) ->
  post1 y (pass1 s sb Ym Xm xim y x wv wf cv cf H).
Proof.
  intros y s sb Hy Hs Hsb z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros x wv wf cv cf H Hz Hxle Hlv Hlf Hdone Hnext Hw.
  pose proof bnds as Bnd.
  rewrite pass1_eq.
  destruct (bdec (x <? Xm)) as [Hx | Hx].
  - pose proof Hx as Hx'. rewrite ltb_spec in Hx'.
    pose proof (to_Z_bounded x) as Bx. pose proof (to_Z_bounded y) as By.
    assert (Hx1 : (φ (x + 1)) = ((φ x) + 1)%Z) by sia.
    assert (HxX : ((φ x) < Z.of_N X)%Z) by lia.
    cbv zeta.
    rewrite (condS_m y x Hy HxX).
    rewrite (north_m y x s sb Hy HxX Hs Hsb).
    destruct (code_at _ _ (Hs x HxX)) as (_ & _ & E62 & _). rewrite E62.
    assert (HS : rep (pS (nn y) (nn x))
                   (if condS (nn y) (nn x) then 1 else 0)
                   (if condS (nn y) (nn x) then 1 else 0))
      by exact (rep_cond _ (fun r => r = []) 1 1 (fun _ => rep_nil)).
    assert (HN : rep (pN (nn y) (nn x))
                   (if condN (nn y) (nn x) then cv.[x] else 0)
                   (if condN (nn y) (nn x) then cf.[x] else 0)).
    { apply (rep_cond (condN (nn y) (nn x)) (snoc_set (Pref ((nn y + 1)%N, nn x)) North)).
      intros E. apply rep_snoc. apply Hnext; [lia|].
      unfold condN in E. apply andb_prop in E as [E _]. apply andb_prop in E as [E _].
      apply N.ltb_lt in E. lia. }
    pose proof (rep_union _ _ _ _ _ _ HS HN (disj_SN _ _)) as HSN.
    pose proof (rep_union _ _ _ _ _ _ HSN (Hw Hx') (disj_SNW _ _)) as HA.
    change (fun r => (pS (nn y) (nn x) r \/ pN (nn y) (nn x) r) \/ pW (nn y) (nn x) r)
      with (Aset (nn y) (nn x)) in HA.
    eapply IH; [ | reflexivity | lia | rewrite alength_set; exact Hlv
               | rewrite alength_set; exact Hlf | | | ].
    + rewrite <- Hz. apply dec_step. exact Hx.
    + intros j Hj. rewrite Hx1 in Hj.
      destruct (Z.eq_dec (φ j) (φ x)) as [E | E].
      * assert (j = x) by (apply to_Z_inj; exact E). subst j.
        rewrite !aget_set_same by (rewrite ?Hlv, ?Hlf; exact Hx). exact HA.
      * rewrite !aget_set_other by (intro F; apply E; rewrite F; reflexivity).
        apply Hdone. lia.
    + intros j Hj Hy1. rewrite Hx1 in Hj.
      rewrite !aget_set_other by (intro F; subst j; lia).
      apply Hnext; [lia|exact Hy1].
    + intros Hx2. rewrite nn_succ by lia. rewrite <- condW_succ.
      apply (rep_cond (condW (nn y) (nn x + 1))
               (snoc_set (Pref (nn y, (nn x + 1 - 1)%N)) Current)).
      intros E. rewrite condW_succ in E. apply Ascii.eqb_eq in E.
      apply rep_snoc. replace (nn x + 1 - 1)%N with (nn x) by lia.
      apply (rep_ext (Aset (nn y) (nn x))); [|exact HA].
      intros r. apply pref_east; [lia|lia|exact E].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hx.
    split; [exact Hlv|split; [exact Hlf|]].
    intros j Hj. apply Hdone. lia.
Qed.

(* ---- pass 2 ---- *)

Definition post2 (y : int) (av af : int)
    (r : (array int * array int) * (int * int)) : Prop :=
  PArray.length (fst (fst r)) = Xm /\ PArray.length (snd (fst r)) = Xm /\
  (forall j : int, ((φ j) < (φ Xm))%Z ->
     rep (Pref (nn y, nn j)) (fst (fst r)).[j] (snd (fst r)).[j]) /\
  (nn y = y0 -> rep (Pref (y0, x0)) (fst (snd r)) (snd (snd r))) /\
  (nn y <> y0 -> fst (snd r) = av /\ snd (snd r) = af).

Lemma pass2_spec : forall (y : int) (s : PrimString.string),
  ((φ y) < Z.of_N Y)%Z -> row_ok s (nn y) ->
  forall z (x ev ef : int) (cv cf : array int) (av af : int)
    (H : Acc (Zwf 0) (φ x)),
  (φ x) = z -> ((φ x) <= (φ Xm))%Z ->
  PArray.length cv = Xm -> PArray.length cf = Xm ->
  (forall j : int, ((φ j) < (φ x))%Z -> rep (Aset (nn y) (nn j)) cv.[j] cf.[j]) ->
  (forall j : int, ((φ x) <= (φ j) < (φ Xm))%Z -> rep (Pref (nn y, nn j)) cv.[j] cf.[j]) ->
  ((0 < (φ x))%Z -> rep (pE (nn y) (nn x - 1)) ev ef) ->
  (nn y = y0 -> (nn x <= x0)%N -> rep (Pref (y0, x0)) av af) ->
  post2 y av af (pass2 s x ev ef cv cf av af H).
Proof.
  intros y s Hy Hs z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros x ev ef cv cf av af H Hz Hxle Hlv Hlf Hdone Hnext He Hacc.
  pose proof bnds as Bnd. pose proof Hc0 as ((Hy0 & Hx0) & Hcas & _).
  rewrite pass2_eq.
  destruct (bdec (0 <? x)) as [Hx | Hx].
  - pose proof Hx as Hx'. rewrite ltb_spec in Hx'. change (φ 0) with 0%Z in Hx'.
    pose proof (to_Z_bounded x) as Bx. pose proof (to_Z_bounded y) as By.
    assert (Hx1 : (φ (x - 1)) = ((φ x) - 1)%Z) by sia.
    assert (HxX : ((φ (x - 1)) < Z.of_N X)%Z) by lia.
    assert (Hnx : nn (x - 1) = (nn x - 1)%N) by lia.
    cbv zeta.
    destruct (code_at _ _ (Hs (x - 1) HxX)) as (E64 & _ & _ & E60).
    rewrite E64, E60.
    assert (HB : rep (Pref (nn y, nn (x - 1)))
                   (addm cv.[x - 1] ev) (orf cf.[x - 1] ef)).
    { apply (rep_ext (fun r => Aset (nn y) (nn (x - 1)) r \/ pE (nn y) (nn (x - 1)) r)).
      - intros r. symmetry. apply pref_decomp; lia.
      - apply rep_union; [apply Hdone; lia| |apply disj_AE].
        rewrite Hnx. apply He. lia. }
    assert (Hlt : Zwf 0 (φ (x - 1)) z) by (rewrite <- Hz; apply dec_down; exact Hx).
    assert (A5 : forall j : int, ((φ j) < (φ (x - 1)))%Z ->
              rep (Aset (nn y) (nn j)) cv.[x - 1 <- addm cv.[x - 1] ev].[j]
                                       cf.[x - 1 <- orf cf.[x - 1] ef].[j]).
    { intros j Hj. rewrite !aget_set_other by (intro F; subst j; lia).
      apply Hdone. lia. }
    assert (A6 : forall j : int, ((φ (x - 1)) <= (φ j) < (φ Xm))%Z ->
              rep (Pref (nn y, nn j)) cv.[x - 1 <- addm cv.[x - 1] ev].[j]
                                      cf.[x - 1 <- orf cf.[x - 1] ef].[j]).
    { intros j Hj. destruct (Z.eq_dec (φ j) (φ (x - 1))) as [E | E].
      - assert (j = x - 1) by (apply to_Z_inj; exact E). subst j.
        rewrite !aget_set_same by (rewrite ?Hlv, ?Hlf; apply ltb_spec; lia).
        exact HB.
      - rewrite !aget_set_other by (intro F; apply E; rewrite F; reflexivity).
        apply Hnext. lia. }
    assert (A7 : (0 < (φ (x - 1)))%Z ->
              rep (pE (nn y) (nn (x - 1) - 1))
                (if Ascii.eqb (cell map (nn y) (nn (x - 1))) "<"
                 then addm cv.[x - 1] ev else 0)
                (if Ascii.eqb (cell map (nn y) (nn (x - 1))) "<"
                 then orf cf.[x - 1] ef else 0)).
    { intros Hp. rewrite <- condE_pred by lia.
      apply (rep_cond (condE (nn y) (nn (x - 1) - 1))
               (snoc_set (Pref (nn y, (nn (x - 1) - 1 + 1)%N)) Current)).
      intros _. apply rep_snoc. replace (nn (x - 1) - 1 + 1)%N with (nn (x - 1)) by lia.
      exact HB. }
    assert (A8 : nn y = y0 -> (nn (x - 1) <= x0)%N ->
              rep (Pref (y0, x0))
                (if Ascii.eqb (cell map (nn y) (nn (x - 1))) "@"
                 then addm cv.[x - 1] ev else av)
                (if Ascii.eqb (cell map (nn y) (nn (x - 1))) "@"
                 then orf cf.[x - 1] ef else af)).
    { intros Ey Ex. destruct (Ascii.eqb (cell map (nn y) (nn (x - 1))) "@") eqn:Ec.
      - destruct (castle_unique (nn y) (nn (x - 1)) ltac:(lia) ltac:(lia) Ec) as [<- <-]. exact HB.
      - apply Hacc; [exact Ey|].
        destruct (N.eq_dec (nn (x - 1)) x0) as [E|E]; [|lia].
        exfalso. rewrite Ey, E, Hcas in Ec. discriminate. }
    destruct (IH _ Hlt (x - 1) _ _ _ _ _ _ (Acc_inv H (dec_down x Hx)) eq_refl
                ltac:(lia) ltac:(rewrite alength_set; exact Hlv)
                ltac:(rewrite alength_set; exact Hlf) A5 A6 A7 A8)
      as (L1 & L2 & R1 & R2 & R3).
    split; [exact L1|split; [exact L2|split; [exact R1|split; [exact R2|]]]].
    intros Ey. destruct (R3 Ey) as [-> ->].
    destruct (Ascii.eqb (cell map (nn y) (nn (x - 1))) "@") eqn:Ec; [|auto].
    exfalso. apply Ey. apply (castle_unique _ (nn (x - 1))); [lia|lia|exact Ec].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hx. change (φ 0) with 0%Z in Hx.
    pose proof (to_Z_bounded x).
    split; [exact Hlv|split; [exact Hlf|split; [|split]]].
    + intros j Hj. apply Hnext. pose proof (to_Z_bounded j). lia.
    + intros Ey. apply Hacc; [exact Ey|lia].
    + auto.
Qed.

(* ---- the rows ---- *)

Lemma rows_spec : forall z (k : int) (cv cf : array int) (av af : int)
    (H : Acc (Zwf 0) (φ k)),
  (φ k) = z -> ((φ k) <= (φ Ym))%Z ->
  PArray.length cv = Xm -> PArray.length cf = Xm ->
  (((φ k) < (φ Ym))%Z -> forall j : int, ((φ j) < (φ Xm))%Z ->
     rep (Pref (nn k, nn j)) cv.[j] cf.[j]) ->
  ((nn k <= y0)%N -> rep (Pref (y0, x0)) av af) ->
  rep (Pref (y0, x0)) (fst (rows m Ym Xm xim k cv cf av af H))
                      (snd (rows m Ym Xm xim k cv cf av af H)).
Proof.
  intro z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k cv cf av af H Hz Hkle Hlv Hlf Hrow Hacc.
  pose proof bnds as Bnd. pose proof Hc0 as ((Hy0 & Hx0) & Hcas & _).
  rewrite rows_eq.
  destruct (bdec (0 <? k)) as [Hk | Hk].
  - pose proof Hk as Hk'. rewrite ltb_spec in Hk'. change (φ 0) with 0%Z in Hk'.
    pose proof (to_Z_bounded k) as Bk.
    assert (Hk1 : (φ (k - 1)) = ((φ k) - 1)%Z) by sia.
    assert (Hyy : ((φ (k - 1)) < Z.of_N Y)%Z) by lia.
    assert (Hnk : nn k = (nn (k - 1) + 1)%N) by lia.
    cbv zeta.
    assert (Hw : rep (pW (nn (k - 1)) (nn 0)) 0 0)
      by (apply rep_false; reflexivity).
    pose proof (pass1_spec (k - 1) m.[k - 1] m.[k] Hyy (row_of_m (k - 1) Hyy)
                  ltac:(intros Hl; rewrite <- Hnk; apply row_of_m; lia)
                  _ 0 0 0 cv cf (Zwf_well_founded 0 (gap Xm 0)) eq_refl
                  ltac:(change (φ 0) with 0%Z; lia) Hlv Hlf
                  ltac:(intros j Hj; pose proof (to_Z_bounded j);
                        change (φ 0) with 0%Z in Hj; lia)
                  ltac:(intros j Hj Hl; rewrite <- Hnk; apply Hrow; [lia|lia])
                  (fun _ => Hw))
      as (L1 & L2 & R1).
    set (r1 := pass1 m.[k - 1] m.[k] Ym Xm xim (k - 1) 0 0 0 cv cf
                 (Zwf_well_founded 0 (gap Xm 0))) in *.
    assert (He : (0 < (φ Xm))%Z -> rep (pE (nn (k - 1)) (nn Xm - 1)) 0 0).
    { intros _. apply rep_false. unfold condE.
      replace (nn Xm - 1 + 1)%N with X by lia.
      rewrite cell_oob by lia. reflexivity. }
    pose proof (pass2_spec (k - 1) m.[k - 1] Hyy (row_of_m (k - 1) Hyy)
                  _ Xm 0 0 (fst r1) (snd r1) av af (Zwf_well_founded 0 (φ Xm))
                  eq_refl ltac:(lia) L1 L2 R1
                  ltac:(intros j Hj; lia) He
                  ltac:(intros _ F; lia))
      as (M1 & M2 & S1 & S2 & S3).
    apply (IH (φ (k - 1))); [rewrite <- Hz; apply dec_down; exact Hk
                            | reflexivity | lia | exact M1 | exact M2 | | ].
    + intros _. exact S1.
    + intros Hle. destruct (N.eq_dec (nn (k - 1)) y0) as [E|E].
      * apply S2. exact E.
      * destruct (S3 E) as [-> ->]. apply Hacc. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk. change (φ 0) with 0%Z in Hk.
    pose proof (to_Z_bounded k). simpl. apply Hacc. lia.
Qed.

Lemma impl_correct : exists o : option N,
  repr (helpfulcurrents_impl Ym Xm xim m) o /\ helpfulcurrents_spec Y X xinit map o.
Proof.
  pose proof bnds as Bnd. pose proof Hc0 as ((Hy0 & Hx0) & Hcas & _).
  unfold helpfulcurrents_impl.
  assert (HmL : PArray.length (PArray.make Xm 0) = Xm).
  { rewrite alength_make.
    replace (Xm <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  pose proof (rows_spec _ Ym (PArray.make Xm 0) (PArray.make Xm 0) 0 0
                (Zwf_well_founded 0 (φ Ym)) eq_refl ltac:(lia) HmL HmL
                ltac:(intros F; lia) ltac:(intros F; lia)) as HR.
  set (r := rows m Ym Xm xim Ym (PArray.make Xm 0) (PArray.make Xm 0) 0 0
              (Zwf_well_founded 0 (φ Ym))) in *.
  destruct HR as (n & (rs & Hd & Hl & Hi) & Hvv & Hf).
  destruct (snd r =? 0) eqn:E.
  - exists None. split; [exact I|].
    intros rt Hrt. rewrite Uint63.eqb_spec in E. rewrite E in Hf.
    change (φ 0) with 0%Z in Hf. destruct Hf as [Hf _]. specialize (Hf eq_refl).
    subst n. destruct rs; [|discriminate].
    apply (Hi rt). apply route_pref. exact Hrt.
  - exists (Some (nn (fst r))). split; [reflexivity|].
    rewrite <- Bool.not_true_iff_false, Uint63.eqb_spec in E.
    assert (Hn : n <> 0%nat).
    { intros ->. apply E. apply to_Z_inj. apply Hf. reflexivity. }
    exists (N.of_nat n). split; [lia|split].
    + exists rs. split; [exact Hd|split].
      * unfold len. rewrite Hl. reflexivity.
      * intros rt. rewrite Hi. symmetry. apply route_pref.
    + rewrite Hvv. lia.
Qed.

End Math.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition helpfulcurrents : uint -> uint -> uint -> array PrimString.string -> option uint
  := helpfulcurrents_impl.

Lemma helpfulcurrents_correct :
  forall (Y X xinit : N) (map : list string)
         (y x xi : uint) (m : array PrimString.string),
  valid_input Y X xinit map ->
  repr y Y -> repr x X -> repr xi xinit -> repr m map ->
  exists o : option N,
    repr (helpfulcurrents y x xi m) o /\ helpfulcurrents_spec Y X xinit map o.
Proof.
  intros Y X xinit map y x xi m Hv Hy Hx Hxi Hm.
  destruct (vi_castle _ _ _ _ Hv) as (y0 & x0 & Hc).
  unfold repr, repr_uint in Hy, Hx, Hxi.
  pose proof (to_Z_bounded y). pose proof (to_Z_bounded x).
  pose proof (to_Z_bounded xi).
  apply (impl_correct map Y X xinit Hv y0 x0 Hc m y x xi); [lia|lia|lia|exact Hm].
Qed.
