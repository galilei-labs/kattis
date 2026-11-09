(* Correctness proofs for basincity_implem.v. *)
From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.
Open Scope bool_scope.

Unset Lia Cache.

Require Export basincity_implem.
Open Scope uint63_scope.
Open Scope array_scope.
Open Scope bool_scope.


Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma aget_make : forall (n i : int) (b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma eqb_Z : forall a b : int, (a =? b) = true <-> (φ a) = (φ b).
Proof. intros a b. rewrite eqb_spec. split; [intros ->; reflexivity | apply to_Z_inj]. Qed.

Lemma fill_dg_eq : forall y n i dg H, fill_dg y n i dg H =
  match bdec (i <? n) with
  | left Hi => fill_dg y n (i + 1) dg.[i <- PArray.length y.[i]]
                 (Acc_inv H (dec_step n i Hi))
  | right _ => dg
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma fill_nb_eq : forall y n i nb H, fill_nb y n i nb H =
  match bdec (i <? n) with
  | left Hi =>
      let row := y.[i] in
      let b := 4 * i in
      fill_nb y n (i + 1)
        (put_slot row b 3 (put_slot row b 2 (put_slot row b 1 (put_slot row b 0 nb))))
        (Acc_inv H (dec_step n i Hi))
  | right _ => nb
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma fill_dg_spec : forall y n z i dg H, gap n i = z -> ((φ i) <= (φ n))%Z ->
  PArray.length dg = n ->
  (forall v, ((φ v) < (φ i))%Z -> dg.[v] = PArray.length y.[v]) ->
  PArray.length (fill_dg y n i dg H) = n /\
  forall v, ((φ v) < (φ n))%Z -> (fill_dg y n i dg H).[v] = PArray.length y.[v].
Proof.
  intros y n z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i dg H Hz Hi Hl Hc. rewrite fill_dg_eq.
  destruct (bdec (i <? n)) as [Hlt | Hlt].
  - pose proof Hlt as Hlt'. rewrite ltb_Z in Hlt'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    eapply IH; [rewrite <- Hz; apply dec_step, Hlt | reflexivity | lia
               | rewrite alength_set; exact Hl |].
    intros v Hv. destruct (Z.eq_dec (φ v) (φ i)) as [E | E].
    + assert (v = i) as -> by (apply to_Z_inj, E).
      apply aget_set_same. rewrite Hl. exact Hlt.
    + rewrite aget_set_other by (intro F; subst; lia). apply Hc. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_Z in Hlt.
    split; [exact Hl|]. intros v Hv. apply Hc. lia.
Qed.

Lemma put_slot_len : forall row b j nb,
  PArray.length (put_slot row b j nb) = PArray.length nb.
Proof. intros. unfold put_slot. destruct (_ <? _); [apply alength_set | reflexivity]. Qed.

Lemma put_slot_other : forall row b j nb x, x <> b + j ->
  (put_slot row b j nb).[x] = nb.[x].
Proof.
  intros. unfold put_slot. destruct (_ <? _); [apply aget_set_other; congruence | reflexivity].
Qed.

Lemma put_slot_same : forall row b j nb, (b + j <? PArray.length nb) = true ->
  (j <? PArray.length row) = true ->
  (put_slot row b j nb).[b + j] = row.[j] - 1.
Proof.
  intros row b j nb H1 H2. unfold put_slot. rewrite H2. apply aget_set_same, H1.
Qed.

Lemma fill_nb_spec : forall y n z i nb H, gap n i = z -> ((φ i) <= (φ n))%Z ->
  ((φ n) <= 100000)%Z ->
  PArray.length nb = 4 * n ->
  (forall v j, ((φ v) < (φ i))%Z -> ((φ j) < 4)%Z -> ((φ j) < (φ (PArray.length y.[v])))%Z ->
     nb.[4 * v + j] = y.[v].[j] - 1) ->
  PArray.length (fill_nb y n i nb H) = 4 * n /\
  forall v j, ((φ v) < (φ n))%Z -> ((φ j) < 4)%Z -> ((φ j) < (φ (PArray.length y.[v])))%Z ->
     (fill_nb y n i nb H).[4 * v + j] = y.[v].[j] - 1.
Proof.
  intros y n z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i nb H Hz Hi Hn Hl Hc. rewrite fill_nb_eq.
  destruct (bdec (i <? n)) as [Hlt | Hlt].
  - pose proof Hlt as Hlt'. rewrite ltb_Z in Hlt'. cbv zeta.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    assert (H4n : (φ (4 * n)) = (4 * (φ n))%Z) by sia.
    eapply IH; [rewrite <- Hz; apply dec_step, Hlt | reflexivity | lia | exact Hn
               | rewrite !put_slot_len; exact Hl |].
    intros v j Hv Hj Hjr. pose proof (to_Z_bounded v). pose proof (to_Z_bounded j).
    assert (Hvj : (φ (4 * v + j)) = (4 * (φ v) + (φ j))%Z) by sia.
    destruct (Z.eq_dec (φ v) (φ i)) as [E | E].
    + assert (v = i) as -> by (apply to_Z_inj, E).
      assert (Hb : forall j', ((φ j') < 4)%Z ->
                (4 * i + j' <? PArray.length nb) = true).
      { intros j' Hj'. rewrite Hl, ltb_Z. pose proof (to_Z_bounded j'). sia. }
      assert (Hjr' : (j <? PArray.length y.[i]) = true) by (apply ltb_Z; exact Hjr).
      destruct (small4 j Hj) as [-> | [-> | [-> | ->]]].
      * rewrite !put_slot_other by (intro F; apply (f_equal to_Z) in F; sia).
        apply put_slot_same; [apply Hb; reflexivity | exact Hjr'].
      * rewrite !put_slot_other by (intro F; apply (f_equal to_Z) in F; sia).
        apply put_slot_same; [rewrite put_slot_len; apply Hb; reflexivity | exact Hjr'].
      * rewrite put_slot_other by (intro F; apply (f_equal to_Z) in F; sia).
        apply put_slot_same; [rewrite !put_slot_len; apply Hb; reflexivity | exact Hjr'].
      * apply put_slot_same; [rewrite !put_slot_len; apply Hb; reflexivity | exact Hjr'].
    + rewrite !put_slot_other by (intro F; apply (f_equal to_Z) in F; sia).
      apply Hc; auto. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_Z in Hlt.
    split; [exact Hl|]. intros v j Hv. apply Hc. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Reading the input                                                   *)
(* ------------------------------------------------------------------ *)

Definition vnum (x : int) : N := (Z.to_N (φ x) + 1)%N.

Lemma repr_rows : forall (y : array (array uint)) (adj : list (list N)),
  repr y adj ->
  (φ (PArray.length y)) = Z.of_nat (List.length adj) /\
  forall v, ((φ v) < (φ (PArray.length y)))%Z ->
    (φ (PArray.length y.[v])) = Z.of_nat (List.length (line adj (vnum v))) /\
    forall j, ((φ j) < (φ (PArray.length y.[v])))%Z ->
      Z.of_N (nth (Z.to_nat (φ j)) (line adj (vnum v)) 0%N) = (φ (y.[v].[j])).
Proof.
  intros y adj [Hl Hc].
  assert (Hl' : (φ (PArray.length y)) = Z.of_nat (List.length adj)) by (symmetry; exact Hl).
  split; [exact Hl'|].
  intros v Hv. pose proof (to_Z_bounded v).
  destruct (Hc (Z.to_nat (φ v)) ltac:(lia)) as (m & Hm & [Hrl Hrc]).
  rewrite Z2Nat.id in Hrl, Hrc by lia. rewrite of_to_Z in Hrl, Hrc.
  assert (Hline : line adj (vnum v) = m).
  { unfold line, vnum. replace (Z.to_N (φ v) + 1 - 1)%N with (Z.to_N (φ v)) by lia.
    replace (N.to_nat (Z.to_N (φ v))) with (Z.to_nat (φ v)) by lia.
    apply nth_error_nth. exact Hm. }
  assert (Hrl2 : (φ (PArray.length@{Set} y.[v])) = Z.of_nat (List.length m))
    by (symmetry; exact Hrl).
  rewrite Hline. split; [exact Hrl2|].
  intros j Hj. pose proof (to_Z_bounded j).
  assert (Hjm : (Z.to_nat (φ j) < List.length m)%nat) by lia.
  destruct (Hrc (Z.to_nat (φ j)) Hjm) as (c & Hcm & Hcr).
  rewrite Z2Nat.id in Hcr by lia. rewrite of_to_Z in Hcr.
  rewrite (nth_error_nth _ _ _ Hcm).
  unfold repr, repr_uint in Hcr. rewrite <- Hcr.
  rewrite Z2N.id by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The tables describe the graph of the statement                      *)
(* ------------------------------------------------------------------ *)

Section Input.
  Variable k0 : N.
  Variable adj : list (list N).
  Hypothesis Hv : valid_input k0 adj.
  Variable n : int.
  Variables nb dg : array int.
  Hypothesis HnA : (φ n) = Z.of_nat (List.length adj).
  Hypothesis Hdg : forall v, ((φ v) < (φ n))%Z ->
    (φ (dg.[v])) = Z.of_nat (List.length (line adj (vnum v))).
  Hypothesis Hnbr : forall v j, ((φ v) < (φ n))%Z -> ((φ j) < (φ (dg.[v])))%Z ->
    ((φ (nbr nb v j)) + 1)%Z = Z.of_N (nth (Z.to_nat (φ j)) (line adj (vnum v)) 0%N).

  Lemma line_in : forall v, ((φ v) < (φ n))%Z -> In (line adj (vnum v)) adj.
  Proof.
    intros v H. pose proof (to_Z_bounded v). unfold line, vnum.
    replace (N.to_nat (Z.to_N (φ v) + 1 - 1)) with (Z.to_nat (φ v)) by lia.
    apply nth_In. lia.
  Qed.

  Lemma vnum_inter : forall v, ((φ v) < (φ n))%Z -> is_intersection adj (vnum v).
  Proof.
    intros v H. pose proof (to_Z_bounded v). unfold is_intersection, vnum, len. lia.
  Qed.

  Lemma Hn_bound : ((φ n) <= 100000)%Z.
  Proof. destruct Hv as [_ Hn _ _ _ _ _]. unfold len in Hn. lia. Qed.

  Lemma Hdeg' : forall v, ((φ v) < (φ n))%Z -> ((φ (dg.[v])) <= 4)%Z.
  Proof.
    intros v H. rewrite Hdg by exact H.
    destruct Hv as [_ _ Hd _ _ _ _]. rewrite Forall_forall in Hd.
    pose proof (Hd _ (line_in v H)) as E. unfold len in E. lia.
  Qed.

  Lemma nbr_val : forall v j, ((φ v) < (φ n))%Z -> ((φ j) < (φ (dg.[v])))%Z ->
    In (vnum (nbr nb v j)) (line adj (vnum v)) /\ ((φ (nbr nb v j)) < (φ n))%Z.
  Proof.
    intros v j H Hj. pose proof (Hnbr v j H Hj) as E.
    pose proof (to_Z_bounded j). pose proof (to_Z_bounded (nbr nb v j)).
    rewrite Hdg in Hj by exact H.
    set (c := nth (Z.to_nat (φ j)) (line adj (vnum v)) 0%N) in E.
    assert (Hc : In c (line adj (vnum v))) by (apply nth_In; lia).
    assert (Hvn : vnum (nbr nb v j) = c) by (unfold vnum; lia).
    rewrite Hvn. split; [exact Hc|].
    destruct Hv as [_ _ _ Hr _ _ _].
    pose proof (Hr _ _ (vnum_inter v H) Hc) as Hi. unfold is_intersection, len in Hi.
    lia.
  Qed.

  Lemma Hrange' : forall v j, ((φ v) < (φ n))%Z -> ((φ j) < (φ (dg.[v])))%Z ->
    ((φ (nbr nb v j)) < (φ n))%Z.
  Proof. intros v j H Hj. exact (proj2 (nbr_val v j H Hj)). Qed.

  Lemma vnum_inj : forall a b, vnum a = vnum b -> a = b.
  Proof. intros a b E. unfold vnum in E. apply to_Z_inj. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). lia. Qed.

  Lemma Eb_neigh : forall x w, ((φ x) < (φ n))%Z -> ((φ w) < (φ n))%Z ->
    (Eb n nb dg x w = true <-> neighbours adj (vnum x) (vnum w)).
  Proof.
    intros x w Hx Hw. rewrite (Eb_spec n nb dg Hdeg'). unfold neighbours. split.
    - intros (_ & j & Hj & ->). apply nbr_val; auto.
    - intros Hin. split; [exact Hx|].
      apply In_nth with (d := 0%N) in Hin. destruct Hin as (jn & Hjn & Ejn).
      pose proof (Hdeg' x Hx) as Hd. pose proof (Hdg x Hx) as Hd'.
      exists (of_Z (Z.of_nat jn)).
      assert (Hj : (φ (of_Z (Z.of_nat jn))) = Z.of_nat jn).
      { rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia. }
      assert (Hjd : ((φ (of_Z (Z.of_nat jn))) < (φ (dg.[x])))%Z) by lia.
      split; [exact Hjd|].
      pose proof (Hnbr x _ Hx Hjd) as E. rewrite Hj, Nat2Z.id, Ejn in E.
      apply vnum_inj. pose proof (to_Z_bounded w).
      pose proof (to_Z_bounded (nbr nb x (of_Z (Z.of_nat jn)))). unfold vnum in *. lia.
  Qed.

  Lemma Eb_bounds : forall a b, Eb n nb dg a b = true ->
    ((φ a) < (φ n))%Z /\ ((φ b) < (φ n))%Z.
  Proof.
    intros a b E. apply (Eb_spec n nb dg Hdeg') in E. destruct E as (Ha & j & Hj & ->).
    split; [exact Ha | apply Hrange'; auto].
  Qed.

  Lemma Hsym' : forall a b, Eb n nb dg a b = true -> Eb n nb dg b a = true.
  Proof.
    intros a b E. destruct (Eb_bounds a b E) as [Ha Hb].
    apply Eb_neigh in E; auto. apply Eb_neigh; auto.
    destruct Hv as [_ _ _ _ _ _ Hm]. apply Hm; [apply vnum_inter; exact Ha | exact E].
  Qed.

  Lemma Hirr' : forall a, Eb n nb dg a a = false.
  Proof.
    intros a. destruct (Eb n nb dg a a) eqn:E; [|reflexivity]. exfalso.
    destruct (Eb_bounds a a E) as [Ha _].
    apply Eb_neigh in E; auto.
    destruct Hv as [_ _ _ _ _ Hi _]. exact (Hi _ (vnum_inter a Ha) E).
  Qed.

  (* the independent sets of the tables are the placements *)
  Lemma has_placement : forall kn : nat,
    has (Eb n nb dg) (fun x => ((φ x) < (φ n))%Z) kn <->
    exists ds, placement adj (N.of_nat kn) ds.
  Proof.
    intros kn. split.
    - intros (S & HS & HN & HP & HE). exists (map vnum S).
      unfold placement. split; [unfold len; rewrite length_map; congruence|].
      split; [apply NoDup_map_NoDup_ForallPairs; [|exact HN]|].
      { intros a b _ _. apply vnum_inj. }
      split.
      + intros x Hx. apply in_map_iff in Hx. destruct Hx as (s & <- & Hs).
        apply vnum_inter, HP, Hs.
      + intros a b Ha Hb Hab.
        apply in_map_iff in Ha. destruct Ha as (s1 & <- & Hs1).
        apply in_map_iff in Hb. destruct Hb as (s2 & <- & Hs2).
        apply Eb_neigh in Hab; [| apply HP; auto | apply HP; auto].
        rewrite HE in Hab by assumption. discriminate.
    - intros (ds & Hl & HN & Hi & Hne).
      set (g := fun d : N => of_Z (Z.of_N d - 1)).
      assert (Hg : forall d, In d ds -> vnum (g d) = d /\ ((φ (g d)) < (φ n))%Z).
      { intros d Hd. pose proof (Hi d Hd) as Hid. unfold is_intersection, len in Hid.
        assert (E : (φ (g d)) = (Z.of_N d - 1)%Z).
        { unfold g. rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val.
          destruct Hv as [_ Hn _ _ _ _ _]. unfold len in Hn. lia. }
        unfold vnum. rewrite E. split; lia. }
      assert (Hm : map vnum (map g ds) = ds).
      { rewrite map_map. rewrite <- (map_id ds) at 2. apply map_ext_in.
        intros d Hd. apply Hg, Hd. }
      exists (map g ds). split; [unfold len in Hl; rewrite length_map; lia|].
      split; [apply (NoDup_map_inv vnum); rewrite Hm; exact HN|].
      split.
      + intros x Hx. apply in_map_iff in Hx. destruct Hx as (d & <- & Hd). apply Hg, Hd.
      + intros a b Ha Hb.
        apply in_map_iff in Ha. destruct Ha as (d1 & <- & Hd1).
        apply in_map_iff in Hb. destruct Hb as (d2 & <- & Hd2).
        destruct (Eb n nb dg (g d1) (g d2)) eqn:E; [|reflexivity]. exfalso.
        apply Eb_neigh in E; [| apply Hg; auto | apply Hg; auto].
        rewrite (proj1 (Hg d1 Hd1)), (proj1 (Hg d2 Hd2)) in E.
        exact (Hne d1 d2 Hd1 Hd2 E).
  Qed.
End Input.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma pred_val : forall (a : int) (z : Z), (φ a) = z -> (1 <= z)%Z ->
  ((φ (a - 1)) + 1)%Z = z.
Proof. intros a z E H. subst z. sia. Qed.

(* The spec's match on the boolean answer, from the iff form. *)
Lemma bool_match_of_iff : forall (b : bool) (P : Prop),
  (b = true <-> P) -> match b with true => P | false => ~ P end.
Proof.
  intros [|] P H; [apply H; reflexivity | intros HP; apply H in HP; discriminate].
Qed.

Lemma basincity_impl_correct :
  forall (k : N) (adj : list (list N)) (x : uint) (y : array (array uint)),
  valid_input k adj -> repr x k -> repr y adj ->
  exists b : bool, repr (basincity_impl x y) b /\ basincity_spec k adj b.
Proof.
  intros k adj x y Hv Hx Hy.
  exists (basincity_impl x y). split; [reflexivity|].
  destruct (repr_rows y adj Hy) as [HnA0 Hrows0].
  assert (HnA : (φ (PArray.length@{Set} y)) = Z.of_nat (List.length adj)) by exact HnA0.
  assert (Hrows : forall v, ((φ v) < (φ (PArray.length@{Set} y)))%Z ->
    (φ (PArray.length@{Set} y.[v])) = Z.of_nat (List.length (line adj (vnum v))) /\
    forall j, ((φ j) < (φ (PArray.length@{Set} y.[v])))%Z ->
      Z.of_N (nth (Z.to_nat (φ j)) (line adj (vnum v)) 0%N) = (φ (y.[v].[j])))
    by exact Hrows0.
  clear HnA0 Hrows0.
  unfold basincity_impl.
  set (n := PArray.length y) in *.
  assert (Hn100 : ((φ n) <= 100000)%Z)
    by (destruct Hv as [_ H _ _ _ _ _]; unfold len in H; lia).
  assert (Hk15 : ((φ x) <= 15)%Z)
    by (destruct Hv as [H _ _ _ _ _ _]; unfold repr, repr_uint in Hx; lia).
  assert (Hmk : forall m : int, ((φ m) <= 400000)%Z ->
            PArray.length (PArray.make m 0) = m).
  { intros m Hm. rewrite alength_make.
    replace (m <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  assert (H4n : (φ (4 * n)) = (4 * (φ n))%Z) by sia.
  destruct (fill_dg_spec y n _ 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0))
              eq_refl ltac:(pose proof (to_Z_bounded n); change (φ 0) with 0%Z; lia)
              (Hmk n ltac:(lia))
              ltac:(intros v Hv'; change (φ 0) with 0%Z in Hv';
                    pose proof (to_Z_bounded v); lia)) as [Hdl Hdc].
  destruct (fill_nb_spec y n _ 0 (PArray.make (4 * n) 0) (Zwf_well_founded 0 (gap n 0))
              eq_refl ltac:(pose proof (to_Z_bounded n); change (φ 0) with 0%Z; lia)
              Hn100 (Hmk (4 * n) ltac:(lia))
              ltac:(intros v j Hv'; change (φ 0) with 0%Z in Hv';
                    pose proof (to_Z_bounded v); lia)) as [Hnl Hnc].
  set (dg := fill_dg y n 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0))) in *.
  set (nb := fill_nb y n 0 (PArray.make (4 * n) 0) (Zwf_well_founded 0 (gap n 0))) in *.
  assert (Hdg : forall v, ((φ v) < (φ n))%Z ->
    (φ (dg.[v])) = Z.of_nat (List.length (line adj (vnum v)))).
  { intros v H. rewrite Hdc by exact H. apply (Hrows v H). }
  assert (Hdeg := Hdeg' k adj Hv n dg HnA Hdg).
  assert (Hnbr : forall v j, ((φ v) < (φ n))%Z -> ((φ j) < (φ (dg.[v])))%Z ->
    ((φ (nbr nb v j)) + 1)%Z = Z.of_N (nth (Z.to_nat (φ j)) (line adj (vnum v)) 0%N)).
  { intros v j H Hj. pose proof (Hdeg v H) as Hd4. pose proof (Hdg v H) as Hdv.
    assert (Hjl : (Z.to_nat (φ j) < List.length (line adj (vnum v)))%nat)
      by (pose proof (to_Z_bounded j); lia).
    rewrite Hdc in Hj, Hd4 by exact H.
    destruct (Hrows v H) as [Hrl Hrc].
    unfold nbr. rewrite Hnc by (auto; lia).
    pose proof (Hrc j Hj) as Ev.
    (* the neighbour number is at least 1 *)
    assert (Hin : In (nth (Z.to_nat (φ j)) (line adj (vnum v)) 0%N) (line adj (vnum v))).
    { apply nth_In. exact Hjl. }
    destruct Hv as [_ _ _ Hr _ _ _].
    pose proof (Hr _ _ (vnum_inter adj n HnA v H) Hin) as Hi.
    unfold is_intersection in Hi.
    apply (pred_val _ _ (eq_sym Ev)). lia. }
  pose proof (search_spec n nb dg Hn100 Hdeg (Hrange' k adj Hv n nb dg HnA Hdg Hnbr)
                (Hsym' k adj Hv n nb dg HnA Hdg Hnbr) (Hirr' k adj Hv n nb dg HnA Hdg Hnbr)
                _ x (PArray.make n 0) (Zwf_well_founded 0 (φ x)) eq_refl Hk15) as Hs.
  destruct Hs as [_ Hs].
  { split; [apply Hmk; lia|]. intros v _. left. apply aget_make. }
  unfold basincity_spec. apply bool_match_of_iff. rewrite Hs.
  rewrite (has_iff (Eb n nb dg) _ (fun v => ((φ v) < (φ n))%Z)).
  2:{ intros v. unfold Pr. rewrite aget_make. tauto. }
  rewrite (has_placement k adj Hv n nb dg HnA Hdg Hnbr).
  replace (N.of_nat (Z.to_nat (φ x))) with k; [reflexivity|].
  unfold repr, repr_uint in Hx. lia.
Qed.

Definition basincity_correct :
  forall (k : N) (adj : list (list N)) (x : uint) (y : array (array uint)),
  valid_input k adj -> repr x k -> repr y adj ->
  exists b : bool, repr (basincity x y) b /\ basincity_spec k adj b
  := basincity_impl_correct.
