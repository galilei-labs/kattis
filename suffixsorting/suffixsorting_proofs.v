(* Correctness proofs for suffixsorting_implem.v. *)
From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Permutation Sorted String Ascii.
From Stdlib Require PrimString Sint63.
Import ListNotations.

Unset Lia Cache.
Open Scope nat_scope.

Require Export suffixsorting_implem.
Open Scope nat_scope.


(* ================================================================== *)
(* Math side: lexicographic comparison of code lists                   *)
(* ================================================================== *)

Fixpoint lcmp (u v : list N) : comparison :=
  match u, v with
  | [], [] => Eq
  | [], _ :: _ => Lt
  | _ :: _, [] => Gt
  | x :: u', y :: v' =>
      match N.compare x y with Eq => lcmp u' v' | c => c end
  end.

Lemma lcmp_eq : forall u v, lcmp u v = Eq -> u = v.
Proof.
  induction u as [|x u IH]; destruct v as [|y v]; simpl; try discriminate; auto.
  intros H. destruct (N.compare x y) eqn:E; try discriminate.
  apply N.compare_eq in E. subst. f_equal. auto.
Qed.

Lemma lcmp_antisym : forall u v, lcmp v u = CompOpp (lcmp u v).
Proof.
  induction u as [|x u IH]; destruct v as [|y v]; simpl; auto.
  rewrite (N.compare_antisym x y). destruct (N.compare x y); simpl; auto.
Qed.

Lemma lcmp_firstn_add : forall k m u v,
  lcmp (firstn (k + m) u) (firstn (k + m) v) =
  match lcmp (firstn k u) (firstn k v) with
  | Eq => lcmp (firstn m (skipn k u)) (firstn m (skipn k v))
  | c => c
  end.
Proof.
  induction k as [|k IH]; intros m u v.
  - reflexivity.
  - destruct u as [|x u], v as [|y v]; simpl; rewrite ?firstn_nil; try reflexivity.
    destruct (N.compare x y); auto.
Qed.

Lemma lcmp_firstn_lt : forall m u v,
  lcmp (firstn m u) (firstn m v) = Lt -> lcmp u v = Lt.
Proof.
  induction m as [|m IH]; intros u v H; [discriminate|].
  destruct u as [|x u], v as [|y v]; simpl in *; try discriminate; auto.
  destruct (N.compare x y); auto.
Qed.

(* the code list of a string *)
Fixpoint codes (s : string) : list N :=
  match s with
  | EmptyString => []
  | String c s' => N_of_ascii c :: codes s'
  end.

Lemma compare_codes : forall u v, String.compare u v = lcmp (codes u) (codes v).
Proof.
  induction u as [|a u IH]; destruct v as [|b v]; simpl; auto.
  unfold Ascii.compare. destruct (N.compare (N_of_ascii a) (N_of_ascii b)); auto.
Qed.

Lemma codes_length : forall s, List.length (codes s) = String.length s.
Proof. induction s; simpl; auto. Qed.

Lemma substring0 : forall s m, String.length s <= m -> substring 0 m s = s.
Proof.
  induction s as [|c s IH]; intros m Hm.
  - destruct m; reflexivity.
  - destruct m as [|m]; simpl in Hm; [lia|]. simpl. f_equal. apply IH. lia.
Qed.

Lemma codes_substring : forall i m s, String.length s <= i + m ->
  codes (substring i m s) = skipn i (codes s).
Proof.
  induction i as [|i IH]; intros m s Hs.
  - rewrite substring0 by exact Hs. reflexivity.
  - destruct s as [|c s]; [reflexivity|]. simpl in *. apply IH. lia.
Qed.

Lemma codes_get : forall s k c, String.get k s = Some c ->
  nth_error (codes s) k = Some (N_of_ascii c).
Proof.
  induction s as [|a s IH]; destruct k as [|k]; simpl; intros c H;
    try discriminate; [congruence | auto].
Qed.

(* the key of position i at length k: the first k codes of suffix i *)
Definition K (L : list N) (k i : nat) : list N := firstn k (skipn i L).

(* ================================================================== *)
(* Math side: sortedness by a key                                      *)
(* ================================================================== *)

Definition le_f (f : int -> Z) (x y : int) : Prop := (f x <= f y)%Z.

Lemma sorted_nth : forall f l, Sorted (le_f f) l -> forall t d, S t < List.length l ->
  le_f f (nth t l d) (nth (S t) l d).
Proof.
  intros f. induction l as [|a l IH]; simpl; intros Hs t d Ht; [lia|].
  apply Sorted_inv in Hs as [Hs Hh]. destruct t as [|t].
  - destruct l as [|b l]; simpl in *; [lia|]. inversion Hh; auto.
  - apply IH; auto. lia.
Qed.

Lemma SS_app : forall (R : int -> int -> Prop) A B,
  StronglySorted R A -> StronglySorted R B ->
  (forall a b, In a A -> In b B -> R a b) -> StronglySorted R (A ++ B).
Proof.
  intros R A B. induction A as [|x A IH]; simpl; intros HA HB HAB; [exact HB|].
  apply StronglySorted_inv in HA as [HA Hx]. constructor.
  - apply IH; auto.
  - apply Forall_app. split; [exact Hx|]. apply Forall_forall. intros y Hy. apply HAB; auto.
Qed.

Lemma SS_filter : forall (R : int -> int -> Prop) f l,
  StronglySorted R l -> StronglySorted R (filter f l).
Proof.
  intros R f. induction l as [|x l IH]; simpl; intros H; [constructor|].
  apply StronglySorted_inv in H as [H Hx]. destruct (f x); [constructor|]; auto.
  rewrite Forall_forall in *. intros y Hy. apply filter_In in Hy as [Hy _]. auto.
Qed.

Lemma SS_all : forall (R : int -> int -> Prop) l,
  (forall x y, In x l -> In y l -> R x y) -> StronglySorted R l.
Proof.
  intros R. induction l as [|x l IH]; intros H; constructor.
  - apply IH. intros a b Ha Hb. apply H; right; assumption.
  - apply Forall_forall. intros y Hy. apply H; [left; reflexivity | right; exact Hy].
Qed.

Lemma SS_impl : forall (R R' : int -> int -> Prop) l,
  (forall x y, In x l -> In y l -> R x y -> R' x y) ->
  StronglySorted R l -> StronglySorted R' l.
Proof.
  intros R R'. induction l as [|x l IH]; intros H HS; constructor;
    apply StronglySorted_inv in HS as [HS Hx].
  - apply IH; auto. intros a b Ha Hb. apply H; right; assumption.
  - rewrite Forall_forall in *. intros y Hy. apply H; [left | right | apply Hx]; auto.
Qed.

(* ================================================================== *)
(* Math side: the counting sort as a list function                      *)
(* ================================================================== *)

Section CSort.
Variable f : int -> nat.

(* the elements of key v, in their order in l *)
Definition chunk (v : nat) (l : list int) : list int := filter (fun x => Nat.eqb (f x) v) l.
Definition ceq (v : nat) (l : list int) : nat := List.length (chunk v l).
(* the number of elements of key below v: where chunk v starts *)
Definition clt (v : nat) (l : list int) : nat :=
  List.length (filter (fun x => Nat.ltb (f x) v) l).
(* the stable counting sort of l on the keys a .. a + m - 1 *)
Definition cs (l : list int) (a m : nat) : list int := flat_map (fun v => chunk v l) (seq a m).

Lemma chunk_app1 : forall v l x,
  chunk v (l ++ [x]) = chunk v l ++ (if Nat.eqb (f x) v then [x] else []).
Proof. intros. unfold chunk. rewrite filter_app. reflexivity. Qed.

Lemma ceq_app1 : forall v l x,
  ceq v (l ++ [x]) = ceq v l + (if Nat.eqb (f x) v then 1 else 0).
Proof.
  intros. unfold ceq. rewrite chunk_app1, length_app. destruct (Nat.eqb (f x) v); reflexivity.
Qed.

Lemma ceq_app : forall v l1 l2, ceq v (l1 ++ l2) = ceq v l1 + ceq v l2.
Proof. intros. unfold ceq, chunk. rewrite filter_app, length_app. reflexivity. Qed.

Lemma ceq_le : forall v l, ceq v l <= List.length l.
Proof.
  intros v. induction l as [|x l IH]; [reflexivity|]. unfold ceq, chunk in *. simpl.
  destruct (Nat.eqb (f x) v); simpl; lia.
Qed.

Lemma clt_le : forall v l, clt v l <= List.length l.
Proof.
  intros v. induction l as [|x l IH]; [reflexivity|]. unfold clt in *. simpl.
  destruct (Nat.ltb (f x) v); simpl; lia.
Qed.

Lemma clt_0 : forall l, clt 0 l = 0.
Proof.
  induction l as [|x l IH]; [reflexivity|]. unfold clt in *. simpl.
  destruct (f x); simpl; exact IH.
Qed.

Lemma clt_S : forall v l, clt (S v) l = clt v l + ceq v l.
Proof.
  intros v. induction l as [|x l IH]; [reflexivity|]. unfold clt, ceq, chunk in *. simpl.
  destruct (Nat.ltb_spec (f x) (S v)), (Nat.ltb_spec (f x) v), (Nat.eqb_spec (f x) v);
    simpl; lia.
Qed.

Lemma clt_mono : forall v w l, v <= w -> clt v l <= clt w l.
Proof.
  intros v w l H. induction H as [|w H IH]; [lia|]. rewrite clt_S. lia.
Qed.

Lemma clt_all : forall B l, (forall x, In x l -> f x < B) -> clt B l = List.length l.
Proof.
  intros B. induction l as [|x l IH]; intros H; [reflexivity|]. unfold clt in *. simpl.
  destruct (Nat.ltb_spec (f x) B) as [E|E].
  - simpl. f_equal. apply IH. intros y Hy. apply H. right. exact Hy.
  - exfalso. specialize (H x (or_introl eq_refl)). lia.
Qed.

Lemma filter_part : forall (P Q R : int -> bool) l,
  (forall x, R x = orb (P x) (Q x)) -> (forall x, P x = true -> Q x = false) ->
  Permutation (filter P l ++ filter Q l) (filter R l).
Proof.
  intros P Q R l HR HPQ. induction l as [|x l IH]; [reflexivity|]. simpl.
  rewrite HR. destruct (P x) eqn:Ep.
  - rewrite (HPQ x Ep). simpl. constructor. exact IH.
  - destruct (Q x); simpl.
    + eapply perm_trans; [apply Permutation_sym, Permutation_middle|]. constructor. exact IH.
    + exact IH.
Qed.

Lemma filter_none : forall (P : int -> bool) l, (forall x, P x = false) -> filter P l = [].
Proof. intros P l H. induction l as [|x l IH]; simpl; [reflexivity|]. rewrite H. exact IH. Qed.

Lemma filter_every : forall (P : int -> bool) l, (forall x, In x l -> P x = true) -> filter P l = l.
Proof.
  intros P l H. induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite H by (left; reflexivity). f_equal. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma cs_perm_gen : forall l m a,
  Permutation (cs l a m) (filter (fun x => andb (Nat.leb a (f x)) (Nat.ltb (f x) (a + m))) l).
Proof.
  intros l m. induction m as [|m IH]; intros a.
  - change (cs l a 0) with (@nil int). rewrite filter_none; [reflexivity|]. intros x.
    rewrite Nat.add_0_r.
    destruct (Nat.leb_spec a (f x)), (Nat.ltb_spec (f x) a); simpl; try reflexivity; lia.
  - change (cs l a (S m)) with (chunk a l ++ cs l (S a) m).
    eapply perm_trans; [apply Permutation_app_head, IH|].
    apply filter_part.
    + intros x. destruct (Nat.eqb_spec (f x) a), (Nat.leb_spec a (f x)),
        (Nat.ltb_spec (f x) (a + S m)), (Nat.leb_spec (S a) (f x)),
        (Nat.ltb_spec (f x) (S a + m)); simpl; try reflexivity; lia.
    + intros x E. apply Nat.eqb_eq in E.
      destruct (Nat.leb_spec (S a) (f x)); simpl; [lia | reflexivity].
Qed.

Lemma cs_perm : forall B l, (forall x, In x l -> f x < B) -> Permutation (cs l 0 B) l.
Proof.
  intros B l H. eapply perm_trans; [apply cs_perm_gen|].
  rewrite filter_every; [reflexivity|]. intros x Hx. specialize (H x Hx).
  destruct (Nat.ltb_spec (f x) (0 + B)); [reflexivity | lia].
Qed.

Lemma cs_ss : forall (R : int -> int -> Prop) l m a,
  (forall v, StronglySorted R (chunk v l)) ->
  (forall x y, In x l -> In y l -> f x < f y -> R x y) ->
  StronglySorted R (cs l a m).
Proof.
  intros R l m. induction m as [|m IH]; intros a Hc Hlt; [constructor|].
  change (cs l a (S m)) with (chunk a l ++ cs l (S a) m).
  apply SS_app; auto.
  intros x y Hx Hy. unfold chunk in Hx. apply filter_In in Hx as [Hx Ex].
  apply Nat.eqb_eq in Ex.
  unfold cs in Hy. apply in_flat_map in Hy as (v & Hv & Hy).
  apply in_seq in Hv. unfold chunk in Hy. apply filter_In in Hy as [Hy Ey].
  apply Nat.eqb_eq in Ey. apply Hlt; auto. lia.
Qed.

End CSort.
(* ================================================================== *)
(* Uint63 / PArray plumbing                                            *)
(* ================================================================== *)

Open Scope uint63_scope.
Open Scope array_scope.

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

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma aget_make : forall (n i b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

(* ================================================================== *)
(* Prop side: unfolding equations                                      *)
(* ================================================================== *)

Lemma init_rank_eq : forall x n i r H, init_rank x n i r H =
  match bdec (i <? n) with
  | left Hi =>
      init_rank x n (i + 1) r.[i <- PrimString.get x i + 1]
        (Acc_inv H (dec_step n i Hi))
  | right _ => r
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma init_id_eq : forall n i sa H, init_id n i sa H =
  match bdec (i <? n) with
  | left Hi => init_id n (i + 1) sa.[i <- i] (Acc_inv H (dec_step n i Hi))
  | right _ => sa
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma count_loop_eq : forall r n k src i cnt H, count_loop r n k src i cnt H =
  match bdec (i <? n) with
  | left Hi =>
      count_loop r n k src (i + 1)
        cnt.[skey r n k src.[i] <- cnt.[skey r n k src.[i]] + 1] (Acc_inv H (dec_step n i Hi))
  | right _ => cnt
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma prefix_loop_eq : forall B v acc cnt H, prefix_loop B v acc cnt H =
  match bdec (v <? B) with
  | left Hv =>
      prefix_loop B (v + 1) (acc + cnt.[v]) cnt.[v <- acc] (Acc_inv H (dec_step B v Hv))
  | right _ => cnt
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma place_loop_eq : forall r n k src i cnt dst H, place_loop r n k src i cnt dst H =
  match bdec (i <? n) with
  | left Hi =>
      place_loop r n k src (i + 1)
        cnt.[skey r n k src.[i] <- cnt.[skey r n k src.[i]] + 1]
        dst.[cnt.[skey r n k src.[i]] <- src.[i]] (Acc_inv H (dec_step n i Hi))
  | right _ => dst
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma rank_loop_eq : forall r n k sa t cur nr H, rank_loop r n k sa t cur nr H =
  match bdec (t <? n) with
  | left Ht =>
      let c := if (if r.[sa.[t - 1]] =? r.[sa.[t]]
                   then skey r n k sa.[t - 1] =? skey r n k sa.[t] else false)
               then cur else cur + 1 in
      rank_loop r n k sa (t + 1) c nr.[sa.[t] <- c] (Acc_inv H (dec_step n t Ht))
  | right _ => (nr, cur)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma rounds_eq : forall n k r nr sa tmp H, rounds n k r nr sa tmp H =
  let tmp1 := csort r n k sa tmp in
  let sa1 := csort r n 0 tmp1 sa in
  let q := rank_loop r n k sa1 1 1 nr.[sa1.[0] <- 1] (Zwf_well_founded 0 (gap n 1)) in
  if snd q =? n then sa1
  else
    match bdec (andb (k <? k + k) (k + k <? n)) with
    | left Hc => rounds n (k + k) (fst q) r sa1 tmp1 (Acc_inv H (dec_dbl n k Hc))
    | right _ => sa1
    end.
Proof. intros. destruct H. reflexivity. Qed.
(* ================================================================== *)
(* Prop side: indices and segments                                     *)
(* ================================================================== *)

Definition nt (i : int) : nat := Z.to_nat (φ i).

Lemma of_nt : forall i : int, of_nat (nt i) = i.
Proof.
  intros i. unfold nt. rewrite Z2Nat.id by (pose proof (to_Z_bounded i); lia).
  apply of_to_Z.
Qed.

Lemma phi_of_nat : forall t : nat, (Z.of_nat t < wB)%Z -> (φ (of_nat t)) = Z.of_nat t.
Proof. intros t Ht. rewrite of_Z_spec. apply Z.mod_small. lia. Qed.

Lemma nt_of_nat : forall t : nat, (Z.of_nat t < wB)%Z -> nt (of_nat t) = t.
Proof. intros t Ht. unfold nt. rewrite phi_of_nat by exact Ht. apply Nat2Z.id. Qed.

Lemma nt_phi : forall i : int, Z.of_nat (nt i) = (φ i).
Proof. intros i. unfold nt. rewrite Z2Nat.id by (pose proof (to_Z_bounded i); lia). reflexivity. Qed.

Lemma eqb_Z : forall x y : int, (x =? y) = Z.eqb (φ x) (φ y).
Proof.
  intros x y. destruct (x =? y) eqn:E; symmetry.
  - apply Z.eqb_eq. apply Uint63.eqb_spec in E. subst. reflexivity.
  - apply Z.eqb_neq. intro F. apply to_Z_inj in F. subst.
    rewrite Uint63.eqb_refl in E. discriminate.
Qed.

Lemma leb_Z : forall x y : int, (x <=? y) = Z.leb (φ x) (φ y).
Proof.
  intros x y. destruct (x <=? y) eqn:E; symmetry.
  - apply Z.leb_le. apply Uint63.leb_spec in E. exact E.
  - apply Z.leb_gt. rewrite <- Bool.not_true_iff_false, Uint63.leb_spec in E. lia.
Qed.

Definition seg (a : array int) (lo len : nat) : list int :=
  map (fun t => a.[of_nat t]) (seq lo len).

Lemma seg_length : forall a lo m, List.length (seg a lo m) = m.
Proof. intros. unfold seg. rewrite length_map, length_seq. reflexivity. Qed.

Lemma seg_app : forall a lo m1 m2,
  seg a lo (m1 + m2) = seg a lo m1 ++ seg a (lo + m1) m2.
Proof. intros. unfold seg. rewrite seq_app, map_app. reflexivity. Qed.

Lemma seg_S : forall a lo m, seg a lo (S m) = seg a lo m ++ [a.[of_nat (lo + m)]].
Proof. intros. unfold seg. rewrite seq_S, map_app. reflexivity. Qed.

Lemma seg_cons : forall a lo m, seg a lo (S m) = a.[of_nat lo] :: seg a (S lo) m.
Proof. reflexivity. Qed.

Lemma seg_ext : forall a b lo m,
  (forall t, lo <= t < lo + m -> a.[of_nat t] = b.[of_nat t]) -> seg a lo m = seg b lo m.
Proof.
  intros a b lo m H. unfold seg. apply map_ext_in. intros t Ht.
  apply in_seq in Ht. apply H. lia.
Qed.

Lemma seg_nth_error : forall a lo m t, t < m ->
  nth_error (seg a lo m) t = Some a.[of_nat (lo + t)].
Proof.
  intros a lo m t Ht. unfold seg. rewrite nth_error_map, nth_error_seq.
  destruct (Nat.ltb_spec t m); [reflexivity | lia].
Qed.

Lemma seg_nth : forall a lo m t d, t < m -> nth t (seg a lo m) d = a.[of_nat (lo + t)].
Proof. intros. apply nth_error_nth. apply seg_nth_error. exact H. Qed.

(* ================================================================== *)
(* Prop side: the filling loops                                        *)
(* ================================================================== *)

Lemma init_rank_spec : forall x n (z : Z) i r H,
  gap n i = z -> PArray.length r = n -> ((φ i) <= (φ n))%Z ->
  (forall t, ((φ t) < (φ i))%Z -> r.[t] = PrimString.get x t + 1) ->
  PArray.length (init_rank x n i r H) = n /\
  forall t, ((φ t) < (φ n))%Z -> (init_rank x n i r H).[t] = PrimString.get x t + 1.
Proof.
  intros x n z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i r H Hz Hlen Hin Hinv.
  rewrite init_rank_eq.
  destruct (bdec (i <? n)) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    eapply IH; [ | reflexivity | | | ].
    + rewrite <- Hz. apply dec_step. exact Hi.
    + rewrite alength_set. exact Hlen.
    + lia.
    + intros t Ht. rewrite Hi1 in Ht.
      destruct (Z.eq_dec (φ t) (φ i)) as [E | E].
      * apply to_Z_inj in E. subst t.
        apply aget_set_same. rewrite Hlen. exact Hi.
      * rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity).
        apply Hinv. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi.
    split; [exact Hlen|]. intros t Ht. apply Hinv. lia.
Qed.

Lemma init_id_spec : forall n (z : Z) i sa H,
  gap n i = z -> PArray.length sa = n -> ((φ i) <= (φ n))%Z ->
  (forall t, ((φ t) < (φ i))%Z -> sa.[t] = t) ->
  PArray.length (init_id n i sa H) = n /\
  forall t, ((φ t) < (φ n))%Z -> (init_id n i sa H).[t] = t.
Proof.
  intros n z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i r H Hz Hlen Hin Hinv.
  rewrite init_id_eq.
  destruct (bdec (i <? n)) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    eapply IH; [ | reflexivity | | | ].
    + rewrite <- Hz. apply dec_step. exact Hi.
    + rewrite alength_set. exact Hlen.
    + lia.
    + intros t Ht. rewrite Hi1 in Ht.
      destruct (Z.eq_dec (φ t) (φ i)) as [E | E].
      * apply to_Z_inj in E. subst t.
        apply aget_set_same. rewrite Hlen. exact Hi.
      * rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity).
        apply Hinv. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi.
    split; [exact Hlen|]. intros t Ht. apply Hinv. lia.
Qed.

Lemma nt_S : forall i m : int, ((φ i) < (φ m))%Z -> nt (i + 1) = S (nt i).
Proof.
  intros i m H. pose proof (to_Z_bounded m).
  assert (E : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold nt. rewrite E. pose proof (to_Z_bounded i). lia.
Qed.

(* ================================================================== *)
(* Prop side: the ranks along a sorted order                           *)
(* ================================================================== *)

(* the rank given to the t-th position of the sorted order: one more at
   every strict increase of the key g *)
Fixpoint Rk (g : nat -> Z) (t : nat) : Z :=
  match t with
  | O => 1%Z
  | S t' => (Rk g t' + (if Z.eqb (g t') (g (S t')) then 0 else 1))%Z
  end.

Lemma Rk_step : forall g t, (Rk g t <= Rk g (S t) <= Rk g t + 1)%Z.
Proof. intros g t. cbn [Rk]. destruct (Z.eqb (g t) (g (S t))); lia. Qed.

Lemma Rk_bounds : forall g t, (1 <= Rk g t <= Z.of_nat t + 1)%Z.
Proof.
  intros g t. induction t as [|t IH]; [cbn; lia|].
  pose proof (Rk_step g t). lia.
Qed.

Lemma Rk_mono : forall g p d, (Rk g p <= Rk g (p + d)%nat <= Rk g p + Z.of_nat d)%Z.
Proof.
  intros g p d. induction d as [|d IH]; [rewrite Nat.add_0_r; lia|].
  rewrite Nat.add_succ_r. pose proof (Rk_step g (p + d)). lia.
Qed.

Lemma Rk_cmp : forall g n, (forall t, (S t < n)%nat -> (g t <= g (S t))%Z) ->
  forall p d, (p + d < n)%nat ->
  Z.compare (Rk g p) (Rk g (p + d)%nat) = Z.compare (g p) (g (p + d)%nat).
Proof.
  intros g n Hs p d. induction d as [|d IH]; intros Hd.
  - rewrite Nat.add_0_r, !Z.compare_refl. reflexivity.
  - specialize (IH ltac:(lia)). pose proof (Hs (p + d)%nat ltac:(lia)) as Hg.
    pose proof (Rk_mono g p d) as Hm.
    rewrite Nat.add_succ_r. cbn [Rk].
    destruct (Z.eqb (g (p + d)%nat) (g (S (p + d)))) eqn:E.
    + apply Z.eqb_eq in E. rewrite <- E, Z.add_0_r. exact IH.
    + apply Z.eqb_neq in E.
      assert (Hle : (g p <= g (p + d)%nat)%Z).
      { apply (proj1 (Z.compare_le_iff _ _)). rewrite <- IH.
        apply (proj2 (Z.compare_le_iff _ _)). lia. }
      transitivity Lt; [apply Z.compare_lt_iff; lia | symmetry; apply Z.compare_lt_iff; lia].
Qed.

Lemma Rk_all_distinct : forall g n, (1 <= n)%nat -> Rk g (n - 1) = Z.of_nat n ->
  forall t, (S t < n)%nat -> g t <> g (S t).
Proof.
  intros g n Hn HR t Ht E.
  pose proof (Rk_bounds g t).
  pose proof (Rk_mono g (S t) (n - 1 - S t)) as Hm.
  replace (S t + (n - 1 - S t))%nat with (n - 1)%nat in Hm by lia.
  assert (Rk g (S t) = Rk g t) by (cbn [Rk]; rewrite (proj2 (Z.eqb_eq _ _) E); lia).
  lia.
Qed.

(* ================================================================== *)
(* Prop side: rank and key invariants                                  *)
(* ================================================================== *)

Lemma K_nil : forall L k i, (List.length L <= i)%nat -> K L k i = [].
Proof. intros L k i H. unfold K. rewrite skipn_all2 by exact H. destruct k; reflexivity. Qed.

Lemma K_cons : forall L k i, (i < List.length L)%nat -> (1 <= k)%nat ->
  exists x l, K L k i = x :: l.
Proof.
  intros L k i Hi Hk. unfold K. destruct (skipn i L) as [|x l] eqn:E.
  - apply (f_equal (@List.length N)) in E. rewrite length_skipn in E. simpl in E. lia.
  - destruct k as [|k]; [lia|]. simpl. eauto.
Qed.

Lemma K_double : forall L k i j,
  lcmp (K L (k + k) i) (K L (k + k) j) =
  match lcmp (K L k i) (K L k j) with
  | Eq => lcmp (K L k (i + k)) (K L k (j + k))
  | c => c
  end.
Proof.
  intros L k i j. unfold K. rewrite lcmp_firstn_add, !skipn_skipn.
  rewrite (Nat.add_comm k i), (Nat.add_comm k j). reflexivity.
Qed.

Lemma pair_cmp : forall a b c d : Z,
  (0 <= b < 8388608)%Z -> (0 <= d < 8388608)%Z ->
  Z.compare (a * 8388608 + b) (c * 8388608 + d) =
  match Z.compare a c with Eq => Z.compare b d | o => o end.
Proof.
  intros a b c d Hb Hd. destruct (Z.compare_spec a c) as [E|E|E].
  - subst c. apply Z.add_compare_mono_l.
  - apply Z.compare_lt_iff. nia.
  - apply Z.compare_gt_iff. nia.
Qed.

Lemma perm_facts : forall sa (n : nat),
  (Z.of_nat n < wB)%Z ->
  Permutation (map nt (seg sa 0 n)) (seq 0 n) ->
  (forall t, (t < n)%nat -> (nt sa.[of_nat t] < n)%nat) /\
  (forall t1 t2, (t1 < n)%nat -> (t2 < n)%nat -> sa.[of_nat t1] = sa.[of_nat t2] -> t1 = t2) /\
  (forall i, (i < n)%nat -> exists t, (t < n)%nat /\ nt sa.[of_nat t] = i).
Proof.
  intros sa n Hw HP.
  assert (Hnth : forall t, (t < n)%nat -> nth_error (map nt (seg sa 0 n)) t = Some (nt sa.[of_nat t])).
  { intros t Ht. rewrite nth_error_map, seg_nth_error by exact Ht. reflexivity. }
  split; [|split].
  - intros t Ht. pose proof (nth_error_In _ _ (Hnth t Ht)) as X.
    eapply Permutation_in in X; [|exact HP]. apply in_seq in X. lia.
  - intros t1 t2 H1 H2 E.
    assert (ND : NoDup (map nt (seg sa 0 n))).
    { eapply Permutation_NoDup; [apply Permutation_sym; exact HP | apply seq_NoDup]. }
    rewrite NoDup_nth_error in ND. apply ND.
    + rewrite length_map, seg_length. exact H1.
    + rewrite (Hnth t1 H1), (Hnth t2 H2), E. reflexivity.
  - intros i Hi. assert (Hin : In i (seq 0 n)) by (apply in_seq; lia).
    eapply Permutation_in in Hin; [|apply Permutation_sym; exact HP].
    apply In_nth_error in Hin as [t Ht].
    assert (Htn : (t < n)%nat).
    { rewrite <- (seg_length sa 0 n), <- (length_map nt).
      apply (proj1 (nth_error_Some _ _)). rewrite Ht. discriminate. }
    exists t. split; [exact Htn|]. rewrite Hnth in Ht by exact Htn. congruence.
Qed.

Lemma nt_inj : forall i j : int, nt i = nt j -> i = j.
Proof. intros i j E. rewrite <- (of_nt i), <- (of_nt j), E. reflexivity. Qed.

Lemma skipn_nth_error : forall (L : list N) i c, nth_error L i = Some c ->
  skipn i L = c :: skipn (S i) L.
Proof.
  induction L as [|a L IH]; destruct i as [|i]; simpl; intros c H; try discriminate.
  - injection H as <-. reflexivity.
  - apply IH. exact H.
Qed.

(* ================================================================== *)
(* Prop side: the counting sort on arrays                              *)
(* ================================================================== *)

Definition kfn (r : array int) (n k x : int) : nat := nt (skey r n k x).

Lemma phi_succ : forall i m : int, ((φ i) < (φ m))%Z -> (φ (i + 1)) = ((φ i) + 1)%Z.
Proof. intros i m H. pose proof (to_Z_bounded m). sia. Qed.

Lemma phi_add : forall a b : int, ((φ a) + (φ b) < wB)%Z -> (φ (a + b)) = ((φ a) + (φ b))%Z.
Proof. intros a b H. rewrite add_spec. apply Z.mod_small. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). lia. Qed.

Lemma seg_in0 : forall (a : array int) m t, (t < m)%nat -> In a.[of_nat t] (seg a 0 m).
Proof. intros a m t Ht. eapply nth_error_In. rewrite seg_nth_error by exact Ht. reflexivity. Qed.

Lemma nt_eq : forall i j : int, (φ i) = (φ j) -> nt i = nt j.
Proof. intros i j E. unfold nt. rewrite E. reflexivity. Qed.

Lemma cbound_spec : forall n, ((φ n) < 4194303)%Z ->
  (257 <= (φ (cbound n)))%Z /\ ((φ n) < (φ (cbound n)))%Z /\ ((φ (cbound n)) <= 4194303)%Z.
Proof.
  intros n Hn. unfold cbound. destruct (n <? 256) eqn:E.
  - rewrite ltb_spec in E. change (φ 256) with 256%Z in E. change (φ 257) with 257%Z. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E. change (φ 256) with 256%Z in E.
    assert ((φ (n + 1)) = ((φ n) + 1)%Z) by sia. lia.
Qed.

Lemma count_loop_spec : forall r n k src B,
  ((φ n) < 4194303)%Z ->
  (forall x, In x (seg src 0 (nt n)) -> ((φ (skey r n k x)) < (φ B))%Z) ->
  forall (z : Z) i cnt H,
  gap n i = z -> ((φ i) <= (φ n))%Z -> PArray.length cnt = B ->
  (forall c, ((φ c) < (φ B))%Z ->
     (φ (cnt.[c])) = Z.of_nat (ceq (kfn r n k) (nt c) (seg src 0 (nt i)))) ->
  PArray.length (count_loop r n k src i cnt H) = B /\
  (forall c, ((φ c) < (φ B))%Z ->
     (φ ((count_loop r n k src i cnt H).[c]))
     = Z.of_nat (ceq (kfn r n k) (nt c) (seg src 0 (nt n)))).
Proof.
  intros r n k src B Hn Hkey z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i cnt H Hz Hi Hlen Hinv.
  pose proof (nt_phi i). pose proof (nt_phi n).
  rewrite count_loop_eq.
  destruct (bdec (i <? n)) as [Hin | Hin].
  - pose proof Hin as Hin'. rewrite ltb_spec in Hin'.
    pose proof (phi_succ i n Hin') as Hi1.
    set (x := src.[i]). set (v := skey r n k x).
    assert (Hx : In x (seg src 0 (nt n))).
    { unfold x. rewrite <- (of_nt i). apply seg_in0. lia. }
    pose proof (Hkey x Hx) as Hv. fold v in Hv.
    assert (Hseg : seg src 0 (nt (i + 1)) = seg src 0 (nt i) ++ [x]).
    { rewrite (nt_S i n Hin'), seg_S. cbn [Nat.add]. rewrite of_nt. reflexivity. }
    assert (Hvb : (v <? PArray.length cnt) = true) by (rewrite ltb_spec, Hlen; exact Hv).
    apply (IH (gap n (i + 1))); [rewrite <- Hz; apply dec_step; exact Hin | reflexivity
      | lia | rewrite alength_set; exact Hlen | ].
    intros c Hc. rewrite Hseg, ceq_app1.
    destruct (Z.eq_dec (φ c) (φ v)) as [E | E].
    + apply to_Z_inj in E. subst c. rewrite aget_set_same by exact Hvb.
      replace (Nat.eqb (kfn r n k x) (nt v)) with true by (symmetry; apply Nat.eqb_eq; reflexivity).
      pose proof (Hinv v Hv) as Hc'.
      pose proof (ceq_le (kfn r n k) (nt v) (seg src 0 (nt i))) as Hle. rewrite seg_length in Hle.
      assert (Hb : ((φ (cnt.[v])) + 1 < wB)%Z) by (rewrite wB_val; lia).
      rewrite (phi_add _ 1) by (change (φ 1) with 1%Z; lia). change (φ 1) with 1%Z. lia.
    + rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity).
      replace (Nat.eqb (kfn r n k x) (nt c)) with false.
      * rewrite Hinv by exact Hc. lia.
      * symmetry. apply Nat.eqb_neq. intro F. apply E. unfold kfn in F. fold v in F.
        rewrite <- (nt_phi c), <- (nt_phi v), F. reflexivity.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hin.
    split; [exact Hlen|]. intros c Hc. rewrite Hinv by exact Hc.
    rewrite (nt_eq i n) by lia. reflexivity.
Qed.

Lemma prefix_loop_spec : forall (f : int -> nat) l B,
  ((φ B) <= 4194303)%Z -> (Z.of_nat (List.length l) <= 4194303)%Z ->
  forall (z : Z) v acc cnt H,
  gap B v = z -> ((φ v) <= (φ B))%Z -> PArray.length cnt = B ->
  (φ acc) = Z.of_nat (clt f (nt v) l) ->
  (forall c, ((φ c) < (φ v))%Z -> (φ (cnt.[c])) = Z.of_nat (clt f (nt c) l)) ->
  (forall c, ((φ v) <= (φ c) < (φ B))%Z -> (φ (cnt.[c])) = Z.of_nat (ceq f (nt c) l)) ->
  PArray.length (prefix_loop B v acc cnt H) = B /\
  (forall c, ((φ c) < (φ B))%Z ->
     (φ ((prefix_loop B v acc cnt H).[c])) = Z.of_nat (clt f (nt c) l)).
Proof.
  intros f l B HB Hl z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros v acc cnt H Hz Hv Hlen Hacc Hlo Hhi.
  pose proof (nt_phi v). pose proof (nt_phi B).
  rewrite prefix_loop_eq.
  destruct (bdec (v <? B)) as [HvB | HvB].
  - pose proof HvB as HvB'. rewrite ltb_spec in HvB'.
    pose proof (phi_succ v B HvB') as Hv1.
    assert (Hvb : (v <? PArray.length cnt) = true) by (rewrite Hlen; exact HvB).
    pose proof (clt_S f (nt v) l) as HS. pose proof (clt_le f (S (nt v)) l).
    pose proof (Hhi v (conj (Z.le_refl _) HvB')) as Hcv.
    apply (IH (gap B (v + 1))); [rewrite <- Hz; apply dec_step; exact HvB | reflexivity
      | lia | rewrite alength_set; exact Hlen | | | ].
    + rewrite (nt_S v B HvB'), HS.
      assert (Hb : ((φ acc) + (φ (cnt.[v])) < wB)%Z) by (rewrite wB_val; lia).
      rewrite phi_add by exact Hb. lia.
    + intros c Hc. destruct (Z.eq_dec (φ c) (φ v)) as [E | E].
      * apply to_Z_inj in E. subst c. rewrite aget_set_same by exact Hvb. exact Hacc.
      * rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity).
        apply Hlo. lia.
    + intros c Hc. rewrite aget_set_other by (intro F; subst c; lia). apply Hhi. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in HvB.
    split; [exact Hlen|]. intros c Hc. apply Hlo. lia.
Qed.

Lemma place_loop_spec : forall r n k src B,
  ((φ n) < 4194303)%Z -> ((φ B) <= 4194303)%Z ->
  (forall x, In x (seg src 0 (nt n)) -> ((φ (skey r n k x)) < (φ B))%Z) ->
  forall (z : Z) i cnt dst H,
  gap n i = z -> ((φ i) <= (φ n))%Z -> PArray.length cnt = B -> PArray.length dst = n ->
  (forall c, ((φ c) < (φ B))%Z ->
     (φ (cnt.[c])) = Z.of_nat (clt (kfn r n k) (nt c) (seg src 0 (nt n))
                             + ceq (kfn r n k) (nt c) (seg src 0 (nt i)))) ->
  (forall v t, (v < nt B)%nat -> (t < ceq (kfn r n k) v (seg src 0 (nt i)))%nat ->
     dst.[of_nat (clt (kfn r n k) v (seg src 0 (nt n)) + t)]
     = nth t (chunk (kfn r n k) v (seg src 0 (nt i))) 0) ->
  PArray.length (place_loop r n k src i cnt dst H) = n /\
  (forall v t, (v < nt B)%nat -> (t < ceq (kfn r n k) v (seg src 0 (nt n)))%nat ->
     (place_loop r n k src i cnt dst H).[of_nat (clt (kfn r n k) v (seg src 0 (nt n)) + t)]
     = nth t (chunk (kfn r n k) v (seg src 0 (nt n))) 0).
Proof.
  intros r n k src B Hn HB Hkey z.
  set (f := kfn r n k). set (l := seg src 0 (nt n)).
  assert (Hll : List.length l = nt n) by apply seg_length.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i cnt dst H Hz Hi Hlen Hdl Hinv Hdst.
  pose proof (nt_phi i) as Ni. pose proof (nt_phi n) as Nn. pose proof (nt_phi B) as NB.
  rewrite place_loop_eq.
  destruct (bdec (i <? n)) as [Hin | Hin].
  - pose proof Hin as Hin'. rewrite ltb_spec in Hin'.
    pose proof (phi_succ i n Hin') as Hi1.
    set (x := src.[i]). set (v := skey r n k x).
    set (p := seg src 0 (nt i)).
    assert (Hx : In x l).
    { unfold x, l. rewrite <- (of_nt i). apply seg_in0. lia. }
    pose proof (Hkey x Hx) as Hv. fold v in Hv.
    pose proof (nt_phi v) as Nv.
    assert (Hfx : f x = nt v) by reflexivity.
    assert (Hseg : seg src 0 (S (nt i)) = p ++ [x]).
    { unfold p. rewrite seg_S. cbn [Nat.add]. rewrite of_nt. reflexivity. }
    assert (Hpre : forall w, (ceq f w (p ++ [x]) <= ceq f w l)%nat).
    { intros w. unfold l.
      replace (nt n) with (S (nt i) + (nt n - S (nt i)))%nat by lia.
      rewrite seg_app, Hseg. rewrite (ceq_app f w (p ++ [x])). lia. }
    assert (Hvb : (v <? PArray.length cnt) = true) by (rewrite ltb_spec, Hlen; exact Hv).
    set (pos := cnt.[v]).
    assert (Hpos : (φ pos) = Z.of_nat (clt f (nt v) l + ceq f (nt v) p)) by (apply Hinv; exact Hv).
    assert (Hceqx : ceq f (nt v) (p ++ [x]) = (ceq f (nt v) p + 1)%nat).
    { rewrite ceq_app1, Hfx, Nat.eqb_refl. reflexivity. }
    pose proof (Hpre (nt v)) as Hpv. rewrite Hceqx in Hpv.
    pose proof (clt_S f (nt v) l) as HSv. pose proof (clt_le f (S (nt v)) l) as HLv.
    assert (Hposb : ((φ pos) < (φ n))%Z) by lia.
    assert (Hpd : (pos <? PArray.length dst) = true) by (rewrite ltb_spec, Hdl; exact Hposb).
    pose proof (phi_succ pos n Hposb) as Hp1.
    apply (IH (gap n (i + 1))); [rewrite <- Hz; apply dec_step; exact Hin | reflexivity
      | lia | rewrite alength_set; exact Hlen | rewrite alength_set; exact Hdl | | ].
    + rewrite (nt_S i n Hin'), Hseg. intros c Hc.
      destruct (Z.eq_dec (φ c) (φ v)) as [E | E].
      * apply to_Z_inj in E. subst c. rewrite aget_set_same by exact Hvb.
        fold pos. rewrite Hp1, Hpos, Hceqx. lia.
      * rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity).
        rewrite ceq_app1, Hfx.
        replace (Nat.eqb (nt v) (nt c)) with false.
        -- rewrite Hinv by exact Hc. fold p. lia.
        -- symmetry. apply Nat.eqb_neq. intro F. apply E.
           rewrite <- (nt_phi c), <- (nt_phi v), F. reflexivity.
    + rewrite (nt_S i n Hin'), Hseg. intros w t Hw Ht.
      assert (Hwb : (Z.of_nat (clt f w l + t) < wB)%Z).
      { pose proof (Hpre w). pose proof (clt_S f w l). pose proof (clt_le f (S w) l).
        rewrite wB_val. lia. }
      rewrite chunk_app1. rewrite ceq_app1 in Ht. rewrite Hfx in Ht |- *.
      destruct (Nat.eq_dec w (nt v)) as [-> | Hne].
      * rewrite Nat.eqb_refl in Ht |- *.
        destruct (Nat.lt_ge_cases t (ceq f (nt v) p)) as [Hlt | Hge].
        -- rewrite aget_set_other.
           ++ rewrite app_nth1 by (unfold ceq in Hlt; exact Hlt). apply Hdst; assumption.
           ++ intro F. apply (f_equal to_Z) in F. rewrite phi_of_nat in F by exact Hwb. lia.
        -- assert (Et : t = ceq f (nt v) p) by lia.
           assert (Eo : of_nat (clt f (nt v) l + t) = pos).
           { apply to_Z_inj. rewrite phi_of_nat by exact Hwb. lia. }
           rewrite Eo, aget_set_same by exact Hpd.
           rewrite app_nth2 by (unfold ceq in Et; lia).
           replace (t - List.length (chunk f (nt v) p))%nat with 0%nat by (unfold ceq in Et; lia).
           reflexivity.
      * replace (Nat.eqb (nt v) w) with false in Ht |- *
          by (symmetry; apply Nat.eqb_neq; intro F; apply Hne; symmetry; exact F).
        rewrite app_nil_r. rewrite Nat.add_0_r in Ht.
        rewrite aget_set_other.
        -- apply Hdst; assumption.
        -- intro F. apply (f_equal to_Z) in F. rewrite phi_of_nat in F by exact Hwb.
           pose proof (Hpre w) as Hpw. rewrite ceq_app1, Hfx in Hpw.
           replace (Nat.eqb (nt v) w) with false in Hpw
             by (symmetry; apply Nat.eqb_neq; intro G; apply Hne; symmetry; exact G).
           pose proof (clt_S f w l).
           destruct (Nat.lt_ge_cases w (nt v)) as [Hwv | Hwv].
           ++ pose proof (clt_mono f (S w) (nt v) l ltac:(lia)). lia.
           ++ pose proof (clt_mono f (S (nt v)) w l ltac:(lia)). lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hin.
    assert (Ein : nt i = nt n) by (apply nt_eq; lia).
    split; [exact Hdl|]. intros w t Hw Ht. rewrite Ein in Hdst. apply Hdst; assumption.
Qed.

Lemma seg_cs : forall (f : int -> nat) l (dst : array int) Bn,
  (Z.of_nat (List.length l) < wB)%Z ->
  (forall x, In x l -> (f x < Bn)%nat) ->
  (forall v t, (v < Bn)%nat -> (t < ceq f v l)%nat ->
     dst.[of_nat (clt f v l + t)] = nth t (chunk f v l) 0) ->
  seg dst 0 (List.length l) = cs f l 0 Bn.
Proof.
  intros f l dst Bn Hw Hk Hd.
  assert (G : forall m a, (a + m <= Bn)%nat ->
            seg dst (clt f a l) (clt f (a + m) l - clt f a l) = cs f l a m).
  { induction m as [|m IH]; intros a Ha.
    - rewrite Nat.add_0_r, Nat.sub_diag. reflexivity.
    - change (cs f l a (S m)) with (chunk f a l ++ cs f l (S a) m).
      pose proof (clt_S f a l) as HS.
      pose proof (clt_mono f (S a) (S a + m) l ltac:(lia)) as HM.
      replace (a + S m)%nat with (S a + m)%nat by lia.
      replace (clt f (S a + m) l - clt f a l)%nat
        with (ceq f a l + (clt f (S a + m) l - clt f (S a) l))%nat by lia.
      rewrite seg_app. f_equal.
      + apply nth_ext with (d := 0) (d' := 0).
        * rewrite seg_length. reflexivity.
        * intros t Ht. rewrite seg_length in Ht. rewrite seg_nth by exact Ht.
          apply Hd; [lia | exact Ht].
      + rewrite <- HS. apply IH. lia. }
  pose proof (G Bn 0%nat ltac:(lia)) as X.
  rewrite clt_0, Nat.sub_0_r, Nat.add_0_l, clt_all in X by exact Hk. exact X.
Qed.

Lemma csort_spec : forall r n k src dst,
  ((φ n) < 4194303)%Z -> PArray.length dst = n ->
  (forall x, In x (seg src 0 (nt n)) -> ((φ (skey r n k x)) < (φ (cbound n)))%Z) ->
  PArray.length (csort r n k src dst) = n /\
  seg (csort r n k src dst) 0 (nt n)
  = cs (kfn r n k) (seg src 0 (nt n)) 0 (nt (cbound n)).
Proof.
  intros r n k src dst Hn Hdl Hkey.
  destruct (cbound_spec n Hn) as (B1 & B2 & B3).
  pose proof (nt_phi n) as Nn.
  unfold csort. cbv zeta. set (B := cbound n) in *.
  assert (LB : PArray.length (PArray.make B 0) = B).
  { rewrite alength_make. replace (B <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite Uint63.leb_spec, max_length_val. lia. }
  destruct (count_loop_spec r n k src B Hn Hkey (gap n 0) 0 (PArray.make B 0)
              (Zwf_well_founded 0 (gap n 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) LB
              ltac:(intros c Hc; rewrite aget_make; reflexivity)) as [L0 C0].
  set (c0 := count_loop r n k src 0 (PArray.make B 0) (Zwf_well_founded 0 (gap n 0))) in *.
  set (l := seg src 0 (nt n)) in *.
  assert (Hll : List.length l = nt n) by apply seg_length.
  destruct (prefix_loop_spec (kfn r n k) l B B3 ltac:(lia) (gap B 0) 0 0 c0
              (Zwf_well_founded 0 (gap B 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) L0
              ltac:(change (nt 0) with 0%nat; rewrite clt_0; reflexivity)
              ltac:(intros c Hc; change (φ 0) with 0%Z in Hc; pose proof (to_Z_bounded c); lia)
              ltac:(intros c Hc; apply C0; lia)) as [L1 C1].
  set (c1 := prefix_loop B 0 0 c0 (Zwf_well_founded 0 (gap B 0))) in *.
  destruct (place_loop_spec r n k src B Hn B3 Hkey (gap n 0) 0 c1 dst
              (Zwf_well_founded 0 (gap n 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) L1 Hdl
              ltac:(intros c Hc; rewrite C1 by exact Hc;
                    change (seg src 0 (nt 0)) with (@nil int); unfold ceq, chunk; simpl filter;
                    simpl List.length; rewrite Nat.add_0_r; reflexivity)
              ltac:(intros v t Hv Ht; change (seg src 0 (nt 0)) with (@nil int) in Ht;
                    unfold ceq, chunk in Ht; simpl in Ht; lia)) as [L2 C2].
  split; [exact L2|].
  rewrite <- Hll at 1. apply seg_cs.
  - rewrite Hll, wB_val. lia.
  - intros x Hx. pose proof (Hkey x Hx). unfold kfn.
    pose proof (nt_phi (skey r n k x)). pose proof (nt_phi B). lia.
  - exact C2.
Qed.

(* ================================================================== *)
(* Prop side: rank and key invariants                                  *)
(* ================================================================== *)

(* r ranks the positions by their first k codes; rank 0 is free for the
   sentinel, and every rank has a cell in the count table *)
Definition rank_inv (L : list N) (n : int) (k : nat) (r : array int) : Prop :=
  PArray.length r = n /\
  (forall i, ((φ i) < (φ n))%Z -> (1 <= (φ (r.[i])) < (φ (cbound n)))%Z) /\
  (forall i j, ((φ i) < (φ n))%Z -> ((φ j) < (φ n))%Z ->
     Z.compare (φ (r.[i])) (φ (r.[j])) = lcmp (K L k (nt i)) (K L k (nt j))).

(* key orders the positions by their first k codes *)
Definition key_inv (L : list N) (n : int) (k : nat) (key : int -> Z) : Prop :=
  forall i j, ((φ i) < (φ n))%Z -> ((φ j) < (φ n))%Z ->
     Z.compare (key i) (key j) = lcmp (K L k (nt i)) (K L k (nt j)).

(* the rank pair of position x, as one integer (Prop side only) *)
Definition pk (r : array int) (n k x : int) : Z :=
  ((φ (r.[x])) * 8388608 + (φ (skey r n k x)))%Z.

Lemma skey_bound : forall r n k x, ((φ n) < 4194303)%Z ->
  (forall i, ((φ i) < (φ n))%Z -> (1 <= (φ (r.[i])) < (φ (cbound n)))%Z) ->
  ((φ (skey r n k x)) < (φ (cbound n)))%Z.
Proof.
  intros r n k x Hn Hr. unfold skey. destruct (x + k <? n) eqn:E.
  - rewrite ltb_spec in E. apply Hr. exact E.
  - change (φ 0) with 0%Z. pose proof (cbound_spec n Hn). lia.
Qed.

Lemma key_inv_of_rank : forall L n k r,
  List.length L = nt n -> ((φ n) < 4194303)%Z -> (1 <= (φ k) <= (φ n))%Z ->
  rank_inv L n (nt k) r ->
  key_inv L n (nt k + nt k) (pk r n k).
Proof.
  intros L n k r HL Hn Hk [Hrl [Hrb Hrc]].
  pose proof (nt_phi n) as Hnn. pose proof (nt_phi k) as Hkn.
  pose proof (cbound_spec n Hn) as (B1 & B2 & B3).
  set (v := fun i : int => skey r n k i).
  assert (Hv : forall i, ((φ i) < (φ n))%Z ->
     (0 <= (φ (v i)) < 8388608)%Z /\
     (((φ ((i + k)%uint63)) < (φ n))%Z /\ (φ (v i)) = (φ (r.[(i + k)%uint63]))
      \/ ((φ n) <= (φ ((i + k)%uint63)))%Z /\ (φ (v i)) = 0%Z) /\
     (φ ((i + k)%uint63)) = ((φ i) + (φ k))%Z).
  { intros i Hi. assert (Hik : (φ (i + k)) = ((φ i) + (φ k))%Z) by (apply phi_add; rewrite wB_val; lia).
    pose proof (skey_bound r n k i Hn Hrb). pose proof (to_Z_bounded (v i)).
    unfold v, skey in *. destruct (i + k <? n) eqn:E.
    - rewrite ltb_spec in E. split; [lia|]. split; [|exact Hik].
      left. split; [exact E | reflexivity].
    - rewrite <- Bool.not_true_iff_false, ltb_spec in E. split; [lia|].
      split; [|exact Hik]. right. split; [lia | reflexivity]. }
  assert (Hsec : forall i j, ((φ i) < (φ n))%Z -> ((φ j) < (φ n))%Z ->
     Z.compare (φ (v i)) (φ (v j))
     = lcmp (K L (nt k) (nt i + nt k)) (K L (nt k) (nt j + nt k))).
  { intros i j Hi Hj.
    destruct (Hv i Hi) as [_ [[[Ei Vi] | [Ei Vi]] Si]];
    destruct (Hv j Hj) as [_ [[[Ej Vj] | [Ej Vj]] Sj]];
    rewrite Vi, Vj.
    - rewrite Hrc by assumption. unfold nt. rewrite Si, Sj.
      pose proof (to_Z_bounded i). pose proof (to_Z_bounded j). pose proof (to_Z_bounded k).
      rewrite !Z2Nat.inj_add by lia. reflexivity.
    - rewrite (K_nil L (nt k) (nt j + nt k)) by (pose proof (nt_phi j); lia).
      pose proof (Hrb (i + k) Ei).
      destruct (K_cons L (nt k) (nt i + nt k)) as (x & l & Ex);
        [pose proof (nt_phi i); lia | lia |].
      rewrite Ex. apply Z.compare_gt_iff. lia.
    - rewrite (K_nil L (nt k) (nt i + nt k)) by (pose proof (nt_phi i); lia).
      pose proof (Hrb (j + k) Ej).
      destruct (K_cons L (nt k) (nt j + nt k)) as (x & l & Ex);
        [pose proof (nt_phi j); lia | lia |].
      rewrite Ex. apply Z.compare_lt_iff. lia.
    - rewrite (K_nil L (nt k) (nt i + nt k)) by (pose proof (nt_phi i); lia).
      rewrite (K_nil L (nt k) (nt j + nt k)) by (pose proof (nt_phi j); lia).
      reflexivity. }
  intros i j Hi Hj. unfold pk. fold (v i) (v j).
  rewrite pair_cmp by (apply Hv; assumption).
  rewrite K_double, (Hrc i j Hi Hj), (Hsec i j Hi Hj). reflexivity.
Qed.

Lemma peq_spec : forall r n k a b, ((φ n) < 4194303)%Z ->
  (forall i, ((φ i) < (φ n))%Z -> (1 <= (φ (r.[i])) < (φ (cbound n)))%Z) ->
  (if r.[a] =? r.[b] then skey r n k a =? skey r n k b else false)
  = Z.eqb (pk r n k a) (pk r n k b).
Proof.
  intros r n k a b Hn Hr.
  pose proof (cbound_spec n Hn) as (B1 & B2 & B3).
  pose proof (skey_bound r n k a Hn Hr). pose proof (skey_bound r n k b Hn Hr).
  pose proof (to_Z_bounded (skey r n k a)). pose proof (to_Z_bounded (skey r n k b)).
  pose proof (to_Z_bounded (r.[a])). pose proof (to_Z_bounded (r.[b])).
  unfold pk. rewrite !eqb_Z.
  destruct (Z.eqb_spec (φ (r.[a])) (φ (r.[b]))) as [E1|E1].
  - destruct (Z.eqb_spec (φ (skey r n k a)) (φ (skey r n k b))) as [E2|E2]; symmetry.
    + apply Z.eqb_eq. lia.
    + apply Z.eqb_neq. lia.
  - symmetry. apply Z.eqb_neq. lia.
Qed.

Lemma rank_loop_spec : forall r n k sa,
  ((φ n) < 4194303)%Z ->
  (forall i, ((φ i) < (φ n))%Z -> (1 <= (φ (r.[i])) < (φ (cbound n)))%Z) ->
  (forall t1 t2, (t1 < nt n)%nat -> (t2 < nt n)%nat ->
     sa.[of_nat t1] = sa.[of_nat t2] -> t1 = t2) ->
  (forall t, (t < nt n)%nat -> ((φ (sa.[of_nat t])) < (φ n))%Z) ->
  forall (z : Z) t cur nr H,
  gap n t = z -> (1 <= (φ t) <= (φ n))%Z -> PArray.length nr = n ->
  (φ cur) = Rk (fun t => pk r n k (sa.[of_nat t])) (nt t - 1) ->
  (forall t', (t' < nt t)%nat ->
     (φ (nr.[sa.[of_nat t']])) = Rk (fun t => pk r n k (sa.[of_nat t])) t') ->
  PArray.length (fst (rank_loop r n k sa t cur nr H)) = n /\
  (forall t', (t' < nt n)%nat ->
     (φ ((fst (rank_loop r n k sa t cur nr H)).[sa.[of_nat t']]))
     = Rk (fun t => pk r n k (sa.[of_nat t])) t') /\
  (φ (snd (rank_loop r n k sa t cur nr H))) = Rk (fun t => pk r n k (sa.[of_nat t])) (nt n - 1).
Proof.
  intros r n k sa Hn Hr Hinj Hval z.
  set (g := fun t => pk r n k (sa.[of_nat t])).
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros t cur nr H Hz Ht Hlen Hcur Hinv.
  pose proof (nt_phi t). pose proof (nt_phi n).
  rewrite rank_loop_eq.
  destruct (bdec (t <? n)) as [Htn | Htn].
  - cbv zeta. pose proof Htn as Htn'. rewrite ltb_spec in Htn'.
    pose proof (phi_succ t n Htn') as Ht1.
    assert (Htm : (φ (t - 1)) = ((φ t) - 1)%Z) by (rewrite sub_spec; change (φ 1) with 1%Z; apply Z.mod_small; pose proof (to_Z_bounded t); lia).
    assert (Eo : of_nat (nt t - 1) = t - 1).
    { rewrite <- (of_nt (t - 1)). f_equal. unfold nt. rewrite Htm. lia. }
    assert (Ent : nt t = S (nt t - 1)) by lia.
    rewrite (peq_spec r n k _ _ Hn Hr).
    set (nr1 := if Z.eqb (pk r n k sa.[t - 1]) (pk r n k sa.[t]) then cur else cur + 1).
    assert (Hnr : (φ nr1) = Rk g (nt t)).
    { rewrite Ent. cbn [Rk]. rewrite <- Ent. unfold g at 2 3.
      rewrite Eo, of_nt. unfold nr1.
      pose proof (Rk_bounds g (nt t - 1)).
      destruct (Z.eqb (pk r n k sa.[t - 1]) (pk r n k sa.[t])).
      - rewrite Hcur. lia.
      - rewrite phi_add; change (φ 1) with 1%Z; rewrite Hcur; [lia|].
        rewrite wB_val. lia. }
    assert (Hst : (sa.[t] <? PArray.length nr) = true).
    { rewrite ltb_spec, Hlen. rewrite <- (of_nt t). apply Hval. lia. }
    apply (IH (gap n (t + 1))); [ rewrite <- Hz; apply dec_step; exact Htn | reflexivity
      | lia | rewrite alength_set; exact Hlen | | ].
    + replace (nt (t + 1) - 1)%nat with (nt t) by (rewrite (nt_S t n Htn'); lia).
      exact Hnr.
    + intros t' Ht'. rewrite (nt_S t n Htn') in Ht'.
      destruct (Nat.eq_dec t' (nt t)) as [E | E].
      * subst t'. rewrite of_nt, aget_set_same by exact Hst. exact Hnr.
      * rewrite aget_set_other; [apply Hinv; lia|].
        intro F. apply E. apply Hinj; [lia | lia |]. rewrite of_nt. symmetry. exact F.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Htn.
    cbn [fst snd]. split; [exact Hlen|]. split.
    + intros t' Ht'. apply Hinv. lia.
    + rewrite Hcur. f_equal. lia.
Qed.

Lemma new_rank_inv : forall L n k key sa r,
  ((φ n) < 4194303)%Z ->
  key_inv L n k key ->
  Permutation (map nt (seg sa 0 (nt n))) (seq 0 (nt n)) ->
  Sorted (le_f key) (seg sa 0 (nt n)) ->
  PArray.length r = n ->
  (forall t', (t' < nt n)%nat ->
     (φ (r.[sa.[of_nat t']])) = Rk (fun t => key (sa.[of_nat t])) t') ->
  rank_inv L n k r.
Proof.
  intros L n k key sa r Hn Hkey HP HS Hrl Hr.
  pose proof (nt_phi n) as Hnn.
  pose proof (cbound_spec n Hn) as (B1 & B2 & B3).
  destruct (perm_facts sa (nt n) ltac:(rewrite wB_val; lia) HP) as (Fv & Finj & Fsurj).
  set (g := fun t => key (sa.[of_nat t])) in *.
  assert (Hadj : forall t, (S t < nt n)%nat -> (g t <= g (S t))%Z).
  { intros t Ht. pose proof (sorted_nth _ _ HS t 0 ltac:(rewrite seg_length; exact Ht)) as X.
    unfold le_f in X. rewrite !seg_nth in X by lia. exact X. }
  assert (Hpos : forall i, ((φ i) < (φ n))%Z -> exists t, (t < nt n)%nat /\ sa.[of_nat t] = i).
  { intros i Hi. destruct (Fsurj (nt i)) as (t & Ht & Et); [pose proof (nt_phi i); lia|].
    exists t. split; [exact Ht | apply nt_inj; exact Et]. }
  split; [exact Hrl|]. split.
  - intros i Hi. destruct (Hpos i Hi) as (t & Ht & <-). rewrite Hr by exact Ht.
    pose proof (Rk_bounds g t). lia.
  - assert (Hle : forall p q, (p <= q)%nat -> (q < nt n)%nat ->
       Z.compare (φ (r.[sa.[of_nat p]])) (φ (r.[sa.[of_nat q]]))
       = Z.compare (key (sa.[of_nat p])) (key (sa.[of_nat q]))).
    { intros p q Hpq Hq. rewrite !Hr by lia.
      replace q with (p + (q - p))%nat by lia.
      apply (Rk_cmp g (nt n) Hadj). lia. }
    intros i j Hi Hj.
    destruct (Hpos i Hi) as (p & Hp & Ep). destruct (Hpos j Hj) as (q & Hq & Eq).
    assert (Vi : ((φ (sa.[of_nat p])) < (φ n))%Z) by (pose proof (Fv p Hp); pose proof (nt_phi (sa.[of_nat p])); lia).
    assert (Vj : ((φ (sa.[of_nat q])) < (φ n))%Z) by (pose proof (Fv q Hq); pose proof (nt_phi (sa.[of_nat q])); lia).
    destruct (Nat.le_gt_cases p q) as [Hpq | Hpq].
    + rewrite <- Ep, <- Eq, Hle by lia. apply Hkey; assumption.
    + rewrite <- Ep, <- Eq. rewrite Z.compare_antisym, Hle by lia.
      rewrite Hkey by assumption. rewrite lcmp_antisym. apply CompOpp_involutive.
Qed.

(* ================================================================== *)
(* Prop side: one round's two counting passes sort on the rank pair    *)
(* ================================================================== *)

Lemma skey0 : forall r n x, ((φ x) < (φ n))%Z -> skey r n 0 x = r.[x].
Proof.
  intros r n x Hx. unfold skey.
  assert (E : x + 0 = x).
  { apply to_Z_inj. rewrite add_spec. change (φ 0) with 0%Z. rewrite Z.add_0_r.
    apply Z.mod_small. apply to_Z_bounded. }
  rewrite E. replace (x <? n) with true by (symmetry; rewrite ltb_spec; exact Hx). reflexivity.
Qed.

Lemma perm_in : forall (l : list int) n, Permutation (map nt l) (seq 0 (nt n)) ->
  forall x, In x l -> ((φ x) < (φ n))%Z.
Proof.
  intros l n HP x Hx. apply (in_map nt) in Hx. eapply Permutation_in in Hx; [|exact HP].
  apply in_seq in Hx. pose proof (nt_phi x). pose proof (nt_phi n). lia.
Qed.

Lemma round_sort : forall r n k sa tmp,
  (1 <= (φ n) < 4194303)%Z ->
  (forall i, ((φ i) < (φ n))%Z -> (1 <= (φ (r.[i])) < (φ (cbound n)))%Z) ->
  PArray.length sa = n -> PArray.length tmp = n ->
  Permutation (map nt (seg sa 0 (nt n))) (seq 0 (nt n)) ->
  PArray.length (csort r n k sa tmp) = n /\
  PArray.length (csort r n 0 (csort r n k sa tmp) sa) = n /\
  Permutation (map nt (seg (csort r n 0 (csort r n k sa tmp) sa) 0 (nt n))) (seq 0 (nt n)) /\
  Sorted (le_f (pk r n k)) (seg (csort r n 0 (csort r n k sa tmp) sa) 0 (nt n)).
Proof.
  intros r n k sa tmp Hn Hr Hsl Htl HP.
  assert (Hn' : ((φ n) < 4194303)%Z) by lia.
  pose proof (nt_phi n) as Nn. pose proof (cbound_spec n Hn') as (B1 & B2 & B3).
  pose proof (nt_phi (cbound n)) as NB.
  assert (Hkb : forall k' x, (kfn r n k' x < nt (cbound n))%nat).
  { intros k' x. unfold kfn. pose proof (skey_bound r n k' x Hn' Hr).
    pose proof (nt_phi (skey r n k' x)). lia. }
  destruct (csort_spec r n k sa tmp Hn' Htl (fun x _ => skey_bound r n k x Hn' Hr)) as [Lt St].
  set (tmp1 := csort r n k sa tmp) in *.
  destruct (csort_spec r n 0 tmp1 sa Hn' Hsl (fun x _ => skey_bound r n 0 x Hn' Hr)) as [Ls Ss].
  set (sa1 := csort r n 0 tmp1 sa) in *.
  set (l0 := seg sa 0 (nt n)) in *. set (l2 := seg tmp1 0 (nt n)) in *.
  assert (P2 : Permutation l2 l0) by (rewrite St; apply cs_perm; intros x _; apply Hkb).
  assert (P1 : Permutation (seg sa1 0 (nt n)) l2) by (rewrite Ss; apply cs_perm; intros x _; apply Hkb).
  assert (HP1 : Permutation (map nt (seg sa1 0 (nt n))) (seq 0 (nt n))).
  { eapply perm_trans; [apply Permutation_map; eapply perm_trans; [exact P1 | exact P2] | exact HP]. }
  assert (In2 : forall x, In x l2 -> ((φ x) < (φ n))%Z).
  { intros x Hx. apply (perm_in l0 n HP). eapply Permutation_in; [exact P2 | exact Hx]. }
  (* the values of the two keys *)
  assert (Kv : forall x, In x l2 ->
     Z.of_nat (kfn r n 0 x) = (φ (r.[x])) /\
     Z.of_nat (kfn r n k x) = (φ (skey r n k x)) /\
     (0 <= (φ (skey r n k x)) < 8388608)%Z).
  { intros x Hx. pose proof (In2 x Hx) as Hxn. unfold kfn. rewrite !nt_phi, skey0 by exact Hxn.
    pose proof (skey_bound r n k x Hn' Hr). pose proof (to_Z_bounded (skey r n k x)).
    split; [reflexivity | split; [reflexivity | lia]]. }
  assert (SS2 : StronglySorted (fun x y => kfn r n k x <= kfn r n k y)%nat l2).
  { rewrite St. apply cs_ss.
    - intros v. apply SS_all. intros x y Hx Hy. unfold chunk in Hx, Hy.
      apply filter_In in Hx as [_ Ex]. apply filter_In in Hy as [_ Ey].
      apply Nat.eqb_eq in Ex, Ey. lia.
    - intros x y _ _ Hxy. lia. }
  split; [exact Lt|]. split; [exact Ls|]. split; [exact HP1|].
  rewrite Ss. apply StronglySorted_Sorted. apply cs_ss.
  - intros v. eapply SS_impl; [|apply SS_filter; exact SS2].
    intros x y Hx Hy Hxy. unfold chunk in Hx, Hy.
    apply filter_In in Hx as [Hx Ex]. apply filter_In in Hy as [Hy Ey].
    apply Nat.eqb_eq in Ex, Ey. cbv beta in Hxy.
    destruct (Kv x Hx) as (X1 & X2 & X3). destruct (Kv y Hy) as (Y1 & Y2 & Y3).
    unfold le_f, pk. lia.
  - intros x y Hx Hy Hxy.
    destruct (Kv x Hx) as (X1 & X2 & X3). destruct (Kv y Hy) as (Y1 & Y2 & Y3).
    unfold le_f, pk. lia.
Qed.

(* ================================================================== *)
(* Prop side: the doubling rounds                                      *)
(* ================================================================== *)

Lemma rounds_spec : forall L n, List.length L = nt n -> (1 <= (φ n) < 4194303)%Z ->
  forall (z : Z) k r nr sa tmp H,
  gap n k = z -> (1 <= (φ k) <= (φ n))%Z ->
  rank_inv L n (nt k) r ->
  PArray.length nr = n -> PArray.length sa = n -> PArray.length tmp = n ->
  Permutation (map nt (seg sa 0 (nt n))) (seq 0 (nt n)) ->
  PArray.length (rounds n k r nr sa tmp H) = n /\
  Permutation (map nt (seg (rounds n k r nr sa tmp H) 0 (nt n))) (seq 0 (nt n)) /\
  (forall t, (S t < nt n)%nat ->
     lcmp (skipn (nt ((rounds n k r nr sa tmp H).[of_nat t])) L)
          (skipn (nt ((rounds n k r nr sa tmp H).[of_nat (S t)])) L) = Lt).
Proof.
  intros L n HL Hn z.
  pose proof (nt_phi n) as Hnn.
  assert (Hn' : ((φ n) < 4194303)%Z) by lia.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k r nr sa tmp H Hz Hk Hr Hnl Hsl Htl HP.
  rewrite rounds_eq. cbv zeta.
  pose proof (key_inv_of_rank L n k r HL Hn' Hk Hr) as Hkey.
  destruct Hr as [Hrl [Hrb Hrc]].
  destruct (round_sort r n k sa tmp Hn Hrb Hsl Htl HP) as (Ltm & Ls & HP1 & Ss).
  set (tmp1 := csort r n k sa tmp) in *.
  set (sa1 := csort r n 0 tmp1 sa) in *.
  destruct (perm_facts sa1 (nt n) ltac:(rewrite wB_val; lia) HP1) as (Fv & Finj & Fsurj).
  assert (Fv' : forall t, (t < nt n)%nat -> ((φ (sa1.[of_nat t])) < (φ n))%Z).
  { intros t Ht. pose proof (Fv t Ht). pose proof (nt_phi (sa1.[of_nat t])). lia. }
  set (g := fun t => pk r n k (sa1.[of_nat t])).
  assert (Hadj : forall t, (S t < nt n)%nat -> (g t <= g (S t))%Z).
  { intros t Ht. pose proof (sorted_nth _ _ Ss t 0 ltac:(rewrite seg_length; exact Ht)) as X.
    unfold le_f in X. rewrite !seg_nth in X by lia. exact X. }
  assert (Hs0 : (sa1.[0] <? PArray.length nr) = true).
  { rewrite ltb_spec, Hnl. apply (Fv' 0%nat). lia. }
  pose proof (rank_loop_spec r n k sa1 Hn' Hrb Finj Fv' (gap n 1) 1 1 nr.[sa1.[0] <- 1]
                (Zwf_well_founded 0 (gap n 1)) eq_refl
                ltac:(change (φ 1) with 1%Z; lia) ltac:(rewrite alength_set; exact Hnl)
                ltac:(reflexivity)
                ltac:(intros t' Ht'; change (nt 1) with 1%nat in Ht';
                      replace t' with 0%nat by lia; change (of_nat 0) with 0;
                      rewrite aget_set_same by exact Hs0; reflexivity)) as Xr.
  destruct (rank_loop r n k sa1 1 1 nr.[sa1.[0] <- 1] (Zwf_well_founded 0 (gap n 1)))
    as [r1 last] eqn:Er.
  cbn [fst snd] in Xr |- *. destruct Xr as (Lr & Cr & Llast).
  fold g in Cr, Llast.
  assert (Hkt : forall t, (S t < nt n)%nat ->
            Z.compare (g t) (g (S t))
            = lcmp (K L (nt k + nt k) (nt (sa1.[of_nat t])))
                   (K L (nt k + nt k) (nt (sa1.[of_nat (S t)])))).
  { intros t Ht. apply Hkey; apply Fv'; lia. }
  assert (Hdone : (forall t, (S t < nt n)%nat -> (g t < g (S t))%Z) ->
     forall t, (S t < nt n)%nat ->
     lcmp (skipn (nt (sa1.[of_nat t])) L) (skipn (nt (sa1.[of_nat (S t)])) L) = Lt).
  { intros Hlt t Ht. apply (lcmp_firstn_lt (nt k + nt k)).
    pose proof (Hkt t Ht) as X. unfold K in X. rewrite <- X. apply Z.compare_lt_iff. apply Hlt. exact Ht. }
  destruct (last =? n) eqn:El.
  - apply Uint63.eqb_spec in El. subst last.
    split; [exact Ls|]. split; [exact HP1|].
    apply Hdone. intros t Ht.
    pose proof (Rk_all_distinct g (nt n) ltac:(lia) ltac:(rewrite <- Llast; lia) t Ht).
    pose proof (Hadj t Ht). lia.
  - destruct (bdec (andb (k <? k + k) (k + k <? n))) as [Hc | Hc].
    + pose proof Hc as Hc'. apply andb_prop in Hc' as [C1 C2].
      rewrite ltb_spec in C1, C2.
      assert (Hkk : (φ (k + k)) = ((φ k) + (φ k))%Z) by (apply phi_add; rewrite wB_val; lia).
      apply (IH (gap n (k + k))); [ rewrite <- Hz; apply dec_dbl; exact Hc | reflexivity
        | lia | | exact Hrl | exact Ls | exact Ltm | exact HP1 ].
      replace (nt (k + k)) with (nt k + nt k)%nat
        by (unfold nt; rewrite Hkk; pose proof (to_Z_bounded k); lia).
      apply (new_rank_inv L n (nt k + nt k) (pk r n k) sa1 r1); try assumption.
    + split; [exact Ls|]. split; [exact HP1|].
      assert (H2k : ((φ n) <= (φ k) + (φ k))%Z).
      { destruct (Z.le_gt_cases (φ n) ((φ k) + (φ k))) as [E|E]; [exact E|].
        exfalso. assert (Hkk : (φ (k + k)) = ((φ k) + (φ k))%Z) by (apply phi_add; rewrite wB_val; lia).
        assert (C1 : (k <? k + k) = true) by (rewrite ltb_spec; lia).
        assert (C2 : (k + k <? n) = true) by (rewrite ltb_spec; lia).
        rewrite C1, C2 in Hc. discriminate. }
      pose proof (nt_phi k).
      intros t Ht.
      assert (Ef : forall i, (i < nt n)%nat -> K L (nt k + nt k) i = skipn i L).
      { intros i Hi. unfold K. apply firstn_all2. rewrite length_skipn. lia. }
      pose proof (Fv t ltac:(lia)) as V1. pose proof (Fv (S t) Ht) as V2.
      pose proof (Hkt t Ht) as X. rewrite !Ef in X by assumption.
      rewrite <- X. pose proof (Hadj t Ht) as Y.
      destruct (Z.compare_spec (g t) (g (S t))) as [E|E|E]; [|reflexivity|lia].
      exfalso. symmetry in X. apply lcmp_eq in X.
      apply (f_equal (@List.length N)) in X. rewrite !length_skipn in X.
      assert (nt (sa1.[of_nat t]) = nt (sa1.[of_nat (S t)])) by lia.
      assert (t = S t) by (apply Finj; [lia | lia | apply nt_inj; assumption]). lia.
Qed.

(* ================================================================== *)
(* The contract                                                        *)
(* ================================================================== *)

Lemma suffix_array_impl_correct : forall (s : string) (x : PrimString.string),
  valid_input s -> repr x s ->
  exists sa : list N, repr (suffix_array_impl x) sa /\ suffix_array_spec s sa.
Proof.
  intros s x [Hv] [Hxl Hxc].
  unfold slen in Hv.
  unfold suffix_array_impl. cbv zeta.
  set (n := PrimString.length x) in *.
  set (L := codes s).
  assert (HnZ : (φ n) = Z.of_nat (String.length s)) by (symmetry; exact Hxl).
  assert (Hnt : nt n = String.length s) by (unfold nt; rewrite HnZ; apply Nat2Z.id).
  assert (HL : List.length L = nt n) by (unfold L; rewrite codes_length; symmetry; exact Hnt).
  assert (Hn : (1 <= (φ n) <= 100000)%Z) by lia.
  assert (Hcode : forall t : int, ((φ t) < (φ n))%Z ->
            nth_error L (nt t) = Some (Z.to_N (φ (PrimString.get x t))) /\
            ((φ (PrimString.get x t)) < 256)%Z).
  { intros t Ht. pose proof (nt_phi t).
    destruct (Hxc (nt t) ltac:(lia)) as (c & Hc & Hr).
    unfold repr, repr_uint in Hr. rewrite of_nt in Hr.
    pose proof (N_ascii_bounded c). pose proof (to_Z_bounded (PrimString.get x t)).
    split; [|lia]. unfold L. rewrite (codes_get s (nt t) c Hc), <- Hr. reflexivity. }
  assert (Lmk : PArray.length (PArray.make n 0) = n).
  { rewrite alength_make. replace (n <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite Uint63.leb_spec, max_length_val. lia. }
  destruct (init_rank_spec x n (gap n 0) 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0))
              eq_refl Lmk ltac:(change (φ 0) with 0%Z; lia)
              ltac:(intros t Ht; change (φ 0) with 0%Z in Ht; pose proof (to_Z_bounded t); lia))
    as [Lr0 Cr0].
  set (r0 := init_rank x n 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0))) in *.
  destruct (init_id_spec n (gap n 0) 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0))
              eq_refl Lmk ltac:(change (φ 0) with 0%Z; lia)
              ltac:(intros t Ht; change (φ 0) with 0%Z in Ht; pose proof (to_Z_bounded t); lia))
    as [Ls0 Cs0].
  set (sa0 := init_id n 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0))) in *.
  assert (Hval0 : forall i, ((φ i) < (φ n))%Z ->
            (φ (r0.[i])) = ((φ (PrimString.get x i)) + 1)%Z).
  { intros i Hi. rewrite Cr0 by exact Hi. destruct (Hcode i Hi) as [_ B]. sia. }
  assert (Hrank : rank_inv L n (nt 1) r0).
  { change (nt 1) with 1%nat. split; [exact Lr0|]. split.
    - intros i Hi. rewrite Hval0 by exact Hi. destruct (Hcode i Hi) as [_ B].
      pose proof (to_Z_bounded (PrimString.get x i)).
      pose proof (cbound_spec n ltac:(lia)). lia.
    - intros i j Hi Hj. rewrite (Hval0 i Hi), (Hval0 j Hj).
      rewrite (Z.add_comm _ 1), (Z.add_comm _ 1), Z.add_compare_mono_l.
      destruct (Hcode i Hi) as [Ci _]. destruct (Hcode j Hj) as [Cj _].
      unfold K. rewrite (skipn_nth_error L (nt i) _ Ci), (skipn_nth_error L (nt j) _ Cj).
      cbn [firstn lcmp].
      pose proof (to_Z_bounded (PrimString.get x i)).
      pose proof (to_Z_bounded (PrimString.get x j)).
      rewrite <- N2Z.inj_compare, !Z2N.id by lia.
      destruct (Z.compare _ _); reflexivity. }
  assert (Hperm : Permutation (map nt (seg sa0 0 (nt n))) (seq 0 (nt n))).
  { replace (map nt (seg sa0 0 (nt n))) with (seq 0 (nt n)); [reflexivity|].
    unfold seg. rewrite map_map. rewrite <- (map_id (seq 0 (nt n))) at 1.
    apply map_ext_in. intros t Ht. apply in_seq in Ht. pose proof (nt_phi n).
    rewrite Cs0 by (rewrite phi_of_nat by (rewrite wB_val; lia); lia).
    symmetry. apply nt_of_nat. rewrite wB_val. lia. }
  destruct (rounds_spec L n HL ltac:(lia) (gap n 1) 1 r0 (PArray.make n 0) sa0
              (PArray.make n 0) (Zwf_well_founded 0 (gap n 1)) eq_refl
              ltac:(change (φ 1) with 1%Z; lia) Hrank Lmk Ls0 Lmk Hperm)
    as (Lres & Pres & Sres).
  set (res := rounds n 1 r0 (PArray.make n 0) sa0 (PArray.make n 0)
                (Zwf_well_founded 0 (gap n 1))) in *.
  set (W := map (fun t => Z.to_N (φ (res.[of_nat t]))) (seq 0 (nt n))).
  assert (Hnth : forall t, (t < nt n)%nat -> nth t W 0%N = Z.to_N (φ (res.[of_nat t]))).
  { intros t Ht. apply nth_error_nth. unfold W. rewrite nth_error_map, nth_error_seq.
    destruct (Nat.ltb_spec t (nt n)); [reflexivity | lia]. }
  exists W. split.
  - split.
    + unfold W. rewrite length_map, length_seq, nt_phi. symmetry. exact (f_equal to_Z Lres).
    + intros k0 Hk0. unfold W in Hk0. rewrite length_map, length_seq in Hk0.
      exists (Z.to_N (φ (res.[of_nat k0]))). split.
      * unfold W. rewrite nth_error_map, nth_error_seq.
        destruct (Nat.ltb_spec k0 (nt n)); [reflexivity | lia].
      * reflexivity.
  - split.
    + unfold positions. rewrite <- Hnt.
      assert (E : W = map N.of_nat (map nt (seg res 0 (nt n)))).
      { unfold W, seg. rewrite !map_map. apply map_ext. intros t. unfold nt.
        rewrite Z_nat_N. reflexivity. }
      rewrite E. apply Permutation_map. exact Pres.
    + intros r Hr. unfold len in Hr. unfold W in Hr. rewrite length_map, length_seq in Hr.
      unfold lex_lt, suffix, get_list_N.
      rewrite !Hnth by lia.
      rewrite compare_codes, !codes_substring by lia.
      rewrite !Z_N_nat.
      replace (N.to_nat (r + 1)) with (S (N.to_nat r)) by lia.
      exact (Sres (N.to_nat r) ltac:(lia)).
Qed.

Definition suffix_array_correct : forall (s : string) (x : PrimString.string),
  valid_input s -> repr x s ->
  exists sa : list N, repr (suffix_array x) sa /\ suffix_array_spec s sa
  := suffix_array_impl_correct.
