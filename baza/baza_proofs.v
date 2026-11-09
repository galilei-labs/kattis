(* Correctness proofs for baza_implem.v. *)
(* Implementation of baza (baza.spec): a trie of the database words with
   a counter per node, built once in database order; every query answered
   offline against it.  See README.md, "Implementation". *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require String Ascii PrimString.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Require Export baza_implem.
Open Scope uint63_scope.
Open Scope array_scope.


Lemma ins_loop_eq : forall w L T cnt sz i n s H,
  ins_loop w L T cnt sz i n s H =
  match bdec (i <? L) with
  | left Hi =>
      let c := PrimString.get w i - 97 in
      let m := tget T c n in
      if m =? 0 then
        ins_loop w L (tset T c n sz) cnt.[sz <- 1] (sz + 1) (i + 1) sz (s + 1)
          (Acc_inv H (dec_step L i Hi))
      else
        let k := cnt.[m] + 1 in
        ins_loop w L T cnt.[m <- k] sz (i + 1) m (s + k)
          (Acc_inv H (dec_step L i Hi))
  | right _ => mkI T cnt sz n s
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma build_eq : forall db N T cnt endv sz j H,
  build db N T cnt endv sz j H =
  match bdec (j <? N) with
  | left Hj =>
      let w := db.[j] in
      let r := ins_loop w (PrimString.length w) T cnt sz 0 0 0
                 (Zwf_well_founded 0 (gap (PrimString.length w) 0)) in
      build db N (r_T r) (r_cnt r) endv.[r_n r <- j + 1 + r_s r] (r_sz r) (j + 1)
        (Acc_inv H (dec_step N j Hj))
  | right _ => mkB T cnt endv
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma qwalk_eq : forall q L T cnt endv N i n s H,
  qwalk q L T cnt endv N i n s H =
  match bdec (i <? L) with
  | left Hi =>
      let m := tget T (PrimString.get q i - 97) n in
      if m =? 0 then N + s
      else qwalk q L T cnt endv N (i + 1) m (s + cnt.[m])
             (Acc_inv H (dec_step L i Hi))
  | right _ => let e := endv.[n] in if e =? 0 then N + s else e
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma answer_eq : forall qs Q T cnt endv N out k H,
  answer qs Q T cnt endv N out k H =
  match bdec (k <? Q) with
  | left Hk =>
      answer qs Q T cnt endv N out.[k <- query qs.[k] T cnt endv N] (k + 1)
        (Acc_inv H (dec_step Q k Hk))
  | right _ => out
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma total_eq : forall db N j acc H,
  total db N j acc H =
  match bdec (j <? N) with
  | left Hj => total db N (j + 1) (acc + PrimString.length db.[j])
                 (Acc_inv H (dec_step N j Hj))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.


(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma ltb_reflect : forall x y : int, Bool.reflect ((φ x) < (φ y))%Z (x <? y).
Proof. intros. apply Bool.iff_reflect. symmetry. apply ltb_spec. Qed.

Ltac split_c c :=
  repeat match goal with |- context [c <? ?k] => destruct (ltb_reflect c k) end.

Lemma sel_upd_same : forall t c a, ((φ c) < 26)%Z -> sel (upd t c a) c = a.
Proof. intros t c a Hc. destruct t. unfold sel, upd. split_c c; reflexivity. Qed.

Lemma sel_upd_other : forall t c c' a, ((φ c) < 26)%Z -> ((φ c') < 26)%Z -> c <> c' ->
  sel (upd t c a) c' = sel t c'.
Proof.
  intros t c c' a Hc Hc' Hne. pose proof (to_Z_bounded c). pose proof (to_Z_bounded c').
  destruct t. unfold upd. split_c c; unfold sel; split_c c';
    first [reflexivity | exfalso; apply Hne; apply to_Z_inj; lia].
Qed.

Lemma sel_mk_tab : forall cap c, sel (mk_tab cap) c = PArray.make cap 0.
Proof. intros cap c. unfold sel, mk_tab. split_c c; reflexivity. Qed.

Lemma tget_tset_same : forall t c n v, ((φ c) < 26)%Z ->
  ((φ n) < (φ (PArray.length (sel t c))))%Z -> tget (tset t c n v) c n = v.
Proof.
  intros t c n v Hc Hn. unfold tget, tset. rewrite sel_upd_same by exact Hc.
  exact (get_set_same int (sel t c) n v ltac:(rewrite ltb_spec; exact Hn)).
Qed.

Lemma tget_tset_other : forall t c c' n n' v, ((φ c) < 26)%Z -> ((φ c') < 26)%Z ->
  (c <> c' \/ n <> n') -> tget (tset t c n v) c' n' = tget t c' n'.
Proof.
  intros t c c' n n' v Hc Hc' Hne. unfold tget, tset.
  destruct (c =? c') eqn:E.
  - apply eqb_spec in E. subst c'. rewrite sel_upd_same by exact Hc.
    exact (get_set_other int (sel t c) n n' v
             ltac:(destruct Hne as [Hne | Hne]; [congruence | exact Hne])).
  - apply eqb_false_spec in E. rewrite sel_upd_other by assumption. reflexivity.
Qed.

Lemma len_tset : forall t c c' n v, ((φ c) < 26)%Z -> ((φ c') < 26)%Z ->
  PArray.length (sel (tset t c n v) c') = PArray.length (sel t c').
Proof.
  intros t c c' n v Hc Hc'. unfold tset.
  destruct (c =? c') eqn:E.
  - apply eqb_spec in E. subst c'. rewrite sel_upd_same by exact Hc.
    exact (length_set int (sel t c) n v).
  - apply eqb_false_spec in E. rewrite sel_upd_other by assumption. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Math side: a word is the list of its letter indices (code - 97)     *)
(* ------------------------------------------------------------------ *)

Open Scope list_scope.

(* p is a prefix of u *)
Fixpoint preb (p u : list Z) : bool :=
  match p, u with
  | [], _ => true
  | x :: p', y :: u' => Z.eqb x y && preb p' u'
  | _ :: _, [] => false
  end.

(* how many words of W start with p *)
Definition cntW (W : list (list Z)) (p : list Z) : nat :=
  list_sum (map (fun v => if preb p v then 1%nat else 0%nat) W).

(* p is the root or the prefix of a word of W: the strings with a node *)
Definition SW (W : list (list Z)) (p : list Z) : Prop :=
  p = [] \/ exists v, In v W /\ preb p v = true.

Definition sumlen (W : list (list Z)) : nat := list_sum (map (@List.length Z) W).

Fixpoint sumn (f : nat -> nat) (n : nat) : nat :=
  match n with O => O | S n' => (sumn f n' + f n')%nat end.

(* the sum of the counters met on the path of q *)
Definition pathsum (W : list (list Z)) (q : list Z) : nat :=
  sumn (fun l => cntW W (firstn (S l) q)) (List.length q).

Fixpoint index_of (p : list Z) (W : list (list Z)) : option nat :=
  match W with
  | [] => None
  | v :: W' => if list_eq_dec Z.eq_dec p v then Some O
               else option_map S (index_of p W')
  end.

(* the value stored at the end node of p *)
Definition EW (W : list (list Z)) (p : list Z) : Z :=
  match index_of p W with
  | Some k => Z.of_nat (S k + pathsum (firstn (S k) W) p)
  | None => 0%Z
  end.

(* the answer to query q *)
Definition ansm (W : list (list Z)) (q : list Z) : nat :=
  match index_of q W with
  | Some k => (S k + pathsum (firstn (S k) W) q)%nat
  | None => (List.length W + pathsum W q)%nat
  end.

Lemma preb_spec : forall p u, preb p u = true <-> exists r, u = p ++ r.
Proof.
  induction p as [|x p IH]; intros [|y u]; simpl.
  - split; [intros _; exists []; reflexivity | reflexivity].
  - split; [intros _; exists (y :: u); reflexivity | reflexivity].
  - split; [discriminate | intros [r Hr]; discriminate].
  - split.
    + intros H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst y.
      apply IH in H2 as [r ->]. exists r. reflexivity.
    + intros [r Hr]. injection Hr as -> ->. rewrite Z.eqb_refl. simpl.
      apply IH. exists r. reflexivity.
Qed.

Lemma preb_app : forall p r, preb p (p ++ r) = true.
Proof. intros p r. apply preb_spec. exists r. reflexivity. Qed.

Lemma preb_refl : forall p, preb p p = true.
Proof. intros p. rewrite <- (app_nil_r p) at 2. apply preb_app. Qed.

Lemma preb_trans : forall p q u, preb p q = true -> preb q u = true -> preb p u = true.
Proof.
  intros p q u H1 H2. apply preb_spec in H1 as [r1 ->]. apply preb_spec in H2 as [r2 ->].
  rewrite <- app_assoc. apply preb_app.
Qed.

Lemma preb_len : forall p u, preb p u = true -> (List.length p <= List.length u)%nat.
Proof. intros p u H. apply preb_spec in H as [r ->]. rewrite length_app. lia. Qed.

Lemma preb_nil_r : forall p, preb p [] = true -> p = [].
Proof. intros [|x p] H; [reflexivity | discriminate]. Qed.

Lemma preb_snoc : forall p q x,
  preb p (q ++ [x]) = true <-> p = q ++ [x] \/ preb p q = true.
Proof.
  intros p q x. split.
  - intros H. apply preb_spec in H as [r Hr].
    destruct r as [|a l' _] using rev_ind.
    + left. rewrite app_nil_r in Hr. symmetry. exact Hr.
    + rewrite app_assoc in Hr.
      apply app_inj_tail in Hr as [Hq _]. right. apply preb_spec. exists l'. exact Hq.
  - intros [-> | H]; [apply preb_refl | eapply preb_trans; [exact H | apply preb_app]].
Qed.

Lemma preb_firstn : forall l u, preb (firstn l u) u = true.
Proof. intros l u. rewrite <- (firstn_skipn l u) at 2. apply preb_app. Qed.

Lemma SW_closed : forall W p q, preb p q = true -> SW W q -> SW W p.
Proof.
  intros W p q H [-> | [v [Hv Hq]]].
  - left. apply preb_nil_r. exact H.
  - right. exists v. split; [exact Hv | eapply preb_trans; eassumption].
Qed.

Lemma SW_snoc_iff : forall W v p, SW (W ++ [v]) p <-> SW W p \/ preb p v = true.
Proof.
  intros W v p. unfold SW. split.
  - intros [-> | [v' [Hv Hp]]]; [left; left; reflexivity|].
    apply in_app_iff in Hv as [Hv | [<- | []]].
    + left. right. exists v'. auto.
    + right. exact Hp.
  - intros [[-> | [v' [Hv Hp]]] | Hp].
    + left. reflexivity.
    + right. exists v'. split; [apply in_app_iff; left; exact Hv | exact Hp].
    + right. exists v. split; [apply in_app_iff; right; left; reflexivity | exact Hp].
Qed.

Lemma cntW_cons : forall v W p,
  cntW (v :: W) p = ((if preb p v then 1 else 0) + cntW W p)%nat.
Proof. reflexivity. Qed.

Lemma cntW_app : forall W v p,
  cntW (W ++ [v]) p = (cntW W p + (if preb p v then 1 else 0))%nat.
Proof.
  intros W v p. unfold cntW. rewrite map_app, list_sum_app. simpl. lia.
Qed.

Lemma cntW_le : forall W p, (cntW W p <= List.length W)%nat.
Proof.
  induction W as [|v W IH]; intros p; [reflexivity|].
  rewrite cntW_cons. simpl. specialize (IH p). destruct (preb p v); lia.
Qed.

Lemma cntW_notS : forall W p, ~ SW W p -> cntW W p = 0%nat.
Proof.
  induction W as [|v W IH]; intros p H; [reflexivity|].
  rewrite cntW_cons. destruct (preb p v) eqn:E.
  - exfalso. apply H. right. exists v. split; [left; reflexivity | exact E].
  - simpl. apply IH. intros [Hp | [v' [Hv Hp]]]; apply H; [left; exact Hp|].
    right. exists v'. split; [right; exact Hv | exact Hp].
Qed.

Lemma sumlen_app : forall W v, sumlen (W ++ [v]) = (sumlen W + List.length v)%nat.
Proof. intros W v. unfold sumlen. rewrite map_app, list_sum_app. simpl. lia. Qed.

Lemma sumn_ext : forall f g n, (forall l, (l < n)%nat -> f l = g l) -> sumn f n = sumn g n.
Proof.
  intros f g n. induction n as [|n IH]; intros H; [reflexivity|].
  simpl. rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma sumn_le : forall f n b, (forall l, (l < n)%nat -> (f l <= b)%nat) ->
  (sumn f n <= n * b)%nat.
Proof.
  intros f n b. induction n as [|n IH]; intros H; [simpl; lia|].
  simpl. specialize (IH ltac:(intros; apply H; lia)). specialize (H n ltac:(lia)). lia.
Qed.

Lemma index_of_some : forall p W k, index_of p W = Some k -> nth_error W k = Some p.
Proof.
  intros p W. induction W as [|v W IH]; intros k H; simpl in H; [discriminate|].
  destruct (list_eq_dec Z.eq_dec p v) as [-> | Hne].
  - injection H as <-. reflexivity.
  - destruct (index_of p W) as [k'|] eqn:E; simpl in H; [|discriminate].
    injection H as <-. simpl. apply IH. reflexivity.
Qed.

Lemma index_of_none : forall p W, index_of p W = None <-> ~ In p W.
Proof.
  intros p W. induction W as [|v W IH]; simpl.
  - split; [intros _ [] | reflexivity].
  - destruct (list_eq_dec Z.eq_dec p v) as [-> | Hne].
    + split; [discriminate | intros H; exfalso; apply H; left; reflexivity].
    + destruct (index_of p W) as [k'|] eqn:E; simpl.
      * split; [discriminate|]. intros H. exfalso. apply H. right.
        apply nth_error_In with k'. apply index_of_some. exact E.
      * split; [|reflexivity]. intros _ [H | H]; [congruence|].
        apply IH in H; [exact H | reflexivity].
Qed.

Lemma index_of_lt : forall p W k, index_of p W = Some k -> (k < List.length W)%nat.
Proof.
  intros p W k H. apply index_of_some in H. apply nth_error_Some. congruence.
Qed.

Lemma index_of_app_ne : forall p W v, p <> v -> index_of p (W ++ [v]) = index_of p W.
Proof.
  intros p W v Hne. induction W as [|v' W IH]; simpl.
  - destruct (list_eq_dec Z.eq_dec p v); [contradiction | reflexivity].
  - rewrite IH. reflexivity.
Qed.

Lemma index_of_app_last : forall W v, ~ In v W -> index_of v (W ++ [v]) = Some (List.length W).
Proof.
  induction W as [|v' W IH]; intros v H; simpl.
  - destruct (list_eq_dec Z.eq_dec v v); [reflexivity | contradiction].
  - destruct (list_eq_dec Z.eq_dec v v') as [-> | Hne].
    + exfalso. apply H. left. reflexivity.
    + rewrite IH by (intros H'; apply H; right; exact H'). reflexivity.
Qed.

Lemma EW_app_ne : forall W v p, p <> v -> EW (W ++ [v]) p = EW W p.
Proof.
  intros W v p Hne. unfold EW. rewrite index_of_app_ne by exact Hne.
  destruct (index_of p W) as [k|] eqn:E; [|reflexivity].
  apply index_of_lt in E. rewrite firstn_app.
  replace (S k - List.length W)%nat with O by lia. rewrite app_nil_r. reflexivity.
Qed.

Lemma EW_app_last : forall W v, ~ In v W ->
  EW (W ++ [v]) v = Z.of_nat (S (List.length W) + pathsum (W ++ [v]) v).
Proof.
  intros W v H. unfold EW. rewrite index_of_app_last by exact H.
  rewrite firstn_all2; [reflexivity|]. rewrite length_app. simpl. lia.
Qed.

Lemma preb_snoc_ne : forall p pre x, p <> pre ++ [x] -> preb p (pre ++ [x]) = preb p pre.
Proof.
  intros p pre x Hp. destruct (preb p pre) eqn:E1.
  - apply preb_snoc. right. exact E1.
  - destruct (preb p (pre ++ [x])) eqn:E2; [|reflexivity].
    apply preb_snoc in E2 as [E2|E2]; congruence.
Qed.

Lemma preb_snoc_short : forall pre x, preb (pre ++ [x]) pre = false.
Proof.
  intros pre x. destruct (preb (pre ++ [x]) pre) eqn:E; [|reflexivity].
  apply preb_len in E. rewrite length_app in E. simpl in E. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Array plumbing at a fixed universe                                  *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  ((φ i) < (φ (PArray.length t)))%Z -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b ltac:(rewrite ltb_spec; exact H)). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma alength_make : forall (n : int) (b : int),
  ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n b) = n.
Proof.
  intros n b H.
  transitivity (if n <=? PArray.max_length then n else PArray.max_length);
    [exact (length_make int n b)|].
  replace (n <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Lemma aget_make : forall (n i : int) (b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* The trie invariant                                                  *)
(* ------------------------------------------------------------------ *)

(* lbl n is the string of node n.  Wc: the words whose prefixes have
   nodes and are counted; We: the words whose end node holds its value. *)
Record Inv (T : tab) (cnt endv : array int) (sz : int) (lbl : int -> list Z)
    (Wc We : list (list Z)) : Prop := {
  iv_len_c : forall c, ((φ c) < 26)%Z -> PArray.length (sel T c) = PArray.length cnt;
  iv_len_e : PArray.length endv = PArray.length cnt;
  iv_sz : (1 <= (φ sz) <= (φ (PArray.length cnt)))%Z;
  iv_cap : ((φ sz) <= 1 + Z.of_nat (sumlen Wc))%Z;
  iv_root : lbl 0 = [];
  iv_inj : forall n m, ((φ n) < (φ sz))%Z -> ((φ m) < (φ sz))%Z -> lbl n = lbl m -> n = m;
  iv_S : forall n, ((φ n) < (φ sz))%Z -> SW Wc (lbl n);
  iv_child : forall n c, ((φ n) < (φ sz))%Z -> ((φ c) < 26)%Z ->
      (tget T c n <> 0 ->
         ((φ (tget T c n)) < (φ sz))%Z /\ lbl (tget T c n) = lbl n ++ [(φ c)]) /\
      (tget T c n = 0 -> ~ SW Wc (lbl n ++ [(φ c)]));
  iv_fresh : forall n c, ((φ sz) <= (φ n) < (φ (PArray.length cnt)))%Z -> ((φ c) < 26)%Z ->
      tget T c n = 0 /\ endv.[n] = 0;
  iv_cnt : forall n, (0 < (φ n) < (φ sz))%Z -> (φ (cnt.[n])) = Z.of_nat (cntW Wc (lbl n));
  iv_end : forall n, ((φ n) < (φ sz))%Z -> (φ (endv.[n])) = EW We (lbl n);
}.

Lemma lt_succ_cases : forall k sz : int, (φ (sz + 1)) = ((φ sz) + 1)%Z ->
  ((φ k) < (φ (sz + 1)))%Z -> k = sz \/ ((φ k) < (φ sz))%Z.
Proof.
  intros k sz H1 H2. destruct (Z.eq_dec (φ k) (φ sz)) as [E | E].
  - left. apply to_Z_inj. exact E.
  - right. lia.
Qed.

Lemma ins_step_new : forall T cnt endv sz lbl W0 pre x n c,
  Inv T cnt endv sz lbl (W0 ++ [pre]) W0 ->
  ((φ n) < (φ sz))%Z -> lbl n = pre -> (φ c) = x -> ((φ c) < 26)%Z -> tget T c n = 0 ->
  ((φ sz) < (φ (PArray.length cnt)))%Z ->
  Inv (tset T c n sz) cnt.[sz <- 1] endv (sz + 1)
      (fun k => if k =? sz then pre ++ [x] else lbl k) (W0 ++ [pre ++ [x]]) W0.
Proof.
  intros T cnt endv sz lbl W0 pre x n c HI Hn Hln Hcx Hc Ht0 Hcap.
  destruct HI as [Hlc Hle Hsz Hcp Hroot Hinj HS Hch Hfr Hcnt Hend].
  pose proof (alength_bound cnt) as Bc.
  assert (Hsz1 : (φ (sz + 1)) = ((φ sz) + 1)%Z) by sia.
  assert (HnS : ~ SW (W0 ++ [pre]) (pre ++ [x])).
  { destruct (Hch n c Hn Hc) as [_ H]. rewrite Hln, Hcx in H. exact (H Ht0). }
  assert (HnS0 : ~ SW W0 (pre ++ [x])).
  { intros H. apply HnS. apply SW_snoc_iff. left. exact H. }
  assert (Hne : forall k, ((φ k) < (φ sz))%Z -> lbl k <> pre ++ [x]).
  { intros k Hk E. apply HnS. rewrite <- E. apply HS. exact Hk. }
  assert (Lsz : forall k, (k =? sz) = false -> True) by auto.
  set (lbl' := fun k => if k =? sz then pre ++ [x] else lbl k).
  assert (Lold : forall k, ((φ k) < (φ sz))%Z -> lbl' k = lbl k).
  { intros k Hk. unfold lbl'. replace (k =? sz) with false; [reflexivity|].
    symmetry. apply eqb_false_spec. intros ->. lia. }
  assert (Lnew : lbl' sz = pre ++ [x]).
  { unfold lbl'. rewrite eqb_refl. reflexivity. }
  assert (Hnsz : n <> sz) by (intros ->; lia).
  assert (Hold_new : forall p, SW (W0 ++ [pre]) p -> SW (W0 ++ [pre ++ [x]]) p).
  { intros p H. apply SW_snoc_iff in H as [H | H]; apply SW_snoc_iff; [left; exact H|].
    right. eapply preb_trans; [exact H | apply preb_app]. }
  constructor.
  - intros c' Hc'. rewrite len_tset by assumption. rewrite alength_set. apply Hlc. exact Hc'.
  - rewrite alength_set. exact Hle.
  - rewrite alength_set. lia.
  - rewrite sumlen_app, length_app. rewrite sumlen_app in Hcp.
    change (List.length [x]) with 1%nat. lia.
  - rewrite Lold by lia. exact Hroot.
  - intros k1 k2 Hk1 Hk2 E.
    destruct (lt_succ_cases k1 sz Hsz1 Hk1) as [-> | H1];
      destruct (lt_succ_cases k2 sz Hsz1 Hk2) as [-> | H2]; [reflexivity | | |].
    + rewrite Lnew, Lold in E by exact H2. exfalso. exact (Hne k2 H2 (eq_sym E)).
    + rewrite Lnew, Lold in E by exact H1. exfalso. exact (Hne k1 H1 E).
    + rewrite !Lold in E by assumption. apply Hinj; assumption.
  - intros k Hk. destruct (lt_succ_cases k sz Hsz1 Hk) as [-> | H1].
    + rewrite Lnew. right. exists (pre ++ [x]). split; [|apply preb_refl].
      apply in_app_iff. right. left. reflexivity.
    + rewrite Lold by exact H1. apply Hold_new. apply HS. exact H1.
  - intros k c' Hk Hc'.
    destruct (lt_succ_cases k sz Hsz1 Hk) as [-> | H1].
    + rewrite tget_tset_other by (try assumption; right; exact Hnsz).
      destruct (Hfr sz c' ltac:(lia) Hc') as [Hz _]. rewrite Hz.
      split; [intros F; contradiction F; reflexivity|]. intros _.
      rewrite Lnew. intros H. apply SW_snoc_iff in H as [H | H].
      * apply HnS0. eapply SW_closed; [|exact H]. apply preb_app.
      * apply preb_len in H. rewrite !length_app in H. simpl in H. lia.
    + rewrite (Lold k H1).
      destruct (Uint63.eqb c c' && Uint63.eqb k n)%bool eqn:Ecn.
      * apply andb_prop in Ecn as [E1 E2]. apply eqb_spec in E1, E2. subst c' k.
        rewrite tget_tset_same by (try assumption; rewrite Hlc by exact Hc; lia).
        split; [|intros F; exfalso; rewrite F in Hsz; change (φ 0) with 0%Z in Hsz; lia].
        intros _. split; [lia|]. rewrite Lnew, Hln, Hcx. reflexivity.
      * rewrite tget_tset_other; [| assumption | assumption |].
        2:{ apply Bool.andb_false_iff in Ecn as [E | E]; apply eqb_false_spec in E;
            [left | right; intros F; apply E; symmetry]; congruence. }
        destruct (Hch k c' H1 Hc') as [Hy Hz]. split.
        -- intros Hm. destruct (Hy Hm) as [Hm1 Hm2]. split; [lia|].
           rewrite Lold by exact Hm1. exact Hm2.
        -- intros Hm H. apply SW_snoc_iff in H as [H | H].
           ++ apply (Hz Hm). apply SW_snoc_iff. left. exact H.
           ++ apply preb_snoc in H as [H | H].
              ** apply app_inj_tail in H as [H2 H3].
                 assert (k = n) by (apply Hinj; [exact H1 | exact Hn | congruence]).
                 assert (c' = c) by (apply to_Z_inj; lia).
                 subst. rewrite !eqb_refl in Ecn. discriminate.
              ** apply (Hz Hm). apply SW_snoc_iff. right. exact H.
  - intros k c' Hk Hc'. rewrite alength_set in Hk.
    rewrite tget_tset_other by (try assumption; right; intros ->; lia).
    apply Hfr; [lia | exact Hc'].
  - intros k Hk. destruct (lt_succ_cases k sz Hsz1 ltac:(lia)) as [-> | H1].
    + rewrite aget_set_same by lia. rewrite Lnew, cntW_app, preb_refl.
      rewrite (cntW_notS W0 _ HnS0). reflexivity.
    + rewrite aget_set_other by (intros ->; lia). rewrite (Lold k H1), Hcnt by lia.
      rewrite !cntW_app. rewrite preb_snoc_ne by (apply Hne; exact H1). reflexivity.
  - intros k Hk. destruct (lt_succ_cases k sz Hsz1 Hk) as [-> | H1].
    + destruct (Hfr sz c ltac:(lia) Hc) as [_ Hz]. rewrite Hz, Lnew.
      unfold EW. replace (index_of (pre ++ [x]) W0) with (@None nat); [reflexivity|].
      symmetry. apply index_of_none. intros H. apply HnS0. right.
      exists (pre ++ [x]). split; [exact H | apply preb_refl].
    + rewrite (Lold k H1). apply Hend. exact H1.
Qed.

Lemma ins_step_old : forall T cnt endv sz lbl W0 pre x n c,
  Inv T cnt endv sz lbl (W0 ++ [pre]) W0 ->
  (Z.of_nat (List.length W0) <= 30000)%Z ->
  ((φ n) < (φ sz))%Z -> lbl n = pre -> (φ c) = x -> ((φ c) < 26)%Z -> tget T c n <> 0 ->
  Inv T cnt.[tget T c n <- cnt.[tget T c n] + 1] endv sz lbl (W0 ++ [pre ++ [x]]) W0 /\
  (φ (cnt.[tget T c n] + 1)) = Z.of_nat (S (cntW W0 (pre ++ [x]))) /\
  ((φ (tget T c n)) < (φ sz))%Z /\ lbl (tget T c n) = pre ++ [x].
Proof.
  intros T cnt endv sz lbl W0 pre x n c HI HW Hn Hln Hcx Hc Hm0.
  destruct HI as [Hlc Hle Hsz Hcp Hroot Hinj HS Hch Hfr Hcnt Hend].
  destruct (proj1 (Hch n c Hn Hc) Hm0) as [Hmsz Hlm].
  rewrite Hln, Hcx in Hlm.
  set (m := tget T c n) in *.
  assert (Hmpos : (0 < (φ m))%Z).
  { pose proof (to_Z_bounded m). destruct (Z.eq_dec (φ m) 0) as [E|E]; [|lia].
    exfalso. apply Hm0. apply to_Z_inj. exact E. }
  assert (HSm : SW (W0 ++ [pre]) (pre ++ [x])) by (rewrite <- Hlm; apply HS; exact Hmsz).
  assert (Hiff : forall p, SW (W0 ++ [pre ++ [x]]) p <-> SW (W0 ++ [pre]) p).
  { intros p. split.
    - intros H. apply SW_snoc_iff in H as [H | H].
      + apply SW_snoc_iff. left. exact H.
      + eapply SW_closed; [exact H | exact HSm].
    - intros H. apply SW_snoc_iff in H as [H | H]; apply SW_snoc_iff; [left; exact H|].
      right. eapply preb_trans; [exact H | apply preb_app]. }
  assert (Hcm : (φ (cnt.[m] + 1)) = Z.of_nat (S (cntW W0 (pre ++ [x])))).
  { assert (Hc0 : (φ (cnt.[m])) = Z.of_nat (cntW W0 (pre ++ [x]))).
    { rewrite Hcnt by lia. rewrite Hlm, cntW_app, preb_snoc_short. lia. }
    pose proof (cntW_le W0 (pre ++ [x])).
    rewrite add_spec, Hc0. change (φ 1) with 1%Z. rewrite wB_val.
    rewrite Z.mod_small; lia. }
  split; [|split; [exact Hcm | split; [exact Hmsz | exact Hlm]]].
  constructor.
  - intros c' Hc'. rewrite alength_set. apply Hlc. exact Hc'.
  - rewrite alength_set. exact Hle.
  - rewrite alength_set. exact Hsz.
  - rewrite sumlen_app, length_app. rewrite sumlen_app in Hcp.
    change (List.length [x]) with 1%nat. lia.
  - exact Hroot.
  - exact Hinj.
  - intros k Hk. apply Hiff. apply HS. exact Hk.
  - intros k c' Hk Hc'. destruct (Hch k c' Hk Hc') as [Hy Hz]. split; [exact Hy|].
    intros H0 H. apply (Hz H0). apply Hiff. exact H.
  - intros k c' Hk Hc'. rewrite alength_set in Hk. apply Hfr; assumption.
  - intros k Hk. destruct (k =? m) eqn:E.
    + apply eqb_spec in E. subst k.
      rewrite aget_set_same by lia.
      rewrite Hcm, Hlm, cntW_app, preb_refl. lia.
    + apply eqb_false_spec in E. rewrite aget_set_other by (intros F; apply E; symmetry; exact F).
      rewrite Hcnt by exact Hk. rewrite !cntW_app. rewrite preb_snoc_ne; [reflexivity|].
      intros F. apply E. apply Hinj; [lia | exact Hmsz | congruence].
  - exact Hend.
Qed.

Lemma Inv_nil : forall T cnt endv sz lbl W0 We,
  Inv T cnt endv sz lbl W0 We -> Inv T cnt endv sz lbl (W0 ++ [[]]) We.
Proof.
  intros T cnt endv sz lbl W0 We HI.
  destruct HI as [Hlc Hle Hsz Hcp Hroot Hinj HS Hch Hfr Hcnt Hend].
  assert (Hiff : forall p, SW (W0 ++ [[]]) p <-> SW W0 p).
  { intros p. rewrite SW_snoc_iff. split; [|left; assumption].
    intros [H | H]; [exact H | left; apply preb_nil_r; exact H]. }
  constructor; try assumption.
  - rewrite sumlen_app. change (List.length (@nil Z)) with 0%nat. lia.
  - intros k Hk. apply Hiff. apply HS. exact Hk.
  - intros k c Hk Hc. destruct (Hch k c Hk Hc) as [Hy Hz]. split; [exact Hy|].
    intros H0 H. apply (Hz H0). apply Hiff. exact H.
  - intros k Hk. rewrite Hcnt by exact Hk. rewrite cntW_app.
    destruct (preb (lbl k) []) eqn:E; [|lia].
    apply preb_nil_r in E. rewrite <- Hroot in E.
    apply Hinj in E; [| lia | lia]. subst k. change (φ 0) with 0%Z in Hk. lia.
Qed.

Lemma Inv_end : forall T cnt endv sz lbl Wc W0 n u v,
  Inv T cnt endv sz lbl Wc W0 -> ((φ n) < (φ sz))%Z -> lbl n = u -> ~ In u W0 ->
  (φ v) = EW (W0 ++ [u]) u ->
  Inv T cnt endv.[n <- v] sz lbl Wc (W0 ++ [u]).
Proof.
  intros T cnt endv sz lbl Wc W0 n u v HI Hn Hln Hu Hv.
  destruct HI as [Hlc Hle Hsz Hcp Hroot Hinj HS Hch Hfr Hcnt Hend].
  constructor; try assumption.
  - rewrite alength_set. exact Hle.
  - intros k c Hk Hc. rewrite aget_set_other by (intros ->; lia). apply Hfr; assumption.
  - intros k Hk. destruct (k =? n) eqn:E.
    + apply eqb_spec in E. subst k. rewrite aget_set_same by (rewrite Hle; lia).
      rewrite Hln. exact Hv.
    + apply eqb_false_spec in E. rewrite aget_set_other by (intros F; apply E; symmetry; exact F).
      rewrite EW_app_ne; [apply Hend; exact Hk|].
      intros F. apply E. apply Hinj; [exact Hk | exact Hn | congruence].
Qed.

(* ------------------------------------------------------------------ *)
(* The insertion loop                                                  *)
(* ------------------------------------------------------------------ *)

(* w is read as the letter indices u *)
Definition wrep (w : PrimString.string) (u : list Z) : Prop :=
  (φ (PrimString.length w)) = Z.of_nat (List.length u) /\
  forall i : int, ((φ i) < (φ (PrimString.length w)))%Z ->
    nth_error u (Z.to_nat (φ i)) = Some (φ (PrimString.get w i - 97)) /\
    ((φ (PrimString.get w i - 97)) < 26)%Z.

Lemma firstn_snoc : forall {A} (u : list A) i x, nth_error u i = Some x ->
  firstn (S i) u = firstn i u ++ [x].
Proof.
  intros A u. induction u as [|y u IH]; intros i x H; [destruct i; discriminate|].
  destruct i as [|i]; simpl in H.
  - injection H as ->. reflexivity.
  - change (firstn (S (S i)) (y :: u)) with (y :: firstn (S i) u).
    rewrite (IH i x H). reflexivity.
Qed.

Definition stepsum (W0 : list (list Z)) (u : list Z) (i : nat) : nat :=
  sumn (fun l => S (cntW W0 (firstn (S l) u))) i.

Lemma stepsum_bound : forall W0 u i,
  (stepsum W0 u i <= i * (List.length W0 + 1))%nat.
Proof.
  intros W0 u i. apply sumn_le. intros l _. pose proof (cntW_le W0 (firstn (S l) u)). lia.
Qed.

Lemma ins_spec : forall w u W0, wrep w u ->
  (Z.of_nat (List.length u) < 30)%Z -> (Z.of_nat (List.length W0) <= 30000)%Z ->
  forall z i T cnt endv sz n s lbl (H : Acc (Zwf 0) (gap (PrimString.length w) i)),
  gap (PrimString.length w) i = z ->
  ((φ i) <= (φ (PrimString.length w)))%Z ->
  Inv T cnt endv sz lbl (W0 ++ [firstn (Z.to_nat (φ i)) u]) W0 ->
  (1 + Z.of_nat (sumlen (W0 ++ [u])) <= (φ (PArray.length cnt)))%Z ->
  ((φ n) < (φ sz))%Z -> lbl n = firstn (Z.to_nat (φ i)) u ->
  (φ s) = Z.of_nat (stepsum W0 u (Z.to_nat (φ i))) ->
  forall r, r = ins_loop w (PrimString.length w) T cnt sz i n s H ->
  PArray.length (r_cnt r) = PArray.length cnt /\
  exists lbl', Inv (r_T r) (r_cnt r) endv (r_sz r) lbl' (W0 ++ [u]) W0 /\
    ((φ (r_n r)) < (φ (r_sz r)))%Z /\ lbl' (r_n r) = u /\
    (φ (r_s r)) = Z.of_nat (stepsum W0 u (List.length u)).
Proof.
  intros w u W0 Hw Hu HW z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i T cnt endv sz n s lbl H Hz Hi HI Hcap Hn Hln Hs r Hr.
  rewrite ins_loop_eq in Hr.
  pose proof Hw as [Hwl Hwc].
  pose proof (to_Z_bounded i) as Bi.
  destruct (bdec (i <? PrimString.length w)) as [Hi' | Hi'].
  - pose proof Hi' as Hlt. rewrite ltb_spec in Hlt.
    destruct (Hwc i Hlt) as [Hx Hc26].
    cbv zeta in Hr.
    set (c := PrimString.get w i - 97) in *.
    set (pre := firstn (Z.to_nat (φ i)) u) in *.
    assert (Hfs : firstn (S (Z.to_nat (φ i))) u = pre ++ [(φ c)])
      by (apply firstn_snoc; exact Hx).
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    assert (Hti : Z.to_nat (φ (i + 1)) = S (Z.to_nat (φ i))) by lia.
    assert (Hdec : Zwf 0 (gap (PrimString.length w) (i + 1)) z)
      by (rewrite <- Hz; apply dec_step; exact Hi').
    assert (Bs : (Z.of_nat (stepsum W0 u (S (Z.to_nat (φ i)))) <= 900030)%Z).
    { pose proof (stepsum_bound W0 u (S (Z.to_nat (φ i)))) as Bs.
      apply Nat2Z.inj_le in Bs. rewrite Nat2Z.inj_mul in Bs. nia. }
    assert (Hss : stepsum W0 u (S (Z.to_nat (φ i))) =
                    (stepsum W0 u (Z.to_nat (φ i)) + S (cntW W0 (pre ++ [(φ c)])))%nat)
      by (unfold stepsum; cbn [sumn]; rewrite Hfs; reflexivity).
    destruct (tget T c n =? 0) eqn:Et.
    + apply eqb_spec in Et.
      assert (Hszc : ((φ sz) < (φ (PArray.length cnt)))%Z).
      { pose proof (iv_cap _ _ _ _ _ _ _ HI) as Hc.
        rewrite !sumlen_app in *. unfold pre in Hc. rewrite length_firstn in Hc. lia. }
      pose proof (iv_sz _ _ _ _ _ _ _ HI) as Hsz.
      assert (Hc0 : cntW W0 (pre ++ [(φ c)]) = O).
      { apply cntW_notS. intros F.
        destruct (iv_child _ _ _ _ _ _ _ HI n c Hn Hc26) as [_ Hz0].
        apply (Hz0 Et). rewrite Hln. apply SW_snoc_iff. left. exact F. }
      pose proof (ins_step_new T cnt endv sz lbl W0 pre (φ c) n c HI Hn Hln eq_refl Hc26 Et Hszc)
        as HI'.
      rewrite <- Hfs, <- Hti in HI'.
      destruct (IH _ Hdec (i + 1) _ _ endv _ sz (s + 1) _ _ eq_refl ltac:(lia) HI'
                  ltac:(rewrite alength_set; exact Hcap) ltac:(sia)
                  ltac:(cbv beta; rewrite eqb_refl, Hti, Hfs; reflexivity)
                  ltac:(rewrite Hti, Hss, Hc0, add_spec; change (φ 1) with 1%Z;
                        rewrite Hs, Z.mod_small; rewrite ?wB_val; lia)
                  r Hr) as [Hlen Hrest].
      split; [rewrite Hlen, alength_set; reflexivity | exact Hrest].
    + apply eqb_false_spec in Et.
      destruct (ins_step_old T cnt endv sz lbl W0 pre (φ c) n c HI HW Hn Hln eq_refl Hc26 Et)
        as [HI' [Hk [Hmsz Hlm]]].
      rewrite <- Hfs, <- Hti in HI'.
      destruct (IH _ Hdec (i + 1) _ _ endv sz (tget T c n) (s + (cnt.[tget T c n] + 1)) _ _ eq_refl ltac:(lia) HI'
                  ltac:(rewrite alength_set; exact Hcap) Hmsz
                  ltac:(rewrite Hti, Hfs; exact Hlm)
                  ltac:(rewrite Hti, Hss, add_spec, Hk, Hs, Z.mod_small; rewrite ?wB_val; lia)
                  r Hr) as [Hlen Hrest].
      split; [rewrite Hlen, alength_set; reflexivity | exact Hrest].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi'.
    assert (Hiu : Z.to_nat (φ i) = List.length u) by lia.
    rewrite Hiu, firstn_all in HI, Hln. rewrite Hiu in Hs.
    subst r. simpl. split; [reflexivity|]. exists lbl. auto.
Qed.

(* ------------------------------------------------------------------ *)
(* The database loop                                                   *)
(* ------------------------------------------------------------------ *)

(* the array of words db is read as the list D of letter-index lists *)
Definition dbrep (db : array PrimString.string) (D : list (list Z)) : Prop :=
  (φ (PArray.length db)) = Z.of_nat (List.length D) /\
  forall j : int, ((φ j) < (φ (PArray.length db)))%Z ->
    exists u, nth_error D (Z.to_nat (φ j)) = Some u /\ wrep db.[j] u.

Lemma sumlen_firstn_le : forall D k, (sumlen (firstn k D) <= sumlen D)%nat.
Proof.
  intros D k. rewrite <- (firstn_skipn k D) at 2. unfold sumlen.
  rewrite map_app, list_sum_app. lia.
Qed.

Lemma stepsum_pathsum : forall W0 u, pathsum (W0 ++ [u]) u = stepsum W0 u (List.length u).
Proof.
  intros W0 u. unfold pathsum, stepsum. apply sumn_ext. intros l _.
  rewrite cntW_app, preb_firstn. lia.
Qed.

Lemma notin_prefix : forall (D : list (list Z)) j u, NoDup D -> nth_error D j = Some u ->
  ~ In u (firstn j D).
Proof.
  intros D j u HD Hu Hin.
  assert (E : D = firstn j D ++ u :: skipn (S j) D).
  { rewrite <- (firstn_skipn (S j) D) at 1. rewrite (firstn_snoc D j u Hu), <- app_assoc.
    reflexivity. }
  rewrite E in HD. apply NoDup_remove_2 in HD. apply HD. apply in_app_iff. left. exact Hin.
Qed.

Lemma build_spec : forall db D, dbrep db D -> NoDup D ->
  (Z.of_nat (List.length D) <= 30000)%Z ->
  Forall (fun u => Z.of_nat (List.length u) < 30)%Z D ->
  forall z j T cnt endv sz lbl (H : Acc (Zwf 0) (gap (PArray.length db) j)),
  gap (PArray.length db) j = z ->
  ((φ j) <= (φ (PArray.length db)))%Z ->
  Inv T cnt endv sz lbl (firstn (Z.to_nat (φ j)) D) (firstn (Z.to_nat (φ j)) D) ->
  (1 + Z.of_nat (sumlen D) <= (φ (PArray.length cnt)))%Z ->
  forall b, b = build db (PArray.length db) T cnt endv sz j H ->
  exists sz' lbl', Inv (b_T b) (b_cnt b) (b_end b) sz' lbl' D D.
Proof.
  intros db D Hdb HND HDl HDu z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j T cnt endv sz lbl H Hz Hj HI Hcap b Hb.
  rewrite build_eq in Hb.
  pose proof Hdb as [Hdl Hdc].
  pose proof (to_Z_bounded j) as Bj.
  destruct (bdec (j <? PArray.length db)) as [Hj' | Hj'].
  - pose proof Hj' as Hlt. rewrite ltb_spec in Hlt.
    destruct (Hdc j Hlt) as [u [Hu Hw]].
    cbv zeta in Hb.
    set (W0 := firstn (Z.to_nat (φ j)) D) in *.
    assert (HW0 : Z.of_nat (List.length W0) = (φ j))
      by (unfold W0; rewrite length_firstn; lia).
    assert (Hul : (Z.of_nat (List.length u) < 30)%Z).
    { rewrite Forall_forall in HDu. apply HDu. eapply nth_error_In. exact Hu. }
    assert (HI0 : Inv T cnt endv sz lbl (W0 ++ [firstn (Z.to_nat (φ 0)) u]) W0)
      by (apply Inv_nil; exact HI).
    assert (Hfs : firstn (S (Z.to_nat (φ j))) D = W0 ++ [u]) by (apply firstn_snoc; exact Hu).
    assert (Hcap' : (1 + Z.of_nat (sumlen (W0 ++ [u])) <= (φ (PArray.length cnt)))%Z).
    { rewrite <- Hfs. pose proof (sumlen_firstn_le D (S (Z.to_nat (φ j)))). lia. }
    pose proof (iv_sz _ _ _ _ _ _ _ HI) as Hsz.
    destruct (ins_spec db.[j] u W0 Hw Hul ltac:(lia) _ 0 T cnt endv sz 0 0 lbl
                (Zwf_well_founded 0 (gap (PrimString.length db.[j]) 0)) eq_refl
                ltac:(destruct Hw as [Hwl _]; change (φ 0) with 0%Z; lia) HI0 Hcap'
                ltac:(change (φ 0) with 0%Z; lia)
                ltac:(rewrite (iv_root _ _ _ _ _ _ _ HI); reflexivity)
                ltac:(reflexivity) _ eq_refl)
      as [Hlen [lbl' [HI' [Hn' [Hln' Hs']]]]].
    assert (Hnin : ~ In u W0) by (apply notin_prefix; assumption).
    assert (Bs : (Z.of_nat (stepsum W0 u (List.length u)) <= 900030)%Z).
    { pose proof (stepsum_bound W0 u (List.length u)) as Bs.
      apply Nat2Z.inj_le in Bs. rewrite Nat2Z.inj_mul in Bs. nia. }
    match type of Hs' with (φ (r_s ?t)) = _ => set (r := t) in * end.
    assert (Hv : (φ (j + 1 + r_s r)) = EW (W0 ++ [u]) u).
    { rewrite EW_app_last by exact Hnin. rewrite stepsum_pathsum.
      rewrite !add_spec. change (φ 1) with 1%Z. rewrite Hs', wB_val.
      rewrite (Z.mod_small ((φ j) + 1)) by lia. rewrite Z.mod_small by lia. lia. }
    pose proof (Inv_end _ _ _ _ _ _ _ _ _ _ HI' Hn' Hln' Hnin Hv) as HI2.
    rewrite <- Hfs in HI2.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    assert (Htj : Z.to_nat (φ (j + 1)) = S (Z.to_nat (φ j))) by lia.
    rewrite <- Htj in HI2.
    assert (Hdec : Zwf 0 (gap (PArray.length db) (j + 1)) z)
      by (rewrite <- Hz; apply dec_step; exact Hj').
    exact (IH _ Hdec (j + 1) _ _ _ _ _ _ eq_refl ltac:(lia) HI2
             ltac:(rewrite Hlen; exact Hcap) b Hb).
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hj'.
    assert (HjD : Z.to_nat (φ j) = List.length D) by lia.
    rewrite HjD, firstn_all in HI. subst b. simpl. exists sz, lbl. exact HI.
Qed.

(* ------------------------------------------------------------------ *)
(* The query walk                                                      *)
(* ------------------------------------------------------------------ *)

Lemma sumn_tail_zero : forall f k n, (k <= n)%nat ->
  (forall l, (k <= l < n)%nat -> f l = O) -> sumn f n = sumn f k.
Proof.
  intros f k n. induction n as [|n IH]; intros Hk H.
  - replace k with O by lia. reflexivity.
  - destruct (Nat.eq_dec k (S n)) as [-> | Hne]; [reflexivity|].
    simpl. rewrite IH; [| lia | intros; apply H; lia]. rewrite H by lia. lia.
Qed.

Lemma qwalk_spec : forall T cnt endv sz lbl D, Inv T cnt endv sz lbl D D ->
  (Z.of_nat (List.length D) <= 30000)%Z ->
  forall q v N, wrep q v -> (Z.of_nat (List.length v) < 30)%Z ->
  (φ N) = Z.of_nat (List.length D) ->
  forall z i n s (H : Acc (Zwf 0) (gap (PrimString.length q) i)),
  gap (PrimString.length q) i = z -> ((φ i) <= (φ (PrimString.length q)))%Z ->
  ((φ n) < (φ sz))%Z -> lbl n = firstn (Z.to_nat (φ i)) v ->
  (φ s) = Z.of_nat (sumn (fun l => cntW D (firstn (S l) v)) (Z.to_nat (φ i))) ->
  (φ (qwalk q (PrimString.length q) T cnt endv N i n s H)) = Z.of_nat (ansm D v).
Proof.
  intros T cnt endv sz lbl D HI HD q v N Hw Hv HN z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i n s H Hz Hi Hn Hln Hs.
  rewrite qwalk_eq.
  pose proof Hw as [Hwl Hwc].
  pose proof (to_Z_bounded i) as Bi.
  set (f := fun l => cntW D (firstn (S l) v)) in *.
  assert (Bf : forall k, (k <= List.length v)%nat -> (Z.of_nat (sumn f k) <= 900000)%Z).
  { intros k Hk. pose proof (sumn_le f k (List.length D) ltac:(intros; apply cntW_le)) as B.
    apply Nat2Z.inj_le in B. rewrite Nat2Z.inj_mul in B. nia. }
  assert (Hpath : pathsum D v = sumn f (List.length v)) by reflexivity.
  destruct (bdec (i <? PrimString.length q)) as [Hi' | Hi'].
  - pose proof Hi' as Hlt. rewrite ltb_spec in Hlt.
    destruct (Hwc i Hlt) as [Hx Hc26].
    cbv zeta.
    set (c := PrimString.get q i - 97) in *.
    assert (Hfs : firstn (S (Z.to_nat (φ i))) v = firstn (Z.to_nat (φ i)) v ++ [(φ c)])
      by (apply firstn_snoc; exact Hx).
    destruct (iv_child _ _ _ _ _ _ _ HI n c Hn Hc26) as [Hy Hz0].
    rewrite Hln, <- Hfs in Hy, Hz0.
    destruct (tget T c n =? 0) eqn:Et.
    + apply eqb_spec in Et. specialize (Hz0 Et).
      assert (Hnone : index_of v D = None).
      { apply index_of_none. intros Hin. apply Hz0. right. exists v.
        split; [exact Hin | apply preb_firstn]. }
      unfold ansm. rewrite Hnone, Hpath.
      assert (Hrest : sumn f (List.length v) = sumn f (Z.to_nat (φ i))).
      { apply sumn_tail_zero; [lia|]. intros l Hl. unfold f. apply cntW_notS.
        intros HS. apply Hz0. eapply SW_closed; [|exact HS].
        replace (firstn (S (Z.to_nat (φ i))) v)
          with (firstn (S (Z.to_nat (φ i))) (firstn (S l) v))
          by (rewrite firstn_firstn; f_equal; lia).
        apply preb_firstn. }
      pose proof (Bf (Z.to_nat (φ i)) ltac:(lia)).
      rewrite Hrest, add_spec, HN, Hs, wB_val, Z.mod_small by lia. lia.
    + apply eqb_false_spec in Et. destruct (Hy Et) as [Hmsz Hlm].
      assert (Hmpos : (0 < (φ (tget T c n)))%Z).
      { pose proof (to_Z_bounded (tget T c n)).
        destruct (Z.eq_dec (φ (tget T c n)) 0) as [E|E]; [|lia].
        exfalso. apply Et. apply to_Z_inj. exact E. }
      assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
      assert (Hti : Z.to_nat (φ (i + 1)) = S (Z.to_nat (φ i))) by lia.
      assert (Hdec : Zwf 0 (gap (PrimString.length q) (i + 1)) z)
        by (rewrite <- Hz; apply dec_step; exact Hi').
      pose proof (iv_cnt _ _ _ _ _ _ _ HI (tget T c n) ltac:(lia)) as Hcm.
      rewrite Hlm in Hcm.
      pose proof (Bf (S (Z.to_nat (φ i))) ltac:(lia)) as Bf1.
      apply (IH _ Hdec (i + 1) _ _ _ eq_refl ltac:(lia) Hmsz ltac:(rewrite Hti; exact Hlm)).
      rewrite Hti, add_spec, Hs, Hcm, Z.mod_small.
      * change (sumn f (S (Z.to_nat (φ i))))
          with (sumn f (Z.to_nat (φ i)) + f (Z.to_nat (φ i)))%nat.
        rewrite Nat2Z.inj_add. reflexivity.
      * change (sumn f (S (Z.to_nat (φ i))))
          with (sumn f (Z.to_nat (φ i)) + f (Z.to_nat (φ i)))%nat in Bf1.
        rewrite Nat2Z.inj_add in Bf1.
        change (f (Z.to_nat (φ i))) with (cntW D (firstn (S (Z.to_nat (φ i))) v)) in Bf1.
        rewrite wB_val. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi'.
    assert (Hiv : Z.to_nat (φ i) = List.length v) by lia.
    rewrite Hiv, firstn_all in Hln. rewrite Hiv in Hs.
    cbv zeta.
    pose proof (iv_end _ _ _ _ _ _ _ HI n Hn) as He. rewrite Hln in He.
    unfold EW in He. unfold ansm.
    destruct (index_of v D) as [k|] eqn:Ei.
    + replace (endv.[n] =? 0) with false.
      * exact He.
      * symmetry. apply eqb_false_spec. intros F. rewrite F in He.
        change (φ 0) with 0%Z in He. lia.
    + replace (endv.[n] =? 0) with true.
      * pose proof (Bf (List.length v) ltac:(lia)).
        rewrite add_spec, HN, Hs, wB_val, Z.mod_small by lia. rewrite <- Hpath. lia.
      * symmetry. apply eqb_spec. apply to_Z_inj. exact He.
Qed.

Lemma query_spec : forall T cnt endv sz lbl D, Inv T cnt endv sz lbl D D ->
  (Z.of_nat (List.length D) <= 30000)%Z ->
  forall q v N, wrep q v -> (Z.of_nat (List.length v) < 30)%Z ->
  (φ N) = Z.of_nat (List.length D) ->
  (φ (query q T cnt endv N)) = Z.of_nat (ansm D v).
Proof.
  intros T cnt endv sz lbl D HI HD q v N Hw Hv HN. unfold query.
  pose proof (iv_sz _ _ _ _ _ _ _ HI) as Hsz.
  pose proof Hw as [Hwl _].
  apply (qwalk_spec T cnt endv sz lbl D HI HD q v N Hw Hv HN _ 0 0 0 _ eq_refl).
  - change (φ 0) with 0%Z. lia.
  - change (φ 0) with 0%Z. lia.
  - rewrite (iv_root _ _ _ _ _ _ _ HI). reflexivity.
  - reflexivity.
Qed.

Lemma answer_spec : forall T cnt endv sz lbl D, Inv T cnt endv sz lbl D D ->
  (Z.of_nat (List.length D) <= 30000)%Z ->
  forall qs Qs N, dbrep qs Qs -> Forall (fun v => Z.of_nat (List.length v) < 30)%Z Qs ->
  (φ N) = Z.of_nat (List.length D) ->
  forall z k out (H : Acc (Zwf 0) (gap (PArray.length qs) k)),
  gap (PArray.length qs) k = z -> ((φ k) <= (φ (PArray.length qs)))%Z ->
  PArray.length out = PArray.length qs ->
  (forall k', ((φ k') < (φ k))%Z -> forall v, nth_error Qs (Z.to_nat (φ k')) = Some v ->
      (φ (out.[k'])) = Z.of_nat (ansm D v)) ->
  forall res, res = answer qs (PArray.length qs) T cnt endv N out k H ->
  PArray.length res = PArray.length qs /\
  forall k', ((φ k') < (φ (PArray.length qs)))%Z ->
    forall v, nth_error Qs (Z.to_nat (φ k')) = Some v ->
      (φ (res.[k'])) = Z.of_nat (ansm D v).
Proof.
  intros T cnt endv sz lbl D HI HD qs Qs N Hqs HQ HN z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k out H Hz Hk Hlen Hout res Hres.
  rewrite answer_eq in Hres.
  pose proof Hqs as [Hql Hqc].
  destruct (bdec (k <? PArray.length qs)) as [Hk' | Hk'].
  - pose proof Hk' as Hlt. rewrite ltb_spec in Hlt.
    destruct (Hqc k Hlt) as [v [Hv Hw]].
    assert (Hvl : (Z.of_nat (List.length v) < 30)%Z).
    { rewrite Forall_forall in HQ. apply HQ. eapply nth_error_In. exact Hv. }
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    assert (Hdec : Zwf 0 (gap (PArray.length qs) (k + 1)) z)
      by (rewrite <- Hz; apply dec_step; exact Hk').
    apply (IH _ Hdec (k + 1) (out.[k <- query qs.[k] T cnt endv N])
             (Acc_inv H (dec_step (PArray.length qs) k Hk')) eq_refl ltac:(lia)
             ltac:(rewrite alength_set; exact Hlen)); [|exact Hres].
    intros k' Hk'' v' Hv'.
    destruct (Z.eq_dec (φ k') (φ k)) as [E | E].
    + assert (k' = k) by (apply to_Z_inj; exact E). subst k'.
      rewrite aget_set_same by lia. rewrite Hv in Hv'. injection Hv' as <-.
      exact (query_spec T cnt endv sz lbl D HI HD _ v N Hw Hvl HN).
    + rewrite aget_set_other by (intros F; apply E; rewrite F; reflexivity).
      apply Hout; [lia | exact Hv'].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk'.
    subst res. split; [exact Hlen|]. intros k' Hk'' v Hv. apply Hout; [lia | exact Hv].
Qed.

(* ------------------------------------------------------------------ *)
(* The total length and the initial trie                               *)
(* ------------------------------------------------------------------ *)

Lemma skipn_nth : forall {A} (D : list A) j u, nth_error D j = Some u ->
  skipn j D = u :: skipn (S j) D.
Proof.
  intros A D. induction D as [|y D IH]; intros j u H; [destruct j; discriminate|].
  destruct j as [|j]; simpl in H.
  - injection H as ->. reflexivity.
  - simpl. apply IH. exact H.
Qed.

Lemma sumlen_cons : forall u W, sumlen (u :: W) = (List.length u + sumlen W)%nat.
Proof. reflexivity. Qed.

Lemma total_spec : forall db D, dbrep db D ->
  forall z j acc (H : Acc (Zwf 0) (gap (PArray.length db) j)),
  gap (PArray.length db) j = z -> ((φ j) <= (φ (PArray.length db)))%Z ->
  ((φ acc) + Z.of_nat (sumlen (skipn (Z.to_nat (φ j)) D)) < wB)%Z ->
  (φ (total db (PArray.length db) j acc H))
  = ((φ acc) + Z.of_nat (sumlen (skipn (Z.to_nat (φ j)) D)))%Z.
Proof.
  intros db D Hdb z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j acc H Hz Hj Hb.
  rewrite total_eq.
  pose proof Hdb as [Hdl Hdc].
  pose proof (to_Z_bounded j) as Bj.
  destruct (bdec (j <? PArray.length db)) as [Hj' | Hj'].
  - pose proof Hj' as Hlt. rewrite ltb_spec in Hlt.
    destruct (Hdc j Hlt) as [u [Hu [Hwl _]]].
    rewrite (skipn_nth D _ u Hu), sumlen_cons in *.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    assert (Htj : Z.to_nat (φ (j + 1)) = S (Z.to_nat (φ j))) by lia.
    assert (Hdec : Zwf 0 (gap (PArray.length db) (j + 1)) z)
      by (rewrite <- Hz; apply dec_step; exact Hj').
    pose proof (to_Z_bounded acc).
    assert (Ha : (φ (acc + PrimString.length db.[j])) = ((φ acc) + Z.of_nat (List.length u))%Z).
    { rewrite add_spec, Hwl. apply Z.mod_small. lia. }
    rewrite (IH _ Hdec (j + 1) _ _ eq_refl ltac:(lia)); rewrite Ha, Htj; lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hj'.
    rewrite skipn_all2 by lia. simpl. lia.
Qed.

Lemma sumlen_bound : forall D, Forall (fun u => Z.of_nat (List.length u) < 30)%Z D ->
  (Z.of_nat (sumlen D) <= 29 * Z.of_nat (List.length D))%Z.
Proof.
  induction D as [|u D IH]; intros H; [simpl; lia|].
  inversion H as [|? ? Hu HD]; subst. rewrite sumlen_cons. specialize (IH HD).
  simpl List.length. lia.
Qed.

Lemma Inv_init : forall cap : int, (1 <= (φ cap) <= 4194303)%Z ->
  Inv (mk_tab cap) (PArray.make cap 0) (PArray.make cap 0) 1 (fun _ => []) [] [].
Proof.
  intros cap Hcap.
  assert (Hl : PArray.length (PArray.make cap 0) = cap) by (apply alength_make; lia).
  assert (Hlt1 : forall n : int, ((φ n) < (φ 1))%Z -> n = 0).
  { intros n Hn. change (φ 1) with 1%Z in Hn. pose proof (to_Z_bounded n).
    apply to_Z_inj. change (φ 0) with 0%Z. lia. }
  assert (Hg : forall c n, tget (mk_tab cap) c n = 0).
  { intros c n. unfold tget. rewrite sel_mk_tab. apply aget_make. }
  constructor.
  - intros c _. rewrite sel_mk_tab. reflexivity.
  - reflexivity.
  - rewrite Hl. change (φ 1) with 1%Z. lia.
  - change (φ 1) with 1%Z. simpl. lia.
  - reflexivity.
  - intros n m Hn Hm _. rewrite (Hlt1 n Hn), (Hlt1 m Hm). reflexivity.
  - intros n _. left. reflexivity.
  - intros n c _ _. rewrite Hg. split; [intros F; contradiction F; reflexivity|].
    intros _ [F | [v [[] _]]]. discriminate.
  - intros n c _ _. rewrite Hg, aget_make. split; reflexivity.
  - intros n Hn. change (φ 1) with 1%Z in Hn. lia.
  - intros n _. rewrite aget_make. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Strings: a word is read as its letter indices                       *)
(* ------------------------------------------------------------------ *)

Definition lw (w : String.string) : list Z :=
  map (fun a => (Z.of_N (Ascii.N_of_ascii a) - 97)%Z) (String.list_ascii_of_string w).

Lemma lw_length : forall w, List.length (lw w) = String.length w.
Proof. induction w as [|a w IH]; simpl; [reflexivity | rewrite <- IH; reflexivity]. Qed.

Lemma lw_get : forall w k c, String.get k w = Some c ->
  nth_error (lw w) k = Some (Z.of_N (Ascii.N_of_ascii c) - 97)%Z.
Proof.
  induction w as [|a w IH]; intros k c H; [discriminate|].
  destruct k as [|k]; simpl in H.
  - injection H as ->. reflexivity.
  - simpl. apply IH. exact H.
Qed.

Lemma ascii_Z_inj : forall a b : Ascii.ascii,
  (Z.of_N (Ascii.N_of_ascii a) - 97 = Z.of_N (Ascii.N_of_ascii b) - 97)%Z -> a = b.
Proof.
  intros a b H. rewrite <- (Ascii.ascii_N_embedding a), <- (Ascii.ascii_N_embedding b).
  f_equal. lia.
Qed.

Lemma lw_inj : forall a b, lw a = lw b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; try discriminate; [reflexivity|].
  simpl in H. injection H as H1 H2. apply ascii_Z_inj in H1. subst y.
  f_equal. apply IH. exact H2.
Qed.

Lemma NoDup_map_lw : forall l, NoDup l -> NoDup (map lw l).
Proof.
  induction l as [|a l IH]; intros H; simpl; [constructor|].
  inversion H as [|? ? Ha Hl]; subst. constructor; [|apply IH; exact Hl].
  intros Hin. apply in_map_iff in Hin as [b [Eb Hb]]. apply lw_inj in Eb. subst b.
  contradiction.
Qed.

Lemma wrep_of_repr : forall (x : PrimString.string) (w : String.string),
  repr x w -> lowercase w -> wrep x (lw w).
Proof.
  intros x w [Hl Hc] Hlow. split.
  - rewrite lw_length. symmetry. exact Hl.
  - intros i Hi. pose proof (to_Z_bounded i) as Bi.
    destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as [c [Hget Hrep]].
    unfold repr, repr_uint in Hrep.
    assert (Ei : Uint63.of_nat (Z.to_nat (φ i)) = i).
    { apply to_Z_inj. rewrite of_Z_spec. rewrite Z2Nat.id by lia. apply Z.mod_small. lia. }
    rewrite Ei in Hrep.
    pose proof (Hlow _ _ Hget) as Hc97.
    set (g := PrimString.get x i) in *.
    pose proof (to_Z_bounded g) as Bg.
    assert (Hg : (φ g) = Z.of_N (Ascii.N_of_ascii c)) by (rewrite <- Hrep; lia).
    assert (Hg97 : (φ (g - 97)) = ((φ g) - 97)%Z).
    { rewrite sub_spec. change (φ 97) with 97%Z. apply Z.mod_small. lia. }
    rewrite Hg97, Hg. split; [apply lw_get; exact Hget | lia].
Qed.

Lemma dbrep_of_repr : forall (x : array PrimString.string) (db : list String.string),
  repr x db -> Forall lowercase db -> dbrep x (map lw db).
Proof.
  intros x db [Hl Hc] Hlow. rewrite Forall_forall in Hlow. split.
  - rewrite length_map. symmetry. exact Hl.
  - intros j Hj. pose proof (to_Z_bounded j) as Bj.
    assert (Hj' : (Z.to_nat (φ j) < List.length db)%nat).
    { assert (Hj2 : ((φ j) < Z.of_nat (List.length db))%Z) by (rewrite Hl; exact Hj). lia. }
    destruct (Hc (Z.to_nat (φ j)) Hj') as [m [Hm Hrep]].
    assert (Ej : Uint63.of_nat (Z.to_nat (φ j)) = j).
    { apply to_Z_inj. rewrite of_Z_spec. rewrite Z2Nat.id by lia. apply Z.mod_small. lia. }
    rewrite Ej in Hrep.
    exists (lw m). split; [rewrite nth_error_map, Hm; reflexivity|].
    apply wrep_of_repr; [exact Hrep | apply Hlow; eapply nth_error_In; exact Hm].
Qed.

(* ------------------------------------------------------------------ *)
(* Longest common prefixes                                             *)
(* ------------------------------------------------------------------ *)

Fixpoint lcpl (a b : list Z) : nat :=
  match a, b with
  | x :: a', y :: b' => if Z.eqb x y then S (lcpl a' b') else O
  | _, _ => O
  end.

Fixpoint lcpS (a b : String.string) : nat :=
  match a, b with
  | String.String x a', String.String y b' =>
      if Ascii.ascii_dec x y then S (lcpS a' b') else O
  | _, _ => O
  end.

Lemma lcpl_lw : forall a b, lcpl (lw a) (lw b) = lcpS a b.
Proof.
  induction a as [|x a IH]; intros [|y b]; try reflexivity.
  simpl. destruct (Ascii.ascii_dec x y) as [-> | Hne].
  - rewrite Z.eqb_refl. f_equal. apply IH.
  - destruct (Z.eqb_spec (Z.of_N (Ascii.N_of_ascii x) - 97) (Z.of_N (Ascii.N_of_ascii y) - 97))
      as [E | E]; [|reflexivity].
    apply ascii_Z_inj in E. contradiction.
Qed.

Lemma starts_with_empty : forall q, starts_with String.EmptyString q -> q = String.EmptyString.
Proof. intros [|a q] [s Hs]; [reflexivity | discriminate]. Qed.

Lemma starts_with_cons : forall x a z q,
  starts_with (String.String x a) (String.String z q) -> z = x /\ starts_with a q.
Proof. intros x a z q [s Hs]. simpl in Hs. injection Hs as -> ->. split; [reflexivity | exists s; reflexivity]. Qed.

Lemma lcp_length_lcpS : forall a b, lcp_length a b (N.of_nat (lcpS a b)).
Proof.
  induction a as [|x a IH]; intros b.
  - exists String.EmptyString. split; [exists String.EmptyString; reflexivity|].
    split; [exists b; reflexivity|]. split; [reflexivity|].
    intros q Hq _. apply starts_with_empty in Hq. subst q. unfold slen. simpl. lia.
  - destruct b as [|y b].
    + exists String.EmptyString. split; [exists (String.String x a); reflexivity|].
      split; [exists String.EmptyString; reflexivity|]. split; [reflexivity|].
      intros q _ Hq. apply starts_with_empty in Hq. subst q. unfold slen. simpl. lia.
    + simpl. destruct (Ascii.ascii_dec x y) as [<- | Hne].
      * destruct (IH b) as [p [[s1 Hs1] [[s2 Hs2] [Hp Hmax]]]].
        exists (String.String x p). split; [exists s1; simpl; rewrite <- Hs1; reflexivity|].
        split; [exists s2; simpl; rewrite <- Hs2; reflexivity|].
        split; [unfold slen in *; simpl; lia|].
        intros [|z q] Hqa Hqb; [unfold slen; simpl; lia|].
        apply starts_with_cons in Hqa as [_ Hqa]. apply starts_with_cons in Hqb as [_ Hqb].
        specialize (Hmax q Hqa Hqb). unfold slen in *. simpl. lia.
      * exists String.EmptyString. split; [exists (String.String x a); reflexivity|].
        split; [exists (String.String y b); reflexivity|]. split; [reflexivity|].
        intros [|z q] Hqa Hqb; [unfold slen; simpl; lia|].
        apply starts_with_cons in Hqa as [E1 _]. apply starts_with_cons in Hqb as [E2 _].
        congruence.
Qed.

Lemma sumn_zero : forall f n, (forall l, (l < n)%nat -> f l = O) -> sumn f n = O.
Proof.
  intros f n. induction n as [|n IH]; intros H; [reflexivity|].
  simpl. rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma sumn_add : forall f g n, sumn (fun l => f l + g l)%nat n = (sumn f n + sumn g n)%nat.
Proof. intros f g n. induction n as [|n IH]; [reflexivity|]. simpl. rewrite IH. lia. Qed.

Lemma sumn_shift : forall f n, sumn f (S n) = (f O + sumn (fun l => f (S l)) n)%nat.
Proof.
  intros f n. induction n as [|n IH]; [simpl; lia|].
  change (sumn f (S (S n))) with (sumn f (S n) + f (S n))%nat. rewrite IH. simpl. lia.
Qed.

Lemma sumn_lcpl : forall q v,
  sumn (fun l => if preb (firstn (S l) q) v then 1 else 0)%nat (List.length q) = lcpl q v.
Proof.
  induction q as [|x q IH]; intros v; [reflexivity|].
  cbn [List.length]. rewrite sumn_shift.
  destruct v as [|y v].
  - simpl. apply sumn_zero. intros l _. reflexivity.
  - cbn [lcpl firstn preb]. destruct (Z.eqb x y).
    + simpl. f_equal. apply IH.
    + simpl. apply sumn_zero. intros l _. reflexivity.
Qed.

Lemma pathsum_lcp : forall W q, pathsum W q = list_sum (map (lcpl q) W).
Proof.
  induction W as [|v W IH]; intros q.
  - unfold pathsum. apply sumn_zero. intros l _. reflexivity.
  - unfold pathsum in *. simpl map. simpl list_sum. rewrite <- IH.
    rewrite <- sumn_lcpl.
    rewrite <- sumn_add. apply sumn_ext. intros l _. rewrite cntW_cons. reflexivity.
Qed.

Lemma fold_N_sum : forall {A} (g : A -> nat) l,
  fold_right N.add 0%N (map (fun x => N.of_nat (g x)) l) = N.of_nat (list_sum (map g l)).
Proof. intros A g l. induction l as [|a l IH]; [reflexivity|]. simpl. rewrite IH. lia. Qed.

Lemma Forall2_map_r : forall {A B} (R : A -> B -> Prop) (f : A -> B) l,
  (forall x, In x l -> R x (f x)) -> Forall2 R l (map f l).
Proof.
  intros A B R f l. induction l as [|a l IH]; intros H; simpl; constructor.
  - apply H. left. reflexivity.
  - apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma steps_ok : forall db w, search_steps db w (N.of_nat (ansm (map lw db) (lw w))).
Proof.
  intros db w. unfold ansm.
  assert (Hm : forall l, map (lcpl (lw w)) (map lw l) = map (lcpS w) l).
  { intros l. rewrite map_map. apply map_ext. intros a. apply lcpl_lw. }
  destruct (index_of (lw w) (map lw db)) as [k|] eqn:Ei.
  - apply index_of_some in Ei. rewrite nth_error_map in Ei.
    destruct (nth_error db k) as [w'|] eqn:Ek; [|discriminate].
    simpl in Ei. injection Ei as Ew. apply lw_inj in Ew. subst w'.
    exists (N.of_nat (S k)), (map (fun v => N.of_nat (lcpS w v)) (firstn (S k) db)).
    split; [|split].
    + left. exists (N.of_nat k). split; [rewrite Nat2N.id; exact Ek | lia].
    + rewrite Nat2N.id. apply Forall2_map_r. intros v _. apply lcp_length_lcpS.
    + rewrite fold_N_sum, pathsum_lcp, firstn_map, Hm. lia.
  - apply index_of_none in Ei.
    exists (len db), (map (fun v => N.of_nat (lcpS w v)) db).
    split; [|split].
    + right. split; [intros Hin; apply Ei; apply in_map; exact Hin | reflexivity].
    + unfold len. rewrite Nat2N.id, firstn_all. apply Forall2_map_r.
      intros v _. apply lcp_length_lcpS.
    + rewrite fold_N_sum, pathsum_lcp, Hm, length_map. unfold len. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma lengths_ok : forall l : list String.string,
  Forall (fun w => slen w < 30)%N l ->
  Forall (fun u => Z.of_nat (List.length u) < 30)%Z (map lw l).
Proof.
  intros l H. apply Forall_map. eapply Forall_impl; [|exact H].
  intros w Hw. unfold slen in Hw. rewrite lw_length. lia.
Qed.

Lemma baza_impl_correct : forall (db qs : list String.string) (x y : array PrimString.string),
  valid_input db qs -> repr x db -> repr y qs ->
  exists o : list N, repr (baza_impl x y) o /\ baza_spec db qs o.
Proof.
  intros db qs x y Hv Hx Hy.
  destruct Hv as [Hn Hq Hdl Hql Hdlo Hqlo Hnd].
  unfold len in Hn, Hq.
  set (D := map lw db). set (Qs := map lw qs).
  assert (HdbD : dbrep x D) by (apply dbrep_of_repr; assumption).
  assert (HqsQ : dbrep y Qs) by (apply dbrep_of_repr; assumption).
  assert (HDl : (Z.of_nat (List.length D) <= 30000)%Z) by (unfold D; rewrite length_map; lia).
  assert (HDu := lengths_ok db Hdl). fold D in HDu.
  assert (HQu := lengths_ok qs Hql). fold Qs in HQu.
  assert (HND : NoDup D) by (apply NoDup_map_lw; exact Hnd).
  pose proof HdbD as [HN _]. pose proof HqsQ as [HQ _].
  pose proof (sumlen_bound D HDu) as Bsl.
  assert (Htot : (φ (total x (PArray.length x) 0 0 (Zwf_well_founded 0 (gap (PArray.length x) 0))))
                 = Z.of_nat (sumlen D)).
  { rewrite (total_spec x D HdbD _ 0 0 _ eq_refl); change (φ 0) with 0%Z;
      [reflexivity | lia | rewrite wB_val; simpl skipn; lia]. }
  set (cap := 1 + total x (PArray.length x) 0 0 (Zwf_well_founded 0 (gap (PArray.length x) 0))).
  assert (Hcap : (φ cap) = (1 + Z.of_nat (sumlen D))%Z).
  { unfold cap. rewrite add_spec, Htot. change (φ 1) with 1%Z. rewrite wB_val.
    apply Z.mod_small. lia. }
  pose proof (Inv_init cap ltac:(lia)) as HI0.
  assert (Hlc : PArray.length (PArray.make cap 0) = cap) by (apply alength_make; lia).
  destruct (build_spec x D HdbD HND HDl HDu _ 0 (mk_tab cap) (PArray.make cap 0)
              (PArray.make cap 0) 1 (fun _ => [])
              (Zwf_well_founded 0 (gap (PArray.length x) 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) HI0
              ltac:(rewrite Hlc; lia) _ eq_refl)
    as [sz' [lbl' HI]].
  set (b := build x (PArray.length x) (mk_tab cap) (PArray.make cap 0) (PArray.make cap 0) 1 0
              (Zwf_well_founded 0 (gap (PArray.length x) 0))) in HI.
  assert (HQl0 : (Z.of_nat (List.length Qs) <= 30000)%Z) by (unfold Qs; rewrite length_map; lia).
  assert (HQl : PArray.length (PArray.make (PArray.length y) 0) = PArray.length y)
    by (apply alength_make; lia).
  destruct (answer_spec (b_T b) (b_cnt b) (b_end b) sz' lbl' D HI HDl y Qs (PArray.length x)
              HqsQ HQu HN _ 0 (PArray.make (PArray.length y) 0)
              (Zwf_well_founded 0 (gap (PArray.length y) 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) HQl
              ltac:(intros k' Hk'; change (φ 0) with 0%Z in Hk'; pose proof (to_Z_bounded k'); lia)
              (baza_impl x y) eq_refl)
    as [Hrl Hrc].
  exists (map (fun q => N.of_nat (ansm D (lw q))) qs).
  split.
  - assert (Hyq : (φ (PArray.length y)) = Z.of_nat (List.length qs))
      by (unfold Qs in HQ; rewrite length_map in HQ; exact HQ).
    split.
    + rewrite length_map.
      assert (E : (φ (@PArray.length@{Set} int (baza_impl x y))) = Z.of_nat (List.length qs))
        by (rewrite Hrl; exact Hyq).
      symmetry. exact E.
    + intros k Hk. rewrite length_map in Hk.
      destruct (nth_error qs k) as [q|] eqn:Eq; [| apply nth_error_None in Eq; lia].
      exists (N.of_nat (ansm D (lw q))). split; [rewrite nth_error_map, Eq; reflexivity|].
      assert (Ek : (φ (Uint63.of_nat k)) = Z.of_nat k).
      { rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia. }
      pose proof (Hrc (Uint63.of_nat k) ltac:(lia) (lw q)
                    ltac:(rewrite Ek, Nat2Z.id; unfold Qs; rewrite nth_error_map, Eq; reflexivity))
        as Hc.
      assert (Hc' : Z.to_N (φ (@PArray.get@{Set} int (baza_impl x y) (Uint63.of_nat k)))
                    = N.of_nat (ansm D (lw q)))
        by (rewrite Hc; lia).
      exact Hc'.
  - unfold baza_spec. apply Forall2_map_r. intros w _. apply steps_ok.
Qed.

Definition baza_correct : forall (db qs : list String.string) (x y : array PrimString.string),
  valid_input db qs -> repr x db -> repr y qs ->
  exists o : list N, repr (baza x y) o /\ baza_spec db qs o
  := baza_impl_correct.
