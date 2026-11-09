(* Correctness proofs for doublets_implem.v. *)
(* Implementation of doublets (doublets.spec), steering v2.

   Code.  [doublets xd xs xt] builds, once per call:
   - a word table: wl.[i] = length of word i, and a chained hash table on
     whole words (heads wb, links wn), used to find the index of a query's
     source and target words;
   - the wildcard-key index: entry e = 16 i + p stands for word i with
     position p masked (p < length of word i <= 16).  A chained hash table
     on the masked keys (heads bk, links bn; the key is hashed without being
     materialised and compared by [keq] at insertion, once) gives every
     entry a class id cls.[e], the first entry inserted with the same key;
     the entries of class c are chained from hd.[c] through cn.
   Then one BFS per query from its source word index, on int arrays only:
   distances (D, dist + 1, 0 = unvisited), parents P, queue Q, and a
   per-class mark M so that a class chain is walked at most once per query.
   No letter is read and no hash is computed during a search.  The chain is
   read back from the parent pointers into the dictionary's own strings.
   Chain pointers are stored + 1 (0 = end of chain).

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) _] proof (a gap to a bound, or a decreasing pointer). *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import String Ascii.
From Stdlib Require PrimString PString Sint63.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Require Export doublets_implem.
Open Scope uint63_scope.
Open Scope array_scope.


Notation pstring := PrimString.string.

(* ------------------------------------------------------------------ *)
(* The search                                                          *)
(* ------------------------------------------------------------------ *)

(* the search state: distances + 1, parents, queue, queue tail, class marks.
   A tuple behind a notation, not a record nor a type definition: the
   classic extraction prints a declared type's array fields malformed. *)
Notation bst := (array int * array int * array int * int * array int)%type.

(* ================================================================== *)
(* Prop side                                                           *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma len_bound : forall A (t : array A), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros A t. pose proof (leb_length A t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma len_make : forall A (n : int) (a : A),
  ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n a) = n.
Proof.
  intros A n a H. rewrite length_make.
  replace (n ≤? max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Lemma neq_Z : forall i j : int, (φ i) <> (φ j) -> i <> j.
Proof. intros i j H E. apply H. rewrite E. reflexivity. Qed.

(* get/set at the universe of the code (Set), one copy per cell type *)
Lemma gss : forall (t : array int) (i : int) (a : int),
  ((φ i) < (φ (PArray.length t)))%Z -> t.[i <- a].[i] = a.
Proof.
  intros t i a H. assert (H' : (i <? PArray.length t) = true) by (rewrite ltb_spec; exact H).
  exact (get_set_same int t i a H').
Qed.

Lemma gso : forall (t : array int) (i j : int) (a : int),
  (φ i) <> (φ j) -> t.[i <- a].[j] = t.[j].
Proof. intros t i j a H. exact (get_set_other int t i j a (neq_Z i j H)). Qed.

Lemma gmk : forall (n i a : int), (PArray.make n a).[i] = a.
Proof. intros. exact (get_make int a n i). Qed.

Lemma lset : forall (t : array int) (i a : int), PArray.length t.[i <- a] = PArray.length t.
Proof. intros. exact (length_set int t i a). Qed.

Lemma lmk : forall (n a : int), ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n a) = n.
Proof. intros. exact (len_make int n a H). Qed.

Lemma gss_s : forall (t : array pstring) (i : int) (a : pstring),
  ((φ i) < (φ (PArray.length t)))%Z -> t.[i <- a].[i] = a.
Proof.
  intros t i a H. assert (H' : (i <? PArray.length t) = true) by (rewrite ltb_spec; exact H).
  exact (get_set_same pstring t i a H').
Qed.

Lemma gso_s : forall (t : array pstring) (i j : int) (a : pstring),
  (φ i) <> (φ j) -> t.[i <- a].[j] = t.[j].
Proof. intros t i j a H. exact (get_set_other pstring t i j a (neq_Z i j H)). Qed.

Lemma gmk_s : forall (n i : int) (a : pstring), (PArray.make n a).[i] = a.
Proof. intros. exact (get_make pstring a n i). Qed.

Lemma lset_s : forall (t : array pstring) (i : int) (a : pstring),
  PArray.length t.[i <- a] = PArray.length t.
Proof. intros. exact (length_set pstring t i a). Qed.

Lemma lmk_s : forall (n : int) (a : pstring), ((φ n) <= 4194303)%Z ->
  PArray.length (PArray.make n a) = n.
Proof. intros. exact (len_make pstring n a H). Qed.

Lemma gss_o : forall (t : array (option (array pstring))) (i : int) a,
  ((φ i) < (φ (PArray.length t)))%Z -> t.[i <- a].[i] = a.
Proof.
  intros t i a H. assert (H' : (i <? PArray.length t) = true) by (rewrite ltb_spec; exact H).
  exact (get_set_same _ t i a H').
Qed.

Lemma gso_o : forall (t : array (option (array pstring))) (i j : int) a,
  (φ i) <> (φ j) -> t.[i <- a].[j] = t.[j].
Proof. intros t i j a H. exact (get_set_other _ t i j a (neq_Z i j H)). Qed.

Lemma lset_o : forall (t : array (option (array pstring))) (i : int) a,
  PArray.length t.[i <- a] = PArray.length t.
Proof. intros. exact (length_set _ t i a). Qed.

Lemma lmk_o : forall (n : int) (a : option (array pstring)), ((φ n) <= 4194303)%Z ->
  PArray.length (PArray.make n a) = n.
Proof. intros. exact (len_make _ n a H). Qed.

Lemma lsr4 : forall e : int, (φ (e >> 4)) = ((φ e) / 16)%Z.
Proof. intros e. rewrite lsr_spec. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Unfolding lemmas                                                    *)
(* ------------------------------------------------------------------ *)

Lemma hloop_eq : forall x p len j h H,
  hloop x p len j h H =
  match bdec (j <? len) with
  | left Hj =>
      hloop x p len (j + 1)
        (h * 31 + (if j =? p then 1 else PrimString.get x j + 2))
        (Acc_inv H (dec_step len j Hj))
  | right _ => h
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma kloop_eq : forall x y p len j H,
  kloop x y p len j H =
  match bdec (j <? len) with
  | left Hj =>
      if orb (j =? p) (PrimString.get x j =? PrimString.get y j)
      then kloop x y p len (j + 1) (Acc_inv H (dec_step len j Hj))
      else false
  | right _ => true
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma find_eq : forall nx test ptr H,
  find nx test ptr H =
  if ptr =? 0 then 0
  else if test (ptr - 1) then ptr
  else match bdec (nx.[ptr - 1] <? ptr) with
       | left Hl => find nx test nx.[ptr - 1] (Acc_inv H (dec_ptr _ _ Hl))
       | right _ => 0
       end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Keys                                                                *)
(* ------------------------------------------------------------------ *)

(* x and y have the same length and agree everywhere but at p *)
Definition kagree (x y : pstring) (p : int) : Prop :=
  PrimString.length x = PrimString.length y /\
  forall k, ((φ k) < (φ (PrimString.length x)))%Z -> k <> p ->
    PrimString.get x k = PrimString.get y k.

Lemma hloop_agree : forall x y p len,
  (forall k, ((φ k) < (φ len))%Z -> k <> p -> PrimString.get x k = PrimString.get y k) ->
  forall z j h H1 H2, gap len j = z ->
  hloop x p len j h H1 = hloop y p len j h H2.
Proof.
  intros x y p len Hag z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j h H1 H2 Hz.
  rewrite (hloop_eq x), (hloop_eq y).
  destruct (bdec (j <? len)) as [Hj | Hj]; [|reflexivity].
  assert (E : (if j =? p then 1 else PrimString.get x j + 2)
            = (if j =? p then 1 else PrimString.get y j + 2)).
  { destruct (j =? p) eqn:Ep; [reflexivity|].
    rewrite Uint63.eqb_false_spec in Ep. rewrite ltb_spec in Hj.
    rewrite (Hag j Hj Ep). reflexivity. }
  rewrite E. eapply IH; [| reflexivity]. rewrite <- Hz. apply dec_step. exact Hj.
Qed.

Lemma khash_agree : forall m x y p, kagree x y p -> khash m x p = khash m y p.
Proof.
  intros m x y p [Hl Hag]. unfold khash. cbv zeta. rewrite <- Hl.
  f_equal. eapply hloop_agree; [| reflexivity]. exact Hag.
Qed.

Lemma khash_bound : forall m x p, (0 < (φ m))%Z -> ((φ (khash m x p)) < (φ m))%Z.
Proof.
  intros m x p Hm. unfold khash. rewrite mod_spec.
  apply Z.mod_pos_bound. exact Hm.
Qed.

Lemma kloop_spec : forall x y p len z j H, gap len j = z ->
  kloop x y p len j H = true <->
  (forall k, ((φ j) <= (φ k) < (φ len))%Z -> k <> p -> PrimString.get x k = PrimString.get y k).
Proof.
  intros x y p len z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j H Hz. rewrite kloop_eq.
  destruct (bdec (j <? len)) as [Hj | Hj].
  - pose proof Hj as Hj'. rewrite ltb_spec in Hj'.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    destruct (orb (j =? p) (PrimString.get x j =? PrimString.get y j)) eqn:Eo.
    + rewrite (IH (gap len (j + 1))); [| rewrite <- Hz; apply dec_step; exact Hj | reflexivity].
      split.
      * intros Hk k Hk1 Hkp.
        destruct (Z.eq_dec (φ k) (φ j)) as [E | E].
        -- assert (k = j) by (apply to_Z_inj; exact E). subst k.
           apply Bool.orb_true_iff in Eo as [Eo | Eo].
           ++ rewrite Uint63.eqb_spec in Eo. contradiction.
           ++ rewrite Uint63.eqb_spec in Eo. exact Eo.
        -- apply Hk; [lia | exact Hkp].
      * intros Hk k Hk1 Hkp. apply Hk; [lia | exact Hkp].
    + split; [discriminate|].
      intros Hk. apply Bool.orb_false_iff in Eo as [E1 E2].
      rewrite Uint63.eqb_false_spec in E1, E2.
      exfalso. apply E2. apply Hk; [lia | exact E1].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hj.
    split; [intros _ k Hk; lia | reflexivity].
Qed.

Lemma keq_spec : forall x y p, keq x y p = true <-> kagree x y p.
Proof.
  intros x y p. unfold keq, kagree. cbv zeta.
  destruct (PrimString.length x =? PrimString.length y) eqn:E.
  - rewrite Uint63.eqb_spec in E.
    rewrite (kloop_spec x y p _ _ 0 _ eq_refl).
    split.
    + intros Hk. split; [exact E|]. intros k Hk1 Hkp. apply Hk; [|exact Hkp].
      change (φ 0) with 0%Z. pose proof (to_Z_bounded k). lia.
    + intros [_ Hk] k Hk1 Hkp. apply Hk; [lia | exact Hkp].
  - rewrite Uint63.eqb_false_spec in E. split; [discriminate | intros [Hl _]; contradiction].
Qed.

(* ------------------------------------------------------------------ *)
(* Chains                                                              *)
(* ------------------------------------------------------------------ *)

(* entry y is on the chain that starts at pointer ptr (pointers are + 1) *)
Inductive inchain (nx : array int) : int -> int -> Prop :=
| ic_here : forall ptr, ptr <> 0 -> inchain nx ptr (ptr - 1)
| ic_next : forall ptr y, ptr <> 0 -> inchain nx nx.[ptr - 1] y -> inchain nx ptr y.

(* links point backwards *)
Definition Dec (nx : array int) : Prop := forall x, ((φ (nx.[x])) <= (φ x))%Z.

Lemma Dec_make : forall n, Dec (PArray.make n 0).
Proof. intros n x. rewrite gmk. change (φ 0) with 0%Z. pose proof (to_Z_bounded x). lia. Qed.

Lemma Dec_set : forall nx e v, Dec nx -> ((φ e) < (φ (PArray.length nx)))%Z ->
  ((φ v) <= (φ e))%Z -> Dec nx.[e <- v].
Proof.
  intros nx e v Hd He Hv x.
  destruct (Z.eq_dec (φ e) (φ x)) as [E | E].
  - assert (e = x) by (apply to_Z_inj; exact E). subst x. rewrite gss by exact He. exact Hv.
  - rewrite gso by exact E. apply Hd.
Qed.

Lemma inchain_nz : forall nx y, ~ inchain nx 0 y.
Proof. intros nx y H. inversion H; congruence. Qed.

Lemma inchain_lt : forall nx ptr y, Dec nx -> inchain nx ptr y -> ((φ y) < (φ ptr))%Z.
Proof.
  intros nx ptr y Hd H. induction H as [ptr Hp | ptr y Hp H IH].
  - sia.
  - pose proof (Hd (ptr - 1)). sia.
Qed.

Lemma inchain_set_low : forall nx e v ptr y, Dec nx -> ((φ ptr) <= (φ e))%Z ->
  (inchain nx.[e <- v] ptr y <-> inchain nx ptr y).
Proof.
  intros nx e v ptr y Hd Hpe. split.
  - intros H. revert Hpe. induction H as [ptr Hp | ptr y Hp H IH]; intros Hpe.
    + apply ic_here. exact Hp.
    + apply ic_next; [exact Hp|].
      assert (Hne : (φ e) <> (φ (ptr - 1))) by sia.
      rewrite gso in IH by exact Hne. rewrite gso in H by exact Hne.
      apply IH. pose proof (Hd (ptr - 1)). sia.
  - intros H. revert Hpe. induction H as [ptr Hp | ptr y Hp H IH]; intros Hpe.
    + apply ic_here. exact Hp.
    + apply ic_next; [exact Hp|].
      assert (Hne : (φ e) <> (φ (ptr - 1))) by sia.
      rewrite gso by exact Hne.
      apply IH. pose proof (Hd (ptr - 1)). sia.
Qed.

Lemma inchain_push : forall nx e v y, Dec nx ->
  ((φ e) < (φ (PArray.length nx)))%Z -> ((φ v) <= (φ e))%Z ->
  (inchain nx.[e <- v] (e + 1) y <-> y = e \/ inchain nx v y).
Proof.
  intros nx e v y Hd He Hv.
  pose proof (len_bound _ nx) as Hlb.
  assert (E1 : e + 1 - 1 = e) by sia.
  assert (Hnz : e + 1 <> 0) by sia.
  split.
  - intros H. inversion H as [ptr Hp Eq | ptr y' Hp H' Eq]; subst.
    + left. exact E1.
    + right. rewrite E1, gss in H' by exact He.
      rewrite inchain_set_low in H' by (exact Hd || lia). exact H'.
  - intros [-> | H].
    + pose proof (ic_here nx.[e <- v] (e + 1) Hnz) as Hh. rewrite E1 in Hh. exact Hh.
    + apply ic_next; [exact Hnz|]. rewrite E1, gss by exact He.
      rewrite inchain_set_low by (exact Hd || lia). exact H.
Qed.

Lemma find_spec : forall nx test, Dec nx -> forall z ptr H, (φ ptr) = z ->
  (find nx test ptr H = 0 /\ forall y, inchain nx ptr y -> test y = false) \/
  (find nx test ptr H <> 0 /\ inchain nx ptr (find nx test ptr H - 1) /\
   test (find nx test ptr H - 1) = true).
Proof.
  intros nx test Hd z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros ptr H Hz. rewrite find_eq.
  destruct (ptr =? 0) eqn:E0.
  - rewrite Uint63.eqb_spec in E0. subst ptr. left. split; [reflexivity|].
    intros y Hy. exfalso. exact (inchain_nz _ _ Hy).
  - rewrite Uint63.eqb_false_spec in E0.
    destruct (test (ptr - 1)) eqn:Et.
    + right. split; [exact E0|]. split; [apply ic_here; exact E0 | exact Et].
    + destruct (bdec (nx.[ptr - 1] <? ptr)) as [Hl | Hl].
      * destruct (IH (φ (nx.[ptr - 1])) ltac:(rewrite <- Hz; apply dec_ptr; exact Hl)
                    _ (Acc_inv H (dec_ptr _ _ Hl)) eq_refl)
          as [[R1 R2] | [R1 [R2 R3]]].
        -- left. split; [exact R1|]. intros y Hy.
           inversion Hy as [p0 Hp Eq | p0 y' Hp H' Eq]; subst.
           ++ exact Et.
           ++ apply R2. exact H'.
        -- right. split; [exact R1|]. split; [|exact R3].
           apply ic_next; [exact E0 | exact R2].
      * exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hl.
        pose proof (Hd (ptr - 1)). apply Hl. sia.
Qed.

(* ------------------------------------------------------------------ *)
(* The word table                                                      *)
(* ------------------------------------------------------------------ *)

Lemma wbuild_eq : forall xd n i wl wb wn H,
  wbuild xd n i wl wb wn H =
  match bdec (i <? n) with
  | left Hi =>
      let w := xd.[i] in
      let h := khash M_word w (PrimString.length w) in
      let old := wb.[h] in
      wbuild xd n (i + 1) wl.[i <- PrimString.length w] wb.[h <- i + 1]
        wn.[i <- old] (Acc_inv H (dec_step n i Hi))
  | right _ => (wl, wb, wn)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition wh (x : pstring) : int := khash M_word x (PrimString.length x).

Lemma wh_bound : forall x, ((φ (wh x)) < 65536)%Z.
Proof. intros x. apply (khash_bound M_word). reflexivity. Qed.

Definition WInv (xd : array pstring) (i : int) (wl wb wn : array int) : Prop :=
  PArray.length wl = PArray.length xd /\ PArray.length wb = M_word /\
  PArray.length wn = PArray.length xd /\ Dec wn /\
  (forall h, ((φ (wb.[h])) <= (φ i))%Z) /\
  (forall y, ((φ y) < (φ i))%Z ->
     wl.[y] = PrimString.length xd.[y] /\ inchain wn wb.[wh xd.[y]] y).

Lemma wbuild_spec : forall xd z i wl wb wn H,
  gap (PArray.length xd) i = z -> ((φ i) <= (φ (PArray.length xd)))%Z ->
  WInv xd i wl wb wn ->
  let r := wbuild xd (PArray.length xd) i wl wb wn H in
  WInv xd (PArray.length xd) (fst (fst r)) (snd (fst r)) (snd r).
Proof.
  intros xd z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i wl wb wn H Hz Hi Hinv. cbv zeta. rewrite wbuild_eq.
  destruct (bdec (i <? PArray.length xd)) as [Hlt | Hge].
  - cbv zeta. pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    destruct Hinv as (L1 & L2 & L3 & Hd & Hb & Hc).
    set (h := khash M_word xd.[i] (PrimString.length xd.[i])).
    assert (Hh : ((φ h) < (φ (PArray.length wb)))%Z)
      by (rewrite L2; apply (wh_bound xd.[i])).
    apply IH with (y := gap (PArray.length xd) (i + 1));
      [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | lia |].
    split; [rewrite lset; exact L1|].
    split; [rewrite lset; exact L2|].
    split; [rewrite lset; exact L3|].
    split; [apply Dec_set; [exact Hd | lia | apply Hb]|].
    split.
    + intros h'. destruct (Z.eq_dec (φ h) (φ h')) as [E | E].
      * assert (h = h') by (apply to_Z_inj; exact E). subst h'.
        rewrite gss by exact Hh. lia.
      * rewrite gso by exact E. pose proof (Hb h'). lia.
    + intros y Hy. rewrite Hi1 in Hy.
      destruct (Z.eq_dec (φ y) (φ i)) as [Ey | Ey].
      * assert (y = i) by (apply to_Z_inj; exact Ey). subst y.
        split; [rewrite gss by lia; reflexivity|].
        fold (wh xd.[i]). fold h. rewrite gss by exact Hh.
        rewrite inchain_push by (exact Hd || lia || apply Hb). left. reflexivity.
      * destruct (Hc y ltac:(lia)) as [Hc1 Hc2].
        split; [rewrite gso by lia; exact Hc1|].
        destruct (Z.eq_dec (φ h) (φ (wh xd.[y]))) as [E | E].
        -- assert (Eh : wh xd.[y] = h) by (apply to_Z_inj; symmetry; exact E).
           rewrite Eh in Hc2 |- *. rewrite gss by exact Hh.
           rewrite inchain_push by (exact Hd || lia || apply Hb). right. exact Hc2.
        -- rewrite gso by exact E.
           rewrite inchain_set_low by (exact Hd || apply Hb). exact Hc2.
  - simpl. rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
    replace (PArray.length xd) with i at 1 by (apply to_Z_inj; lia). exact Hinv.
Qed.

Lemma lookup_spec : forall xd wl wb wn q,
  WInv xd (PArray.length xd) wl wb wn ->
  (lookup xd wb wn q = 0 /\
     forall y, ((φ y) < (φ (PArray.length xd)))%Z -> xd.[y] <> q) \/
  (lookup xd wb wn q <> 0 /\
     ((φ (lookup xd wb wn q - 1)) < (φ (PArray.length xd)))%Z /\
     xd.[lookup xd wb wn q - 1] = q).
Proof.
  intros xd wl wb wn q (L1 & L2 & L3 & Hd & Hb & Hc).
  unfold lookup. cbv zeta.
  destruct (find_spec wn (wtest xd q) Hd _ wb.[khash M_word q (PrimString.length q)]
              (Zwf_well_founded 0 _) eq_refl) as [[R1 R2] | [R1 [R2 R3]]].
  - left. split; [exact R1|]. intros y Hy E.
    destruct (Hc y Hy) as [_ Hc2]. rewrite E in Hc2. unfold wh in Hc2.
    pose proof (R2 y Hc2) as F. unfold wtest in F. rewrite E in F.
    rewrite PString.compare_refl in F. discriminate.
  - right. split; [exact R1|].
    pose proof (inchain_lt _ _ _ Hd R2) as Hlt.
    split; [pose proof (Hb (khash M_word q (PrimString.length q))); lia|].
    unfold wtest in R3. destruct (PrimString.compare _ q) eqn:Ec; try discriminate.
    apply PString.compare_eq. exact Ec.
Qed.

(* ------------------------------------------------------------------ *)
(* The wildcard-key classes                                            *)
(* ------------------------------------------------------------------ *)

Lemma build_eq : forall xd N16 e cls bk bn hd cn H,
  build xd N16 e cls bk bn hd cn H =
  match bdec (e <? N16) with
  | left He =>
      let w := xd.[e >> 4] in
      let p := e mod 16 in
      if p <? PrimString.length w then
        let h := khash M_key w p in
        let old := bk.[h] in
        let r := find bn (ktest xd w p) old (Zwf_well_founded 0 (φ old)) in
        let c := if r =? 0 then e else cls.[r - 1] in
        let oldc := hd.[c] in
        build xd N16 (e + 1) cls.[e <- c] bk.[h <- e + 1] bn.[e <- old]
          hd.[c <- e + 1] cn.[e <- oldc] (Acc_inv H (dec_step N16 e He))
      else build xd N16 (e + 1) cls bk bn hd cn (Acc_inv H (dec_step N16 e He))
  | right _ => (cls, hd, cn)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Section Classes.

Variable xd : array pstring.

Definition N16 : int := PArray.length xd * 16.

(* entry y is word y / 16 with position y mod 16 masked *)
Definition valid (y : int) : Prop :=
  ((φ y) < (φ N16))%Z /\ ((φ (y mod 16)) < (φ (PrimString.length xd.[y >> 4])))%Z.

Definition keyeq (y y' : int) : Prop :=
  y mod 16 = y' mod 16 /\ kagree xd.[y >> 4] xd.[y' >> 4] (y mod 16).

Definition kh (y : int) : int := khash M_key xd.[y >> 4] (y mod 16).

Lemma kagree_refl : forall x p, kagree x x p.
Proof. intros x p. split; [reflexivity | intros; reflexivity]. Qed.

Lemma kagree_sym : forall x y p, kagree x y p -> kagree y x p.
Proof.
  intros x y p [Hl Hk]. split; [symmetry; exact Hl|].
  intros k Hk1 Hkp. symmetry. apply Hk; [rewrite Hl; exact Hk1 | exact Hkp].
Qed.

Lemma kagree_trans : forall x y w p, kagree x y p -> kagree y w p -> kagree x w p.
Proof.
  intros x y w p [Hl1 Hk1] [Hl2 Hk2]. split; [congruence|].
  intros k Hk Hkp. rewrite (Hk1 k Hk Hkp). apply Hk2; [rewrite <- Hl1; exact Hk | exact Hkp].
Qed.

Lemma keyeq_refl : forall y, keyeq y y.
Proof. intros y. split; [reflexivity | apply kagree_refl]. Qed.

Lemma keyeq_sym : forall y y', keyeq y y' -> keyeq y' y.
Proof.
  intros y y' [Hp Hk]. split; [symmetry; exact Hp|]. rewrite <- Hp. apply kagree_sym. exact Hk.
Qed.

Lemma keyeq_trans : forall y y' y'', keyeq y y' -> keyeq y' y'' -> keyeq y y''.
Proof.
  intros y y' y'' [Hp1 Hk1] [Hp2 Hk2]. split; [congruence|].
  eapply kagree_trans; [exact Hk1|]. rewrite Hp1. exact Hk2.
Qed.

Lemma keyeq_kh : forall y y', keyeq y y' -> kh y = kh y'.
Proof.
  intros y y' [Hp Hk]. unfold kh. rewrite (khash_agree _ _ _ _ Hk). rewrite Hp. reflexivity.
Qed.

Lemma ktest_spec : forall w p y,
  ktest xd w p y = true <-> y mod 16 = p /\ kagree xd.[y >> 4] w p.
Proof.
  intros w p y. unfold ktest. rewrite Bool.andb_true_iff, Uint63.eqb_spec, keq_spec.
  reflexivity.
Qed.

Definition BInv (e : int) (cls bk bn hd cn : array int) : Prop :=
  PArray.length cls = N16 /\ PArray.length bk = M_key /\
  PArray.length bn = N16 /\ PArray.length hd = N16 /\ PArray.length cn = N16 /\
  Dec bn /\ Dec cn /\
  (forall h, ((φ (bk.[h])) <= (φ e))%Z) /\ (forall c, ((φ (hd.[c])) <= (φ e))%Z) /\
  (forall y, valid y -> ((φ y) < (φ e))%Z -> inchain bn bk.[kh y] y) /\
  (forall y, valid y -> ((φ y) < (φ e))%Z -> ((φ (cls.[y])) <= (φ y))%Z) /\
  (forall y y', valid y -> ((φ y) < (φ e))%Z -> valid y' -> ((φ y') < (φ e))%Z ->
     (cls.[y] = cls.[y'] <-> keyeq y y')) /\
  (forall c y, inchain cn hd.[c] y <-> (valid y /\ ((φ y) < (φ e))%Z /\ cls.[y] = c)).

Hypothesis Hn : ((φ (PArray.length xd)) <= 25143)%Z.

Lemma N16_val : (φ N16) = ((φ (PArray.length xd)) * 16)%Z.
Proof. unfold N16. pose proof (to_Z_bounded (PArray.length xd)). sia. Qed.

(* one valid entry e joins class c *)
Lemma binv_step : forall e cls bk bn hd cn c,
  BInv e cls bk bn hd cn -> valid e ->
  ((φ c) <= (φ e))%Z ->
  (forall y, valid y -> ((φ y) < (φ e))%Z -> (cls.[y] = c <-> keyeq y e)) ->
  BInv (e + 1) cls.[e <- c] bk.[kh e <- e + 1] bn.[e <- bk.[kh e]]
       hd.[c <- e + 1] cn.[e <- hd.[c]].
Proof.
  intros e cls bk bn hd cn c
    (L1 & L2 & L3 & L4 & L5 & Dbn & Dcn & Bbk & Bhd & Cbk & Bcl & Ecl & Chd) Hv Hc K.
  pose proof N16_val as HN.
  assert (He : ((φ e) < (φ N16))%Z) by (destruct Hv; lia).
  assert (Hi1 : (φ (e + 1)) = ((φ e) + 1)%Z) by sia.
  assert (Hkh : ((φ (kh e)) < (φ (PArray.length bk)))%Z)
    by (rewrite L2; apply khash_bound; reflexivity).
  assert (HeN : forall t : array int, PArray.length t = N16 -> ((φ e) < (φ (PArray.length t)))%Z)
    by (intros t Ht; rewrite Ht; exact He).
  assert (HcN : ((φ c) < (φ (PArray.length hd)))%Z) by (rewrite L4; lia).
  split; [rewrite lset; exact L1|]. split; [rewrite lset; exact L2|].
  split; [rewrite lset; exact L3|]. split; [rewrite lset; exact L4|].
  split; [rewrite lset; exact L5|].
  split; [apply Dec_set; [exact Dbn | apply HeN; exact L3 | apply Bbk]|].
  split; [apply Dec_set; [exact Dcn | apply HeN; exact L5 | apply Bhd]|].
  split.
  { intros h. destruct (Z.eq_dec (φ (kh e)) (φ h)) as [E | E].
    - assert (kh e = h) by (apply to_Z_inj; exact E). subst h. rewrite gss by exact Hkh. lia.
    - rewrite gso by exact E. pose proof (Bbk h). lia. }
  split.
  { intros c'. destruct (Z.eq_dec (φ c) (φ c')) as [E | E].
    - assert (c = c') by (apply to_Z_inj; exact E). subst c'. rewrite gss by exact HcN. lia.
    - rewrite gso by exact E. pose proof (Bhd c'). lia. }
  split.
  { intros y Hy Hye. rewrite Hi1 in Hye.
    destruct (Z.eq_dec (φ (kh e)) (φ (kh y))) as [E | E].
    - assert (Eh : kh y = kh e) by (apply to_Z_inj; symmetry; exact E).
      rewrite Eh. rewrite gss by exact Hkh.
      rewrite inchain_push by first [exact Dbn | (apply HeN; exact L3) | apply Bbk].
      destruct (Z.eq_dec (φ y) (φ e)) as [Ey | Ey].
      + left. apply to_Z_inj. exact Ey.
      + right. rewrite <- Eh. apply Cbk; [exact Hy | lia].
    - rewrite gso by exact E.
      rewrite inchain_set_low by (exact Dbn || apply Bbk).
      destruct (Z.eq_dec (φ y) (φ e)) as [Ey | Ey].
      + exfalso. apply E. assert (y = e) by (apply to_Z_inj; exact Ey). subst y. reflexivity.
      + apply Cbk; [exact Hy | lia]. }
  split.
  { intros y Hy Hye. rewrite Hi1 in Hye.
    destruct (Z.eq_dec (φ e) (φ y)) as [Ey | Ey].
    - assert (e = y) by (apply to_Z_inj; exact Ey). subst y.
      rewrite gss by (apply HeN; exact L1). exact Hc.
    - rewrite gso by exact Ey. apply Bcl; [exact Hy | lia]. }
  split.
  { intros y y' Hy Hye Hy' Hye'. rewrite Hi1 in Hye, Hye'.
    destruct (Z.eq_dec (φ e) (φ y)) as [Ey | Ey];
    destruct (Z.eq_dec (φ e) (φ y')) as [Ey' | Ey'].
    - assert (e = y) by (apply to_Z_inj; exact Ey).
      assert (e = y') by (apply to_Z_inj; exact Ey'). subst y y'.
      split; intros; [apply keyeq_refl | reflexivity].
    - assert (e = y) by (apply to_Z_inj; exact Ey). subst y.
      rewrite gss by (apply HeN; exact L1). rewrite gso by exact Ey'.
      split.
      + intros Hcy. apply keyeq_sym. apply K; [exact Hy' | lia | symmetry; exact Hcy].
      + intros Hk. symmetry. apply K; [exact Hy' | lia | apply keyeq_sym; exact Hk].
    - assert (e = y') by (apply to_Z_inj; exact Ey'). subst y'.
      rewrite gss by (apply HeN; exact L1). rewrite gso by exact Ey.
      apply K; [exact Hy | lia].
    - rewrite !gso by assumption. apply Ecl; [exact Hy | lia | exact Hy' | lia]. }
  { intros c' y.
    destruct (Z.eq_dec (φ c) (φ c')) as [E | E].
    - assert (c = c') by (apply to_Z_inj; exact E). subst c'.
      rewrite gss by exact HcN.
      rewrite inchain_push by first [exact Dcn | (apply HeN; exact L5) | apply Bhd].
      rewrite Chd. rewrite Hi1.
      split.
      + intros [-> | (Hy & Hye & Hcy)].
        * split; [exact Hv|]. split; [lia|]. rewrite gss by (apply HeN; exact L1). reflexivity.
        * split; [exact Hy|]. split; [lia|]. rewrite gso by lia. exact Hcy.
      + intros (Hy & Hye & Hcy).
        destruct (Z.eq_dec (φ e) (φ y)) as [Ey | Ey].
        * left. apply to_Z_inj. symmetry. exact Ey.
        * right. rewrite gso in Hcy by exact Ey. split; [exact Hy|]. split; [lia | exact Hcy].
    - rewrite gso by exact E.
      rewrite inchain_set_low by (exact Dcn || apply Bhd).
      rewrite Chd. rewrite Hi1.
      split.
      + intros (Hy & Hye & Hcy). split; [exact Hy|]. split; [lia|]. rewrite gso by lia. exact Hcy.
      + intros (Hy & Hye & Hcy).
        destruct (Z.eq_dec (φ e) (φ y)) as [Ey | Ey].
        * assert (e = y) by (apply to_Z_inj; exact Ey). subst y.
          rewrite gss in Hcy by (apply HeN; exact L1). subst c'. exfalso; apply E; reflexivity.
        * rewrite gso in Hcy by exact Ey. split; [exact Hy|]. split; [lia | exact Hcy]. }
Qed.

End Classes.

Definition FInv (xd : array pstring) (cls hd cn : array int) : Prop :=
  PArray.length cls = N16 xd /\ PArray.length hd = N16 xd /\ Dec cn /\
  (forall y, valid xd y -> ((φ (cls.[y])) <= (φ y))%Z) /\
  (forall y y', valid xd y -> valid xd y' -> (cls.[y] = cls.[y'] <-> keyeq xd y y')) /\
  (forall c y, inchain cn hd.[c] y <-> (valid xd y /\ cls.[y] = c)).

Lemma binv_skip : forall xd e cls bk bn hd cn,
  ((φ (PArray.length xd)) <= 25143)%Z ->
  BInv xd e cls bk bn hd cn -> ~ valid xd e -> ((φ e) < (φ (N16 xd)))%Z ->
  BInv xd (e + 1) cls bk bn hd cn.
Proof.
  intros xd e cls bk bn hd cn Hn
    (L1 & L2 & L3 & L4 & L5 & Dbn & Dcn & Bbk & Bhd & Cbk & Bcl & Ecl & Chd) Hv HeN.
  pose proof (N16_val xd Hn).
  assert (Hi1 : (φ (e + 1)) = ((φ e) + 1)%Z) by sia.
  assert (Hlt : forall y, valid xd y -> ((φ y) < (φ (e + 1)))%Z -> ((φ y) < (φ e))%Z).
  { intros y Hy Hye. destruct (Z.eq_dec (φ y) (φ e)) as [E | E].
    - assert (y = e) by (apply to_Z_inj; exact E). subst y. contradiction.
    - lia. }
  do 7 (split; [assumption|]).
  split; [intros h; pose proof (Bbk h); lia|].
  split; [intros c; pose proof (Bhd c); lia|].
  split; [intros y Hy Hye; apply Cbk; [exact Hy | apply Hlt; assumption]|].
  split; [intros y Hy Hye; apply Bcl; [exact Hy | apply Hlt; assumption]|].
  split; [intros y y' Hy Hye Hy' Hye'; apply Ecl; [exact Hy | apply Hlt; assumption
                                                  | exact Hy' | apply Hlt; assumption]|].
  intros c y. rewrite Chd. split.
  - intros (Hy & Hye & Hc). split; [exact Hy|]. split; [lia | exact Hc].
  - intros (Hy & Hye & Hc). split; [exact Hy|]. split; [apply Hlt; assumption | exact Hc].
Qed.

Lemma build_spec : forall xd, ((φ (PArray.length xd)) <= 25143)%Z ->
  forall z e cls bk bn hd cn H, gap (N16 xd) e = z -> ((φ e) <= (φ (N16 xd)))%Z ->
  BInv xd e cls bk bn hd cn ->
  let r := build xd (N16 xd) e cls bk bn hd cn H in
  FInv xd (fst (fst r)) (snd (fst r)) (snd r).
Proof.
  intros xd Hn z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros e cls bk bn hd cn H Hz Hle Hinv. cbv zeta. rewrite build_eq.
  destruct (bdec (e <? N16 xd)) as [Hlt | Hge].
  - cbv zeta. pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (IH' : forall cls bk bn hd cn H',
              BInv xd (e + 1) cls bk bn hd cn ->
              FInv xd (fst (fst (build xd (N16 xd) (e + 1) cls bk bn hd cn H')))
                (snd (fst (build xd (N16 xd) (e + 1) cls bk bn hd cn H')))
                (snd (build xd (N16 xd) (e + 1) cls bk bn hd cn H'))).
    { intros. eapply IH; [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | sia | assumption]. }
    destruct (e mod 16 <? PrimString.length xd.[e >> 4]) eqn:Ev.
    + rewrite ltb_spec in Ev.
      assert (Hv : valid xd e) by (split; assumption).
      fold (kh xd e).
      pose proof Hinv as (L1 & L2 & L3 & L4 & L5 & Dbn & Dcn & Bbk & Bhd & Cbk & Bcl & Ecl & Chd).
      destruct (find_spec bn (ktest xd xd.[e >> 4] (e mod 16)) Dbn _ bk.[kh xd e]
                  (Zwf_well_founded 0 _) eq_refl) as [[R1 R2] | [R1 [R2 R3]]].
      * rewrite R1. simpl. apply IH'. apply binv_step; [exact Hn | exact Hinv | exact Hv | lia |].
        intros y Hy Hye. split.
        -- intros Hc. pose proof (Bcl y Hy Hye). rewrite Hc in H0. lia.
        -- intros Hk. exfalso.
           pose proof (Cbk y Hy Hye) as Hc. rewrite (keyeq_kh xd y e Hk) in Hc.
           pose proof (R2 y Hc) as F. rewrite <- Bool.not_true_iff_false in F. apply F.
           apply ktest_spec. destruct Hk as [Hp Hk]. split; [exact Hp|]. rewrite <- Hp. exact Hk.
      * assert (E : (find bn (ktest xd xd.[e >> 4] (e mod 16)) bk.[kh xd e]
                       (Zwf_well_founded 0 (φ (bk.[kh xd e]))) =? 0) = false)
          by (rewrite Uint63.eqb_false_spec; exact R1).
        rewrite E.
        set (y0 := find bn _ _ _ - 1) in *.
        pose proof (inchain_lt _ _ _ Dbn R2) as Hy0. pose proof (Bbk (kh xd e)).
        apply ktest_spec in R3. destruct R3 as [Hp0 Hk0].
        assert (Hv0 : valid xd y0).
        { split; [lia|]. destruct Hk0 as [Hl0 _]. rewrite Hl0, Hp0. exact Ev. }
        assert (Hke : keyeq xd y0 e) by (split; [exact Hp0 | rewrite Hp0; exact Hk0]).
        apply IH'. apply binv_step; [exact Hn | exact Hinv | exact Hv | pose proof (Bcl y0 Hv0 ltac:(lia)); lia |].
        intros y Hy Hye. rewrite (Ecl y y0 Hy Hye Hv0 ltac:(lia)). split.
        -- intros Hk. eapply keyeq_trans; [exact Hk | exact Hke].
        -- intros Hk. eapply keyeq_trans; [exact Hk | apply keyeq_sym; exact Hke].
    + apply IH'. apply binv_skip; [exact Hn | exact Hinv | | exact Hlt'].
      intros [_ Hv]. rewrite <- Bool.not_true_iff_false, ltb_spec in Ev. contradiction.
  - simpl. rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
    assert (Ee : e = N16 xd) by (apply to_Z_inj; lia). subst e.
    destruct Hinv as (L1 & L2 & L3 & L4 & L5 & Dbn & Dcn & Bbk & Bhd & Cbk & Bcl & Ecl & Chd).
    split; [exact L1|]. split; [exact L4|]. split; [exact Dcn|].
    split; [intros y Hy; apply Bcl; [exact Hy | apply Hy]|].
    split; [intros y y' Hy Hy'; apply Ecl; [exact Hy | apply Hy | exact Hy' | apply Hy']|].
    intros c y. rewrite Chd. split.
    + intros (Hy & _ & Hc). split; assumption.
    + intros (Hy & Hc). split; [exact Hy|]. split; [apply Hy | exact Hc].
Qed.


(* ------------------------------------------------------------------ *)
(* The search                                                          *)
(* ------------------------------------------------------------------ *)

(* x and y are equal or a doublet: they agree everywhere but at some p *)
Definition msim (x y : pstring) : Prop :=
  exists p, ((φ p) < (φ (PrimString.length x)))%Z /\ kagree x y p.

Section Search.

Variables (xd : array pstring) (cls hd cn wl : array int) (s0 : int).

Local Notation n := (PArray.length xd).

Hypothesis Hn : ((φ n) <= 25143)%Z.
Hypothesis Hlen : forall i, ((φ i) < (φ n))%Z -> (1 <= (φ (PrimString.length xd.[i])) <= 16)%Z.
Hypothesis Hwl : forall i, ((φ i) < (φ n))%Z -> wl.[i] = PrimString.length xd.[i].
Hypothesis Hfi : FInv xd cls hd cn.
Hypothesis Hs0 : ((φ s0) < (φ n))%Z.

(* v is reached from s0 by k doublet-or-equal steps between dictionary words *)
Inductive ri : int -> nat -> Prop :=
| ri0 : ri s0 0
| riS : forall u v k, ri u k -> ((φ v) < (φ n))%Z -> msim xd.[u] xd.[v] -> ri v (S k).

Definition vis (s : bst) (v : int) : Prop := (sD s).[v] <> 0.
Definition dist (s : bst) (v : int) : Z := ((φ ((sD s).[v])) - 1)%Z.

Record Inv (s : bst) (qh : int) : Prop := {
  i_lD : PArray.length (sD s) = n;
  i_lP : PArray.length (sP s) = n;
  i_lQ : PArray.length (sQ s) = n;
  i_lM : PArray.length (sM s) = N16 xd;
  i_qh : ((φ qh) <= (φ (sT s)))%Z;
  i_T : ((φ (sT s)) <= (φ n))%Z;
  i_Qv : forall j, ((φ j) < (φ (sT s)))%Z -> ((φ ((sQ s).[j])) < (φ n))%Z /\ vis s (sQ s).[j];
  i_vQ : forall v, ((φ v) < (φ n))%Z -> vis s v ->
           exists j, ((φ j) < (φ (sT s)))%Z /\ (sQ s).[j] = v;
  i_Qd : forall j1 j2, ((φ j1) < (φ (sT s)))%Z -> ((φ j2) < (φ (sT s)))%Z ->
           (sQ s).[j1] = (sQ s).[j2] -> j1 = j2;
  i_s0 : (sD s).[s0] = 1;
  i_Db : forall v, ((φ v) < (φ n))%Z -> ((φ ((sD s).[v])) <= (φ (sT s)))%Z;
  i_par : forall v, ((φ v) < (φ n))%Z -> vis s v ->
           ((φ ((sD s).[v])) = 1%Z -> v = s0) /\
           ((1 < (φ ((sD s).[v])))%Z ->
              ((φ ((sP s).[v])) < (φ n))%Z /\ vis s (sP s).[v] /\
              ((φ ((sD s).[(sP s).[v]])) + 1 = (φ ((sD s).[v])))%Z /\
              msim xd.[(sP s).[v]] xd.[v]);
  i_opt : forall v, ((φ v) < (φ n))%Z -> vis s v -> forall k, ri v k -> (dist s v <= Z.of_nat k)%Z;
  i_mono : forall j1 j2, ((φ j1) <= (φ j2))%Z -> ((φ j2) < (φ (sT s)))%Z ->
           (dist s (sQ s).[j1] <= dist s (sQ s).[j2])%Z;
  i_spread : ((φ qh) < (φ (sT s)))%Z -> forall j, ((φ j) < (φ (sT s)))%Z ->
           (dist s (sQ s).[j] <= dist s (sQ s).[qh] + 1)%Z;
  i_mark : forall c, (sM s).[c] <> 0 -> forall y, valid xd y -> cls.[y] = c -> vis s (y >> 4);
  i_proc : forall j, ((φ j) < (φ qh))%Z -> forall p,
           ((φ p) < (φ (PrimString.length xd.[(sQ s).[j]])))%Z ->
           (sM s).[cls.[(sQ s).[j] * 16 + p]] <> 0
}.

Definition mono (s s' : bst) : Prop :=
  ((φ (sT s)) <= (φ (sT s')))%Z /\
  (forall j, ((φ j) < (φ (sT s)))%Z -> (sQ s').[j] = (sQ s).[j]) /\
  (forall v, ((φ v) < (φ n))%Z -> vis s v -> (sD s').[v] = (sD s).[v]) /\
  (forall c, (sM s).[c] <> 0 -> (sM s').[c] <> 0).

Lemma mono_refl : forall s, mono s s.
Proof. intros s. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. auto. Qed.

Lemma mono_trans : forall s1 s2 s3, mono s1 s2 -> mono s2 s3 -> mono s1 s3.
Proof.
  intros s1 s2 s3 (A1 & B1 & C1 & D1) (A2 & B2 & C2 & D2).
  split; [lia|]. split; [intros j Hj; rewrite B2 by lia; apply B1; exact Hj|].
  split; [|auto].
  intros v Hv Hvis. rewrite C2; [apply C1; assumption | exact Hv |].
  unfold vis in *. rewrite C1; assumption.
Qed.

Lemma mono_vis : forall s s' v, mono s s' -> ((φ v) < (φ n))%Z -> vis s v -> vis s' v.
Proof. intros s s' v (_ & _ & C & _) Hv Hvis. unfold vis in *. rewrite C; assumption. Qed.

(* entries *)
Lemma ent_word : forall u p, ((φ u) < (φ n))%Z -> (0 <= (φ p) < 16)%Z ->
  (u * 16 + p) >> 4 = u.
Proof. intros u p Hu Hp. apply to_Z_inj. rewrite lsr4. sia. Qed.

Lemma ent_pos : forall u p, ((φ u) < (φ n))%Z -> (0 <= (φ p) < 16)%Z ->
  (u * 16 + p) mod 16 = p.
Proof. intros u p Hu Hp. apply to_Z_inj. sia. Qed.

Lemma ent_valid : forall u p, ((φ u) < (φ n))%Z ->
  ((φ p) < (φ (PrimString.length xd.[u])))%Z -> valid xd (u * 16 + p).
Proof.
  intros u p Hu Hp. pose proof (Hlen u Hu). pose proof (to_Z_bounded p).
  pose proof (N16_val xd Hn).
  split.
  - sia.
  - rewrite ent_pos, ent_word by lia. exact Hp.
Qed.

Lemma valid_word : forall y, valid xd y -> ((φ (y >> 4)) < (φ n))%Z.
Proof.
  intros y [Hy _]. rewrite lsr4. pose proof (N16_val xd Hn). pose proof (to_Z_bounded y).
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma valid_keyeq_msim : forall u p y, ((φ u) < (φ n))%Z ->
  ((φ p) < (φ (PrimString.length xd.[u])))%Z -> valid xd y ->
  keyeq xd (u * 16 + p) y -> msim xd.[u] xd.[y >> 4].
Proof.
  intros u p y Hu Hp Hy [Hm Hk]. pose proof (Hlen u Hu). pose proof (to_Z_bounded y).
  rewrite ent_word, ent_pos in Hk by lia. exists p. split; [exact Hp | exact Hk].
Qed.

Lemma vis_pos : forall s v, vis s v -> (1 <= (φ ((sD s).[v])))%Z.
Proof.
  intros s v H. unfold vis in H. pose proof (to_Z_bounded ((sD s).[v])).
  assert ((φ ((sD s).[v])) <> 0%Z) by (intro E; apply H; apply to_Z_inj; exact E). lia.
Qed.

Lemma vis_dec : forall s v, {vis s v} + {~ vis s v}.
Proof.
  intros s v. unfold vis. destruct ((sD s).[v] =? 0) eqn:E.
  - right. rewrite Uint63.eqb_spec in E. intro F. apply F. exact E.
  - left. rewrite Uint63.eqb_false_spec in E. exact E.
Defined.

Lemma ri_lt : forall v k, ri v k -> ((φ v) < (φ n))%Z.
Proof. intros v k H. destruct H; assumption. Qed.

(* every word adjacent to a processed node is visited *)
Lemma closure : forall s qh, Inv s qh -> forall j, ((φ j) < (φ qh))%Z ->
  forall v, ((φ v) < (φ n))%Z -> msim xd.[(sQ s).[j]] xd.[v] -> vis s v.
Proof.
  intros s qh Hi j Hj v Hv (p & Hp & Hk).
  set (u := (sQ s).[j]) in *.
  assert (Hu : ((φ u) < (φ n))%Z) by (apply (i_Qv _ _ Hi); pose proof (i_qh _ _ Hi); lia).
  pose proof (Hlen u Hu). pose proof (to_Z_bounded p).
  destruct Hfi as (F1 & F2 & F3 & F4 & F5 & F6).
  assert (Vu : valid xd (u * 16 + p)) by (apply ent_valid; assumption).
  assert (Vv : valid xd (v * 16 + p)).
  { apply ent_valid; [exact Hv|]. destruct Hk as [Hl _]. rewrite <- Hl. exact Hp. }
  assert (Hke : keyeq xd (u * 16 + p) (v * 16 + p)).
  { split; [rewrite !ent_pos by lia; reflexivity|].
    rewrite !ent_word, ent_pos by (try lia; pose proof (Hlen v Hv); lia). exact Hk. }
  apply F5 in Hke; [|exact Vu | exact Vv].
  pose proof (i_proc _ _ Hi j Hj p Hp) as Hm. fold u in Hm.
  pose proof (i_mark _ _ Hi _ Hm (v * 16 + p) Vv (eq_sym Hke)) as Hvis.
  rewrite ent_word in Hvis by lia. exact Hvis.
Qed.

(* an unvisited node reached in k steps is at least one step beyond the head *)
Lemma frontier : forall s qh, Inv s qh ->
  forall x k, ri x k -> ~ vis s x ->
  ((φ qh) < (φ (sT s)))%Z /\ (dist s (sQ s).[qh] + 1 <= Z.of_nat k)%Z.
Proof.
  intros s qh Hi x k H. induction H as [| u v k Hr IH Hv Hm]; intros Hnv.
  - exfalso. apply Hnv. unfold vis. rewrite (i_s0 _ _ Hi). apply neq_Z. cbv; discriminate.
  - destruct (vis_dec s u) as [Hu | Hu].
    + pose proof (ri_lt _ _ Hr) as Hun.
      destruct (i_vQ _ _ Hi u Hun Hu) as (j & Hj & Hq).
      destruct (Z_lt_le_dec (φ j) (φ qh)) as [Hjq | Hjq].
      * exfalso. apply Hnv. eapply closure; [exact Hi | exact Hjq | exact Hv |]. rewrite Hq. exact Hm.
      * split; [lia|].
        pose proof (i_mono _ _ Hi qh j Hjq Hj) as M. rewrite Hq in M.
        pose proof (i_opt _ _ Hi u Hun Hu k Hr). lia.
    + destruct (IH Hu) as [A B]. split; [exact A | lia].
Qed.

(* the queue has room for one more unvisited node *)
Lemma room : forall s qh, Inv s qh -> forall v, ((φ v) < (φ n))%Z -> ~ vis s v ->
  ((φ (sT s)) < (φ n))%Z.
Proof.
  intros s qh Hi v Hv Hnv.
  pose proof (i_T _ _ Hi) as HT.
  set (T := Z.to_nat (φ (sT s))).
  set (f := fun k : nat => Z.to_nat (φ ((sQ s).[of_Z (Z.of_nat k)]))).
  assert (Hof : forall k, (k < T)%nat -> (φ (of_Z (Z.of_nat k))) = Z.of_nat k).
  { intros k Hk. rewrite of_Z_spec. apply Z.mod_small. unfold T in Hk.
    change wB with 9223372036854775808%Z. lia. }
  assert (Hnd : NoDup (Z.to_nat (φ v) :: map f (seq 0 T))).
  { constructor.
    - intros Hin. apply in_map_iff in Hin as (k & Hk & Hin). apply in_seq in Hin.
      apply Hnv. unfold f in Hk.
      assert (Hq : (sQ s).[of_Z (Z.of_nat k)] = v).
      { apply to_Z_inj. pose proof (to_Z_bounded v).
        pose proof (to_Z_bounded ((sQ s).[of_Z (Z.of_nat k)])). lia. }
      rewrite <- Hq. apply (i_Qv _ _ Hi). rewrite Hof by lia. unfold T in Hin. lia.
    - apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
      intros a b Ha Hb Hab. apply in_seq in Ha, Hb. unfold f in Hab.
      assert (Hq : (sQ s).[of_Z (Z.of_nat a)] = (sQ s).[of_Z (Z.of_nat b)]).
      { apply to_Z_inj.
        pose proof (to_Z_bounded ((sQ s).[of_Z (Z.of_nat a)])).
        pose proof (to_Z_bounded ((sQ s).[of_Z (Z.of_nat b)])). lia. }
      apply (i_Qd _ _ Hi) in Hq;
        [| rewrite Hof by lia; unfold T in Ha; lia | rewrite Hof by lia; unfold T in Hb; lia].
      apply (f_equal to_Z) in Hq. rewrite !Hof in Hq by lia. lia. }
  assert (Hinc : incl (Z.to_nat (φ v) :: map f (seq 0 T)) (seq 0 (Z.to_nat (φ n)))).
  { intros x [Hx | Hx].
    - subst x. apply in_seq. pose proof (to_Z_bounded v). lia.
    - apply in_map_iff in Hx as (k & Hk & Hin). apply in_seq in Hin. subst x.
      apply in_seq. unfold f.
      assert (Hk' : ((φ (of_Z (Z.of_nat k))) < (φ (sT s)))%Z) by (rewrite Hof by lia; unfold T in Hin; lia).
      pose proof (proj1 (i_Qv _ _ Hi _ Hk')).
      pose proof (to_Z_bounded ((sQ s).[of_Z (Z.of_nat k)])). lia. }
  pose proof (NoDup_incl_length Hnd Hinc) as Hl.
  simpl in Hl. rewrite length_map, !length_seq in Hl. unfold T in Hl.
  pose proof (to_Z_bounded (sT s)). lia.
Qed.

(* visiting one unvisited neighbour v of the head u *)
Lemma visit : forall s qh, Inv s qh -> ((φ qh) < (φ (sT s)))%Z ->
  forall v, ((φ v) < (φ n))%Z -> ~ vis s v -> msim xd.[(sQ s).[qh]] xd.[v] ->
  let u := (sQ s).[qh] in
  let s' := mkb (sD s).[v <- (sD s).[u] + 1] (sP s).[v <- u]
                (sQ s).[sT s <- v] (sT s + 1) (sM s) in
  Inv s' qh /\ mono s s' /\ vis s' v.
Proof.
  intros s qh Hi Hqh v Hv Hnv Hm u s'.
  pose proof (room _ _ Hi v Hv Hnv) as HTn.
  destruct (i_Qv _ _ Hi qh Hqh) as [Hu Hvu]. fold u in Hu, Hvu.
  pose proof (vis_pos _ _ Hvu) as Hdu1. pose proof (i_Db _ _ Hi u Hu) as HduT.
  pose proof (i_lD _ _ Hi) as LD. pose proof (i_lP _ _ Hi) as LP. pose proof (i_lQ _ _ Hi) as LQ.
  assert (Hdu : (φ ((sD s).[u] + 1)) = ((φ ((sD s).[u])) + 1)%Z) by sia.
  assert (HT1 : (φ (sT s + 1)) = ((φ (sT s)) + 1)%Z) by sia.
  assert (Huv : (φ u) <> (φ v)) by (intro E; apply Hnv; replace v with u by (apply to_Z_inj; exact E); exact Hvu).
  assert (HDv : (sD s').[v] = (sD s).[u] + 1) by (simpl; apply gss; rewrite LD; exact Hv).
  assert (HDo : forall x, (φ v) <> (φ x) -> (sD s').[x] = (sD s).[x]) by (intros x E; simpl; apply gso; exact E).
  assert (HPv : (sP s').[v] = u) by (simpl; apply gss; rewrite LP; exact Hv).
  assert (HPo : forall x, (φ v) <> (φ x) -> (sP s').[x] = (sP s).[x]) by (intros x E; simpl; apply gso; exact E).
  assert (HQT : (sQ s').[sT s] = v) by (simpl; apply gss; rewrite LQ; exact HTn).
  assert (HQo : forall j, (φ (sT s)) <> (φ j) -> (sQ s').[j] = (sQ s).[j]) by (intros j E; simpl; apply gso; exact E).
  assert (Hvisv : vis s' v) by (unfold vis; rewrite HDv; apply neq_Z; lia).
  assert (Hviso : forall x, (φ v) <> (φ x) -> (vis s' x <-> vis s x)) by (intros x E; unfold vis; rewrite HDo by exact E; reflexivity).
  assert (Hdisto : forall x, (φ v) <> (φ x) -> dist s' x = dist s x) by (intros x E; unfold dist; rewrite HDo by exact E; reflexivity).
  assert (Hdistv : dist s' v = (dist s u + 1)%Z) by (unfold dist; rewrite HDv, Hdu; lia).
  assert (Hneq : forall x, vis s x -> (φ v) <> (φ x))
    by (intros x Hx E; apply Hnv; replace v with x by (apply to_Z_inj; symmetry; exact E); exact Hx).
  assert (HQj : forall j, ((φ j) < (φ (sT s)))%Z -> (sQ s').[j] = (sQ s).[j]) by (intros j Hj; apply HQo; lia).
  assert (HsT : sT s' = sT s + 1) by reflexivity.
  split; [|split; [|exact Hvisv]].
  - constructor.
    + simpl. rewrite lset. exact LD.
    + simpl. rewrite lset. exact LP.
    + simpl. rewrite lset. exact LQ.
    + exact (i_lM _ _ Hi).
    + rewrite HsT, HT1. lia.
    + rewrite HsT, HT1. lia.
    + intros j Hj. rewrite HsT, HT1 in Hj.
      destruct (Z.eq_dec (φ (sT s)) (φ j)) as [E | E].
      * replace j with (sT s) by (apply to_Z_inj; exact E). rewrite HQT. split; [exact Hv | exact Hvisv].
      * rewrite HQo by exact E. destruct (i_Qv _ _ Hi j ltac:(lia)) as [A B].
        split; [exact A|]. apply Hviso; [apply Hneq; exact B | exact B].
    + intros x Hx Hvx. rewrite HsT, HT1.
      destruct (Z.eq_dec (φ v) (φ x)) as [E | E].
      * exists (sT s). split; [lia|]. rewrite HQT. apply to_Z_inj. exact E.
      * apply Hviso in Hvx; [|exact E]. destruct (i_vQ _ _ Hi x Hx Hvx) as (j & Hj & Hq).
        exists j. split; [lia|]. rewrite HQj by exact Hj. exact Hq.
    + intros j1 j2 Hj1 Hj2 Hq. rewrite HsT, HT1 in Hj1, Hj2.
      destruct (Z.eq_dec (φ (sT s)) (φ j1)) as [E1 | E1];
      destruct (Z.eq_dec (φ (sT s)) (φ j2)) as [E2 | E2].
      * apply to_Z_inj. lia.
      * exfalso. rewrite (HQo j2 E2) in Hq. replace j1 with (sT s) in Hq by (apply to_Z_inj; exact E1).
        rewrite HQT in Hq. destruct (i_Qv _ _ Hi j2 ltac:(lia)) as [_ B]. rewrite <- Hq in B. contradiction.
      * exfalso. rewrite (HQo j1 E1) in Hq. replace j2 with (sT s) in Hq by (apply to_Z_inj; exact E2).
        rewrite HQT in Hq. destruct (i_Qv _ _ Hi j1 ltac:(lia)) as [_ B]. rewrite Hq in B. contradiction.
      * rewrite (HQo j1 E1), (HQo j2 E2) in Hq. apply (i_Qd _ _ Hi); [lia | lia | exact Hq].
    + rewrite HDo; [exact (i_s0 _ _ Hi)|]. apply Hneq. unfold vis. rewrite (i_s0 _ _ Hi). apply neq_Z. cbv; discriminate.
    + intros x Hx. rewrite HsT, HT1.
      destruct (Z.eq_dec (φ v) (φ x)) as [E | E].
      * replace x with v by (apply to_Z_inj; exact E). rewrite HDv, Hdu. lia.
      * rewrite HDo by exact E. pose proof (i_Db _ _ Hi x Hx). lia.
    + intros x Hx Hvx.
      destruct (Z.eq_dec (φ v) (φ x)) as [E | E].
      * replace x with v by (apply to_Z_inj; exact E). rewrite HDv, Hdu, HPv.
        split; [lia|]. intros _. split; [exact Hu|].
        split; [apply Hviso; [lia | exact Hvu] |].
        split; [rewrite HDo by lia; reflexivity | exact Hm].
      * apply Hviso in Hvx; [|exact E]. rewrite HDo, HPo by exact E.
        destruct (i_par _ _ Hi x Hx Hvx) as [A B]. split; [exact A|].
        intros Hlt. destruct (B Hlt) as (B1 & B2 & B3 & B4).
        split; [exact B1|]. pose proof (Hneq _ B2) as E2.
        split; [apply Hviso; [exact E2 | exact B2]|].
        split; [rewrite HDo by exact E2; exact B3 | exact B4].
    + intros x Hx Hvx k Hr.
      destruct (Z.eq_dec (φ v) (φ x)) as [E | E].
      * replace x with v in * by (apply to_Z_inj; exact E). rewrite Hdistv.
        destruct (frontier _ _ Hi v k Hr Hnv) as [_ F]. fold u in F. exact F.
      * apply Hviso in Hvx; [|exact E]. rewrite Hdisto by exact E. apply (i_opt _ _ Hi); assumption.
    + intros j1 j2 Hj Hj2. rewrite HsT, HT1 in Hj2.
      destruct (Z.eq_dec (φ (sT s)) (φ j2)) as [E2 | E2].
      * replace j2 with (sT s) by (apply to_Z_inj; exact E2). rewrite HQT, Hdistv.
        destruct (Z.eq_dec (φ (sT s)) (φ j1)) as [E1 | E1].
        -- replace j1 with (sT s) by (apply to_Z_inj; exact E1). rewrite HQT, Hdistv. lia.
        -- rewrite HQo by exact E1. destruct (i_Qv _ _ Hi j1 ltac:(lia)) as [_ B].
           rewrite Hdisto by (apply Hneq; exact B).
           pose proof (i_spread _ _ Hi Hqh j1 ltac:(lia)). fold u in H. lia.
      * rewrite !HQo by lia.
        destruct (i_Qv _ _ Hi j1 ltac:(lia)) as [_ B1]. destruct (i_Qv _ _ Hi j2 ltac:(lia)) as [_ B2].
        rewrite !Hdisto by (apply Hneq; assumption).
        apply (i_mono _ _ Hi); lia.
    + intros _ j Hj. rewrite HsT, HT1 in Hj. rewrite (HQj qh Hqh). fold u.
      rewrite (Hdisto u) by lia.
      destruct (Z.eq_dec (φ (sT s)) (φ j)) as [E | E].
      * replace j with (sT s) by (apply to_Z_inj; exact E). rewrite HQT, Hdistv. lia.
      * rewrite HQo by exact E. destruct (i_Qv _ _ Hi j ltac:(lia)) as [_ B].
        rewrite Hdisto by (apply Hneq; exact B).
        pose proof (i_spread _ _ Hi Hqh j ltac:(lia)). fold u in H. lia.
    + intros c Hc y Hy Hcy. simpl in Hc.
      pose proof (i_mark _ _ Hi c Hc y Hy Hcy) as B.
      apply Hviso; [apply Hneq; exact B | exact B].
    + intros j Hj p Hp. simpl. rewrite HQj in Hp |- * by (pose proof (i_qh _ _ Hi); lia).
      exact (i_proc _ _ Hi j Hj p Hp).
  - split; [rewrite HsT, HT1; lia|].
    split; [exact HQj|].
    split; [intros x Hx Hvx; apply HDo; apply Hneq; exact Hvx|].
    simpl. auto.
Qed.

Lemma cwalk_eq : forall u du ptr s H,
  cwalk cn u du ptr s H =
  if ptr =? 0 then s
  else
    let e := ptr - 1 in
    let v := e >> 4 in
    let s' := if (sD s).[v] =? 0
              then mkb (sD s).[v <- du + 1] (sP s).[v <- u]
                       (sQ s).[sT s <- v] (sT s + 1) (sM s)
              else s in
    match bdec (cn.[e] <? ptr) with
    | left Hl => cwalk cn u du cn.[e] s' (Acc_inv H (dec_ptr _ _ Hl))
    | right _ => s'
    end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma cwalk_spec : forall qh u du z ptr s H, (φ ptr) = z ->
  Inv s qh -> ((φ qh) < (φ (sT s)))%Z -> u = (sQ s).[qh] -> du = (sD s).[u] ->
  (forall y, inchain cn ptr y -> valid xd y /\ msim xd.[u] xd.[y >> 4]) ->
  let s' := cwalk cn u du ptr s H in
  Inv s' qh /\ mono s s' /\ sM s' = sM s /\
  (forall y, inchain cn ptr y -> vis s' (y >> 4)).
Proof.
  intros qh u du z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros ptr s H Hz Hi Hqh Hu Hdu Hch s'. subst s'. rewrite cwalk_eq.
  destruct (ptr =? 0) eqn:E0.
  - rewrite Uint63.eqb_spec in E0. subst ptr.
    split; [exact Hi|]. split; [apply mono_refl|]. split; [reflexivity|].
    intros y Hy. exfalso. exact (inchain_nz _ _ Hy).
  - rewrite Uint63.eqb_false_spec in E0. cbv zeta.
    destruct (Hch (ptr - 1) (ic_here _ _ E0)) as [Hve Hme].
    pose proof (valid_word _ Hve) as Hvn.
    set (v := (ptr - 1) >> 4) in *.
    assert (S1 : exists s1, s1 = (if (sD s).[v] =? 0
              then mkb (sD s).[v <- du + 1] (sP s).[v <- u]
                       (sQ s).[sT s <- v] (sT s + 1) (sM s)
              else s) /\
              Inv s1 qh /\ mono s s1 /\ sM s1 = sM s /\ vis s1 v).
    { eexists. split; [reflexivity|].
      destruct ((sD s).[v] =? 0) eqn:Ev.
      - rewrite Uint63.eqb_spec in Ev.
        assert (Hnv : ~ vis s v) by (unfold vis; intro F; apply F; exact Ev).
        subst u du.
        destruct (visit s qh Hi Hqh v Hvn Hnv Hme) as (A & B & C).
        split; [exact A|]. split; [exact B|]. split; [reflexivity | exact C].
      - rewrite Uint63.eqb_false_spec in Ev.
        split; [exact Hi|]. split; [apply mono_refl|]. split; [reflexivity | exact Ev]. }
    destruct S1 as (s1 & Es1 & I1 & M1 & EM1 & V1). rewrite <- Es1.
    assert (Hqh1 : ((φ qh) < (φ (sT s1)))%Z) by (destruct M1; lia).
    assert (Hu1 : u = (sQ s1).[qh]) by (destruct M1 as (_ & B & _); rewrite B by exact Hqh; exact Hu).
    assert (Hdu1 : du = (sD s1).[u]).
    { destruct M1 as (_ & _ & C & _). rewrite C; [exact Hdu | |].
      - rewrite Hu. apply (i_Qv _ _ Hi). exact Hqh.
      - rewrite Hu. apply (i_Qv _ _ Hi). exact Hqh. }
    destruct (bdec (cn.[ptr - 1] <? ptr)) as [Hl | Hl].
    + destruct (IH (φ (cn.[ptr - 1])) ltac:(rewrite <- Hz; apply dec_ptr; exact Hl)
                  cn.[ptr - 1] s1 (Acc_inv H (dec_ptr _ _ Hl)) eq_refl I1 Hqh1 Hu1 Hdu1
                  ltac:(intros y Hy; apply Hch; apply ic_next; [exact E0 | exact Hy]))
        as (A & B & C & D).
      split; [exact A|]. split; [eapply mono_trans; eassumption|].
      split; [rewrite C; exact EM1|].
      intros y Hy. inversion Hy as [p0 Hp Eq | p0 y' Hp H' Eq]; subst.
      * eapply mono_vis; [exact B | exact Hvn | exact V1].
      * apply D. exact H'.
    + exfalso. destruct Hfi as (_ & _ & Dcn & _).
      rewrite <- Bool.not_true_iff_false, ltb_spec in Hl.
      pose proof (Dcn (ptr - 1)). apply Hl. sia.
Qed.

Lemma setmark : forall s qh c, Inv s qh -> ((φ c) < (φ (N16 xd)))%Z ->
  (forall y, valid xd y -> cls.[y] = c -> vis s (y >> 4)) ->
  let s' := mkb (sD s) (sP s) (sQ s) (sT s) (sM s).[c <- 1] in
  Inv s' qh /\ mono s s' /\ (sM s').[c] <> 0.
Proof.
  intros s qh c Hi Hc Hall s'.
  assert (HM : (sM s').[c] = 1) by (simpl; apply gss; rewrite (i_lM _ _ Hi); exact Hc).
  assert (HMo : forall x, (φ c) <> (φ x) -> (sM s').[x] = (sM s).[x]) by (intros x E; simpl; apply gso; exact E).
  assert (H1 : (1 : int) <> 0) by (apply neq_Z; cbv; discriminate).
  assert (Hup : forall x, (sM s).[x] <> 0 -> (sM s').[x] <> 0).
  { intros x Hx. destruct (Z.eq_dec (φ c) (φ x)) as [E | E].
    - replace x with c by (apply to_Z_inj; exact E). rewrite HM. exact H1.
    - rewrite HMo by exact E. exact Hx. }
  split; [|split; [|rewrite HM; exact H1]].
  - destruct Hi. constructor; try assumption.
    + simpl. rewrite lset. assumption.
    + intros c' Hc' y Hy Hcy. destruct (Z.eq_dec (φ c) (φ c')) as [E | E].
      * replace c' with c in Hcy by (apply to_Z_inj; exact E). apply Hall; assumption.
      * rewrite HMo in Hc' by exact E. eapply i_mark0; eassumption.
    + intros j Hj p Hp. apply Hup. apply i_proc0; assumption.
  - split; [simpl; lia|]. split; [reflexivity|]. split; [reflexivity|]. exact Hup.
Qed.

Lemma ploop_eq : forall u du base len p s H,
  ploop cls hd cn u du base len p s H =
  match bdec (p <? len) with
  | left Hp =>
      let c := cls.[base + p] in
      if (sM s).[c] =? 0 then
        let s1 := cwalk cn u du hd.[c] s (Zwf_well_founded 0 (φ (hd.[c]))) in
        ploop cls hd cn u du base len (p + 1)
          (mkb (sD s1) (sP s1) (sQ s1) (sT s1) (sM s1).[c <- 1])
          (Acc_inv H (dec_step len p Hp))
      else ploop cls hd cn u du base len (p + 1) s
             (Acc_inv H (dec_step len p Hp))
  | right _ => s
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma ploop_spec : forall qh u du len z p s H, gap len p = z ->
  ((φ p) <= (φ len))%Z -> Inv s qh -> ((φ qh) < (φ (sT s)))%Z ->
  u = (sQ s).[qh] -> du = (sD s).[u] -> len = PrimString.length xd.[u] ->
  (forall p', ((φ p') < (φ p))%Z -> (sM s).[cls.[u * 16 + p']] <> 0) ->
  let s' := ploop cls hd cn u du (u * 16) len p s H in
  Inv s' qh /\ mono s s' /\
  (forall p', ((φ p') < (φ len))%Z -> (sM s').[cls.[u * 16 + p']] <> 0).
Proof.
  intros qh u du len z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros p s H Hz Hp Hi Hqh Hu Hdu Hlu Hpart s'. subst s'. rewrite ploop_eq.
  assert (Hun : ((φ u) < (φ n))%Z) by (rewrite Hu; apply (i_Qv _ _ Hi); exact Hqh).
  assert (Hvu : vis s u) by (rewrite Hu; apply (i_Qv _ _ Hi); exact Hqh).
  pose proof (Hlen u Hun) as Hl16.
  destruct Hfi as (F1 & F2 & F3 & F4 & F5 & F6).
  destruct (bdec (p <? len)) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Hp1 : (φ (p + 1)) = ((φ p) + 1)%Z) by sia.
    cbv zeta.
    assert (Hvp : valid xd (u * 16 + p)) by (apply ent_valid; [exact Hun | rewrite <- Hlu; exact Hlt']).
    set (c := cls.[u * 16 + p]).
    assert (Hc : ((φ c) < (φ (N16 xd)))%Z) by (pose proof (F4 _ Hvp); destruct Hvp; unfold c; lia).
    assert (Hdec : Zwf 0 (gap len (p + 1)) z) by (rewrite <- Hz; apply dec_step; exact Hlt).
    destruct ((sM s).[c] =? 0) eqn:EM.
    + rewrite Uint63.eqb_spec in EM.
      destruct (cwalk_spec qh u du _ hd.[c] s (Zwf_well_founded 0 (φ (hd.[c]))) eq_refl
                  Hi Hqh Hu Hdu) as (A & B & C & D).
      { intros y Hy. apply F6 in Hy as [Hy Hcy]. split; [exact Hy|].
        apply (valid_keyeq_msim u p y Hun ltac:(rewrite <- Hlu; exact Hlt') Hy).
        apply F5; [exact Hvp | exact Hy | symmetry; exact Hcy]. }
      set (s1 := cwalk cn u du hd.[c] s _) in *.
      destruct (setmark s1 qh c A Hc) as (A2 & B2 & C2).
      { intros y Hy Hcy. apply D. apply F6. split; assumption. }
      set (s2 := mkb (sD s1) (sP s1) (sQ s1) (sT s1) (sM s1).[c <- 1]) in *.
      assert (M12 : mono s s2) by (eapply mono_trans; eassumption).
      destruct (IH _ Hdec (p + 1) s2 (Acc_inv H (dec_step len p Hlt)) eq_refl ltac:(lia) A2)
        as (A3 & B3 & C3).
      * destruct M12; lia.
      * destruct M12 as (_ & X & _). rewrite X by exact Hqh. exact Hu.
      * destruct M12 as (_ & _ & X & _). rewrite X; [exact Hdu | exact Hun | exact Hvu].
      * exact Hlu.
      * intros p' Hp'. rewrite Hp1 in Hp'.
        destruct (Z.eq_dec (φ p') (φ p)) as [E | E].
        -- replace p' with p by (apply to_Z_inj; symmetry; exact E). exact C2.
        -- destruct M12 as (_ & _ & _ & X). apply X. apply Hpart. lia.
      * split; [exact A3|]. split; [eapply mono_trans; eassumption | exact C3].
    + rewrite Uint63.eqb_false_spec in EM.
      destruct (IH _ Hdec (p + 1) s (Acc_inv H (dec_step len p Hlt)) eq_refl ltac:(lia) Hi
                  Hqh Hu Hdu Hlu) as (A3 & B3 & C3).
      * intros p' Hp'. rewrite Hp1 in Hp'.
        destruct (Z.eq_dec (φ p') (φ p)) as [E | E].
        -- replace p' with p by (apply to_Z_inj; symmetry; exact E). exact EM.
        -- apply Hpart. lia.
      * split; [exact A3|]. split; [exact B3 | exact C3].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
    split; [exact Hi|]. split; [apply mono_refl|].
    intros p' Hp'. apply Hpart. lia.
Qed.

Lemma advance : forall s qh, Inv s qh -> ((φ qh) < (φ (sT s)))%Z ->
  (forall p, ((φ p) < (φ (PrimString.length xd.[(sQ s).[qh]])))%Z ->
     (sM s).[cls.[(sQ s).[qh] * 16 + p]] <> 0) ->
  Inv s (qh + 1).
Proof.
  intros s qh Hi Hqh Hall.
  assert (Hq1 : (φ (qh + 1)) = ((φ qh) + 1)%Z) by (pose proof (i_T _ _ Hi); sia).
  destruct Hi. constructor; try assumption.
  - lia.
  - intros Hlt j Hj. pose proof (i_spread0 Hqh j Hj).
    pose proof (i_mono0 qh (qh + 1) ltac:(lia) ltac:(lia)). lia.
  - intros j Hj p Hp. destruct (Z.eq_dec (φ j) (φ qh)) as [E | E].
    + replace j with qh in * by (apply to_Z_inj; symmetry; exact E). apply Hall. exact Hp.
    + apply i_proc0; [lia | exact Hp].
Qed.

Lemma bfs_eq : forall qh s H,
  bfs cls hd cn wl n qh s H =
  match bdec (qh <? n) with
  | left Hq =>
      if qh <? sT s then
        let u := (sQ s).[qh] in
        let len := wl.[u] in
        let s' := ploop cls hd cn u (sD s).[u] (u * 16) len 0 s
                    (Zwf_well_founded 0 (gap len 0)) in
        bfs cls hd cn wl n (qh + 1) s' (Acc_inv H (dec_step n qh Hq))
      else s
  | right _ => s
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma bfs_spec : forall z qh s H, gap n qh = z -> Inv s qh ->
  exists qf, Inv (bfs cls hd cn wl n qh s H) qf /\
             (φ qf) = (φ (sT (bfs cls hd cn wl n qh s H))).
Proof.
  intros z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros qh s H Hz Hi. rewrite bfs_eq.
  destruct (bdec (qh <? n)) as [Hq | Hq].
  - destruct (qh <? sT s) eqn:Et.
    + rewrite ltb_spec in Et. cbv zeta.
      assert (Hun : ((φ ((sQ s).[qh])) < (φ n))%Z) by (apply (i_Qv _ _ Hi); exact Et).
      destruct (ploop_spec qh (sQ s).[qh] (sD s).[(sQ s).[qh]] wl.[(sQ s).[qh]] _ 0 s
                  (Zwf_well_founded 0 (gap wl.[(sQ s).[qh]] 0)) eq_refl
                  ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded wl.[(sQ s).[qh]]); lia)
                  Hi Et eq_refl eq_refl (Hwl _ Hun)
                  ltac:(intros p' Hp'; change (φ 0) with 0%Z in Hp'; pose proof (to_Z_bounded p'); lia))
        as (A & B & C).
      eapply IH; [rewrite <- Hz; apply dec_step; exact Hq | reflexivity |].
      apply advance; [exact A | destruct B; lia |].
      destruct B as (_ & B2 & _). rewrite B2 by exact Et.
      rewrite <- (Hwl _ Hun). exact C.
    + exists qh. split; [exact Hi|].
      rewrite <- Bool.not_true_iff_false, ltb_spec in Et. pose proof (i_qh _ _ Hi). lia.
  - exists qh. split; [exact Hi|].
    rewrite <- Bool.not_true_iff_false, ltb_spec in Hq.
    pose proof (i_qh _ _ Hi). pose proof (i_T _ _ Hi). lia.
Qed.

Lemma init_inv :
  let st := mkb (PArray.make n 0).[s0 <- 1] (PArray.make n 0)
                (PArray.make n 0).[0 <- s0] 1 (PArray.make (N16 xd) 0) in
  Inv st 0.
Proof.
  intros st.
  pose proof (N16_val xd Hn) as HN. pose proof (to_Z_bounded s0).
  assert (Ln : PArray.length (PArray.make n 0) = n) by (apply lmk; lia).
  assert (HD : forall v, (sD st).[v] = if ((φ v) =? (φ s0))%Z then 1 else 0).
  { intros v. simpl. destruct (Z.eqb_spec (φ v) (φ s0)) as [E | E].
    - replace v with s0 by (apply to_Z_inj; symmetry; exact E). apply gss. rewrite Ln. exact Hs0.
    - rewrite gso by lia. apply gmk. }
  assert (HQ0 : (sQ st).[0] = s0) by (simpl; apply gss; rewrite Ln; change (φ 0) with 0%Z; lia).
  assert (Hvis : forall v, vis st v <-> v = s0).
  { intros v. unfold vis. rewrite HD. destruct (Z.eqb_spec (φ v) (φ s0)) as [E | E].
    - split; [intros _; apply to_Z_inj; exact E | intros _; apply neq_Z; cbv; discriminate].
    - split; [intros F; exfalso; apply F; reflexivity | intros ->; lia]. }
  assert (Hj0 : forall j, ((φ j) < (φ (sT st)))%Z -> j = 0)
    by (intros j Hj; simpl in Hj; change (φ 1) with 1%Z in Hj; apply to_Z_inj;
        pose proof (to_Z_bounded j); change (φ 0) with 0%Z; lia).
  constructor.
  - simpl. rewrite lset. exact Ln.
  - exact Ln.
  - simpl. rewrite lset. exact Ln.
  - apply lmk. lia.
  - simpl. change (φ 1) with 1%Z. change (φ 0) with 0%Z. lia.
  - simpl. change (φ 1) with 1%Z. lia.
  - intros j Hj. rewrite (Hj0 j Hj), HQ0. split; [exact Hs0 | apply Hvis; reflexivity].
  - intros v Hv Hvv. apply Hvis in Hvv. subst v. exists 0. split; [simpl; change (φ 1) with 1%Z; change (φ 0) with 0%Z; lia | exact HQ0].
  - intros j1 j2 Hj1 Hj2 _. rewrite (Hj0 j1 Hj1), (Hj0 j2 Hj2). reflexivity.
  - rewrite HD. rewrite Z.eqb_refl. reflexivity.
  - intros v Hv. rewrite HD. simpl. change (φ 1) with 1%Z.
    destruct ((φ v) =? (φ s0))%Z; [change (φ 1) with 1%Z | change (φ 0) with 0%Z]; lia.
  - intros v Hv Hvv. apply Hvis in Hvv. subst v. rewrite HD, Z.eqb_refl.
    change (φ 1) with 1%Z. split; [reflexivity | lia].
  - intros v Hv Hvv k _. apply Hvis in Hvv. subst v. unfold dist. rewrite HD, Z.eqb_refl.
    change (φ 1) with 1%Z. lia.
  - intros j1 j2 Hj Hj2. rewrite (Hj0 j2 Hj2). assert (j1 = 0) by (apply to_Z_inj;
      pose proof (to_Z_bounded j1); pose proof (Hj0 j2 Hj2); subst j2; change (φ 0) with 0%Z in *; lia).
    subst j1. lia.
  - intros _ j Hj. rewrite (Hj0 j Hj). lia.
  - intros c Hc. exfalso. apply Hc. simpl. apply gmk.
  - intros j Hj. change (φ 0) with 0%Z in Hj. pose proof (to_Z_bounded j). lia.
Qed.

(* at the end of the search, every reachable node is visited *)
Lemma complete : forall s qf, Inv s qf -> (φ qf) = (φ (sT s)) ->
  forall x k, ri x k -> vis s x.
Proof.
  intros s qf Hi Hq x k Hr. destruct (vis_dec s x) as [V | V]; [exact V|].
  destruct (frontier s qf Hi x k Hr V) as [A _]. lia.
Qed.

(* the m-th ancestor through the parent pointers *)
Fixpoint anc (P : array int) (m : nat) (v : int) : int :=
  match m with O => v | S m => P.[anc P m v] end.

Lemma anc_shift : forall P m v, anc P m P.[v] = anc P (S m) v.
Proof. intros P m v. induction m as [| m IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma anc_spec : forall s q, Inv s q -> forall v, ((φ v) < (φ n))%Z -> vis s v ->
  forall m, (Z.of_nat m < (φ ((sD s).[v])))%Z ->
  ((φ (anc (sP s) m v)) < (φ n))%Z /\ vis s (anc (sP s) m v) /\
  (φ ((sD s).[anc (sP s) m v])) = ((φ ((sD s).[v])) - Z.of_nat m)%Z.
Proof.
  intros s q Hi v Hv Hvv m. induction m as [| m IH]; intros Hm.
  - simpl. split; [exact Hv|]. split; [exact Hvv | lia].
  - rewrite Nat2Z.inj_succ in Hm.
    destruct (IH ltac:(lia)) as (A & B & C).
    change (anc (sP s) (S m) v) with ((sP s).[anc (sP s) m v]).
    assert (G : (1 < (φ ((sD s).[anc (sP s) m v])))%Z) by (rewrite C; clear -Hm; lia).
    destruct (i_par _ _ Hi _ A B) as [_ P]. destruct (P G) as (P1 & P2 & P3 & _).
    split; [exact P1|]. split; [exact P2 | rewrite Nat2Z.inj_succ; clear -P3 C; lia].
Qed.

Lemma anc_msim : forall s q, Inv s q -> forall v, ((φ v) < (φ n))%Z -> vis s v ->
  forall m, (Z.of_nat (S m) < (φ ((sD s).[v])))%Z ->
  msim xd.[anc (sP s) (S m) v] xd.[anc (sP s) m v].
Proof.
  intros s q Hi v Hv Hvv m Hm.
  rewrite Nat2Z.inj_succ in Hm.
  destruct (anc_spec s q Hi v Hv Hvv m ltac:(lia)) as (A & B & C).
  change (anc (sP s) (S m) v) with ((sP s).[anc (sP s) m v]).
  assert (G : (1 < (φ ((sD s).[anc (sP s) m v])))%Z) by (rewrite C; clear -Hm; lia).
  destruct (i_par _ _ Hi _ A B) as [_ P]. destruct (P G) as (_ & _ & _ & P4). exact P4.
Qed.

Lemma anc_top : forall s q, Inv s q -> forall v, ((φ v) < (φ n))%Z -> vis s v ->
  anc (sP s) (Z.to_nat ((φ ((sD s).[v])) - 1)) v = s0.
Proof.
  intros s q Hi v Hv Hvv. pose proof (vis_pos _ _ Hvv).
  destruct (anc_spec s q Hi v Hv Hvv (Z.to_nat ((φ ((sD s).[v])) - 1)) ltac:(lia)) as (A & B & C).
  destruct (i_par _ _ Hi _ A B) as [P _]. apply P. lia.
Qed.

(* the parent pointers give a path of length dist v *)
Lemma path_ri : forall s q, Inv s q -> forall v, ((φ v) < (φ n))%Z -> vis s v ->
  forall m, (Z.of_nat m < (φ ((sD s).[v])))%Z ->
  ri (anc (sP s) m v) (Z.to_nat ((φ ((sD s).[v])) - 1) - m).
Proof.
  intros s q Hi v Hv Hvv m Hm. pose proof (vis_pos _ _ Hvv).
  remember (Z.to_nat ((φ ((sD s).[v])) - 1) - m)%nat as k eqn:Ek.
  revert m Hm Ek. induction k as [| k IH]; intros m Hm Ek.
  - replace m with (Z.to_nat ((φ ((sD s).[v])) - 1)) by lia.
    rewrite (anc_top s q Hi v Hv Hvv). apply ri0.
  - pose proof (IH (S m) ltac:(lia) ltac:(lia)) as R.
    destruct (anc_spec s q Hi v Hv Hvv m Hm) as (A & _ & _).
    eapply riS; [exact R | exact A |]. apply (anc_msim s q Hi v Hv Hvv m). lia.
Qed.

Lemma recon_eq : forall D P v out H,
  recon xd D P v out H =
  let out' := out.[D.[v] - 1 <- xd.[v]] in
  if D.[v] <=? 1 then out'
  else match bdec (D.[P.[v]] <? D.[v]) with
       | left Hl => recon xd D P P.[v] out' (Acc_inv H (dec_ptr _ _ Hl))
       | right _ => out'
       end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma recon_spec : forall s q, Inv s q -> forall z v out H,
  (φ ((sD s).[v])) = z -> ((φ v) < (φ n))%Z -> vis s v ->
  ((φ ((sD s).[v])) <= (φ (PArray.length out)))%Z ->
  let r := recon xd (sD s) (sP s) v out H in
  PArray.length r = PArray.length out /\
  (forall k, ((φ k) < (φ ((sD s).[v])))%Z ->
     r.[k] = xd.[anc (sP s) (Z.to_nat ((φ ((sD s).[v])) - 1 - (φ k))) v]) /\
  (forall k, ((φ ((sD s).[v])) <= (φ k))%Z -> r.[k] = out.[k]).
Proof.
  intros s q Hi z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros v out H Hz Hv Hvv Hlo r. subst r. rewrite recon_eq. cbv zeta.
  pose proof (vis_pos _ _ Hvv) as Hd1.
  set (d := (sD s).[v]) in *.
  assert (Hd' : (φ (d - 1)) = ((φ d) - 1)%Z) by sia.
  assert (Hout1 : (sD s).[v] = d) by reflexivity.
  assert (Gs : out.[d - 1 <- xd.[v]].[d - 1] = xd.[v]) by (apply gss_s; lia).
  assert (Go : forall k, (φ (d - 1)) <> (φ k) -> out.[d - 1 <- xd.[v]].[k] = out.[k])
    by (intros k E; apply gso_s; exact E).
  destruct (d <=? 1) eqn:E1.
  - rewrite leb_spec in E1. change (φ 1) with 1%Z in E1.
    split; [apply lset_s|]. split.
    + intros k Hk. replace k with (d - 1) by (apply to_Z_inj; pose proof (to_Z_bounded k); lia).
      rewrite Gs. replace (Z.to_nat ((φ d) - 1 - (φ (d - 1)))) with O by lia. reflexivity.
    + intros k Hk. apply Go. lia.
  - rewrite <- Bool.not_true_iff_false, leb_spec in E1. change (φ 1) with 1%Z in E1.
    destruct (i_par _ _ Hi v Hv Hvv) as [_ P]. destruct (P ltac:(fold d; clear -E1; lia)) as (P1 & P2 & P3 & _).
    fold d in P3.
    destruct (bdec ((sD s).[(sP s).[v]] <? d)) as [Hl | Hl].
    + destruct (IH (φ ((sD s).[(sP s).[v]])) ltac:(rewrite <- Hz; apply dec_ptr; exact Hl)
                  (sP s).[v] out.[d - 1 <- xd.[v]] (Acc_inv H (dec_ptr _ _ Hl)) eq_refl P1 P2
                  ltac:(rewrite lset_s; lia)) as (A & B & C).
      split; [rewrite A; apply lset_s|]. split.
      * intros k Hk. destruct (Z_lt_le_dec (φ k) (φ ((sD s).[(sP s).[v]]))) as [Hk2 | Hk2].
        -- rewrite B by exact Hk2. rewrite anc_shift. f_equal. f_equal. clear -P3 Hk2. lia.
        -- rewrite C by exact Hk2.
           replace k with (d - 1) by (apply to_Z_inj; clear -P3 Hk2 Hk Hd'; lia).
           rewrite Gs. replace (Z.to_nat ((φ d) - 1 - (φ (d - 1)))) with O by (clear -Hd'; lia). reflexivity.
      * intros k Hk. rewrite C by (clear -P3 Hk; lia). apply Go. clear -Hk Hd'. lia.
    + exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hl. lia.
Qed.

End Search.

(* ------------------------------------------------------------------ *)
(* From machine strings to math strings                               *)
(* ------------------------------------------------------------------ *)

Lemma sget_none : forall (a : string) k, (String.length a <= k)%nat -> String.get k a = None.
Proof.
  induction a as [| c a IH]; intros k Hk; [reflexivity|].
  destruct k as [| k]; simpl in Hk; [lia|]. simpl. apply IH. lia.
Qed.

Lemma repr_len : forall (x : pstring) (a : string), repr x a ->
  (φ (PrimString.length x)) = Z.of_nat (String.length a).
Proof. intros x a [H _]. symmetry. exact H. Qed.

Lemma repr_get : forall (x : pstring) (a : string), repr x a ->
  forall k, ((φ k) < (φ (PrimString.length x)))%Z ->
  exists c, String.get (Z.to_nat (φ k)) a = Some c /\
            (φ (PrimString.get x k)) = Z.of_N (N_of_ascii c).
Proof.
  intros x a [Hl Hc] k Hk.
  destruct (Hc (Z.to_nat (φ k)) ltac:(pose proof (to_Z_bounded k); lia)) as (c & Hg & Hr).
  exists c. split; [exact Hg|].
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded k); lia).
  rewrite of_to_Z in Hr. unfold repr, repr_uint in Hr. rewrite <- Hr.
  pose proof (to_Z_bounded (PrimString.get x k)). lia.
Qed.

Lemma code_inj : forall c1 c2 : ascii, Z.of_N (N_of_ascii c1) = Z.of_N (N_of_ascii c2) -> c1 = c2.
Proof.
  intros c1 c2 H. rewrite <- (ascii_N_embedding c1), <- (ascii_N_embedding c2).
  f_equal. lia.
Qed.

(* same length, then: equal letters at k on both sides *)
Lemma get_iff : forall (x y : pstring) (a b : string), repr x a -> repr y b ->
  PrimString.length x = PrimString.length y ->
  forall k, ((φ k) < (φ (PrimString.length x)))%Z ->
  (PrimString.get x k = PrimString.get y k <->
   String.get (Z.to_nat (φ k)) a = String.get (Z.to_nat (φ k)) b).
Proof.
  intros x y a b Ha Hb Hl k Hk.
  destruct (repr_get x a Ha k Hk) as (c1 & G1 & C1).
  destruct (repr_get y b Hb k ltac:(rewrite <- Hl; exact Hk)) as (c2 & G2 & C2).
  rewrite G1, G2. split.
  - intros E. f_equal. apply code_inj. rewrite <- C1, <- C2, E. reflexivity.
  - intros E. injection E as E. subst c2. apply to_Z_inj. rewrite C1, C2. reflexivity.
Qed.

Lemma repr_eq : forall (x y : pstring) (a b : string), repr x a -> repr y b -> (x = y <-> a = b).
Proof.
  intros x y a b Ha Hb. pose proof (repr_len x a Ha) as La. pose proof (repr_len y b Hb) as Lb.
  split.
  - intros <-. apply String.get_correct. intros k.
    destruct (Nat.lt_ge_cases k (String.length a)) as [Hk | Hk].
    + set (k' := of_Z (Z.of_nat k)).
      assert (Hk' : (φ k') = Z.of_nat k).
      { unfold k'. rewrite of_Z_spec. apply Z.mod_small. pose proof (PString.valid_length x).
        change wB with 9223372036854775808%Z. split; [lia|].
        pose proof (to_Z_bounded (PrimString.length x)). lia. }
      pose proof (proj1 (get_iff x x a b Ha Hb eq_refl k' ltac:(lia)) eq_refl) as E.
      rewrite Hk', Nat2Z.id in E. exact E.
    + rewrite !sget_none by lia. reflexivity.
  - intros <-. apply PString.string_eq_ext.
    assert (Hl : PrimString.length x = PrimString.length y) by (apply to_Z_inj; lia).
    split; [exact Hl|]. intros k Hk.
    apply (get_iff x y a a Ha Hb Hl k Hk). reflexivity.
Qed.

Lemma msim_doublet : forall (x y : pstring) (a b : string), repr x a -> repr y b ->
  msim x y -> x <> y -> doublet a b.
Proof.
  intros x y a b Ha Hb (p & Hp & Hl & Hag) Hne.
  pose proof (repr_len x a Ha) as La. pose proof (repr_len y b Hb) as Lb.
  split; [rewrite Hl in La; lia|].
  exists (Z.to_nat (φ p)). split; [lia|]. split.
  - intros E. apply Hne. apply PString.string_eq_ext. split; [exact Hl|].
    intros k Hk. destruct (Z.eq_dec (φ k) (φ p)) as [Ek | Ek].
    + replace k with p by (apply to_Z_inj; symmetry; exact Ek). apply (get_iff x y a b Ha Hb Hl p Hp). exact E.
    + apply Hag; [exact Hk | apply neq_Z; exact Ek].
  - intros j Hj Hjp.
    set (j' := of_Z (Z.of_nat j)).
    assert (Hj' : (φ j') = Z.of_nat j).
    { unfold j'. rewrite of_Z_spec. apply Z.mod_small.
      pose proof (to_Z_bounded (PrimString.length x)). split; [lia|]. lia. }
    pose proof (proj1 (get_iff x y a b Ha Hb Hl j' ltac:(lia))) as G.
    rewrite Hj', Nat2Z.id in G. apply G. apply Hag; [lia|].
    intros E. apply Hjp. rewrite <- E, Hj'. lia.
Qed.

Lemma doublet_msim : forall (x y : pstring) (a b : string), repr x a -> repr y b -> doublet a b -> msim x y.
Proof.
  intros x y a b Ha Hb (Hl & k & Hk & Hd & Ho).
  pose proof (repr_len x a Ha) as La. pose proof (repr_len y b Hb) as Lb.
  assert (Hl' : PrimString.length x = PrimString.length y) by (apply to_Z_inj; lia).
  set (p := of_Z (Z.of_nat k)).
  assert (Hp : (φ p) = Z.of_nat k).
  { unfold p. rewrite of_Z_spec. apply Z.mod_small.
    pose proof (to_Z_bounded (PrimString.length x)). split; [lia|]. lia. }
  exists p. split; [lia|]. split; [exact Hl'|].
  intros j Hj Hjp. apply (get_iff x y a b Ha Hb Hl' j Hj). apply Ho; [lia|].
  intros E. apply Hjp. apply to_Z_inj. rewrite Hp, <- E. pose proof (to_Z_bounded j). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The chain read back has no repeated word                           *)
(* ------------------------------------------------------------------ *)

Lemma no_repeat : forall xd cls s0 s q t,
  Inv xd cls s0 s q -> ((φ t) < (φ (PArray.length xd)))%Z -> vis s t ->
  xd.[t] <> xd.[s0] ->
  forall m, (Z.of_nat (S m) < (φ ((sD s).[t])))%Z ->
  xd.[anc (sP s) (S m) t] <> xd.[anc (sP s) m t].
Proof.
  intros xd cls s0 s q t Hi Ht Hvt Hts m Hm E.
  rewrite Nat2Z.inj_succ in Hm.
  pose proof (vis_pos xd s0 _ _ Hvt) as Hd1.
  set (d := (φ ((sD s).[t]))) in *.
  destruct (anc_spec xd cls s0 s q Hi t Ht Hvt (S m) ltac:(rewrite Nat2Z.inj_succ; lia)) as (Ax & Bx & Cx).
  destruct (anc_spec xd cls s0 s q Hi t Ht Hvt m ltac:(lia)) as (Ay & By & Cy).
  pose proof (path_ri xd cls s0 s q Hi t Ht Hvt (S m) ltac:(rewrite Nat2Z.inj_succ; lia)) as Rx.
  fold d in Rx, Cx, Cy.
  destruct (Z.to_nat (d - 1) - S m)%nat as [| K] eqn:EK.
  - (* x is the source *)
    assert (Ex : anc (sP s) (S m) t = s0).
    { pose proof (anc_top xd cls s0 s q Hi t Ht Hvt) as T. fold d in T.
      replace (Z.to_nat (d - 1)) with (S m) in T by lia. exact T. }
    destruct m as [| m'].
    + apply Hts. rewrite <- Ex. symmetry. exact E.
    + destruct (anc_spec xd cls s0 s q Hi t Ht Hvt m' ltac:(lia)) as (Az & Bz & Cz).
      fold d in Cz.
      pose proof (anc_msim xd cls s0 s q Hi t Ht Hvt m' ltac:(rewrite Nat2Z.inj_succ; lia)) as Mz.
      rewrite <- E in Mz.
      assert (Rz : ri xd s0 (anc (sP s) m' t) 1).
      { eapply riS; [| exact Az | exact Mz]. rewrite Ex. apply ri0. }
      pose proof (i_opt _ _ _ _ _ Hi _ Az Bz 1 Rz) as O. unfold dist in O. rewrite Cz in O.
      rewrite Nat2Z.inj_succ in Hm. lia.
  - inversion Rx as [| u v k Ru Hv Hmu]. subst.
    rewrite E in Hmu.
    assert (Ry : ri xd s0 (anc (sP s) m t) (S K)) by (eapply riS; eassumption).
    pose proof (i_opt _ _ _ _ _ Hi _ Ay By _ Ry) as O. unfold dist in O. rewrite Cy in O.
    lia.
Qed.

(* ------------------------------------------------------------------ *)
(* One query                                                           *)
(* ------------------------------------------------------------------ *)

Lemma dict_len : forall (dict : list string) (xd : array pstring), repr xd dict ->
  (φ (PArray.length xd)) = Z.of_nat (List.length dict).
Proof. intros dict xd [HL _]. symmetry. exact HL. Qed.

Lemma dict_at : forall (dict : list string) (xd : array pstring), repr xd dict ->
  forall i, ((φ i) < (φ (PArray.length xd)))%Z ->
  exists a, nth_error dict (Z.to_nat (φ i)) = Some a /\ repr xd.[i] a.
Proof.
  intros dict xd Hd i Hi. pose proof (dict_len dict xd Hd) as HL. destruct Hd as [_ HC].
  destruct (HC (Z.to_nat (φ i)) ltac:(pose proof (to_Z_bounded i); lia)) as (m & Hm & Hr).
  exists m. split; [exact Hm|].
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia). rewrite of_to_Z in Hr. exact Hr.
Qed.

Lemma in_dict : forall (dict : list string) (xd : array pstring), repr xd dict ->
  forall a, In a dict -> exists i, ((φ i) < (φ (PArray.length xd)))%Z /\ repr xd.[i] a.
Proof.
  intros dict xd Hd a Ha. pose proof (dict_len dict xd Hd) as HL.
  apply In_nth_error in Ha as (k & Hk).
  assert (Hkl : (k < List.length dict)%nat) by (apply nth_error_Some; congruence).
  pose proof (len_bound _ xd).
  set (i := of_Z (Z.of_nat k)).
  assert (Hi : (φ i) = Z.of_nat k) by (unfold i; rewrite of_Z_spec; apply Z.mod_small;
                                      change wB with 9223372036854775808%Z; lia).
  exists i. split; [lia|].
  destruct (dict_at dict xd Hd i ltac:(lia)) as (b & Hb & Hr).
  rewrite Hi, Nat2Z.id, Hk in Hb. injection Hb as <-. exact Hr.
Qed.

Section Query.

Variables (dict : list string) (xd : array pstring) (cls hd cn wl wb wn : array int).

Local Notation n := (PArray.length xd).

Hypothesis Hd : repr xd dict.
Hypothesis Hn : ((φ n) <= 25143)%Z.
Hypothesis Hlen : forall i, ((φ i) < (φ n))%Z -> (1 <= (φ (PrimString.length xd.[i])) <= 16)%Z.
Hypothesis Hw : WInv xd n wl wb wn.
Hypothesis Hfi : FInv xd cls hd cn.

Lemma Hwl : forall i, ((φ i) < (φ n))%Z -> wl.[i] = PrimString.length xd.[i].
Proof. intros i Hi. destruct Hw as (_ & _ & _ & _ & _ & H). apply (H i Hi). Qed.

(* a math chain gives a path of the same length *)
Lemma chain_ri : forall s0 t a b c,
  ((φ s0) < (φ n))%Z -> repr xd.[s0] a -> ((φ t) < (φ n))%Z -> repr xd.[t] b -> a <> b ->
  is_chain dict a b c -> ri xd s0 t (List.length c - 1).
Proof.
  intros s0 t a b c Hs0 Ha Ht Hb Hab (H0 & Hl & Hall & Hadj).
  assert (Hlen0 : (0 < List.length c)%nat) by (destruct c; [discriminate | simpl; lia]).
  assert (Claim : forall j, (j < List.length c)%nat ->
            exists x w, ((φ x) < (φ n))%Z /\ nth_error c j = Some w /\ repr xd.[x] w /\ ri xd s0 x j).
  { intros j. induction j as [| j IH]; intros Hj.
    - exists s0, a. split; [exact Hs0|]. split; [exact H0|]. split; [exact Ha | apply ri0].
    - destruct (IH ltac:(lia)) as (x & w & Hx & Hw' & Hr & Hri).
      destruct (nth_error c (S j)) as [w2|] eqn:E2; [| apply nth_error_None in E2; lia].
      assert (Hin : In w2 dict) by (rewrite Forall_forall in Hall; apply Hall; eapply nth_error_In; exact E2).
      destruct (in_dict dict xd Hd w2 Hin) as (y & Hy & Hry).
      exists y, w2. split; [exact Hy|]. split; [reflexivity|]. split; [exact Hry|].
      eapply riS; [exact Hri | exact Hy |].
      eapply doublet_msim; [exact Hr | exact Hry | eapply Hadj; eassumption]. }
  destruct (Claim (List.length c - 1)%nat ltac:(lia)) as (x & w & Hx & Hw' & Hr & Hri).
  rewrite Hl in Hw'. injection Hw' as <-.
  assert (Ex : xd.[x] = xd.[t]) by (apply (repr_eq _ _ _ _ Hr Hb); reflexivity).
  destruct (List.length c - 1)%nat as [| K] eqn:EK.
  - exfalso. apply Hab. rewrite H0 in Hl. injection Hl as Hl. exact Hl.
  - inversion Hri as [| u v k Ru Hv Hmu]. subst. rewrite Ex in Hmu.
    eapply riS; [exact Ru | exact Ht | exact Hmu].
Qed.

Definition mw (i : int) : string := nth (Z.to_nat (φ i)) dict EmptyString.

Lemma mw_repr : forall i, ((φ i) < (φ n))%Z -> repr xd.[i] (mw i) /\ In (mw i) dict.
Proof.
  intros i Hi. destruct (dict_at dict xd Hd i Hi) as (a & Ha & Hr).
  unfold mw. rewrite (nth_error_nth _ _ _ Ha). split; [exact Hr|].
  eapply nth_error_In. exact Ha.
Qed.

Lemma answer2_correct : forall s0 a xtgt b,
  ((φ s0) < (φ n))%Z -> repr xd.[s0] a -> repr xtgt b -> xd.[s0] <> xtgt ->
  exists r, repr (answer2 xd n (N16 xd) cls hd cn wl wb wn s0 xtgt) r /\
            answer dict a b r.
Proof.
  intros s0 a xtgt b Hs0 Ha Hb Hne.
  unfold answer2. cbv zeta.
  destruct (lookup_spec xd wl wb wn xtgt Hw) as [[R0 Rn] | [R0 [Rlt Req]]].
  - rewrite R0, Uint63.eqb_refl. exists None. split; [exact I|].
    intros c (H0 & Hl & Hall & _).
    assert (Hin : In b dict) by (rewrite Forall_forall in Hall; apply Hall; eapply nth_error_In; exact Hl).
    destruct (in_dict dict xd Hd b Hin) as (i & Hi & Hr).
    apply (Rn i Hi). apply (repr_eq _ _ _ _ Hr Hb). reflexivity.
  - assert (E : (lookup xd wb wn xtgt =? 0) = false) by (rewrite Uint63.eqb_false_spec; exact R0).
    rewrite E.
    set (t := lookup xd wb wn xtgt - 1) in *.
    assert (Hbt : repr xd.[t] b) by (rewrite Req; exact Hb).
    assert (Hab : a <> b).
    { intros <-. apply Hne. rewrite <- Req. apply (repr_eq _ _ _ _ Ha Hbt). reflexivity. }
    assert (Hts : xd.[t] <> xd.[s0]) by (rewrite Req; intro F; apply Hne; symmetry; exact F).
    unfold bfs_from.
    pose proof (init_inv xd cls s0 Hn Hs0) as Hinit. cbv zeta in Hinit.
    destruct (bfs_spec xd cls hd cn wl s0 Hn Hlen Hwl Hfi Hs0 _ 0 _
                (Zwf_well_founded 0 (gap n 0)) eq_refl Hinit) as (qf & Hi & Hq).
    set (sf := bfs cls hd cn wl n 0 _ _) in *.
    destruct ((sD sf).[t] =? 0) eqn:Ed.
    + exists None. split; [exact I|]. intros c Hc.
      pose proof (chain_ri s0 t a b c Hs0 Ha Rlt Hbt Hab Hc) as Hr.
      pose proof (complete xd cls hd cn s0 Hn Hlen Hfi Hs0 sf qf Hi Hq t _ Hr) as Hv.
      rewrite Uint63.eqb_spec in Ed. exact (Hv Ed).
    + rewrite Uint63.eqb_false_spec in Ed.
      assert (Hvt : vis sf t) by exact Ed.
      pose proof (vis_pos xd s0 _ _ Hvt) as Hd1.
      pose proof (i_Db _ _ _ _ _ Hi t Rlt) as HdT. pose proof (i_T _ _ _ _ _ Hi) as HTn.
      set (d := (sD sf).[t]) in *.
      assert (Hlo : PArray.length (PArray.make d xd.[t]) = d) by (apply lmk_s; lia).
      destruct (recon_spec xd cls s0 sf qf Hi _ t (PArray.make d xd.[t])
                  (Zwf_well_founded 0 (φ d)) eq_refl Rlt Hvt ltac:(rewrite Hlo; lia))
        as (RL & RC & _).
      set (r := recon xd (sD sf) (sP sf) t (PArray.make d xd.[t]) _) in *.
      set (node := fun k : nat => anc (sP sf) (Z.to_nat ((φ d) - 1 - Z.of_nat k)) t).
      assert (Hnode : forall k, (Z.of_nat k < (φ d))%Z ->
                ((φ (node k)) < (φ n))%Z /\ repr xd.[node k] (mw (node k)) /\
                In (mw (node k)) dict).
      { intros k Hk.
        destruct (anc_spec xd cls s0 sf qf Hi t Rlt Hvt (Z.to_nat ((φ d) - 1 - Z.of_nat k)) ltac:(lia))
          as (A & _ & _).
        split; [exact A|]. apply mw_repr; assumption. }
      assert (Hof : forall k, (Z.of_nat k < (φ d))%Z -> (φ (of_Z (Z.of_nat k))) = Z.of_nat k).
      { intros k Hk. rewrite of_Z_spec. apply Z.mod_small. change wB with 9223372036854775808%Z. lia. }
      set (L := map (fun k => mw (node k)) (seq 0 (Z.to_nat (φ d)))).
      assert (HLl : List.length L = Z.to_nat (φ d)) by (unfold L; rewrite length_map, length_seq; reflexivity).
      assert (HLn : forall k, (k < Z.to_nat (φ d))%nat -> nth_error L k = Some (mw (node k))).
      { intros k Hk. unfold L. rewrite nth_error_map, nth_error_seq.
        destruct (Nat.ltb_spec k (Z.to_nat (φ d))); [reflexivity | lia]. }
      exists (Some L). split.
      * split.
        -- rewrite HLl. assert (RL' : PArray.length r = d) by (rewrite RL; exact Hlo).
           transitivity (φ d); [lia|]. rewrite <- RL'. reflexivity.
        -- intros k Hk. rewrite HLl in Hk. exists (mw (node k)).
           split; [apply HLn; exact Hk|].
           assert (Ec : r.[of_Z (Z.of_nat k)] = xd.[node k]).
           { rewrite RC by (rewrite Hof by lia; lia). unfold node. rewrite Hof by lia. reflexivity. }
           destruct (Hnode k ltac:(lia)) as (_ & Hr & _). rewrite <- Ec in Hr. exact Hr.
      * assert (Hs : mw (node 0%nat) = a).
        { assert (E0 : node 0%nat = s0).
          { unfold node. replace ((φ d) - 1 - Z.of_nat 0)%Z with ((φ d) - 1)%Z by lia.
            exact (anc_top xd cls s0 sf qf Hi t Rlt Hvt). }
          destruct (Hnode 0%nat ltac:(lia)) as (_ & Hr0 & _). rewrite E0 in Hr0 |- *.
          apply (repr_eq _ _ _ _ Hr0 Ha). reflexivity. }
        assert (Ht : mw (node (Z.to_nat (φ d) - 1)%nat) = b).
        { assert (E1 : node (Z.to_nat (φ d) - 1)%nat = t).
          { unfold node. replace (Z.to_nat ((φ d) - 1 - Z.of_nat (Z.to_nat (φ d) - 1)%nat)) with O by lia.
            reflexivity. }
          destruct (Hnode (Z.to_nat (φ d) - 1)%nat ltac:(lia)) as (_ & Hr1 & _). rewrite E1 in Hr1 |- *.
          apply (repr_eq _ _ _ _ Hr1 Hbt). reflexivity. }
        split; [split; [| split; [| split]] |].
        -- rewrite (HLn 0%nat) by lia. rewrite Hs. reflexivity.
        -- rewrite HLl, HLn by lia. rewrite Ht. reflexivity.
        -- apply Forall_forall. intros w Hw'. unfold L in Hw'. apply in_map_iff in Hw' as (k & <- & Hk).
           apply in_seq in Hk. apply (Hnode k ltac:(lia)).
        -- intros k a1 b1 Ha1 Hb1.
           assert (Hk : (S k < Z.to_nat (φ d))%nat) by (rewrite <- HLl; apply nth_error_Some; congruence).
           rewrite HLn in Ha1, Hb1 by lia. injection Ha1 as <-. injection Hb1 as <-.
           set (m := Z.to_nat ((φ d) - 1 - Z.of_nat (S k))).
           assert (Ek : node k = anc (sP sf) (S m) t)
             by (unfold node, m; f_equal; lia).
           assert (Ek1 : node (S k) = anc (sP sf) m t) by reflexivity.
           destruct (Hnode k ltac:(lia)) as (_ & Hr1 & _).
           destruct (Hnode (S k) ltac:(lia)) as (_ & Hr2 & _).
           eapply msim_doublet; [exact Hr1 | exact Hr2 | |].
           ++ rewrite Ek, Ek1. apply (anc_msim xd cls s0 sf qf Hi t Rlt Hvt m). lia.
           ++ rewrite Ek, Ek1. apply (no_repeat xd cls s0 sf qf t Hi Rlt Hvt Hts m). lia.
        -- intros c' Hc'.
           pose proof (chain_ri s0 t a b c' Hs0 Ha Rlt Hbt Hab Hc') as Hr.
           pose proof (i_opt _ _ _ _ _ Hi t Rlt Hvt _ Hr) as O. unfold dist in O. fold d in O.
           destruct Hc' as (H0 & _).
           assert (0 < List.length c')%nat by (destruct c'; [discriminate | simpl; lia]).
           unfold len. rewrite HLl. lia.
Qed.

Lemma answer1_correct : forall xsrc a xtgt b, repr xsrc a -> repr xtgt b ->
  exists r, repr (answer1 xd n (N16 xd) cls hd cn wl wb wn xsrc xtgt) r /\
            answer dict a b r.
Proof.
  intros xsrc a xtgt b Ha Hb. unfold answer1. cbv zeta.
  destruct (lookup_spec xd wl wb wn xsrc Hw) as [[R0 Rn] | [R0 [Rlt Req]]].
  - rewrite R0, Uint63.eqb_refl. exists None. split; [exact I|].
    intros c (H0 & Hl & Hall & _).
    assert (Hin : In a dict) by (rewrite Forall_forall in Hall; apply Hall; eapply nth_error_In; exact H0).
    destruct (in_dict dict xd Hd a Hin) as (i & Hi & Hr).
    apply (Rn i Hi). apply (repr_eq _ _ _ _ Hr Ha). reflexivity.
  - assert (E : (lookup xd wb wn xsrc =? 0) = false) by (rewrite Uint63.eqb_false_spec; exact R0).
    rewrite E.
    set (s0 := lookup xd wb wn xsrc - 1) in *.
    assert (Has : repr xd.[s0] a) by (rewrite Req; exact Ha).
    destruct (PrimString.compare xsrc xtgt) eqn:Ec.
    + apply PString.compare_eq in Ec. subst xtgt.
      assert (Eab : a = b) by (apply (repr_eq _ _ _ _ Ha Hb); reflexivity). subst b.
      exists (Some [a]). split.
      * split.
        -- pose proof (lmk_s 1 xd.[s0] ltac:(change (φ 1) with 1%Z; lia)) as L1.
           etransitivity; [| exact (f_equal to_Z (eq_sym L1))]. reflexivity.
        -- intros k Hk. simpl in Hk. assert (k = 0%nat) by lia. subst k.
           exists a. split; [reflexivity|]. pose proof Has as H'.
           rewrite <- (gmk_s 1 (of_Z (Z.of_nat 0)) xd.[s0]) in H'. exact H'.
      * split; [split; [| split; [| split]] |].
        -- reflexivity.
        -- reflexivity.
        -- constructor; [| constructor]. destruct (mw_repr s0 Rlt) as [Hr Hin].
           replace a with (mw s0) by (apply (repr_eq _ _ _ _ Hr Has); reflexivity). exact Hin.
        -- intros k a1 b1 Ha1 Hb1. destruct k; discriminate.
        -- intros c' (H0 & _). destruct c'; [discriminate|]. unfold len. simpl. lia.
    + apply answer2_correct; [exact Rlt | exact Has | exact Hb |].
      rewrite Req. intro F. rewrite F, PString.compare_refl in Ec. discriminate.
    + apply answer2_correct; [exact Rlt | exact Has | exact Hb |].
      rewrite Req. intro F. rewrite F, PString.compare_refl in Ec. discriminate.
Qed.

End Query.

(* ------------------------------------------------------------------ *)
(* All the queries                                                     *)
(* ------------------------------------------------------------------ *)

Lemma qloop_eq : forall xd xs xt n N16 cls hd cn wl wb wn nq q out H,
  qloop xd xs xt n N16 cls hd cn wl wb wn nq q out H =
  match bdec (q <? nq) with
  | left Hq =>
      qloop xd xs xt n N16 cls hd cn wl wb wn nq (q + 1)
        out.[q <- answer1 xd n N16 cls hd cn wl wb wn xs.[q] xt.[q]]
        (Acc_inv H (dec_step nq q Hq))
  | right _ => out
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma qloop_spec : forall xd xs xt n N16 cls hd cn wl wb wn nq z q out H,
  gap nq q = z -> ((φ q) <= (φ nq))%Z -> PArray.length out = nq ->
  (forall k, ((φ k) < (φ q))%Z -> out.[k] = answer1 xd n N16 cls hd cn wl wb wn xs.[k] xt.[k]) ->
  let r := qloop xd xs xt n N16 cls hd cn wl wb wn nq q out H in
  PArray.length r = nq /\
  forall k, ((φ k) < (φ nq))%Z -> r.[k] = answer1 xd n N16 cls hd cn wl wb wn xs.[k] xt.[k].
Proof.
  intros xd xs xt n N16 cls hd cn wl wb wn nq z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros q out H Hz Hq Hl Hc r. subst r. rewrite qloop_eq.
  destruct (bdec (q <? nq)) as [Hlt | Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Hq1 : (φ (q + 1)) = ((φ q) + 1)%Z) by sia.
    apply IH with (y := gap nq (q + 1)); [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | lia | |].
    + rewrite lset_o. exact Hl.
    + intros k Hk. destruct (Z.eq_dec (φ q) (φ k)) as [E | E].
      * replace k with q by (apply to_Z_inj; exact E). apply gss_o. rewrite Hl. exact Hlt'.
      * rewrite gso_o by exact E. apply Hc. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
    split; [exact Hl|]. intros k Hk. apply Hc. lia.
Qed.

Lemma choice_list : forall {A} (P : nat -> A -> Prop) (d : A) N,
  (forall k, (k < N)%nat -> exists r, P k r) ->
  exists l, List.length l = N /\ forall k, (k < N)%nat -> P k (nth k l d).
Proof.
  intros A P d N. induction N as [| N IH]; intros H.
  - exists []. split; [reflexivity | intros k Hk; lia].
  - destruct (IH ltac:(intros k Hk; apply H; lia)) as (l & Hl & Hp).
    destruct (H N ltac:(lia)) as (r & Hr).
    exists (l ++ [r]). split; [rewrite length_app; simpl; lia|].
    intros k Hk. destruct (Nat.lt_ge_cases k N) as [Hk' | Hk'].
    + rewrite app_nth1 by lia. apply Hp. exact Hk'.
    + replace k with N by lia. rewrite app_nth2 by lia. rewrite Hl, Nat.sub_diag. exact Hr.
Qed.

Lemma Forall2_by_nth : forall {A B} (R : A -> B -> Prop) (l1 : list A) (l2 : list B) d1 d2,
  List.length l1 = List.length l2 ->
  (forall k, (k < List.length l1)%nat -> R (nth k l1 d1) (nth k l2 d2)) -> Forall2 R l1 l2.
Proof.
  intros A B R l1. induction l1 as [| x l1 IH]; intros l2 d1 d2 Hl Hk; destruct l2 as [| y l2];
    try (simpl in Hl; discriminate); constructor.
  - apply (Hk 0%nat). simpl. lia.
  - apply (IH l2 d1 d2); [simpl in Hl; lia|]. intros k Hk'. apply (Hk (S k)). simpl. lia.
Qed.

Lemma doublets_impl_correct :
  forall (dict src tgt : list string) (xd xs xt : array PrimString.string),
  valid_input dict src tgt -> repr xd dict -> repr xs src -> repr xt tgt ->
  exists o : list (option (list string)),
    repr (doublets_impl xd xs xt) o /\ doublets_spec dict src tgt o.
Proof.
  intros dict src tgt xd xs xt Hv Hd Hs Ht.
  destruct Hv as [Vd Vw _ Vq Vp _ _].
  pose proof (dict_len dict xd Hd) as HL0. unfold len in Vd, Vq, Vp.
  assert (HL : (φ (PArray.length@{Set} xd)) = Z.of_nat (List.length dict)) by exact HL0.
  assert (Hn : ((φ (PArray.length@{Set} xd)) <= 25143)%Z) by lia.
  assert (Hlen : forall i, ((φ i) < (φ (PArray.length@{Set} xd)))%Z ->
            (1 <= (φ (PrimString.length (PArray.get@{Set} xd i))) <= 16)%Z).
  { intros i Hi. destruct (dict_at dict xd Hd i ltac:(exact Hi)) as (a & Ha & Hr).
    rewrite Forall_forall in Vw. pose proof (Vw a (nth_error_In _ _ Ha)) as Hw.
    unfold slen in Hw. pose proof (repr_len _ _ Hr) as Hl1.
    assert (Hl2 : (φ (PrimString.length (PArray.get@{Set} xd i))) = Z.of_nat (String.length a)) by exact Hl1.
    lia. }
  pose proof (N16_val xd Hn) as HN.
  unfold doublets_impl. cbv zeta.
  (* the word table *)
  assert (W0 : WInv xd 0 (PArray.make@{Set} (PArray.length@{Set} xd) 0) (PArray.make@{Set} M_word 0)
                 (PArray.make@{Set} (PArray.length@{Set} xd) 0)).
  { split; [apply lmk; lia|]. split; [apply lmk; cbv; discriminate|].
    split; [apply lmk; lia|]. split; [apply Dec_make|].
    split; [intros h; rewrite gmk; lia|].
    intros y Hy. change (φ 0) with 0%Z in Hy. pose proof (to_Z_bounded y). lia. }
  pose proof (wbuild_spec xd _ 0 _ _ _ (Zwf_well_founded 0 (gap (PArray.length@{Set} xd) 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded (PArray.length@{Set} xd)); lia) W0) as W.
  cbv zeta in W.
  destruct (wbuild xd (PArray.length@{Set} xd) 0 _ _ _ _) as [[wl wb] wn] eqn:Ew. simpl in W.
  (* the classes *)
  assert (B0 : BInv xd 0 (PArray.make@{Set} (N16 xd) 0) (PArray.make@{Set} M_key 0) (PArray.make@{Set} (N16 xd) 0)
                 (PArray.make@{Set} (N16 xd) 0) (PArray.make@{Set} (N16 xd) 0)).
  { assert (LN : PArray.length (PArray.make@{Set} (N16 xd) 0) = N16 xd) by (apply lmk; lia).
    split; [exact LN|]. split; [apply lmk; cbv; discriminate|].
    split; [exact LN|]. split; [exact LN|]. split; [exact LN|].
    split; [apply Dec_make|]. split; [apply Dec_make|].
    split; [intros h; rewrite gmk; lia|]. split; [intros h; rewrite gmk; lia|].
    split; [intros y _ Hy; change (φ 0) with 0%Z in Hy; pose proof (to_Z_bounded y); lia|].
    split; [intros y _ Hy; change (φ 0) with 0%Z in Hy; pose proof (to_Z_bounded y); lia|].
    split; [intros y y' _ Hy; change (φ 0) with 0%Z in Hy; pose proof (to_Z_bounded y); lia|].
    intros c y. rewrite gmk. split.
    - intros F. exfalso. exact (inchain_nz _ _ F).
    - intros (_ & Hy & _). change (φ 0) with 0%Z in Hy. pose proof (to_Z_bounded y). lia. }
  pose proof (build_spec xd Hn _ 0 _ _ _ _ _ (Zwf_well_founded 0 (gap (N16 xd) 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; lia) B0) as F.
  cbv zeta in F. change (PArray.length@{Set} xd * 16) with (N16 xd).
  destruct (build xd (N16 xd) 0 _ _ _ _ _ _) as [[cls hd] cn] eqn:Eb. simpl in F.
  (* the queries *)
  pose proof (dict_len src xs Hs) as HLs0. pose proof (dict_len tgt xt Ht) as HLt.
  assert (HLs : (φ (PArray.length@{Set} xs)) = Z.of_nat (List.length src)) by exact HLs0.
  assert (Lo : PArray.length (PArray.make@{Set} (PArray.length@{Set} xs) (@None (array pstring))) = PArray.length@{Set} xs)
    by (apply lmk_o; lia).
  destruct (qloop_spec xd xs xt (PArray.length@{Set} xd) (N16 xd) cls hd cn wl wb wn (PArray.length@{Set} xs)
              _ 0 _ (Zwf_well_founded 0 (gap (PArray.length@{Set} xs) 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded (PArray.length@{Set} xs)); lia) Lo
              ltac:(intros k Hk; change (φ 0) with 0%Z in Hk; pose proof (to_Z_bounded k); lia))
    as (RL & RC).
  set (out := qloop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in *.
  assert (Hof : forall k, (k < List.length src)%nat -> (φ (of_Z (Z.of_nat k))) = Z.of_nat k).
  { intros k Hk. rewrite of_Z_spec. apply Z.mod_small. change wB with 9223372036854775808%Z.
    pose proof (len_bound _ xs). lia. }
  destruct (choice_list (fun k r => repr out.[of_Z (Z.of_nat k)] r /\
                          answer dict (nth k src EmptyString) (nth k tgt EmptyString) r)
              None (List.length src)) as (o & Ho & Hoc).
  { intros k Hk.
    destruct (dict_at src xs Hs (of_Z (Z.of_nat k)) ltac:(rewrite Hof by exact Hk; lia)) as (a & Ha & Hra).
    destruct (dict_at tgt xt Ht (of_Z (Z.of_nat k)) ltac:(rewrite Hof by exact Hk; lia)) as (b & Hb & Hrb).
    rewrite Hof, Nat2Z.id in Ha, Hb by exact Hk.
    destruct (answer1_correct dict xd cls hd cn wl wb wn Hd Hn Hlen W F _ a _ b Hra Hrb) as (r & Hr1 & Hr2).
    exists r. split.
    - rewrite RC by (rewrite Hof by exact Hk; lia). exact Hr1.
    - rewrite (nth_error_nth _ _ _ Ha), (nth_error_nth _ _ _ Hb). exact Hr2. }
  exists o. split.
  - split.
    + transitivity (φ (PArray.length out)); [rewrite Ho, RL; lia | reflexivity].
    + intros k Hk. exists (nth k o None). split.
      * apply nth_error_nth'. exact Hk.
      * rewrite Ho in Hk. exact (proj1 (Hoc k Hk)).
  - unfold doublets_spec.
    apply (Forall2_by_nth _ _ _ (EmptyString, EmptyString) None).
    + rewrite length_combine, Ho. lia.
    + intros k Hk. rewrite length_combine in Hk.
      rewrite combine_nth by lia. simpl. apply (Hoc k). lia.
Qed.

Definition doublets_correct :
  forall (dict src tgt : list string)
         (xd xs xt : array PrimString.string),
  valid_input dict src tgt -> repr xd dict -> repr xs src -> repr xt tgt ->
  exists o : list (option (list string)),
    repr (doublets xd xs xt) o /\ doublets_spec dict src tgt o
  := doublets_impl_correct.
