(* Executable implementation and its required termination dependencies.
   Correctness proofs are in shortestpath1_proofs.v. *)
(* Implementation of shortestpath1 (shortestpath1.spec): Dijkstra's
   algorithm with a binary min-heap (lazy deletion) over a CSR graph.

   Code.
   - CSR: [count_loop] counts the out-degree of every vertex into
     c.[u+1] (c of length n+1), [prefix_loop] turns c into the offsets
     off.[u] = number of edges whose source is < u, and [fill_loop] places
     edge k at slot off.[us k] + (its rank among the edges of source us k),
     through a copy of the offsets used as insertion cursors.
   - Heap: two parallel flat arrays hk (keys) and hv (vertices) of capacity
     m + 1 and a size; [sift_up] / [sift_down] swap linearly (both cells
     are read before the first set).  Lazy deletion: a relaxation pushes
     (new distance, v); a popped vertex is settled only if [done] says it
     is not settled yet.
   - [main] pops, settles, and [scan] relaxes the out-edges of the settled
     vertex; [out_loop] builds the array of options (INF -> None).

   Termination: every loop recurses on an erased [Acc (Zwf 0) _] proof.
   The measure of [main] is size + (sum of the out-degrees of the
   unsettled vertices), a Prop-side quantity: a pop removes one entry, and
   the scan of the edges of u pushes at most deg u entries while u leaves
   the sum.  No nat, no Z in the code. *)

From Shortestpath1.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.
Open Scope bool_scope.

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

Lemma lsr1_spec : forall x : int, (φ (x >> 1)) = ((φ x) / 2)%Z.
Proof. intros x. rewrite lsr_spec. reflexivity. Qed.

Lemma up_step : forall i : int,
  (0 <? i) = true -> Zwf 0 (φ ((i - 1) >> 1)) (φ i).
Proof.
  intros i H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  rewrite lsr1_spec. unfold Zwf.
  assert ((φ (i - 1)) = (φ i) - 1)%Z by sia. sia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Definition INF : int := 9223372036854775807.

(* c.[us.[k] + 1] += 1 for k = k0 .. m - 1 *)
Fixpoint count_loop (us : array int) (m k : int) (c : array int)
    (H : Acc (Zwf 0) (gap m k)) {struct H} : array int :=
  match bdec (k <? m) with
  | left Hk =>
      let u1 := us.[k] + 1 in
      count_loop us m (k + 1) (c.[u1 <- c.[u1] + 1])
        (Acc_inv H (dec_step m k Hk))
  | right _ => c
  end.

(* c.[i+1] += c.[i] for i = i0 .. n - 1 *)
Fixpoint prefix_loop (n i : int) (c : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi =>
      let a := c.[i] in
      let b := c.[i + 1] in
      prefix_loop n (i + 1) (c.[i + 1 <- b + a])
        (Acc_inv H (dec_step n i Hi))
  | right _ => c
  end.

(* edge k goes to slot pos.[us.[k]], which then moves one to the right *)
Fixpoint fill_loop (us vs ws : array int) (m k : int)
    (pos adj wt : array int)
    (H : Acc (Zwf 0) (gap m k)) {struct H} : array int * array int :=
  match bdec (k <? m) with
  | left Hk =>
      let u := us.[k] in
      let j := pos.[u] in
      fill_loop us vs ws m (k + 1) (pos.[u <- j + 1])
        (adj.[j <- vs.[k]]) (wt.[j <- ws.[k]])
        (Acc_inv H (dec_step m k Hk))
  | right _ => (adj, wt)
  end.

(* The binary heap: keys hk, vertices hv, parent of i is (i - 1) / 2. *)
Fixpoint sift_up (hk hv : array int) (i : int)
    (H : Acc (Zwf 0) (φ i)) {struct H} : array int * array int :=
  match bdec (0 <? i) with
  | left Hi =>
      let p := (i - 1) >> 1 in
      let ki := hk.[i] in
      let kp := hk.[p] in
      match bdec (ki <? kp) with
      | left _ =>
          let vi := hv.[i] in
          let vp := hv.[p] in
          sift_up (hk.[i <- kp].[p <- ki]) (hv.[i <- vp].[p <- vi]) p
            (Acc_inv H (up_step i Hi))
      | right _ => (hk, hv)
      end
  | right _ => (hk, hv)
  end.

(* the smaller child of i, l = 2 i + 1 being < sz *)
Definition child (hk : array int) (sz l : int) : int :=
  if (l + 1 <? sz) && (hk.[l + 1] <? hk.[l]) then l + 1 else l.

Lemma down_step : forall (hk : array int) (sz i : int),
  ((i + i + 1 <? sz) && (i <? i + i + 1)) = true ->
  Zwf 0 (gap sz (child hk sz (i + i + 1))) (gap sz i).
Proof.
  intros hk sz i H. apply andb_prop in H. destruct H as [H1 H2].
  rewrite ltb_spec in H1, H2. unfold child, Zwf, gap.
  destruct ((i + i + 1 + 1 <? sz) && (hk.[i + i + 1 + 1] <? hk.[i + i + 1])); sia.
Qed.

Fixpoint sift_down (hk hv : array int) (sz i : int)
    (H : Acc (Zwf 0) (gap sz i)) {struct H} : array int * array int :=
  let l := i + i + 1 in
  match bdec ((l <? sz) && (i <? l)) with
  | left Hl =>
      let c := child hk sz l in
      let ki := hk.[i] in
      let kc := hk.[c] in
      match bdec (kc <? ki) with
      | left _ =>
          let vi := hv.[i] in
          let vc := hv.[c] in
          sift_down (hk.[i <- kc].[c <- ki]) (hv.[i <- vc].[c <- vi]) sz c
            (Acc_inv H (down_step hk sz i Hl))
      | right _ => (hk, hv)
      end
  | right _ => (hk, hv)
  end.

(* remove the root of a heap of size sz > 0; the new size is sz - 1 *)
Definition pop (hk hv : array int) (sz : int) : array int * array int :=
  let sz' := sz - 1 in
  let k := hk.[sz'] in
  let v := hv.[sz'] in
  sift_down (hk.[0 <- k]) (hv.[0 <- v]) sz' 0 (Zwf_well_founded 0 _).

(* insert (k, v) into a heap of size sz; the new size is sz + 1 *)
Definition push (hk hv : array int) (sz k v : int) : array int * array int :=
  sift_up (hk.[sz <- k]) (hv.[sz <- v]) sz (Zwf_well_founded 0 _).

Record St := mkSt { st_dist : array int; st_hk : array int;
                    st_hv : array int; st_sz : int }.

(* relax the edges j = j0 .. hi - 1 of a vertex at distance du *)
Fixpoint scan (adj wt : array int) (du hi j : int) (dist hk hv : array int)
    (sz : int) (H : Acc (Zwf 0) (gap hi j)) {struct H} : St :=
  match bdec (j <? hi) with
  | left Hj =>
      let v := adj.[j] in
      let nd := du + wt.[j] in
      match bdec (nd <? dist.[v]) with
      | left _ =>
          let '(hk', hv') := push hk hv sz nd v in
          scan adj wt du hi (j + 1) (dist.[v <- nd]) hk' hv' (sz + 1)
            (Acc_inv H (dec_step hi j Hj))
      | right _ =>
          scan adj wt du hi (j + 1) dist hk hv sz
            (Acc_inv H (dec_step hi j Hj))
      end
  | right _ => mkSt dist hk hv sz
  end.

(* Prop-side measure of the main loop *)
Fixpoint sumf (f : Z -> Z) (k : nat) : Z :=
  match k with
  | O => 0%Z
  | S k => (sumf f k + f (Z.of_nat k))%Z
  end.

Definition deg (off : array int) (u : Z) : Z :=
  Z.max 0 ((φ (off.[of_Z (u + 1)])) - (φ (off.[of_Z u]))).

Definition pot (off done : array int) : Z :=
  sumf (fun u => if done.[of_Z u] =? 0 then deg off u else 0%Z)
       (Z.to_nat (φ (PArray.length done))).

Definition mu (off done : array int) (sz : int) : Z := ((φ sz) + pot off done)%Z.

Lemma sumf_nonneg : forall f k, (forall u, 0 <= f u)%Z -> (0 <= sumf f k)%Z.
Proof.
  intros f k Hf. induction k as [| k IH]; simpl; [lia|]. specialize (Hf (Z.of_nat k)). lia.
Qed.

Lemma pot_nonneg : forall off done, (0 <= pot off done)%Z.
Proof.
  intros off done. apply sumf_nonneg. intros u. unfold deg.
  destruct (done.[of_Z u] =? 0); lia.
Qed.

Lemma sumf_ext : forall f g k, (forall u, (0 <= u < Z.of_nat k)%Z -> f u = g u) ->
  sumf f k = sumf g k.
Proof.
  intros f g k. induction k as [| k IH]; intros Hfg; simpl; [reflexivity|].
  rewrite IH by (intros u Hu; apply Hfg; lia). rewrite Hfg by lia. reflexivity.
Qed.

(* f and g agree except at u < k *)
Lemma sumf_update : forall f g k u, (0 <= u < Z.of_nat k)%Z ->
  (forall v, (0 <= v < Z.of_nat k)%Z -> v <> u -> f v = g v) ->
  (sumf f k - sumf g k = f u - g u)%Z.
Proof.
  intros f g k. induction k as [| k IH]; intros u Hu Hfg; simpl in *; [lia|].
  destruct (Z.eq_dec u (Z.of_nat k)) as [E | E].
  - subst u. rewrite (sumf_ext f g k) by (intros v Hv; apply Hfg; lia). lia.
  - rewrite (Hfg (Z.of_nat k)) by lia.
    specialize (IH u ltac:(lia) ltac:(intros v Hv Hne; apply Hfg; lia)). lia.
Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma of_Z_small : forall z, (0 <= z < 9223372036854775808)%Z -> (φ (of_Z z)) = z.
Proof. intros z Hz. rewrite of_Z_spec. apply Z.mod_small. exact Hz. Qed.

Lemma pot_set_done : forall off done u,
  (u <? PArray.length done) = true -> (done.[u] =? 0) = true ->
  pot off (done.[u <- 1]) = (pot off done - deg off (φ u))%Z.
Proof.
  intros off done u Hu H0. unfold pot. rewrite alength_set.
  rewrite ltb_spec in Hu.
  pose proof (alength_bound done).
  pose proof (to_Z_bounded u).
  set (k := Z.to_nat (φ (PArray.length done))).
  match goal with |- sumf ?f k = (sumf ?g k - _)%Z =>
    assert (E := sumf_update g f k (φ u) ltac:(lia)) end.
  cbv beta in E.
  rewrite of_to_Z, H0, aget_set_same in E by (rewrite ltb_spec; lia).
  change (1 =? 0) with false in E.
  match type of E with ?P -> _ => enough (Hx : P) by (specialize (E Hx);
    change (if false then deg off (φ u) else 0%Z) with 0%Z in E; lia) end.
  intros v Hv Hne. rewrite aget_set_other; [reflexivity|].
  intros F. apply Hne. rewrite F, of_Z_small by lia. reflexivity.
Qed.

Lemma scan_size_aux : forall adj wt du hi z j dist hk hv sz H,
  gap hi j = z ->
  ((φ (st_sz (scan adj wt du hi j dist hk hv sz H)))
   <= (φ sz) + Z.max 0 (gap hi j))%Z.
Proof.
  intros adj wt du hi z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j dist hk hv sz H Hz. destruct H as [H]. simpl.
  destruct (bdec (j <? hi)) as [Hj | Hj].
  - pose proof (dec_step hi j Hj) as D. rewrite Hz in D.
    assert (Hz' : gap hi (j + 1) = (z - 1)%Z)
      by (rewrite ltb_spec in Hj; unfold gap in *; sia).
    assert (Hg : (gap hi j >= 1)%Z)
      by (pose proof Hj as Hj'; rewrite ltb_spec in Hj'; unfold gap; lia).
    destruct (bdec (du + wt.[j] <? dist.[adj.[j]])).
    + destruct (push hk hv sz (du + wt.[j]) adj.[j]) as [hk' hv'].
      eapply Z.le_trans; [apply (IH _ D); reflexivity |].
      rewrite Hz', <- Hz. unfold Zwf in D. pose proof (to_Z_bounded sz).
      assert ((φ (sz + 1)) <= (φ sz) + 1)%Z by sia. lia.
    + eapply Z.le_trans; [apply (IH _ D); reflexivity |].
      rewrite Hz', <- Hz. unfold Zwf in D. lia.
  - simpl. lia.
Qed.

Lemma scan_size : forall adj wt du hi j dist hk hv sz H,
  ((φ (st_sz (scan adj wt du hi j dist hk hv sz H)))
   <= (φ sz) + Z.max 0 (gap hi j))%Z.
Proof. intros. eapply scan_size_aux. reflexivity. Qed.

Lemma main_step1 : forall off done st u (r : St),
  (0 <? st_sz st) = true ->
  ((u <? PArray.length done) && (done.[u] =? 0)) = true ->
  ((φ (st_sz r)) <= (φ (st_sz st - 1)) + Z.max 0 (gap off.[u + 1] off.[u]))%Z ->
  Zwf 0 (mu off (done.[u <- 1]) (st_sz r)) (mu off done (st_sz st)).
Proof.
  intros off done st u r Hs Hu Hr.
  apply andb_prop in Hu. destruct Hu as [Hu H0].
  pose proof (pot_set_done off done u Hu H0) as E.
  pose proof (pot_nonneg off done). pose proof (pot_nonneg off (done.[u <- 1])).
  rewrite ltb_spec in Hu, Hs. pose proof (alength_bound done).
  assert (Hd : deg off (φ u) = Z.max 0 (gap off.[u + 1] off.[u])).
  { unfold deg, gap. rewrite of_to_Z.
    replace (of_Z ((φ u) + 1)) with (u + 1); [reflexivity|].
    apply to_Z_inj. rewrite of_Z_small by (pose proof (to_Z_bounded u); lia). sia. }
  unfold Zwf, mu. change (φ 0) with 0%Z in Hs.
  assert ((φ (st_sz st - 1)) = (φ (st_sz st)) - 1)%Z by sia.
  pose proof (to_Z_bounded (st_sz r)). lia.
Qed.

Lemma main_step2 : forall off done st,
  (0 <? st_sz st) = true ->
  Zwf 0 (mu off done (st_sz st - 1)) (mu off done (st_sz st)).
Proof.
  intros off done st Hs. rewrite ltb_spec in Hs. change (φ 0) with 0%Z in Hs.
  pose proof (pot_nonneg off done). unfold Zwf, mu.
  assert ((φ (st_sz st - 1)) = (φ (st_sz st)) - 1)%Z by sia. lia.
Qed.

Fixpoint main (off adj wt done : array int) (st : St)
    (H : Acc (Zwf 0) (mu off done (st_sz st))) {struct H} : array int :=
  match bdec (0 <? st_sz st) with
  | left Hs =>
      let u := (st_hv st).[0] in
      let '(hk1, hv1) := pop (st_hk st) (st_hv st) (st_sz st) in
      match bdec ((u <? PArray.length done) && (done.[u] =? 0)) with
      | left Hu =>
          let st2 := scan adj wt (st_dist st).[u] off.[u + 1] off.[u]
                       (st_dist st) hk1 hv1 (st_sz st - 1)
                       (Zwf_well_founded 0 _) in
          main off adj wt (done.[u <- 1]) st2
            (Acc_inv H (main_step1 off done st u st2 Hs Hu
              (scan_size adj wt _ _ _ _ _ _ _ _)))
      | right _ =>
          main off adj wt done (mkSt (st_dist st) hk1 hv1 (st_sz st - 1))
            (Acc_inv H (main_step2 off done st Hs))
      end
  | right _ => st_dist st
  end.

(* out.[v] := Some dist.[v], or None for INF, for v = v0 .. n - 1 *)
Fixpoint out_loop (dist : array int) (n v : int) (out : array (option int))
    (H : Acc (Zwf 0) (gap n v)) {struct H} : array (option int) :=
  match bdec (v <? n) with
  | left Hv =>
      let d := dist.[v] in
      out_loop dist n (v + 1)
        (out.[v <- if d =? INF then None else Some d])
        (Acc_inv H (dec_step n v Hv))
  | right _ => out
  end.

Definition dijkstra_impl (n : uint) (us vs ws : array uint) (s : uint)
    : array (option uint) :=
  let m := PArray.length us in
  let c := count_loop us m 0 (PArray.make (n + 1) 0)
             (Zwf_well_founded 0 _) in
  let off := prefix_loop n 0 c (Zwf_well_founded 0 _) in
  let '(adj, wt) := fill_loop us vs ws m 0 (PArray.copy off)
                      (PArray.make m 0) (PArray.make m 0)
                      (Zwf_well_founded 0 _) in
  let dist0 := (PArray.make n INF).[s <- 0] in
  let hk0 := PArray.make (m + 1) 0 in
  let hv0 := (PArray.make (m + 1) 0).[0 <- s] in
  let dist := main off adj wt (PArray.make n 0) (mkSt dist0 hk0 hv0 1)
                (Zwf_well_founded 0 _) in
  out_loop dist n 0 (PArray.make n None) (Zwf_well_founded 0 _).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition dijkstra : uint -> array uint -> array uint -> array uint -> uint ->
                      array (option uint) := dijkstra_impl.
