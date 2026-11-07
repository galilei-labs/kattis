(* Implementation of numbersetshard (numbersetshard.spec). *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf
  Znumtheory Relations.
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
  unfold Zwf, gap. pose proof (to_Z_bounded m). lia.
Qed.

Definition rmeas (rk : array int) (x : int) : Z := (wB - (φ (rk.[x])))%Z.

Lemma rdec : forall (rk : array int) (x z : int),
  (rk.[x] <? rk.[z]) = true -> Zwf 0 (rmeas rk z) (rmeas rk x).
Proof.
  intros rk x z H. rewrite ltb_spec in H.
  pose proof (to_Z_bounded rk.[z]). unfold Zwf, rmeas. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Sieve marking: cells j, j+i, ..., cnt - t of them, are set. *)
Fixpoint mark (c : array bool) (i cnt t j : int)
    (H : Acc (Zwf 0) (gap cnt t)) {struct H} : array bool :=
  match bdec (t <? cnt) with
  | left Ht => mark c.[j <- true] i cnt (t + 1) (j + i)
                 (Acc_inv H (dec_step cnt t Ht))
  | right _ => c
  end.

Definition mark_from (c : array bool) (w i : int) : array bool :=
  let s := i * i in
  let cnt := (w - s) / i + 1 in
  mark c i cnt 0 s (Zwf_well_founded 0 (gap cnt 0)).

(* Eratosthenes on c (length n = w + 1), from i on, while i * i <= w. *)
Fixpoint sieve (c : array bool) (w n i : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array bool :=
  match bdec (i <? n) with
  | left Hi =>
      if i * i <=? w then
        let c' := if c.[i] then c else mark_from c w i in
        sieve c' w n (i + 1) (Acc_inv H (dec_step n i Hi))
      else c
  | right _ => c
  end.

(* Find with path halving.  The rank test is always true on a valid
   forest; it is the termination argument. *)
Fixpoint find (par rk : array int) (x : int)
    (H : Acc (Zwf 0) (rmeas rk x)) {struct H} : int * array int :=
  let y := par.[x] in
  if y =? x then (x, par)
  else
    let z := par.[y] in
    match bdec (rk.[x] <? rk.[z]) with
    | left Hl => find par.[x <- z] rk z (Acc_inv H (rdec rk x z Hl))
    | right _ => (x, par)
    end.

(* Union by rank. *)
Definition union (par rk : array int) (u v : int) : array int * array int :=
  let (ru, par1) := find par rk u (Zwf_well_founded 0 (rmeas rk u)) in
  let (rv, par2) := find par1 rk v (Zwf_well_founded 0 (rmeas rk v)) in
  if ru =? rv then (par2, rk)
  else
    let ku := rk.[ru] in
    let kv := rk.[rv] in
    if ku <? kv then (par2.[ru <- rv], rk)
    else if kv <? ku then (par2.[rv <- ru], rk)
    else (par2.[ru <- rv], rk.[rv <- kv + 1]).

(* Union of the offsets o, o + q, o + 2q, ... (cnt - t links). *)
Fixpoint ulink (par rk : array int) (q cnt t o : int)
    (H : Acc (Zwf 0) (gap cnt t)) {struct H} : array int * array int :=
  match bdec (t <? cnt) with
  | left Ht =>
      let (par', rk') := union par rk o (o + q) in
      ulink par' rk' q cnt (t + 1) (o + q) (Acc_inv H (dec_step cnt t Ht))
  | right _ => (par, rk)
  end.

(* First offset o with q | a + o. *)
Definition first_off (a q : int) : int := (q - a mod q) mod q.

(* For every prime q in [q, n), link its multiples in [a, a + w]. *)
Fixpoint uprimes (c : array bool) (a w n : int) (par rk : array int) (q : int)
    (H : Acc (Zwf 0) (gap n q)) {struct H} : array int * array int :=
  match bdec (q <? n) with
  | left Hq =>
      let (par', rk') :=
        if c.[q] then (par, rk)
        else
          let o0 := first_off a q in
          ulink par rk q ((w - o0) / q) 0 o0
            (Zwf_well_founded 0 (gap ((w - o0) / q) 0)) in
      uprimes c a w n par' rk' (q + 1) (Acc_inv H (dec_step n q Hq))
  | right _ => (par, rk)
  end.

Fixpoint iota (par : array int) (n i : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi => iota par.[i <- i] n (i + 1) (Acc_inv H (dec_step n i Hi))
  | right _ => par
  end.

Fixpoint count (par : array int) (n o acc : int)
    (H : Acc (Zwf 0) (gap n o)) {struct H} : int :=
  match bdec (o <? n) with
  | left Ho => count par n (o + 1) (if par.[o] =? o then acc + 1 else acc)
                 (Acc_inv H (dec_step n o Ho))
  | right _ => acc
  end.

Definition numbersets_impl (x y z : uint) : uint :=
  let w := y - x in
  let n := w + 1 in
  let c := sieve (PArray.make n false) w n 2 (Zwf_well_founded 0 (gap n 2)) in
  let par0 := iota (PArray.make n 0) n 0 (Zwf_well_founded 0 (gap n 0)) in
  let rk0 := PArray.make n 0 in
  let (par, rk) := uprimes c x w n par0 rk0 z (Zwf_well_founded 0 (gap n z)) in
  count par n 0 0 (Zwf_well_founded 0 (gap n 0)).

(* ------------------------------------------------------------------ *)
(* Unfolding equations                                                 *)
(* ------------------------------------------------------------------ *)

Lemma mark_eq : forall c i cnt t j H,
  mark c i cnt t j H =
  match bdec (t <? cnt) with
  | left Ht => mark c.[j <- true] i cnt (t + 1) (j + i)
                 (Acc_inv H (dec_step cnt t Ht))
  | right _ => c
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma sieve_eq : forall c w n i H,
  sieve c w n i H =
  match bdec (i <? n) with
  | left Hi =>
      if i * i <=? w then
        let c' := if c.[i] then c else mark_from c w i in
        sieve c' w n (i + 1) (Acc_inv H (dec_step n i Hi))
      else c
  | right _ => c
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma find_eq : forall par rk x H,
  find par rk x H =
  let y := par.[x] in
  if y =? x then (x, par)
  else
    let z := par.[y] in
    match bdec (rk.[x] <? rk.[z]) with
    | left Hl => find par.[x <- z] rk z (Acc_inv H (rdec rk x z Hl))
    | right _ => (x, par)
    end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma ulink_eq : forall par rk q cnt t o H,
  ulink par rk q cnt t o H =
  match bdec (t <? cnt) with
  | left Ht =>
      let (par', rk') := union par rk o (o + q) in
      ulink par' rk' q cnt (t + 1) (o + q) (Acc_inv H (dec_step cnt t Ht))
  | right _ => (par, rk)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma uprimes_eq : forall c a w n par rk q H,
  uprimes c a w n par rk q H =
  match bdec (q <? n) with
  | left Hq =>
      let (par', rk') :=
        if c.[q] then (par, rk)
        else
          let o0 := first_off a q in
          ulink par rk q ((w - o0) / q) 0 o0
            (Zwf_well_founded 0 (gap ((w - o0) / q) 0)) in
      uprimes c a w n par' rk' (q + 1) (Acc_inv H (dec_step n q Hq))
  | right _ => (par, rk)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma iota_eq : forall par n i H,
  iota par n i H =
  match bdec (i <? n) with
  | left Hi => iota par.[i <- i] n (i + 1) (Acc_inv H (dec_step n i Hi))
  | right _ => par
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma count_eq : forall par n o acc H,
  count par n o acc H =
  match bdec (o <? n) with
  | left Ho => count par n (o + 1) (if par.[o] =? o then acc + 1 else acc)
                 (Acc_inv H (dec_step n o Ho))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* PROOFS *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alength_bound : forall {A} (t : array A), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros A t. pose proof (leb_length A t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma bget_set_same : forall (t : array bool) (i : int) (b : bool),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same bool t i b H). Qed.
Lemma bget_set_other : forall (t : array bool) (i j : int) (b : bool),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other bool t i j b H). Qed.
Lemma blength_set : forall (t : array bool) (i : int) (b : bool),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set bool t i b). Qed.
Lemma bget_make : forall (n i : int) (b : bool), (PArray.make n b).[i] = b.
Proof. intros. exact (get_make bool b n i). Qed.
Lemma blength_make : forall (n : int) (b : bool),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make bool n b). Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.
Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.
Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.
Lemma aget_make : forall (n i : int) (b : int), (PArray.make n b).[i] = b.
Proof. intros. exact (get_make int b n i). Qed.
Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma to_Z_inj_iff : forall x y : int, (φ x) = (φ y) <-> x = y.
Proof. intros x y; split; [apply to_Z_inj | intros ->; reflexivity]. Qed.

(* ------------------------------------------------------------------ *)
(* Sieve                                                               *)
(* ------------------------------------------------------------------ *)

Local Open Scope Z_scope.

(* m has a divisor d in [2, k) with d * d <= m. *)
Definition sv (k m : Z) : Prop := exists d, 2 <= d < k /\ d * d <= m /\ (d | m).
Definition svall (m : Z) : Prop := exists d, 2 <= d /\ d * d <= m /\ (d | m).

Lemma mark_spec : forall (n : Z) (i cnt : int) (s : Z) (z : Z) (t j : int)
    (c : array bool) (H : Acc (Zwf 0) (gap cnt t)),
  gap cnt t = z ->
  (φ (PArray.length c)) = n ->
  (φ t) <= (φ cnt) ->
  (φ j) = s + (φ t) * (φ i) ->
  0 <= s -> 
  (forall t', (φ t) <= t' < (φ cnt) -> s + t' * (φ i) < n) ->
  s + (φ cnt) * (φ i) < wB ->
  (φ (PArray.length (mark c i cnt t j H))) = n /\
  forall m : int, (φ m) < n ->
    ((mark c i cnt t j H).[m] = true <->
     c.[m] = true \/ exists t', (φ t) <= t' < (φ cnt) /\ (φ m) = s + t' * (φ i)).
Proof.
  intros n i cnt s z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros t j c H Hz Hl Ht Hj Hs Hb Hw.
  rewrite mark_eq.
  destruct (bdec (t <? cnt)%uint63) as [Hlt | Hlt].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    pose proof (to_Z_bounded t). pose proof (to_Z_bounded i).
    pose proof (to_Z_bounded j).
    assert (Ht1 : (φ (t + 1)) = (φ t) + 1) by sia.
    assert (Hjb : (φ j) < n) by (rewrite Hj; apply Hb; lia).
    assert (Hji : (φ (j + i)) = (φ j) + (φ i)).
    { assert (((φ t) + 1) * (φ i) <= (φ cnt) * (φ i)) by (apply Z.mul_le_mono_nonneg_r; lia).
      rewrite add_spec. apply Z.mod_small. lia. }
    assert (Hl' : (φ (PArray.length c.[j <- true])) = n)
      by (rewrite blength_set; exact Hl).
    destruct (IH (gap cnt (t + 1)%uint63) ltac:(rewrite <- Hz; apply dec_step; exact Hlt)
                 (t + 1)%uint63 (j + i)%uint63 (c.[j <- true])
                 (Acc_inv H (dec_step cnt t Hlt)) eq_refl
                 Hl' ltac:(lia)
                 ltac:(rewrite Hji, Hj, Ht1; ring) Hs
                 ltac:(intros t' Ht'; apply Hb; lia) Hw) as [IHl IHc].
    split; [exact IHl|].
    intros m Hm. rewrite IHc by exact Hm.
    destruct (Uint63.eqs j m) as [E | E].
    + subst m.
      assert (Hjl : (j <? PArray.length c)%uint63 = true) by (rewrite ltb_spec; lia).
      split; [intros _; right; exists (φ t); lia
             | intros _; left; exact (bget_set_same c j true Hjl)].
    + rewrite (bget_set_other c j m true E).
      rewrite Ht1. split.
      * intros [C | (t' & T1 & T2)]; [left; exact C | right; exists t'; split; [lia | exact T2]].
      * intros [C | (t' & T1 & T2)]; [left; exact C |].
        destruct (Z.eq_dec t' (φ t)) as [Et | Et].
        -- exfalso. apply E. apply to_Z_inj. rewrite Hj, T2, Et. reflexivity.
        -- right. exists t'. split; [lia | exact T2].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt.
    split; [exact Hl|].
    intros m Hm. split; [intros C; left; exact C|].
    intros [C | (t' & T1 & T2)]; [exact C | lia].
Qed.

Lemma mark_from_spec : forall (n : Z) (c : array bool) (w i : int),
  (φ (PArray.length c)) = n -> (φ w) + 1 = n -> n <= 4194304 ->
  2 <= (φ i) -> (φ i) * (φ i) <= (φ w) ->
  (φ (PArray.length (mark_from c w i))) = n /\
  forall m : int, (φ m) < n ->
    ((mark_from c w i).[m] = true <->
     c.[m] = true \/ ((φ i) * (φ i) <= (φ m) /\ ((φ i) | (φ m)))).
Proof.
  intros n c w i Hl Hw Hn Hi Hii.
  unfold mark_from.
  assert (Hs : (φ (i * i)) = (φ i) * (φ i)).
  { rewrite mul_spec. apply Z.mod_small. rewrite wB_val. nia. }
  assert (Hws : (φ (w - i * i)) = (φ w) - (φ i) * (φ i)) by (rewrite sub_spec, Hs; apply Z.mod_small; rewrite wB_val; lia).
  assert (Hc : (φ ((w - i * i) / i + 1)) = ((φ w) - (φ i) * (φ i)) / (φ i) + 1).
  { rewrite add_spec, div_spec, Hws. change (φ 1) with 1. apply Z.mod_small.
    pose proof (Z.div_le_upper_bound ((φ w) - (φ i) * (φ i)) (φ i) (φ w) ltac:(lia) ltac:(nia)).
    pose proof (Z.div_pos ((φ w) - (φ i) * (φ i)) (φ i) ltac:(lia) ltac:(lia)).
    rewrite wB_val. lia. }
  pose proof (Z.div_pos ((φ w) - (φ i) * (φ i)) (φ i) ltac:(lia) ltac:(lia)) as Hdp.
  pose proof (Z.mul_div_le ((φ w) - (φ i) * (φ i)) (φ i) ltac:(lia)) as Hdl.
  destruct (mark_spec n i ((w - i * i) / i + 1) ((φ i) * (φ i)) _ 0 (i * i) c
              (Zwf_well_founded 0 (gap ((w - i * i) / i + 1) 0)) eq_refl Hl)
    as [Ml Mc].
  - change (φ 0) with 0. lia.
  - change (φ 0) with 0. rewrite Hs. ring.
  - nia.
  - intros t' Ht'. change (φ 0) with 0 in Ht'. rewrite Hc in Ht'.
    assert (t' * (φ i) <= (((φ w) - (φ i)*(φ i))/(φ i)) * (φ i)) by (apply Z.mul_le_mono_nonneg_r; lia).
    lia.
  - rewrite Hc, wB_val. assert ((φ i) <= (φ w)) by nia.
    replace ((((φ w) - (φ i) * (φ i)) / (φ i) + 1) * (φ i)) with
      ((φ i) * (((φ w) - (φ i) * (φ i)) / (φ i)) + (φ i)) by ring.
    lia.
  - split; [exact Ml|].
    intros m Hm. rewrite Mc by exact Hm.
    change (φ 0) with 0. rewrite Hc.
    pose proof (to_Z_bounded m).
    split; intros [C | D]; try (left; exact C); right.
    + destruct D as (t' & T1 & T2). split; [nia|].
      exists ((φ i) + t'). lia.
    + destruct D as (D1 & k & Hk).
      exists (k - (φ i)). split; [|lia].
      split; [nia|].
      assert (k - (φ i) <= ((φ w) - (φ i) * (φ i)) / (φ i)); [|lia].
      apply Z.div_le_lower_bound; [lia|].
      replace ((φ i) * (k - (φ i))) with (k * (φ i) - (φ i) * (φ i)) by ring. lia.
Qed.

Lemma sv_full : forall k m,
  (forall d, 2 <= d -> d * d <= m -> d < k) -> (sv k m <-> svall m).
Proof.
  intros k m Hk. split.
  - intros (d & D1 & D2 & D3). exists d. split; [lia | split; assumption].
  - intros (d & D1 & D2 & D3). exists d. split; [split; [lia | apply Hk; lia] | split; assumption].
Qed.

Lemma sv_step : forall k m, 2 <= k ->
  (sv (k + 1) m <-> sv k m \/ (k * k <= m /\ (k | m))).
Proof.
  intros k m Hk. split.
  - intros (d & D1 & D2 & D3).
    destruct (Z.eq_dec d k) as [E | E].
    + subst d. right. split; assumption.
    + left. exists d. split; [lia | split; assumption].
  - intros [(d & D1 & D2 & D3) | (D2 & D3)].
    + exists d. split; [lia | split; assumption].
    + exists k. split; [lia | split; assumption].
Qed.

Lemma svall_prime : forall m, 2 <= m -> (svall m <-> ~ prime m).
Proof.
  intros m Hm. split.
  - intros (d & D1 & D2 & D3) Hp.
    destruct (prime_divisors m Hp d D3) as [E | [E | [E | E]]]; subst d; nia.
  - intros Hnp.
    destruct (not_prime_divide m ltac:(lia) Hnp) as (d & Hd & [e He]).
    destruct (Z_le_gt_dec (d * d) m) as [Hdd | Hdd].
    + exists d. split; [lia | split; [exact Hdd | exists e; exact He]].
    + assert (He1 : 2 <= e) by nia.
      assert (He2 : e < d) by nia.
      exists e. split; [lia | split; [nia | exists d; lia]].
Qed.

Lemma sieve_spec : forall (w nn : int), (φ nn) = (φ w) + 1 -> (φ nn) <= 4194303 ->
  forall (z : Z) (i : int) (c : array bool) (H : Acc (Zwf 0) (gap nn i)),
  gap nn i = z ->
  (φ (PArray.length c)) = (φ nn) -> 2 <= (φ i) ->
  (forall m : int, (φ m) < (φ nn) -> (c.[m] = true <-> sv (φ i) (φ m))) ->
  (φ (PArray.length (sieve c w nn i H))) = (φ nn) /\
  forall m : int, (φ m) < (φ nn) -> ((sieve c w nn i H).[m] = true <-> svall (φ m)).
Proof.
  intros w nn Hw Hn z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i c H Hz Hl Hi Hc.
  rewrite sieve_eq.
  destruct (bdec (i <? nn)%uint63) as [Hlt | Hlt].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Hii : (φ (i * i))%uint63 = (φ i) * (φ i)).
    { rewrite mul_spec. apply Z.mod_small. rewrite wB_val. nia. }
    destruct ((i * i <=? w)%uint63) eqn:Eii.
    + rewrite leb_spec, Hii in Eii. cbv zeta.
      assert (Hi1 : (φ (i + 1))%uint63 = (φ i) + 1) by sia.
      pose (c' := if c.[i] then c else mark_from c w i).
      assert (Hc' : (φ (PArray.length c')) = (φ nn) /\
                    forall m : int, (φ m) < (φ nn) -> (c'.[m] = true <-> sv ((φ i) + 1) (φ m))).
      { unfold c'. destruct (c.[i]) eqn:Ci.
        - split; [exact Hl|]. intros m Hm. rewrite Hc by exact Hm. rewrite sv_step by lia.
          split; [intros C; left; exact C|].
          intros [C | (D1 & D2)]; [exact C|].
          apply Hc in Ci; [|lia].
          destruct Ci as (d & E1 & E2 & E3).
          exists d. split; [lia | split; [nia | eapply Z.divide_trans; eassumption]].
        - destruct (mark_from_spec (φ nn) c w i Hl ltac:(lia) ltac:(lia) Hi Eii) as [Ml Mc].
          split; [exact Ml|]. intros m Hm. rewrite Mc, Hc, sv_step by lia. reflexivity. }
      destruct Hc' as [Hl' Hcc'].
      fold c'.
      apply (IH (gap nn (i + 1)%uint63)); [rewrite <- Hz; apply dec_step; exact Hlt
        | reflexivity | exact Hl' | lia | rewrite Hi1; exact Hcc'].
    + rewrite <- Bool.not_true_iff_false, leb_spec, Hii in Eii.
      split; [exact Hl|]. intros m Hm. rewrite Hc by exact Hm.
      apply sv_full. intros d D1 D2. nia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt.
    split; [exact Hl|]. intros m Hm. rewrite Hc by exact Hm.
    apply sv_full. intros d D1 D2. nia.
Qed.

(* The sieve of the program: c.[m] = false iff m is prime, on [2, w]. *)
Lemma sieve_prime : forall (w nn : int), (φ nn) = (φ w) + 1 -> (φ nn) <= 4194303 ->
  let c := sieve (PArray.make nn false) w nn 2 (Zwf_well_founded 0 (gap nn 2)) in
  forall m : int, 2 <= (φ m) <= (φ w) -> (c.[m] = false <-> prime (φ m)).
Proof.
  intros w nn Hw Hn c m Hm.
  assert (Hl : (φ (PArray.length (PArray.make nn false))) = (φ nn)).
  { rewrite blength_make.
    replace (nn <=? PArray.max_length)%uint63 with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  destruct (sieve_spec w nn Hw Hn _ 2 (PArray.make nn false)
              (Zwf_well_founded 0 (gap nn 2)) eq_refl Hl ltac:(change (φ 2) with 2; lia))
    as [_ Sc].
  - intros m' Hm'. rewrite bget_make. change (φ 2) with 2.
    split; [discriminate | intros (d & D & _); lia].
  - fold c in Sc. rewrite <- Bool.not_true_iff_false, Sc by lia.
    rewrite svall_prime by lia. split; [intros C; destruct (prime_dec (φ m)); tauto | tauto].
Qed.

(* ------------------------------------------------------------------ *)
(* Union-find: the forest invariant and the root relation              *)
(* ------------------------------------------------------------------ *)

Record Inv (n B : Z) (par rk : array int) : Prop := {
  inv_lp : (φ (PArray.length par)) = n;
  inv_lr : (φ (PArray.length rk)) = n;
  inv_par : forall x : int, (φ x) < n -> (φ (par.[x])) < n;
  inv_rank : forall x : int, (φ x) < n -> par.[x] <> x -> (φ (rk.[x])) < (φ (rk.[par.[x]]));
  inv_bound : forall x : int, (φ x) < n -> (φ (rk.[x])) <= B;
}.

Lemma Inv_mono : forall n B B' par rk, Inv n B par rk -> B <= B' -> Inv n B' par rk.
Proof.
  intros n B B' par rk [H1 H2 H3 H4 H5] HB. constructor; auto.
  intros x Hx. specialize (H5 x Hx). lia.
Qed.

(* x reaches the root r by parent links. *)
Inductive rt (par : array int) : int -> int -> Prop :=
| rt_root : forall x, par.[x] = x -> rt par x x
| rt_step : forall x r, par.[x] <> x -> rt par par.[x] r -> rt par x r.

Lemma rt_unique : forall par x r1, rt par x r1 -> forall r2, rt par x r2 -> r1 = r2.
Proof.
  intros par x r1 H. induction H as [x Hx | x r Hx Hr IH]; intros r2 H2.
  - destruct H2 as [x' Hx' | x' r' Hx' Hr']; [reflexivity | contradiction].
  - destruct H2 as [x' Hx' | x' r' Hx' Hr']; [contradiction | apply IH; exact Hr'].
Qed.

Lemma rt_is_root : forall par x r, rt par x r -> par.[r] = r.
Proof. intros par x r H. induction H; assumption. Qed.

Lemma rt_root_eq : forall par x r, par.[x] = x -> rt par x r -> r = x.
Proof. intros par x r Hx H. eapply rt_unique; [exact H | apply rt_root; exact Hx]. Qed.

Lemma rt_bound : forall n B par rk, Inv n B par rk ->
  forall x r, rt par x r -> (φ x) < n -> (φ r) < n.
Proof.
  intros n B par rk HI x r H. induction H as [x Hx | x r Hx Hr IH]; intros Hb.
  - exact Hb.
  - apply IH. apply (inv_par _ _ _ _ HI). exact Hb.
Qed.

Lemma rt_exists : forall n B par rk, Inv n B par rk ->
  forall x, (φ x) < n -> exists r, rt par x r.
Proof.
  intros n B par rk HI.
  assert (G : forall z x, rmeas rk x = z -> (φ x) < n -> exists r, rt par x r).
  { intro z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros x Hz Hx.
    destruct (Uint63.eqs par.[x] x) as [E | E].
    - exists x. apply rt_root. exact E.
    - pose proof (inv_rank _ _ _ _ HI x Hx E) as Hr.
      pose proof (to_Z_bounded rk.[par.[x]]).
      destruct (IH (rmeas rk par.[x])) with (x := par.[x]) as [r Hr'].
      + rewrite <- Hz. unfold Zwf, rmeas. lia.
      + reflexivity.
      + apply (inv_par _ _ _ _ HI). exact Hx.
      + exists r. apply rt_step; assumption. }
  intros x Hx. eapply G; [reflexivity | exact Hx].
Qed.

Definition S (par : array int) (x y : int) : Prop := exists r, rt par x r /\ rt par y r.

Lemma S_iff_root : forall par x y rx ry, rt par x rx -> rt par y ry ->
  (S par x y <-> rx = ry).
Proof.
  intros par x y rx ry Hx Hy. split.
  - intros (r & H1 & H2).
    rewrite (rt_unique _ _ _ Hx _ H1), (rt_unique _ _ _ Hy _ H2). reflexivity.
  - intros ->. exists ry. split; assumption.
Qed.

Lemma S_pres : forall n B par rk par',
  Inv n B par rk -> (forall y s, rt par y s -> rt par' y s) ->
  forall x y, (φ x) < n -> (φ y) < n -> (S par x y <-> S par' x y).
Proof.
  intros n B par rk par' HI Hp x y Hx Hy.
  destruct (rt_exists _ _ _ _ HI x Hx) as [rx Rx].
  destruct (rt_exists _ _ _ _ HI y Hy) as [ry Ry].
  rewrite (S_iff_root _ _ _ _ _ Rx Ry), (S_iff_root _ _ _ _ _ (Hp _ _ Rx) (Hp _ _ Ry)).
  reflexivity.
Qed.

Lemma S_trans : forall n B par rk, Inv n B par rk ->
  forall x y z, (φ y) < n -> S par x y -> S par y z -> S par x z.
Proof.
  intros n B par rk HI x y z Hy (r1 & A1 & A2) (r2 & B1 & B2).
  rewrite (rt_unique _ _ _ A2 _ B1) in A1. exists r2. split; assumption.
Qed.

Lemma S_sym : forall par x y, S par x y -> S par y x.
Proof. intros par x y (r & A1 & A2). exists r. split; assumption. Qed.

(* ------------------------------------------------------------------ *)
(* find                                                                *)
(* ------------------------------------------------------------------ *)

Lemma halve_pres : forall (par : array int) (x : int),
  (φ x) < (φ (PArray.length par)) -> par.[x] <> x ->
  forall y s, rt par y s -> rt (par.[x <- par.[par.[x]]]) y s.
Proof.
  intros par x Hxl Hx.
  assert (Hxl' : (x <? PArray.length par)%uint63 = true) by (rewrite ltb_spec; exact Hxl).
  set (par1 := par.[x <- par.[par.[x]]]).
  assert (Px : par1.[x] = par.[par.[x]]) by (apply aget_set_same; exact Hxl').
  assert (Po : forall y, x <> y -> par1.[y] = par.[y]) by (intros y E; apply aget_set_other; exact E).
  intros y s H. induction H as [y Hy | y s Hy Hs IH].
  - apply rt_root. rewrite Po; [exact Hy|]. intro E. subst y. contradiction.
  - destruct (Uint63.eqs x y) as [E | E].
    + subst y. set (y1 := par.[x]) in *.
      destruct (Uint63.eqs par.[y1] y1) as [E1 | E1].
      * apply rt_step.
        -- rewrite Px, E1. exact Hy.
        -- rewrite Px, E1. exact IH.
      * assert (Hxy1 : x <> y1) by (intro F; apply Hy; symmetry; exact F).
        assert (Py1 : par1.[y1] = par.[y1]) by (apply Po; exact Hxy1).
        assert (IH2 : rt par1 par.[y1] s).
        { inversion IH as [y' Hy' | y' s' Hy' Hs']; subst.
          - exfalso. rewrite Py1 in Hy'. contradiction.
          - rewrite Py1 in Hs'. exact Hs'. }
        destruct (Uint63.eqs par1.[x] x) as [E2 | E2].
        -- rewrite Px in E2. rewrite E2 in IH2. exact IH2.
        -- apply rt_step; [exact E2 | rewrite Px; exact IH2].
    + apply rt_step.
      * rewrite Po by exact E. exact Hy.
      * rewrite Po by exact E. exact IH.
Qed.

Lemma find_spec : forall n B (rk : array int) (z : Z) (par : array int) (x : int)
    (H : Acc (Zwf 0) (rmeas rk x)) r par',
  rmeas rk x = z -> Inv n B par rk -> (φ x) < n ->
  find par rk x H = (r, par') ->
  Inv n B par' rk /\ rt par x r /\ (forall y s, rt par y s -> rt par' y s) /\ (φ r) < n.
Proof.
  intros n B rk z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros par x H r par' Hz HI Hx Hf.
  rewrite find_eq in Hf. cbv zeta in Hf.
  destruct (par.[x] =? x)%uint63 eqn:E.
  - rewrite eqb_spec in E. injection Hf as <- <-.
    split; [exact HI | split; [apply rt_root; exact E | split; [auto | exact Hx]]].
  - assert (E' : par.[x] <> x) by (intro F; rewrite <- eqb_spec, E in F; discriminate).
    set (y := par.[x]) in *. set (z' := par.[y]) in *.
    assert (Hy : (φ y) < n) by (apply (inv_par _ _ _ _ HI); exact Hx).
    assert (Hz' : (φ z') < n) by (apply (inv_par _ _ _ _ HI); exact Hy).
    assert (Rxz : (φ (rk.[x])) < (φ (rk.[z']))).
    { pose proof (inv_rank _ _ _ _ HI x Hx E') as R1. fold y in R1.
      destruct (Uint63.eqs par.[y] y) as [E1 | E1].
      - unfold z'. rewrite E1. exact R1.
      - pose proof (inv_rank _ _ _ _ HI y Hy E1) as R2. fold z' in R2. lia. }
    destruct (bdec (rk.[x] <? rk.[z'])%uint63) as [Hl | Hl].
    2: { exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hl. lia. }
    assert (Hxz : z' <> x) by (intro F; rewrite F in Rxz; lia).
    assert (Hxl : (φ x) < (φ (PArray.length par))) by (rewrite (inv_lp _ _ _ _ HI); exact Hx).
    assert (Hxl' : (x <? PArray.length par)%uint63 = true) by (rewrite ltb_spec; exact Hxl).
    set (par1 := par.[x <- z']) in *.
    assert (Px : par1.[x] = z') by (apply aget_set_same; exact Hxl').
    assert (Po : forall y, x <> y -> par1.[y] = par.[y]) by (intros y0 E0; apply aget_set_other; exact E0).
    assert (HI1 : Inv n B par1 rk).
    { destruct HI as [I1 I2 I3 I4 I5]. constructor.
      - unfold par1. rewrite alength_set. exact I1.
      - exact I2.
      - intros x0 Hx0. destruct (Uint63.eqs x x0) as [E0 | E0].
        + subst x0. rewrite Px. exact Hz'.
        + rewrite Po by exact E0. apply I3. exact Hx0.
      - intros x0 Hx0 Hn0. destruct (Uint63.eqs x x0) as [E0 | E0].
        + subst x0. rewrite Px. exact Rxz.
        + rewrite Po in * by exact E0. apply I4; assumption.
      - exact I5. }
    assert (Hpres : forall y0 s, rt par y0 s -> rt par1 y0 s)
      by (apply halve_pres; [exact Hxl | exact E']).
    assert (Hw : Zwf 0 (rmeas rk z') z) by (rewrite <- Hz; exact (rdec rk x z' Hl)).
    destruct (IH (rmeas rk z') Hw par1 z' _ r par' eq_refl HI1 Hz' Hf)
      as (I' & R' & P' & B').
    split; [exact I'|].
    split.
    + destruct (rt_exists _ _ _ _ HI x Hx) as [s0 S0].
      assert (S1 : rt par1 x r) by (apply rt_step; [rewrite Px; exact Hxz | rewrite Px; exact R']).
      rewrite <- (rt_unique _ _ _ (Hpres _ _ S0) _ S1). exact S0.
    + split; [intros y0 s Hs; apply P', Hpres, Hs | exact B'].
Qed.

(* ------------------------------------------------------------------ *)
(* link and union                                                      *)
(* ------------------------------------------------------------------ *)

Definition relink (ru rv r : int) : int := if (r =? ru)%uint63 then rv else r.

Lemma link_rt : forall (par : array int) (ru rv : int),
  par.[ru] = ru -> par.[rv] = rv -> ru <> rv ->
  (φ ru) < (φ (PArray.length par)) ->
  forall x r, rt par x r -> rt (par.[ru <- rv]) x (relink ru rv r).
Proof.
  intros par ru rv Hu Hv Huv Hl.
  assert (Hl' : (ru <? PArray.length par)%uint63 = true) by (rewrite ltb_spec; exact Hl).
  set (par' := par.[ru <- rv]).
  assert (Pu : par'.[ru] = rv) by (apply aget_set_same; exact Hl').
  assert (Po : forall y, ru <> y -> par'.[y] = par.[y]) by (intros y E; apply aget_set_other; exact E).
  intros x r H. induction H as [x Hx | x r Hx Hr IH].
  - unfold relink. destruct (x =? ru)%uint63 eqn:E.
    + rewrite eqb_spec in E. subst x.
      apply rt_step; [rewrite Pu; intro F; apply Huv; symmetry; exact F|].
      rewrite Pu. apply rt_root. rewrite Po by exact Huv. exact Hv.
    + assert (E' : ru <> x) by (intro F; subst x; rewrite eqb_refl in E; discriminate).
      apply rt_root. rewrite Po by exact E'. exact Hx.
  - assert (E' : ru <> x) by (intro F; subst x; contradiction).
    apply rt_step; rewrite Po by exact E'; assumption.
Qed.

Lemma link_inv : forall n B B' (par rk rk' : array int) (ru rv : int),
  Inv n B par rk -> par.[ru] = ru -> par.[rv] = rv -> ru <> rv ->
  (φ ru) < n -> (φ rv) < n ->
  (φ (PArray.length rk')) = n ->
  (forall y, (φ y) < n -> (φ (rk.[y])) <= (φ (rk'.[y])) <= B') ->
  (forall y, y <> rv -> rk'.[y] = rk.[y]) ->
  (φ (rk'.[ru])) < (φ (rk'.[rv])) ->
  Inv n B' (par.[ru <- rv]) rk'.
Proof.
  intros n B B' par rk rk' ru rv HI Hu Hv Huv Hun Hvn Hl Hmono Hsame Hlt.
  destruct HI as [I1 I2 I3 I4 I5].
  assert (Hl' : (ru <? PArray.length par)%uint63 = true) by (rewrite ltb_spec; lia).
  assert (Pu : par.[ru <- rv].[ru] = rv) by (apply aget_set_same; exact Hl').
  assert (Po : forall y, ru <> y -> par.[ru <- rv].[y] = par.[y]) by (intros y E; apply aget_set_other; exact E).
  constructor.
  - rewrite alength_set. exact I1.
  - exact Hl.
  - intros x Hx. destruct (Uint63.eqs ru x) as [E | E].
    + subst x. rewrite Pu. exact Hvn.
    + rewrite Po by exact E. apply I3. exact Hx.
  - intros x Hx Hn. destruct (Uint63.eqs ru x) as [E | E].
    + subst x. rewrite Pu. exact Hlt.
    + rewrite Po in * by exact E.
      assert (Exv : x <> rv) by (intro F; subst x; contradiction).
      rewrite (Hsame x Exv).
      pose proof (I4 x Hx Hn). pose proof (Hmono (par.[x]) (I3 x Hx)). lia.
  - intros x Hx. apply Hmono. exact Hx.
Qed.

Lemma S_link : forall n B B' (par rk par' rk' : array int) (ru rv u v : int),
  Inv n B par rk -> Inv n B' par' rk' -> ru <> rv ->
  rt par u ru -> rt par v rv ->
  (forall x r, rt par x r -> rt par' x (relink ru rv r)) ->
  forall x y, (φ x) < n -> (φ y) < n ->
  (S par' x y <-> S par x y \/ (S par x u /\ S par v y) \/ (S par x v /\ S par u y)).
Proof.
  intros n B B' par rk par' rk' ru rv u v HI HI' Huv Ru Rv Hmap x y Hx Hy.
  destruct (rt_exists _ _ _ _ HI x Hx) as [rx Rx].
  destruct (rt_exists _ _ _ _ HI y Hy) as [ry Ry].
  rewrite (S_iff_root _ _ _ _ _ (Hmap _ _ Rx) (Hmap _ _ Ry)).
  rewrite (S_iff_root _ _ _ _ _ Rx Ry), (S_iff_root _ _ _ _ _ Rx Ru),
    (S_iff_root _ _ _ _ _ Rv Ry), (S_iff_root _ _ _ _ _ Rx Rv),
    (S_iff_root _ _ _ _ _ Ru Ry).
  unfold relink.
  destruct (rx =? ru)%uint63 eqn:E1; destruct (ry =? ru)%uint63 eqn:E2;
    rewrite ?eqb_spec in E1; rewrite ?eqb_spec in E2;
    try (assert (E1' : rx <> ru) by (intro F; subst rx; rewrite eqb_refl in E1; discriminate));
    try (assert (E2' : ry <> ru) by (intro F; subst ry; rewrite eqb_refl in E2; discriminate));
    subst; intuition congruence.
Qed.

Lemma union_spec : forall n B (par rk : array int) (u v : int) par' rk',
  Inv n B par rk -> B + 1 < wB -> (φ u) < n -> (φ v) < n ->
  union par rk u v = (par', rk') ->
  Inv n (B + 1) par' rk' /\
  forall x y, (φ x) < n -> (φ y) < n ->
  (S par' x y <-> S par x y \/ (S par x u /\ S par v y) \/ (S par x v /\ S par u y)).
Proof.
  intros n B par rk u v par' rk' HI HB Hu Hv Hun.
  unfold union in Hun.
  destruct (find par rk u _) as [ru par1] eqn:F1.
  destruct (find par1 rk v _) as [rv par2] eqn:F2.
  destruct (find_spec n B rk _ par u _ ru par1 eq_refl HI Hu F1) as (I1 & R1 & P1 & B1).
  destruct (find_spec n B rk _ par1 v _ rv par2 eq_refl I1 Hv F2) as (I2 & R2 & P2 & B2).
  assert (Ru : rt par2 u ru) by (apply P2, P1; exact R1).
  assert (Rv : rt par2 v rv) by (apply P2; exact R2).
  assert (P12 : forall y s, rt par y s -> rt par2 y s) by (intros; apply P2, P1; assumption).
  assert (Hpres : forall x y, (φ x) < n -> (φ y) < n -> (S par x y <-> S par2 x y))
    by (intros; apply (S_pres _ _ _ _ _ HI P12); assumption).
  assert (Gu : par2.[ru] = ru) by (eapply rt_is_root; exact Ru).
  assert (Gv : par2.[rv] = rv) by (eapply rt_is_root; exact Rv).
  assert (Hlr : (φ (PArray.length rk)) = n) by exact (inv_lr _ _ _ _ HI).
  assert (Hlp : (φ (PArray.length par2)) = n) by exact (inv_lp _ _ _ _ I2).
  pose proof (inv_bound _ _ _ _ I2 ru B1) as Bu.
  pose proof (inv_bound _ _ _ _ I2 rv B2) as Bv.
  pose proof (to_Z_bounded (rk.[ru])) as Zu. pose proof (to_Z_bounded (rk.[rv])) as Zv.
  assert (HSx : forall x y, (φ x) < n -> (φ y) < n ->
    (S par x y \/ (S par x u /\ S par v y) \/ (S par x v /\ S par u y) <->
     S par2 x y \/ (S par2 x u /\ S par2 v y) \/ (S par2 x v /\ S par2 u y))).
  { intros x y Hx Hy. rewrite !Hpres by assumption. reflexivity. }
  destruct (ru =? rv)%uint63 eqn:E.
  - rewrite eqb_spec in E. subst rv. injection Hun as <- <-.
    split; [eapply Inv_mono; [exact I2 | lia]|].
    intros x y Hx Hy. rewrite HSx by assumption.
    assert (Suv : S par2 u v) by (exists ru; split; assumption).
    split; [intros H; left; exact H|].
    intros [H | [[H1 H2] | [H1 H2]]]; [exact H | |].
    + eapply S_trans; [exact I2 | exact Hu | exact H1 |].
      eapply S_trans; [exact I2 | exact Hv | exact Suv | exact H2].
    + eapply S_trans; [exact I2 | exact Hv | exact H1 |].
      eapply S_trans; [exact I2 | exact Hu | apply S_sym; exact Suv | exact H2].
  - assert (E' : ru <> rv) by (intro F; subst rv; rewrite eqb_refl in E; discriminate).
    assert (Hlu : (φ ru) < (φ (PArray.length par2))) by lia.
    assert (Hlv : (φ rv) < (φ (PArray.length par2))) by lia.
    destruct (rk.[ru] <? rk.[rv])%uint63 eqn:L1.
    + rewrite ltb_spec in L1. injection Hun as <- <-.
      assert (I3 : Inv n B (par2.[ru <- rv]) rk).
      { apply (link_inv n B B par2 rk rk ru rv I2 Gu Gv E' B1 B2 Hlr).
        - intros y Hy. split; [lia | apply (inv_bound _ _ _ _ I2); exact Hy].
        - reflexivity.
        - exact L1. }
      split; [eapply Inv_mono; [exact I3 | lia]|].
      intros x y Hx Hy. rewrite HSx by assumption.
      exact (S_link n B B par2 rk _ rk ru rv u v I2 I3 E' Ru Rv
               (link_rt par2 ru rv Gu Gv E' Hlu) x y Hx Hy).
    + rewrite <- Bool.not_true_iff_false, ltb_spec in L1.
      destruct (rk.[rv] <? rk.[ru])%uint63 eqn:L2.
      * rewrite ltb_spec in L2. injection Hun as <- <-.
        assert (E'' : rv <> ru) by (intro F; apply E'; symmetry; exact F).
        assert (I3 : Inv n B (par2.[rv <- ru]) rk).
        { apply (link_inv n B B par2 rk rk rv ru I2 Gv Gu E'' B2 B1 Hlr).
          - intros y Hy. split; [lia | apply (inv_bound _ _ _ _ I2); exact Hy].
          - reflexivity.
          - exact L2. }
        split; [eapply Inv_mono; [exact I3 | lia]|].
        intros x y Hx Hy. rewrite HSx by assumption.
        rewrite (S_link n B B par2 rk _ rk rv ru v u I2 I3 E'' Rv Ru
               (link_rt par2 rv ru Gv Gu E'' Hlv) x y Hx Hy).
        split; intros [H0 | [H0 | H0]]; auto.
      * rewrite <- Bool.not_true_iff_false, ltb_spec in L2. injection Hun as <- <-.
        assert (Hrvl : (rv <? PArray.length rk)%uint63 = true) by (rewrite ltb_spec; lia).
        assert (K1 : (φ (rk.[rv] + 1))%uint63 = (φ (rk.[rv])) + 1).
        { rewrite add_spec. change (φ 1) with 1. apply Z.mod_small. lia. }
        assert (Kv : (rk.[rv <- (rk.[rv] + 1)%uint63]).[rv] = (rk.[rv] + 1)%uint63)
          by (apply aget_set_same; exact Hrvl).
        assert (Ko : forall y, rv <> y -> (rk.[rv <- (rk.[rv] + 1)%uint63]).[y] = rk.[y])
          by (intros y Ey; apply aget_set_other; exact Ey).
        assert (I3 : Inv n (B + 1) (par2.[ru <- rv]) (rk.[rv <- (rk.[rv] + 1)%uint63])).
        { apply (link_inv n B (B + 1) par2 rk _ ru rv I2 Gu Gv E' B1 B2).
          - rewrite alength_set. exact Hlr.
          - intros y Hy. destruct (Uint63.eqs rv y) as [Ey | Ey].
            + subst y. rewrite Kv, K1. lia.
            + rewrite Ko by exact Ey. pose proof (inv_bound _ _ _ _ I2 y Hy). lia.
          - intros y Ey. apply Ko. intro F; apply Ey; symmetry; exact F.
          - rewrite Kv, K1, Ko by (intro F; apply E'; symmetry; exact F). lia. }
        split; [exact I3|].
        intros x y Hx Hy. rewrite HSx by assumption.
        exact (S_link n B (B + 1) par2 rk _ _ ru rv u v I2 I3 E' Ru Rv
               (link_rt par2 ru rv Gu Gv E' Hlu) x y Hx Hy).
Qed.

(* ------------------------------------------------------------------ *)
(* Equivalence closures                                                *)
(* ------------------------------------------------------------------ *)

Notation crst := (clos_refl_sym_trans Z).

Lemma crst_mono : forall (D D' : Z -> Z -> Prop),
  (forall x y, D x y -> D' x y) -> forall x y, crst D x y -> crst D' x y.
Proof.
  intros D D' H x y Hc. induction Hc.
  - apply rst_step. apply H. assumption.
  - apply rst_refl.
  - apply rst_sym. assumption.
  - eapply rst_trans; eassumption.
Qed.

Lemma crst_iff : forall (D D' : Z -> Z -> Prop),
  (forall x y, D x y <-> D' x y) -> forall x y, crst D x y <-> crst D' x y.
Proof.
  intros D D' H x y. split; apply crst_mono; intros a b; apply H.
Qed.

Lemma crst_add : forall (D : Z -> Z -> Prop) u v x y,
  crst (fun a b => D a b \/ (a = u /\ b = v)) x y <->
  crst D x y \/ (crst D x u /\ crst D v y) \/ (crst D x v /\ crst D u y).
Proof.
  intros D u v x y. split.
  - intros H. induction H as [a b Hab | a | a b _ IH | a b c _ IH1 _ IH2].
    + destruct Hab as [Hab | [-> ->]].
      * left. apply rst_step. exact Hab.
      * right. left. split; apply rst_refl.
    + left. apply rst_refl.
    + destruct IH as [H1 | [[H1 H2] | [H1 H2]]].
      * left. apply rst_sym. exact H1.
      * right. right. split; apply rst_sym; assumption.
      * right. left. split; apply rst_sym; assumption.
    + destruct IH1 as [H1 | [[H1 H2] | [H1 H2]]];
      destruct IH2 as [K1 | [[K1 K2] | [K1 K2]]].
      * left. eapply rst_trans; eassumption.
      * right. left. split; [eapply rst_trans; eassumption | exact K2].
      * right. right. split; [eapply rst_trans; eassumption | exact K2].
      * right. left. split; [exact H1 | eapply rst_trans; eassumption].
      * right. left. split; [exact H1 | exact K2].
      * left. eapply rst_trans; [exact H1 | exact K2].
      * right. right. split; [exact H1 | eapply rst_trans; eassumption].
      * left. eapply rst_trans; [exact H1 | exact K2].
      * right. right. split; [exact H1 | exact K2].
  - assert (M : forall a b, crst D a b ->
                crst (fun a b => D a b \/ (a = u /\ b = v)) a b)
      by (apply crst_mono; intros a b Hab; left; exact Hab).
    assert (Euv : crst (fun a b => D a b \/ (a = u /\ b = v)) u v)
      by (apply rst_step; right; split; reflexivity).
    intros [H | [[H1 H2] | [H1 H2]]].
    + apply M. exact H.
    + eapply rst_trans; [apply M; exact H1 |].
      eapply rst_trans; [exact Euv | apply M; exact H2].
    + eapply rst_trans; [apply M; exact H1 |].
      eapply rst_trans; [apply rst_sym; exact Euv | apply M; exact H2].
Qed.

(* ------------------------------------------------------------------ *)
(* The edges: consecutive multiples of a prime q >= P in [A, A + W]    *)
(* ------------------------------------------------------------------ *)

Definition edge (A P W q o1 o2 : Z) : Prop :=
  prime q /\ P <= q /\ o2 = o1 + q /\ 0 <= o1 /\ o2 <= W /\ (q | A + o1).

Definition Dfin (A P W : Z) (o1 o2 : Z) : Prop := exists q, edge A P W q o1 o2.

(* The edges of the primes below q0, and those of q0 starting below o. *)
Definition Done (A P W q0 o : Z) (o1 o2 : Z) : Prop :=
  exists q, edge A P W q o1 o2 /\ (q < q0 \/ (q = q0 /\ o1 < o)).

Lemma cong_off : forall A q o0 o1, 0 < q -> (q | A + o1) -> (q | A + o0) ->
  0 <= o0 < q -> 0 <= o1 -> exists k, 0 <= k /\ o1 = o0 + k * q.
Proof.
  intros A q o0 o1 Hq H1 H0 Ho0 Ho1.
  assert (Hd : (q | o1 - o0)).
  { replace (o1 - o0) with ((A + o1) - (A + o0)) by ring. apply Z.divide_sub_r; assumption. }
  destruct Hd as [k Hk]. exists k. split; [|lia].
  destruct (Z_lt_le_dec k 0) as [Hk0 | Hk0]; [|exact Hk0].
  exfalso. assert (k * q <= - q) by nia. lia.
Qed.

Lemma Done_add : forall A P W q0 o,
  prime q0 -> P <= q0 -> (q0 | A + o) -> 0 <= o -> o + q0 <= W ->
  forall o1 o2, Done A P W q0 (o + q0) o1 o2 <-> Done A P W q0 o o1 o2 \/ (o1 = o /\ o2 = o + q0).
Proof.
  intros A P W q0 o Hp HP Hd Ho Hw o1 o2.
  pose proof (prime_ge_2 q0 Hp) as Hq2.
  split.
  - intros (q & Hq & [Hlt | [-> Hlt]]).
    + left. exists q. split; [exact Hq | left; exact Hlt].
    + destruct (Z_lt_le_dec o1 o) as [Hl | Hl].
      * left. exists q0. split; [exact Hq | right; split; [reflexivity | exact Hl]].
      * right. destruct Hq as (_ & _ & E2 & H0 & _ & Hd1).
        assert (Hd2 : (q0 | o1 - o)).
        { replace (o1 - o) with ((A + o1) - (A + o)) by ring. apply Z.divide_sub_r; assumption. }
        destruct Hd2 as [k Hk].
        assert (k = 0) by nia. subst k. split; lia.
  - intros [(q & Hq & [Hlt | [-> Hlt]]) | [-> ->]].
    + exists q. split; [exact Hq | left; exact Hlt].
    + exists q0. split; [exact Hq | right; split; [reflexivity | lia]].
    + exists q0. split; [| right; split; [reflexivity | lia]].
      exact (conj Hp (conj HP (conj eq_refl (conj Ho (conj Hw Hd))))).
Qed.

Lemma Done_start : forall A P W q0 o0, 0 <= o0 < q0 -> (q0 | A + o0) ->
  forall o1 o2, Done A P W q0 0 o1 o2 <-> Done A P W q0 o0 o1 o2.
Proof.
  intros A P W q0 o0 Ho Hd o1 o2. split.
  - intros (q & Hq & [Hlt | [-> Hlt]]).
    + exists q. split; [exact Hq | left; exact Hlt].
    + exfalso. destruct Hq as (_ & _ & _ & H0 & _). lia.
  - intros (q & Hq & [Hlt | [-> Hlt]]).
    + exists q. split; [exact Hq | left; exact Hlt].
    + exfalso. destruct Hq as (_ & _ & _ & H0 & _ & Hd1).
      destruct (cong_off A q0 o0 o1 ltac:(lia) Hd1 Hd Ho H0) as (k & Hk & E). nia.
Qed.

Lemma Done_end : forall A P W q0 o0, 0 <= o0 < q0 -> (q0 | A + o0) ->
  forall o1 o2, Done A P W q0 (o0 + (W - o0) / q0 * q0) o1 o2 <-> Done A P W (q0 + 1) 0 o1 o2.
Proof.
  intros A P W q0 o0 Ho Hd o1 o2. split.
  - intros (q & Hq & [Hlt | [E Hlt]]); exists q; split; try exact Hq; left; lia.
  - intros (q & Hq & [Hlt | [-> Hlt]]).
    + destruct (Z_lt_le_dec q q0) as [Hl | Hl].
      * exists q. split; [exact Hq | left; exact Hl].
      * assert (q = q0) by lia. subst q.
        exists q0. split; [exact Hq | right; split; [reflexivity|]].
        destruct Hq as (_ & _ & E2 & H0 & Hw & Hd1).
        destruct (cong_off A q0 o0 o1 ltac:(lia) Hd1 Hd Ho H0) as (k & Hk & E).
        assert (k + 1 <= (W - o0) / q0) by (apply Z.div_le_lower_bound; lia).
        assert ((k + 1) * q0 <= (W - o0) / q0 * q0) by (apply Z.mul_le_mono_nonneg_r; lia).
        lia.
    + exfalso. destruct Hq as (_ & _ & _ & H0 & _). lia.
Qed.

Lemma Done_skip : forall A P W q0, ~ prime q0 ->
  forall o1 o2, Done A P W q0 0 o1 o2 <-> Done A P W (q0 + 1) 0 o1 o2.
Proof.
  intros A P W q0 Hnp o1 o2. split.
  - intros (q & Hq & [Hlt | [E Hlt]]); exists q; split; try exact Hq; left; lia.
  - intros (q & Hq & [Hlt | [-> Hlt]]).
    + exists q. split; [exact Hq|]. left.
      destruct (Z.eq_dec q q0) as [-> | E]; [destruct Hq; contradiction | lia].
    + exfalso. destruct Hq as (_ & _ & _ & H0 & _). lia.
Qed.

Lemma Done_final : forall A P W q0, W < q0 ->
  forall o1 o2, Done A P W q0 0 o1 o2 <-> Dfin A P W o1 o2.
Proof.
  intros A P W q0 Hq0 o1 o2. split.
  - intros (q & Hq & _). exists q. exact Hq.
  - intros (q & Hq). exists q. split; [exact Hq|]. left.
    destruct Hq as (_ & _ & E2 & H0 & Hw & _). lia.
Qed.

Lemma Done_init : forall A P W o1 o2, ~ Done A P W P 0 o1 o2.
Proof.
  intros A P W o1 o2 (q & Hq & [Hlt | [-> Hlt]]);
    destruct Hq as (_ & HP & _ & H0 & _); lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The linking loops                                                   *)
(* ------------------------------------------------------------------ *)

Definition Corr (n : Z) (par : array int) (R : Z -> Z -> Prop) : Prop :=
  forall x y : int, (φ x) < n -> (φ y) < n -> (S par x y <-> R (φ x) (φ y)).

Lemma Corr_iff : forall n par (R R' : Z -> Z -> Prop),
  (forall a b, R a b <-> R' a b) -> Corr n par R -> Corr n par R'.
Proof.
  intros n par R R' H HC x y Hx Hy. rewrite <- H. apply HC; assumption.
Qed.

Lemma Corr_union : forall n B (par rk par' rk' : array int) (u v : int) (D : Z -> Z -> Prop),
  Inv n B par rk -> B + 1 < wB -> (φ u) < n -> (φ v) < n ->
  Corr n par (crst D) ->
  union par rk u v = (par', rk') ->
  Inv n (B + 1) par' rk' /\
  Corr n par' (crst (fun a b => D a b \/ (a = (φ u) /\ b = (φ v)))).
Proof.
  intros n B par rk par' rk' u v D HI HB Hu Hv HC Hun.
  destruct (union_spec n B par rk u v par' rk' HI HB Hu Hv Hun) as [I' HS].
  split; [exact I'|].
  intros x y Hx Hy. rewrite HS by assumption. rewrite crst_add.
  unfold Corr in HC. rewrite !HC by assumption. reflexivity.
Qed.

Lemma ulink_spec : forall (n A P W Bq : Z) (q cnt : int) (o0 : Z),
  n = W + 1 -> n <= 4194303 -> prime (φ q) -> P <= (φ q) -> ((φ q) | A + o0) ->
  0 <= o0 < (φ q) -> (φ cnt) = (W - o0) / (φ q) -> 0 <= Bq -> Bq + n + 1 < wB ->
  forall (z : Z) (t o : int) (par rk : array int) (H : Acc (Zwf 0) (gap cnt t)) par' rk',
  gap cnt t = z -> (φ t) <= (φ cnt) -> (φ o) = o0 + (φ t) * (φ q) ->
  Inv n (Bq + (φ t)) par rk -> Corr n par (crst (Done A P W (φ q) (φ o))) ->
  ulink par rk q cnt t o H = (par', rk') ->
  Inv n (Bq + (φ cnt)) par' rk' /\
  Corr n par' (crst (Done A P W (φ q) (o0 + (φ cnt) * (φ q)))).
Proof.
  intros n A P W Bq q cnt o0 Hn Hnb Hp HP Hd Ho0 Hc HB0 HB z.
  pose proof (prime_ge_2 _ Hp) as Hq2.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros t o par rk H par' rk' Hz Ht Ho HI HC Hf.
  rewrite ulink_eq in Hf.
  destruct (bdec (t <? cnt)%uint63) as [Hlt | Hlt].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    pose proof (to_Z_bounded t) as Bt.
    assert (Ht1 : (φ (t + 1))%uint63 = (φ t) + 1) by sia.
    assert (Hcq : (φ cnt) * (φ q) <= W - o0).
    { rewrite Hc. rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
    assert (Htq : ((φ t) + 1) * (φ q) <= (φ cnt) * (φ q)) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (Hoq : (φ (o + q))%uint63 = (φ o) + (φ q)).
    { rewrite add_spec. apply Z.mod_small. pose proof (to_Z_bounded o). rewrite wB_val. lia. }
    assert ((φ cnt) <= (φ cnt) * (φ q)) by (pose proof (to_Z_bounded cnt); nia).
    assert (Hcn : (φ cnt) < n) by lia.
    destruct (union par rk o (o + q)%uint63) as [p1 r1] eqn:U.
    assert (Hdo : ((φ q) | A + (φ o))).
    { rewrite Ho. replace (A + (o0 + (φ t) * (φ q))) with ((A + o0) + (φ t) * (φ q)) by ring.
      apply Z.divide_add_r; [exact Hd | apply Z.divide_mul_r, Z.divide_refl]. }
    destruct (Corr_union n (Bq + (φ t)) par rk p1 r1 o (o + q)%uint63 _ HI ltac:(lia)
                ltac:(lia) ltac:(lia) HC U) as [I1 C1].
    assert (C2 : Corr n p1 (crst (Done A P W (φ q) ((φ (o + q))%uint63)))).
    { eapply Corr_iff; [| exact C1].
      intros a b. rewrite Hoq. apply crst_iff. intros a' b'.
      rewrite Done_add by (try assumption; lia). reflexivity. }
    eapply (IH (gap cnt (t + 1)%uint63)); [rewrite <- Hz; apply dec_step; exact Hlt
      | reflexivity | lia | rewrite Hoq, Ho, Ht1; ring
      | rewrite Ht1, Z.add_assoc; exact I1 | exact C2 | exact Hf].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt.
    injection Hf as <- <-.
    assert (Et : (φ t) = (φ cnt)) by lia.
    split; [rewrite <- Et; exact HI|].
    rewrite <- Et, <- Ho. exact HC.
Qed.

Lemma first_off_math : forall A Q, 0 < Q ->
  0 <= (Q - A mod Q) mod Q < Q /\ (Q | A + (Q - A mod Q) mod Q).
Proof.
  intros A Q HQ. split; [apply Z.mod_pos_bound; exact HQ|].
  apply Z.mod_divide; [lia|].
  rewrite Zplus_mod_idemp_r.
  replace (A + (Q - A mod Q)) with ((A / Q + 1) * Q)
    by (rewrite (Z.mod_eq A Q) by lia; ring).
  apply Z.mod_mul. lia.
Qed.

Lemma first_off_spec : forall a q : int, 0 < (φ q) ->
  (φ (first_off a q)) = ((φ q) - (φ a) mod (φ q)) mod (φ q).
Proof.
  intros a q Hq. unfold first_off.
  rewrite mod_spec, sub_spec, mod_spec.
  pose proof (Z.mod_pos_bound (φ a) (φ q) Hq).
  pose proof (to_Z_bounded q).
  rewrite (Z.mod_small ((φ q) - (φ a) mod (φ q)) wB) by lia. reflexivity.
Qed.

Lemma uprimes_spec : forall (c : array bool) (a w nn : int) (A P W n : Z),
  (φ a) = A -> (φ w) = W -> (φ nn) = n -> n = W + 1 -> n <= 4194303 -> 0 <= W -> 2 <= P ->
  (forall m : int, 2 <= (φ m) <= W -> (c.[m] = false <-> prime (φ m))) ->
  forall (zz : Z) (q : int) (par rk : array int) (H : Acc (Zwf 0) (gap nn q)) par' rk',
  gap nn q = zz -> P <= (φ q) -> Inv n ((φ q) * n) par rk ->
  Corr n par (crst (Done A P W (φ q) 0)) ->
  uprimes c a w nn par rk q H = (par', rk') ->
  (exists B, Inv n B par' rk') /\ Corr n par' (crst (Dfin A P W)).
Proof.
  intros c a w nn A P W n Ha Hw Hnn Hn Hnb HW HP Hc zz.
  induction zz as [zz IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros q par rk H par' rk' Hz Hq HI HC Hf.
  rewrite uprimes_eq in Hf.
  destruct (bdec (q <? nn)%uint63) as [Hlt | Hlt].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Hq1 : (φ (q + 1))%uint63 = (φ q) + 1) by sia.
    assert (Hdec : Zwf 0 (gap nn (q + 1)%uint63) zz) by (rewrite <- Hz; apply dec_step; exact Hlt).
    destruct (c.[q]) eqn:Cq.
    + assert (Hnp : ~ prime (φ q)).
      { intro Hp. apply (Hc q ltac:(lia)) in Hp. rewrite Hp in Cq. discriminate. }
      cbv beta iota in Hf.
      eapply (IH _ Hdec (q + 1)%uint63); [reflexivity | lia | | | exact Hf].
      * eapply Inv_mono; [exact HI|]. rewrite Hq1.
        replace (((φ q) + 1) * n) with ((φ q) * n + n) by ring. lia.
      * eapply Corr_iff; [| exact HC]. intros a0 b0. rewrite Hq1.
        apply crst_iff. intros a' b'. apply Done_skip. exact Hnp.
    + assert (Hp : prime (φ q)) by (apply (Hc q ltac:(lia)); exact Cq).
      pose proof (prime_ge_2 _ Hp) as Hq2.
      cbv beta iota zeta in Hf.
      destruct (ulink par rk q ((w - first_off a q) / q) 0 (first_off a q)
                  (Zwf_well_founded 0 (gap ((w - first_off a q) / q) 0))) as [p1 r1] eqn:U.
      set (o0 := ((φ q) - A mod (φ q)) mod (φ q)).
      destruct (first_off_math A (φ q) ltac:(lia)) as [Ho0 Hd0]. fold o0 in Ho0, Hd0.
      assert (Ho : (φ (first_off a q)) = o0) by (rewrite first_off_spec, Ha by lia; reflexivity).
      assert (Hcnt : (φ ((w - first_off a q) / q))%uint63 = (W - o0) / (φ q)).
      { rewrite div_spec, sub_spec, Ho, Hw. rewrite Z.mod_small; [reflexivity|].
        pose proof (to_Z_bounded w). lia. }
      assert (B1 : 0 <= (φ q) * n) by (apply Z.mul_nonneg_nonneg; lia).
      assert (B2 : (φ q) * n + n + 1 < wB).
      { rewrite wB_val. assert ((φ q) * n <= 4194303 * 4194303) by (apply Z.mul_le_mono_nonneg; lia). lia. }
      assert (T1 : (φ 0) <= (φ ((w - first_off a q) / q))%uint63)
        by (change (φ 0) with 0; rewrite Hcnt; apply Z.div_pos; lia).
      assert (T2 : (φ (first_off a q)) = o0 + (φ 0) * (φ q)) by (change (φ 0) with 0; lia).
      assert (T3 : Inv n ((φ q) * n + (φ 0)) par rk) by (change (φ 0) with 0; rewrite Z.add_0_r; exact HI).
      assert (T4 : Corr n par (crst (Done A P W (φ q) (φ (first_off a q))))).
      { rewrite Ho. eapply Corr_iff; [| exact HC].
        intros a0 b0; apply crst_iff; intros a' b'; apply Done_start; assumption. }
      destruct (ulink_spec n A P W ((φ q) * n) q _ o0 Hn Hnb Hp Hq Hd0 Ho0 Hcnt
                  B1 B2 _ 0 (first_off a q) par rk _ p1 r1 eq_refl T1 T2 T3 T4 U) as [I1 C1].
      eapply (IH _ Hdec (q + 1)%uint63); [reflexivity | lia | | | exact Hf].
      * eapply Inv_mono; [exact I1|]. rewrite Hq1, Hcnt.
        assert ((W - o0) / (φ q) <= W - o0).
        { apply Z.div_le_upper_bound; [lia|].
          rewrite <- (Z.mul_1_l (W - o0)) at 1. apply Z.mul_le_mono_nonneg_r; lia. }
        replace (((φ q) + 1) * n) with ((φ q) * n + n) by ring. lia.
      * eapply Corr_iff; [| exact C1]. intros a0 b0. rewrite Hq1, Hcnt.
        apply crst_iff. intros a' b'. apply Done_end; assumption.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt.
    injection Hf as <- <-.
    split; [exists ((φ q) * n); exact HI|].
    eapply Corr_iff; [| exact HC]. intros a0 b0.
    apply crst_iff. intros a' b'. apply Done_final. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Initial forest and the count                                        *)
(* ------------------------------------------------------------------ *)

Lemma iota_spec : forall (nn : int), (φ nn) <= 4194303 ->
  forall (z : Z) (i : int) (par : array int) (H : Acc (Zwf 0) (gap nn i)),
  gap nn i = z -> (φ (PArray.length par)) = (φ nn) -> (φ i) <= (φ nn) ->
  (forall x : int, (φ x) < (φ i) -> par.[x] = x) ->
  (φ (PArray.length (iota par nn i H))) = (φ nn) /\
  forall x : int, (φ x) < (φ nn) -> (iota par nn i H).[x] = x.
Proof.
  intros nn Hnn z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i par H Hz Hl Hi Hc.
  rewrite iota_eq.
  destruct (bdec (i <? nn)%uint63) as [Hlt | Hlt].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Hi1 : (φ (i + 1))%uint63 = (φ i) + 1) by sia.
    assert (Hil : (i <? PArray.length par)%uint63 = true) by (rewrite ltb_spec; lia).
    apply (IH (gap nn (i + 1)%uint63)); [rewrite <- Hz; apply dec_step; exact Hlt
      | reflexivity | rewrite alength_set; exact Hl | lia |].
    intros x Hx. rewrite Hi1 in Hx.
    destruct (Uint63.eqs i x) as [E | E].
    + subst x. apply aget_set_same. exact Hil.
    + rewrite aget_set_other by exact E. apply Hc.
      assert ((φ x) <> (φ i)) by (intro F; apply E; apply to_Z_inj; symmetry; exact F). lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt.
    split; [exact Hl|]. intros x Hx. apply Hc. lia.
Qed.

(* The representatives: a + o for the roots o < k, in increasing order. *)
Fixpoint rl (par : array int) (A : Z) (k : nat) : list N :=
  match k with
  | O => []
  | Datatypes.S k' =>
      rl par A k' ++
      (if (par.[of_Z (Z.of_nat k')] =? of_Z (Z.of_nat k'))%uint63
       then [Z.to_N (A + Z.of_nat k')] else [])
  end.

Lemma rl_length : forall par A k, (List.length (rl par A k) <= k)%nat.
Proof.
  intros par A k. induction k as [| k IH]; [simpl; lia|].
  simpl. rewrite length_app.
  destruct (par.[of_Z (Z.of_nat k)] =? of_Z (Z.of_nat k))%uint63; simpl; lia.
Qed.

Lemma rl_In : forall par A k v,
  In v (rl par A k) <->
  exists j : nat, (j < k)%nat /\ par.[of_Z (Z.of_nat j)] = of_Z (Z.of_nat j) /\
                  v = Z.to_N (A + Z.of_nat j).
Proof.
  intros par A k v. induction k as [| k IH].
  - simpl. split; [tauto | intros (j & Hj & _); lia].
  - simpl. rewrite in_app_iff, IH.
    destruct (par.[of_Z (Z.of_nat k)] =? of_Z (Z.of_nat k))%uint63 eqn:E.
    + rewrite eqb_spec in E. simpl. split.
      * intros [(j & Hj & H1 & H2) | [H | []]].
        -- exists j. split; [lia | split; assumption].
        -- exists k. split; [lia | split; [exact E | symmetry; exact H]].
      * intros (j & Hj & H1 & H2).
        destruct (Nat.eq_dec j k) as [-> | Ne].
        -- right. left. symmetry. exact H2.
        -- left. exists j. split; [lia | split; assumption].
    + simpl. split.
      * intros [(j & Hj & H1 & H2) | []]. exists j. split; [lia | split; assumption].
      * intros (j & Hj & H1 & H2). left.
        destruct (Nat.eq_dec j k) as [-> | Ne].
        -- rewrite H1, eqb_refl in E. discriminate.
        -- exists j. split; [lia | split; assumption].
Qed.

Lemma rl_NoDup : forall par A k, 0 <= A -> NoDup (rl par A k).
Proof.
  intros par A k HA. induction k as [| k IH]; [constructor|].
  simpl. apply NoDup_app; [exact IH | |].
  - destruct (_ =? _)%uint63; [apply NoDup_cons; [intros []|constructor] | constructor].
  - intros v Hv Hv'. apply rl_In in Hv. destruct Hv as (j & Hj & _ & ->).
    destruct (_ =? _)%uint63; [|destruct Hv'].
    destruct Hv' as [E | []]. lia.
Qed.

Lemma count_spec : forall (par : array int) (nn : int) (A : Z), (φ nn) <= 4194303 ->
  forall (z : Z) (o acc : int) (H : Acc (Zwf 0) (gap nn o)),
  gap nn o = z -> (φ o) <= (φ nn) ->
  (φ acc) = Z.of_nat (List.length (rl par A (Z.to_nat (φ o)))) ->
  (φ (count par nn o acc H)) = Z.of_nat (List.length (rl par A (Z.to_nat (φ nn)))).
Proof.
  intros par nn A Hnn z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros o acc H Hz Ho Hacc.
  rewrite count_eq.
  destruct (bdec (o <? nn)%uint63) as [Hlt | Hlt].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    pose proof (to_Z_bounded o) as Bo.
    assert (Ho1 : (φ (o + 1))%uint63 = (φ o) + 1) by sia.
    apply (IH (gap nn (o + 1)%uint63)); [rewrite <- Hz; apply dec_step; exact Hlt
      | reflexivity | lia |].
    rewrite Ho1, Z2Nat.inj_add, Nat.add_1_r by lia. simpl.
    rewrite Z2Nat.id by lia. rewrite of_to_Z, length_app.
    pose proof (rl_length par A (Z.to_nat (φ o))).
    destruct (par.[o] =? o)%uint63; simpl.
    + rewrite add_spec, Hacc. change (φ 1) with 1. rewrite Z.mod_small; [lia|].
      rewrite wB_val. lia.
    + rewrite Hacc. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt.
    replace (φ nn) with (φ o) by lia. exact Hacc.
Qed.

(* ------------------------------------------------------------------ *)
(* From the edges to the statement's merges                            *)
(* ------------------------------------------------------------------ *)

Lemma ndiv_zdiv : forall q m : N, N.divide q m -> (Z.of_N q | Z.of_N m).
Proof. intros q m [k Hk]. exists (Z.of_N k). rewrite Hk. lia. Qed.

Lemma zdiv_ndiv : forall q m : Z, 0 < q -> 0 <= m -> (q | m) -> N.divide (Z.to_N q) (Z.to_N m).
Proof.
  intros q m Hq Hm [k Hk]. exists (Z.to_N k).
  assert (0 <= k) by nia.
  rewrite Hk, Z2N.inj_mul by lia. reflexivity.
Qed.

Lemma chain : forall A P W X Y Q,
  X <= Y -> A <= X -> Y <= A + W -> prime Q -> P <= Q -> (Q | X) -> (Q | Y) ->
  crst (Dfin A P W) (X - A) (Y - A).
Proof.
  intros A P W X Y Q Hxy HAx HyW Hp HP HX HY.
  pose proof (prime_ge_2 _ Hp) as Hq2.
  assert (Hd : (Q | Y - X)) by (apply Z.divide_sub_r; assumption).
  destruct Hd as [k Hk].
  assert (Hk0 : 0 <= k) by nia.
  assert (G : forall j : nat, Z.of_nat j <= k ->
              crst (Dfin A P W) (X - A) (X + Z.of_nat j * Q - A)).
  { intro j. induction j as [| j IHj]; intros Hj.
    - replace (X + Z.of_nat 0 * Q - A) with (X - A) by (simpl; ring). apply rst_refl.
    - eapply rst_trans; [apply IHj; lia|].
      apply rst_step. exists Q.
      assert (Hjq : 0 <= Z.of_nat j * Q) by (apply Z.mul_nonneg_nonneg; lia).
      assert (Hjq2 : (Z.of_nat j + 1) * Q <= k * Q) by (apply Z.mul_le_mono_nonneg_r; lia).
      refine (conj Hp (conj HP (conj _ (conj _ (conj _ _))))).
      + rewrite Nat2Z.inj_succ. unfold Z.succ. ring.
      + lia.
      + rewrite Nat2Z.inj_succ. unfold Z.succ. lia.
      + replace (A + (X + Z.of_nat j * Q - A)) with (X + Z.of_nat j * Q) by ring.
        apply Z.divide_add_r; [exact HX | apply Z.divide_mul_r, Z.divide_refl]. }
  replace (Y - A) with (X + Z.of_nat (Z.to_nat k) * Q - A) by (rewrite Z2Nat.id by lia; lia).
  apply G. lia.
Qed.

Section Bridge.
  Variables a b p : N.
  Let A := Z.of_N a.
  Let W := Z.of_N b - Z.of_N a.
  Let P := Z.of_N p.

  Lemma same_set_D : forall x y, same_set a b p x y ->
    x = y \/ (in_interval a b x /\ in_interval a b y /\
              crst (Dfin A P W) (Z.of_N x - A) (Z.of_N y - A)).
  Proof.
    intros x y H. induction H as [x y Hm | x | x y _ IH | x y z _ IH1 _ IH2].
    - right. destruct Hm as (Ix & Iy & q & Hq & Hpq & Dx & Dy).
      unfold in_interval in *.
      split; [exact Ix | split; [exact Iy|]].
      destruct (N.le_ge_cases x y) as [Hl | Hl].
      + apply (chain A P W (Z.of_N x) (Z.of_N y) (Z.of_N q)); unfold A, W, P;
          try lia; try assumption; apply ndiv_zdiv; assumption.
      + apply rst_sym.
        apply (chain A P W (Z.of_N y) (Z.of_N x) (Z.of_N q)); unfold A, W, P;
          try lia; try assumption; apply ndiv_zdiv; assumption.
    - left. reflexivity.
    - destruct IH as [-> | (I1 & I2 & C)]; [left; reflexivity|].
      right. split; [exact I2 | split; [exact I1 | apply rst_sym; exact C]].
    - destruct IH1 as [-> | (I1 & I2 & C1)]; destruct IH2 as [-> | (J1 & J2 & C2)].
      + left. reflexivity.
      + right. split; [exact J1 | split; [exact J2 | exact C2]].
      + right. split; [exact I1 | split; [exact I2 | exact C1]].
      + right. split; [exact I1 | split; [exact J2 | eapply rst_trans; eassumption]].
  Qed.

  Lemma D_same_set : forall o1 o2, crst (Dfin A P W) o1 o2 ->
    same_set a b p (Z.to_N (A + o1)) (Z.to_N (A + o2)).
  Proof.
    intros o1 o2 H. induction H as [o1 o2 Hd | o | o1 o2 _ IH | o1 o2 o3 _ IH1 _ IH2].
    - apply rst_step. destruct Hd as (q & Hp & HP & E2 & H0 & Hw & Hd).
      pose proof (prime_ge_2 _ Hp) as Hq2.
      unfold merge, in_interval, share_prime_at_least.
      unfold A, W, P in *.
      split; [lia | split; [lia|]].
      exists (Z.to_N q). split; [rewrite Z2N.id by lia; exact Hp|].
      split; [lia|].
      split; apply zdiv_ndiv; try lia; [exact Hd|].
      rewrite E2. replace (Z.of_N a + (o1 + q)) with ((Z.of_N a + o1) + q) by ring.
      apply Z.divide_add_r; [exact Hd | apply Z.divide_refl].
    - apply rst_refl.
    - apply rst_sym. exact IH.
    - eapply rst_trans; eassumption.
  Qed.
End Bridge.

Lemma FOP_impl : forall {T} (R1 R2 : T -> T -> Prop) l,
  ForallOrdPairs R1 l -> (forall x y, In x l -> In y l -> R1 x y -> R2 x y) ->
  ForallOrdPairs R2 l.
Proof.
  intros T R1 R2 l H. induction H as [| x l Hx Hl IH]; intros Himp; constructor.
  - rewrite Forall_forall in *. intros y Hy. apply Himp; [left; reflexivity | right; exact Hy | apply Hx; exact Hy].
  - apply IH. intros u v Hu Hv. apply Himp; right; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma numbersets_impl_correct : forall (a b p : N) (x y z : uint),
  valid_input a b p -> repr x a -> repr y b -> repr z p ->
  exists n : N, repr (numbersets_impl x y z) n /\ numbersets_spec a b p n.
Proof.
  intros a b p x y z Hv Hx Hy Hz.
  destruct Hv as [Va Vab Vb Vw Vp].
  unfold repr, repr_uint in Hx, Hy, Hz.
  pose proof (to_Z_bounded x) as Bx. pose proof (to_Z_bounded y) as By.
  pose proof (to_Z_bounded z) as Bz.
  assert (Ex : (φ x) = Z.of_N a) by lia.
  assert (Ey : (φ y) = Z.of_N b) by lia.
  assert (Ez : (φ z) = Z.of_N p) by lia.
  set (A := Z.of_N a) in *. set (W := Z.of_N b - Z.of_N a). set (P := Z.of_N p).
  assert (HW : 0 <= W <= 1000000) by (unfold W; lia).
  assert (Hw : (φ (y - x))%uint63 = W).
  { rewrite sub_spec, Ex, Ey. apply Z.mod_small. unfold W, A in *. lia. }
  set (n := W + 1).
  assert (Hnn : (φ (y - x + 1))%uint63 = n).
  { rewrite add_spec, Hw. change (φ 1) with 1. apply Z.mod_small. rewrite wB_val. unfold n. lia. }
  assert (Hnb : n <= 4194303) by (unfold n; lia).
  unfold numbersets_impl. cbv zeta.
  set (w := (y - x)%uint63) in *. set (nn := (w + 1)%uint63) in *.
  pose proof (sieve_prime w nn ltac:(lia) ltac:(lia)) as Hc. cbv zeta in Hc.
  set (c := sieve (PArray.make nn false) w nn 2 (Zwf_well_founded 0 (gap nn 2))) in *.
  (* the initial forest *)
  assert (Lm : forall d : int, (φ (PArray.length (PArray.make nn d))) = n).
  { intro d. rewrite alength_make.
    replace (nn <=? PArray.max_length)%uint63 with true; [exact Hnn|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  destruct (iota_spec nn ltac:(lia) _ 0 (PArray.make nn 0%uint63) (Zwf_well_founded 0 (gap nn 0))
              eq_refl ltac:(rewrite Lm; lia) ltac:(change (φ 0) with 0; lia)
              ltac:(intros x0 Hx0; change (φ 0) with 0 in Hx0; pose proof (to_Z_bounded x0); lia))
    as [Il Ic].
  set (par0 := iota (PArray.make nn 0%uint63) nn 0 (Zwf_well_founded 0 (gap nn 0))) in *.
  set (rk0 := PArray.make nn 0%uint63).
  assert (I0 : Inv n ((φ z) * n) par0 rk0).
  { constructor.
    - rewrite Il. exact Hnn.
    - apply Lm.
    - intros x0 Hx0. rewrite Ic by lia. exact Hx0.
    - intros x0 Hx0 Hn0. exfalso. apply Hn0. apply Ic. lia.
    - intros x0 Hx0. unfold rk0. rewrite aget_make. change (φ 0) with 0.
      apply Z.mul_nonneg_nonneg; lia. }
  assert (C0 : Corr n par0 (crst (Done A P W (φ z) 0))).
  { intros u v Hu Hv.
    rewrite (S_iff_root _ _ _ _ _ (rt_root par0 u (Ic u ltac:(lia)))
                                  (rt_root par0 v (Ic v ltac:(lia)))).
    rewrite Ez. split.
    - intros ->. apply rst_refl.
    - intros H. apply to_Z_inj. clear Hu Hv.
      induction H as [o1 o2 Hd | o | o1 o2 _ IH | o1 o2 o3 _ IH1 _ IH2].
      + exfalso. exact (Done_init _ _ _ _ _ Hd).
      + reflexivity.
      + symmetry. exact IH.
      + rewrite IH1. exact IH2. }
  rewrite Hw in Hc.
  destruct (uprimes c x w nn par0 rk0 z (Zwf_well_founded 0 (gap nn z))) as [par rk] eqn:U.
  destruct (uprimes_spec c x w nn A P W n Ex Hw Hnn eq_refl Hnb ltac:(lia) ltac:(unfold P; lia)
              Hc _ z par0 rk0 _ par rk eq_refl ltac:(lia) I0 C0 U) as [[B IB] CB].
  set (k := Z.to_nat n).
  pose proof (count_spec par nn A ltac:(lia) _ 0 0 (Zwf_well_founded 0 (gap nn 0)) eq_refl
                ltac:(change (φ 0) with 0; lia) ltac:(reflexivity)) as Hcnt.
  rewrite Hnn in Hcnt. fold k in Hcnt.
  set (cnt := count par nn 0 0 (Zwf_well_founded 0 (gap nn 0))) in *.
  exists (Z.to_N (φ cnt)). split; [reflexivity|].
  (* the representatives *)
  assert (Hof : forall j : nat, (j < k)%nat -> (φ (of_Z (Z.of_nat j))) = Z.of_nat j).
  { intros j Hj. rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. unfold k in Hj. lia. }
  unfold numbersets_spec, set_count. exists (rl par A k).
  split; [unfold len; rewrite Hcnt; lia|].
  split.
  { rewrite Forall_forall. intros v Hv. apply rl_In in Hv. destruct Hv as (j & Hj & _ & ->).
    unfold in_interval, k, n, W, A in *. lia. }
  split.
  { apply (FOP_impl (fun r s => r <> s)); [apply NoDup_iff_ForallOrdPairs, rl_NoDup; unfold A; lia|].
    intros r s Hr Hs Hrs Hss.
    apply rl_In in Hr. destruct Hr as (j1 & Hj1 & R1 & ->).
    apply rl_In in Hs. destruct Hs as (j2 & Hj2 & R2 & ->).
    destruct (same_set_D a b p _ _ Hss) as [E | (_ & _ & Hd)]; [exact (Hrs E)|].
    fold A W P in Hd.
    rewrite !Z2N.id in Hd by (unfold A; lia).
    replace (A + Z.of_nat j1 - A) with (Z.of_nat j1) in Hd by ring.
    replace (A + Z.of_nat j2 - A) with (Z.of_nat j2) in Hd by ring.
    rewrite <- (Hof j1 Hj1), <- (Hof j2 Hj2) in Hd.
    apply CB in Hd; [| rewrite Hof by exact Hj1; unfold k in Hj1; lia
                     | rewrite Hof by exact Hj2; unfold k in Hj2; lia].
    rewrite (S_iff_root _ _ _ _ _ (rt_root _ _ R1) (rt_root _ _ R2)) in Hd.
    apply Hrs. rewrite <- (Hof j1 Hj1), <- (Hof j2 Hj2), Hd. reflexivity. }
  { intros v Hv. unfold in_interval in Hv.
    set (o := Z.of_N v - A).
    assert (Ho : 0 <= o < n) by (unfold o, n, W, A; lia).
    assert (Hoo : (φ (of_Z o)) = o) by (rewrite of_Z_spec; apply Z.mod_small; rewrite wB_val; lia).
    destruct (rt_exists _ _ _ _ IB (of_Z o) ltac:(lia)) as [r Hr].
    pose proof (rt_bound _ _ _ _ IB _ _ Hr ltac:(lia)) as Hrb.
    pose proof (rt_is_root _ _ _ Hr) as Hrr.
    assert (Hs : S par (of_Z o) r) by (exists r; split; [exact Hr | apply rt_root; exact Hrr]).
    apply CB in Hs; [| lia | exact Hrb].
    rewrite Hoo in Hs.
    pose proof (D_same_set a b p _ _ Hs) as Hss. fold A in Hss.
    replace (Z.to_N (A + o)) with v in Hss by (unfold o, A; lia).
    exists (Z.to_N (A + (φ r))). split; [|exact Hss].
    apply rl_In. exists (Z.to_nat (φ r)).
    pose proof (to_Z_bounded r).
    rewrite Z2Nat.id by lia. rewrite of_to_Z.
    split; [unfold k; lia | split; [exact Hrr | reflexivity]]. }
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition numbersets : uint -> uint -> uint -> uint := numbersets_impl.

Definition numbersets_correct : forall (a b p : N) (x y z : uint),
  valid_input a b p -> repr x a -> repr y b -> repr z p ->
  exists n : N, repr (numbersets x y z) n /\ numbersets_spec a b p n
  := numbersets_impl_correct.
