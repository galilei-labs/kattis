(* Executable implementation and its required termination dependencies.
   Correctness proofs are in kattissquest_proofs.v. *)
(* Implementation of kattissquest (kattissquest.spec).

   See the README of this try for the design; the code section below is
   self-contained. *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Permutation.
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

Lemma shr1_spec : forall k : int, (φ (k >> 1)) = ((φ k) / 2)%Z.
Proof. intros k. rewrite lsr_spec. reflexivity. Qed.

Lemma dec_lo : forall k : int, (1 <? k) = true -> Zwf 0 (φ (k >> 1)) (φ k).
Proof.
  intros k H. rewrite ltb_spec in H. unfold Zwf. rewrite shr1_spec.
  change (φ 1) with 1%Z in H. Z.to_euclidean_division_equations; lia.
Qed.

Lemma dec_hi : forall k : int, (1 <? k) = true -> Zwf 0 (φ (k - (k >> 1))) (φ k).
Proof.
  intros k H. rewrite ltb_spec in H. unfold Zwf.
  change (φ 1) with 1%Z in H.
  assert (E : (φ (k - (k >> 1))) = ((φ k) - (φ k) / 2)%Z).
  { rewrite sub_spec, shr1_spec. apply Z.mod_small.
    pose proof (to_Z_bounded k). split; [|].
    - assert ((φ k) / 2 <= (φ k))%Z by (apply Z.div_le_upper_bound; lia). lia.
    - assert (0 <= (φ k) / 2)%Z by (apply Z.div_pos; lia). lia. }
  rewrite E. assert (1 <= (φ k) / 2)%Z by (apply Z.div_le_lower_bound; lia).
  assert ((φ k) / 2 <= (φ k))%Z by (apply Z.div_le_upper_bound; lia). lia.
Qed.

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_par : forall i : int, (0 <? i) = true -> Zwf 0 (φ ((i - 1) >> 1)) (φ i).
Proof.
  intros i H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  unfold Zwf. rewrite shr1_spec.
  assert (E : (φ (i - 1)) = ((φ i) - 1)%Z) by sia. rewrite E.
  Z.to_euclidean_division_equations; lia.
Qed.

Lemma dec_sub : forall x e : int, ((0 <? e) && (e <=? x))%bool = true ->
  Zwf 0 (φ (x - e)) (φ x).
Proof.
  intros x e H. apply andb_prop in H. destruct H as [H1 H2].
  rewrite ltb_spec in H1. rewrite leb_spec in H2. change (φ 0) with 0%Z in H1.
  unfold Zwf. assert (E : (φ (x - e)) = ((φ x) - (φ e))%Z) by sia. lia.
Qed.

Lemma dec_k : forall m k : int, ((k <? 62) && ((1 << k) <=? m))%bool = true ->
  Zwf 0 (62 - (φ (k + 1))) (62 - (φ k)).
Proof.
  intros m k H. apply andb_prop in H. destruct H as [H1 _].
  rewrite ltb_spec in H1. change (φ 62) with 62%Z in H1.
  unfold Zwf. assert (E : (φ (k + 1)) = ((φ k) + 1)%Z) by sia. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The van Emde Boas tree                                              *)
(* ------------------------------------------------------------------ *)

(* A vEB node of universe 2^k is two cells (min, max; [nil] when empty)
   followed by its summary (universe 2^(k - k/2)) and its 2^(k - k/2)
   clusters (universe 2^(k/2)), laid out contiguously in one flat array.
   [t.[j]] is the number of cells of a node of universe 2^j. *)

Definition nil : int := 9223372036854775807.

Definition kl (k : int) : int := k >> 1.
Definition kh (k : int) : int := k - (k >> 1).

Definition clb (t : array int) (b k i : int) : int := b + 2 + t.[kh k] + i * t.[kl k].

Fixpoint vins (t v : array int) (b k x : int) (H : Acc (Zwf 0) (φ k)) {struct H}
    : array int :=
  let m := v.[b] in
  if m =? nil then v.[b <- x].[b + 1 <- x]
  else
    let y := if x <? m then m else x in
    let v1 := if x <? m then v.[b <- x] else v in
    let v2 :=
      match bdec (1 <? k) with
      | left Hk =>
          let hy := y >> kl k in
          let ly := y - (hy << kl k) in
          let c := clb t b k hy in
          if v1.[c] =? nil then
            let v3 := vins t v1 (b + 2) (kh k) hy (Acc_inv H (dec_hi k Hk)) in
            v3.[c <- ly].[c + 1 <- ly]
          else vins t v1 c (kl k) ly (Acc_inv H (dec_lo k Hk))
      | right _ => v1
      end in
    if v2.[b + 1] <? y then v2.[b + 1 <- y] else v2.

Fixpoint vdel (t v : array int) (b k x : int) (H : Acc (Zwf 0) (φ k)) {struct H}
    : array int :=
  let m := v.[b] in
  let M := v.[b + 1] in
  if m =? M then v.[b <- nil].[b + 1 <- nil]
  else
    match bdec (1 <? k) with
    | right _ => let r := if x =? 0 then 1 else 0 in v.[b <- r].[b + 1 <- r]
    | left Hk =>
        let y := if x =? m then let f := v.[b + 2] in (f << kl k) + v.[clb t b k f]
                 else x in
        let v1 := if x =? m then v.[b <- y] else v in
        let hy := y >> kl k in
        let ly := y - (hy << kl k) in
        let c := clb t b k hy in
        let v2 := vdel t v1 c (kl k) ly (Acc_inv H (dec_lo k Hk)) in
        if v2.[c] =? nil then
          let v3 := vdel t v2 (b + 2) (kh k) hy (Acc_inv H (dec_hi k Hk)) in
          if y =? v3.[b + 1] then
            let sm := v3.[b + 2 + 1] in
            if sm =? nil then v3.[b + 1 <- v3.[b]]
            else v3.[b + 1 <- (sm << kl k) + v3.[clb t b k sm + 1]]
          else v3
        else if y =? v2.[b + 1] then v2.[b + 1 <- (hy << kl k) + v2.[c + 1]]
        else v2
    end.

(* the largest element <= x, or nil *)
Fixpoint vpred (t v : array int) (b k x : int) (H : Acc (Zwf 0) (φ k)) {struct H}
    : int :=
  let m := v.[b] in
  if x <? m then nil
  else
    let M := v.[b + 1] in
    if M <=? x then M
    else
      match bdec (1 <? k) with
      | right _ => m
      | left Hk =>
          let hx := x >> kl k in
          let lx := x - (hx << kl k) in
          let c := clb t b k hx in
          if v.[c] <=? lx then (hx << kl k) + vpred t v c (kl k) lx (Acc_inv H (dec_lo k Hk))
          else if hx =? 0 then m
          else
            let ph := vpred t v (b + 2) (kh k) (hx - 1) (Acc_inv H (dec_hi k Hk)) in
            if ph =? nil then m
            else (ph << kl k) + v.[clb t b k ph + 1]
      end.

(* ------------------------------------------------------------------ *)
(* Binary max-heaps, one per energy, in segments of one flat array     *)
(* ------------------------------------------------------------------ *)

(* positions are relative to the segment start s *)
Fixpoint sup (gd : array int) (s i : int) (H : Acc (Zwf 0) (φ i)) {struct H} : array int :=
  match bdec (0 <? i) with
  | left Hi =>
      let p := (i - 1) >> 1 in
      let a := gd.[s + p] in
      let b := gd.[s + i] in
      if a <? b then sup gd.[s + p <- b].[s + i <- a] s p (Acc_inv H (dec_par i Hi))
      else gd
  | right _ => gd
  end.

Definition pickc (gd : array int) (s n i : int) : int :=
  let c1 := 2 * i + 1 in
  if c1 + 1 <? n then (if gd.[s + c1] <? gd.[s + (c1 + 1)] then c1 + 1 else c1) else c1.

Lemma dec_pick : forall (gd : array int) (s n i : int),
  ((i <? 2 * i + 1) && (2 * i + 1 <? n))%bool = true ->
  Zwf 0 ((φ n) - (φ (pickc gd s n i))) ((φ n) - (φ i)).
Proof.
  intros gd s n i H. apply andb_prop in H. destruct H as [H1 H2].
  rewrite ltb_spec in H1, H2. unfold Zwf, pickc.
  pose proof (to_Z_bounded n).
  destruct (2 * i + 1 + 1 <? n) eqn:E.
  - rewrite ltb_spec in E.
    assert ((φ (2 * i + 1 + 1)) = (φ (2 * i + 1)) + 1)%Z by sia.
    destruct (gd.[s + (2 * i + 1)] <? gd.[s + (2 * i + 1 + 1)]); lia.
  - lia.
Qed.

Fixpoint sdown (gd : array int) (s n i : int) (H : Acc (Zwf 0) ((φ n) - (φ i))%Z) {struct H}
    : array int :=
  match bdec ((i <? 2 * i + 1) && (2 * i + 1 <? n)) with
  | right _ => gd
  | left Hc =>
      let c := pickc gd s n i in
      let a := gd.[s + i] in
      let b := gd.[s + c] in
      if a <? b then sdown gd.[s + i <- b].[s + c <- a] s n c (Acc_inv H (dec_pick gd s n i Hc))
      else gd
  end.

Definition hpush (gd : array int) (s n g : int) : array int :=
  sup gd.[s + n <- g] s n (Zwf_well_founded 0 _).

(* removes the root of a heap of size n >= 1 *)
Definition hpop (gd : array int) (s n : int) : array int :=
  let last := gd.[s + (n - 1)] in
  sdown gd.[s <- last] s (n - 1) 0 (Zwf_well_founded 0 _).

(* ------------------------------------------------------------------ *)
(* Preprocessing                                                       *)
(* ------------------------------------------------------------------ *)

(* the largest energy (at least 1) and the number of queries *)
Fixpoint scan (x : array command) (N j m q : int) (H : Acc (Zwf 0) (gap N j)) {struct H}
    : int * int :=
  match bdec (j <? N) with
  | left Hj =>
      match x.[j] with
      | Prelude.Add e _ => scan x N (j + 1) (if m <? e then e else m) q (Acc_inv H (dec_step N j Hj))
      | Query _ => scan x N (j + 1) m (q + 1) (Acc_inv H (dec_step N j Hj))
      end
  | right _ => (m, q)
  end.

(* the least k >= 1 (and <= 62) with m < 2^k *)
Fixpoint kloop (m k : int) (H : Acc (Zwf 0) (62 - (φ k))%Z) {struct H} : int :=
  match bdec ((k <? 62) && ((1 << k) <=? m)) with
  | left Hk => kloop m (k + 1) (Acc_inv H (dec_k m k Hk))
  | right _ => k
  end.

(* the size table: t.[j] cells for a node of universe 2^j, j = k .. K *)
Fixpoint stab (t : array int) (K k : int) (H : Acc (Zwf 0) (gap (K + 1) k)) {struct H}
    : array int :=
  match bdec (k <? K + 1) with
  | left Hk =>
      let s := if k <=? 1 then 2 else 2 + t.[kh k] + (t.[kl k] << kh k) in
      stab t.[k <- s] K (k + 1) (Acc_inv H (dec_step (K + 1) k Hk))
  | right _ => t
  end.

(* the number of quests of each energy *)
Fixpoint cntloop (x : array command) (N j : int) (c : array int)
    (H : Acc (Zwf 0) (gap N j)) {struct H} : array int :=
  match bdec (j <? N) with
  | left Hj =>
      match x.[j] with
      | Prelude.Add e _ => cntloop x N (j + 1) c.[e <- c.[e] + 1] (Acc_inv H (dec_step N j Hj))
      | Query _ => cntloop x N (j + 1) c (Acc_inv H (dec_step N j Hj))
      end
  | right _ => c
  end.

(* exclusive prefix sums, in place: the segment start of each energy *)
Fixpoint pref (c : array int) (U e acc : int) (H : Acc (Zwf 0) (gap U e)) {struct H}
    : array int :=
  match bdec (e <? U) with
  | left He =>
      let ce := c.[e] in
      pref c.[e <- acc] U (e + 1) (acc + ce) (Acc_inv H (dec_step U e He))
  | right _ => c
  end.

(* ------------------------------------------------------------------ *)
(* Sessions and the command loop                                       *)
(* ------------------------------------------------------------------ *)

Fixpoint sess (t st : array int) (K U : int) (v gd hz : array int) (x acc : int)
    (H : Acc (Zwf 0) (φ x)) {struct H} : array int * array int * array int * int :=
  let x' := if x <? U then x else U - 1 in
  let e := vpred t v 0 K x' (Zwf_well_founded 0 _) in
  match bdec ((0 <? e) && (e <=? x)) with
  | left He =>
      let s := st.[e] in
      let n := hz.[e] in
      let g := gd.[s] in
      let gd1 := hpop gd s n in
      let hz1 := hz.[e <- n - 1] in
      let v1 := if n =? 1 then vdel t v 0 K e (Zwf_well_founded 0 _) else v in
      sess t st K U v1 gd1 hz1 (x - e) (acc + g) (Acc_inv H (dec_sub x e He))
  | right _ => (v, gd, hz, acc)
  end.

Fixpoint mloop (x : array command) (t st : array int) (K U N j : int)
    (v gd hz out : array int) (qi : int) (H : Acc (Zwf 0) (gap N j)) {struct H}
    : array int :=
  match bdec (j <? N) with
  | right _ => out
  | left Hj =>
      match x.[j] with
      | Prelude.Add e g =>
          let s := st.[e] in
          let n := hz.[e] in
          let gd1 := hpush gd s n g in
          let hz1 := hz.[e <- n + 1] in
          let v1 := if n =? 0 then vins t v 0 K e (Zwf_well_founded 0 _) else v in
          mloop x t st K U N (j + 1) v1 gd1 hz1 out qi (Acc_inv H (dec_step N j Hj))
      | Query q =>
          let '(v1, gd1, hz1, a) := sess t st K U v gd hz q 0 (Zwf_well_founded 0 _) in
          mloop x t st K U N (j + 1) v1 gd1 hz1 out.[qi <- a] (qi + 1)
            (Acc_inv H (dec_step N j Hj))
      end
  end.

Definition kattissquest_impl (x : array command) : array uint :=
  let N := PArray.length x in
  let '(mE, Q) := scan x N 0 1 0 (Zwf_well_founded 0 _) in
  let K := kloop mE 1 (Zwf_well_founded 0 _) in
  let t := stab (PArray.make (K + 1) 0) K 1 (Zwf_well_founded 0 _) in
  let U := 1 << K in
  let cnt := cntloop x N 0 (PArray.make U 0) (Zwf_well_founded 0 _) in
  let st := pref cnt U 0 0 (Zwf_well_founded 0 _) in
  mloop x t st K U N 0 (PArray.make t.[K] nil) (PArray.make N 0) (PArray.make U 0)
    (PArray.make Q 0) 0 (Zwf_well_founded 0 _).

Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition kattissquest : array command -> array uint := kattissquest_impl.
