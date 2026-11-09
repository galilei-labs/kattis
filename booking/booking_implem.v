(* Executable implementation and its required termination dependencies.
   Correctness proofs are in booking_proofs.v. *)
(* Implementation of booking (booking.spec): interval partitioning by
   sorting.  Every date-time becomes a minute count in O(1) (closed-form
   Gregorian day count); each booking gives an arrival key and a release
   key (departure + c), refined by sub-slots so that zero-length bookings
   (c = 0, arrival = departure) are handled as the spec's [compatible]
   says, and so that all keys of one array are distinct; both flat arrays
   are sorted in place by quicksort (Lomuto, middle pivot); one linear
   two-pointer sweep returns max_p (p + 1 - #{releases <= A[p]}).
   Termination: erased Acc (Zwf 0) proofs on Z measures, as in the
   template.  See README.md, "Implementation". *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Permutation Sorted.
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
  unfold Zwf, gap. lia.
Qed.

Lemma dec_left : forall lo hi m : int,
  ((lo <=? m) && (m <? hi)) = true -> Zwf 0 (gap m lo) (gap hi lo).
Proof.
  intros lo hi m H. apply andb_prop in H. destruct H as [H1 H2].
  rewrite leb_spec in H1. rewrite ltb_spec in H2. unfold Zwf, gap. lia.
Qed.

Lemma dec_right : forall lo hi m : int,
  ((lo <=? m) && (m <? hi)) = true -> Zwf 0 (gap hi (m + 1)) (gap hi lo).
Proof.
  intros lo hi m H. apply andb_prop in H. destruct H as [H1 H2].
  rewrite leb_spec in H1. rewrite ltb_spec in H2.
  assert (E : (φ (m + 1)) = ((φ m) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Quicksort, in place, on an array of int read unsigned               *)
(* ------------------------------------------------------------------ *)

Definition swap (a : array int) (i j : int) : array int :=
  let x := a.[i] in
  let y := a.[j] in
  a.[i <- y].[j <- x].

(* Lomuto partition of [lo, hi1) around the pivot p (stored at hi1):
   cells [lo, i) are < p, cells [i, j) are >= p. *)
Fixpoint part_loop (a : array int) (p hi1 i j : int)
    (H : Acc (Zwf 0) (gap hi1 j)) {struct H} : array int * int :=
  match bdec (j <? hi1) with
  | left Hj =>
      if a.[j] <? p
      then part_loop (swap a i j) p hi1 (i + 1) (j + 1) (Acc_inv H (dec_step hi1 j Hj))
      else part_loop a p hi1 i (j + 1) (Acc_inv H (dec_step hi1 j Hj))
  | right _ => (a, i)
  end.

(* Partition of [lo, hi), hi - lo >= 2, around its middle cell; returns the
   final position of the pivot. *)
Definition partition (a : array int) (lo hi : int) : array int * int :=
  let mid := lo + (hi - lo) / 2 in
  let hi1 := hi - 1 in
  let a1 := swap a mid hi1 in
  let p := a1.[hi1] in
  let (a2, i) := part_loop a1 p hi1 lo lo (Zwf_well_founded 0 (gap hi1 lo)) in
  (swap a2 i hi1, i).

Fixpoint qsort (a : array int) (lo hi : int)
    (H : Acc (Zwf 0) (gap hi lo)) {struct H} : array int :=
  match bdec (lo + 1 <? hi) with
  | left _ =>
      let (a1, m) := partition a lo hi in
      match bdec ((lo <=? m) && (m <? hi)) with
      | left Hm =>
          let a2 := qsort a1 lo m (Acc_inv H (dec_left lo hi m Hm)) in
          qsort a2 (m + 1) hi (Acc_inv H (dec_right lo hi m Hm))
      | right _ => a1
      end
  | right _ => a
  end.

Definition sort_all (a : array int) : array int :=
  qsort a 0 (PArray.length a) (Zwf_well_founded 0 (gap (PArray.length a) 0)).

(* ------------------------------------------------------------------ *)
(* The two-pointer sweep                                               *)
(* ------------------------------------------------------------------ *)

Definition meas (n p q : int) : Z := ((φ n) - (φ p) + (wB - (φ q)))%Z.

Lemma dec_q : forall (A R : array int) (n p q : int),
  (p <? n) = true -> ((q <? n) && (R.[q] <=? A.[p])) = true ->
  Zwf 0 (meas n p (q + 1)) (meas n p q).
Proof.
  intros A R n p q Hp Hq. apply andb_prop in Hq. destruct Hq as [Hq _].
  rewrite ltb_spec in Hp, Hq. pose proof (to_Z_bounded q). pose proof (to_Z_bounded n).
  assert (E : (φ (q + 1)) = ((φ q) + 1)%Z) by sia.
  unfold Zwf, meas. lia.
Qed.

Lemma dec_p : forall (n p q : int),
  (p <? n) = true -> Zwf 0 (meas n (p + 1) q) (meas n p q).
Proof.
  intros n p q Hp. rewrite ltb_spec in Hp. pose proof (to_Z_bounded q). pose proof (to_Z_bounded n).
  assert (E : (φ (p + 1)) = ((φ p) + 1)%Z) by sia.
  unfold Zwf, meas. lia.
Qed.

(* best = max(best, max over arrivals A.[p] of (p + 1) - #{releases <= A.[p]}) *)
Fixpoint sweep (A R : array int) (n p q best : int)
    (H : Acc (Zwf 0) (meas n p q)) {struct H} : int :=
  match bdec (p <? n) with
  | left Hp =>
      match bdec ((q <? n) && (R.[q] <=? A.[p])) with
      | left Hq => sweep A R n p (q + 1) best (Acc_inv H (dec_q A R n p q Hp Hq))
      | right _ =>
          sweep A R n (p + 1) q (if best + q <? p + 1 then p + 1 - q else best)
            (Acc_inv H (dec_p n p q Hp))
      end
  | right _ => best
  end.

(* ------------------------------------------------------------------ *)
(* Calendar: O(1) closed-form minute count                             *)
(* ------------------------------------------------------------------ *)

Definition leapb (y : int) : bool :=
  ((y mod 4 =? 0) && negb (y mod 100 =? 0)) || (y mod 400 =? 0).

(* days from 0000-01-01 to y-01-01: 365 y + #{k < y : k leap} *)
Definition days_before_year (y : int) : int :=
  365 * y + (y + 3) / 4 - (y + 99) / 100 + (y + 399) / 400.

(* days from y-01-01 to y-m-01 *)
Definition days_before_month (y m : int) : int :=
  (367 * m - 362) / 12 - (if m <=? 2 then 0 else if leapb y then 1 else 2).

Definition mach_minutes (t : datetime uint) : int :=
  let y := year t in
  let days := days_before_year y + days_before_month y (month t) + (day t - 1) in
  (days * 24 + hour t) * 60 + minute t.

(* ------------------------------------------------------------------ *)
(* Keys: a booking as a half-open, non-empty interval of integer keys  *)
(* ------------------------------------------------------------------ *)

(* A minute t is split into 20000 sub-slots: releases of the non-empty
   bookings at t (sub-slot i, i the booking index), then the empty bookings
   (arrival = departure + c, possible when c = 0) arriving at t, each on its
   own pair of sub-slots 5000 + 2i, 5001 + 2i, then the arrivals of the
   non-empty bookings at t (sub-slot 15000 + i).  Two bookings are
   compatible iff their key intervals are disjoint, every key interval is
   non-empty, and all arrival keys (resp. release keys) are distinct. *)
Definition key_al (ma r i : int) : int :=
  if ma =? r then ma * 20000 + 5000 + 2 * i else ma * 20000 + 15000 + i.

Definition key_rh (ma r i : int) : int :=
  if ma =? r then ma * 20000 + 5001 + 2 * i else r * 20000 + i.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* cells k .. n-1 of the arrival-key and release-key arrays *)
Fixpoint fill (xa xd : array (datetime uint)) (c n k : int) (A R : array int)
    (H : Acc (Zwf 0) (gap n k)) {struct H} : array int * array int :=
  match bdec (k <? n) with
  | left Hk =>
      let ma := mach_minutes xa.[k] in
      let r := mach_minutes xd.[k] + c in
      fill xa xd c n (k + 1) A.[k <- key_al ma r k] R.[k <- key_rh ma r k]
        (Acc_inv H (dec_step n k Hk))
  | right _ => (A, R)
  end.

Definition min_rooms_impl (c : uint) (xa xd : array (datetime uint)) : uint :=
  let n := PArray.length xa in
  let (A, R) := fill xa xd c n 0 (PArray.make n 0) (PArray.make n 0)
                     (Zwf_well_founded 0 (gap n 0)) in
  let A' := sort_all A in
  let R' := sort_all R in
  sweep A' R' n 0 0 0 (Zwf_well_founded 0 (meas n 0 0)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition min_rooms : uint -> array (datetime uint) -> array (datetime uint) -> uint :=
  min_rooms_impl.
