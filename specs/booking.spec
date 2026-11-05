(* @function        min_rooms
   @signature       uint -> array (datetime uint) -> array (datetime uint) -> uint
   @math_signature  N -> list (datetime N) -> list (datetime N) -> N
   @summary         [min_rooms c arr dep] is the minimum number of hotel
                    rooms to which one test case's bookings (booking i from
                    arr_i to dep_i, Gregorian calendar, leap years included)
                    can be assigned so that two bookings sharing a room never
                    overlap, a room being unusable for c minutes after each
                    departure (cleaning): a room left at time t can be taken
                    again at exactly t + c.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.
Open Scope bool_scope.

(* One "YYYY-MM-DD HH:MM" of the input, as its five numbers: datetime uint on
   the machine side, datetime N on the math side.  The reservation codes do
   not influence the answer and are not passed. *)
Record datetime (A : Type) := { year : A; month : A; day : A; hour : A; minute : A }.
Arguments year {A}. Arguments month {A}. Arguments day {A}.
Arguments hour {A}. Arguments minute {A}.

Instance repr_datetime : Repr (datetime uint) (datetime N) :=
  fun x t => repr (year x) (year t) /\ repr (month x) (month t) /\
             repr (day x) (day t) /\ repr (hour x) (hour t) /\
             repr (minute x) (minute t).

(* Math side. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* Gregorian leap years. *)
Definition leap (y : N) : bool :=
  (y mod 4 =? 0) && negb (y mod 100 =? 0) || (y mod 400 =? 0).

Definition days_in_year (y : N) : N := if leap y then 366 else 365.

Definition days_in_month (y m : N) : N :=
  if m =? 2 then (if leap y then 29 else 28)
  else if (m =? 4) || (m =? 6) || (m =? 9) || (m =? 11) then 30
  else 31.

(* f 0 + f 1 + ... + f (n - 1). *)
Fixpoint sum_below (f : N -> N) (n : nat) : N :=
  match n with
  | O => 0
  | S m => sum_below f m + f (N.of_nat m)
  end.

(* Minutes elapsed from 0000-01-01 00:00 (proleptic Gregorian) to t. *)
Definition minutes (t : datetime N) : N :=
  let days := sum_below days_in_year (N.to_nat (year t))
            + sum_below (fun k => days_in_month (year t) (k + 1))
                        (N.to_nat (month t - 1))
            + (day t - 1) in
  (days * 24 + hour t) * 60 + minute t.

(* A correct and valid date of the years 2013 to 2016. *)
Definition valid_datetime (t : datetime N) : Prop :=
  2013 <= year t <= 2016 /\ 1 <= month t <= 12 /\
  1 <= day t <= days_in_month (year t) (month t) /\
  hour t <= 23 /\ minute t <= 59.

(* Two bookings (arrival a, departure d) may share a room: one of them,
   cleaning included, is over when the other arrives. *)
Definition compatible (c : N) (a1 d1 a2 d2 : datetime N) : Prop :=
  minutes d1 + c <= minutes a2 \/ minutes d2 + c <= minutes a1.

(* Some assignment of the bookings to rooms 0 .. k-1 puts only compatible
   bookings in the same room. *)
Definition rooms_suffice (c : N) (arr dep : list (datetime N)) (k : N) : Prop :=
  exists room : nat -> N,
    (forall i, (i < List.length arr)%nat -> room i < k) /\
    (forall i j a1 d1 a2 d2,
       nth_error arr i = Some a1 -> nth_error dep i = Some d1 ->
       nth_error arr j = Some a2 -> nth_error dep j = Some d2 ->
       i <> j -> room i = room j -> compatible c a1 d1 a2 d2).

(* The statement's bounds, for one test case. *)
Record valid_input (c : N) (arr dep : list (datetime N)) : Prop := {
  (* 1 <= B <= 5 000, the number of bookings *)
  vi_b : 1 <= len arr <= 5000;
  (* each booking has a date of arrival and a date of departure *)
  vi_dep_len : len dep = len arr;
  (* 0 <= C <= 360, the cleaning time in minutes *)
  vi_c : c <= 360;
  (* correct and valid dates ... reservations are only for the years 2013
     until 2016 *)
  vi_arr : Forall valid_datetime arr;
  vi_dep : Forall valid_datetime dep;
  (* correct dates of arrival and departure: no departure before its arrival *)
  vi_order : Forall2 (fun a d => minutes a <= minutes d) arr dep;
}.

(* The answer: k rooms suffice, and no fewer do. *)
Definition min_rooms_spec (c : N) (arr dep : list (datetime N)) (k : N) : Prop :=
  rooms_suffice c arr dep k /\
  forall k', rooms_suffice c arr dep k' -> k <= k'.

Program min_rooms : uint -> array (datetime uint) -> array (datetime uint) -> uint.

Specification min_rooms_correct :
  forall (c : N) (arr dep : list (datetime N))
         (x : uint) (xa xd : array (datetime uint)),
  valid_input c arr dep -> repr x c -> repr xa arr -> repr xd dep ->
  exists k : N, repr (min_rooms x xa xd) k /\ min_rooms_spec c arr dep k.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
