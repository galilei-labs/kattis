(** * Booking *)

(** ** Description *)

(** Find the minimum number of resources needed to accommodate time
    intervals, allowing a fixed cleanup period after each interval before
    its resource can be reused.

    [@kattis booking]
    - Difficulty: 4.5

    **Kattis Bounds**
    - 1 to 5000 intervals; cleanup time from 0 to 360 minutes.
    - Valid dates from 2013 through 2016; each interval ends no earlier than
      it starts. *)

(** ** Examples *)

(** Kattis text input and output. *)
(* Input:
4
2 120
1 2013-07-01 15:59 2013-07-08 16:30
2 2013-07-08 17:30 2013-07-15 12:00
3 60
65 2013-07-08 14:30 2013-07-08 16:00
32 2013-07-01 16:00 2013-07-15 12:00
91 2013-07-01 16:00 2013-07-08 15:00
2 360
a7 2016-02-21 14:00 2016-02-28 21:00
xx 2016-03-01 01:00 2016-03-02 12:57
2 60
a9 2016-02-21 14:00 2016-02-28 11:00
a8 2016-02-28 12:00 2016-03-11 21:00
Output:
2
3
1
1
*)

(** ** [@hide] Environment *)

(* @function        min_rooms
   @signature       uint -> array (datetime uint) -> array (datetime uint) -> uint
   @math_signature  N -> list (datetime N) -> list (datetime N) -> N
   @summary         [min_rooms cleaning_time arrivals departures] is the
                    minimum number of hotel rooms to which one test case's
                    bookings (booking i from arrivals_i to departures_i,
                    Gregorian calendar, leap years included) can be assigned
                    so that two bookings sharing a room never overlap, a room
                    being unusable for cleaning_time minutes after each
                    departure (cleaning): a room left at time t can be taken
                    again at exactly t + cleaning_time.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.
Open Scope bool_scope.

(** ** Definitions *)

(** One "YYYY-MM-DD HH:MM" of the input, as its five
    numbers: datetime uint on the machine side, datetime
    N on the math side. The reservation codes do not
    influence the answer and are not passed. *)
Record datetime (A : Type) :=
  { year : A; month : A; day : A; hour : A; minute : A }.
Arguments year {A}. Arguments month {A}. Arguments day {A}.
Arguments hour {A}. Arguments minute {A}.

(** [@hide] The machine date and time represent each
    calendar field. *)
Instance repr_datetime : Repr (datetime uint)
  (datetime N) :=
  fun time_int time =>
    repr (year time_int) (year time) /\ repr
      (month time_int) (month time) /\
    repr (day time_int) (day time) /\ repr (hour time_int)
      (hour time) /\
    repr (minute time_int) (minute time).

(* Math side. *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** Gregorian leap years. *)
Definition leap (calendar_year : N) : bool :=
  (calendar_year mod 4 =? 0) && negb
    (calendar_year mod 100 =? 0)
  || (calendar_year mod 400 =? 0).

(** The number of days in the given Gregorian year. *)
Definition days_in_year (calendar_year : N) : N :=
  if leap calendar_year then 366 else 365.

(** The number of days in the given month and year. *)
Definition days_in_month
  (calendar_year month_number : N) : N :=
  if month_number =? 2 then
    (if leap calendar_year then 29 else 28)
  else if (month_number =? 4) || (month_number =? 6) ||
          (month_number =? 9) ||
            (month_number =? 11) then 30
  else 31.

(** summand 0 + summand 1 + ... + summand (term_count -
    1). *)
Fixpoint sum_below (summand : N -> N)
  (term_count : nat) : N :=
  match term_count with
  | O => 0
  | S previous => sum_below summand previous + summand
    (N.of_nat previous)
  end.

(** Minutes elapsed from 0000-01-01 00:00 (proleptic
    Gregorian) to time. *)
Definition minutes (time : datetime N) : N :=
  let days := sum_below days_in_year (N.to_nat (year time))
            + sum_below (fun month_index =>
                           days_in_month (year time)
                             (month_index + 1))
                        (N.to_nat (month time - 1))
            + (day time - 1) in
  (days * 24 + hour time) * 60 + minute time.

(** A correct and valid date of the years 2013 to 2016. *)
Definition valid_datetime (time : datetime N) : Prop :=
  2013 <= year time <= 2016 /\ 1 <= month time <= 12 /\
  1 <= day time <= days_in_month (year time) (month time) /\
  hour time <= 23 /\ minute time <= 59.

(** Two bookings (arrival, departure) may share a room:
    one of them, cleaning included, is over when the
    other arrives. *)
Definition compatible (cleaning_time : N)
  (arrival departure arrival' departure' : datetime N) :
    Prop :=
  minutes departure + cleaning_time <= minutes arrival' \/
  minutes departure' + cleaning_time <= minutes arrival.

(** Some assignment of the bookings to rooms 0 ..
    room_count-1 puts only compatible bookings in the
    same room. *)
Definition rooms_suffice (cleaning_time : N)
  (arrivals departures : list (datetime N))
    (room_count : N) : Prop :=
  exists room : nat -> N,
    (forall i, (i < List.length arrivals)%nat
      -> room i < room_count) /\
    (forall i j arrival departure arrival' departure',
       nth_error arrivals i = Some arrival ->
       nth_error departures i = Some departure ->
       nth_error arrivals j = Some arrival' ->
       nth_error departures j = Some departure' ->
       i <> j -> room i = room j ->
       compatible cleaning_time arrival departure arrival'
         departure').

(** [@inside min_rooms_correct] The statement's bounds,
    for one test case. *)
Record valid_input (cleaning_time : N)
  (arrivals departures : list (datetime N))
  : Prop := {
  (* 1 <= B <= 5 000, the number of bookings *)
  vi_b : 1 <= len arrivals <= 5000;
  (* each booking has a date of arrival and a date of
    departure *)
  vi_dep_len : len departures = len arrivals;
  (* 0 <= C <= 360, the cleaning time in minutes *)
  vi_c : cleaning_time <= 360;
  (* correct and valid dates ... reservations are only for
    the years 2013
     until 2016 *)
  vi_arr : Forall valid_datetime arrivals;
  vi_dep : Forall valid_datetime departures;
  (* correct dates of arrival and departure: no departure
    before its arrival *)
  vi_order : Forall2 (fun arrival departure =>
                        minutes arrival <= minutes
                          departure)
               arrivals departures;
}.

(** ** Correctness *)

(** [@requirement] [@short must return the minimum
    number of rooms needed.] The answer: output rooms
    suffice, and no fewer do. *)
Definition min_rooms_spec (cleaning_time : N)
  (arrivals departures : list (datetime N))
    (output : N) : Prop :=
  rooms_suffice cleaning_time arrivals departures output /\
  forall room_count',
    rooms_suffice cleaning_time arrivals departures
      room_count' ->
    output <= room_count'.

(** ** Interface *)

(** The machine-level interface.
    - Input [cleaning_time]:
    - Input [arrivals]:
    - Input [departures]:
    - Output [output]: *)
Program min_rooms : uint -> array (datetime uint) -> array
  (datetime uint) -> uint.

(** ** Bridge *)

(** [@requirement min_rooms_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [min_rooms_spec]. *)
Specification min_rooms_correct :
  forall (cleaning_time : N) (arrivals departures : list
    (datetime N))
         (cleaning_time_int : uint)
         (arrivals_arr departures_arr : array
           (datetime uint)),
  valid_input cleaning_time arrivals departures ->
  repr cleaning_time_int cleaning_time ->
  repr arrivals_arr arrivals
    -> repr departures_arr departures ->
  exists output : N,
    repr (min_rooms cleaning_time_int arrivals_arr
      departures_arr)
      output /\
    min_rooms_spec cleaning_time arrivals departures output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
