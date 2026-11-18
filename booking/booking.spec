(** * Booking *)

(** ** Description *)

(** A hotel must assign a room to every reservation, given its arrival and
    departure times. A room cannot host overlapping reservations and must be
    cleaned after each departure. It becomes available again when the given
    cleaning time has elapsed; a new guest may arrive at that exact time.
    Find the minimum number of rooms needed to honor all reservations.

    [@kattis booking]
    - Difficulty: 4.5
    - CPU time limit: 5 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Interval count: $1 \le n \le 5 \times 10^{3}$; cleanup time: $0 \le C \le 360$ minutes.
    - Valid dates with year $2013 \le y \le 2016$; each interval ends no earlier than
      it starts. *)

(** ** Examples *)

(** - Input convention: Case count; each case gives booking count, cleanup time, then identifiers and arrival/departure timestamps.
    - Output convention: One minimum room count per case. *)
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
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope N_scope.
Open Scope bool_scope.

(** ** Definitions *)

(** A date and time as year, month, day, hour, and minute. Fields use [uint]
    on the machine side and [N] on the mathematical side. Reservation codes do
    not affect the result and are omitted from the interface. *)
Record datetime (A : Type) :=
  { year : A; month : A; day : A; hour : A; minute : A }.

(** [@hide] Projection argument declarations. *)
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

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** [calendar_year] is a Gregorian leap year. *)
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

(** The sum of [summand] over zero-based indices below [term_count]. *)
Fixpoint sum_below (summand : N -> N)
  (term_count : nat) : N :=
  match term_count with
  | O => 0
  | S previous => sum_below summand previous + summand
    (N.of_nat previous)
  end.

(** Minutes elapsed from 0000-01-01 00:00 to [time], using the proleptic Gregorian
    calendar. *)
Definition minutes (time : datetime N) : N :=
  let days := sum_below days_in_year (N.to_nat (year time))
            + sum_below (fun month_index =>
                           days_in_month (year time)
                             (month_index + 1))
                        (N.to_nat (month time - 1))
            + (day time - 1) in
  (days * 24 + hour time) * 60 + minute time.

(** [time] is a valid calendar date and time in the years 2013 through 2016. *)
Definition valid_datetime (time : datetime N) : Prop :=
  2013 <= year time <= 2016 /\ 1 <= month time <= 12 /\
  1 <= day time <= days_in_month (year time) (month time) /\
  hour time <= 23 /\ minute time <= 59.

(** The bookings can share a room: one departure, followed by the required cleaning
    time, is no later than the other arrival. *)
Definition compatible (cleaning_time : N)
  (arrival departure arrival' departure' : datetime N) :
    Prop :=
  minutes departure + cleaning_time <= minutes arrival' \/
  minutes departure' + cleaning_time <= minutes arrival.

(** The bookings can be assigned to [room_count] rooms so that every pair sharing a
    room satisfies [compatible]. *)
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

(** [@inside min_rooms_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (cleaning_time : N)
  (arrivals departures : list (datetime N))
  : Prop := {
  (* 1 <= B <= 5 * 10^3, the number of bookings *)
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

(** [@requirement]
    The output is the minimum number of hotel rooms needed for all reservations,
    allowing the required cleaning time after each departure before room reuse. *)
Definition min_rooms_spec (cleaning_time : N)
  (arrivals departures : list (datetime N))
    (output : N) : Prop :=
  rooms_suffice cleaning_time arrivals departures output /\
  forall room_count',
    rooms_suffice cleaning_time arrivals departures
      room_count' ->
    output <= room_count'.

(** ** Interface *)

(** Find the fewest hotel rooms that can accommodate all reservations,
    allowing the required cleaning time between guests sharing a room.
    - Input [cleaning_time]: Minutes required to clean a room after departure.
    - Input [arrivals]: Arrival date and time of each reservation.
    - Input [departures]: Departure date and time of each corresponding reservation.
    - Output [output]: Minimum number of rooms needed, including time reserved for cleaning. *)
Program min_rooms : uint -> array (datetime uint) -> array
  (datetime uint) -> uint.

(** [@example min_rooms]
    - Sample: 1
    - Case: 1
    - Input [cleaning_time]: 120
    - Input [arrivals]: [{| year := 2013; month := 7; day := 1; hour := 15; minute := 59 |}; {| year := 2013; month := 7; day := 8; hour := 17; minute := 30 |}]
    - Input [departures]: [{| year := 2013; month := 7; day := 8; hour := 16; minute := 30 |}; {| year := 2013; month := 7; day := 15; hour := 12; minute := 0 |}]
    - Output [output]: 2
*)

(** [@example min_rooms]
    - Sample: 1
    - Case: 2
    - Input [cleaning_time]: 60
    - Input [arrivals]: [{| year := 2013; month := 7; day := 8; hour := 14; minute := 30 |}; {| year := 2013; month := 7; day := 1; hour := 16; minute := 0 |}; {| year := 2013; month := 7; day := 1; hour := 16; minute := 0 |}]
    - Input [departures]: [{| year := 2013; month := 7; day := 8; hour := 16; minute := 0 |}; {| year := 2013; month := 7; day := 15; hour := 12; minute := 0 |}; {| year := 2013; month := 7; day := 8; hour := 15; minute := 0 |}]
    - Output [output]: 3
*)

(** [@example min_rooms]
    - Sample: 1
    - Case: 3
    - Input [cleaning_time]: 360
    - Input [arrivals]: [{| year := 2016; month := 2; day := 21; hour := 14; minute := 0 |}; {| year := 2016; month := 3; day := 1; hour := 1; minute := 0 |}]
    - Input [departures]: [{| year := 2016; month := 2; day := 28; hour := 21; minute := 0 |}; {| year := 2016; month := 3; day := 2; hour := 12; minute := 57 |}]
    - Output [output]: 1
*)

(** [@example min_rooms]
    - Sample: 1
    - Case: 4
    - Input [cleaning_time]: 60
    - Input [arrivals]: [{| year := 2016; month := 2; day := 21; hour := 14; minute := 0 |}; {| year := 2016; month := 2; day := 28; hour := 12; minute := 0 |}]
    - Input [departures]: [{| year := 2016; month := 2; day := 28; hour := 11; minute := 0 |}; {| year := 2016; month := 3; day := 11; hour := 21; minute := 0 |}]
    - Output [output]: 1
*)

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
