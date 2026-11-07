(* @function        vedurspa
   @signature       array (option float) -> array (option uint) ->
                    array (option float) -> array (option uint) -> uint ->
                    array (option float) * array (option uint) *
                    array (option float) * array (option uint)
   @math_signature  list (option R) -> list (option N) -> list (option R) ->
                    list (option N) -> N ->
                    list (option R) * list (option N) * list (option R) *
                    list (option N)
   @summary         [vedurspa temperatures wind_directions wind_speeds
                    humidities prediction_count] takes the four columns of
                    the n hourly measurements (temperature, wind direction,
                    wind speed, humidity; None is a missing value "-") and
                    predicts hours n .. n+prediction_count-1 of each column
                    by its least-squares line in the hour index, clamped to
                    the column's range: within 10^-6 for temperature and
                    speed, a nearest integer (within 1/2 + 10^-6) for
                    direction and humidity.  A column with fewer than two present values
                    is predicted as missing at every forecast hour.  Kattis
                    scores forecasts and has no correct answer: this is the
                    forced method (CLRS 28.3, least squares).
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope R_scope.

(* Math side.  The n measurement lines are four parallel columns, line k
   being hour k ("the measurements are made one hour apart").  A
   temperature or a speed is the real its float denotes; a direction or a
   humidity an integer, read as a real by [col_R]. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* An integer column, read over the reals. *)
Definition col_R (column : list (option N)) : list (option R) :=
  map (option_map (fun value => IZR (Z.of_N value))) column.

(* Every present value of the column lies in [lower, upper]. *)
Definition col_in (lower upper : R) (column : list (option R)) : Prop :=
  Forall (fun cell => match cell with
                      | Some value => lower <= value <= upper
                      | None => True
                      end) column.

(* The number of present values of column. *)
Fixpoint present (column : list (option R)) : nat :=
  match column with
  | [] => 0%nat
  | None :: rest => present rest
  | Some _ :: rest => S (present rest)
  end.

(* The sum of the squared residuals of the line
   hour |-> intercept + slope hour over the present values of column, its
   first cell being hour first_hour. *)
Fixpoint sse (intercept slope : R) (first_hour : nat)
    (column : list (option R)) : R :=
  match column with
  | [] => 0
  | None :: rest => sse intercept slope (S first_hour) rest
  | Some value :: rest =>
      (value - (intercept + slope * INR first_hour)) ^ 2 +
      sse intercept slope (S first_hour) rest
  end.

(* intercept + slope hour is a least-squares line of column. *)
Definition lsq_line (column : list (option R)) (intercept slope : R) : Prop :=
  forall intercept' slope',
    sse intercept slope 0 column <= sse intercept' slope' 0 column.

Definition clamp (lower upper value : R) : R := Rmax lower (Rmin upper value).

(* predictions is a forecast of the prediction_count hours after column,
   within error_bound: prediction_count cells; cell j is missing iff column
   has fewer than two present values, and otherwise lies in [lower, upper]
   within error_bound of a least-squares line of column at hour
   len column + j, clamped to [lower, upper]. *)
Definition forecast (lower upper error_bound : R) (column : list (option R))
    (prediction_count : N) (predictions : list (option R)) : Prop :=
  len predictions = prediction_count /\
  forall j : nat, (N.of_nat j < prediction_count)%N ->
    (nth j predictions None = None <-> (present column < 2)%nat) /\
    forall predicted, nth j predictions None = Some predicted ->
      lower <= predicted <= upper /\
      exists intercept slope, lsq_line column intercept slope /\
        Rabs (predicted - clamp lower upper
                (intercept + slope * INR (List.length column + j)))
          <= error_bound.

(* The statement's guarantees.  The header line (position, height, date,
   time) does not enter the contract, and is left to the harness.  "Exactly
   one digit after the decimal point" is a property of the input text,
   gone once parsed.  The statement bounds neither n nor
   prediction_count. *)
Record valid_input (temperatures : list (option R))
    (wind_directions : list (option N)) (wind_speeds : list (option R))
    (humidities : list (option N)) (prediction_count : N) : Prop := {
  (* n lines, each of temperature, wind direction, wind speed, humidity *)
  vi_d : len wind_directions = len temperatures;
  vi_s : len wind_speeds = len temperatures;
  vi_h : len humidities = len temperatures;
  (* temperatures are real numbers in the range -50 to 50 *)
  vi_t_range : col_in (-50) 50 temperatures;
  (* average wind directions are integers in the range 0 to 360 *)
  vi_d_range : Forall (fun cell => match cell with
                                   | Some value => (value <= 360)%N
                                   | None => True
                                   end) wind_directions;
  (* average wind speeds are real numbers in the range 0 to 80 *)
  vi_s_range : col_in 0 80 wind_speeds;
  (* humidities are integers in the range 0 to 110 *)
  vi_h_range : Forall (fun cell => match cell with
                                   | Some value => (value <= 110)%N
                                   | None => True
                                   end) humidities;
}.

Definition tol : R := / 1000000.

(* The four forecast columns.  An output of prediction_count cells exists
   only for prediction_count <= PArray.max_length = 4194303; beyond,
   nothing is required. *)
Definition vedurspa_spec (temperatures : list (option R))
    (wind_directions : list (option N)) (wind_speeds : list (option R))
    (humidities : list (option N)) (prediction_count : N)
    (output : list (option R) * list (option N) * list (option R) *
              list (option N))
    : Prop :=
  match output with
  | (temperature_preds, direction_preds, speed_preds, humidity_preds) =>
      (prediction_count <= 4194303)%N ->
      forecast (-50) 50 tol temperatures prediction_count temperature_preds /\
      forecast 0 360 (/2 + tol) (col_R wind_directions) prediction_count
        (col_R direction_preds) /\
      forecast 0 80 tol wind_speeds prediction_count speed_preds /\
      forecast 0 110 (/2 + tol) (col_R humidities) prediction_count
        (col_R humidity_preds)
  end.

Program vedurspa :
  array (option float) -> array (option uint) ->
  array (option float) -> array (option uint) -> uint ->
  array (option float) * array (option uint) *
  array (option float) * array (option uint).

Specification vedurspa_correct :
  forall (temperatures : list (option R))
         (wind_directions : list (option N))
         (wind_speeds : list (option R)) (humidities : list (option N))
         (prediction_count : N)
         (temperatures_arr : array (option float))
         (wind_directions_arr : array (option uint))
         (wind_speeds_arr : array (option float))
         (humidities_arr : array (option uint))
         (prediction_count_int : uint),
  valid_input temperatures wind_directions wind_speeds humidities
    prediction_count ->
  repr temperatures_arr temperatures ->
  repr wind_directions_arr wind_directions ->
  repr wind_speeds_arr wind_speeds -> repr humidities_arr humidities ->
  repr prediction_count_int prediction_count ->
  exists output : list (option R) * list (option N) * list (option R) *
                  list (option N),
    repr (vedurspa temperatures_arr wind_directions_arr wind_speeds_arr
            humidities_arr prediction_count_int) output /\
    vedurspa_spec temperatures wind_directions wind_speeds humidities
      prediction_count output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.

(* The four classical axioms Stdlib's reals rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec ClassicalDedekindReals.sig_not_dec Classical_Prop.classic FunctionalExtensionality.functional_extensionality_dep.
