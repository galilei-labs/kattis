(** * Weather Forecast *)

(** ** Description *)

(** Extrapolate each column of a time series using a least-squares line,
    clamping predictions to the column's permitted range and rounding
    integer-valued columns. Return missing predictions for columns with
    fewer than two observations.

    [@kattis vedurspa]
    - Difficulty: 9.6
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Temperature from -50 to 50 and wind speed from 0 to 80, each with one
      decimal place.
    - Integer wind direction from 0 to 360 and humidity from 0 to 110.
    - Measurements may be missing. *)

(** ** Examples *)

(** - Input convention: Observation/prediction counts, location/time metadata and four measurement columns; - marks missing data.
    - Output convention: One row per prediction: temperature, wind direction, wind speed and humidity; - omits a value.

    This sample illustrates the text format; its predictions are not reference results for the specified least-squares method. *)
(* Input:
72 1
63.9829 22.600517 50.9 2024-02-26 16:00:00
5.4 187 4.1 93
5.2 186 3.9 94
4.6 187 3.0 94
3.9 173 2.0 95
3.2 77 0.7 95
2.7 353 2.4 96
3.8 302 8.1 91
3.4 305 9.4 88
3.8 296 11.3 85
3.5 284 10.2 85
2.9 276 10.7 87
3.0 269 10.1 82
2.6 290 10.0 83
2.1 281 11.7 83
1.2 274 12.9 92
1.8 260 12.6 90
2.4 263 12.8 72
2.1 262 12.8 78
2.2 257 15.6 74
2.1 260 14.9 75
2.4 263 14.1 69
2.4 266 14.3 72
2.5 271 14.5 85
2.4 277 12.9 79
1.8 293 14.3 86
0.9 300 10.7 93
0.7 304 8.4 89
0.8 308 6.3 85
0.8 302 5.5 82
0.4 324 5.7 79
0.0 312 5.1 78
-0.3 301 5.7 77
0.0 308 4.9 70
-0.7 296 4.3 72
-0.9 314 2.2 73
-1.3 45 2.7 83
-1.2 45 2.7 83
-1.6 55 3.0 84
-2.0 102 2.3 86
-2.1 80 2.5 88
-1.6 88 3.2 86
-1.2 83 3.6 85
-0.6 60 3.9 84
-0.3 82 3.8 83
-0.1 77 2.8 77
0.9 61 3.9 70
0.7 73 4.7 74
1.1 79 3.1 71
1.1 71 2.3 73
1.1 49 1.8 70
0.3 39 2.1 78
-0.2 14 2.5 77
-0.3 21 2.2 75
-0.4 29 2.4 71
-0.8 23 2.4 72
-1.3 4 2.1 71
-1.7 21 2.8 73
-2.3 31 2.2 72
-2.4 59 2.7 67
-2.0 40 2.7 67
-1.9 38 2.7 68
-2.1 30 2.6 64
-2.1 44 3.4 60
-2.7 30 3.3 62
-2.8 30 3.9 64
-2.6 27 4.1 62
-1.8 27 4.8 53
-1.4 11 6.0 54
-0.9 18 6.6 58
-1.0 22 8.3 55
-1.0 10 8.1 52
-1.5 4 9.2 62
Output:
-1.5 10 7.6 64
*)

(** ** [@hide] Environment *)

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
From Stdlib Require Import ZArith NArith List Uint63 PArray
  Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope R_scope.

(* Math side. The n measurement lines are four parallel
   columns, line k being hour k ("the measurements are
   made one hour apart"). A temperature or a speed is the
   real its float denotes; a direction or a humidity an
   integer, read as a real by [col_R]. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** An integer column, read over the reals. *)
Definition col_R (column : list (option N)) : list
  (option R) :=
  map (option_map (fun value => IZR (Z.of_N value))) column.

(** Every [present] value of the column lies in [lower,
    upper]. *)
Definition col_in (lower upper : R)
  (column : list (option R)) : Prop :=
  Forall (fun cell => match cell with
                      | Some value => lower <= value <=
            upper
                      | None => True
                      end) column.

(** The number of [present] values of column. *)
Fixpoint present (column : list (option R)) : nat :=
  match column with
  | [] => 0%nat
  | None :: rest => present rest
  | Some _ :: rest => S (present rest)
  end.

(** The sum of the squared residuals of the line hour |->
    intercept + slope hour over the [present] values of
    column, its first cell being hour first_hour. *)
Fixpoint sse (intercept slope : R) (first_hour : nat)
    (column : list (option R)) : R :=
  match column with
  | [] => 0
  | None :: rest => sse intercept slope (S first_hour) rest
  | Some value :: rest =>
      (value - (intercept + slope * INR first_hour)) ^ 2 +
      sse intercept slope (S first_hour) rest
  end.

(** intercept + slope hour is a least-squares line of
    column. *)
Definition lsq_line (column : list (option R)) (intercept
  slope : R) : Prop :=
  forall intercept' slope',
    sse intercept slope 0 column <= sse intercept' slope' 0
      column.

(** Clamp. *)
Definition clamp (lower upper value : R) : R := Rmax lower
  (Rmin upper value).

(** predictions is a [forecast] of the [prediction_count]
    hours after column, within error_bound:
    [prediction_count] cells; cell j is missing iff
    column has fewer than two [present] values, and
    otherwise lies in [lower, upper] within error_bound
    of a least-squares line of column at hour [len]
    column + j, clamped to [lower, upper]. *)
Definition forecast (lower upper error_bound : R)
  (column : list (option R))
    (prediction_count : N) (predictions : list (option R)) :
      Prop :=
  len predictions = prediction_count /\
  forall j : nat, (N.of_nat j < prediction_count)%N ->
    (nth j predictions None = None <-> (present column <
      2)%nat) /\
    forall predicted, nth j predictions None = Some
      predicted ->
      lower <= predicted <= upper /\
      exists intercept slope, lsq_line column intercept
        slope /\
        Rabs (predicted - clamp lower upper
                (intercept + slope * INR (List.length column
        + j))
            )
          <= error_bound.

(** [@inside vedurspa_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (temperatures : list (option R))
    (wind_directions : list (option N))
      (wind_speeds : list (option R))
    (humidities : list (option N)) (prediction_count : N) :
      Prop := {
  (* n lines, each of temperature, wind direction, wind
     speed, humidity *)
  vi_d : len wind_directions = len temperatures;
  vi_s : len wind_speeds = len temperatures;
  vi_h : len humidities = len temperatures;
  (* temperatures are real numbers in the range -50 to 50 *)
  vi_t_range : col_in (-50) 50 temperatures;
  (* average wind directions are integers in the range 0
     to 360 *)
  vi_d_range : Forall (fun cell => match cell with
                                   | Some value =>
            (value <= 360)%N
                                   | None => True
                                   end) wind_directions;
  (* average wind speeds are real numbers in the range 0
     to 80 *)
  vi_s_range : col_in 0 80 wind_speeds;
  (* humidities are integers in the range 0 to 110 *)
  vi_h_range : Forall (fun cell => match cell with
                                   | Some value => (value <=
            110)%N
                                   | None => True
                                   end) humidities;
}.

(** Tol. *)
Definition tol : R := / 1000000.

(** ** Correctness *)

(** [@requirement]
    For prediction counts at most 4,194,303, each output column follows the specified
    least-squares fit, clamping, rounding and missing-data rules within the stated
    tolerances. Larger prediction counts are not constrained by this specification. *)
Definition vedurspa_spec
  (temperatures : list (option R))
  (wind_directions : list (option N))
  (wind_speeds : list (option R))
  (humidities : list (option N))
  (prediction_count : N)
  (output : list (option R) * list (option N) * list (option
    R) * list (option N))
  : Prop :=
  match output with
  | (temperature_preds, direction_preds, speed_preds,
    humidity_preds) =>
      (prediction_count <= 4194303)%N ->
      forecast (-50) 50 tol temperatures prediction_count
        temperature_preds /\
      forecast 0 360 (/2 + tol) (col_R wind_directions)
        prediction_count
        (col_R direction_preds) /\
      forecast 0 80 tol wind_speeds prediction_count
        speed_preds /\
      forecast 0 110 (/2 + tol) (col_R humidities)
        prediction_count
        (col_R humidity_preds)
  end.

(** ** Interface *)

(** Extrapolate each column of a time series using a least-squares line, clamping
    predictions to the column's permitted range and rounding integer-valued columns.
    Return missing predictions for columns with fewer than two observations.
    - Input [temperatures]:
    - Input [wind_directions]:
    - Input [wind_speeds]:
    - Input [humidities]:
    - Input [prediction_count]:
    - Output [output]: *)
Program vedurspa :
  array (option float) -> array (option uint) ->
  array (option float) -> array (option uint) -> uint ->
  array (option float) * array (option uint) *
  array (option float) * array (option uint).

(** ** Bridge *)

(** [@requirement vedurspa_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented [output] satisfying
    [vedurspa_spec]. *)
Specification vedurspa_correct :
  forall (temperatures : list (option R))
         (wind_directions : list (option N))
         (wind_speeds : list (option R)) (humidities : list
           (option N))
         (prediction_count : N)
         (temperatures_arr : array (option float))
         (wind_directions_arr : array (option uint))
         (wind_speeds_arr : array (option float))
         (humidities_arr : array (option uint))
         (prediction_count_int : uint),
  valid_input temperatures wind_directions wind_speeds
    humidities
    prediction_count ->
  repr temperatures_arr temperatures ->
  repr wind_directions_arr wind_directions ->
  repr wind_speeds_arr wind_speeds -> repr humidities_arr
    humidities ->
  repr prediction_count_int prediction_count ->
  exists output : list (option R) * list (option N) * list
    (option R) *
                  list (option N),
    repr (vedurspa temperatures_arr wind_directions_arr
      wind_speeds_arr
            humidities_arr prediction_count_int) output /\
    vedurspa_spec temperatures wind_directions wind_speeds
      humidities
      prediction_count output.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
