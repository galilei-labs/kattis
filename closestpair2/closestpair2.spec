(** * Closest Pair *)

(** ** Description *)

(** One test case: [closestpair x_coordinates
    y_coordinates] takes the n >= 2 points
    (x_coordinates_k, y_coordinates_k) of the case,
    coordinates being exact decimals with at most two
    fractional digits, and returns the indices i, j of
    two distinct points whose squared Euclidean distance
    is minimal among all pairs of distinct points,
    exactly; any such pair, in either order. The harness
    prints x_coordinates_i y_coordinates_i
    x_coordinates_j y_coordinates_j.
    [@kattis closestpair2]
    - Difficulty: 5.2 *)

(** ** [@hide] Environment *)

(* @function        closestpair
   @signature       array sint -> array sint -> uint * uint
   @math_signature  list Q -> list Q -> N * N
   @summary         One test case: [closestpair x_coordinates y_coordinates]
                    takes the n >= 2 points (x_coordinates_k, y_coordinates_k)
                    of the case, coordinates being exact decimals with at most
                    two fractional digits, and returns the indices i, j of two
                    distinct points whose squared Euclidean distance is
                    minimal among all pairs of distinct points, exactly; any
                    such pair, in either order. The harness prints
                    x_coordinates_i y_coordinates_i x_coordinates_j
                    y_coordinates_j.
*)

From Stdlib Require Import ZArith NArith QArith Qabs List
  Uint63 Sint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Q_scope.

(** ** Definitions *)

(** [@hide] Machine coordinates. The OCaml harness
    parses each coordinate text exactly ("1.12",
    "-884.2", "158" become 112, -88420, 15800): a
    machine coordinate is a [sint] word counting
    hundredths, and it represents the rational number of
    that many hundredths. [Q] rather than [Z] hundredths
    on the math side so that the contract speaks of the
    statement's coordinates themselves, in the
    statement's unit. *)
Instance repr_hundredths : Repr sint Q :=
  fun coordinate_int coordinate =>
    coordinate == (Sint63.to_Z coordinate_int # 100).

(* Math side.  The points are two parallel lists, one per
  column of the
   input lines "x y". *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The k-th coordinate, for k < len l (0 outside, never
    relied on). *)
Definition get_list_Q (l : list Q) (k : N) : Q :=
  nth (N.to_nat k) l 0.

(** i and j are two distinct points of the input:
    distinct indices; two indices may hold the same
    point, at distance 0 (third sample case). *)
Definition point_pair (x_coordinates : list Q)
  (i j : N) : Prop :=
  (i < len x_coordinates)%N /\ (j < len x_coordinates)%N
    /\ i <> j.

(** The squared Euclidean distance between points i and
    j. *)
Definition dist2 (x_coordinates y_coordinates : list Q)
  (i j : N) : Q :=
  let delta_x :=
    get_list_Q x_coordinates i - get_list_Q x_coordinates j
    in
  let delta_y :=
    get_list_Q y_coordinates i - get_list_Q y_coordinates j
    in
  delta_x * delta_x + delta_y * delta_y.

(** coordinate has at most two decimals: it is a whole
    number of hundredths. *)
Definition two_decimals (coordinate : Q) : Prop :=
  exists hundredths : Z, coordinate == hundredths # 100.

(** [@inside closestpair_correct] The statement's bounds
    on one test case. *)
Record valid_input
  (x_coordinates y_coordinates : list Q) : Prop := {
  (* 2 <= n <= 100 000 *)
  vi_n : (2 <= len x_coordinates <= 100000)%N;
  (* n points, one per line, each of the form x y *)
  vi_ys : len y_coordinates = len x_coordinates;
  (* coordinates are floating point values with at most 2
    decimals *)
  vi_x_dec : Forall two_decimals x_coordinates;
  vi_y_dec : Forall two_decimals y_coordinates;
  (* ... and absolute value bounded by 100 000 *)
  vi_x : Forall
    (fun coordinate => Qabs coordinate <= 100000)
    x_coordinates;
  vi_y : Forall
    (fun coordinate => Qabs coordinate <= 100000)
    y_coordinates;
}.

(** ** Correctness *)

(** [@requirement] [@short must return a pair of points
    at minimum distance.] The answer, "any closest
    pair": two distinct points that no pair of distinct
    points is strictly closer than, exactly. Both
    point_pair and dist2 are symmetric in i and j, so
    (i, j) and (j, i) are equally accepted. *)
Definition closestpair_spec
  (x_coordinates y_coordinates : list Q)
  (output : N * N) : Prop :=
  match output with
  | (first, second) =>
      point_pair x_coordinates first second /\
      forall i j, point_pair x_coordinates i j ->
        dist2 x_coordinates y_coordinates first second
        <= dist2 x_coordinates y_coordinates i j
  end.

(** ** Interface *)

(** The machine-level interface.
    - Input [x_coordinates]:
    - Input [y_coordinates]:
    - Output [output]: *)
Program closestpair : array sint -> array sint
  -> uint * uint.

(** ** Bridge *)

(** [@requirement closestpair_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [closestpair_spec]. *)
Specification closestpair_correct :
  forall (x_coordinates y_coordinates : list Q)
         (x_coordinates_arr y_coordinates_arr : array sint),
    valid_input x_coordinates y_coordinates ->
    repr x_coordinates_arr x_coordinates ->
    repr y_coordinates_arr y_coordinates ->
    exists output : N * N,
      repr (closestpair x_coordinates_arr y_coordinates_arr)
        output /\
      closestpair_spec x_coordinates y_coordinates output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
