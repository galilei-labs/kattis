(** * Closest Pair *)

(** ** Description *)

(** Find two distinct points with minimum Euclidean distance, using exact
    decimal coordinates.

    [@kattis closestpair2]
    - Difficulty: 5.2
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Point count: $2 \le n \le 10^{5}$.
    - Coordinates have at most two decimal places and absolute value at most
      $10^{5}$. *)

(** ** Examples *)

(** - Input convention: Per case: point count and coordinate pairs; a zero count ends input.
    - Output convention: Four coordinates x1 y1 x2 y2 describing any closest pair, one line per case. *)
(* Input:
2
1.12 0
0 0.51
3
158 12
123 15
1859 -1489
3
21.12 -884.2
18.18 43.34
21.12 -884.2
0
Output:
0.0 0.51 1.12 0.00
123 15 158 12.00
21.12 -884.20 21.12 -884.20
*)

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
                    It runs in at most c1 * (n + 1) * (log2 n + 1) + c2
                    steps of the cost model on a valid input, n the number
                    of points (the presort, then the divide and conquer with
                    a linear merge and strip per level), for two constants
                    c1, c2.
*)

From Stdlib Require Import ZArith NArith QArith Qabs List
  Uint63 Sint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope Q_scope.

(** ** Definitions *)

(** [@hide] Machine coordinates. The OCaml harness
    parses each coordinate text exactly ("1.12",
    "-884.2", "158" become 112, -88420, 15800): a
    machine coordinate is a [sint] word counting
    hundredths, and it represents the rational number of
    that many hundredths. [Q] rather than [Z] hundredths
    in the specification so that the contract speaks of the
    statement's coordinates themselves, in the
    statement's unit. *)
Instance repr_hundredths : Repr sint Q :=
  fun coordinate_int coordinate =>
    coordinate == (Sint63.to_Z coordinate_int # 100).

(* The points are two parallel lists, one per
  column of the
   input lines "x y". *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [k] in [l], or zero beyond the end. *)
Definition get_list_Q (l : list Q) (k : N) : Q :=
  nth (N.to_nat k) l 0.

(** [i] and [j] are distinct valid input indices. Their coordinates may coincide,
    giving distance zero. *)
Definition point_pair (x_coordinates : list Q)
  (i j : N) : Prop :=
  (i < len x_coordinates)%N /\ (j < len x_coordinates)%N
    /\ i <> j.

(** The squared Euclidean distance between the points at indices [i] and [j]. *)
Definition dist2 (x_coordinates y_coordinates : list Q)
  (i j : N) : Q :=
  let delta_x :=
    get_list_Q x_coordinates i - get_list_Q x_coordinates j
    in
  let delta_y :=
    get_list_Q y_coordinates i - get_list_Q y_coordinates j
    in
  delta_x * delta_x + delta_y * delta_y.

(** [coordinate] is an integer multiple of one hundredth. *)
Definition two_decimals (coordinate : Q) : Prop :=
  exists hundredths : Z, coordinate == hundredths # 100.

(** [@inside closestpair_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input
  (x_coordinates y_coordinates : list Q) : Prop := {
  (* 2 <= n <= 10^5 *)
  vi_n : (2 <= len x_coordinates <= 100000)%N;
  (* n points, one per line, each of the form x y *)
  vi_ys : len y_coordinates = len x_coordinates;
  (* coordinates are floating point values with at most 2
    decimals *)
  vi_x_dec : Forall two_decimals x_coordinates;
  vi_y_dec : Forall two_decimals y_coordinates;
  (* ... and absolute value bounded by 10^5 *)
  vi_x : Forall
    (fun coordinate => Qabs coordinate <= 100000)
    x_coordinates;
  vi_y : Forall
    (fun coordinate => Qabs coordinate <= 100000)
    y_coordinates;
}.

(** ** Correctness *)

(** [@requirement]
    The output identifies two distinct input positions attaining the minimum Euclidean
    distance between the exact decimal coordinates. *)
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

(** ** Complexity *)

(** [@requirement] Runs in $O(n \log(n+1))$ steps, where $n$ is the number of points. *)
Definition closestpair_time_spec (c1 c2 n_x_coordinates steps : nat) : Prop :=
  (steps <= c1 * ((n_x_coordinates + 1) * (Nat.log2 (n_x_coordinates) + 1)) + c2)%nat.

(** ** Interface *)

(** Find two distinct points with minimum Euclidean distance, using exact decimal
    coordinates.
    - Input [x_coordinates]: Horizontal coordinates of the input points.
    - Input [y_coordinates]: Vertical coordinates of the corresponding points.
    - Output [output]: The output identifies two distinct input positions attaining the minimum Euclidean distance between the exact decimal coordinates. *)
Program closestpair : array sint -> array sint
  -> uint * uint.

(** [@example closestpair]
    - Sample: 1
    - Case: 1
    - Input [x_coordinates]: [1.12; 0]%Q
    - Input [y_coordinates]: [0; 0.51]%Q
    - Output [output]: (1, 0)
*)

(** [@example closestpair]
    - Sample: 1
    - Case: 2
    - Input [x_coordinates]: [158; 123; 1859]%Q
    - Input [y_coordinates]: [12; 15; -1489]%Q
    - Output [output]: (1, 0)
*)

(** [@example closestpair]
    - Sample: 1
    - Case: 3
    - Input [x_coordinates]: [21.12; 18.18; 21.12]%Q
    - Input [y_coordinates]: [-884.2; 43.34; -884.2]%Q
    - Output [output]: (0, 2)
*)

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

(** ** Complexity *)

(** [@hide] [closestpair_cost] is the cost translation of [closestpair] (the judge
    recomputes it and compares) ... *)
Complexity closestpair_cost for closestpair.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) * (log2 n + 1) + c2 steps of the cost model on a valid input, n the number of points (the presort, then the divide and conquer with a linear merge and strip per level), for two constants
    quantified before the inputs, on every valid input. [@requirement closestpair_time_spec] *)
Specification closestpair_time : exists c1 c2 : nat,
  forall (x_coordinates y_coordinates : list Q)
  (x_coordinates_arr y_coordinates_arr : array sint),
  valid_input x_coordinates y_coordinates ->
  repr x_coordinates_arr x_coordinates ->
  repr y_coordinates_arr y_coordinates ->
  closestpair_time_spec c1 c2 (size x_coordinates_arr) (cost2 closestpair_cost x_coordinates_arr y_coordinates_arr).

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
