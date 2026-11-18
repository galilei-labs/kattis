(** * Intersecting Rectangles *)

(** ** Description *)

(** Decide whether any two axis-aligned rectangles have intersecting
    boundaries. Strict containment without boundary contact does not count.

    [@kattis intersectingrectangles]
    - Difficulty: 5.4
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Rectangle count: $1 \le n \le 10^{5}$.
    - Integer coordinates: $-10^{9} \le x \le 10^{9}$; each rectangle has positive
      width and height.
    - All horizontal coordinates are distinct, as are all vertical
      coordinates. *)

(** ** Examples *)

(** - Input convention: Rectangle count, followed by lower-left and upper-right corner coordinates.
    - Output convention: 1 if any rectangle boundaries intersect; 0 otherwise. *)
(* Input:
3
0 0 2 2
1 1 3 4
5 7 6 8
Output:
1
*)

(** ** [@hide] Environment *)
(* @function        intersecting_rectangles
   @signature       array sint -> array sint -> array sint -> array sint -> bool
   @math_signature  list Z -> list Z -> list Z -> list Z -> bool
   @summary         Rectangle i has lower left corner (lefts_i, bottoms_i)
                    and upper right corner (rights_i, tops_i).  The answer
                    is true exactly when two distinct rectangles have
                    boundaries with a common point of the real plane (a
                    rectangle nested strictly inside another does not
                    count).
                    It runs in at most c1 * (n + 1) * (log2 n + 1) + c2
                    steps of the cost model on a valid input, n the number
                    of rectangles (the sort of the events, then one
                    balanced-tree operation per event, each within its
                    depth, logarithmic by the balance invariant), for two
                    constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Reals.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The integer coordinate at zero-based rectangle index [i] in [column], or zero
    beyond the end. *)
Definition entry (column : list Z) (i : N) : Z :=
  nth (N.to_nat i) column 0.
(** The coordinate at index [i] in [column], embedded in the real numbers. *)
Definition coord (column : list Z) (i : N) : R :=
  IZR (entry column i).

(** The point [(point_x, point_y)] lies in the closed rectangle at index [i]
    and on at least one of its four sides. *)
Definition on_boundary
  (lefts bottoms rights tops : list Z) (i : N)
    (point_x point_y : R) : Prop :=
  (coord lefts i <= point_x <= coord rights i)%R /\
  (coord bottoms i <= point_y <= coord tops i)%R /\
  (point_x = coord lefts i \/ point_x = coord rights i \/
   point_y = coord bottoms i \/ point_y = coord tops i).

(** The boundaries of rectangles [i] and [j] have a common point. *)
Definition intersect
  (lefts bottoms rights tops : list Z) (i j : N)
    : Prop :=
  exists point_x point_y : R,
    on_boundary lefts bottoms rights tops i point_x point_y
      /\
    on_boundary lefts bottoms rights tops j point_x point_y.

(** The boundaries of some two distinct input rectangles have a common point. *)
Definition some_pair_intersects
  (lefts bottoms rights tops : list Z)
    : Prop :=
  exists i j : N, (i < j < len lefts)%N /\
    intersect lefts bottoms rights tops i j.

(** [@inside intersecting_rectangles_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input
  (lefts bottoms rights tops : list Z) : Prop := {
  (* 1 <= n <= 10^5, n the number of rectangles *)
  vi_n : (1 <= len lefts <= 10 ^ 5)%N;
  (* each of the next n lines contains four integers x1
     y1 x2 y2 *)
  vi_y1_len : len bottoms = len lefts;
  vi_x2_len : len rights = len lefts;
  vi_y2_len : len tops = len lefts;
  (* -10^9 <= x1, y1, x2, y2 <= 10^9 *)
  vi_x1 : Forall (fun coordinate => - 10 ^ 9 <= coordinate
    <= 10 ^ 9) lefts;
  vi_y1 : Forall (fun coordinate => - 10 ^ 9 <= coordinate
    <= 10 ^ 9)
            bottoms;
  vi_x2 : Forall (fun coordinate => - 10 ^ 9 <= coordinate
    <= 10 ^ 9)
            rights;
  vi_y2 : Forall (fun coordinate => - 10 ^ 9 <= coordinate
    <= 10 ^ 9) tops;
  (* x1 < x2, y1 < y2 *)
  vi_x_order : forall i, (i < len lefts)%N ->
    entry lefts i < entry rights i;
  vi_y_order : forall i, (i < len lefts)%N ->
    entry bottoms i < entry tops i;
  (* all x values will be distinct *)
  vi_x_distinct : NoDup (lefts ++ rights);
  (* all y values will be distinct *)
  vi_y_distinct : NoDup (bottoms ++ tops);
}.

(** ** Correctness *)

(** [@requirement]
    The output is true exactly when two rectangle boundaries intersect; strict
    containment without boundary contact is excluded. *)
Definition intersecting_rectangles_spec
  (lefts bottoms rights tops : list Z)
    (output : bool) : Prop :=
  output = true <-> some_pair_intersects lefts bottoms rights tops.

(** ** Complexity *)

(** [@requirement] Runs in $O(n \log(n+1))$ steps, where $n$ is the number of rectangles. *)
Definition intersecting_rectangles_time_spec (c1 c2 n_lefts steps : nat) : Prop :=
  (steps <= c1 * ((n_lefts + 1) * (Nat.log2 (n_lefts) + 1)) + c2)%nat.

(** ** Interface *)

(** Test whether two distinct rectangles have a point in common on their
    boundaries. Containment alone, without boundary contact, does not count.
    - Input [lefts]: Left horizontal coordinate of each rectangle.
    - Input [bottoms]: Bottom vertical coordinate of each rectangle.
    - Input [rights]: Right horizontal coordinate of each rectangle.
    - Input [tops]: Top vertical coordinate of each rectangle.
    - Output [output]: The output is true exactly when two rectangle boundaries intersect; strict containment without boundary contact is excluded. *)
Program intersecting_rectangles :
  array sint -> array sint -> array sint -> array sint ->
    bool.

(** [@example intersecting_rectangles]
    - Sample: 1
    - Input [lefts]: [0; 1; 5]%Z
    - Input [bottoms]: [0; 1; 7]%Z
    - Input [rights]: [2; 3; 6]%Z
    - Input [tops]: [2; 4; 8]%Z
    - Output [output]: true
*)

(** ** Bridge *)

(** [@requirement intersecting_rectangles_spec] [@fold full correctness
    statement] On valid represented inputs,
    [intersecting_rectangles] returns a represented output
    satisfying [intersecting_rectangles_spec]. *)
Specification intersecting_rectangles_correct :
  forall (lefts bottoms rights tops : list Z)
         (lefts_arr bottoms_arr rights_arr tops_arr : array
           sint),
  valid_input lefts bottoms rights tops ->
  repr lefts_arr lefts -> repr bottoms_arr bottoms ->
  repr rights_arr rights -> repr tops_arr tops ->
  exists output : bool,
    repr (intersecting_rectangles lefts_arr bottoms_arr
      rights_arr tops_arr)
      output /\
    intersecting_rectangles_spec lefts bottoms rights tops
      output.

(** ** Complexity *)

(** [@hide] [intersecting_rectangles_cost] is the cost translation of [intersecting_rectangles] (the judge
    recomputes it and compares) ... *)
Complexity intersecting_rectangles_cost for intersecting_rectangles.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) * (log2 n + 1) + c2 steps of the cost model on a valid input, n the number of rectangles (the sort of the events, then one balanced-tree operation per event, each within its depth, logarithmic by the balance invariant), for two constants
    quantified before the inputs, on every valid input. [@requirement intersecting_rectangles_time_spec] *)
Specification intersecting_rectangles_time : exists c1 c2 : nat,
  forall (lefts bottoms rights tops : list Z)
  (lefts_arr bottoms_arr rights_arr tops_arr : array
  sint),
  valid_input lefts bottoms rights tops ->
  repr lefts_arr lefts -> repr bottoms_arr bottoms ->
  repr rights_arr rights -> repr tops_arr tops ->
  intersecting_rectangles_time_spec c1 c2 (size lefts_arr) (cost4 intersecting_rectangles_cost lefts_arr bottoms_arr rights_arr tops_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.

(** [@hide] The four classical axioms Stdlib's reals rest on: the math
    side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
