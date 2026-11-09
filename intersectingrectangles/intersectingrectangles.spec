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
    - Integer coordinates in $[-10^{9}, 10^{9}]$; each rectangle has positive
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
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Reals.
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The i-th entry of a column (rectangle i's coordinate), and the same
    as a real number. *)
Definition entry (column : list Z) (i : N) : Z :=
  nth (N.to_nat i) column 0.
(** The [coord] definition. *)
Definition coord (column : list Z) (i : N) : R :=
  IZR (entry column i).

(** The point (point_x, point_y) lies on the boundary of rectangle i :
    in the closed rectangle, and on one of its four sides. *)
Definition on_boundary
  (lefts bottoms rights tops : list Z) (i : N)
    (point_x point_y : R) : Prop :=
  (coord lefts i <= point_x <= coord rights i)%R /\
  (coord bottoms i <= point_y <= coord tops i)%R /\
  (point_x = coord lefts i \/ point_x = coord rights i \/
   point_y = coord bottoms i \/ point_y = coord tops i).

(** The boundaries of rectangles i and j have a common point. *)
Definition intersect
  (lefts bottoms rights tops : list Z) (i j : N)
    : Prop :=
  exists point_x point_y : R,
    on_boundary lefts bottoms rights tops i point_x point_y
      /\
    on_boundary lefts bottoms rights tops j point_x point_y.

(** Some pair of distinct rectangles intersect. *)
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
  match output with
  | true => some_pair_intersects lefts bottoms rights tops
  | false => ~ some_pair_intersects lefts bottoms rights
    tops
  end.

(** ** Interface *)

(** The [intersecting_rectangles] program on machine values.
    - Input [lefts]: Left horizontal coordinate of each rectangle.
    - Input [bottoms]: Bottom vertical coordinate of each rectangle.
    - Input [rights]: Right horizontal coordinate of each rectangle.
    - Input [tops]: Top vertical coordinate of each rectangle.
    - Output [output]: The output is true exactly when two rectangle boundaries intersect; strict containment without boundary contact is excluded. *)
Program intersecting_rectangles :
  array sint -> array sint -> array sint -> array sint ->
    bool.

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

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.

(** [@hide] The four classical axioms Stdlib's reals rest on: the math
    side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
