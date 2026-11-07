(** * Communications Satellite *)

(** ** Description *)

(** Dish i is the circle of centre (x_coordinates_i,
    y_coordinates_i) and radius radii_i ; no two dishes
    overlap. A compliant design is a set of straight
    beams, each joining a point on the circumference of
    one dish to a point on the circumference of a
    different dish, such that no two beams share a
    point, no beam enters the interior of a dish, and
    dishes and beams form one connected structure. The
    result is the minimum total beam length of a
    compliant design, with absolute or relative error
    below 10^-6.
    [@kattis communicationssatellite]
    - Difficulty: 2.9 *)

(** ** [@hide] Environment *)

(* @function        communicationssatellite
   @signature       array sint -> array sint -> array uint -> float
   @math_signature  list Z -> list Z -> list N -> R
   @summary         Dish i is the circle of centre (x_coordinates_i,
                    y_coordinates_i) and radius radii_i ; no two dishes
                    overlap.  A compliant design is a set of straight beams,
                    each joining a point on the circumference of one dish to a
                    point on the circumference of a different dish, such that
                    no two beams share a point, no beam enters the interior
                    of a dish, and dishes and beams form one connected
                    structure.  The result is the minimum total beam length
                    of a compliant design, with absolute or relative error
                    below 10^-6.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Floats Reals.
From Stdlib Require Import Relation_Operators.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope R_scope.

(* Math side.  The coordinates are signed
  (sint), the radii positive
   (uint) ; all geometry is exact, in R. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** A point in the plane. *)
Definition point : Type := R * R.

(** A beam is the segment between its two end points. *)
Definition beam : Type := point * point.

(** The squared Euclidean distance between two points. *)
Definition sqdist (location location' : point) : R :=
  (fst location - fst location') ^ 2 +
    (snd location - snd location') ^ 2.

(** The point lies on the closed beam segment. *)
Definition on_beam (segment : beam)
  (location : point) : Prop :=
  exists fraction, 0 <= fraction <= 1 /\
    location =
      (fst (fst segment) + fraction * (fst
        (snd segment) - fst (fst segment)),
       snd (fst segment) + fraction * (snd
         (snd segment) - snd (fst segment))).

(** The Euclidean length of the beam. *)
Definition beam_length (segment : beam) : R :=
  sqrt (sqdist (fst segment) (snd segment)).

(** The sum of all beam lengths in the design. *)
Definition total_length (design : list beam) : R :=
  fold_right
    (fun segment subtotal => beam_length segment + subtotal)
    0 design.

Section Dishes.

Variables (x_coordinates y_coordinates : list Z)
  (radii : list N).

(** The index names an input dish. *)
Definition is_dish (i : N) : Prop :=
  (i < len x_coordinates)%N.

(** The centre of dish [i]. *)
Definition centre (i : N) : point :=
  (IZR (nth (N.to_nat i) x_coordinates 0%Z),
   IZR (nth (N.to_nat i) y_coordinates 0%Z)).
(** The radius of dish [i]. *)
Definition radius (i : N) : R :=
  IZR (Z.of_N (nth (N.to_nat i) radii 0%N)).

(** The point lies on the circumference of dish [i]. *)
Definition on_circle (i : N) (location : point) : Prop :=
  sqdist location (centre i) = radius i ^ 2.
(** The point lies strictly inside dish [i]. *)
Definition in_interior (i : N) (location : point) : Prop :=
  sqdist location (centre i) < radius i ^ 2.

(** Two different dishes may touch but not overlap. *)
Definition no_overlap : Prop :=
  forall i j, is_dish i -> is_dish j -> i <> j ->
    (radius i + radius j) ^ 2 <= sqdist (centre i)
      (centre j).

(** The beam endpoints lie on two different dishes. *)
Definition joins_two_dishes (segment : beam) : Prop :=
  exists i j, is_dish i /\ is_dish j /\ i <> j /\
    on_circle i (fst segment) /\ on_circle j (snd segment).

(** Two beams neither cross nor attach to each other :
    they share no point. *)
Definition apart (segment segment' : beam) : Prop :=
  forall location, on_beam segment location
    -> ~ on_beam segment' location.

(** The beam does not pass through any dish interior. *)
Definition occludes_no_dish (segment : beam) : Prop :=
  forall i location, is_dish i -> on_beam segment location
    ->
    ~ in_interior i location.

(** The two distinct dishes touch externally. *)
Definition touch (i j : N) : Prop :=
  i <> j /\ sqdist (centre i) (centre j) =
    (radius i + radius j) ^ 2.

(** The beam intersects the closed disk of dish [i]. *)
Definition meets (segment : beam) (i : N) : Prop :=
  exists location, on_beam segment location /\
    sqdist location (centre i) <= radius i ^ 2.

(** Dishes i and j are directly connected : they touch,
    or one beam meets both. *)
Definition linked (design : list beam) (i j : N) : Prop :=
  is_dish i /\ is_dish j /\
  (touch i j \/
   exists segment, In segment design /\ meets segment i
     /\ meets segment j).

(** As beams never meet one another, dishes and beams
    form one connected structure exactly when every two
    dishes are related through [linked]. *)
Definition connected (design : list beam) : Prop :=
  forall i j, is_dish i -> is_dish j -> clos_refl_trans N
    (linked design) i j.

(** The beams join dishes without crossing or occlusion,
    and connect all dishes. *)
Definition compliant (design : list beam) : Prop :=
  Forall joins_two_dishes design
    /\ ForallOrdPairs apart design /\
  Forall occludes_no_dish design /\ connected design.

(** best_cost is the least total beam length of a
    compliant design, and is reached. *)
Definition minimum_cost (best_cost : R) : Prop :=
  (exists design, compliant design
    /\ total_length design = best_cost) /\
  (forall design, compliant design
    -> best_cost <= total_length design).

End Dishes.

(** [@inside communicationssatellite_correct] The
    statement's bounds. *)
Record valid_input (x_coordinates y_coordinates : list Z)
  (radii : list N)
  : Prop := {
  (* 1 <= N <= 2000, the number of dish antennas *)
  vi_n : (1 <= len x_coordinates <= 2000)%N;
  (* N lines, each of which contains three integers X, Y and
    R *)
  vi_len_ys : len y_coordinates = len x_coordinates;
  vi_len_rs : len radii = len x_coordinates;
  (* -1000 <= X, Y <= 1000 *)
  vi_xs : Forall (fun x_coordinate =>
    (-1000 <= x_coordinate <= 1000)%Z)
            x_coordinates;
  vi_ys : Forall (fun y_coordinate =>
    (-1000 <= y_coordinate <= 1000)%Z)
            y_coordinates;
  (* 1 <= R <= 100 *)
  vi_rs : Forall (fun dish_radius =>
    (1 <= dish_radius <= 100)%N) radii;
  (* NASA guarantees that no two dish antennas overlap *)
  vi_no_overlap : no_overlap x_coordinates y_coordinates
    radii;
}.

(** The answer is correct if the absolute or relative
    error is less than 10^-6. *)
Definition within_tolerance
  (printed_cost best_cost : R) : Prop :=
  Rabs (printed_cost - best_cost) < / 10 ^ 6 \/
  Rabs (printed_cost - best_cost) < Rabs best_cost / 10 ^ 6.

(** ** Correctness *)

(** [@requirement] [@short must return the minimum
    connection cost within tolerance.] The result
    satisfies the mathematical requirements. *)
Definition communicationssatellite_spec
    (x_coordinates y_coordinates : list Z) (radii : list N)
    (output : R) : Prop :=
  exists best_cost, minimum_cost x_coordinates y_coordinates
    radii best_cost /\
    within_tolerance output best_cost.

(** ** Interface *)

(** The machine-level interface.
    - Input [x_coordinates]:
    - Input [y_coordinates]:
    - Input [radii]:
    - Output [output]: *)
Program communicationssatellite :
  array sint -> array sint -> array uint -> float.

(** ** Bridge *)

(** [@requirement communicationssatellite_spec] [@fold
    full correctness statement] On valid represented
    inputs, the program returns a represented output
    satisfying [communicationssatellite_spec]. *)
Specification communicationssatellite_correct :
  forall (x_coordinates y_coordinates : list Z)
    (radii : list N)
         (x_coordinates_arr y_coordinates_arr : array sint)
         (radii_arr : array uint),
    valid_input x_coordinates y_coordinates radii ->
    repr x_coordinates_arr x_coordinates ->
    repr y_coordinates_arr y_coordinates
      -> repr radii_arr radii ->
    exists output : R,
      repr (communicationssatellite x_coordinates_arr
        y_coordinates_arr
              radii_arr) output /\
      communicationssatellite_spec x_coordinates
        y_coordinates radii
        output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.

(** [@hide] The four classical axioms Stdlib's reals
    rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
