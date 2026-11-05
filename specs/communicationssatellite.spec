(* @function        communicationssatellite
   @signature       array sint -> array sint -> array uint -> float
   @math_signature  list Z -> list Z -> list N -> R
   @summary         Dish i is the circle of centre (xs_i, ys_i) and radius
                    rs_i ; no two dishes overlap.  A compliant design is a
                    set of straight beams, each joining a point on the
                    circumference of one dish to a point on the circumference
                    of a different dish, such that no two beams share a
                    point, no beam enters the interior of a dish, and dishes
                    and beams form one connected structure.  The result is
                    the minimum total beam length of a compliant design, with
                    absolute or relative error below 10^-6.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals.
From Stdlib Require Import Relation_Operators.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope R_scope.

(* Math side.  The coordinates are signed (sint), the radii positive
   (uint) ; all geometry is exact, in R. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

Definition point : Type := R * R.

(* A beam is the segment between its two end points. *)
Definition beam : Type := point * point.

Definition sqdist (p q : point) : R :=
  (fst p - fst q) ^ 2 + (snd p - snd q) ^ 2.

Definition on_beam (b : beam) (z : point) : Prop :=
  exists t, 0 <= t <= 1 /\
    z = (fst (fst b) + t * (fst (snd b) - fst (fst b)),
         snd (fst b) + t * (snd (snd b) - snd (fst b))).

Definition beam_length (b : beam) : R := sqrt (sqdist (fst b) (snd b)).

Definition total_length (d : list beam) : R :=
  fold_right (fun b s => beam_length b + s) 0 d.

Section Dishes.

Variables (xs ys : list Z) (rs : list N).

Definition is_dish (i : N) : Prop := (i < len xs)%N.

Definition centre (i : N) : point :=
  (IZR (nth (N.to_nat i) xs 0%Z), IZR (nth (N.to_nat i) ys 0%Z)).
Definition radius (i : N) : R := IZR (Z.of_N (nth (N.to_nat i) rs 0%N)).

Definition on_circle (i : N) (z : point) : Prop :=
  sqdist z (centre i) = radius i ^ 2.
Definition in_interior (i : N) (z : point) : Prop :=
  sqdist z (centre i) < radius i ^ 2.

(* Two different dishes may touch but not overlap. *)
Definition no_overlap : Prop :=
  forall i j, is_dish i -> is_dish j -> i <> j ->
    (radius i + radius j) ^ 2 <= sqdist (centre i) (centre j).

Definition joins_two_dishes (b : beam) : Prop :=
  exists i j, is_dish i /\ is_dish j /\ i <> j /\
    on_circle i (fst b) /\ on_circle j (snd b).

(* Two beams neither cross nor attach to each other : they share no point. *)
Definition apart (b b' : beam) : Prop :=
  forall z, on_beam b z -> ~ on_beam b' z.

Definition occludes_no_dish (b : beam) : Prop :=
  forall i z, is_dish i -> on_beam b z -> ~ in_interior i z.

Definition touch (i j : N) : Prop :=
  i <> j /\ sqdist (centre i) (centre j) = (radius i + radius j) ^ 2.

Definition meets (b : beam) (i : N) : Prop :=
  exists z, on_beam b z /\ sqdist z (centre i) <= radius i ^ 2.

(* Dishes i and j are directly connected : they touch, or one beam meets
   both. *)
Definition linked (d : list beam) (i j : N) : Prop :=
  is_dish i /\ is_dish j /\
  (touch i j \/ exists b, In b d /\ meets b i /\ meets b j).

(* As beams never meet one another, dishes and beams form one connected
   structure exactly when every two dishes are related through [linked]. *)
Definition connected (d : list beam) : Prop :=
  forall i j, is_dish i -> is_dish j -> clos_refl_trans N (linked d) i j.

Definition compliant (d : list beam) : Prop :=
  Forall joins_two_dishes d /\ ForallOrdPairs apart d /\
  Forall occludes_no_dish d /\ connected d.

(* m is the least total beam length of a compliant design, and is reached. *)
Definition minimum_cost (m : R) : Prop :=
  (exists d, compliant d /\ total_length d = m) /\
  (forall d, compliant d -> m <= total_length d).

End Dishes.

(* The statement's bounds. *)
Record valid_input (xs ys : list Z) (rs : list N) : Prop := {
  (* 1 <= N <= 2000, the number of dish antennas *)
  vi_n : (1 <= len xs <= 2000)%N;
  (* N lines, each of which contains three integers X, Y and R *)
  vi_len_ys : len ys = len xs;
  vi_len_rs : len rs = len xs;
  (* -1000 <= X, Y <= 1000 *)
  vi_xs : Forall (fun x => (-1000 <= x <= 1000)%Z) xs;
  vi_ys : Forall (fun y => (-1000 <= y <= 1000)%Z) ys;
  (* 1 <= R <= 100 *)
  vi_rs : Forall (fun r => (1 <= r <= 100)%N) rs;
  (* NASA guarantees that no two dish antennas overlap *)
  vi_no_overlap : no_overlap xs ys rs;
}.

(* The answer is correct if the absolute or relative error is less than
   10^-6. *)
Definition within_tolerance (v m : R) : Prop :=
  Rabs (v - m) < / 10 ^ 6 \/ Rabs (v - m) < Rabs m / 10 ^ 6.

Definition communicationssatellite_spec
    (xs ys : list Z) (rs : list N) (v : R) : Prop :=
  exists m, minimum_cost xs ys rs m /\ within_tolerance v m.

(* machine side : gets extracted *)
Program communicationssatellite :
  array sint -> array sint -> array uint -> float.

(* Glue between machine and math worlds *)
Specification communicationssatellite_correct :
  forall (xs ys : list Z) (rs : list N)
         (x y : array sint) (r : array uint),
    valid_input xs ys rs -> repr x xs -> repr y ys -> repr r rs ->
    exists v : R, repr (communicationssatellite x y r) v /\
      communicationssatellite_spec xs ys rs v.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.

(* The four classical axioms Stdlib's reals rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec ClassicalDedekindReals.sig_not_dec Classical_Prop.classic FunctionalExtensionality.functional_extensionality_dep.
