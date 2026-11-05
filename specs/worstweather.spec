(* @function        worstweather
   @signature       array sint -> array uint -> array sint -> array sint ->
                    array answer
   @math_signature  list Z -> list N -> list Z -> list Z -> list answer
   @summary         One test case: the known years ys (increasing) with
                    their rain rs, and m statements "year qx_k had the most
                    rain since year qy_k".  Answer k is Ans_true when every
                    year from qy_k to qx_k is known and the statement holds,
                    Ans_maybe when it is not true but some nonnegative
                    amounts of rain for the unknown years make it hold, and
                    Ans_false otherwise.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* The three outputs "true", "maybe", "false", on both sides. *)
Inductive answer := Ans_true | Ans_maybe | Ans_false.
Instance repr_answer : Repr answer answer := fun x i => x = i.

(* Math side.  Years are signed (the statement allows negatives), amounts of
   rain are nonnegative; the known years and their rain, and the two years
   of the queries, come as parallel lists, one per column of the input. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The element of index i of l (0-based). *)
Definition at_ {A} (l : list A) (d : A) (i : N) : A := nth (N.to_nat i) l d.

(* There is information about year z. *)
Definition known (ys : list Z) (z : Z) : Prop := In z ys.

(* An assignment of an amount of rain to every year that agrees with the
   information: year ys_i gets rs_i, the others any nonnegative integer. *)
Definition assignment (ys : list Z) (rs : list N) (f : Z -> N) : Prop :=
  forall i, (i < len ys)%N -> f (at_ ys 0 i) = at_ rs 0%N i.

(* "Year x had the most rain since year y" under the amounts f: it rained
   at most as much in x as in y, and less than in x in every year strictly
   between them. *)
Definition most_rain_since (f : Z -> N) (y x : Z) : Prop :=
  (f x <= f y)%N /\ (forall z, y < z < x -> (f z < f x)%N).

(* The statement is true: the rain of y, x and every year between them is
   known, and the statement holds of the known amounts. *)
Definition is_true (ys : list Z) (rs : list N) (y x : Z) : Prop :=
  (forall z, y <= z <= x -> known ys z) /\
  (forall f, assignment ys rs f -> most_rain_since f y x).

(* The statement might be true: some assignment makes it hold. *)
Definition might_be_true (ys : list Z) (rs : list N) (y x : Z) : Prop :=
  exists f, assignment ys rs f /\ most_rain_since f y x.

(* a is the answer to "year x had the most rain since year y". *)
Definition answers (ys : list Z) (rs : list N) (y x : Z) (a : answer) : Prop :=
  (a = Ans_true  <-> is_true ys rs y x) /\
  (a = Ans_maybe <-> ~ is_true ys rs y x /\ might_be_true ys rs y x) /\
  (a = Ans_false <-> ~ might_be_true ys rs y x).

(* The statement's guarantees, for one test case. *)
Record valid_input (ys : list Z) (rs : list N) (qy qx : list Z) : Prop := {
  (* 1 <= n <= 50 000, the number of years for which there is information
     (n = 0 is the terminator, not a test case) *)
  vi_n : (1 <= len ys <= 50000)%N;
  (* the i-th of these n lines contains y_i and r_i *)
  vi_rs : len rs = len ys;
  (* -10^9 <= y_i <= 10^9 *)
  vi_years : Forall (fun y => - 10 ^ 9 <= y <= 10 ^ 9) ys;
  (* 1 <= r_i <= 10^9 *)
  vi_rain : Forall (fun r => 1 <= r <= 10 ^ 9)%N rs;
  (* you may assume that y_i < y_(i+1) for 1 <= i < n *)
  vi_increasing : forall i, (i + 1 < len ys)%N ->
    at_ ys 0 i < at_ ys 0 (i + 1)%N;
  (* 1 <= m <= 10 000, the number of queries *)
  vi_m : (1 <= len qy <= 10000)%N;
  (* each of the m lines contains two years Y and X *)
  vi_qx : len qx = len qy;
  (* -10^9 <= Y < X <= 10^9 *)
  vi_queries : forall k, (k < len qy)%N ->
    - 10 ^ 9 <= at_ qy 0 k /\ at_ qy 0 k < at_ qx 0 k /\ at_ qx 0 k <= 10 ^ 9;
}.

(* One answer per query, in order: answer k is the answer to "year qx_k had
   the most rain since year qy_k". *)
Definition worstweather_spec (ys : list Z) (rs : list N) (qy qx : list Z)
    (o : list answer) : Prop :=
  len o = len qy /\
  forall k, (k < len qy)%N ->
    answers ys rs (at_ qy 0 k) (at_ qx 0 k) (at_ o Ans_false k).

Program worstweather :
  array sint -> array uint -> array sint -> array sint -> array answer.

Specification worstweather_correct :
  forall (ys : list Z) (rs : list N) (qy qx : list Z)
         (ys' : array sint) (rs' : array uint) (qy' qx' : array sint),
  valid_input ys rs qy qx ->
  repr ys' ys -> repr rs' rs -> repr qy' qy -> repr qx' qx ->
  exists o : list answer,
    repr (worstweather ys' rs' qy' qx') o /\ worstweather_spec ys rs qy qx o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
