(* @function        solve
   @signature       uint -> array (array float) -> array float
                    -> outcome (array float)
   @math_signature  N -> list (list R) -> list R -> outcome (list R)
   @summary         [solve unknown_count matrix right_sides] decides the
                    linear system matrix x = right_sides over the reals,
                    matrix being unknown_count rows of unknown_count
                    coefficients and right_sides the unknown_count
                    right-hand sides, the system being the exact one the
                    input floats denote : Unique approximation when it has
                    exactly one solution, approximation holding
                    unknown_count floats each within 10^-3 of the
                    corresponding component of that solution (wherever a
                    float lies within 10^-3 of it) ; Multiple when it has
                    several ; Inconsistent when it has none.  The harness
                    prints approximation, "multiple" or "inconsistent"
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* The answer, on both sides : V is array float on the machine side,
   list R on the math side. *)
Inductive outcome (V : Type) : Type :=
  | Unique : V -> outcome V
  | Multiple : outcome V
  | Inconsistent : outcome V.
Arguments Unique {V} _.
Arguments Multiple {V}.
Arguments Inconsistent {V}.

(* A machine outcome represents a math outcome : the same case, and a
   represented vector. *)
Instance repr_outcome V M `{Repr V M} : Repr (outcome V) (outcome M) :=
  fun machine_outcome math_outcome =>
    match machine_outcome, math_outcome with
    | Unique machine_vector, Unique math_vector =>
        repr machine_vector math_vector
    | Multiple, Multiple => True
    | Inconsistent, Inconsistent => True
    | _, _ => False
    end.

(* Math side.  A float input is read as the real it denotes (repr_float) ;
   the system is the one those reals form, and it is solved exactly in R. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The sum of the products of the entries of row and vector, term by term
   (the shorter list ends the sum : never relied on, both have
   unknown_count entries wherever it matters). *)
Fixpoint dot (row vector : list R) : R :=
  match row, vector with
  | coefficient :: coefficients, component :: components =>
      (coefficient * component + dot coefficients components)%R
  | _, _ => 0%R
  end.

(* solution solves matrix x = right_sides : unknown_count components, and
   row by row the sum of the coefficients times the components is the
   right-hand side. *)
Definition solves (unknown_count : N) (matrix : list (list R))
    (right_sides solution : list R) : Prop :=
  len solution = unknown_count /\
  Forall2 (fun row right_side => dot row solution = right_side)
    matrix right_sides.

(* Some float lies within 10^-3 of target.  The tolerance is absolute and
   the doubles thin out as they grow : above 2^44 two consecutive ones are
   more than 2 * 10^-3 apart, so a component of the solution that large may
   have no float within 10^-3 of it, and one beyond 2^1024 has none.  The
   contract asks for the tolerance exactly where a float can meet it. *)
Definition attainable (target : R) : Prop :=
  exists float_value : R, representable (A := float) float_value /\
    (Rabs (float_value - target) <= 1 / 1000)%R.

(* Component by component, approximation is within 10^-3 of solution
   wherever some float is : "the entries of x are allowed to have an error
   of at most 10^-3". *)
Definition approximates (approximation solution : list R) : Prop :=
  Forall2 (fun estimate true_value =>
             attainable true_value ->
             (Rabs (estimate - true_value) <= 1 / 1000)%R)
    approximation solution.

(* The statement's bounds on one test case. *)
Record valid_input (unknown_count : N) (matrix : list (list R))
    (right_sides : list R) : Prop := {
  (* 1 <= n <= 100 *)
  vi_n : 1 <= unknown_count <= 100;
  (* n rows of n coefficients *)
  vi_rows : len matrix = unknown_count;
  vi_row : Forall (fun row => len row = unknown_count) matrix;
  (* n right-hand sides *)
  vi_b : len right_sides = unknown_count;
  (* "floating point numbers" : the statement bounds neither their
     magnitude nor their digits ; each is a finite binary64 (repr_float),
     nothing more. *)
}.

(* The answer : Unique approximation when exactly one vector solves the
   system and approximation approximates it, Multiple when two distinct
   vectors solve it, Inconsistent when none does.  Exactly one case
   holds. *)
Definition solve_spec (unknown_count : N) (matrix : list (list R))
    (right_sides : list R) (output : outcome (list R)) : Prop :=
  match output with
  | Unique approximation =>
      exists solution, solves unknown_count matrix right_sides solution /\
        (forall other, solves unknown_count matrix right_sides other ->
           other = solution) /\
        approximates approximation solution
  | Multiple =>
      exists solution other,
        solves unknown_count matrix right_sides solution /\
        solves unknown_count matrix right_sides other /\ solution <> other
  | Inconsistent =>
      forall solution, ~ solves unknown_count matrix right_sides solution
  end.

(* machine side : the only thing that gets extracted *)
Program solve : uint -> array (array float) -> array float ->
                  outcome (array float).

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification solve_correct :
  forall (unknown_count : N) (matrix : list (list R)) (right_sides : list R)
         (unknown_count_int : uint) (matrix_arr : array (array float))
         (right_sides_arr : array float),
  valid_input unknown_count matrix right_sides ->
  repr unknown_count_int unknown_count -> repr matrix_arr matrix ->
  repr right_sides_arr right_sides ->
  exists output : outcome (list R),
    repr (solve unknown_count_int matrix_arr right_sides_arr) output /\
    solve_spec unknown_count matrix right_sides output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.

(* The four classical axioms Stdlib's reals rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec ClassicalDedekindReals.sig_not_dec Classical_Prop.classic FunctionalExtensionality.functional_extensionality_dep.
