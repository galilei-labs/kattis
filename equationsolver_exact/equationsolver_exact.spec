(** * Linear Equation Solver *)

(** ** Description *)

(** Solve a square linear system, distinguishing a unique solution, multiple
    solutions and inconsistency. For a unique solution, approximate each
    component within 0.001 wherever that accuracy is representable.

    [@kattis equationsolver]
    - Difficulty: 4.4
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Number of unknowns: $1 \le n \le 100$, with a square coefficient matrix.
    - Coefficients and right-hand sides are floating-point numbers; no
      magnitude bound is stated. *)

(** ** Examples *)

(** - Input convention: Per case: matrix dimension, matrix rows and right-hand-side vector; a zero dimension ends input.
    - Output convention: Solution components within 0.001, or multiple or inconsistent, on one line per case. *)
(* Input:
2
1 1
0 1
23 42
1
5
1
3
1 -2 0
2 -4 0
1 -2 1
3 6 4
3
1 1 0
3 3 0
0 1 2
1 4 8
0
Output:
-19 42
0.2
multiple
inconsistent
*)

(** ** [@hide] Environment *)
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

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Floats Reals.
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** A solution classification, parameterized by array float for machine values or list R for mathematical values. *)
Inductive outcome (V : Type) : Type :=
  | Unique : V -> outcome V
  | Multiple : outcome V
  | Inconsistent : outcome V.
Arguments Unique {V} _.
Arguments Multiple {V}.
Arguments Inconsistent {V}.

(* A machine outcome represents a math outcome : the same
   case, and a represented vector. *)
Instance repr_outcome V M `{Repr V M} : Repr (outcome V)
  (outcome M) :=
  fun machine_outcome math_outcome =>
    match machine_outcome, math_outcome with
    | Unique machine_vector, Unique math_vector =>
        repr machine_vector math_vector
    | Multiple, Multiple => True
    | Inconsistent, Inconsistent => True
    | _, _ => False
    end.

(** Math side. A float input is read as the real it denotes (repr_float)
    ; the system is the one those reals form, and it is solved
    exactly in R. The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The sum of the products of the entries of row and vector, term by
    term (the shorter list ends the sum : never relied on, both have
    unknown_count entries wherever it matters). *)
Fixpoint dot (row vector : list R) : R :=
  match row, vector with
  | coefficient :: coefficients, component :: components =>
      (coefficient * component + dot coefficients
        components)%R
  | _, _ => 0%R
  end.

(** solution solves matrix x = right_sides : unknown_count components,
    and row by row the sum of the coefficients times the components
    is the right-hand side. *)
Definition solves (unknown_count : N)
  (matrix : list (list R))
    (right_sides solution : list R) : Prop :=
  len solution = unknown_count /\
  Forall2 (fun row right_side => dot row solution =
    right_side)
    matrix right_sides.

(** Some float lies within 10^-3 of target. The tolerance is absolute
    and the doubles thin out as they grow : above 2^44 two
    consecutive ones are more than 2 * 10^-3 apart, so a component
    of the solution that large may have no float within 10^-3 of it,
    and one beyond 2^1024 has none. The contract asks for the
    tolerance exactly where a float can meet it. *)
Definition attainable (target : R) : Prop :=
  exists float_value : R, representable (A :=
    float) float_value /\
    (Rabs (float_value - target) <= 1 / 1000)%R.

(** Component by component, approximation is within 10^-3 of solution
    wherever some float is : "the entries of x are allowed to have
    an error of at most 10^-3". *)
Definition approximates
  (approximation solution : list R) : Prop :=
  Forall2 (fun estimate true_value =>
             attainable true_value ->
             (Rabs (estimate - true_value) <= 1 / 1000)%R)
    approximation solution.

(** [@inside solve_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (unknown_count : N)
  (matrix : list (list R))
    (right_sides : list R) : Prop := {
  (* 1 <= n <= 100 *)
  vi_n : 1 <= unknown_count <= 100;
  (* n rows of n coefficients *)
  vi_rows : len matrix = unknown_count;
  vi_row : Forall (fun row => len row = unknown_count)
    matrix;
  (* n right-hand sides *)
  vi_b : len right_sides = unknown_count;
  (* "floating point numbers" : the statement bounds
     neither their magnitude nor their digits ; each is a
     finite binary64 (repr_float), nothing more. *)
}.

(** ** Correctness *)

(** [@requirement]
    The output classifies the system as inconsistent, underdetermined or uniquely
    solvable. A unique solution is approximated within 0.001 wherever that accuracy is
    representable. *)
Definition solve_spec (unknown_count : N)
  (matrix : list (list R))
    (right_sides : list R) (output : outcome (list R)) :
      Prop :=
  match output with
  | Unique approximation =>
      exists solution, solves unknown_count matrix
        right_sides solution /\
        (forall other, solves unknown_count matrix
          right_sides other ->
           other = solution) /\
        approximates approximation solution
  | Multiple =>
      exists solution other,
        solves unknown_count matrix right_sides solution /\
        solves unknown_count matrix right_sides other /\
          solution <> other
  | Inconsistent =>
      forall solution, ~ solves unknown_count matrix
        right_sides solution
  end.

(** ** Interface *)

(** Solve a square linear system, distinguishing a unique solution, multiple solutions and
    inconsistency. For a unique solution, approximate each component within 0.001
    wherever that accuracy is representable.
    - Input [unknown_count]: Number of unknowns and equations.
    - Input [matrix]: Square coefficient matrix of the linear system.
    - Input [right_sides]: Right-hand-side vector of the linear system.
    - Output [output]: The output classifies the system as inconsistent, underdetermined or uniquely solvable. A unique solution is approximated within 0.001 wherever that accuracy is representable. *)
Program solve : uint -> array
  (array float) -> array float ->
                  outcome (array float).

(** ** Bridge *)

(** [@requirement solve_spec] [@fold full correctness statement] On
    valid represented inputs, [solve] returns a represented output
    satisfying [solve_spec]. *)
Specification solve_correct :
  forall (unknown_count : N) (matrix : list (list R))
    (right_sides : list R)
         (unknown_count_int : uint) (matrix_arr : array
           (array float))
         (right_sides_arr : array float),
  valid_input unknown_count matrix right_sides ->
  repr unknown_count_int unknown_count ->
    repr matrix_arr matrix ->
  repr right_sides_arr right_sides ->
  exists output : outcome (list R),
    repr (solve unknown_count_int matrix_arr
      right_sides_arr) output /\
    solve_spec unknown_count matrix right_sides output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.

(** [@hide] The four classical axioms Stdlib's reals rest on: the math
    side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec Classical_Prop.classic
  FunctionalExtensionality.functional_extensionality_dep.
