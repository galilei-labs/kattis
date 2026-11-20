(** * Dimensional Analysis *)

(** ** Description *)

(** Check a set of physical equations involving multiplication and division.
    Every named quantity is supposed to have physical units. The equations
    are invalid if they force any individual quantity to be dimensionless,
    meaning that all its unit exponents must be zero. Otherwise they are valid.
    For example, an equation stating that a quantity times itself is one
    forces that quantity to be dimensionless.

    The function receives one signed exponent vector per equation: move all
    factors to the left, recording numerator occurrences positively and
    denominator occurrences negatively. Dimensions turn these multiplicative
    equations into linear constraints on unit exponents.

    [@kattis dimensionalanalysis]
    - Difficulty: 8.1
    - CPU time limit: 4 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Equation count: $1 \le n \le 100$ over at most $100$ quantities.
    - At most $100$ atoms per equation. *)

(** ** Examples *)

(** - Input convention: Equation count, followed by multiplicative equations using names, 1, *, / and =.
    - Output convention: invalid if any quantity is forced to be dimensionless; valid otherwise. *)
(* Input:
5
velocity * time = length
frequency = 1 / time
acceleration = velocity / time
force = mass * acceleration
force = mass * length / time / time
Output:
valid
*)

(** ** [@hide] Environment *)

(* @function        valid
   @signature       uint -> array (array sint) -> bool
   @math_signature  N -> list (list Z) -> bool
   @summary         [valid quantity_count equations] returns true when no
                    physical quantity is forced to be dimensionless by the
                    equations, false otherwise.  equations has one row per
                    equation over the quantity_count quantities
                    0 .. quantity_count - 1 ; the entry (i, j) is the
                    exponent of quantity j in equation i, the number of
                    times it is multiplied minus the number of times it is
                    divided on the left side, minus the same count for the
                    right side.  The harness turns each equation line into
                    its row, numbering the quantities ; the atom 1
                    contributes nothing
*)

From Stdlib Require Import ZArith NArith QArith List Uint63
  PArray.
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** A dimension for each quantity : its exponent on a
    reference dimension, a rational since roots of any
    order may be taken. (A dimension is in general a
    vector of exponents over several base dimensions ;
    the equations constrain each coordinate separately
    and in the same way, so one coordinate decides
    whether a quantity is forced to zero.) *)
Definition assignment := N -> Q.

(** Evaluate the linear equation row at [dimensions], starting the variable indices
    at [j]. *)
Fixpoint row_value (row : list Z) (dimensions : assignment)
  (j : N) : Q :=
  match row with
  | [] => 0%Q
  | entry :: rest =>
      (inject_Z entry * dimensions j + row_value rest
        dimensions (j + 1))%Q
  end.

(** [dimensions] satisfies every equation: each row evaluates to zero. *)
Definition satisfies (equations : list (list Z))
  (dimensions : assignment)
    : Prop :=
  Forall (fun row =>
    (row_value row dimensions 0 == 0)%Q) equations.

(** Some dimension assignment satisfying [equations] gives [quantity] a nonzero
    exponent. *)
Definition free_quantity (equations : list (list Z))
  (quantity : N) : Prop :=
  exists dimensions, satisfies equations dimensions /\
    ~ (dimensions quantity == 0)%Q.

(** The sum of the absolute values of the row coefficients, used to bound the number
    of equation atoms. *)
Fixpoint abs_sum (row : list Z) : Z :=
  match row with
  | [] => 0
  | entry :: rest => Z.abs entry + abs_sum rest
  end.

(** [@inside valid_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (quantity_count : N) (equations : list
  (list Z))
    : Prop := {
  (* 1 <= N <= 100 equations *)
  vi_equations : (1 <= len equations <= 100)%N;
  (* at most 100 unique physical quantities, one column each
    *)
  vi_quantities : (quantity_count <= 100)%N;
  vi_rows : Forall
    (fun row => len row = quantity_count) equations;
  (* each equation contains at most 100 atoms *)
  vi_atoms : Forall
    (fun row => abs_sum row <= 100) equations;
}.

(** ** Correctness *)

(** [@requirement]
    The output is true exactly when no individual quantity is forced to be dimensionless
    by the equations. *)
Definition valid_spec (quantity_count : N)
  (equations : list (list Z))
    (output : bool) : Prop :=
  output = true <->
    forall quantity, (quantity < quantity_count)%N ->
      free_quantity equations quantity.

(** ** Interface *)

(** Check that the physical equations do not force any named quantity to
    have no units. Return [true] for a valid system and [false] if some
    quantity must be dimensionless in every dimension assignment.
    - Input [quantity_count]: Number of distinct physical quantities.
    - Input [equations]: Signed exponent vectors representing the multiplicative equations.
    - Output [output]: The output is true exactly when no individual quantity is forced to be dimensionless by the equations. *)
Program valid : uint -> array (array sint) -> bool.

(** [@example valid]
    - Sample: 1
    - Input [quantity_count]: 7
    - Input [equations]: [[1; 1; -1; 0; 0; 0; 0]; [0; 1; 0; 1; 0; 0; 0]; [-1; 1; 0; 0; 1; 0; 0]; [0; 0; 0; 0; -1; 1; -1]; [0; 2; -1; 0; 0; 1; -1]]%Z
    - Output [output]: true
*)

(** ** Bridge *)

(** [@requirement valid_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented output satisfying
    [valid_spec]. *)
Specification valid_correct :
  forall (quantity_count : N) (equations : list (list Z))
         (quantity_count_int : uint) (equations_arr : array
           (array sint)),
  valid_input quantity_count equations ->
  repr quantity_count_int quantity_count
    -> repr equations_arr equations ->
  exists output : bool,
    repr (valid quantity_count_int equations_arr) output /\
    valid_spec quantity_count equations output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
