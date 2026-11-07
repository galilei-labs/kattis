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

From Stdlib Require Import ZArith NArith QArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* A dimension for each quantity : its exponent on a reference dimension,
   a rational since roots of any order may be taken.  (A dimension is in
   general a vector of exponents over several base dimensions ; the
   equations constrain each coordinate separately and in the same way, so
   one coordinate decides whether a quantity is forced to zero.) *)
Definition assignment := N -> Q.

(* The value of a row under dimensions : the sum of
   entry_j * dimensions j, j counting from the given index. *)
Fixpoint row_value (row : list Z) (dimensions : assignment) (j : N) : Q :=
  match row with
  | [] => 0%Q
  | entry :: rest =>
      (inject_Z entry * dimensions j + row_value rest dimensions (j + 1))%Q
  end.

(* dimensions satisfies every equation : every row sums to zero. *)
Definition satisfies (equations : list (list Z)) (dimensions : assignment)
    : Prop :=
  Forall (fun row => (row_value row dimensions 0 == 0)%Q) equations.

(* The quantity numbered quantity can have a dimension : some assignment
   satisfying the equations gives it a nonzero one. *)
Definition free_quantity (equations : list (list Z)) (quantity : N) : Prop :=
  exists dimensions, satisfies equations dimensions /\
    ~ (dimensions quantity == 0)%Q.

(* The sum of the absolute values of a row : at most the number of atoms
   of the equation. *)
Definition abs_sum (row : list Z) : Z :=
  fold_right (fun entry total => Z.abs entry + total) 0 row.

(* The statement's bounds, for the one test case. *)
Record valid_input (quantity_count : N) (equations : list (list Z))
    : Prop := {
  (* 1 <= N <= 100 equations *)
  vi_equations : (1 <= len equations <= 100)%N;
  (* at most 100 unique physical quantities, one column each *)
  vi_quantities : (quantity_count <= 100)%N;
  vi_rows : Forall (fun row => len row = quantity_count) equations;
  (* each equation contains at most 100 atoms *)
  vi_atoms : Forall (fun row => abs_sum row <= 100) equations;
}.

(* valid exactly when every quantity can have a dimension. *)
Definition valid_spec (quantity_count : N) (equations : list (list Z))
    (output : bool) : Prop :=
  match output with
  | true =>
      forall quantity, (quantity < quantity_count)%N ->
        free_quantity equations quantity
  | false =>
      ~ forall quantity, (quantity < quantity_count)%N ->
          free_quantity equations quantity
  end.

(* machine side : the only thing that gets extracted *)
Program valid : uint -> array (array sint) -> bool.

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification valid_correct :
  forall (quantity_count : N) (equations : list (list Z))
         (quantity_count_int : uint) (equations_arr : array (array sint)),
  valid_input quantity_count equations ->
  repr quantity_count_int quantity_count -> repr equations_arr equations ->
  exists output : bool,
    repr (valid quantity_count_int equations_arr) output /\
    valid_spec quantity_count equations output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
