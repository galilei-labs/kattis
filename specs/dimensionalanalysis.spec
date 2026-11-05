(* @function        valid
   @signature       uint -> array (array sint) -> bool
   @math_signature  N -> list (list Z) -> bool
   @summary         [valid m e] returns true when no physical quantity is
                    forced to be dimensionless by the equations e, false
                    otherwise.  e has one row per equation over the m
                    quantities 0 .. m - 1 ; the entry (i, j) is the
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

(* The value of a row under d : the sum of entry_j * d j, j counting from
   the given index. *)
Fixpoint row_value (row : list Z) (d : assignment) (j : N) : Q :=
  match row with
  | [] => 0%Q
  | x :: rest => (inject_Z x * d j + row_value rest d (j + 1))%Q
  end.

(* d satisfies every equation : every row sums to zero. *)
Definition satisfies (e : list (list Z)) (d : assignment) : Prop :=
  Forall (fun row => (row_value row d 0 == 0)%Q) e.

(* Quantity j can have a dimension : some assignment satisfying the
   equations gives it a nonzero one. *)
Definition free_quantity (e : list (list Z)) (j : N) : Prop :=
  exists d, satisfies e d /\ ~ (d j == 0)%Q.

(* The sum of the absolute values of a row : at most the number of atoms
   of the equation. *)
Definition abs_sum (row : list Z) : Z := fold_right (fun x acc => Z.abs x + acc) 0 row.

(* The statement's bounds, for the one test case. *)
Record valid_input (m : N) (e : list (list Z)) : Prop := {
  (* 1 <= N <= 100 equations *)
  vi_equations : (1 <= len e <= 100)%N;
  (* at most 100 unique physical quantities, one column each *)
  vi_quantities : (m <= 100)%N;
  vi_rows : Forall (fun row => len row = m) e;
  (* each equation contains at most 100 atoms *)
  vi_atoms : Forall (fun row => abs_sum row <= 100) e;
}.

(* valid exactly when every quantity can have a dimension. *)
Definition valid_spec (m : N) (e : list (list Z)) (b : bool) : Prop :=
  b = true <-> forall j, (j < m)%N -> free_quantity e j.

(* machine side : the only thing that gets extracted *)
Program valid : uint -> array (array sint) -> bool.

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification valid_correct :
  forall (m : N) (e : list (list Z)) (xm : uint) (xe : array (array sint)),
  valid_input m e -> repr xm m -> repr xe e ->
  exists b : bool, repr (valid xm xe) b /\ valid_spec m e b.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
