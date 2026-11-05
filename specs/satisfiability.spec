(* @function        satisfiable
   @signature       uint -> array (array (literal uint)) -> bool
   @math_signature  N -> list (list (literal N)) -> bool
   @summary         One test case: n variables X1..Xn and a formula given as
                    its clauses, each clause the disjunction of its literals
                    (Xi or ~Xi). [satisfiable n clauses] is true exactly when
                    some assignment of truth values to the variables makes
                    every clause contain a true literal.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* A literal as the statement writes it: [X i] for Xi, [NotX i] for ~Xi.
   Declared once for both sides: [literal uint] on the machine side,
   [literal N] on the math side. *)
Inductive literal (A : Type) : Type :=
| X : A -> literal A
| NotX : A -> literal A.
Arguments X {A}.
Arguments NotX {A}.

(* A machine literal represents the math literal of the same sign whose
   variable it represents. *)
Instance repr_literal A M `{Repr A M} : Repr (literal A) (literal M) :=
  fun x i => match x, i with
             | X a, X m | NotX a, NotX m => repr a m
             | _, _ => False
             end.

(* Math side. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The variable a literal mentions. *)
Definition var (l : literal N) : N :=
  match l with X i | NotX i => i end.

(* The truth value of a literal under the assignment v of the variables. *)
Definition lit_true (v : N -> bool) (l : literal N) : bool :=
  match l with X i => v i | NotX i => negb (v i) end.

(* Some literal of the clause is true under v. *)
Definition clause_true (v : N -> bool) (c : list (literal N)) : Prop :=
  exists l, In l c /\ lit_true v l = true.

(* Some assignment makes every clause true. *)
Definition is_satisfiable (clauses : list (list (literal N))) : Prop :=
  exists v : N -> bool, Forall (clause_true v) clauses.

(* The statement's bounds, for one test case. *)
Record valid_input (n : N) (clauses : list (list (literal N))) : Prop := {
  (* 1 <= n <= 20 indicates the number of variables *)
  vi_n : 1 <= n <= 20;
  (* 1 <= m <= 100 indicates the number of clauses *)
  vi_m : 1 <= len clauses <= 100;
  (* literals in the form Xi or ~Xi for some 1 <= i <= n *)
  vi_vars : Forall (Forall (fun l => 1 <= var l <= n)) clauses;
}.

(* The answer: true iff the formula is satisfiable. *)
Definition satisfiable_spec (n : N) (clauses : list (list (literal N)))
    (b : bool) : Prop :=
  b = true <-> is_satisfiable clauses.

Program satisfiable : uint -> array (array (literal uint)) -> bool.

Specification satisfiable_correct :
  forall (n : N) (clauses : list (list (literal N)))
         (x : uint) (y : array (array (literal uint))),
  valid_input n clauses -> repr x n -> repr y clauses ->
  exists b : bool, repr (satisfiable x y) b /\ satisfiable_spec n clauses b.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
