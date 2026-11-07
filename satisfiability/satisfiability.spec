(* @function        satisfiable
   @signature       uint -> array (array (literal uint)) -> bool
   @math_signature  N -> list (list (literal N)) -> bool
   @summary         One test case: variable_count variables X1..Xn and a
                    formula given as its clauses, each clause the
                    disjunction of its literals (Xi or ~Xi).
                    [satisfiable variable_count clauses] is true exactly
                    when some assignment of truth values to the variables
                    makes every clause contain a true literal.
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
  fun machine_literal math_literal =>
    match machine_literal, math_literal with
    | X machine_var, X math_var | NotX machine_var, NotX math_var =>
        repr machine_var math_var
    | _, _ => False
    end.

(* Math side. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The variable a literal mentions. *)
Definition var (clause_literal : literal N) : N :=
  match clause_literal with X variable | NotX variable => variable end.

(* The truth value of a literal under the assignment of the variables. *)
Definition lit_true (assignment : N -> bool) (clause_literal : literal N)
    : bool :=
  match clause_literal with
  | X variable => assignment variable
  | NotX variable => negb (assignment variable)
  end.

(* Some literal of the clause is true under assignment. *)
Definition clause_true (assignment : N -> bool) (clause : list (literal N))
    : Prop :=
  exists clause_literal, In clause_literal clause /\
    lit_true assignment clause_literal = true.

(* Some assignment makes every clause true. *)
Definition is_satisfiable (clauses : list (list (literal N))) : Prop :=
  exists assignment : N -> bool, Forall (clause_true assignment) clauses.

(* The statement's bounds, for one test case. *)
Record valid_input (variable_count : N) (clauses : list (list (literal N)))
    : Prop := {
  (* 1 <= n <= 20 indicates the number of variables *)
  vi_n : 1 <= variable_count <= 20;
  (* 1 <= m <= 100 indicates the number of clauses *)
  vi_m : 1 <= len clauses <= 100;
  (* literals in the form Xi or ~Xi for some 1 <= i <= n *)
  vi_vars : Forall (Forall (fun clause_literal =>
    1 <= var clause_literal <= variable_count)) clauses;
}.

(* The answer: true iff the formula is satisfiable. *)
Definition satisfiable_spec (variable_count : N)
    (clauses : list (list (literal N))) (output : bool) : Prop :=
  match output with
  | true => is_satisfiable clauses
  | false => ~ is_satisfiable clauses
  end.

Program satisfiable : uint -> array (array (literal uint)) -> bool.

Specification satisfiable_correct :
  forall (variable_count : N) (clauses : list (list (literal N)))
         (variable_count_int : uint)
         (clauses_arr : array (array (literal uint))),
  valid_input variable_count clauses ->
  repr variable_count_int variable_count -> repr clauses_arr clauses ->
  exists output : bool,
    repr (satisfiable variable_count_int clauses_arr) output /\
    satisfiable_spec variable_count clauses output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
