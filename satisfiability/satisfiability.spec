(** * Yet Satisfiability Again! *)

(** ** Description *)

(** Decide whether a Boolean formula in conjunctive normal form has a
    satisfying assignment.

    [@kattis satisfiability]
    - Difficulty: 2.6
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Variable count: $1 \le n \le 20$ and Clause count: $1 \le m \le 100$. *)

(** ** Examples *)

(** - Input convention: Case count; each case gives variable/clause counts and clauses using Xi, ~Xi and v.
    - Output convention: satisfiable if an assignment exists; unsatisfiable otherwise. *)
(* Input:
2
3 3
X1 v X2
~X1
~X2 v X3
3 5
X1 v X2 v X3
X1 v ~X2
X2 v ~X3
X3 v ~X1
~X1 v ~X2 v ~X3
Output:
satisfiable
unsatisfiable
*)

(** ** [@hide] Environment *)

(* @function        satisfiable
   @signature       uint -> array (array (literal uint)) -> bool
   @math_signature  N -> list (list (literal N)) -> bool
   @summary         One test case: variable_count variables X1..Xn and a
                    formula given as its clauses, each clause the
                    disjunction of its literals (Xi or ~Xi).
                    [satisfiable variable_count clauses] is true exactly
                    when some assignment of truth values to the variables
                    makes every clause contain a true literal.
                    It runs in at most c1 * 2^n * (L + m + 1) + c2 steps of
                    the cost model on a valid input, L the number of
                    literals, m of clauses, for two constants c1, c2.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** A positive or negated Boolean variable, with [uint] machine indices and [N]
    mathematical indices. *)
Inductive literal (A : Type) : Type :=
| X : A -> literal A
| NotX : A -> literal A.

(** [@hide] Constructor argument declarations and the representation relation
    between machine and mathematical literals. *)
Arguments X {A}.
Arguments NotX {A}.

(* A machine literal represents the math literal of the
   same sign whose variable it represents. *)
Instance repr_literal A M `{Repr A M} : Repr (literal A)
  (literal M) :=
  fun machine_literal math_literal =>
    match machine_literal, math_literal with
    | X machine_var, X math_var | NotX machine_var, NotX
      math_var =>
        repr machine_var math_var
    | _, _ => False
    end.

(** [@hide] The cost translation of [literal] and the witness of a machine
    literal (the vocabulary of [KattisLib.Cost]), for the bound below. *)
Elpi complexity literal.
Instance witness_literal A AC `{Witness A AC} :
  Witness (literal A) (fun CM t => literal_cost CM A (AC CM) t) :=
  fun t => match t with
           | X a => X_cost stepsCM A (AC stepsCM) a (witness a)
           | NotX a => NotX_cost stepsCM A (AC stepsCM) a (witness a)
           end.
(** [@hide] The nested arrays of literals, stated in the eta-expanded shape the
    translation gives the argument's family (instance search does not match
    the generic [witness_array] there, as [Cost] notes for arrays of words). *)
Instance witness_array_literal :
  Witness (array (literal uint))
    (fun CM t => array_cost CM (literal uint) (literal_cost CM uint (int_cost CM)) t) :=
  @witness_array (literal uint) (fun CM => literal_cost CM uint (int_cost CM))
    (@witness_literal uint int_cost _).
Instance witness_array_array_literal :
  Witness (array (array (literal uint)))
    (fun CM t => array_cost CM (array (literal uint))
                   (array_cost CM (literal uint) (literal_cost CM uint (int_cost CM))) t) :=
  @witness_array (array (literal uint))
    (fun CM => array_cost CM (literal uint) (literal_cost CM uint (int_cost CM)))
    witness_array_literal.

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The variable index named by the literal. *)
Definition var (clause_literal : literal N) : N :=
  match clause_literal with X variable | NotX variable =>
    variable end.

(** The literal evaluates to true under [assignment]. *)
Definition lit_true (assignment : N -> bool)
  (clause_literal : literal N)
    : bool :=
  match clause_literal with
  | X variable => assignment variable
  | NotX variable => negb (assignment variable)
  end.

(** At least one literal in the clause evaluates to true under [assignment]. *)
Definition clause_true (assignment : N -> bool)
  (clause : list (literal N))
    : Prop :=
  exists clause_literal, In clause_literal clause /\
    lit_true assignment clause_literal = true.

(** Some assignment makes every clause true. *)
Definition is_satisfiable
  (clauses : list (list (literal N))) : Prop :=
  exists assignment : N -> bool, Forall
    (clause_true assignment) clauses.

(** [@inside satisfiable_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (variable_count : N)
  (clauses : list (list (literal N)))
    : Prop := {
  (* 1 <= n <= 20 indicates the number of variables *)
  vi_n : 1 <= variable_count <= 20;
  (* 1 <= m <= 100 indicates the number of clauses *)
  vi_m : 1 <= len clauses <= 100;
  (* literals in the form Xi or ~Xi for some 1 <= i <= n *)
  vi_vars : Forall (Forall (fun clause_literal =>
    1 <= var clause_literal <= variable_count)) clauses;
}.

(** Count literals in [count] clauses starting at index [start], adding to [acc]. *)
Fixpoint lits_from (clauses_arr : array (array (literal uint)))
  (count start acc : nat) : nat :=
  match count with
  | O => acc
  | S rest =>
      lits_from clauses_arr rest (S start)
        (acc + size clauses_arr.[Uint63.of_Z (Z.of_nat start)])%nat
  end.

(** The number of literals of the formula, the sum of the clause lengths,
    the measure of the bound below. *)
Definition lits (clauses_arr : array (array (literal uint))) : nat :=
  lits_from clauses_arr (size clauses_arr) 0%nat 0%nat.

(** ** Correctness *)

(** [@requirement]
    The output is true exactly when the Boolean formula has a satisfying assignment. *)
Definition satisfiable_spec
  (variable_count : N)
  (clauses : list (list (literal N)))
  (output : bool)
  : Prop :=
  output = true <-> is_satisfiable clauses.

(** ** Complexity *)

(** [@requirement] Runs in $O(2^v(L+c+1))$ steps, where $v$ is the variable count, $c$ the number of clauses, and $L$ the total number of literals. *)
Definition satisfiable_time_spec (c1 c2 n_variable_count literals_clauses n_clauses steps : nat) : Prop :=
  (steps <= c1 * (2 ^ n_variable_count * (literals_clauses + n_clauses + 1)) + c2)%nat.

(** ** Interface *)

(** Decide whether a Boolean formula in conjunctive normal form has a satisfying assignment.
    - Input [variable_count]: Number of Boolean variables.
    - Input [clauses]: Clauses of the formula, each containing signed literals.
    - Output [output]: The output is true exactly when the Boolean formula has a satisfying assignment. *)
Program satisfiable : uint -> array (array (literal uint))
  -> bool.

(** [@example satisfiable]
    - Sample: 1
    - Case: 1
    - Input [variable_count]: 3
    - Input [clauses]: [[X 1; X 2]; [NotX 1]; [NotX 2; X 3]]
    - Output [output]: true
*)

(** [@example satisfiable]
    - Sample: 1
    - Case: 2
    - Input [variable_count]: 3
    - Input [clauses]: [[X 1; X 2; X 3]; [X 1; NotX 2]; [X 2; NotX 3]; [X 3; NotX 1]; [NotX 1; NotX 2; NotX 3]]
    - Output [output]: false
*)

(** ** Bridge *)

(** [@requirement satisfiable_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented [output] satisfying
    [satisfiable_spec]. *)
Specification satisfiable_correct :
  forall (variable_count : N) (clauses : list (list (literal
    N)))
         (variable_count_int : uint)
         (clauses_arr : array (array (literal uint))),
  valid_input variable_count clauses ->
  repr variable_count_int variable_count -> repr clauses_arr
    clauses ->
  exists output : bool,
    repr (satisfiable variable_count_int clauses_arr) output
      /\
    satisfiable_spec variable_count clauses output.

(** ** Complexity *)

(** [@hide] [satisfiable_cost] is the cost translation of [satisfiable] (the judge
    recomputes it and compares) ... *)
Complexity satisfiable_cost for satisfiable.

(** [@fold complexity bound] ... and runs in at most c1 * 2^n * (L + m + 1) + c2 steps of the cost model on a valid input, L the number of literals, m of clauses, for two constants
    quantified before the inputs, on every valid input. [@requirement satisfiable_time_spec] *)
Specification satisfiable_time : exists c1 c2 : nat,
  forall (variable_count : N) (clauses : list (list (literal N)))
         (variable_count_int : uint)
         (clauses_arr : array (array (literal uint))),
  valid_input variable_count clauses ->
  repr variable_count_int variable_count -> repr clauses_arr clauses ->
  satisfiable_time_spec c1 c2 (size variable_count_int) (lits clauses_arr) (size clauses_arr) (cost2 satisfiable_cost variable_count_int clauses_arr).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
