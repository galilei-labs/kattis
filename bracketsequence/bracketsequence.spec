(** * Bracket Sequence *)

(** ** Description *)

(** A bracket sequence writes a calculation using integers and parentheses
    but omits its operators. Add entries outside parentheses; inside the
    first level multiply, inside the next level add, and continue alternating
    with each nesting level. For example, [1 (2 (3 4))] means
    $1 + (2 \times (3 + 4)) = 15$. Every parenthesized group is nonempty.
    Evaluate the sequence and return its value modulo $10^{9} + 7$.

    [@kattis bracketsequence]
    - Difficulty: 3.9
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Token count: $1 \le n \le 3 \times 10^{5}$ forming a valid bracket sequence.
    - Integer tokens: $0 \le x \le 10^{9} + 6$. *)

(** ** Examples *)

(** - Input convention: Token count, followed by integers and parentheses separated by spaces.
    - Output convention: The expression value modulo $10^9 + 7$. *)
(* Input:
2
2 3
Output:
5
*)

(** ** [@hide] Environment *)

(* @function        bracketsequence
   @signature       array (token uint) -> uint
   @math_signature  list (token N) -> N
   @summary         [bracketsequence tokens] evaluates the bracket sequence
                    spelled by tokens: the items outside every
                    bracket are added, the items directly inside a pair of
                    brackets are multiplied, and the operator keeps
                    alternating with each nesting level.  The value is
                    returned modulo 10^9+7.
                    It runs in at most c1 * (n + 1) + c2 steps of the cost
                    model on a valid input, n the number of tokens (one pass
                    with a stack), for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** An input token: an opening parenthesis, a closing parenthesis, or an integer.
    Integer tokens use [uint] on the machine side and [N] on the mathematical side. *)
Inductive token (A : Type) : Type :=
| Open : token A
| Close : token A
| Num : A -> token A.

(** [@hide] Constructor argument declarations. *)
Arguments Open {A}.
Arguments Close {A}.
Arguments Num {A} _.

(** [@hide] The token structure is unchanged and its
    number is represented. *)
Instance repr_token A M `{Repr A M} : Repr (token A)
  (token M) :=
  fun machine_symbol symbol =>
    match machine_symbol, symbol with
    | Open, Open | Close, Close => True
    | Num machine_number, Num number => repr machine_number
      number
    | _, _ => False
    end.

(** [@hide] The cost translation of [token] and the witness of a machine
    token (the vocabulary of [KattisLib.Cost]), for the bound below. *)
Elpi complexity token.
Instance witness_token A AC `{Witness A AC} :
  Witness (token A) (fun CM t => token_cost CM A (AC CM) t) :=
  fun t => match t with
           | Open => Open_cost stepsCM A (AC stepsCM)
           | Close => Close_cost stepsCM A (AC stepsCM)
           | Num a => Num_cost stepsCM A (AC stepsCM) a (witness a)
           end.
(** [@hide] The array of tokens, stated in the eta-expanded shape the
    translation gives the argument's family (instance search does not match
    the generic [witness_array] there, as [Cost] notes for arrays of words). *)
Instance witness_array_token :
  Witness (array (token uint))
    (fun CM t => array_cost CM (token uint) (token_cost CM uint (int_cost CM)) t) :=
  @witness_array (token uint) (fun CM => token_cost CM uint (int_cost CM))
    (@witness_token uint int_cost _).

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The modulus used for the result. *)
Definition modulus : N := 10^9 + 7.

(** An expression item is an integer or a nested bracket sequence. *)
Inductive item : Type :=
| Leaf : N -> item
| Group : list item -> item.

(** The token list representing [element], including parentheses around nested
    sequences. *)
Fixpoint item_tokens (element : item) : list (token N) :=
  match element with
  | Leaf number => [Num number]
  | Group items => Open :: flat_map item_tokens items ++
    [Close]
  end.

(** The tokens representing [items] in sequence order. *)
Definition seq_tokens (items : list item) : list
  (token N) :=
  flat_map item_tokens items.

(** [P] holds of every element of [l]. *)
Fixpoint all {A : Type} (P : A -> Prop)
  (l : list A) : Prop :=
  match l with
  | [] => True
  | element :: rest => P element /\ all P rest
  end.

(** Every bracket group in [element] is nonempty, including groups nested at any
    depth. *)
Fixpoint item_ok (element : item) : Prop :=
  match element with
  | Leaf _ => True
  | Group items => items <> [] /\ all item_ok items
  end.

(** Every item has well-formed, nonempty bracket groups. *)
Definition seq_ok (items : list item) : Prop :=
  all item_ok items.

(** The tokens form a bracket sequence. *)
Definition is_bracket_sequence (tokens : list
  (token N)) : Prop :=
  exists items, seq_ok items /\ seq_tokens items = tokens.

(** The sum of the values when [add] is true, their
    product otherwise. *)
Fixpoint combine (add : bool) (values : list N) : N :=
  match values with
  | [] => if add then 0 else 1
  | value :: rest =>
      if add then value + combine add rest else value * combine add rest
  end.

(** The exact value of an item standing in a sequence
    whose operator is addition iff [add]; the items
    inside a bracket pair use the other operator. *)
Fixpoint item_value (add : bool) (element : item) : N :=
  match element with
  | Leaf number => number
  | Group items => combine (negb add) (map (item_value
    (negb add)) items)
  end.

(** The value of the whole sequence, using addition at the outermost level and
    alternating operators at each bracket depth. *)
Definition seq_value (items : list item) : N :=
  combine true (map (item_value true) items).

(** [@inside bracketsequence_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (tokens : list (token N)) : Prop := {
  (* 1 <= n <= 3 * 10^5 tokens *)
  vi_n : 1 <= len tokens <= 3 * 10 ^ 5;
  (* each integer token x satisfies 0 <= x < 10^9+7 *)
  vi_x : Forall (fun symbol => match symbol with
                               | Num number => number < 10 ^
                                 9 + 7
                               | _ => True
                               end) tokens;
  (* it is guaranteed that the tokens form a bracket
    sequence *)
  vi_bracket : is_bracket_sequence tokens;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the value of the nested expression modulo $10^9 + 7$, with addition at
    the outer level and alternating multiplication and addition within parentheses. *)
Definition bracketsequence_spec (tokens : list (token N))
  (output : N) : Prop :=
  forall items, seq_ok items -> seq_tokens items = tokens ->
    output = seq_value items mod modulus.

(** ** Complexity *)

(** [@requirement] Runs in $O(n)$ steps, where $n$ is the number of tokens. *)
Definition bracketsequence_time_spec (c1 c2 n_tokens steps : nat) : Prop :=
  (steps <= c1 * (n_tokens + 1) + c2)%nat.

(** ** Interface *)

(** Evaluate a nested sequence of integers, adding at the outermost level and alternating
    multiplication and addition at successive nesting levels. Return the value modulo
    $10^{9} + 7$.
    - Input [tokens]: Nested integer and parenthesis tokens to evaluate.
    - Output [output]: The output is the value of the nested expression modulo $10^9 + 7$, with addition at the outer level and alternating multiplication and addition within parentheses. *)
Program bracketsequence : array (token uint) -> uint.

(** [@example bracketsequence]
    - Sample: 1
    - Input [tokens]: [Num 2; Num 3]
    - Output [output]: 5
*)

(** ** Bridge *)

(** [@requirement bracketsequence_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [bracketsequence_spec]. *)
Specification bracketsequence_correct :
  forall (tokens : list (token N)) (tokens_arr : array
    (token uint)),
  valid_input tokens -> repr tokens_arr tokens ->
  exists output : N,
    repr (bracketsequence tokens_arr) output /\
    bracketsequence_spec tokens output.

(** ** Complexity *)

(** [@hide] [bracketsequence_cost] is the cost translation of [bracketsequence] (the judge
    recomputes it and compares) ... *)
Complexity bracketsequence_cost for bracketsequence.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) + c2 steps of the cost model on a valid input, n the number of tokens (one pass with a stack), for two constants
    quantified before the inputs, on every valid input. [@requirement bracketsequence_time_spec] *)
Specification bracketsequence_time : exists c1 c2 : nat,
  forall (tokens : list (token N)) (tokens_arr : array
  (token uint)),
  valid_input tokens -> repr tokens_arr tokens ->
  bracketsequence_time_spec c1 c2 (size tokens_arr) (cost1 bracketsequence_cost tokens_arr).

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
