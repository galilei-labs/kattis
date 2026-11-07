(** * Bracket Sequence *)

(** ** Description *)

(** Evaluate a nested sequence of integers, adding at the outermost level
    and alternating multiplication and addition at successive nesting
    levels. Return the value modulo 1000000007.

    [@kattis bracketsequence]
    - Difficulty: 3.9

    **Kattis Bounds**
    - 1 to 300000 tokens forming a valid bracket sequence.
    - Integer tokens from 0 to 1000000006. *)

(** ** Examples *)

(** Kattis text input and output. *)
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
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** One token of the input line: "(", ")" or an integer;
    the same inductive on both sides, its integer a uint
    on the machine side, an N on the math side. *)
Inductive token (A : Type) : Type :=
| Open : token A
| Close : token A
| Num : A -> token A.
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

(** Math side. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The modulus used for the result. *)
Definition modulus : N := 10^9 + 7.

(** A bracket sequence, as the statement reads it: a
    list of items, an item being an integer or a
    bracketed bracket sequence. *)
Inductive item : Type :=
| Leaf : N -> item
| Group : list item -> item.

(** The tokens that write an item, a sequence, down. *)
Fixpoint item_tokens (element : item) : list (token N) :=
  match element with
  | Leaf number => [Num number]
  | Group items => Open :: flat_map item_tokens items ++
    [Close]
  end.

(** The tokens spelling the sequence of items. *)
Definition seq_tokens (items : list item) : list
  (token N) :=
  flat_map item_tokens items.

(** [P] holds of every element of [l]. *)
Definition all {A : Type} (P : A -> Prop)
  (l : list A) : Prop :=
  fold_right (fun element rest_hold => P element
    /\ rest_hold) True l.

(** No bracket pair is empty, at any depth: "( )" is not
    a bracket sequence, nor a subsequence of one. *)
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
Definition combine (add : bool) (values : list N) : N :=
  if add then fold_right N.add 0 values else fold_right
    N.mul 1 values.

(** The exact value of an item standing in a sequence
    whose operator is addition iff [add]; the items
    inside a bracket pair use the other operator. *)
Fixpoint item_value (add : bool) (element : item) : N :=
  match element with
  | Leaf number => number
  | Group items => combine (negb add) (map (item_value
    (negb add)) items)
  end.

(** The value of the whole sequence: outside every
    bracket, addition. *)
Definition seq_value (items : list item) : N :=
  combine true (map (item_value true) items).

(** [@inside bracketsequence_correct] The statement's
    input bounds and guarantees. *)
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

(** [@requirement] [@short must evaluate the bracket
    sequence.] The value of the bracket sequence the
    tokens spell, modulo 10^9+7. *)
Definition bracketsequence_spec (tokens : list (token N))
  (output : N) : Prop :=
  forall items, seq_ok items -> seq_tokens items = tokens ->
    output = seq_value items mod modulus.

(** ** Interface *)

(** The machine-level interface.
    - Input [tokens]:
    - Output [output]: *)
Program bracketsequence : array (token uint) -> uint.

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

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
