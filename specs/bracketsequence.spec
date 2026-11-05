(* @function        bracketsequence
   @signature       array (token uint) -> uint
   @math_signature  list (token N) -> N
   @summary         [bracketsequence ts] evaluates the bracket sequence
                    spelled by the tokens ts: the items outside every
                    bracket are added, the items directly inside a pair of
                    brackets are multiplied, and the operator keeps
                    alternating with each nesting level.  The value is
                    returned modulo 10^9+7.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* One token of the input line: "(", ")" or an integer; the same inductive
   on both sides, its integer a uint on the machine side, an N on the math
   side. *)
Inductive token (A : Type) : Type :=
| Open : token A
| Close : token A
| Num : A -> token A.
Arguments Open {A}.
Arguments Close {A}.
Arguments Num {A} _.

Instance repr_token A M `{Repr A M} : Repr (token A) (token M) :=
  fun x i => match x, i with
             | Open, Open | Close, Close => True
             | Num a, Num m => repr a m
             | _, _ => False
             end.

(* Math side. *)

Definition len {A} (l : list A) : N := N.of_nat (List.length l).

Definition modulus : N := 10^9 + 7.

(* A bracket sequence, as the statement reads it: a list of items, an item
   being an integer or a bracketed bracket sequence. *)
Inductive item : Type :=
| Leaf : N -> item
| Group : list item -> item.

(* The tokens that write an item, a sequence, down. *)
Fixpoint item_tokens (it : item) : list (token N) :=
  match it with
  | Leaf x => [Num x]
  | Group l => Open :: flat_map item_tokens l ++ [Close]
  end.

Definition seq_tokens (s : list item) : list (token N) := flat_map item_tokens s.

(* [P] holds of every element of [l]. *)
Definition all {A : Type} (P : A -> Prop) (l : list A) : Prop :=
  fold_right (fun x acc => P x /\ acc) True l.

(* No bracket pair is empty, at any depth: "( )" is not a bracket sequence,
   nor a subsequence of one. *)
Fixpoint item_ok (it : item) : Prop :=
  match it with
  | Leaf _ => True
  | Group l => l <> [] /\ all item_ok l
  end.

Definition seq_ok (s : list item) : Prop := all item_ok s.

(* The tokens form a bracket sequence. *)
Definition is_bracket_sequence (ts : list (token N)) : Prop :=
  exists s, seq_ok s /\ seq_tokens s = ts.

(* The sum of the values when [add] is true, their product otherwise. *)
Definition combine (add : bool) (vs : list N) : N :=
  if add then fold_right N.add 0 vs else fold_right N.mul 1 vs.

(* The exact value of an item standing in a sequence whose operator is
   addition iff [add]; the items inside a bracket pair use the other
   operator. *)
Fixpoint item_value (add : bool) (it : item) : N :=
  match it with
  | Leaf x => x
  | Group l => combine (negb add) (map (item_value (negb add)) l)
  end.

(* The value of the whole sequence: outside every bracket, addition. *)
Definition seq_value (s : list item) : N := combine true (map (item_value true) s).

Record valid_input (ts : list (token N)) : Prop := {
  (* 1 <= n <= 3 * 10^5 tokens *)
  vi_n : 1 <= len ts <= 3 * 10 ^ 5;
  (* each integer token x satisfies 0 <= x < 10^9+7 *)
  vi_x : Forall (fun t => match t with Num x => x < 10 ^ 9 + 7 | _ => True end) ts;
  (* it is guaranteed that the tokens form a bracket sequence *)
  vi_bracket : is_bracket_sequence ts;
}.

(* The value of the bracket sequence the tokens spell, modulo 10^9+7. *)
Definition bracketsequence_spec (ts : list (token N)) (o : N) : Prop :=
  forall s, seq_ok s -> seq_tokens s = ts -> o = seq_value s mod modulus.

Program bracketsequence : array (token uint) -> uint.

Specification bracketsequence_correct :
  forall (ts : list (token N)) (x : array (token uint)),
  valid_input ts -> repr x ts ->
  exists o : N, repr (bracketsequence x) o /\ bracketsequence_spec ts o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
