(* @function        candydistribution
   @signature       uint -> uint -> option uint
   @math_signature  N -> N -> option N
   @summary         [candydistribution k c], for k kids and bags of c
                    candies each, returns [Some b] where buying b bags, at
                    most 10^9 of them, gives exactly k * x + 1 candies for
                    some positive natural number x, and [None]
                    ("IMPOSSIBLE") exactly when no such number of bags
                    exists. When several b work, any of them may be returned.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. *)

(* "you will never buy more than 10^9 candy bags" *)
Definition max_bags : N := 10 ^ 9.

(* Buying b bags of c candies, within the bag limit, gives (k * x) + 1
   candies for a positive natural number x: a fair distribution of x
   candies to each of the k kids, plus exactly one spare candy. *)
Definition fair_bags (k c b : N) : Prop :=
  1 <= b <= max_bags /\ exists x : N, 1 <= x /\ b * c = k * x + 1.

(* The statement's bounds, for one test case. *)
Record valid_input (k c : N) : Prop := {
  (* "1 <= K, C <= 10^9" *)
  vi_k : 1 <= k <= 10 ^ 9;
  vi_c : 1 <= c <= 10 ^ 9;
}.

(* Some b: b bags are a fair purchase; None: no number of bags is. *)
Definition candydistribution_spec (k c : N) (o : option N) : Prop :=
  match o with
  | Some b => fair_bags k c b
  | None => ~ exists b, fair_bags k c b
  end.

(* machine side: the only thing that gets extracted *)
Program candydistribution : uint -> uint -> option uint.

(* the one line: repr on the inputs (universal), repr on the output
   (existential) *)
Specification candydistribution_correct :
  forall (k c : N) (x y : uint),
  valid_input k c -> repr x k -> repr y c ->
  exists o : option N, repr (candydistribution x y) o /\
                       candydistribution_spec k c o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
