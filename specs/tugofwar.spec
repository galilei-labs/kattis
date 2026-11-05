(* @function        tugofwar
   @signature       array uint -> uint * uint
   @math_signature  list N -> N * N
   @summary         [tugofwar w] divides the people of weights w into two
                    teams whose numbers of people differ by at most one, so
                    that the total weights of the two teams are as nearly
                    equal as possible, and returns the two totals, the
                    lesser first.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  Person k has weight w_k; a division into two teams is a list
   s of booleans, s_k telling whether person k is on the first team. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The sum of the elements of l. *)
Definition sum (l : list N) : N := fold_right N.add 0 l.

(* The weights of the people that s puts on the first team. *)
Definition team (w : list N) (s : list bool) : list N :=
  map fst (filter snd (combine w s)).

(* The weights of the people on the other team. *)
Definition other_team (w : list N) (s : list bool) : list N :=
  team w (map negb s).

(* s puts each person on one team or the other, and the numbers of people
   on the two teams do not differ by more than 1. *)
Definition division (w : list N) (s : list bool) : Prop :=
  len s = len w /\
  (Z.abs (Z.of_N (len (team w s)) - Z.of_N (len (other_team w s))) <= 1)%Z.

(* The difference between the total weights of the two teams. *)
Definition gap (w : list N) (s : list bool) : Z :=
  Z.abs (Z.of_N (sum (team w s)) - Z.of_N (sum (other_team w s))).

(* The statement's bounds. *)
Record valid_input (w : list N) : Prop := {
  (* There is at least 1 and at most 100 people at the picnic. *)
  vi_n : 1 <= len w <= 100;
  (* Each weight is an integer between 1 and 450. *)
  vi_w : Forall (fun x => 1 <= x <= 450) w;
}.

(* (a, b) are the totals of the two teams of a division whose totals are
   as nearly equal as possible, the lesser first. *)
Definition tugofwar_spec (w : list N) (o : N * N) : Prop :=
  let (a, b) := o in
  a <= b /\
  exists s, division w s /\
            sum (team w s) = a /\ sum (other_team w s) = b /\
            forall s', division w s' -> (gap w s <= gap w s')%Z.

(* machine side : the only thing that gets extracted *)
Program tugofwar : array uint -> uint * uint.

(* the one line : repr on the input (universal), repr on the output
   (existential) *)
Specification tugofwar_correct : forall (w : list N) (x : array uint),
  valid_input w -> repr x w ->
  exists o : N * N, repr (tugofwar x) o /\ tugofwar_spec w o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
