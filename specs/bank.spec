(* @function        bank
   @signature       uint -> array uint -> array uint -> uint
   @math_signature  N -> list N -> list N -> N
   @summary         [bank t cash deadline] is the largest total cash the bank
                    can collect in the t minutes before it closes, serving at
                    most one person per minute, person i bringing cash_i and
                    having to be served at a minute that starts no later than
                    deadline_i.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  Person i of the queue is the i-th line of the input : cash_i
   is the i-th element of cash, t_i the i-th element of deadline (the two
   columns of the input, as parallel lists). *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The i-th element of l (0 beyond the end). *)
Definition get (l : list N) (i : N) : N := nth (N.to_nat i) l 0.

(* A schedule lists, minute by minute from minute 0, the person served
   during that minute ([Some i]) or an idle minute ([None]). *)
Definition schedule := list (option N).

(* The persons a schedule serves, in order. *)
Definition served (s : schedule) : list N :=
  flat_map (fun o => match o with Some i => [i] | None => [] end) s.

(* s ends before the bank closes, serves each person at most once, and
   serves only persons of the queue, each at a minute k <= its t_i. *)
Definition valid_schedule (t : N) (cash deadline : list N) (s : schedule)
    : Prop :=
  len s <= t /\
  NoDup (served s) /\
  (forall (k : nat) (i : N), nth_error s k = Some (Some i) ->
     i < len cash /\ N.of_nat k <= get deadline i).

(* The cash a schedule collects. *)
Definition value (cash : list N) (s : schedule) : N :=
  fold_right N.add 0 (map (get cash) (served s)).

(* The statement's bounds. *)
Record valid_input (t : N) (cash deadline : list N) : Prop := {
  (* N lines, each with c_i and t_i *)
  vi_columns : len deadline = len cash;
  (* 1 <= N <= 10 000 *)
  vi_n : 1 <= len cash <= 10000;
  (* 1 <= T <= 47 *)
  vi_t : 1 <= t <= 47;
  (* 1 <= c_i <= 100 000 *)
  vi_cash : Forall (fun c => 1 <= c <= 100000) cash;
  (* 0 <= t_i < T *)
  vi_deadline : Forall (fun d => d < t) deadline;
}.

(* r is the maximum : some valid schedule collects exactly r, and none
   collects more. *)
Definition bank_spec (t : N) (cash deadline : list N) (r : N) : Prop :=
  (exists s, valid_schedule t cash deadline s /\ value cash s = r) /\
  (forall s, valid_schedule t cash deadline s -> value cash s <= r).

(* machine side : the only thing that gets extracted *)
Program bank : uint -> array uint -> array uint -> uint.

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification bank_correct :
  forall (t : N) (cash deadline : list N)
         (x : uint) (y z : array uint),
  valid_input t cash deadline ->
  repr x t -> repr y cash -> repr z deadline ->
  exists r : N, repr (bank x y z) r /\ bank_spec t cash deadline r.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
