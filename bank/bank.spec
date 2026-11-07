(** * Bank Queue *)

(** ** Description *)

(** Choose unit-duration jobs to maximize total reward before a closing
    time. Each job must start no later than its deadline, and only one job
    can run at a time.

    [@kattis bank]
    - Difficulty: 2.3

    **Kattis Bounds**
    - 1 to 10,000 jobs; closing time from 1 to 47.
    - Rewards from 1 to 100,000; deadlines from 0 to closing time - 1. *)

(** ** Examples *)

(** Kattis text input and output. *)
(* Input:
4 4
1000 1
2000 2
500 2
1200 0
Output:
4200
*)

(** ** [@hide] Environment *)

(* @function        bank
   @signature       uint -> array uint -> array uint -> uint
   @math_signature  N -> list N -> list N -> N
   @summary         [bank closing_time cash_amounts deadlines] is the largest
                    total cash the bank can collect in the closing_time
                    minutes before it closes, serving at most one person per
                    minute, person i bringing cash_amounts_i and having to be
                    served at a minute that starts no later than
                    deadlines_i.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  Person i of the queue is the i-th line of the
  input : c_i
   is the i-th element of cash_amounts, t_i the i-th element
     of deadlines
   (the two columns of the input, as parallel lists). *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The i-th element of l (0 beyond the end). *)
Definition get (l : list N) (i : N) : N :=
  nth (N.to_nat i) l 0.

(** A schedule lists, minute by minute from minute 0,
    the person served during that minute ([Some person])
    or an idle minute ([None]). *)
Definition schedule := list (option N).

(** The persons a schedule serves, in order. *)
Definition served (plan : schedule) : list N :=
  flat_map
    (fun slot => match slot with Some person => [person] |
      None => [] end)
    plan.

(** plan ends before the bank closes, serves each person
    at most once, and serves only persons of the queue,
    each at a minute minute <= its t_i. *)
Definition valid_schedule (closing_time : N)
  (cash_amounts deadlines : list N)
    (plan : schedule) : Prop :=
  len plan <= closing_time /\
  NoDup (served plan) /\
  (forall (minute : nat) (person : N),
     nth_error plan minute = Some (Some person) ->
     person < len cash_amounts
       /\ N.of_nat minute <= get deadlines person).

(** The cash a schedule collects. *)
Definition value (cash_amounts : list N)
  (plan : schedule) : N :=
  fold_right N.add 0 (map (get cash_amounts) (served plan)).

(** [@inside bank_correct] The statement's bounds. *)
Record valid_input (closing_time : N)
  (cash_amounts deadlines : list N)
    : Prop := {
  (* N lines, each with c_i and t_i *)
  vi_columns : len deadlines = len cash_amounts;
  (* 1 <= N <= 10 000 *)
  vi_n : 1 <= len cash_amounts <= 10000;
  (* 1 <= T <= 47, T the closing time *)
  vi_t : 1 <= closing_time <= 47;
  (* 1 <= c_i <= 100 000 *)
  vi_cash : Forall
    (fun amount => 1 <= amount <= 100000) cash_amounts;
  (* 0 <= t_i < T *)
  vi_deadline : Forall
    (fun deadline => deadline < closing_time) deadlines;
}.

(** ** Correctness *)

(** [@requirement] [@short must return the greatest cash
    collectable before closing.] output is the maximum :
    some valid schedule collects exactly output, and
    none collects more. *)
Definition bank_spec (closing_time : N)
  (cash_amounts deadlines : list N)
    (output : N) : Prop :=
  (exists plan, valid_schedule closing_time cash_amounts
    deadlines plan /\
                value cash_amounts plan = output) /\
  (forall plan, valid_schedule closing_time cash_amounts
    deadlines plan ->
                value cash_amounts plan <= output).

(** ** Interface *)

(** The machine-level interface.
    - Input [closing_time]:
    - Input [cash_amounts]:
    - Input [deadlines]:
    - Output [output]: *)
Program bank : uint -> array uint -> array uint -> uint.

(** ** Bridge *)

(** [@requirement bank_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented output satisfying [bank_spec]. *)
Specification bank_correct :
  forall (closing_time : N)
    (cash_amounts deadlines : list N)
         (closing_time_int : uint)
         (cash_amounts_arr deadlines_arr : array uint),
  valid_input closing_time cash_amounts deadlines ->
  repr closing_time_int closing_time
    -> repr cash_amounts_arr cash_amounts ->
  repr deadlines_arr deadlines ->
  exists output : N,
    repr (bank closing_time_int cash_amounts_arr
      deadlines_arr) output /\
    bank_spec closing_time cash_amounts deadlines output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
