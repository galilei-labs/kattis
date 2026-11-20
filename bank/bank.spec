(** * Bank Queue *)

(** ** Description *)

(** A bank is about to close, and customers are waiting to deposit cash.
    Only one counter is open, serving one customer per minute. Each customer
    has a departure deadline: service must start no later than that minute.
    Choose which customers to serve, and in what order, to collect the most
    cash before closing. Each customer can be served at most once.

    [@kattis bank]
    - Difficulty: 2.3
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Job count: $1 \le n \le 10^{4}$; closing time: $1 \le T \le 47$.
    - Rewards: $1 \le c_i \le 10^{5}$; deadlines: $0 \le t_i < T$. *)

(** ** Examples *)

(** - Input convention: Job count and closing time, followed by reward-deadline pairs.
    - Output convention: A single integer giving the maximum total reward. *)
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
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope N_scope.

(* Person i of the queue is the i-th line of the
  input : c_i
   is the i-th element of cash_amounts, t_i the i-th element
     of deadlines
   (the two columns of the input, as parallel lists). *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [i] in [l], or zero beyond the end. *)
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

(** [plan] finishes by [closing_time], serves only valid queue entries, serves each
    person at most once, and serves each person no later than their departure
    deadline. *)
Definition valid_schedule (closing_time : N)
  (cash_amounts deadlines : list N)
    (plan : schedule) : Prop :=
  len plan <= closing_time /\
  NoDup (served plan) /\
  (forall (minute : nat) (person : N),
     nth_error plan minute = Some (Some person) ->
     person < len cash_amounts
       /\ N.of_nat minute <= get deadlines person).

(** The total cash deposited by the listed customers. *)
Fixpoint customer_cash (cash_amounts customers : list N) : N :=
  match customers with
  | [] => 0
  | person :: rest => get cash_amounts person + customer_cash cash_amounts rest
  end.

(** The cash a schedule collects. *)
Definition value (cash_amounts : list N)
  (plan : schedule) : N :=
  customer_cash cash_amounts (served plan).

(** [@inside bank_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (closing_time : N)
  (cash_amounts deadlines : list N)
    : Prop := {
  (* N lines, each with c_i and t_i *)
  vi_columns : len deadlines = len cash_amounts;
  (* 1 <= N <= 10^4 *)
  vi_n : 1 <= len cash_amounts <= 10000;
  (* 1 <= T <= 47, T the closing time *)
  vi_t : 1 <= closing_time <= 47;
  (* 1 <= c_i <= 10^5 *)
  vi_cash : Forall
    (fun amount => 1 <= amount <= 100000) cash_amounts;
  (* 0 <= t_i < T *)
  vi_deadline : Forall
    (fun deadline => deadline < closing_time) deadlines;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the maximum cash that can be collected before the bank
    closes, serving at most one customer per minute and starting each
    customer's service no later than their departure deadline. *)
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

(** Serve at most one waiting customer per minute to maximize cash deposited
    before the bank closes, respecting each customer's departure deadline.
    - Input [closing_time]: Number of service minutes available, starting at minute zero.
    - Input [cash_amounts]: Cash each customer will deposit.
    - Input [deadlines]: Latest minute at which service may start for each customer.
    - Output [output]: Maximum total cash collected from customers served before closing. *)
Program bank : uint -> array uint -> array uint -> uint.

(** [@example bank]
    - Sample: 1
    - Input [closing_time]: 4
    - Input [cash_amounts]: [1000; 2000; 500; 1200]
    - Input [deadlines]: [1; 2; 2; 0]
    - Output [output]: 4200
*)

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
