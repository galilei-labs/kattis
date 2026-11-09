(** * Canvas Painting *)

(** ** Description *)

(** Repeatedly split a group of weighted items into two groups, paying the
    group's total weight for each split. Find the minimum cost of separating
    all items into singletons.

    [@kattis canvas]
    - Difficulty: 3.5
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Item count: $1 \le n \le 100{,}000$; each weight in $[1, 100{,}000]$. *)

(** ** Examples *)

(** - Input convention: Case count; each case gives a weight count followed by the weights.
    - Output convention: One minimum total splitting cost per case. *)
(* Input:
2
3
7 4 7
4
5 3 7 5
Output:
29
40
*)

(** ** [@hide] Environment *)

(* @function        canvas
   @signature       array uint -> uint
   @math_signature  list N -> N
   @summary         [canvas sizes] is the least total ink the painting
                    machine of the statement can spend, over every order of
                    the belt and every run of painting steps, to take the
                    canvasses of sizes sizes_0, ..., sizes_(n-1), all of one
                    colour at first, to pairwise distinct colours.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  Canvas i
  (i < len sizes) has size sizes_i ; a colour is an
   N. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The size of canvas i. *)
Definition size (sizes : list N) (i : N) : N :=
  nth (N.to_nat i) sizes 0.

(** summand 0 + summand 1 + ... + summand (term_count -
    1). *)
Fixpoint sum_below (summand : N -> N)
  (term_count : nat) : N :=
  match term_count with
  | O => 0
  | S previous => sum_below summand previous + summand
    (N.of_nat previous)
  end.

(** The number of i < bound with test i. *)
Definition count_below (test : N -> bool) (bound : N) : N :=
  sum_below (fun i => if test i then 1 else 0)
    (N.to_nat bound).

(** A colouring gives each canvas its colour ; at first
    all are white. *)
Definition colouring := N -> N.
(** The initial colouring assigns white to every canvas. *)
Definition white : N := 0.

(** Step 1 : [place i] is the place of canvas i on the
    belt ; places are distinct. *)
Definition belt_order (canvas_count : N) (place : N
  -> N) : Prop :=
  forall i j, i < canvas_count -> j < canvas_count
    -> place i = place j ->
    i = j.

(** Every canvas has a different colour. *)
Definition all_distinct (canvas_count : N)
  (colours : colouring) : Prop :=
  forall i j, i < canvas_count -> j < canvas_count
    -> i <> j ->
    colours i <> colours j.

(** The number of canvasses of colour colour. *)
Definition count_colour (canvas_count : N)
  (colours : colouring)
  (colour : N) : N :=
  count_below (fun i => colours i =? colour) canvas_count.

(** The number of canvasses of colour colour to the left
    of canvas i. *)
Definition left_of (canvas_count : N) (place : N -> N)
  (colours : colouring)
  (colour i : N) : N :=
  count_below (fun j => andb (colours j =? colour)
    (place j <? place i))
    canvas_count.

(** Step 3 : going left to right, the first first_count
    canvasses of colour colour get first_colour, the
    other canvasses of colour colour get rest_colour,
    every other canvas keeps its colour. *)
Definition repaint (canvas_count : N) (place : N -> N)
  (colours : colouring)
    (colour first_count first_colour rest_colour : N) :
      colouring :=
  fun i => if colours i =? colour
           then (if left_of canvas_count place colours
             colour i <? first_count
                 then first_colour else rest_colour)
           else colours i.

(** The ink of that step : the sum of the sizes of the
    canvasses of colour colour. *)
Definition step_ink (sizes : list N) (colours : colouring)
  (colour : N) : N :=
  sum_below
    (fun i => if colours i =? colour then size sizes i else
    0)
    (List.length sizes).

(** [paints sizes place used colours ink] : from
    colouring colours, [used] holding every colour used
    so far, the machine repeats steps 2 and 3
    (first_count less than the number of canvasses of
    colour colour ; first_colour and rest_colour
    distinct and never used) until all colours are
    distinct, and spends [ink] ink in total. *)
Inductive paints (sizes : list N) (place : N -> N)
    : (N -> Prop) -> colouring -> N -> Prop :=
| paints_done : forall used colours,
    all_distinct (len sizes) colours
      -> paints sizes place used colours 0
| paints_step :
  forall used colours colour first_count first_colour
                       rest_colour ink,
    ~ all_distinct (len sizes) colours ->
    first_count < count_colour (len sizes) colours colour ->
    first_colour <> rest_colour -> ~ used first_colour
      -> ~ used rest_colour ->
    paints sizes place
      (fun seen => used seen \/ seen = first_colour
        \/ seen = rest_colour)
      (repaint (len sizes) place colours colour first_count
        first_colour
         rest_colour)
      ink ->
    paints sizes place used colours
      (step_ink sizes colours colour + ink).

(** Some order of the belt, chosen once, and some run of
    the machine from all-white canvasses spend exactly
    [ink] ink. *)
Definition ink_spent (sizes : list N) (ink : N) : Prop :=
  exists place, belt_order (len sizes) place /\
    paints sizes place (fun seen => seen = white)
      (fun _ => white) ink.

(** [@inside canvas_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (sizes : list N) : Prop := {
  (* 1 <= N_i <= 100 000 : number of canvasses in the test
    case *)
  vi_n : 1 <= len sizes <= 100000;
  (* 1 <= s <= 100 000 : size of each canvas *)
  vi_sizes : Forall
    (fun canvas_size => 1 <= canvas_size <= 100000) sizes;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the minimum total cost of recursively splitting the weighted items
    into singletons, charging the total weight of each group split. *)
Definition canvas_spec (sizes : list N)
  (output : N) : Prop :=
  ink_spent sizes output /\
    forall ink, ink_spent sizes ink -> output <= ink.

(** ** Interface *)

(** Repeatedly split a group of weighted items into two groups, paying the group's total
    weight for each split. Find the minimum cost of separating all items into
    singletons.
    - Input [sizes]: Weights of the items to separate.
    - Output [output]: The output is the minimum total cost of recursively splitting the weighted items into singletons, charging the total weight of each group split. *)
Program canvas : array uint -> uint.

(** ** Bridge *)

(** [@requirement canvas_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented output satisfying
    [canvas_spec]. *)
Specification canvas_correct :
  forall (sizes : list N) (sizes_arr : array uint),
  valid_input sizes -> repr sizes_arr sizes ->
  exists output : N,
    repr (canvas sizes_arr) output
      /\ canvas_spec sizes output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
