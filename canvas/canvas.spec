(** * Canvas Painting *)

(** ** Description *)

(** Arrange initially white canvases on a conveyor belt and repaint them
    until every canvas has a different colour. Each step selects all canvases
    of one colour and repaints a prefix and the remainder, in belt order,
    with two fresh colours. The ink cost is the total size of the canvases
    repainted. Choose the belt order and repainting steps to minimize ink use.
    Equivalently, colour groups are recursively split until each is a singleton.

    [@kattis canvas]
    - Difficulty: 3.5
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Canvas count: $1 \le n \le 10^{5}$; each size: $1 \le s_i \le 10^{5}$. *)

(** ** Examples *)

(** - Input convention: Case count; each case gives a canvas count followed by the canvas sizes.
    - Output convention: Minimum total ink consumption per case. *)
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
                    It runs in at most c1 * (n + 1) * (log2 n + 1) + c2
                    steps of the cost model on a valid input, n the number
                    of pieces (the heap of Huffman's algorithm), for two
                    constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(* Canvas i
  (i < len sizes) has size sizes_i ; a colour is an
   N. *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The size of canvas [i], using a zero-based index into [sizes]. *)
Definition size (sizes : list N) (i : N) : N :=
  nth (N.to_nat i) sizes 0.

(** The sum of [summand] over zero-based indices below [term_count]. *)
Fixpoint sum_below (summand : N -> N)
  (term_count : nat) : N :=
  match term_count with
  | O => 0
  | S previous => sum_below summand previous + summand
    (N.of_nat previous)
  end.

(** The number of indices below [bound] satisfying [test]. *)
Definition count_below (test : N -> bool) (bound : N) : N :=
  sum_below (fun i => if test i then 1 else 0)
    (N.to_nat bound).

(** An assignment of a colour to each canvas. *)
Definition colouring := N -> N.
(** The initial colouring assigns white to every canvas. *)
Definition white : N := 0.

(** [place] assigns each canvas a distinct position on the belt. *)
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

(** The number of canvases assigned [colour]. *)
Definition count_colour (canvas_count : N)
  (colours : colouring)
  (colour : N) : N :=
  count_below (fun i => colours i =? colour) canvas_count.

(** The number of canvases of [colour] preceding canvas [i] in belt order. *)
Definition left_of (canvas_count : N) (place : N -> N)
  (colours : colouring)
  (colour i : N) : N :=
  count_below (fun j => andb (colours j =? colour)
    (place j <? place i))
    canvas_count.

(** Among canvases of [colour], repaint the first [first_count] in belt order with
    [first_colour] and the rest with [rest_colour]. Leave all other colours
    unchanged. *)
Definition repaint (canvas_count : N) (place : N -> N)
  (colours : colouring)
    (colour first_count first_colour rest_colour : N) :
      colouring :=
  fun i => if colours i =? colour
           then (if left_of canvas_count place colours
             colour i <? first_count
                 then first_colour else rest_colour)
           else colours i.

(** The ink consumed by this step: the sum of the sizes of all canvases currently of
    [colour]. *)
Definition step_ink (sizes : list N) (colours : colouring)
  (colour : N) : N :=
  sum_below
    (fun i => if colours i =? colour then size sizes i else
    0)
    (List.length sizes).

(** [paints sizes place used colours ink] means that a valid repainting run from
    [colours] reaches pairwise distinct canvas colours, consuming [ink] ink.
    Canvas sizes are given by [sizes], and [place] assigns their belt positions.
    The predicate [used] records colours already used, which cannot be chosen as
    fresh colours. Each step repaints a selected colour group in belt order with
    two distinct fresh colours. The prefix may be empty but is smaller than the
    selected group. *)
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
    the machine from all-white canvases spend exactly
    [ink] ink. *)
Definition ink_spent (sizes : list N) (ink : N) : Prop :=
  exists place, belt_order (len sizes) place /\
    paints sizes place (fun seen => seen = white)
      (fun _ => white) ink.

(** [@inside canvas_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (sizes : list N) : Prop := {
  (* 1 <= N_i <= 10^5 : number of canvasses in the test
    case *)
  vi_n : 1 <= len sizes <= 100000;
  (* 1 <= s <= 10^5 : size of each canvas *)
  vi_sizes : Forall
    (fun canvas_size => 1 <= canvas_size <= 100000) sizes;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the minimum ink consumption over all belt orders and valid
    repainting runs from white canvases to pairwise distinct colours. *)
Definition canvas_spec (sizes : list N)
  (output : N) : Prop :=
  ink_spent sizes output /\
    forall ink, ink_spent sizes ink -> output <= ink.

(** ** Complexity *)

(** [@requirement] Runs in $O(n \log(n+1))$ steps, where $n$ is the number of canvases. *)
Definition canvas_time_spec (c1 c2 n_sizes steps : nat) : Prop :=
  (steps <= c1 * ((n_sizes + 1) * (Nat.log2 (n_sizes) + 1)) + c2)%nat.

(** ** Interface *)

(** Choose a belt order and repaint initially white canvases until their colours
    are pairwise distinct, minimizing total ink consumption. Each repainting
    step costs the total size of its selected colour group.
    - Input [sizes]: Size of each canvas; the belt order may be chosen freely.
    - Output [output]: Minimum total ink consumption over all valid repainting runs and belt orders. *)
Program canvas : array uint -> uint.

(** [@example canvas]
    - Sample: 1
    - Case: 1
    - Input [sizes]: [7; 4; 7]
    - Output [output]: 29
*)

(** [@example canvas]
    - Sample: 1
    - Case: 2
    - Input [sizes]: [5; 3; 7; 5]
    - Output [output]: 40
*)

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

(** ** Complexity *)

(** [@hide] [canvas_cost] is the cost translation of [canvas] (the judge
    recomputes it and compares) ... *)
Complexity canvas_cost for canvas.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) * (log2 n + 1) + c2 steps of the cost model on a valid input, n the number of pieces (the heap of Huffman's algorithm), for two constants
    quantified before the inputs, on every valid input. [@requirement canvas_time_spec] *)
Specification canvas_time : exists c1 c2 : nat,
  forall (sizes : list N) (sizes_arr : array uint),
  valid_input sizes -> repr sizes_arr sizes ->
  canvas_time_spec c1 c2 (Cost.size sizes_arr) (cost1 canvas_cost sizes_arr).

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
