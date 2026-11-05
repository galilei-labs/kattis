(* @function        canvas
   @signature       array uint -> uint
   @math_signature  list N -> N
   @summary         [canvas s] is the least total ink the painting machine
                    of the statement can spend, over every order of the belt
                    and every run of painting steps, to take the canvasses of
                    sizes s_0, ..., s_(n-1), all of one colour at first, to
                    pairwise distinct colours.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  Canvas i (i < len s) has size s_i ; a colour is an N. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The size of canvas i. *)
Definition size (s : list N) (i : N) : N := nth (N.to_nat i) s 0.

(* f 0 + f 1 + ... + f (n - 1). *)
Fixpoint sum_below (f : N -> N) (n : nat) : N :=
  match n with
  | O => 0
  | S m => sum_below f m + f (N.of_nat m)
  end.

(* The number of i < n with P i. *)
Definition count_below (P : N -> bool) (n : N) : N :=
  sum_below (fun i => if P i then 1 else 0) (N.to_nat n).

(* A colouring gives each canvas its colour ; at first all are white. *)
Definition colouring := N -> N.
Definition white : N := 0.

(* Step 1 : [pos i] is the place of canvas i on the belt ; places are
   distinct. *)
Definition belt_order (n : N) (pos : N -> N) : Prop :=
  forall i j, i < n -> j < n -> pos i = pos j -> i = j.

Definition all_distinct (n : N) (c : colouring) : Prop :=
  forall i j, i < n -> j < n -> i <> j -> c i <> c j.

(* The number of canvasses of colour C. *)
Definition count_colour (n : N) (c : colouring) (C : N) : N :=
  count_below (fun i => c i =? C) n.

(* The number of canvasses of colour C to the left of canvas i. *)
Definition left_of (n : N) (pos : N -> N) (c : colouring) (C i : N) : N :=
  count_below (fun j => andb (c j =? C) (pos j <? pos i)) n.

(* Step 3 : going left to right, the first F canvasses of colour C get X,
   the other canvasses of colour C get Y, every other canvas keeps its
   colour. *)
Definition repaint (n : N) (pos : N -> N) (c : colouring) (C F X Y : N)
    : colouring :=
  fun i => if c i =? C
           then (if left_of n pos c C i <? F then X else Y)
           else c i.

(* The ink of that step : the sum of the sizes of the canvasses of colour C. *)
Definition step_ink (s : list N) (c : colouring) (C : N) : N :=
  sum_below (fun i => if c i =? C then size s i else 0) (List.length s).

(* [paints s pos used c k] : from colouring c, [used] holding every colour
   used so far, the machine repeats steps 2 and 3 (F less than the number
   of canvasses of colour C ; X and Y distinct and never used) until all
   colours are distinct, and spends k ink in total. *)
Inductive paints (s : list N) (pos : N -> N)
    : (N -> Prop) -> colouring -> N -> Prop :=
| paints_done : forall used c,
    all_distinct (len s) c -> paints s pos used c 0
| paints_step : forall used c C F X Y k,
    ~ all_distinct (len s) c ->
    F < count_colour (len s) c C ->
    X <> Y -> ~ used X -> ~ used Y ->
    paints s pos (fun z => used z \/ z = X \/ z = Y)
                 (repaint (len s) pos c C F X Y) k ->
    paints s pos used c (step_ink s c C + k).

(* Some order of the belt, chosen once, and some run of the machine from
   all-white canvasses spend exactly k ink. *)
Definition ink_spent (s : list N) (k : N) : Prop :=
  exists pos, belt_order (len s) pos /\
              paints s pos (fun z => z = white) (fun _ => white) k.

(* The statement's bounds, for one test case. *)
Record valid_input (s : list N) : Prop := {
  (* 1 <= N_i <= 100 000 : number of canvasses in the test case *)
  vi_n : 1 <= len s <= 100000;
  (* 1 <= s <= 100 000 : size of each canvas *)
  vi_sizes : Forall (fun x => 1 <= x <= 100000) s;
}.

(* The answer : an amount of ink some painting spends, and no painting
   spends less. *)
Definition canvas_spec (s : list N) (o : N) : Prop :=
  ink_spent s o /\ forall k, ink_spent s k -> o <= k.

Program canvas : array uint -> uint.

Specification canvas_correct : forall (s : list N) (x : array uint),
  valid_input s -> repr x s ->
  exists o : N, repr (canvas x) o /\ canvas_spec s o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
