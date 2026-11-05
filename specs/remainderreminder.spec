(* @function        remainderreminder
   @signature       uint -> uint -> uint -> uint -> uint -> uint -> uint -> uint
   @math_signature  N -> N -> N -> N -> N -> N -> N -> N
   @summary         [remainderreminder a b c d e f g] is the number of books n,
                    f <= n <= g, that leaves c, d and e books over when packed
                    in boxes of the largest, second largest and third largest
                    of the distinct volumes of the open boxes foldable from an
                    a-by-b sheet by cutting equal integer squares at the four
                    corners. The input guarantees that exactly one such n
                    exists.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A book is a 1-inch cube, so a box holds as many books as its
   volume in cubic inches. *)

(* Cutting x-by-x squares at the corners of an a-by-b sheet folds a box of
   integer dimensions x, a - 2x, b - 2x, all at least 1. *)
Definition cut_ok (a b x : N) : Prop :=
  1 <= x /\ 2 * x < a /\ 2 * x < b.

(* [v] is the volume of some box foldable from the sheet. *)
Definition box_size (a b v : N) : Prop :=
  exists x, cut_ok a b x /\ v = x * (a - 2 * x) * (b - 2 * x).

(* v1 > v2 > v3 are the three largest distinct box sizes. *)
Definition three_largest (a b v1 v2 v3 : N) : Prop :=
  box_size a b v1 /\ box_size a b v2 /\ box_size a b v3 /\
  v3 < v2 < v1 /\
  forall v, box_size a b v -> v = v1 \/ v = v2 \/ v = v3 \/ v < v3.

(* [n] books fit everything Bill remembers: n lies in [f, g] and leaves c,
   d, e books over with the largest, second and third largest box size. *)
Definition consistent (a b c d e f g n : N) : Prop :=
  f <= n <= g /\
  exists v1 v2 v3, three_largest a b v1 v2 v3 /\
    n mod v1 = c /\ n mod v2 = d /\ n mod v3 = e.

(* The statement's bounds. *)
Record valid_input (a b c d e f g : N) : Prop := {
  (* a <= b, 7 <= a, b <= 100 *)
  vi_ab : a <= b;
  vi_a : 7 <= a <= 100;
  vi_b : 7 <= b <= 100;
  (* 1 <= c, d, e <= 10^9 *)
  vi_c : 1 <= c <= 10 ^ 9;
  vi_d : 1 <= d <= 10 ^ 9;
  vi_e : 1 <= e <= 10 ^ 9;
  (* 1 <= f < g <= 10^9 *)
  vi_fg : 1 <= f < g;
  vi_g : g <= 10 ^ 9;
  (* Each problem is guaranteed to have a unique answer. *)
  vi_unique : exists! n, consistent a b c d e f g n;
}.

(* The answer is the one consistent number of books. *)
Definition remainderreminder_spec (a b c d e f g o : N) : Prop :=
  forall n, consistent a b c d e f g n <-> n = o.

Program remainderreminder :
  uint -> uint -> uint -> uint -> uint -> uint -> uint -> uint.

Specification remainderreminder_correct :
  forall (a b c d e f g : N) (xa xb xc xd xe xf xg : uint),
  valid_input a b c d e f g ->
  repr xa a -> repr xb b -> repr xc c -> repr xd d -> repr xe e ->
  repr xf f -> repr xg g ->
  exists o : N, repr (remainderreminder xa xb xc xd xe xf xg) o /\
                remainderreminder_spec a b c d e f g o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
