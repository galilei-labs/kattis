(* @function        chatter
   @signature       uint -> uint -> uint -> uint -> uint -> uint * array (uint * uint)
   @math_signature  N -> N -> N -> N -> N -> N * list (N * N)
   @summary         [chatter n r a b c] simulates one day of the chat server:
                    n chats are started between people 0..n-1 drawn from the
                    generator r <- (r*a+b) mod c seeded with r.  It returns the
                    number of groups (people linked by chains of chats) and,
                    from the largest size to the smallest, each distinct group
                    size with the number of groups of that size.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Relations Sorted.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  One call is one day (one input line). *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* Each random value is computed as r <- (r * a + b) mod c. *)
Definition next (a b c r : N) : N := (r * a + b) mod c.

(* [draw n a b c r r' x y]: from generator state r, the next chat is between
   x and y, and the generator is left at r'.  x and y are two successive
   random values mod n, both drawn again while x = y. *)
Inductive draw (n a b c : N) : N -> N -> N -> N -> Prop :=
| draw_distinct : forall r,
    next a b c r mod n <> next a b c (next a b c r) mod n ->
    draw n a b c r (next a b c (next a b c r))
      (next a b c r mod n) (next a b c (next a b c r) mod n)
| draw_again : forall r r' x y,
    next a b c r mod n = next a b c (next a b c r) mod n ->
    draw n a b c (next a b c (next a b c r)) r' x y ->
    draw n a b c r r' x y.

(* [rounds n a b c k r es]: k repetitions of the simulation from generator
   state r start the chats es, in order. *)
Inductive rounds (n a b c : N) : nat -> N -> list (N * N) -> Prop :=
| rounds_done : forall r, rounds n a b c O r []
| rounds_step : forall k r r' x y es,
    draw n a b c r r' x y -> rounds n a b c k r' es ->
    rounds n a b c (S k) r ((x, y) :: es).

(* The chats of the day: n repetitions from the seed r. *)
Definition day (n r a b c : N) (es : list (N * N)) : Prop :=
  rounds n a b c (N.to_nat n) r es.

(* p and q are in the same group: linked by a chain of chats. *)
Definition same_group (es : list (N * N)) : N -> N -> Prop :=
  clos_refl_sym_trans N (fun p q => In (p, q) es).

(* Exactly k values satisfy P. *)
Definition card (P : N -> Prop) (k : N) : Prop :=
  exists l, NoDup l /\ (forall x, In x l <-> P x) /\ len l = k.

(* The group of person p has s members. *)
Definition group_size (n : N) (es : list (N * N)) (p s : N) : Prop :=
  card (fun q => q < n /\ same_group es p q) s.

(* Person p is the smallest member of its group (one leader per group). *)
Definition leader (n : N) (es : list (N * N)) (p : N) : Prop :=
  p < n /\ forall q, same_group es p q -> p <= q.

(* There are exactly k groups. *)
Definition num_groups (n : N) (es : list (N * N)) (k : N) : Prop :=
  card (leader n es) k.

(* Exactly k groups have s members. *)
Definition num_groups_of_size (n : N) (es : list (N * N)) (s k : N) : Prop :=
  card (fun p => leader n es p /\ group_size n es p s) k.

(* The statement's bounds, for one day. *)
Record valid_input (n r a b c : N) : Prop := {
  (* 2 <= n <= 10 000 *)
  vi_n : 2 <= n <= 10000;
  (* 0 <= r <= 10 000 *)
  vi_r : r <= 10000;
  (* 1 <= a, b <= 10 000 *)
  vi_a : 1 <= a <= 10000;
  vi_b : 1 <= b <= 10000;
  (* 2 <= c <= 50 000 *)
  vi_c : 2 <= c <= 50000;
  (* the statement's simulation makes its n chats: every redraw while
     x = y ends (the statement assumes it, as it asks for the result) *)
  vi_ends : exists es, day n r a b c es;
}.

(* The number of groups g, and the table t of the distinct group sizes,
   largest first, each with the number of groups of that size. *)
Definition chatter_spec (n r a b c : N) (o : N * list (N * N)) : Prop :=
  let (g, t) := o in
  forall es, day n r a b c es ->
    num_groups n es g /\
    StronglySorted (fun e f => fst f < fst e) t /\
    (forall s k, In (s, k) t <-> 0 < k /\ num_groups_of_size n es s k).

Program chatter :
  uint -> uint -> uint -> uint -> uint -> uint * array (uint * uint).

Specification chatter_correct :
  forall (n r a b c : N) (xn xr xa xb xc : uint),
  valid_input n r a b c ->
  repr xn n -> repr xr r -> repr xa a -> repr xb b -> repr xc c ->
  exists o : N * list (N * N),
    repr (chatter xn xr xa xb xc) o /\ chatter_spec n r a b c o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
