(** * Chatter *)

(** ** Description *)

(** Generate distinct endpoint pairs using a linear congruential generator,
    joining them until the number of edges equals the number of vertices.
    Return the connected-component count and the frequency of each component
    size, largest first.

    [@kattis chatter]
    - Difficulty: 3.4
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Vertex count: $2 \le n \le 10{,}000$.
    - Seed in $[0, 10{,}000]$; multiplier and increment in $[1, 10{,}000]$.
    - Generator modulus in $[2, 50{,}000]$. *)

(** ** Examples *)

(** - Input convention: One case per line: vertex count, random seed and three generator parameters.
    - Output convention: Component count followed by descending sizes, using size x count without spaces for repeated sizes. *)
(* Input:
10 5 1 2 200
100 311 523 39 101
Output:
6 5 1x5
50 3 2x48 1
*)

(** ** [@hide] Environment *)

(* @function        chatter
   @signature       uint -> uint -> uint -> uint -> uint -> uint * array (uint * uint)
   @math_signature  N -> N -> N -> N -> N -> N * list (N * N)
   @summary         [chatter people_count seed multiplier increment modulus]
                    simulates one day of the chat server: people_count chats
                    are started between people 0..people_count-1 drawn from
                    the generator state <- (state*multiplier+increment) mod
                    modulus seeded with seed.  It returns the number of
                    groups (people linked by chains of chats) and, from the
                    largest size to the smallest, each distinct group size
                    with the number of groups of that size.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Relations Sorted.
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  One call is one day (one input line). *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** Each random value is computed as state <- (state *
    multiplier + increment) mod modulus. *)
Definition next
  (multiplier increment modulus state : N) : N :=
  (state * multiplier + increment) mod modulus.

(** [draw people_count multiplier increment modulus
    state state' person partner]: from generator state
    state, the next chat is between person and partner,
    and the generator is left at state'. person and
    partner are two successive random values mod
    people_count, both drawn again while person =
    partner. *)
Inductive draw
  (people_count multiplier increment modulus : N)
  : N -> N -> N -> N -> Prop :=
| draw_distinct : forall state,
    next multiplier increment modulus state mod people_count
      <>
      next multiplier increment modulus
        (next multiplier increment modulus state) mod
          people_count ->
    draw people_count multiplier increment modulus state
      (next multiplier increment modulus
        (next multiplier increment modulus state))
      (next multiplier increment modulus state mod
        people_count)
      (next multiplier increment modulus
        (next multiplier increment modulus state) mod
          people_count)
| draw_again : forall state state' person partner,
    next multiplier increment modulus state mod people_count
      =
      next multiplier increment modulus
        (next multiplier increment modulus state) mod
          people_count ->
    draw people_count multiplier increment modulus
      (next multiplier increment modulus
        (next multiplier increment modulus state))
      state' person partner ->
    draw people_count multiplier increment modulus state
      state' person
      partner.

(** [rounds people_count multiplier increment modulus
    round_count state chats]: round_count repetitions of
    the simulation from generator state state start the
    chats chats, in order. *)
Inductive rounds
  (people_count multiplier increment modulus : N)
  : nat -> N -> list (N * N) -> Prop :=
| rounds_done : forall state,
    rounds people_count multiplier increment modulus O state
      []
| rounds_step :
  forall round_count state state' person partner chats,
    draw people_count multiplier increment modulus state
      state' person
      partner ->
    rounds people_count multiplier increment modulus
      round_count state'
      chats ->
    rounds people_count multiplier increment modulus
      (S round_count) state
      ((person, partner) :: chats).

(** The chats of the day: people_count repetitions from
    the seed. *)
Definition day
  (people_count seed multiplier increment modulus : N)
  (chats : list (N * N)) : Prop :=
  rounds people_count multiplier increment modulus
    (N.to_nat people_count)
    seed chats.

(** person and other are in the same group: linked by a
    chain of chats. *)
Definition same_group (chats : list (N * N)) : N -> N
  -> Prop :=
  clos_refl_sym_trans N (fun person other => In
    (person, other) chats).

(** Exactly value_count values satisfy property. *)
Definition card (property : N -> Prop)
  (value_count : N) : Prop :=
  exists values, NoDup values /\
    (forall value, In value values <-> property value) /\
    len values = value_count.

(** The group of person has member_count members. *)
Definition group_size (people_count : N) (chats : list
  (N * N))
  (person member_count : N) : Prop :=
  card (fun other => other < people_count
    /\ same_group chats person other)
    member_count.

(** person is the smallest member of its group (one
    leader per group). *)
Definition leader (people_count : N) (chats : list (N * N))
  (person : N)
  : Prop :=
  person < people_count /\
  forall other, same_group chats person other
    -> person <= other.

(** There are exactly group_count groups. *)
Definition num_groups (people_count : N) (chats : list
  (N * N))
  (group_count : N) : Prop :=
  card (leader people_count chats) group_count.

(** Exactly occurrences groups have member_count
    members. *)
Definition num_groups_of_size (people_count : N)
  (chats : list (N * N))
  (member_count occurrences : N) : Prop :=
  card (fun person => leader people_count chats person /\
                      group_size people_count chats person
                        member_count)
    occurrences.

(** [@inside chatter_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input
  (people_count seed multiplier increment modulus : N)
  : Prop := {
  (* 2 <= n <= 10 000 (n = people_count) *)
  vi_n : 2 <= people_count <= 10000;
  (* 0 <= r <= 10 000 (r = seed) *)
  vi_r : seed <= 10000;
  (* 1 <= a, b <= 10 000 (a = multiplier, b = increment) *)
  vi_a : 1 <= multiplier <= 10000;
  vi_b : 1 <= increment <= 10000;
  (* 2 <= c <= 50 000 (c = modulus) *)
  vi_c : 2 <= modulus <= 50000;
  (* the statement's simulation makes its people_count
    chats: every redraw
     while person = partner ends
       (the statement assumes it, as it asks for
     the result) *)
  vi_ends : exists chats,
    day people_count seed multiplier increment modulus
      chats;
}.

(** ** Correctness *)

(** [@requirement]
    The output gives the connected-component count and the frequency of each component
    size in descending size order, after the specified generated connections. *)
Definition chatter_spec
  (people_count seed multiplier increment modulus : N)
  (output : N * list (N * N)) : Prop :=
  match output with
  | (group_count, size_table) =>
      forall chats, day people_count seed multiplier
        increment modulus chats ->
        num_groups people_count chats group_count /\
        StronglySorted
          (fun entry entry' => fst entry' < fst entry)
          size_table /\
        (forall member_count occurrences,
           In (member_count, occurrences) size_table <->
           0 < occurrences /\
           num_groups_of_size people_count chats
             member_count occurrences)
  end.

(** ** Interface *)

(** Generate distinct endpoint pairs using a linear congruential generator, joining them
    until the number of edges equals the number of vertices. Return the connected-
    component count and the frequency of each component size, largest first.
    - Input [people_count]: Number of vertices and generated connections.
    - Input [seed]: Initial state of the connection generator.
    - Input [multiplier]: Multiplier of the linear congruential generator.
    - Input [increment]: Increment of the linear congruential generator.
    - Input [modulus]: Modulus of the linear congruential generator.
    - Output [output]: The output gives the connected-component count and the frequency of each component size in descending size order, after the specified generated connections. *)
Program chatter :
  uint -> uint -> uint -> uint -> uint -> uint * array
    (uint * uint).

(** ** Bridge *)

(** [@requirement chatter_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented output satisfying
    [chatter_spec]. *)
Specification chatter_correct :
  forall (people_count seed multiplier increment modulus :
    N)
    (people_count_int seed_int multiplier_int increment_int
      modulus_int
       : uint),
  valid_input people_count seed multiplier increment modulus
    ->
  repr people_count_int people_count -> repr seed_int seed
    ->
  repr multiplier_int multiplier
    -> repr increment_int increment ->
  repr modulus_int modulus ->
  exists output : N * list (N * N),
    repr (chatter people_count_int seed_int multiplier_int
      increment_int
            modulus_int) output /\
    chatter_spec people_count seed multiplier increment
      modulus output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
