(** * Kingpin Escape *)

(** ** Description *)

(** Add the fewest edges to a tree so the graph remains connected after any
    single edge is removed.

    [@kattis kingpinescape]
    - Difficulty: 7.0
    - CPU time limit: 6 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 2 to $10^{5}$ vertices, initially connected by exactly n - 1 edges
      forming a tree. *)

(** ** Examples *)

(** - Input convention: Vertex count and root index, followed by the tree's 0-based edge endpoints.
    - Output convention: Minimum added-edge count, followed by one endpoint pair per new edge. *)
(* Input:
4 0
0 1
0 2
0 3
Output:
2
3 2
3 1
*)

(** ** [@hide] Environment *)
(* @function        kingpin_escape
   @signature       uint -> uint -> array uint -> array uint -> array uint * array uint
   @math_signature  N -> N -> list N -> list N -> list N * list N
   @summary         [kingpin_escape hideout_count headquarters first_ends
                    second_ends] takes a tree on hideouts
                    0..hideout_count-1, given as its hideout_count-1
                    passageways (first_ends_k, second_ends_k), and the
                    headquarters.  It returns new passageways, as two
                    parallel lists, such that after adding them every
                    hideout still reaches the headquarters when any one
                    passageway is blocked, and no smaller set of new
                    passageways does so.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side. A hideout is an N; a set of passageways is a list of
    pairs, one entry per passageway (a passageway may be listed
    twice). The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The passageways given by two parallel lists (the input's two
    columns, or the output's): the pairs (first_ends_k,
    second_ends_k). *)
Definition passageways
  (first_ends second_ends : list N) : list (N * N) :=
  combine first_ends second_ends.

(** A passageway of network joins hideout and hideout' (in either
    direction). *)
Definition joined (network : list (N * N))
  (hideout hideout' : N) : Prop :=
  In (hideout, hideout') network \/ In (hideout', hideout)
    network.

(** Each hideout of hideouts is joined to the next one by a passageway
    of network. *)
Fixpoint linked (network : list (N * N))
  (hideouts : list N) : Prop :=
  match hideouts with
  | hideout :: ((next :: _) as rest) =>
      joined network hideout next /\ linked network rest
  | _ => True
  end.

(** A route from origin to destination: hideouts, none visited twice,
    from origin to destination, each joined to the next by a
    passageway of network. *)
Definition route (network : list (N * N))
  (origin destination : N)
    (hideouts : list N) : Prop :=
  NoDup hideouts /\ linked network hideouts /\
  hd_error hideouts = Some origin /\ hd_error (rev hideouts)
    = Some destination.

(** The [reaches] definition. *)
Definition reaches (network : list (N * N))
  (origin destination : N) : Prop :=
  exists hideouts, route network origin destination
    hideouts.

(** From every hideout to every other hideout there is precisely one
    route. *)
Definition is_tree (hideout_count : N)
  (network : list (N * N)) : Prop :=
  forall origin destination, origin < hideout_count ->
    destination < hideout_count ->
    exists! hideouts, route network origin destination
      hideouts.

(** network with its k-th passageway blocked. *)
Definition block (network : list (N * N))
  (k : nat) : list (N * N) :=
  firstn k network ++ skipn (S k) network.

(** Whenever at most one passageway of network is blocked, every hideout
    still reaches the headquarters. *)
Definition safe (hideout_count headquarters : N)
  (network : list (N * N))
    : Prop :=
  (forall hideout, hideout < hideout_count ->
     reaches network hideout headquarters) /\
  (forall k hideout, (k < List.length network)%nat ->
     hideout < hideout_count ->
     reaches (block network k) hideout headquarters).

(** Both ends of every passageway of additions are hideouts. *)
Definition in_range (hideout_count : N)
  (additions : list (N * N)) : Prop :=
  forall hideout hideout', In (hideout, hideout') additions
    ->
    hideout < hideout_count /\ hideout' < hideout_count.

(** [@inside kingpin_escape_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (hideout_count headquarters : N)
    (first_ends second_ends : list N) : Prop := {
  (* 2 <= n <= 10^5, the number of hideouts *)
  vi_n : 2 <= hideout_count <= 10 ^ 5;
  (* 0 <= h < n, the location of your headquarters *)
  vi_h : headquarters < hideout_count;
  (* then follow n - 1 lines, each with two integers a, b *)
  vi_ea_len : len first_ends = hideout_count - 1;
  vi_eb_len : len second_ends = hideout_count - 1;
  (* 0 <= a, b < n *)
  vi_ea : Forall (fun hideout => hideout < hideout_count)
    first_ends;
  vi_eb : Forall (fun hideout => hideout < hideout_count)
    second_ends;
  (* from every hideout to every other hideout there is
     precisely one route through the network *)
  vi_tree : is_tree hideout_count (passageways first_ends
    second_ends);
}.

(** ** Correctness *)

(** [@requirement]
    The output is a minimum set of added edges that preserves connectivity after removal
    of any single edge. *)
Definition kingpin_escape_spec
  (hideout_count headquarters : N)
    (first_ends second_ends : list N) (output : list N *
      list N)
  : Prop :=
  match output with
  | (added_firsts, added_seconds) =>
      len added_firsts = len added_seconds /\
      in_range hideout_count (passageways added_firsts
        added_seconds) /\
      safe hideout_count headquarters
        (passageways first_ends second_ends ++
         passageways added_firsts added_seconds) /\
      (forall additions, in_range hideout_count additions ->
         safe hideout_count headquarters
           (passageways first_ends second_ends ++ additions)
             ->
         len added_firsts <= len additions)
  end.

(** ** Interface *)

(** Add the fewest edges to a tree so the graph remains connected after any single edge is
    removed.
    - Input [hideout_count]:
    - Input [headquarters]:
    - Input [first_ends]:
    - Input [second_ends]:
    - Output [output]: *)
Program kingpin_escape :
  uint -> uint -> array uint -> array uint ->
    array uint * array uint.

(** ** Bridge *)

(** [@requirement kingpin_escape_spec] [@fold full correctness
    statement] On valid represented inputs, [kingpin_escape] returns
    a represented output satisfying [kingpin_escape_spec]. *)
Specification kingpin_escape_correct :
  forall (hideout_count headquarters : N) (first_ends
    second_ends : list N)
         (hideout_count_int headquarters_int : uint)
         (first_ends_arr second_ends_arr : array uint),
  valid_input hideout_count headquarters first_ends
    second_ends ->
  repr hideout_count_int hideout_count ->
  repr headquarters_int headquarters ->
  repr first_ends_arr first_ends ->
    repr second_ends_arr second_ends ->
  exists output : list N * list N,
    repr (kingpin_escape hideout_count_int headquarters_int
      first_ends_arr
            second_ends_arr) output /\
    kingpin_escape_spec hideout_count headquarters
      first_ends second_ends
      output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
