(** * Kingpin Escape *)

(** ** Description *)

(** A network of secret passageways connects a kingpin's hideouts. Initially
    there is exactly one route between every pair of hideouts. One hideout
    is the headquarters, where the kingpin is safe.

    Add as few passageways as possible so that, even if the police block any
    one passageway, the kingpin can still reach headquarters from every
    hideout. Report which passageways to add. Passageways can be used in
    either direction, and the blocked passageway may be an original or a new one.

    [@kattis kingpinescape]
    - Difficulty: 7.0
    - CPU time limit: 6 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Vertex count: $2 \le n \le 10^{5}$, initially connected by exactly $n-1$ edges
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
                    It runs in at most c1 * (n + e + 1) + c2 steps of the
                    cost model on a valid input, n the number of hideouts
                    and e of passageways (one depth-first traversal and the
                    leaf pairing), for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** Pair corresponding entries of [first_ends] and [second_ends] to form
    passageways, preserving their order. *)
Definition passageways
  (first_ends second_ends : list N) : list (N * N) :=
  combine first_ends second_ends.

(** An undirected passageway in [network] joins [hideout] and [hideout']. *)
Definition joined (network : list (N * N))
  (hideout hideout' : N) : Prop :=
  In (hideout, hideout') network \/ In (hideout', hideout)
    network.

(** Every consecutive pair in [hideouts] is joined by a passageway in [network]. *)
Fixpoint linked (network : list (N * N))
  (hideouts : list N) : Prop :=
  match hideouts with
  | hideout :: ((next :: _) as rest) =>
      joined network hideout next /\ linked network rest
  | _ => True
  end.

(** [hideouts] is a simple route in [network] from [origin] to [destination], with
    no repeated hideout. *)
Definition route (network : list (N * N))
  (origin destination : N)
    (hideouts : list N) : Prop :=
  NoDup hideouts /\ linked network hideouts /\
  hd_error hideouts = Some origin /\ hd_error (rev hideouts)
    = Some destination.

(** Some simple route in [network] leads from [origin] to [destination]. *)
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

(** Remove the passageway at zero-based index [k] from [network]. *)
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
    The output adds as few passageways as possible while ensuring that every
    hideout can reach headquarters when any one passageway is blocked. *)
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

(** ** Complexity *)

(** [@requirement] Runs in $O(V+E+1)$ steps, where $V$ is the hideout count and $E$ the number of connections. *)
Definition kingpin_escape_time_spec (c1 c2 n_hideout_count n_first_ends steps : nat) : Prop :=
  (steps <= c1 * (n_hideout_count + n_first_ends + 1) + c2)%nat.

(** ** Interface *)

(** Add the fewest secret passageways so every hideout can still reach
    headquarters when any one passageway is blocked.
    - Input [hideout_count]: Number of hideouts, numbered from zero.
    - Input [headquarters]: Hideout containing the safe headquarters.
    - Input [first_ends]: First hideout of each original passageway.
    - Input [second_ends]: Second hideout of each corresponding passageway.
    - Output [output]: Two parallel arrays of endpoint hideouts describing a minimum-size collection of new passageways. *)
Program kingpin_escape :
  uint -> uint -> array uint -> array uint ->
    array uint * array uint.

(** [@example kingpin_escape]
    - Sample: 1
    - Input [hideout_count]: 4
    - Input [headquarters]: 0
    - Input [first_ends]: [0; 0; 0]
    - Input [second_ends]: [1; 2; 3]
    - Output [output]: ([3; 3], [2; 1])
*)

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

(** ** Complexity *)

(** [@hide] [kingpin_escape_cost] is the cost translation of [kingpin_escape] (the judge
    recomputes it and compares) ... *)
Complexity kingpin_escape_cost for kingpin_escape.

(** [@fold complexity bound] ... and runs in at most c1 * (n + e + 1) + c2 steps of the cost model on a valid input, n the number of hideouts and e of passageways (one depth-first traversal and the leaf pairing), for two constants
    quantified before the inputs, on every valid input. [@requirement kingpin_escape_time_spec] *)
Specification kingpin_escape_time : exists c1 c2 : nat,
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
  kingpin_escape_time_spec c1 c2 (size hideout_count_int) (size first_ends_arr) (cost4 kingpin_escape_cost hideout_count_int headquarters_int first_ends_arr second_ends_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
