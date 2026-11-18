(** * Excavator Expedition *)

(** ** Description *)

(** Travel along directed roads from the first location to the last,
    maximizing happiness. Visiting an internal construction site (X) adds
    one; visiting a boring site (.) subtracts one. The first and last
    locations are homes and contribute zero. Roads form an acyclic graph.

    [@kattis excavatorexpedition]
    - Difficulty: 4.1
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Vertex count: $2 \le n \le 4 \times 10^{5}$; Edge count: $1 \le m \le 4 \times 10^{5}$.
    - The graph is acyclic and contains a path from the first vertex to the
      last. *)

(** ** Examples *)

(** - Input convention: Vertex and edge counts, a string of X/. vertex labels, then directed endpoint pairs.
    - Output convention: The maximum path score from vertex 0 to the last vertex. *)
(* Input:
13 15
.X...X.X...X.
0 1
0 2
1 3
2 4
3 5
4 5
5 6
5 7
5 8
6 12
7 9
8 10
9 11
10 11
11 12
Output:
2
*)

(** ** [@hide] Environment *)
(* @function        excavator
   @signature       PrimString.string -> array uint -> array uint -> sint
   @math_signature  String.string -> list N -> list N -> Z
   @summary         [excavator sites edge_sources edge_targets] takes the V
                    sites of a directed acyclic graph (sites.[i] = 'X' for a
                    construction site, '.' for a boring one) and its E edges
                    edge_sources.[k] -> edge_targets.[k], and returns the
                    largest happiness of a route from location 0 to location
                    V-1: the number of construction sites visited minus the
                    number of boring sites visited, the two ends not
                    counted. It may be negative.
                    It runs in at most c1 * (V + E + 1) + c2 steps of the
                    cost model on a valid input, V the number of sites and E
                    of passages (the topological sort and one relaxation
                    sweep), for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Relations.
From Stdlib Require Import String Ascii.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).
(** The number of characters in [text]. *)
Definition slen (text : string) : N :=
  N.of_nat (String.length text).

(** The input contains a directed road from [origin] to [destination]. *)
Definition edge (edge_sources edge_targets : list N)
  (origin destination : N)
    : Prop :=
  exists k, nth_error edge_sources k = Some origin /\
            nth_error edge_targets k = Some destination.

(** Every consecutive pair of entries in [locations] is connected by a directed
    input edge. *)
Fixpoint walk (edge_sources edge_targets : list N)
  (locations : list N)
    : Prop :=
  match locations with
  | here :: ((next :: _) as rest) =>
      edge edge_sources edge_targets here next /\
      walk edge_sources edge_targets rest
  | _ => True
  end.

(** A directed walk from location zero to the last location, represented by its
    visited locations in order. *)
Definition route (sites : string)
  (edge_sources edge_targets locations
    : list N) : Prop :=
  walk edge_sources edge_targets locations /\
  hd_error locations = Some 0%N /\
  last locations 0%N = (slen sites - 1)%N.

(** The location has site marker [kind] in [sites]. *)
Definition is_site (sites : string) (kind : ascii)
  (location : N) : bool :=
  match String.get (N.to_nat location) sites with
  | Some found => Ascii.eqb found kind
  | None => false
  end.

(** The number of visits in [locations] with site marker [kind], excluding the two
    homes. *)
Definition count_sites (sites : string) (kind : ascii)
  (locations : list N)
    : Z :=
  Z.of_nat (List.length (filter (fun location =>
    andb (negb (orb (location =? 0)%N (location =? slen
      sites - 1)%N))
         (is_site sites kind location)) locations)).

(** The number of construction-site visits minus the number of boring-site visits
    along [locations], excluding the homes. *)
Definition happiness (sites : string)
  (locations : list N) : Z :=
  count_sites sites "X"%char locations - count_sites sites
    "."%char locations.

(** [@inside excavator_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (sites : string)
  (edge_sources edge_targets : list N)
    : Prop := {
  (* 1 < V <= 4 * 10^5 (V is the number of characters of
     the site line) *)
  vi_V : (2 <= slen sites <= 400000)%N;
  (* 0 < E <= 4 * 10^5 *)
  vi_E : (1 <= len edge_sources <= 400000)%N;
  (* E lines, each with two integers F_i and T_i *)
  vi_lines : len edge_targets = len edge_sources;
  (* 0 <= F_i, T_i < V *)
  vi_src : Forall (fun origin => (origin < slen sites)%N)
    edge_sources;
  vi_dst : Forall (fun destination => (destination < slen
    sites)%N)
             edge_targets;
  (* for all 0 < i < V, V_i is '.' or 'X' *)
  vi_sites : forall i, (0 < i < slen sites)%N ->
    is_site sites "."%char i = true \/ is_site sites
      "X"%char i = true;
  (* for i in {0, V - 1}, V_i = '.' *)
  vi_homes : is_site sites "."%char 0 = true /\
             is_site sites "."%char (slen sites - 1) = true;
  (* there is always a path from Amka's house to Nanouk's
     grandparents *)
  vi_path : exists locations, route sites edge_sources
    edge_targets locations;
  (* there are no cycles in the graph *)
  vi_acyclic : forall location,
    ~ clos_trans N (edge edge_sources edge_targets) location
      location;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the maximum happiness of a route from the first home to the last,
    counting X as +1 and . as -1 at internal locations and excluding the homes. *)
Definition excavator_spec (sites : string)
  (edge_sources edge_targets
    : list N) (output : Z) : Prop :=
  (exists locations, route sites edge_sources edge_targets
    locations /\
     happiness sites locations = output) /\
  (forall locations, route sites edge_sources edge_targets
    locations ->
     happiness sites locations <= output).

(** ** Complexity *)

(** [@requirement] Runs in $O(n+m+1)$ steps, where $n$ is the number of sites and $m$ the number of edges. *)
Definition excavator_time_spec (c1 c2 n_sites n_edge_sources steps : nat) : Prop :=
  (steps <= c1 * (n_sites + n_edge_sources + 1) + c2)%nat.

(** ** Interface *)

(** Find a route of maximum happiness from the first home to the last home
    through the acyclic road network, scoring internal construction sites
    positively and boring sites negatively.
    - Input [sites]: One marker per zero-based location: X is a construction site (+1), . a boring site (-1). Locations zero and [slen sites - 1] are homes and score zero despite their . markers.
    - Input [edge_sources]: Zero-based starting location of each directed road.
    - Input [edge_targets]: Zero-based destination of each corresponding road.
    - Output [output]: Maximum route happiness, counting only internal locations. *)
Program excavator : PrimString.string -> array uint -> array
  uint -> sint.

(** [@example excavator]
    - Sample: 1
    - Input [sites]: ".X...X.X...X."%string
    - Input [edge_sources]: [0; 0; 1; 2; 3; 4; 5; 5; 5; 6; 7; 8; 9; 10; 11]
    - Input [edge_targets]: [1; 2; 3; 4; 5; 5; 6; 7; 8; 12; 9; 10; 11; 11; 12]
    - Output [output]: 2%Z
*)

(** ** Bridge *)

(** [@requirement excavator_spec] [@fold full correctness statement] On
    valid represented inputs, [excavator] returns a represented
    output satisfying [excavator_spec]. *)
Specification excavator_correct :
  forall (sites : string) (edge_sources edge_targets : list
    N)
         (sites_str : PrimString.string)
         (edge_sources_arr edge_targets_arr : array uint),
  valid_input sites edge_sources edge_targets ->
  repr sites_str sites ->
    repr edge_sources_arr edge_sources ->
  repr edge_targets_arr edge_targets ->
  exists output : Z,
    repr (excavator sites_str edge_sources_arr
      edge_targets_arr)
      output /\
    excavator_spec sites edge_sources edge_targets output.

(** ** Complexity *)

(** [@hide] [excavator_cost] is the cost translation of [excavator] (the judge
    recomputes it and compares) ... *)
Complexity excavator_cost for excavator.

(** [@fold complexity bound] ... and runs in at most c1 * (V + E + 1) + c2 steps of the cost model on a valid input, V the number of sites and E of passages (the topological sort and one relaxation sweep), for two constants
    quantified before the inputs, on every valid input. [@requirement excavator_time_spec] *)
Specification excavator_time : exists c1 c2 : nat,
  forall (sites : string) (edge_sources edge_targets : list
  N)
  (sites_str : PrimString.string)
  (edge_sources_arr edge_targets_arr : array uint),
  valid_input sites edge_sources edge_targets ->
  repr sites_str sites ->
  repr edge_sources_arr edge_sources ->
  repr edge_targets_arr edge_targets ->
  excavator_time_spec c1 c2 (size sites_str) (size edge_sources_arr) (cost3 excavator_cost sites_str edge_sources_arr edge_targets_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
