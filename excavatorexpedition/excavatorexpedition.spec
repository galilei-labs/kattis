(** * Excavator Expedition *)

(** ** Description *)

(** Find a maximum-score path from the first vertex to the last in a
    directed acyclic graph. Each internal vertex contributes either +1 or
    -1; the endpoints contribute zero.

    [@kattis excavatorexpedition]
    - Difficulty: 4.1
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 2 to 400000 vertices; 1 to 400000 edges.
    - The graph is acyclic and contains a path from the first vertex to the
      last. *)

(** ** Examples *)

(** Kattis text input and output. *)
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
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  Relations.
From Stdlib Require Import String Ascii.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** Math side. The site line is the string sites, so V = slen sites; the
    edge list is two parallel lists, the k-th edge going from
    edge_sources_k to edge_targets_k. The number of elements of l,
    and the number of characters of text. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).
(** The [slen] definition. *)
Definition slen (text : string) : N :=
  N.of_nat (String.length text).

(** One can drive from origin to destination: some line k of the edge
    list reads "origin destination". *)
Definition edge (edge_sources edge_targets : list N)
  (origin destination : N)
    : Prop :=
  exists k, nth_error edge_sources k = Some origin /\
            nth_error edge_targets k = Some destination.

(** Every two consecutive locations of locations are joined by an edge. *)
Fixpoint walk (edge_sources edge_targets : list N)
  (locations : list N)
    : Prop :=
  match locations with
  | here :: ((next :: _) as rest) =>
      edge edge_sources edge_targets here next /\
      walk edge_sources edge_targets rest
  | _ => True
  end.

(** A route: a walk from Amka's home, location 0, to the grandparents'
    home, location V - 1, given as the list of the locations it
    visits. *)
Definition route (sites : string)
  (edge_sources edge_targets locations
    : list N) : Prop :=
  walk edge_sources edge_targets locations /\
  hd_error locations = Some 0%N /\
  last locations 0%N = (slen sites - 1)%N.

(** Location location is site kind ('X' or '.') of the site line. *)
Definition is_site (sites : string) (kind : ascii)
  (location : N) : bool :=
  match String.get (N.to_nat location) sites with
  | Some found => Ascii.eqb found kind
  | None => false
  end.

(** The number of locations of locations that are sites kind, the two
    homes excepted. *)
Definition count_sites (sites : string) (kind : ascii)
  (locations : list N)
    : Z :=
  Z.of_nat (List.length (filter (fun location =>
    andb (negb (orb (location =? 0)%N (location =? slen
      sites - 1)%N))
         (is_site sites kind location)) locations)).

(** Nanouk's happiness on the route locations: construction sites minus
    boring sites. *)
Definition happiness (sites : string)
  (locations : list N) : Z :=
  count_sites sites "X"%char locations - count_sites sites
    "."%char locations.

(** [@inside excavator_correct] The statement's bounds and guarantees. *)
Record valid_input (sites : string)
  (edge_sources edge_targets : list N)
    : Prop := {
  (* 1 < V <= 400 000 (V is the number of characters of
     the site line) *)
  vi_V : (2 <= slen sites <= 400000)%N;
  (* 0 < E <= 400 000 *)
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

(** [@requirement] [@short The answer is the happiness of some route,
    and no route does better.] The answer is the happiness of some
    route, and no route does better. *)
Definition excavator_spec (sites : string)
  (edge_sources edge_targets
    : list N) (output : Z) : Prop :=
  (exists locations, route sites edge_sources edge_targets
    locations /\
     happiness sites locations = output) /\
  (forall locations, route sites edge_sources edge_targets
    locations ->
     happiness sites locations <= output).

(** ** Interface *)

(** The [excavator] program on machine values.
    - Input [sites]:
    - Input [edge_sources]:
    - Input [edge_targets]:
    - Output [output]: *)
Program excavator : PrimString.string -> array uint -> array
  uint -> sint.

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

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
