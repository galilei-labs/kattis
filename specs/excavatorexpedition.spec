(* @function        excavator
   @signature       PrimString.string -> array uint -> array uint -> sint
   @math_signature  String.string -> list N -> list N -> Z
   @summary         [excavator s src dst] takes the V sites of a directed
                    acyclic graph (s.[i] = 'X' for a construction site, '.'
                    for a boring one) and its E edges src.[k] -> dst.[k], and
                    returns the largest happiness of a route from location 0
                    to location V-1: the number of construction sites visited
                    minus the number of boring sites visited, the two ends not
                    counted. It may be negative.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Relations.
From Stdlib Require Import String Ascii.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Math side.  The site line is the string s, so V = slen s; the edge list is
   two parallel lists, the k-th edge going from src_k to dst_k. *)

(* The number of elements of l, and the number of characters of s. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).
Definition slen (s : string) : N := N.of_nat (String.length s).

(* One can drive from u to v: some line k of the edge list reads "u v". *)
Definition edge (src dst : list N) (u v : N) : Prop :=
  exists k, nth_error src k = Some u /\ nth_error dst k = Some v.

(* Every two consecutive locations of p are joined by an edge. *)
Fixpoint walk (src dst : list N) (p : list N) : Prop :=
  match p with
  | u :: ((v :: _) as rest) => edge src dst u v /\ walk src dst rest
  | _ => True
  end.

(* A route: a walk from Amka's home, location 0, to the grandparents' home,
   location V - 1, given as the list of the locations it visits. *)
Definition route (s : string) (src dst p : list N) : Prop :=
  walk src dst p /\ hd_error p = Some 0%N /\ last p 0%N = (slen s - 1)%N.

(* Location v is site c ('X' or '.') of the site line. *)
Definition is_site (s : string) (c : ascii) (v : N) : bool :=
  match String.get (N.to_nat v) s with
  | Some c' => Ascii.eqb c' c
  | None => false
  end.

(* The number of locations of p that are sites c, the two homes excepted. *)
Definition count_sites (s : string) (c : ascii) (p : list N) : Z :=
  Z.of_nat (List.length (filter (fun v =>
    andb (negb (orb (v =? 0)%N (v =? slen s - 1)%N)) (is_site s c v)) p)).

(* Nanouk's happiness on route p: construction sites minus boring sites. *)
Definition happiness (s : string) (p : list N) : Z :=
  count_sites s "X"%char p - count_sites s "."%char p.

(* The statement's bounds and guarantees. *)
Record valid_input (s : string) (src dst : list N) : Prop := {
  (* 1 < V <= 400 000 (V is the number of characters of the site line) *)
  vi_V : (2 <= slen s <= 400000)%N;
  (* 0 < E <= 400 000 *)
  vi_E : (1 <= len src <= 400000)%N;
  (* E lines, each with two integers F_i and T_i *)
  vi_lines : len dst = len src;
  (* 0 <= F_i, T_i < V *)
  vi_src : Forall (fun f => (f < slen s)%N) src;
  vi_dst : Forall (fun t => (t < slen s)%N) dst;
  (* for all 0 < i < V, V_i is '.' or 'X' *)
  vi_sites : forall i, (0 < i < slen s)%N ->
    is_site s "."%char i = true \/ is_site s "X"%char i = true;
  (* for i in {0, V - 1}, V_i = '.' *)
  vi_homes : is_site s "."%char 0 = true /\ is_site s "."%char (slen s - 1) = true;
  (* there is always a path from Amka's house to Nanouk's grandparents *)
  vi_path : exists p, route s src dst p;
  (* there are no cycles in the graph *)
  vi_acyclic : forall u, ~ clos_trans N (edge src dst) u u;
}.

(* The answer is the happiness of some route, and no route does better. *)
Definition excavator_spec (s : string) (src dst : list N) (h : Z) : Prop :=
  (exists p, route s src dst p /\ happiness s p = h) /\
  (forall p, route s src dst p -> happiness s p <= h).

(* sint: the happiness may be negative *)
Program excavator : PrimString.string -> array uint -> array uint -> sint.

Specification excavator_correct :
  forall (s : string) (src dst : list N)
         (xs : PrimString.string) (xsrc xdst : array uint),
  valid_input s src dst -> repr xs s -> repr xsrc src -> repr xdst dst ->
  exists h : Z, repr (excavator xs xsrc xdst) h /\ excavator_spec s src dst h.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
