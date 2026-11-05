(* @function        slowleak
   @signature       uint -> uint -> array uint -> array uint -> array uint ->
                    array uint -> option uint
   @math_signature  N -> N -> list N -> list N -> list N -> list N -> option N
   @summary         [slowleak n d st ri rj rk] is the length of the shortest
                    trip from intersection 1 (school) to intersection n (home)
                    along the roads ri.[e] -- rj.[e] of length rk.[e], ridden
                    in either direction, in which the distance ridden since the
                    last refill never exceeds d; the tire is refilled at the
                    school and at the repair stations st.  None ("stuck") when
                    no such trip exists.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  Intersections are numbered 1 to n as in the statement; the
   roads are the parallel lists ri, rj, rk (the m lines "i j k"). *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The e-th element of l, e counted from 0. *)
Definition get (l : list N) (e : N) : N := nth (N.to_nat e) l 0.

(* Some road joins u and v with length k, travelled in either direction. *)
Definition road (ri rj rk : list N) (u v k : N) : Prop :=
  exists e, e < len ri /\ get rk e = k /\
    ((get ri e = u /\ get rj e = v) \/ (get ri e = v /\ get rj e = u)).

(* [walk u v L]: a walk along roads from u to v of total length L. *)
Inductive walk (ri rj rk : list N) : N -> N -> N -> Prop :=
  | walk_nil : forall u, walk ri rj rk u u 0
  | walk_cons : forall u v w k L,
      road ri rj rk u v k -> walk ri rj rk v w L -> walk ri rj rk u w (k + L).

(* The tire can be refilled at v: the school or a repair station. *)
Definition refill (st : list N) (v : N) : Prop := v = 1 \/ In v st.

(* [trip u L]: leaving u with a full tire, home (n) is reached after a total
   length L, each stretch between two refills, or from the last refill to
   home, being at most d (arriving exactly as the tire goes flat is fine). *)
Inductive trip (n d : N) (st ri rj rk : list N) : N -> N -> Prop :=
  | trip_home : forall u L,
      walk ri rj rk u n L -> L <= d -> trip n d st ri rj rk u L
  | trip_refill : forall u v L L',
      walk ri rj rk u v L -> L <= d -> refill st v ->
      trip n d st ri rj rk v L' -> trip n d st ri rj rk u (L + L').

(* D is the length of a trip from the school, and no such trip is shorter. *)
Definition shortest (n d : N) (st ri rj rk : list N) (D : N) : Prop :=
  trip n d st ri rj rk 1 D /\ forall L, trip n d st ri rj rk 1 L -> D <= L.

(* The statement's bounds. *)
Record valid_input (n d : N) (st ri rj rk : list N) : Prop := {
  (* 2 <= n <= 500 *)
  vi_n : 2 <= n <= 500;
  (* 0 < m <= n(n-1)/2 *)
  vi_m : 0 < len ri <= n * (n - 1) / 2;
  (* the next m lines each hold three integers i, j, k *)
  vi_rj : len rj = len ri;
  vi_rk : len rk = len ri;
  (* 0 < t < n *)
  vi_t : 0 < len st < n;
  (* 0 < d < 2^31 *)
  vi_d : 0 < d < 2 ^ 31;
  (* the t stations have values between 2 and n-1, inclusive *)
  vi_st : Forall (fun s => 2 <= s <= n - 1) st;
  (* all integers on this line are unique *)
  vi_st_unique : NoDup st;
  (* 1 <= i < j <= n *)
  vi_ij : Forall2 (fun i j => 1 <= i /\ i < j <= n) ri rj;
  (* 0 < k < 2^31 *)
  vi_k : Forall (fun k => 0 < k < 2 ^ 31) rk;
  (* there is at most one road between any two intersections *)
  vi_simple : NoDup (combine ri rj);
  (* if the trip is possible, the minimum distance D satisfies 0 < D < 2^31 *)
  vi_answer : forall D, shortest n d st ri rj rk D -> 0 < D < 2 ^ 31;
}.

(* Some D for the length of a shortest trip; None ("stuck") when no trip
   exists. *)
Definition slowleak_spec (n d : N) (st ri rj rk : list N) (o : option N)
    : Prop :=
  match o with
  | Some D => shortest n d st ri rj rk D
  | None => forall L, ~ trip n d st ri rj rk 1 L
  end.

Program slowleak :
  uint -> uint -> array uint -> array uint -> array uint -> array uint ->
  option uint.

Specification slowleak_correct :
  forall (n d : N) (st ri rj rk : list N)
         (x y : uint) (xs xi xj xk : array uint),
  valid_input n d st ri rj rk ->
  repr x n -> repr y d -> repr xs st ->
  repr xi ri -> repr xj rj -> repr xk rk ->
  exists o : option N,
    repr (slowleak x y xs xi xj xk) o /\ slowleak_spec n d st ri rj rk o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
