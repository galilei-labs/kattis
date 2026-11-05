(* @function        gcpc
   @signature       uint -> array uint -> array uint -> array uint
   @math_signature  N -> list N -> list N -> list N
   @summary         [gcpc n t p] replays the events "team t_j solved a
                    problem with penalty p_j", in order, for teams 1..n that
                    all start at score (0, 0), and returns, for each i, the
                    rank of team 1 after the first i events: one plus the
                    number of teams with more solved problems, or as many
                    and a smaller total penalty.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The m events are the parallel lists t (the teams) and p (the
   penalties), the j-th event being (t_j, p_j), as in the input's m lines. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The number of problems team k has solved during the events (t, p). *)
Definition solved (k : N) (t : list N) : N :=
  len (filter (fun tj => tj =? k) t).

(* The total penalty of team k: the sum of the penalties of its events. *)
Definition penalty (k : N) (t p : list N) : N :=
  fold_right N.add 0 (map (fun '(tj, pj) => if tj =? k then pj else 0)
                          (combine t p)).

(* The score of team k after the events (t, p): (solved, penalty). *)
Definition score (k : N) (t p : list N) : N * N := (solved k t, penalty k t p).

(* Score (a1, b1) is better than (a2, b2): a1 > a2, or a1 = a2 and b1 < b2. *)
Definition better (s1 s2 : N * N) : bool :=
  let '(a1, b1) := s1 in let '(a2, b2) := s2 in
  (a2 <? a1) || ((a1 =? a2) && (b1 <? b2)).

(* The teams 1, 2, ..., n. *)
Definition teams (n : N) : list N := map N.of_nat (seq 1 (N.to_nat n)).

(* The rank of team 1 after the events (t, p): k + 1, k the number of teams
   whose score is better. *)
Definition rank (n : N) (t p : list N) : N :=
  1 + len (filter (fun k => better (score k t p) (score 1 t p)) (teams n)).

Record valid_input (n : N) (t p : list N) : Prop := {
  (* 1 <= n <= 10^5 is the number of teams *)
  vi_n : 1 <= n <= 10 ^ 5;
  (* 1 <= m <= 10^5 is the number of events *)
  vi_m : 1 <= len t <= 10 ^ 5;
  (* each event line contains two integers t and p *)
  vi_p_len : len p = len t;
  (* 1 <= t <= n *)
  vi_t : Forall (fun tj => 1 <= tj <= n) t;
  (* 1 <= p <= 1000 *)
  vi_p : Forall (fun pj => 1 <= pj <= 1000) p;
}.

(* Output m lines: the i-th is the rank of team 1 after the first i events. *)
Definition gcpc_spec (n : N) (t p : list N) (o : list N) : Prop :=
  len o = len t /\
  forall i : nat, (i < List.length t)%nat ->
    nth i o 0 = rank n (firstn (S i) t) (firstn (S i) p).

Program gcpc : uint -> array uint -> array uint -> array uint.

Specification gcpc_correct :
  forall (n : N) (t p : list N) (xn : uint) (xt xp : array uint),
  valid_input n t p -> repr xn n -> repr xt t -> repr xp p ->
  exists o : list N, repr (gcpc xn xt xp) o /\ gcpc_spec n t p o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
