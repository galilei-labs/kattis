(* @function        kingpin_escape
   @signature       uint -> uint -> array uint -> array uint -> array uint * array uint
   @math_signature  N -> N -> list N -> list N -> list N * list N
   @summary         [kingpin_escape n h ea eb] takes a tree on hideouts
                    0..n-1, given as its n-1 passageways (ea_k, eb_k), and the
                    headquarters h.  It returns new passageways, as two
                    parallel lists, such that after adding them every hideout
                    still reaches h when any one passageway is blocked, and no
                    smaller set of new passageways does so.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A hideout is an N; a set of passageways is a list of pairs,
   one entry per passageway (a passageway may be listed twice). *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The passageways given by two parallel lists (the input's two columns,
   or the output's): the pairs (xs_k, ys_k). *)
Definition passageways (xs ys : list N) : list (N * N) := combine xs ys.

(* A passageway of E joins x and y (in either direction). *)
Definition joined (E : list (N * N)) (x y : N) : Prop :=
  In (x, y) E \/ In (y, x) E.

(* Each hideout of l is joined to the next one by a passageway of E. *)
Fixpoint linked (E : list (N * N)) (l : list N) : Prop :=
  match l with
  | x :: ((y :: _) as t) => joined E x y /\ linked E t
  | _ => True
  end.

(* A route from u to v: hideouts, none visited twice, from u to v, each
   joined to the next by a passageway of E. *)
Definition route (E : list (N * N)) (u v : N) (l : list N) : Prop :=
  NoDup l /\ linked E l /\ hd_error l = Some u /\ hd_error (rev l) = Some v.

Definition reaches (E : list (N * N)) (u v : N) : Prop :=
  exists l, route E u v l.

(* From every hideout to every other hideout there is precisely one route. *)
Definition is_tree (n : N) (E : list (N * N)) : Prop :=
  forall x y, x < n -> y < n -> exists! l, route E x y l.

(* E with its k-th passageway blocked. *)
Definition block (E : list (N * N)) (k : nat) : list (N * N) :=
  firstn k E ++ skipn (S k) E.

(* Whenever at most one passageway of E is blocked, every hideout still
   reaches the headquarters h. *)
Definition safe (n h : N) (E : list (N * N)) : Prop :=
  (forall x, x < n -> reaches E x h) /\
  (forall k x, (k < List.length E)%nat -> x < n -> reaches (block E k) x h).

(* Both ends of every passageway of F are hideouts. *)
Definition in_range (n : N) (F : list (N * N)) : Prop :=
  forall a b, In (a, b) F -> a < n /\ b < n.

Record valid_input (n h : N) (ea eb : list N) : Prop := {
  (* 2 <= n <= 10^5, the number of hideouts *)
  vi_n : 2 <= n <= 10 ^ 5;
  (* 0 <= h < n, the location of your headquarters *)
  vi_h : h < n;
  (* then follow n - 1 lines, each with two integers a, b *)
  vi_ea_len : len ea = n - 1;
  vi_eb_len : len eb = n - 1;
  (* 0 <= a, b < n *)
  vi_ea : Forall (fun a => a < n) ea;
  vi_eb : Forall (fun b => b < n) eb;
  (* from every hideout to every other hideout there is precisely one route
     through the network *)
  vi_tree : is_tree n (passageways ea eb);
}.

(* The answer (xs, ys): the passageways (xs_k, ys_k) between hideouts make
   the network safe once added, and no set of passageways between hideouts
   that does so is smaller.  Any such answer is accepted. *)
Definition kingpin_escape_spec (n h : N) (ea eb : list N) (o : list N * list N)
  : Prop :=
  let '(xs, ys) := o in
  len xs = len ys /\
  in_range n (passageways xs ys) /\
  safe n h (passageways ea eb ++ passageways xs ys) /\
  (forall F, in_range n F -> safe n h (passageways ea eb ++ F) ->
     len xs <= len F).

Program kingpin_escape :
  uint -> uint -> array uint -> array uint -> array uint * array uint.

Specification kingpin_escape_correct :
  forall (n h : N) (ea eb : list N) (n' h' : uint) (ea' eb' : array uint),
  valid_input n h ea eb ->
  repr n' n -> repr h' h -> repr ea' ea -> repr eb' eb ->
  exists o : list N * list N,
    repr (kingpin_escape n' h' ea' eb') o /\ kingpin_escape_spec n h ea eb o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
