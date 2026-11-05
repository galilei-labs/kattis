(* @function        securitybadge
   @signature       uint -> uint -> uint -> uint -> array uint ->
                    array uint -> array uint -> array uint -> uint
   @math_signature  N -> N -> N -> N -> list N -> list N -> list N ->
                    list N -> N
   @summary         [securitybadge n b s d la lb lx ly] counts the badge
                    numbers k in 1 .. b that can get from room s to room d,
                    the rooms being 1 .. n and lock i a one-way door from
                    room la_i to room lb_i that lets through the badges
                    lx_i .. ly_i (inclusive).  A badge gets from s to d when
                    some sequence of locks it passes leads from s to d.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Relations.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* The locks are the L input lines [a b x y], as four parallel lists:
   la (from), lb (to), lx (lowest badge), ly (highest badge). *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The i-th element of l, 0-based. *)
Definition get (l : list N) (i : N) : N := nth (N.to_nat i) l 0.

(* Badge k passes from room u to room w through a single lock. *)
Definition step (la lb lx ly : list N) (k u w : N) : Prop :=
  exists i, i < len la /\ get la i = u /\ get lb i = w /\
            get lx i <= k <= get ly i.

(* Badge k gets from room u to room w: zero or more steps. *)
Definition walks (la lb lx ly : list N) (k u w : N) : Prop :=
  clos_refl_trans N (step la lb lx ly k) u w.

(* Badge k is in 1 .. b and gets from s to d. *)
Definition good (b s d : N) (la lb lx ly : list N) (k : N) : Prop :=
  1 <= k <= b /\ walks la lb lx ly k s d.

Record valid_input (n b s d : N) (la lb lx ly : list N) : Prop := {
  (* L lines, each describing a lock as four integers a b x y *)
  vi_lb_len : len lb = len la;
  vi_lx_len : len lx = len la;
  vi_ly_len : len ly = len la;
  (* 2 <= N <= 1 000 *)
  vi_n : 2 <= n <= 1000;
  (* 1 <= L <= 5 000 *)
  vi_l : 1 <= len la <= 5000;
  (* 1 <= B <= 10^9 *)
  vi_b : 1 <= b <= 10 ^ 9;
  (* 1 <= S <= N, 1 <= D <= N, S <> D *)
  vi_s : 1 <= s <= n;
  vi_d : 1 <= d <= n;
  vi_sd : s <> d;
  (* 1 <= a, b <= N, a <> b, 1 <= x <= B, 1 <= y <= B, x <= y *)
  vi_lock : forall i, i < len la ->
    1 <= get la i <= n /\ 1 <= get lb i <= n /\ get la i <> get lb i /\
    1 <= get lx i <= b /\ 1 <= get ly i <= b /\ get lx i <= get ly i;
  (* no (a, b) pair will occur more than once *)
  vi_pairs : forall i j, i < len la -> j < len la ->
    get la i = get la j -> get lb i = get lb j -> i = j;
}.

(* The answer is the number of good badges: o is the length of a
   duplicate-free list holding exactly the good badges. *)
Definition securitybadge_spec (n b s d : N) (la lb lx ly : list N) (o : N)
    : Prop :=
  exists ks : list N,
    NoDup ks /\ (forall k, In k ks <-> good b s d la lb lx ly k) /\
    o = len ks.

Program securitybadge : uint -> uint -> uint -> uint -> array uint ->
  array uint -> array uint -> array uint -> uint.

Specification securitybadge_correct :
  forall (n b s d : N) (la lb lx ly : list N)
         (xn xb xs xd : uint) (xla xlb xlx xly : array uint),
  valid_input n b s d la lb lx ly ->
  repr xn n -> repr xb b -> repr xs s -> repr xd d ->
  repr xla la -> repr xlb lb -> repr xlx lx -> repr xly ly ->
  exists o : N, repr (securitybadge xn xb xs xd xla xlb xlx xly) o /\
    securitybadge_spec n b s d la lb lx ly o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
