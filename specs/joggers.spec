(* @function        joggers
   @signature       uint -> uint -> array uint -> array uint -> array uint ->
                    array uint -> uint
   @math_signature  N -> N -> list N -> list N -> list N -> list N -> N
   @summary         [joggers n s a b d l]: the woods have intersections 1..n,
                    the campus is 1, trail j joins a_j and b_j and is d_j
                    metres long, and lamps already stand at the intersections
                    listed in l. A jogger runs exactly s metres from the
                    campus back to the campus, turning around anywhere, even
                    inside a trail. The result is the least number of new
                    lamps, placed at intersections, such that every trail some
                    jogger may run on has a lamp at one of its two ends.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The trails are the parallel lists a, b, d (one entry per
   input line "a b d"); trail j is entry j, counted from 0. *)

Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* Entry k of l, counted from 0. *)
Definition get (l : list N) (k : N) : N := nth (N.to_nat k) l 0.

Definition rN (x : N) : R := IZR (Z.of_N x).

(* [v] is an intersection, 1..n. *)
Definition inter (n v : N) : Prop := 1 <= v <= n.

(* Following the trails [js] in order leads from [u] to [v]. *)
Fixpoint chain (a b : list N) (u : N) (js : list N) (v : N) : Prop :=
  match js with
  | [] => u = v
  | j :: js' => j < len a /\
      ((get a j = u /\ chain a b (get b j) js' v) \/
       (get b j = u /\ chain a b (get a j) js' v))
  end.

(* A route from [u] to [v]: adjacent trails, none used twice. *)
Definition route (a b : list N) (u : N) (js : list N) (v : N) : Prop :=
  chain a b u js v /\ NoDup js.

(* A place in the woods: trail j, x metres from its end a_j. *)
Definition place : Type := (N * R)%type.

Definition in_woods (d : list N) (p : place) : Prop :=
  fst p < len d /\ (0 <= snd p <= rN (get d (fst p)))%R.

(* The place [p] is the intersection [v]. *)
Definition at_inter (a b d : list N) (p : place) (v : N) : Prop :=
  (snd p = 0%R /\ get a (fst p) = v) \/
  (snd p = rN (get d (fst p)) /\ get b (fst p) = v).

(* One leg of a run goes straight along one trail, or switches trails at an
   intersection; its length is the distance covered on the trail. *)
Definition leg_ok (a b d : list N) (p q : place) : Prop :=
  fst p = fst q \/ exists v, at_inter a b d p v /\ at_inter a b d q v.

Definition leg_len (p q : place) : R :=
  if fst p =? fst q then Rabs (snd p - snd q) else 0%R.

Fixpoint legs_ok (a b d : list N) (p : place) (ps : list place) : Prop :=
  match ps with
  | [] => True
  | q :: ps' => leg_ok a b d p q /\ legs_ok a b d q ps'
  end.

Fixpoint run_len (p : place) (ps : list place) : R :=
  match ps with
  | [] => 0%R
  | q :: ps' => (leg_len p q + run_len q ps')%R
  end.

(* A jogger's run: from [p] through the turning points [ps], starting and
   finishing at the campus, exactly [s] metres long. *)
Definition jog (a b d : list N) (s : N) (p : place) (ps : list place) : Prop :=
  Forall (in_woods d) (p :: ps) /\
  at_inter a b d p 1 /\ at_inter a b d (last ps p) 1 /\
  legs_ok a b d p ps /\ run_len p ps = rN s.

(* Some leg of the run covers a stretch of trail [j]. *)
Fixpoint runs_on (j : N) (p : place) (ps : list place) : Prop :=
  match ps with
  | [] => False
  | q :: ps' => (fst p = j /\ fst q = j /\ snd p <> snd q) \/ runs_on j q ps'
  end.

(* Trail [j] may be used by some jogger. *)
Definition used (a b d : list N) (s j : N) : Prop :=
  exists p ps, jog a b d s p ps /\ runs_on j p ps.

(* New lamps: distinct intersections. *)
Definition placement (n : N) (xs : list N) : Prop :=
  NoDup xs /\ Forall (inter n) xs.

Definition lit (l xs : list N) (v : N) : Prop := In v l \/ In v xs.

(* Every trail a jogger may use has a lamp at one of its ends. *)
Definition safe (s : N) (a b d l xs : list N) : Prop :=
  forall j, j < len a -> used a b d s j ->
    lit l xs (get a j) \/ lit l xs (get b j).

Record valid_input (n s : N) (a b d l : list N) : Prop := {
  (* 2 <= N <= 50 000 *)
  vi_n : 2 <= n <= 50000;
  (* 1 <= S <= 10^4 *)
  vi_s : 1 <= s <= 10 ^ 4;
  (* then follow N - 1 lines with three integers a b d *)
  vi_trails : len a = n - 1 /\ len b = len a /\ len d = len a;
  (* 1 <= a <= N, 1 <= b <= N *)
  vi_a : Forall (inter n) a;
  vi_b : Forall (inter n) b;
  (* 1 <= d <= 100 *)
  vi_d : Forall (fun x => 1 <= x <= 100) d;
  (* there is exactly one route between each pair of intersections *)
  vi_route : forall u v, inter n u -> inter n v -> exists js, route a b u js v;
  vi_route_unique : forall u v js ks,
    route a b u js v -> route a b u ks v -> js = ks;
  (* 0 <= L <= N *)
  vi_L : len l <= n;
  (* L distinct integers, lamps at intersections l_1 .. l_L *)
  vi_l : Forall (inter n) l;
  vi_l_distinct : NoDup l;
}.

(* The least number of new lamps that makes every usable trail safe. *)
Definition joggers_spec (n s : N) (a b d l : list N) (o : N) : Prop :=
  (exists xs, placement n xs /\ safe s a b d l xs /\ len xs = o) /\
  (forall xs, placement n xs -> safe s a b d l xs -> o <= len xs).

Program joggers : uint -> uint -> array uint -> array uint ->
  array uint -> array uint -> uint.

Specification joggers_correct :
  forall (n s : N) (a b d l : list N) (xn xs : uint)
         (xa xb xd xl : array uint),
  valid_input n s a b d l ->
  repr xn n -> repr xs s -> repr xa a -> repr xb b -> repr xd d ->
  repr xl l ->
  exists o : N, repr (joggers xn xs xa xb xd xl) o /\
    joggers_spec n s a b d l o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.

(* The four classical axioms Stdlib's reals rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec ClassicalDedekindReals.sig_not_dec Classical_Prop.classic FunctionalExtensionality.functional_extensionality_dep.
