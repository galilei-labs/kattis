(* @function        chess_consistent
   @signature       uint -> array uint -> array bool -> array uint -> bool
   @math_signature  N -> list N -> list bool -> list N -> bool
   @summary         [chess_consistent n ks wins ls] reads m reported matches
                    between players 0..n-1, match j being "ks_j beat ls_j"
                    when wins_j is true and "ks_j drew with ls_j" when it is
                    false.  It returns true ("consistent") exactly when some
                    skill level per player explains every match, the more
                    skilled player always winning and a draw happening iff
                    the two skills are equal; false ("inconsistent")
                    otherwise.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The m match lines "K s L" are three parallel lists, one per
   column; the symbol s is a bool: true for '>', false for '='. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The j-th element of l (d beyond the end). *)
Definition at_ {A} (d : A) (l : list A) (j : N) : A := nth (N.to_nat j) l d.

(* Matches j1 and j2 are between the same two players, in either order. *)
Definition same_pair (ks ls : list N) (j1 j2 : N) : Prop :=
  (at_ 0 ks j1 = at_ 0 ks j2 /\ at_ 0 ls j1 = at_ 0 ls j2) \/
  (at_ 0 ks j1 = at_ 0 ls j2 /\ at_ 0 ls j1 = at_ 0 ks j2).

(* Skill levels s (one integer per player) explain match j: K beat L iff
   K is strictly more skilled, a draw iff the skills are equal. *)
Definition explains (s : N -> Z) (ks : list N) (wins : list bool)
    (ls : list N) (j : N) : Prop :=
  if at_ false wins j then Z.gt (s (at_ 0 ks j)) (s (at_ 0 ls j))
  else s (at_ 0 ks j) = s (at_ 0 ls j).

(* The list is consistent: some skill levels explain every reported match.
   Otherwise at least one match is necessarily falsely reported. *)
Definition consistent (ks : list N) (wins : list bool) (ls : list N) : Prop :=
  exists s : N -> Z, forall j, j < len ks -> explains s ks wins ls j.

Record valid_input (n : N) (ks : list N) (wins : list bool) (ls : list N)
  : Prop := {
  (* 2 <= N <= 50 000 *)
  vi_n : 2 <= n <= 50000;
  (* 1 <= M <= 250 000 *)
  vi_m : 1 <= len ks <= 250000;
  (* the following M lines each consist of an integer K, a symbol and
     another integer L *)
  vi_wins_len : len wins = len ks;
  vi_ls_len : len ls = len ks;
  (* 0 <= K, L < N *)
  vi_ks : Forall (fun k => k < n) ks;
  vi_ls : Forall (fun l => l < n) ls;
  (* there is at most one reported match between any given pair of players *)
  vi_one_match : forall j1 j2, j1 < len ks -> j2 < len ks ->
    same_pair ks ls j1 j2 -> j1 = j2;
  (* each player takes part in at least one reported match *)
  vi_every_player : forall p, p < n ->
    exists j, j < len ks /\ (at_ 0 ks j = p \/ at_ 0 ls j = p);
}.

(* The answer: true ("consistent") iff the list is consistent. *)
Definition chess_consistent_spec (n : N) (ks : list N) (wins : list bool)
    (ls : list N) (b : bool) : Prop :=
  b = true <-> consistent ks wins ls.

Program chess_consistent :
  uint -> array uint -> array bool -> array uint -> bool.

Specification chess_consistent_correct :
  forall (n : N) (ks : list N) (wins : list bool) (ls : list N)
         (xn : uint) (xks : array uint) (xwins : array bool)
         (xls : array uint),
  valid_input n ks wins ls ->
  repr xn n -> repr xks ks -> repr xwins wins -> repr xls ls ->
  exists b : bool, repr (chess_consistent xn xks xwins xls) b /\
                   chess_consistent_spec n ks wins ls b.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
