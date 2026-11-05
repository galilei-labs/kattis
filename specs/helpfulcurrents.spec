(* @function        helpfulcurrents
   @signature       uint -> uint -> uint -> array PrimString.string -> option uint
   @math_signature  N -> N -> N -> list String.string -> option N
   @summary         [helpfulcurrents Y X xinit map] counts the distinct routes
                    of the ship from column xinit of the bottom row of the map
                    to the castle '@', a route being a sequence of moves, each
                    either north onto a cell that is not '#' or along the
                    current ('>' east, '<' west) of the cell the ship is on.
                    It returns [Some (count mod 1000003)] when at least one
                    route exists and [None] ("begin repairs") when none does.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray String Ascii.
From Stdlib Require PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The map is the list of its Y rows, row 0 the northernmost
   (the first line of the input), the ship starting on row Y - 1. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The character in column x of row y ('#' outside the map). *)
Definition cell (map : list string) (y x : N) : ascii :=
  match String.get (N.to_nat x) (nth (N.to_nat y) map EmptyString) with
  | Some c => c
  | None => "#"%char
  end.

Definition in_map (Y X y x : N) : Prop := y < Y /\ x < X.

(* The two moves of the statement: north (lowering the sails), or along
   the current of the cell the ship is on (retracting them). *)
Inductive move := North | Current.

(* One move from (y, x): none from the castle, where the route ends; north
   onto row y - 1 unless the ship is on row 0 or that cell is '#'; along
   the current, east on '>' and west on '<', none on any other cell. *)
Definition step (map : list string) (p : N * N) (mv : move) : option (N * N) :=
  let '(y, x) := p in
  let c := cell map y x in
  if Ascii.eqb c "@"%char then None
  else match mv with
  | North =>
      if orb (y =? 0) (Ascii.eqb (cell map (y - 1) x) "#"%char) then None
      else Some (y - 1, x)
  | Current =>
      if Ascii.eqb c ">"%char then Some (y, x + 1)
      else if Ascii.eqb c "<"%char then Some (y, x - 1)
      else None
  end.

(* The cell reached from p by the moves of r, if every move is possible. *)
Fixpoint run (map : list string) (p : N * N) (r : list move) : option (N * N) :=
  match r with
  | [] => Some p
  | mv :: r' =>
      match step map p mv with
      | None => None
      | Some q => run map q r'
      end
  end.

(* r takes the ship from column xinit of the bottom row to the castle. *)
Definition is_route (Y xinit : N) (map : list string) (r : list move) : Prop :=
  exists q, run map (Y - 1, xinit) r = Some q /\
            cell map (fst q) (snd q) = "@"%char.

(* There are exactly n routes. *)
Definition route_count (Y xinit : N) (map : list string) (n : N) : Prop :=
  exists rs, NoDup rs /\ len rs = n /\
             forall r, In r rs <-> is_route Y xinit map r.

(* The statement's bounds and guarantees. *)
Record valid_input (Y X xinit : N) (map : list string) : Prop := {
  (* 0 < Y <= 300 *)
  vi_Y : 0 < Y <= 300;
  (* 0 <= x_init < X <= 50 000 *)
  vi_X : xinit < X <= 50000;
  (* Then follow Y rows, each with X characters each *)
  vi_rows : len map = Y;
  vi_cols : Forall (fun row => N.of_nat (String.length row) = X) map;
  (* All characters C_{x,y} is one of '~', '#', '@', '>' and '<' *)
  vi_chars : forall y x, in_map Y X y x ->
    In (cell map y x) ["~"%char; "#"%char; "@"%char; ">"%char; "<"%char];
  (* If C_{x,y} = '>', then x+1 < X and C_{x+1,y} is not '<' nor '#' *)
  vi_east : forall y x, in_map Y X y x -> cell map y x = ">"%char ->
    x + 1 < X /\ cell map y (x + 1) <> "<"%char /\ cell map y (x + 1) <> "#"%char;
  (* If C_{x,y} = '<', then 0 <= x-1 and C_{x-1,y} is not '>' nor '#' *)
  vi_west : forall y x, in_map Y X y x -> cell map y x = "<"%char ->
    1 <= x /\ cell map y (x - 1) <> ">"%char /\ cell map y (x - 1) <> "#"%char;
  (* There is exactly one '@' tile on the map *)
  vi_castle : exists y0 x0, in_map Y X y0 x0 /\ cell map y0 x0 = "@"%char /\
    forall y x, in_map Y X y x -> cell map y x = "@"%char -> y = y0 /\ x = x0;
  (* The boat will not start on a '#' tile *)
  vi_start : cell map (Y - 1) xinit <> "#"%char;
}.

(* None is "begin repairs": there is no route.  Some k: there are n > 0
   routes, and k is n modulo 1 000 003. *)
Definition helpfulcurrents_spec (Y X xinit : N) (map : list string)
    (o : option N) : Prop :=
  match o with
  | None => forall r, ~ is_route Y xinit map r
  | Some k => exists n, 0 < n /\ route_count Y xinit map n /\ k = n mod 1000003
  end.

Program helpfulcurrents :
  uint -> uint -> uint -> array PrimString.string -> option uint.

Specification helpfulcurrents_correct :
  forall (Y X xinit : N) (map : list string)
         (y x xi : uint) (m : array PrimString.string),
  valid_input Y X xinit map ->
  repr y Y -> repr x X -> repr xi xinit -> repr m map ->
  exists o : option N,
    repr (helpfulcurrents y x xi m) o /\ helpfulcurrents_spec Y X xinit map o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
