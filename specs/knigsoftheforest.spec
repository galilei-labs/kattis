(* @function        knigsoftheforest
   @signature       uint -> uint -> uint -> uint -> array uint -> array uint
                    -> option uint
   @math_signature  N -> N -> N -> N -> list N -> list N -> option N
   @summary         [knigsoftheforest k n y p ys ps]: Karl-Algtav enters the
                    tournament in year y with strength p, the other moose in
                    years ys with strengths ps (parallel lists).  Every year
                    from 2011 on, the strongest moose that has entered and not
                    yet won wins and leaves.  The result is Some Y when Karl
                    wins in year Y, one of the n years 2011 .. 2011 + n - 1
                    the data cover, and None ("unknown") otherwise.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The moose are numbered: moose 0 is Karl-Algtav, moose i + 1
   the i-th of the other moose, so their years are y :: ys and their
   strengths p :: ps. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The entry of moose c in the column l. *)
Definition entry (l : list N) (c : N) : N := nth (N.to_nat c) l 0.

(* Year Y is one of the n years for which the data are sufficient. *)
Definition data_year (n Y : N) : Prop := 2011 <= Y <= 2011 + n - 1.

(* Given the winners w of the earlier years, moose c competes in year Y: it
   exists, has entered by Y, and has not won in any year 2011 .. Y - 1. *)
Definition contender (yrs : list N) (w : N -> N) (Y c : N) : Prop :=
  c < len yrs /\ entry yrs c <= Y /\
  forall Y', 2011 <= Y' < Y -> w Y' <> c.

(* w gives the winner of every data year: a contender of that year, at
   least as strong as every contender of that year. *)
Definition schedule (n : N) (yrs strs : list N) (w : N -> N) : Prop :=
  forall Y, data_year n Y ->
    contender yrs w Y (w Y) /\
    forall c, contender yrs w Y c -> entry strs c <= entry strs (w Y).

(* The statement's bounds and guarantees. *)
Record valid_input (k n y p : N) (ys ps : list N) : Prop := {
  (* 1 <= k <= 10^5, the size of the tournament pool *)
  vi_k : 1 <= k <= 10 ^ 5;
  (* 1 <= n <= 10^5, the number of years with sufficient information *)
  vi_n : 1 <= n <= 10 ^ 5;
  (* Karl-Algtav: 2011 <= y <= 2011 + n - 1 *)
  vi_y : 2011 <= y <= 2011 + n - 1;
  (* Karl-Algtav: 0 <= p <= 2^31 - 1 *)
  vi_p : p <= 2 ^ 31 - 1;
  (* then follow n + k - 2 lines describing each of the other moose *)
  vi_ys_len : len ys = n + k - 2;
  vi_ps_len : len ps = n + k - 2;
  (* in the same format as for Karl-Algtav *)
  vi_ys : Forall (fun z => 2011 <= z <= 2011 + n - 1) ys;
  vi_ps : Forall (fun q => q <= 2 ^ 31 - 1) ps;
  (* exactly k of the moose will have 2011 as their year of entry *)
  vi_pool : len (filter (N.eqb 2011) (y :: ys)) = k;
  (* the remaining n - 1 moose will have unique years of entry *)
  vi_newcomers : NoDup (filter (fun z => negb (z =? 2011)) (y :: ys));
  (* the strength of each moose is unique *)
  vi_strengths : NoDup (p :: ps);
}.

(* The winners are determined, and the answer is Some Y exactly when Y is a
   data year in which Karl (moose 0) wins; None when he wins in none. *)
Definition knigsoftheforest_spec (k n y p : N) (ys ps : list N)
    (o : option N) : Prop :=
  (exists w, schedule n (y :: ys) (p :: ps) w) /\
  forall w, schedule n (y :: ys) (p :: ps) w ->
    forall Y, o = Some Y <-> data_year n Y /\ w Y = 0.

Program knigsoftheforest :
  uint -> uint -> uint -> uint -> array uint -> array uint -> option uint.

Specification knigsoftheforest_correct :
  forall (k n y p : N) (ys ps : list N)
         (kx nx yx px : uint) (ysx psx : array uint),
  valid_input k n y p ys ps ->
  repr kx k -> repr nx n -> repr yx y -> repr px p ->
  repr ysx ys -> repr psx ps ->
  exists o : option N,
    repr (knigsoftheforest kx nx yx px ysx psx) o /\
    knigsoftheforest_spec k n y p ys ps o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
