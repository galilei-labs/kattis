(* @function        vedurspa
   @signature       array (option float) -> array (option uint) ->
                    array (option float) -> array (option uint) -> uint ->
                    array (option float) * array (option uint) *
                    array (option float) * array (option uint)
   @math_signature  list (option R) -> list (option N) -> list (option R) ->
                    list (option N) -> N ->
                    list (option R) * list (option N) * list (option R) *
                    list (option N)
   @summary         [vedurspa t d s h m] takes the four columns of the n
                    hourly measurements (temperature, wind direction, wind
                    speed, humidity; None is a missing value "-") and
                    predicts hours n .. n+m-1 of each column by its
                    least-squares line in the hour index, clamped to the
                    column's range: within 10^-6 for temperature and speed,
                    a nearest integer (within 1/2 + 10^-6) for direction and
                    humidity.  A column with fewer than two present values
                    is predicted as missing at every forecast hour.  Kattis
                    scores forecasts and has no correct answer: this is the
                    forced method (CLRS 28.3, least squares).
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope R_scope.

(* Math side.  The n measurement lines are four parallel columns, line k
   being hour k ("the measurements are made one hour apart").  A
   temperature or a speed is the real its float denotes; a direction or a
   humidity an integer, read as a real by [col_R]. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* An integer column, read over the reals. *)
Definition col_R (c : list (option N)) : list (option R) :=
  map (option_map (fun v => IZR (Z.of_N v))) c.

(* Every present value of the column c lies in [lo, hi]. *)
Definition col_in (lo hi : R) (c : list (option R)) : Prop :=
  Forall (fun o => match o with Some v => lo <= v <= hi | None => True end) c.

(* The number of present values of c. *)
Fixpoint present (c : list (option R)) : nat :=
  match c with
  | [] => 0%nat
  | None :: c' => present c'
  | Some _ :: c' => S (present c')
  end.

(* The sum of the squared residuals of the line t |-> a + b t over the
   present values of c, its first cell being hour t0. *)
Fixpoint sse (a b : R) (t0 : nat) (c : list (option R)) : R :=
  match c with
  | [] => 0
  | None :: c' => sse a b (S t0) c'
  | Some y :: c' => (y - (a + b * INR t0)) ^ 2 + sse a b (S t0) c'
  end.

(* a + b t is a least-squares line of the column c. *)
Definition lsq_line (c : list (option R)) (a b : R) : Prop :=
  forall a' b', sse a b 0 c <= sse a' b' 0 c.

Definition clamp (lo hi v : R) : R := Rmax lo (Rmin hi v).

(* out is a forecast of the m hours after the column c, within err: m
   cells; cell j is missing iff c has fewer than two present values, and
   otherwise lies in [lo, hi] within err of a least-squares line of c at
   hour len c + j, clamped to [lo, hi]. *)
Definition forecast (lo hi err : R) (c : list (option R)) (m : N)
    (out : list (option R)) : Prop :=
  len out = m /\
  forall j : nat, (N.of_nat j < m)%N ->
    (nth j out None = None <-> (present c < 2)%nat) /\
    forall r, nth j out None = Some r ->
      lo <= r <= hi /\
      exists a b, lsq_line c a b /\
        Rabs (r - clamp lo hi (a + b * INR (List.length c + j))) <= err.

(* The statement's guarantees.  The header line (position, height, date,
   time) does not enter the contract, and is left to the harness.  "Exactly
   one digit after the decimal point" is a property of the input text,
   gone once parsed.  The statement bounds neither n nor m. *)
Record valid_input (t : list (option R)) (d : list (option N))
    (s : list (option R)) (h : list (option N)) (m : N) : Prop := {
  (* n lines, each of temperature, wind direction, wind speed, humidity *)
  vi_d : len d = len t;
  vi_s : len s = len t;
  vi_h : len h = len t;
  (* temperatures are real numbers in the range -50 to 50 *)
  vi_t_range : col_in (-50) 50 t;
  (* average wind directions are integers in the range 0 to 360 *)
  vi_d_range : Forall (fun o => match o with Some v => (v <= 360)%N | None => True end) d;
  (* average wind speeds are real numbers in the range 0 to 80 *)
  vi_s_range : col_in 0 80 s;
  (* humidities are integers in the range 0 to 110 *)
  vi_h_range : Forall (fun o => match o with Some v => (v <= 110)%N | None => True end) h;
}.

Definition tol : R := / 1000000.

(* The four forecast columns.  An output of m cells exists only for m <=
   PArray.max_length = 4194303; beyond, nothing is required. *)
Definition vedurspa_spec (t : list (option R)) (d : list (option N))
    (s : list (option R)) (h : list (option N)) (m : N)
    (o : list (option R) * list (option N) * list (option R) * list (option N))
    : Prop :=
  let '(ot, od, os, oh) := o in
  (m <= 4194303)%N ->
  forecast (-50) 50 tol t m ot /\
  forecast 0 360 (/2 + tol) (col_R d) m (col_R od) /\
  forecast 0 80 tol s m os /\
  forecast 0 110 (/2 + tol) (col_R h) m (col_R oh).

Program vedurspa :
  array (option float) -> array (option uint) ->
  array (option float) -> array (option uint) -> uint ->
  array (option float) * array (option uint) *
  array (option float) * array (option uint).

Specification vedurspa_correct :
  forall (t : list (option R)) (d : list (option N)) (s : list (option R))
         (h : list (option N)) (m : N)
         (xt : array (option float)) (xd : array (option uint))
         (xs : array (option float)) (xh : array (option uint)) (xm : uint),
  valid_input t d s h m ->
  repr xt t -> repr xd d -> repr xs s -> repr xh h -> repr xm m ->
  exists o : list (option R) * list (option N) * list (option R) *
             list (option N),
    repr (vedurspa xt xd xs xh xm) o /\ vedurspa_spec t d s h m o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.

(* The four classical axioms Stdlib's reals rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec ClassicalDedekindReals.sig_not_dec Classical_Prop.classic FunctionalExtensionality.functional_extensionality_dep.
