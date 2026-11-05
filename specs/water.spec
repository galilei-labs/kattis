(* @function        water
   @signature       uint -> array uint -> array uint -> array uint ->
                    array uint -> array uint -> array uint -> array uint
   @math_signature  N -> list N -> list N -> list N ->
                    list N -> list N -> list N -> list N
   @summary         [water n pa pb pc ia ib ic] gets n stations 1..n (1 the
                    pumping station, 2 the mansion), the initial pipes
                    (pipe j joins pa_j and pb_j with capacity pc_j) and the
                    k improvements (improvement t adds capacity ic_t between
                    ia_t and ib_t). It returns k+1 values: value t is the
                    maximum amount of water that can flow from station 1 to
                    station 2 once the first t improvements are made.
*)

From Stdlib Require Import ZArith NArith List Bool Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The pipes of each section are three parallel lists, one per
   column of the lines "a b c". *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* Element j of l (0 beyond the end). *)
Definition get (l : list N) (j : N) : N := nth (N.to_nat j) l 0.

(* u is a station. *)
Definition station (n u : N) : Prop := 1 <= u <= n.

(* g 0 + g 1 + ... + g (t - 1). *)
Fixpoint sum_below (g : N -> N) (t : nat) : N :=
  match t with
  | O => 0
  | S t' => sum_below g t' + g (N.of_nat t')
  end.

(* The capacity between u and v of the first t pipes of the section a b c:
   a pipe joins its two stations in both directions, and capacities of the
   same pair add up (an improvement increases the pipe's capacity). *)
Definition cap_upto (a b c : list N) (t : N) (u v : N) : N :=
  sum_below (fun j => if (get a j =? u) && (get b j =? v)
                         || (get a j =? v) && (get b j =? u)
                      then get c j else 0) (N.to_nat t).

(* The capacity between u and v after the first t improvements. *)
Definition capacity (pa pb pc ia ib ic : list N) (t u v : N) : N :=
  cap_upto pa pb pc (len pa) u v + cap_upto ia ib ic t u v.

(* g 1 + g 2 + ... + g m. *)
Fixpoint sum_stations (g : N -> Z) (m : nat) : Z :=
  match m with
  | O => 0%Z
  | S m' => (sum_stations g m' + g (N.of_nat m))%Z
  end.

(* The net amount of water leaving station u under f. *)
Definition net_out (n : N) (f : N -> N -> Z) (u : N) : Z :=
  sum_stations (f u) (N.to_nat n).

(* f u v is the net amount of water sent from u to v through the pipes
   joining them: it is antisymmetric, at most the capacity, and every
   station other than 1 and 2 keeps no water. *)
Definition is_flow (n : N) (cap : N -> N -> N) (f : N -> N -> Z) : Prop :=
  (forall u v, station n u -> station n v -> f u v = (- f v u)%Z) /\
  (forall u v, station n u -> station n v -> (f u v <= Z.of_N (cap u v))%Z) /\
  (forall u, station n u -> u <> 1 -> u <> 2 -> net_out n f u = 0%Z).

(* w is the maximum amount of water reaching the mansion: some flow brings
   w, and no flow brings more. *)
Definition max_flow (n : N) (cap : N -> N -> N) (w : N) : Prop :=
  (exists f, is_flow n cap f /\ net_out n f 1 = Z.of_N w) /\
  (forall f, is_flow n cap f -> (net_out n f 1 <= Z.of_N w)%Z).

Record valid_input (n : N) (pa pb pc ia ib ic : list N) : Prop := {
  (* 2 <= n <= 100 *)
  vi_n : 2 <= n <= 100;
  (* 0 <= p <= n(n-1)/2, the p lines of the initial pipes being "a b c" *)
  vi_p : len pa <= n * (n - 1) / 2;
  vi_pb : len pb = len pa;
  vi_pc : len pc = len pa;
  (* 1 <= k <= 10 000, the k lines of the improvements being "a b c" *)
  vi_k : 1 <= len ia <= 10000;
  vi_ib : len ib = len ia;
  vi_ic : len ic = len ia;
  (* initial pipes: 1 <= a < b <= n and 1 <= c <= 1 000 *)
  vi_pab : forall j, j < len pa -> 1 <= get pa j < get pb j /\ get pb j <= n;
  vi_pcap : forall j, j < len pa -> 1 <= get pc j <= 1000;
  (* no (a, b) pair will appear more than once in this section *)
  vi_pdistinct : NoDup (combine pa pb);
  (* improvements: 1 <= a < b <= n and 1 <= c <= 1 000 *)
  vi_iab : forall t, t < len ia -> 1 <= get ia t < get ib t /\ get ib t <= n;
  vi_icap : forall t, t < len ia -> 1 <= get ic t <= 1000;
}.

(* k + 1 values; value t is the maximum flow from 1 to 2 after the first t
   improvements (value 0: the initial configuration). *)
Definition water_spec (n : N) (pa pb pc ia ib ic o : list N) : Prop :=
  len o = len ia + 1 /\
  forall t, t < len o -> max_flow n (capacity pa pb pc ia ib ic t) (get o t).

Program water : uint -> array uint -> array uint -> array uint ->
  array uint -> array uint -> array uint -> array uint.

Specification water_correct :
  forall (n : N) (pa pb pc ia ib ic : list N)
         (xn : uint) (xpa xpb xpc xia xib xic : array uint),
  valid_input n pa pb pc ia ib ic ->
  repr xn n -> repr xpa pa -> repr xpb pb -> repr xpc pc ->
  repr xia ia -> repr xib ib -> repr xic ic ->
  exists o : list N, repr (water xn xpa xpb xpc xia xib xic) o /\
    water_spec n pa pb pc ia ib ic o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
