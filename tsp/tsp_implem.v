(* Executable implementation and its required termination dependencies.
   Correctness proofs are in tsp_proofs.v. *)
(* Implementation of tsp.spec: CLRS 35.2 APPROX-TSP-TOUR, a minimum
   spanning tree by dense Prim (O(n^2), no heap, no edge list, no distance
   matrix), then the preorder walk of the tree from vertex 0.

   Code.  Exactness: [fex] reads every coordinate as m * 2^e (m, e in Z,
   from [frshiftexp] / [normfr_mantissa], [zofi] digit by digit, no nat);
   E is the least exponent of all the coordinates, and GX, GY hold the
   coordinates as integers on the grid 2^E (exact).  [Dz a b] is the exact
   squared distance in units of 2^(2E), a Z: Prim compares these, so its
   choices are exact with respect to the real distances.
   Prim: rank array rk (n = not in the tree yet), key array K (Z), parent
   array P; step k picks the outside vertex of least key (one scan), gives
   it rank k, relaxes the keys of the outside vertices (one scan).
   Walk: an explicit stack and a scan pointer it[u] per vertex; at the top
   u, the vertex c = it[u] is scanned, output and pushed when P[c] = u;
   u is popped when it[u] = n.  At most n^2 + n steps, bounded by the
   [loop] combinator (erased Acc on hi - i), as are all the loops.

   Proof.  [path_bound]: Prim's cut property (the edge added at step k is
   no longer than any edge between ranks < k and ranks >= k) bounds the
   tree weight W by any Hamiltonian path (induction removing the vertex of
   largest rank), hence by any tour ([W_le_tour]).  The walk invariant
   [DI]: output length + d(last, top of stack) + length of the stack path
   <= 2 * (weight of the tree edges of the vertices output so far), by the
   triangle inequality at every pop; at the end every vertex has been
   output exactly once (induction on the rank), so the tour is at most 2 W.
   The exact distance is the spec's [dist]; [di_D] ties it to [Dz]. *)

From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf.
From StdGalilei Require Import repr.
From StdGalilei Require Import repr_float.
From Flocq Require Core.Core IEEE754.BinarySingleNaN IEEE754.PrimFloat.
From Speck Require Import Prelude.
Import ListNotations.

Open Scope uint63_scope.
Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* The termination device                                              *)
(* ------------------------------------------------------------------ *)

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

Definition gap (m j : int) : Z := (to_Z m - to_Z j)%Z.

Lemma dec_step : forall hi i : int, (i <? hi) = true -> Zwf 0 (gap hi (i + 1)) (gap hi i).
Proof.
  intros hi i H. rewrite Uint63.ltb_spec in H. pose proof (to_Z_bounded hi).
  assert (to_Z (i + 1) = (to_Z i + 1)%Z) by sia. unfold Zwf, gap. lia.
Qed.


(* The one loop combinator: for i = lo, lo+1, ... while i < hi and
   [cont i s], s := f i s. *)
Section Loop.
Context {St : Type}.

Fixpoint wloop (hi : int) (cont : int -> St -> bool) (f : int -> St -> St)
    (i : int) (s : St) (H : Acc (Zwf 0) (gap hi i)) {struct H} : St :=
  match bdec (i <? hi) with
  | left Hi =>
      if cont i s then wloop hi cont f (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
      else s
  | right _ => s
  end.

Definition loop (hi : int) (cont : int -> St -> bool) (f : int -> St -> St)
    (i : int) (s : St) : St :=
  wloop hi cont f i s (Zwf_well_founded 0 (gap hi i)).

End Loop.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* -- Exact arithmetic, used only to settle close comparisons. -------- *)

Lemma dec_half : forall i : int, (i =? 0) = false -> Zwf 0 (to_Z (i / 2)) (to_Z i).
Proof.
  intros i H. assert (to_Z i <> 0%Z).
  { intros E. assert (i = 0) by (apply to_Z_inj; exact E). subst i. discriminate. }
  pose proof (to_Z_bounded i). unfold Zwf. sia.
Qed.

(* the integer a machine word denotes, by binary digits (no nat) *)
Fixpoint zofi_rec (i : int) (H : Acc (Zwf 0) (to_Z i)) {struct H} : Z :=
  match bdec (i =? 0) with
  | left _ => 0%Z
  | right Hn =>
      let r := zofi_rec (i / 2) (Acc_inv H (dec_half i Hn)) in
      let bit := if i mod 2 =? 0 then 0%Z else 1%Z in
      (2 * r + bit)%Z
  end.

Definition zofi (i : int) : Z := zofi_rec i (Zwf_well_founded 0 (to_Z i)).

(* A dyadic number (m, e) denotes m * 2^e. *)
Definition dal (d : Z * Z) (e : Z) : Z := Z.shiftl (fst d) (snd d - e).

(* the exact value of a finite float, from its normalised mantissa and
   exponent: f = m * 2^(e - 2101 - 53) *)
Definition fex (f : float) : Z * Z :=
  let (z, e) := frshiftexp f in
  let m := zofi (normfr_mantissa z) in
  ((if (f <? 0)%float then - m else m)%Z, (zofi e - 2154)%Z).

(* -- Floats. ---------------------------------------------------------- *)


(* -- The exact grid. ---------------------------------------------------- *)

(* the least exponent over all the coordinates (and 0) *)
Definition expo_step (x y : array float) (i : int) (E : Z) : Z :=
  Z.min E (Z.min (snd (fex x.[i])) (snd (fex y.[i]))).

(* the coordinates as integers on the grid 2^E: exact *)
Definition grid_step (x y : array float) (E : Z) (i : int) (st : array Z * array Z)
    : array Z * array Z :=
  ((fst st).[i <- dal (fex x.[i]) E], (snd st).[i <- dal (fex y.[i]) E]).

(* the exact squared distance between points a and b, in units of 2^(2E) *)
Definition Dz (GX GY : array Z) (a b : int) : Z :=
  let dx := (GX.[a] - GX.[b])%Z in
  let dy := (GY.[a] - GY.[b])%Z in
  (dx * dx + dy * dy)%Z.

(* -- Prim, dense. ---------------------------------------------------------- *)

Definition key_init (GX GY : array Z) (w : int) (K : array Z) : array Z :=
  K.[w <- Dz GX GY 0 w].

(* the vertex outside the tree (rank n) of least key; n if none *)
Definition amin_step (n : int) (rk : array int) (K : array Z) (w b : int) : int :=
  if andb (rk.[w] =? n) (orb (b =? n) (Z.ltb K.[w] K.[b])) then w else b.

Definition relax_step (GX GY : array Z) (n : int) (rk : array int) (v : int) (w : int)
    (st : array Z * array int) : array Z * array int :=
  if rk.[w] =? n then
    let d := Dz GX GY v w in
    if Z.ltb d (fst st).[w] then ((fst st).[w <- d], (snd st).[w <- v]) else st
  else st.

(* step k: the vertex v of least key gets rank k, then the keys are relaxed *)
Definition prim_step (GX GY : array Z) (n : int) (k : int)
    (st : array int * array Z * array int) : array int * array Z * array int :=
  let rk := fst (fst st) in
  let v := loop n (fun _ _ => true) (amin_step n rk (snd (fst st))) 0 n in
  let rk' := rk.[v <- k] in
  let KP := loop n (fun _ _ => true) (relax_step GX GY n rk' v) 0 (snd (fst st), snd st) in
  (rk', fst KP, snd KP).

(* -- The preorder walk. ------------------------------------------------------ *)

(* state: per-vertex scan pointer, stack and its size, output and its size *)
Definition DS : Type := array int * array int * int * array int * int.

Definition ds_it (s : DS) : array int := fst (fst (fst (fst s))).
Definition ds_stk (s : DS) : array int := snd (fst (fst (fst s))).
Definition ds_sp (s : DS) : int := snd (fst (fst s)).
Definition ds_out (s : DS) : array int := snd (fst s).
Definition ds_cnt (s : DS) : int := snd s.

(* at the top u of the stack: scan the next vertex c; when c is a child of
   u, output it and push it; when u has been scanned to n, pop it *)
Definition dfs_step (n : int) (P : array int) (j : int) (s : DS) : DS :=
  let it := ds_it s in let stk := ds_stk s in let sp := ds_sp s in
  let out := ds_out s in let cnt := ds_cnt s in
  let u := stk.[sp - 1] in
  let c := it.[u] in
  if c <? n then
    let it' := it.[u <- c + 1] in
    if andb (P.[c] =? u) (negb (c =? 0)) then
      (it', stk.[sp <- c], sp + 1, out.[cnt <- c], cnt + 1)
    else (it', stk, sp, out, cnt)
  else (it, stk, sp - 1, out, cnt).

Definition tsp_impl (x y : array float) : array int :=
  let n := PArray.length x in
  let E := loop n (fun _ _ => true) (expo_step x y) 0 0%Z in
  let G := loop n (fun _ _ => true) (grid_step x y E) 0
             (PArray.make n 0%Z, PArray.make n 0%Z) in
  let GX := fst G in let GY := snd G in
  let K0 := loop n (fun _ _ => true) (key_init GX GY) 0 (PArray.make n 0%Z) in
  let rk0 := (PArray.make n n).[0 <- 0] in
  let PR := loop n (fun _ _ => true) (prim_step GX GY n) 1 (rk0, K0, PArray.make n 0) in
  let s := loop (n * n + n + 1) (fun _ s => 0 <? ds_sp s) (dfs_step n (snd PR)) 0
             (PArray.make n 0, PArray.make n 0, 1, PArray.make n 0, 1) in
  ds_out s.

Local Notation bp := (Raux.bpow Zaux.radix2).

(* ------------------------------------------------------------------ *)
(* Generic lemmas: sums, the triangle inequality, pigeonholes          *)
(* ------------------------------------------------------------------ *)

Local Open Scope R_scope.

Local Close Scope R_scope.

Local Open Scope nat_scope.

Local Close Scope nat_scope.

Definition tsp : array float -> array float -> array uint := tsp_impl.
