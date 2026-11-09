(* Executable implementation and its required termination dependencies.
   Correctness proofs are in dimensionalanalysis_proofs.v. *)
(* Implementation of dimensionalanalysis (dimensionalanalysis.spec).

   Code.  ONE exact, fraction-free Gauss-Jordan elimination of the n x m
   exponent table, in place on one flat [array Z] (cell (i, j) at i*m + j),
   threaded linearly.  Columns c = 0 .. m-1 in order: the pivot is the first
   row not yet used as a pivot row (flags in one flat [array bool]) with a
   nonzero entry in column c; every other row i with f = T[i][c] <> 0 becomes
   p * row i - f * row s (p the pivot), then is divided by the gcd of its
   entries ([StdGalilei.bigint.zgcd]) to keep the entries at the size of minors.
   At the end the table is a reduced echelon form up to row scaling, and a
   quantity is forced dimensionless exactly when some row has a single
   nonzero entry, so [valid] answers "no row has exactly one nonzero".
   Entries are converted from sint to Z by a nat-free binary recursion
   ([sconv]; Uint63.to_Z recurses on a nat).  Indices, lengths and counters
   are Uint63; the only bignums are the cells and the arithmetic on them.

   Termination: every loop is the one combinator [for_] (lo .. hi - 1),
   structural on an erased [Acc (Zwf 0) (gap hi i)]; [uconv] on an erased
   [Acc (Zwf 0) (φ x)].

   Proof.  [for_spec] is the one loop rule (an invariant P indexed by φ i).
   On the math side the table is a Z-indexed matrix [cell T m]; [Inv]
   says that it has the same rational solutions as the input ([sol]) and
   the pivot structure [PivOK] (used rows have a pivot column < c, alone
   nonzero in it; other rows are zero on the columns < c).  [inv_elim] /
   [inv_skip] carry it across a column; [final_iff] reads the answer off
   at c = m, building the witness assignment [dk] (one free column set to
   1, pivot columns solved).  [satisfies_iff] / [free_iff] connect [sol]
   to the spec's [satisfies] / [free_quantity]. *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From StdGalilei Require Import bigint.
From Stdlib Require Import ZArith NArith QArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* The termination device and the one loop                             *)
(* ------------------------------------------------------------------ *)

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

(* s threaded through f i, for i = lo .. hi - 1. *)
Fixpoint loop {S : Type} (f : int -> S -> S) (hi i : int) (s : S)
    (H : Acc (Zwf 0) (gap hi i)) {struct H} : S :=
  match bdec (i <? hi) with
  | left Hi => loop f hi (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
  | right _ => s
  end.

Definition for_ {S : Type} (lo hi : int) (s : S) (f : int -> S -> S) : S :=
  loop f hi lo s (Zwf_well_founded 0 (gap hi lo)).

(* ------------------------------------------------------------------ *)
(* sint -> Z, nat-free (Uint63.to_Z recurses on a nat)                 *)
(* ------------------------------------------------------------------ *)

Lemma half_dec : forall x : int, (x =? 0) = false -> Zwf 0 (φ (x / 2)) (φ x).
Proof.
  intros x H. rewrite eqb_false_spec in H.
  assert ((φ x) <> 0%Z) by (intro E; apply H; apply to_Z_inj; exact E).
  pose proof (to_Z_bounded x). unfold Zwf. rewrite div_spec.
  change (φ 2) with 2%Z. split; [lia|]. apply Z.div_lt; lia.
Qed.

Fixpoint uconv (x : int) (H : Acc (Zwf 0) (φ x)) {struct H} : Z :=
  match bdec (x =? 0) with
  | left _ => 0%Z
  | right Hx =>
      (2 * uconv (x / 2)%uint63 (Acc_inv H (half_dec x Hx))
       + (if (x mod 2 =? 0)%uint63 then 0 else 1))%Z
  end.

Definition sconv (x : sint) : Z :=
  if x <? 4611686018427387904 then uconv x (Zwf_well_founded 0 _)
  else (- uconv (0 - x) (Zwf_well_founded 0 _))%Z.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* the flat n x m table of Z, cell (i, j) at i * m + j *)
Definition ztab (n m : int) (xe : array (array sint)) : array Z :=
  for_ 0 n (PArray.make (n * m) 0%Z) (fun i T =>
    let row := xe.[i] in
    for_ 0 m T (fun j T => T.[i * m + j <- sconv row.[j]])).

(* row i := p * row i - f * row s *)
Definition upd_row (m i s : int) (p f : Z) (T : array Z) : array Z :=
  for_ 0 m T (fun j T =>
    T.[i * m + j <- (p * T.[i * m + j] - f * T.[s * m + j])%Z]).

Definition row_gcd (m i : int) (T : array Z) : Z :=
  for_ 0 m 0%Z (fun j g => zgcd g T.[i * m + j]).

Definition div_row (m i : int) (g : Z) (T : array Z) : array Z :=
  for_ 0 m T (fun j T => T.[i * m + j <- (T.[i * m + j] / g)%Z]).

Definition norm_row (m i : int) (T : array Z) : array Z :=
  let g := row_gcd m i T in
  if (1 <? g)%Z then div_row m i g T else T.

(* eliminate column c from every row but the pivot row s *)
Definition elim_rows (n m s c : int) (T : array Z) : array Z :=
  let p := T.[s * m + c] in
  for_ 0 n T (fun i T =>
    if i =? s then T
    else
      let f := T.[i * m + c] in
      if (f =? 0)%Z then T else norm_row m i (upd_row m i s p f T)).

(* the first row not yet a pivot row with a nonzero entry in column c,
   or n *)
Definition find_piv (n m c : int) (T : array Z) (U : array bool) : int :=
  for_ 0 n n (fun i r =>
    if r =? n then
      (if U.[i] then r else if (T.[i * m + c] =? 0)%Z then r else i)
    else r).

Definition col_step (n m : int) (c : int) (st : array Z * array bool)
    : array Z * array bool :=
  let T := fst st in
  let U := snd st in
  let s := find_piv n m c T U in
  if s =? n then st else (elim_rows n m s c T, U.[s <- true]).

Definition count_nz (m i : int) (T : array Z) : int :=
  for_ 0 m 0 (fun j k => if (T.[i * m + j] =? 0)%Z then k else k + 1).

Definition valid_impl (xm : uint) (xe : array (array sint)) : bool :=
  let n := PArray.length xe in
  let m := xm in
  let st := for_ 0 m (ztab n m xe, PArray.make n false) (col_step n m) in
  let T := fst st in
  for_ 0 n true (fun i b => if b then negb (count_nz m i T =? 1) else false).

(* ------------------------------------------------------------------ *)
(* Math side: sums over Q, solutions of a Z-indexed matrix             *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition valid : uint -> array (array sint) -> bool := valid_impl.
