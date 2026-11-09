(* Executable implementation and its required termination dependencies.
   Correctness proofs are in stringmatching_proofs.v. *)
(* Implementation of stringmatching (stringmatching.spec): Knuth-Morris-
   Pratt.

   Code.  [find_all xp xt] returns the empty array when |xt| < |xp|.
   Otherwise it builds the failure table once ([build]: one flat
   [array int] of |xp| cells, tbl.[i] = the longest proper border of the
   prefix of length i+1, computed left to right with the same fallback
   [fall] as the scan), then scans the text once left to right ([scan]):
   [fall] extends the matched length q by the next text symbol, falling
   back through tbl.[q-1] on a mismatch; on a full match (q = |xp|) the
   position i+1-|xp| is written into a scratch buffer of |xt|-|xp|+1
   cells and q falls back to tbl.[|xp|-1], so overlapping occurrences are
   found.  At the end the cnt positions found are copied ([copy]) into an
   exactly sized result.  Every array is threaded linearly; the strings
   are only read.  No Z, N or nat in the code.

   [fall] carries one extra comparison, [tbl.[q-1] <? q], as its
   termination guard (the recursion is on an erased [Acc (Zwf 0) (φ q)]);
   the proof shows the guard always holds (a border is shorter than its
   prefix).  The other loops recurse on [Acc (Zwf 0) (gap _ _)] as in
   template/polymul1.

   Proof.  On abstract symbol maps p, u : Z -> Z, [S i q] (the prefix of
   length q of p ends at position i of u) and [border q k]; [tbl_ok F Q]
   says F q is the longest proper border of prefix q for q <= Q.
   [fall_spec]: from S i q, the result r satisfies S (i+1) r and is the
   largest such length below q+1.  [build_spec] (u = p) and [scan_spec]
   (u = the text) are the loop invariants; [occurs_iff_occ] links the
   spec's [occurs_at] (on String.string) to the symbol maps through
   [repr]; [out_ok_correct] reads the math list off the result array. *)

From Stringmatching.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf String Ascii.
From Stdlib Require PrimString.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

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

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_fall : forall q' q : int,
  (q' <? q) = true -> Zwf 0 (φ q') (φ q).
Proof.
  intros q' q H. rewrite ltb_spec in H. pose proof (to_Z_bounded q').
  unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* The fallback of KMP.  q is the length of the current matched prefix
   of the pattern xp, c the next symbol: while the pattern's symbol q
   differs from c, fall back to tbl.[q-1] (the failure value of the prefix
   of length q); return the new matched length (q + 1 on a match, 0 when
   even the empty prefix cannot be extended).  The test [q' <? q] is the
   termination guard (a failure value is always shorter than its prefix,
   so the [right] branch is dead code). *)
Fixpoint fall (xp : PrimString.string) (tbl : array int) (c q : int)
    (H : Acc (Zwf 0) (φ q)) {struct H} : int :=
  if PrimString.get xp q =? c then q + 1
  else match bdec (0 <? q) with
       | left _ =>
           let q' := tbl.[q - 1] in
           match bdec (q' <? q) with
           | left Hlt => fall xp tbl c q' (Acc_inv H (dec_fall q' q Hlt))
           | right _ => 0
           end
       | right _ => 0
       end.

(* The failure table: tbl.[i] := the length of the longest proper border
   of the prefix of length i + 1, for i = 1 .. m-1 (tbl.[0] = 0 from the
   allocation); q is tbl.[i-1]. *)
Fixpoint build (xp : PrimString.string) (m : int) (tbl : array int) (i q : int)
    (H : Acc (Zwf 0) (gap m i)) {struct H} : array int :=
  match bdec (i <? m) with
  | left Hi =>
      let r := fall xp tbl (PrimString.get xp i) q (Zwf_well_founded 0 (φ q)) in
      build xp m tbl.[i <- r] (i + 1) r (Acc_inv H (dec_step m i Hi))
  | right _ => tbl
  end.

(* res.[k] := buf.[k] for k = k0 .. c-1. *)
Fixpoint copy (buf res : array int) (c k : int)
    (H : Acc (Zwf 0) (gap c k)) {struct H} : array int :=
  match bdec (k <? c) with
  | left Hk => copy buf res.[k <- buf.[k]] c (k + 1) (Acc_inv H (dec_step c k Hk))
  | right _ => res
  end.

(* The text scan: i the next text position, q the matched length, the
   occurrences found so far in buf.[0 .. cnt-1]; on a full match record
   i + 1 - m and fall back to tbl.[m-1].  At the end, copy the cnt
   positions into an exactly sized array. *)
Fixpoint scan (xp xt : PrimString.string) (tbl : array int) (m n : int)
    (buf : array int) (i q cnt : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi =>
      let r := fall xp tbl (PrimString.get xt i) q (Zwf_well_founded 0 (φ q)) in
      if r =? m then
        scan xp xt tbl m n buf.[cnt <- i + 1 - m] (i + 1) tbl.[m - 1] (cnt + 1)
          (Acc_inv H (dec_step n i Hi))
      else
        scan xp xt tbl m n buf (i + 1) r cnt (Acc_inv H (dec_step n i Hi))
  | right _ => copy buf (PArray.make cnt 0) cnt 0 (Zwf_well_founded 0 (gap cnt 0))
  end.

Definition find_all_impl (xp xt : PrimString.string) : array uint :=
  let m := PrimString.length xp in
  let n := PrimString.length xt in
  if n <? m then PArray.make 0 0
  else
    let tbl := build xp m (PArray.make m 0) 1 0 (Zwf_well_founded 0 (gap m 1)) in
    scan xp xt tbl m n (PArray.make (n - m + 1) 0) 0 0 0
      (Zwf_well_founded 0 (gap n 0)).

(* ------------------------------------------------------------------ *)
(* Prop side: borders and matched prefixes, on abstract symbol maps    *)
(* ------------------------------------------------------------------ *)

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition find_all : PrimString.string -> PrimString.string -> array uint :=
  find_all_impl.
