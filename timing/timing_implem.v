(* Executable implementation and its required termination dependencies.
   Correctness proofs are in timing_proofs.v. *)
(* Implementation of timing.spec (steering v3): the t time units
   simulated one by one in binary64, a per-fort error bound accumulated at
   run time in floats rounded upward, and the exact computation of the
   first try as the fallback.

   MAIN PATH ([timing_impl], Part 3 at the end of the file).
   - once: [cnt_step] counts the non-self links touching each fort (an
     [array int]), [out_step] sums the fraction leaving each fort (an
     [array float]).
   - [tstep], t times, on (v, e, ok): v the strengths (one flat
     [array float]), e one error bound per fort (0 at the start: the inputs
     are the exact floats the spec reads), ok a flag.  [unit_f] (try 2,
     unchanged) copies v and scatters every link j (s -> d, s <> d):
     a := p_j * v[s]; w[d] += a; w[s] -= a, every product from the
     start-of-unit v.  [ebound] then makes one pass over the links
     ([elink]: Ein[d] += p_j * e[s]; Mac[s], Mac[d] += |a|) and one over
     the forts ([efort]):
        e'[x] = up( coef_x * e[x] + Ein[x] + k_x * (|v[x]| + Mac[x] + 1) )
     coef_x = |1 - out_x| + 2^-30 (an upper bound of |1 - out_x|),
     k_x = (2 cnt_x + 3) u, u = 2^-52, up(y) = y * (1 + 2^-30) + 2^-52.
     ok drops to false (and stays false) as soon as some e'[x] > 1.
   - the faced value of each fort in floats ([faced_f], try 2) and their
     minimum o ([fmin]); per fort, [fpair] sums e and |v| over the fort and
     the forts joined to it, and F_i = up(E_i + (N+1) u (M_i + 1))
     ([fbound]); B = max_i F_i ([gmax]).
   - [fcheck]: o is returned when ok and (B < 2^-20, an absolute error
     below 10^-6, or B (2^20 + 1) < o, a relative one), compared exactly
     over Z on the dyadic values of B and o (try 2's [fex], [dlt]).
     Otherwise the fallback runs.

   PROOF.  [ap k x X]: the float x and the real X >= 0 are within the
   factor (1+u)^k (and k eta) of each other, both ways; it goes through
   the rounded add and mul of nonneg values ([ap_add], [ap_mulc],
   [ap_mul0]) and [up] turns it into fval (up x) >= X ([ap_up]).  The link
   pass and the fort pass ([elink_spec], [ebound_spec]) give
   fval e'[x] >= Sx: coef_x e[x] + sum_{d_j = x} p_j e[s_j] +
   k_x (|v[x]| + sum of the |a| touching x + 1).  Against the exact step
   ([unit_err], from try 2's [unit_spec] and [Am_apply]) the new error at
   x is at most |1 - out_x| |err x| + sum_{d_j = x, s_j <> x} p_j |err s_j|
   + (2 cnt_x + 2) u (M_x + 1), M_x = |v x| + the transfers touching x.
   Induction over the units ([sim_inv]): |v_k(i) - strength k i| <= e_k(i)
   <= 1.  The faced sums add N u (M_i + 1) ([faced_f_spec2], per fort), so
   every computed faced value is within F_i <= B of the exact one, and the
   computed minimum within B of the true minimum.

   FALLBACK (Part 1, from ../implem-bens-1, renamed [timing_exact]):
   matrix exponentiation by squaring, Strassen products, in fixed point
   over Z at scale 2^-96.

   Exact arithmetic: in the fallback (Z bignums) and in [fcheck] (the
   comparison of B and o over Z, once).  The main path's strengths,
   fractions, error bounds and faced values are floats only.

   Termination: every loop recurses on an erased [Acc (Zwf 0) _] proof. *)

From Timing.spec Require Import Prelude.
From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf.
From StdGalilei Require Import repr.
From StdGalilei Require Import repr_float.
From Flocq Require Core.Core IEEE754.BinarySingleNaN IEEE754.PrimFloat.
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

Lemma dec_half : forall i : int, (i =? 0) = false -> Zwf 0 (to_Z (i / 2)) (to_Z i).
Proof.
  intros i H. assert (to_Z i <> 0%Z).
  { intros E. assert (i = 0) by (apply to_Z_inj; exact E). subst i. discriminate. }
  pose proof (to_Z_bounded i). unfold Zwf. sia.
Qed.

(* for i = lo, lo+1, ..., hi-1: s := f i s *)
Section Loop.
Context {St : Type}.

Fixpoint wloop (hi : int) (f : int -> St -> St)
    (i : int) (s : St) (H : Acc (Zwf 0) (gap hi i)) {struct H} : St :=
  match bdec (i <? hi) with
  | left Hi => wloop hi f (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
  | right _ => s
  end.

Definition loop (hi : int) (f : int -> St -> St) (i : int) (s : St) : St :=
  wloop hi f i s (Zwf_well_founded 0 (gap hi i)).

End Loop.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

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

(* the machine word of a positive below 2^63, by binary digits *)
Fixpoint iofp (p : positive) : int :=
  match p with
  | xH => 1
  | xO q => 2 * iofp q
  | xI q => 2 * iofp q + 1
  end.

Definition iofz (z : Z) : int :=
  match z with Zpos p => iofp p | _ => 0 end.

(* the exact value of a finite float, (m, e) for m * 2^e *)
Definition fex (f : float) : Z * Z :=
  let (z, e) := frshiftexp f in
  let m := zofi (normfr_mantissa z) in
  ((if (f <? 0)%float then - m else m)%Z, (zofi e - 2154)%Z).

(* the fixed-point scale: z stands for z / 2^PP *)
Definition PP : Z := 96%Z.
Definition ONE : Z := Z.shiftl 1 PP.

(* floor (f * 2^PP) *)
Definition fixv (f : float) : Z :=
  let d := fex f in Z.shiftl (fst d) (snd d + PP).

(* -- flat Z matrices ------------------------------------------------- *)

Definition build (len : int) (f : int -> Z) : array Z :=
  loop len (fun k (a : array Z) => a.[k <- f k]) 0 (PArray.make len 0%Z).

(* sum_k X[i][k] * Y[k][j], size s *)
Definition dot (s : int) (X Y : array Z) (i j : int) : Z :=
  loop s (fun k acc => (acc + X.[i * s + k] * Y.[k * s + j])%Z) 0 0%Z.

Definition naive (s : int) (X Y : array Z) : array Z :=
  build (s * s) (fun k => dot s X Y (k / s) (k mod s)).

Definition quad (X : array Z) (s h di dj : int) : array Z :=
  build (h * h) (fun k => X.[(di + k / h) * s + (dj + k mod h)]).

Definition madd (h : int) (A B : array Z) : array Z :=
  build (h * h) (fun k => (A.[k] + B.[k])%Z).

Definition msub (h : int) (A B : array Z) : array Z :=
  build (h * h) (fun k => (A.[k] - B.[k])%Z).

Definition comb (s h : int) (C11 C12 C21 C22 : array Z) : array Z :=
  build (s * s) (fun k =>
    let i := k / s in let j := k mod s in
    if i <? h then
      (if j <? h then C11.[i * h + j] else C12.[i * h + (j - h)])
    else
      (if j <? h then C21.[(i - h) * h + j] else C22.[(i - h) * h + (j - h)])).

Definition cut : int := 16.
Definition splitb (s : int) : bool := (cut <? s) && (s mod 2 =? 0).

Lemma dec_split : forall s : int, splitb s = true -> Zwf 0 (to_Z (s / 2)) (to_Z s).
Proof.
  intros s H. unfold splitb in H. apply andb_prop in H as [H _].
  unfold cut in H. rewrite Uint63.ltb_spec in H. change (to_Z 16) with 16%Z in H.
  pose proof (to_Z_bounded s). unfold Zwf. sia.
Qed.

(* the exact product of two s*s matrices, Strassen's seven products *)
Fixpoint strass (s : int) (X Y : array Z) (H : Acc (Zwf 0) (to_Z s)) {struct H} : array Z :=
  match bdec (splitb s) with
  | left Hs =>
      let h := s / 2 in
      let sr := fun A B => strass h A B (Acc_inv H (dec_split s Hs)) in
      let A11 := quad X s h 0 0 in let A12 := quad X s h 0 h in
      let A21 := quad X s h h 0 in let A22 := quad X s h h h in
      let B11 := quad Y s h 0 0 in let B12 := quad Y s h 0 h in
      let B21 := quad Y s h h 0 in let B22 := quad Y s h h h in
      let M1 := sr (madd h A11 A22) (madd h B11 B22) in
      let M2 := sr (madd h A21 A22) B11 in
      let M3 := sr A11 (msub h B12 B22) in
      let M4 := sr A22 (msub h B21 B11) in
      let M5 := sr (madd h A11 A12) B22 in
      let M6 := sr (msub h A21 A11) (madd h B11 B12) in
      let M7 := sr (msub h A12 A22) (madd h B21 B22) in
      comb s h (madd h (msub h (madd h M1 M4) M5) M7)
               (madd h M3 M5)
               (madd h M2 M4)
               (madd h (madd h (msub h M1 M2) M3) M6)
  | right _ => naive s X Y
  end.

(* the product of two fixed-point matrices, floored back to 2^-PP *)
Definition mulr (m : int) (X Y : array Z) : array Z :=
  let C := strass m X Y (Zwf_well_founded 0 (to_Z m)) in
  build (m * m) (fun k => Z.shiftr C.[k] PP).

(* the identity *)
Definition ident (m : int) : array Z :=
  build (m * m) (fun k => if k / m =? k mod m then ONE else 0%Z).

(* link l: +p at (dst, src), -p at (src, src) *)
Definition link_step (m : int) (xs xd : array uint) (xf : array float)
    (l : int) (A : array Z) : array Z :=
  let s := xs.[l] in let d := xd.[l] in let F := fixv xf.[l] in
  let A1 := A.[d * m + s <- (A.[d * m + s] + F)%Z] in
  A1.[s * m + s <- (A1.[s * m + s] - F)%Z].

Definition amat (m L : int) (xs xd : array uint) (xf : array float) : array Z :=
  loop L (link_step m xs xd xf) 0 (ident m).

(* square and multiply: R (None for the identity) times B^t *)
Fixpoint pw (m t : int) (R : option (array Z)) (B : array Z)
    (H : Acc (Zwf 0) (to_Z t)) {struct H} : option (array Z) :=
  match bdec (t =? 0) with
  | left _ => R
  | right Hn =>
      let R' := if t mod 2 =? 0 then R
                else Some (match R with None => B | Some X => mulr m X B end) in
      let t' := t / 2 in
      if t' =? 0 then R' else pw m t' R' (mulr m B B) (Acc_inv H (dec_half t Hn))
  end.

(* -- the answer ------------------------------------------------------ *)

Definition adj_step (n : int) (xs xd : array uint) (l : int) (a : array bool) : array bool :=
  let s := xs.[l] in let d := xd.[l] in
  if s =? d then a else a.[s * n + d <- true].[d * n + s <- true].

Definition faced_z (n : int) (adj : array bool) (v : array Z) (i : int) : Z :=
  (v.[i] + loop n (fun k acc => if adj.[i * n + k] then (acc + v.[k])%Z else acc) 0 0%Z)%Z.

(* z / 2^(2 PP) as a float, for 0 <= z *)
Definition cv (z : Z) : float :=
  (of_uint63 (iofz (Z.shiftr z (2 * PP - 30))) / of_uint63 1073741824)%float.

Definition conv (z : Z) : float :=
  if (z <? 0)%Z then (- cv (- z))%float else cv z.

Definition timing_exact (xt : uint) (xu : array float) (xs xd : array uint)
    (xf : array float) : float :=
  let n := PArray.length xu in
  let L := PArray.length xs in
  let m := ((n + 7) / 8) * 8 in
  let A := amat m L xs xd xf in
  let Rf := match pw m xt None A (Zwf_well_founded 0 (to_Z xt)) with
            | None => ident m | Some X => X end in
  let uh := build m (fun s => if s <? n then fixv xu.[s] else 0%Z) in
  let v := build m (fun i => loop m (fun k acc => (acc + Rf.[i * m + k] * uh.[k])%Z) 0 0%Z) in
  let adj := loop L (adj_step n xs xd) 0 (PArray.make (n * n) false) in
  let best := loop n (fun i b => Z.min b (faced_z n adj v i)) 1 (faced_z n adj v 0) in
  conv best.

(* ------------------------------------------------------------------ *)
(* Integer matrices, mathematically                                    *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* Real matrices and the column-sum norm                               *)
(* ------------------------------------------------------------------ *)

Local Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(* Exact value of a float, fixed point                                 *)
(* ------------------------------------------------------------------ *)

Local Instance prec53' : FLX.Prec_gt_0 53 := eq_refl _.
Local Instance fexp64_valid' : Generic_fmt.Valid_exp fexp64 := FLT.FLT_exp_valid _ _.

Local Notation bp := (Raux.bpow Zaux.radix2).

(* ------------------------------------------------------------------ *)
(* The remaining loops                                                 *)
(* ------------------------------------------------------------------ *)

Local Open Scope Z_scope.

Local Open Scope R_scope.


Open Scope uint63_scope.
(* ================================================================== *)
(* Part 2: the main path, a step-by-step simulation in binary64        *)
(* ================================================================== *)

(* link j, from the start-of-unit strengths v, into the new strengths w *)
Definition link_f (xs xd : array uint) (xf : array float) (v : array float)
    (j : int) (w : array float) : array float :=
  let s := xs.[j] in let d := xd.[j] in
  if s =? d then w else
  let a := (xf.[j] * v.[s])%float in
  let w1 := w.[d <- (w.[d] + a)%float] in
  w1.[s <- (w1.[s] - a)%float].

(* one time unit: a fresh copy of v, then every link *)
Definition unit_f (L : int) (xs xd : array uint) (xf : array float) (v : array float) : array float :=
  loop L (link_f xs xd xf v) 0 (PArray.copy v).

(* t time units *)
(* the number of links (other than self-loops) touching each fort *)
Definition cnt_step (xs xd : array uint) (j : int) (c : array int) : array int :=
  let s := xs.[j] in let d := xd.[j] in
  if s =? d then c else
  let c1 := c.[s <- c.[s] + 1] in c1.[d <- c1.[d] + 1].

(* what fort i faces, in floats *)
Definition faced_f (n : int) (adj : array bool) (v : array float) (i : int) : float :=
  loop n (fun k acc => if adj.[i * n + k] then (acc + v.[k])%float else acc) 0 v.[i].

Definition fmin (b x : float) : float := if (x <? b)%float then x else b.

(* the bound check, exact, once: x 2^a < y 2^b *)
Definition dlt (x a y b : Z) : bool :=
  if (a <=? b)%Z then (x <? Z.shiftl y (b - a))%Z else (Z.shiftl x (a - b) <? y)%Z.


Local Open Scope R_scope.


Open Scope uint63_scope.

(* ================================================================== *)
(* Part 3: the runtime error bound (steering v3)                       *)
(* ================================================================== *)

Definition f_u : float := 0x1p-52%float.          (* u = 2^-52 *)
Definition f_K1 : float := 0x1.00000004p0%float.  (* 1 + 2^-30 *)
Definition f_s30 : float := 0x1p-30%float.        (* 2^-30 *)

(* the fraction leaving each fort (non-self links), once *)
Definition out_step (xs xd : array uint) (xf : array float) (j : int) (o : array float) : array float :=
  let s := xs.[j] in let d := xd.[j] in
  if s =? d then o else o.[s <- (o.[s] + xf.[j])%float].

(* an upper bound of |1 - out_x| *)
Definition coef (ou : array float) (x : int) : float :=
  (PrimFloat.abs (1 - ou.[x]) + f_s30)%float.

(* (2 cnt_x + 3) u, an upper bound of (2 cnt_x + 2) u *)
Definition kx (c : array int) (x : int) : float :=
  (of_uint63 (c.[x] + c.[x] + 3) * f_u)%float.

(* a float above its argument's real (proven with the accumulated factor) *)
Definition up (y : float) : float := (y * f_K1 + f_u)%float.

(* one link of the bound pass: what flows into d from e, and the sizes
   of the transfers touching s and d *)
Definition elink (xs xd : array uint) (xf : array float) (v e : array float)
    (j : int) (st : array float * array float) : array float * array float :=
  let s := xs.[j] in let d := xd.[j] in
  if s =? d then st else
  let a := PrimFloat.abs (xf.[j] * v.[s]) in
  let ein := fst st in let mac := snd st in
  let mac1 := mac.[d <- (mac.[d] + a)%float] in
  (ein.[d <- (ein.[d] + xf.[j] * e.[s])%float], mac1.[s <- (mac1.[s] + a)%float]).

(* one fort of the bound pass *)
Definition efort (ou : array float) (c : array int) (v e ein mac : array float)
    (x : int) (st : array float * bool) : array float * bool :=
  let y := up ((coef ou x * e.[x] + ein.[x]) + kx c x * ((PrimFloat.abs v.[x] + mac.[x]) + 1))%float in
  ((fst st).[x <- y], (snd st && (y <=? 1)%float)).

Definition ebound (n L : int) (xs xd : array uint) (xf : array float) (ou : array float) (c : array int)
    (v e : array float) : array float * bool :=
  let st := loop L (elink xs xd xf v e) 0 (PArray.make n 0%float, PArray.make n 0%float) in
  loop n (efort ou c v e (fst st) (snd st)) 0 (PArray.make n 0%float, true).

(* one time unit: strengths, then their error bounds *)
Definition tstep (n L : int) (xs xd : array uint) (xf : array float) (ou : array float) (c : array int)
    (j : int) (st : array float * array float * bool) : array float * array float * bool :=
  match st with
  | (v, e, ok) =>
    if ok then
      let r := ebound n L xs xd xf ou c v e in
      (unit_f L xs xd xf v, fst r, snd r)
    else st
  end.

(* the faced value's error bound and the magnitudes it adds *)
Definition fpair (n : int) (adj : array bool) (v e : array float) (i : int) : float * float :=
  loop n (fun k st => if adj.[i * n + k]
                      then ((fst st + e.[k])%float, (snd st + PrimFloat.abs v.[k])%float) else st)
       0 (e.[i], PrimFloat.abs v.[i]).

Definition fbound (n : int) (adj : array bool) (v e : array float) (nu : float) (i : int) : float :=
  let p := fpair n adj v e i in up (fst p + nu * (snd p + 1))%float.

Definition gmax (n : int) (g : int -> float) : float :=
  loop n (fun i m => if (m <? g i)%float then g i else m) 0 0%float.

(* B < 2^-20 (absolute) or B (2^20 + 1) < o (relative), exactly *)
Definition fcheck (B o : float) : bool :=
  let (mb, eb) := fex B in let (mo, eo) := fex o in
  dlt mb eb 1 (-20) || dlt (mb * 1048577) eb mo eo.

Definition timing_impl (xt : uint) (xu : array float) (xs xd : array uint)
    (xf : array float) : float :=
  let n := PArray.length xu in
  let L := PArray.length xs in
  let c := loop L (cnt_step xs xd) 0 (PArray.make n 0) in
  let ou := loop L (out_step xs xd xf) 0 (PArray.make n 0%float) in
  match loop xt (tstep n L xs xd xf ou c) 0 (xu, PArray.make n 0%float, true) with
  | (v, e, ok) =>
    if ok then
      let adj := loop L (adj_step n xs xd) 0 (PArray.make (n * n) false) in
      let o := loop n (fun i b => fmin b (faced_f n adj v i)) 1 (faced_f n adj v 0) in
      let nu := (of_uint63 (n + 1) * f_u)%float in
      let B := gmax n (fbound n adj v e nu) in
      if fcheck B o then o else timing_exact xt xu xs xd xf
    else timing_exact xt xu xs xd xf
  end.

(* ------------------------------------------------------------------ *)
(* Constants                                                           *)
(* ------------------------------------------------------------------ *)

Local Open Scope R_scope.

Definition timing : uint -> array float -> array uint -> array uint -> array float -> float :=
  timing_impl.
