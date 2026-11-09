(* Executable implementation and its required termination dependencies.
   Correctness proofs are in equationsolver_exact_proofs.v. *)
(* Implementation of equationsolver_exact.spec under steering v4.

   v4 = ../implem-bens-3 (steering v3), pasted, with the singular branch
   (float rank r < n) extended : the k = n - r dropped rows of Q, rounded,
   are checked exactly as reduced left-null vectors (any of them proving
   the system inconsistent gives Inconsistent) ; the padded n x n matrix B
   (rows outside D copied from A with the free columns C zeroed, row d_t
   the unit row of its paired free column c_t ; a nested array, the one
   nested table the steering allows) is certified injective by the
   eps < 1 half of the certificate ([certify_inj]), which decides
   Multiple ; otherwise v3's witness pair, then the exact fallback.
   The Prop side : [exact_exists_arr] (injective => surjective, for any
   float matrix), [lnull_extend] and [padded_math].

   v3 =../implem-bens-2 (steering v2) with the float decode [dec] made
   constant time : frshiftexp + normfr_mantissa + Uint63.to_Z, no copy of
   Prim2SF (no shr_fexp / Zdigits2), and i2z / z2i the primitives
   Uint63.to_Z / of_Z instead of bit loops.  Everything else is v2's.

   Part 1 (from ../implem-bens-1, the exact Gauss-Jordan over Z) : the
   fallback [solve_exact] and its proof, plus the elimination theory
   generalised to every scale of the right-hand side, which gives
   [exact_exists] (an injective system has a solution).
   Part 2 : the float path -- unverified Gaussian elimination with partial
   pivoting giving x~ and R ~ A^-1, the certificate ||I - RA|| < 1 and the
   residual bound (float dot products with a proven forward error bound,
   norm arithmetic exact on dyadics), the Multiple / Inconsistent witness
   checks (exact), and [solve]. *)

From Speck Require Import Prelude.
From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf.
From StdGalilei Require Import repr.
From StdGalilei Require Import bigint.
Import ListNotations.

Open Scope uint63_scope.
Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* The termination device and the loop combinator                      *)
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
(* Conversions int <-> Z : the primitives, constant time (steering v3) *)
(* ------------------------------------------------------------------ *)

(* Uint63.to_Z / of_Z, called directly. Optional extraction mappings in
   StdGalilei.extraction.ocaml.bigint target an external Bigint runtime;
   this implementation does not enable those mappings. *)
Definition i2z (x : int) : Z := to_Z x.
Definition z2i (z : Z) : int := of_Z z.

(* ------------------------------------------------------------------ *)
(* SF2Prim, for the fallback's output rounding only                    *)
(* ------------------------------------------------------------------ *)

Definition ldexp' (f : float) (e : Z) : float :=
  let e' := Z.max (Z.min e (Z.sub emax emin)) (Z.sub (Z.sub emin emax) (Zpos 1)) in
  ldshiftexp f (z2i (Z.add e' shift)).

Definition SF2Prim' (ef : spec_float) : float :=
  match ef with
  | S754_nan => nan
  | S754_zero false => zero
  | S754_zero true => neg_zero
  | S754_infinity false => infinity
  | S754_infinity true => neg_infinity
  | S754_finite s m e =>
    let pm := of_uint63 (z2i (Zpos m)) in
    let f := ldexp' pm e in
    if s then (-f)%float else f
  end.

(* a float, read exactly, in constant time : signed mantissa and exponent,
   (0, 0) when not finite or zero.  For a subnormal the mantissa is padded
   with trailing zeros (a non-canonical pair, the same value). *)
Definition dec (f : float) : Z * Z :=
  if is_nan f then (0%Z, 0%Z)
  else if is_zero f then (0%Z, 0%Z)
  else if is_infinity f then (0%Z, 0%Z)
  else
    let (r, e) := frshiftexp f in
    let m := to_Z (normfr_mantissa r) in
    ((if get_sign f then (- m)%Z else m), (to_Z e - shift - prec)%Z).

(* the integer f * 2^-E, for E at most the exponent of f *)
Definition scale (f : float) (E : Z) : Z := Z.shiftl (fst (dec f)) (snd (dec f) - E).

(* the rounding of a rational to the nearest binary64 (zero on overflow) *)
Definition qr (sx : bool) (mx : positive) (sy : bool) (my : positive) : float :=
  let '(mz, ez, lz) := SFdiv_core_binary prec emax (Zpos mx) 0 (Zpos my) 0 in
  match SpecFloat.binary_round_aux prec emax (xorb sx sy) mz ez lz with
  | S754_finite s m e => SF2Prim' (S754_finite s m e)
  | _ => zero
  end.

Definition qround (num den : Z) : float :=
  match num, den with
  | Zpos mx, Zpos my => qr false mx false my
  | Zpos mx, Zneg my => qr false mx true my
  | Zneg mx, Zpos my => qr true mx false my
  | Zneg mx, Zneg my => qr true mx true my
  | _, _ => zero
  end.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* The table T : n rows of w = n + 1 integers, row-major, the last
   column being the right-hand side. *)

(* the least exponent of a row (and 0) *)
Definition row_exp (n : int) (row : array float) (bi : float) : Z :=
  loop n (fun _ _ => true) (fun j E => Z.min E (snd (dec row.[j]))) 0
       (Z.min 0 (snd (dec bi))).

Definition fill_row (n w i : int) (row : array float) (E : Z) (T : array Z) : array Z :=
  loop n (fun _ _ => true) (fun j T => T.[i * w + j <- scale row.[j] E]) 0 T.

Definition build_step (a : array (array float)) (b : array float) (n w : int)
    (i : int) (T : array Z) : array Z :=
  let row := a.[i] in
  let bi := b.[i] in
  let E := row_exp n row bi in
  let T := fill_row n w i row E T in
  T.[i * w + n <- scale bi E].

Definition build (a : array (array float)) (b : array float) (n w : int) : array Z :=
  loop n (fun _ _ => true) (build_step a b n w) 0 (PArray.make (n * w) 0%Z).

(* the first row q in [r, n) with T[q][c] <> 0, n if none *)
Definition find_piv (T : array Z) (n w c r : int) : int :=
  loop n (fun _ _ => true)
    (fun i s => if s =? n then (if Z.eqb T.[i * w + c] 0 then s else i) else s) r n.

Definition swap_rows (T : array Z) (w q r : int) : array Z :=
  loop w (fun _ _ => true)
    (fun j T => let x := T.[r * w + j] in let y := T.[q * w + j] in
                T.[r * w + j <- y].[q * w + j <- x]) 0 T.

(* row i := a * row i - b * row r *)
Definition upd_row (T : array Z) (w i r : int) (a b : Z) : array Z :=
  loop w (fun _ _ => true)
    (fun j T => T.[i * w + j <- (a * T.[i * w + j] - b * T.[r * w + j])%Z]) 0 T.

Definition row_gcd (T : array Z) (w i : int) : Z :=
  loop w (fun _ _ => true) (fun j g => zgcd g T.[i * w + j]) 0 0%Z.

Definition div_row (T : array Z) (w i : int) (g : Z) : array Z :=
  loop w (fun _ _ => true) (fun j T => T.[i * w + j <- (T.[i * w + j] / g)%Z]) 0 T.

(* clear column c of row i with the pivot row r (pivot a), then divide
   the row by the gcd of its entries *)
Definition elim_row (w c r : int) (a : Z) (i : int) (T : array Z) : array Z :=
  if i =? r then T else
  let b := T.[i * w + c] in
  if Z.eqb b 0 then T else
  let T := upd_row T w i r a b in
  let g := row_gcd T w i in
  if Z.ltb 1 g then div_row T w i g else T.

(* Gauss-Jordan step on column c, r pivots so far *)
Definition col_step (n w : int) (c : int) (st : array Z * int) : array Z * int :=
  let (T, r) := st in
  let q := find_piv T n w c r in
  if q =? n then (T, r) else
  let T := swap_rows T w q r in
  let a := T.[r * w + c] in
  (loop n (fun _ _ => true) (elim_row w c r a) 0 T, r + 1).

Definition eliminate (n w : int) (T : array Z) : array Z * int :=
  loop n (fun _ _ => true) (col_step n w) 0 (T, 0).

Definition inconsistent (T : array Z) (n w r : int) : bool :=
  loop n (fun _ _ => true) (fun i fl => orb fl (negb (Z.eqb T.[i * w + n] 0))) r false.

Definition output (T : array Z) (n w : int) : array float :=
  loop n (fun _ _ => true)
    (fun i out => out.[i <- qround T.[i * w + n] T.[i * w + i]]) 0 (PArray.make n zero).

Definition solve_exact (n : uint) (a : array (array float)) (b : array float) : outcome (array float) :=
  let w := n + 1 in
  let T := build a b n w in
  let (T, r) := eliminate n w T in
  if inconsistent T n w r then Inconsistent
  else if r <? n then Multiple
  else Unique (output T n w).

(* ------------------------------------------------------------------ *)
(* Floats, exactly                                                     *)
(* ------------------------------------------------------------------ *)

From Flocq Require Import Core IEEE754.BinarySingleNaN.
From Flocq Require IEEE754.PrimFloat.
From StdGalilei Require Import repr_float.
Notation float := PrimFloat.float.
Local Instance prec53' : Prec_gt_0 53 := eq_refl _.
Local Instance fexp64_valid' : Valid_exp fexp64 := FLT_exp_valid _ _.

(* ------------------------------------------------------------------ *)
(* Linear systems over integer tables, Prop side                       *)
(* ------------------------------------------------------------------ *)

Open Scope R_scope.

Fixpoint sumR (f : nat -> R) (k : nat) : R :=
  match k with
  | O => 0
  | S k => sumR f k + f k
  end.

Lemma sumR_ext : forall f g k, (forall j, (j < k)%nat -> f j = g j) -> sumR f k = sumR g k.
Proof.
  intros f g k H. induction k as [| k IH]; simpl; [reflexivity |].
  rewrite IH by (intros; apply H; lia). rewrite (H k) by lia. reflexivity.
Qed.

Lemma sumR_lin : forall f g c1 c2 k,
  sumR (fun j => c1 * f j + c2 * g j) k = c1 * sumR f k + c2 * sumR g k.
Proof. intros f g c1 c2 k. induction k as [| k IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma sumR_scal : forall f c k, sumR (fun j => c * f j) k = c * sumR f k.
Proof. intros f c k. induction k as [| k IH]; simpl; [ring | rewrite IH; ring]. Qed.

Section Systems.
Variable N : nat.

Definition rowsum (V : nat -> nat -> Z) (i : nat) (x : nat -> R) : R :=
  sumR (fun j => IZR (V i j) * x j) N.

Definition roweq (V : nat -> nat -> Z) (i : nat) (x : nat -> R) : Prop :=
  rowsum V i x = IZR (V i N).

Definition sol (V : nat -> nat -> Z) (x : nat -> R) : Prop :=
  forall i, (i < N)%nat -> roweq V i x.

Definition equiv (V V' : nat -> nat -> Z) : Prop := forall x, sol V x <-> sol V' x.

Lemma equiv_refl : forall V, equiv V V.
Proof. intros V x. tauto. Qed.

Lemma equiv_trans : forall V1 V2 V3, equiv V1 V2 -> equiv V2 V3 -> equiv V1 V3.
Proof. intros V1 V2 V3 H1 H2 x. specialize (H1 x). specialize (H2 x). tauto. Qed.

Lemma rowsum_ext : forall V V' i i' x, (forall j, (j < N)%nat -> V' i' j = V i j) ->
  rowsum V' i' x = rowsum V i x.
Proof. intros V V' i i' x H. apply sumR_ext. intros j Hj. rewrite H by exact Hj. reflexivity. Qed.

(* row i := (a * row i - b * row r) / g, the other rows unchanged *)
Definition rowop (V V' : nat -> nat -> Z) (i r : nat) (a b : Z) : Prop :=
  (forall k j, k <> i -> (k < N)%nat -> (j <= N)%nat -> V' k j = V k j) /\
  exists g, g <> 0%Z /\ forall j, (j <= N)%nat -> (g * V' i j = a * V i j - b * V r j)%Z.

Lemma rowop_equiv : forall V V' i r a b, (i < N)%nat -> (r < N)%nat -> i <> r -> a <> 0%Z ->
  rowop V V' i r a b -> equiv V V'.
Proof.
  intros V V' i r a b Hi Hr Hir Ha [HV (g & Hg & Hrow)] x.
  assert (Ks : forall k, k <> i -> (k < N)%nat -> rowsum V' k x = rowsum V k x /\ V' k N = V k N).
  { intros k Hki HkN. split; [apply rowsum_ext; intros j Hj; apply HV; lia | apply HV; lia]. }
  assert (Si : IZR g * rowsum V' i x = IZR a * rowsum V i x + - IZR b * rowsum V r x).
  { unfold rowsum. rewrite <- sumR_scal, <- sumR_lin. apply sumR_ext. intros j Hj.
    rewrite <- Rmult_assoc, <- mult_IZR, Hrow by lia. rewrite minus_IZR, !mult_IZR. ring. }
  assert (Ni : IZR g * IZR (V' i N) = IZR a * IZR (V i N) + - IZR b * IZR (V r N)).
  { rewrite <- mult_IZR, Hrow by lia. rewrite minus_IZR, !mult_IZR. ring. }
  assert (Hg' : IZR g <> 0) by (apply not_0_IZR; exact Hg).
  assert (Ha' : IZR a <> 0) by (apply not_0_IZR; exact Ha).
  unfold sol, roweq. split; intros H k Hk.
  - destruct (Nat.eq_dec k i) as [-> | Hne].
    + apply (Rmult_eq_reg_l (IZR g)); [| exact Hg']. rewrite Si, Ni, (H i Hi), (H r Hr). ring.
    + destruct (Ks k Hne Hk) as [-> ->]. apply H; exact Hk.
  - assert (Er : rowsum V r x = IZR (V r N)).
    { destruct (Ks r (not_eq_sym Hir) Hr) as [<- <-]. apply H; exact Hr. }
    destruct (Nat.eq_dec k i) as [-> | Hne].
    + apply (Rmult_eq_reg_l (IZR a)); [| exact Ha'].
      assert (E1 : IZR g * rowsum V' i x = IZR g * IZR (V' i N)) by (rewrite (H i Hi); reflexivity).
      rewrite Si, Ni, Er in E1. lra.
    + destruct (Ks k Hne Hk) as [<- <-]. apply H; exact Hk.
Qed.

(* swapping rows p and r *)
Definition sw (p r k : nat) : nat := if Nat.eqb k p then r else if Nat.eqb k r then p else k.

Lemma sw_lt : forall p r k, (p < N)%nat -> (r < N)%nat -> (k < N)%nat -> (sw p r k < N)%nat.
Proof. intros p r k Hp Hr Hk. unfold sw. destruct (Nat.eqb k p), (Nat.eqb k r); lia. Qed.

Lemma sw_sw : forall p r k, sw p r (sw r p k) = k.
Proof.
  intros p r k. unfold sw.
  destruct (Nat.eqb_spec k r) as [E1 | E1]; destruct (Nat.eqb_spec k p) as [E2 | E2];
    repeat (rewrite ?Nat.eqb_refl; simpl);
    repeat match goal with |- context [PeanoNat.Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b) end; lia.
Qed.

Lemma swap_equiv : forall V V' p r, (p < N)%nat -> (r < N)%nat ->
  (forall k j, (k < N)%nat -> (j <= N)%nat -> V' k j = V (sw p r k) j) -> equiv V V'.
Proof.
  intros V V' p r Hp Hr HV x. unfold sol, roweq.
  assert (E : forall k, (k < N)%nat -> rowsum V' k x = rowsum V (sw p r k) x /\ V' k N = V (sw p r k) N).
  { intros k Hk. split; [apply rowsum_ext; intros j Hj; apply HV; lia | apply HV; lia]. }
  split; intros H k Hk.
  - destruct (E k Hk) as [-> ->]. apply H, sw_lt; assumption.
  - pose proof (sw_sw p r k) as Hs. rewrite <- Hs.
    assert (Hk' : (sw r p k < N)%nat) by (apply sw_lt; assumption).
    destruct (E _ Hk') as [<- <-]. apply H; exact Hk'.
Qed.

(* the same table with its right-hand side multiplied by t : t = 1 is the
   system itself, t = 0 its homogeneous system *)
Definition sc (t : Z) (V : nat -> nat -> Z) (i j : nat) : Z :=
  if Nat.eqb j N then (t * V i j)%Z else V i j.

(* equivalence of the systems for every scale of the right-hand side *)
Definition equivG (V V' : nat -> nat -> Z) : Prop :=
  forall t x, sol (sc t V) x <-> sol (sc t V') x.

Definition hsol (V : nat -> nat -> Z) (x : nat -> R) : Prop :=
  forall i, (i < N)%nat -> rowsum V i x = 0.

Lemma equivG_refl : forall V, equivG V V.
Proof. intros V t x. tauto. Qed.

Lemma equivG_trans : forall V1 V2 V3, equivG V1 V2 -> equivG V2 V3 -> equivG V1 V3.
Proof. intros V1 V2 V3 H1 H2 t x. specialize (H1 t x). specialize (H2 t x). tauto. Qed.

Lemma sol_extV : forall V V' x, (forall i j, (i < N)%nat -> (j <= N)%nat -> V' i j = V i j) ->
  sol V x -> sol V' x.
Proof.
  intros V V' x H Hs i Hi. unfold roweq. rewrite (rowsum_ext V V' i i x) by (intros; apply H; lia).
  rewrite H by lia. apply Hs, Hi.
Qed.

Lemma sol_sc1 : forall V x, sol (sc 1 V) x <-> sol V x.
Proof.
  intros V x. split; apply sol_extV; intros i j Hi Hj; unfold sc;
    destruct (Nat.eqb j N); try reflexivity; ring.
Qed.

Lemma sol_sc0 : forall V x, sol (sc 0 V) x <-> hsol V x.
Proof.
  intros V x. unfold sol, roweq, hsol. split; intros H i Hi; specialize (H i Hi).
  - rewrite (rowsum_ext V (sc 0 V) i i x) in H; [rewrite H; unfold sc; rewrite Nat.eqb_refl; reflexivity |].
    intros j Hj. unfold sc. destruct (Nat.eqb_spec j N); [lia | reflexivity].
  - rewrite (rowsum_ext V (sc 0 V) i i x); [rewrite H; unfold sc; rewrite Nat.eqb_refl; reflexivity |].
    intros j Hj. unfold sc. destruct (Nat.eqb_spec j N); [lia | reflexivity].
Qed.

Lemma equivG_sol : forall V V', equivG V V' -> forall x, sol V x <-> sol V' x.
Proof.
  intros V V' H x. split; intros Hx; apply sol_sc1; apply (H 1%Z x); apply sol_sc1; exact Hx.
Qed.

Lemma equivG_hsol : forall V V', equivG V V' -> forall x, hsol V x <-> hsol V' x.
Proof.
  intros V V' H x. split; intros Hx; apply sol_sc0; apply (H 0%Z x); apply sol_sc0; exact Hx.
Qed.

Lemma rowop_equivG : forall V V' i r a b, (i < N)%nat -> (r < N)%nat -> i <> r -> a <> 0%Z ->
  rowop V V' i r a b -> equivG V V'.
Proof.
  intros V V' i r a b Hi Hr Hir Ha [HK (g & Hg & HG)] t.
  apply (rowop_equiv (sc t V) (sc t V') i r a b); auto.
  split.
  - intros k j Hk HkN Hj. unfold sc. rewrite HK by assumption. reflexivity.
  - exists g. split; [exact Hg |]. intros j Hj. unfold sc.
    destruct (Nat.eqb j N); [| apply HG; exact Hj].
    replace (g * (t * V' i j))%Z with (t * (g * V' i j))%Z by ring. rewrite HG by exact Hj. ring.
Qed.

Lemma swap_equivG : forall V V' p r, (p < N)%nat -> (r < N)%nat ->
  (forall k j, (k < N)%nat -> (j <= N)%nat -> V' k j = V (sw p r k) j) -> equivG V V'.
Proof.
  intros V V' p r Hp Hr HV t. apply (swap_equiv (sc t V) (sc t V') p r Hp Hr).
  intros k j Hk Hj. unfold sc. rewrite HV by assumption. reflexivity.
Qed.

End Systems.

(* ------------------------------------------------------------------ *)
(* The table, machine side                                             *)
(* ------------------------------------------------------------------ *)

Open Scope uint63_scope.

(* ------------------------------------------------------------------ *)
(* The forward error of a float dot product                           *)
(* ------------------------------------------------------------------ *)

Open Scope R_scope.

Open Scope uint63_scope.

(* the sequential float dot product of X[ox ..] and Y[oy ..] over len terms *)
Definition fdot (X : array float) (ox : int) (Y : array float) (oy : int) (len : int) : float :=
  loop len (fun _ _ => true) (fun k s => (s + X.[ox + k] * Y.[oy + k])%float) 0 zero.

(* ------------------------------------------------------------------ *)
(* Exact dyadic numbers m * 2^e (Z mantissa and exponent) : the        *)
(* certificate's O(n^2) norm and bound arithmetic and the witness      *)
(* checks                                                             *)
(* ------------------------------------------------------------------ *)

Definition dy := (Z * Z)%type.

Definition dadd (x y : dy) : dy :=
  let (m1, e1) := x in let (m2, e2) := y in
  if Z.leb e1 e2 then ((m1 + Z.shiftl m2 (e2 - e1))%Z, e1)
  else ((Z.shiftl m1 (e1 - e2) + m2)%Z, e2).

Definition dmul (x y : dy) : dy := ((fst x * fst y)%Z, (snd x + snd y)%Z).
Definition dabs (x : dy) : dy := (Z.abs (fst x), snd x).
Definition dneg (x : dy) : dy := ((- fst x)%Z, snd x).
Definition dleb (x y : dy) : bool := Z.leb 0 (fst (dadd y (dneg x))).
Definition dltb (x y : dy) : bool := Z.ltb 0 (fst (dadd y (dneg x))).
Definition dzero (x : dy) : bool := Z.eqb (fst x) 0.
Definition dmax (x y : dy) : dy := if dleb x y then y else x.
Definition d0 : dy := (0%Z, 0%Z).
Definition dint (z : Z) : dy := (z, 0%Z).

(* ------------------------------------------------------------------ *)
(* The certificate, on real matrices                                  *)
(* ------------------------------------------------------------------ *)

Open Scope R_scope.

(* ================================================================== *)
(* The program of the float path                                      *)
(* ================================================================== *)

Open Scope uint63_scope.

(* ------------------------------------------------------------------ *)
(* Unverified numerics : Gaussian elimination with partial pivoting   *)
(* (CLRS ch. 28) on M = [A | b] (n x (n + 1), flat) and on Q = I       *)
(* (n x n, flat), back substitution giving the candidate x~ and the    *)
(* approximate inverse R (in Q).  Nothing is proven of them : the      *)
(* certificate below checks what they produce.                         *)
(* ------------------------------------------------------------------ *)

Definition init_M (xa : array (array float)) (xb : array float) (n w : int) : array float :=
  loop n (fun _ _ => true)
    (fun i M => let row := xa.[i] in
       let M := loop n (fun _ _ => true) (fun j M => M.[i * w + j <- row.[j]]) 0 M in
       M.[i * w + n <- xb.[i]]) 0 (PArray.make (n * w) zero).

Definition init_Q (n : int) : array float :=
  loop n (fun _ _ => true) (fun i Q => Q.[i * n + i <- one]) 0 (PArray.make (n * n) zero).

(* the pivot threshold of each column : 2^-40 times its largest magnitude
   in A ; it only steers the candidates (which column looks free), it
   decides nothing *)
Definition thr_scale : float := 0x1p-40%float.

Definition col_thr (xa : array (array float)) (n : int) : array float :=
  loop n (fun _ _ => true)
    (fun j T => let m := loop n (fun _ _ => true)
                   (fun i m => let v := PrimFloat.abs (xa.[i].[j]) in if (m <? v)%float then v else m) 0 zero in
                T.[j <- (m * thr_scale)%float]) 0 (PArray.make n zero).

Definition swap_f (T : array float) (w p r : int) : array float :=
  loop w (fun _ _ => true)
    (fun j T => let x := T.[r * w + j] in let y := T.[p * w + j] in
                T.[r * w + j <- y].[p * w + j <- x]) 0 T.

(* row i -= f * row r, columns [lo, w) *)
Definition axpy_row (T : array float) (w i r lo : int) (f : float) : array float :=
  loop w (fun _ _ => true)
    (fun j T => T.[i * w + j <- (T.[i * w + j] - f * T.[r * w + j])%float]) lo T.

Definition scale_row (T : array float) (w i : int) (piv : float) : array float :=
  loop w (fun _ _ => true) (fun j T => T.[i * w + j <- (T.[i * w + j] / piv)%float]) 0 T.

(* a fresh array of length n, cell i = f i (v4 : the padded matrix, the
   row permutation's start) *)
Definition tab {T : Type} (n : int) (d : T) (f : int -> T) : array T :=
  loop n (fun _ _ => true) (fun i t => t.[i <- f i]) 0 (PArray.make n d).

(* v4 : fs_perm, the original index of the row now at each position
   (unverified, validated by the left-null check) *)
Record fstate := FS { fs_M : array float; fs_Q : array float; fs_r : int; fs_pc : array int;
                      fs_perm : array int }.

Definition fwd_col (n w : int) (thr : array float) (c : int) (st : fstate) : fstate :=
  let r := fs_r st in
  if r <? n then
    let M := fs_M st in
    let '(p, mx) := loop n (fun _ _ => true)
        (fun i pm => let v := PrimFloat.abs M.[i * w + c] in
                     if (snd pm <? v)%float then (i, v) else pm) r (r, zero) in
    if (mx <=? thr.[c])%float then st
    else
      let M := swap_f M w p r in
      let Q := swap_f (fs_Q st) n p r in
      let piv := M.[r * w + c] in
      let '(M, Q) := loop n (fun _ _ => true)
          (fun i mq => let '(M, Q) := mq in
             let f := (M.[i * w + c] / piv)%float in
             let M := axpy_row M w i r (c + 1) f in
             (M.[i * w + c <- zero], axpy_row Q n i r 0 f)) (r + 1) (M, Q) in
      let pm := fs_perm st in
      let x := pm.[p] in let y := pm.[r] in
      FS M Q (r + 1) (fs_pc st).[r <- c] pm.[p <- y].[r <- x]
  else st.

Definition forward (n w : int) (thr : array float) (M Q : array float) : fstate :=
  loop n (fun _ _ => true) (fwd_col n w thr) 0 (FS M Q 0 (PArray.make n 0) (tab n 0 (fun i => i))).

(* back substitution on the triangular M (rank n), the same operations on Q *)
Definition backsub (n w : int) (M Q : array float) : array float * array float :=
  loop n (fun _ _ => true)
    (fun t mq => let '(M, Q) := mq in
       let i := n - 1 - t in
       let piv := M.[i * w + i] in
       let xi := (M.[i * w + n] / piv)%float in
       let M := M.[i * w + n <- xi] in
       let Q := scale_row Q n i piv in
       loop i (fun _ _ => true)
         (fun i' mq => let '(M, Q) := mq in
            let f := M.[i' * w + i] in
            (M.[i' * w + n <- (M.[i' * w + n] - f * xi)%float], axpy_row Q n i' i 0 f)) 0 (M, Q))
    0 (M, Q).

Definition get_col (M : array float) (n w c : int) : array float :=
  loop n (fun _ _ => true) (fun i x => x.[i <- M.[i * w + c]]) 0 (PArray.make n zero).

Definition get_row (Q : array float) (n i : int) : array float :=
  loop n (fun _ _ => true) (fun k x => x.[k <- Q.[i * n + k]]) 0 (PArray.make n zero).

(* witness candidates on the echelon form of rank r < n *)
Definition free_col (pc : array int) (n r : int) : int :=
  let isp := loop r (fun _ _ => true) (fun t isp => isp.[pc.[t] <- true]) 0 (PArray.make n false) in
  loop n (fun _ _ => true) (fun c f => if andb (f =? n) (negb isp.[c]) then c else f) 0 n.

(* v4 : the k free columns, those not in pc[0..r), in increasing order
   (cells k .. n-1 unused) *)
Definition free_cols (pc : array int) (n r : int) : array int :=
  let isp := loop r (fun _ _ => true) (fun t isp => isp.[pc.[t] <- true]) 0 (PArray.make n false) in
  fst (loop n (fun _ _ => true)
         (fun c st => let '(fc, cnt) := st in
            if isp.[c] then (fc, cnt) else (fc.[cnt <- c], cnt + 1)) 0 (PArray.make n 0, 0)).

(* x[pc t] := (rhs t - sum_{j > pc t} M[t][j] x[j]) / M[t][pc t], t = r-1 .. 0 *)
Definition echelon_solve (M : array float) (pc : array int) (n w r : int) (homog : bool)
    (x : array float) : array float :=
  loop r (fun _ _ => true)
    (fun s x => let t := r - 1 - s in let c := pc.[t] in
       let s0 := if homog then zero else M.[t * w + n] in
       let acc := loop n (fun _ _ => true)
                    (fun j acc => (acc - M.[t * w + j] * x.[j])%float) (c + 1) s0 in
       x.[c <- (acc / M.[t * w + c])%float]) 0 x.

(* a float, read exactly, rounded to a fraction h / k with k <= 2^30 by
   continued fractions (stops at relative distance 2^-40) *)
Definition rat1 (f : float) : Z * Z :=
  let (m, e) := dec f in
  if Z.leb 0 e then (Z.shiftl m e, 1%Z) else
  let den := Z.shiftl 1 (- e) in
  let st := loop 64 (fun _ st => negb (snd st))
    (fun _ st => let '(an, ad, h1, h0, k1, k0) := fst st in
       let q := (an / ad)%Z in
       let h := (q * h1 + h0)%Z in let k := (q * k1 + k0)%Z in
       if Z.ltb 1073741824 k then (fst st, true)
       else let rem := (an - q * ad)%Z in
            let close := Z.leb (Z.shiftl (Z.abs (m * k - h * den)) 40) (Z.abs m * k) in
            ((ad, rem, h, h1, k, k1), orb (Z.eqb rem 0) close))
    0 ((m, den, 1%Z, 0%Z, 0%Z, 1%Z), false) in
  let '(_, _, h1, _, k1, _) := fst st in
  if Z.ltb 0 k1 then (h1, k1) else (0%Z, 1%Z).

(* a float vector rounded to fractions, over a common denominator L :
   the integer numerators and L *)
Definition ratvec (x : array float) (n : int) : array Z * Z :=
  let '(H, K, L) := loop n (fun _ _ => true)
      (fun j st => let '(H, K, L) := st in let (h, k) := rat1 x.[j] in
         (H.[j <- h], K.[j <- k], (L / zgcd L k * k)%Z)) 0
      (PArray.make n 0%Z, PArray.make n 1%Z, 1%Z) in
  (loop n (fun _ _ => true) (fun j P => P.[j <- (H.[j] * (L / K.[j]))%Z]) 0 (PArray.make n 0%Z), L).

(* ------------------------------------------------------------------ *)
(* Verified : the certificate and the witness checks                  *)
(* ------------------------------------------------------------------ *)

Definition dsumf (len : int) (f : int -> dy) : dy :=
  loop len (fun _ _ => true) (fun k acc => dadd acc (f k)) 0 d0.

Definition allf (len : int) (p : int -> bool) : bool :=
  loop len (fun _ _ => true) (fun k b => andb b (p k)) 0 true.

(* sum of f k d_k, with d_k := g k, and whether every d_k is finite *)
Definition dsumb (len : int) (g : int -> float) (f : int -> float -> dy) : dy * bool :=
  loop len (fun _ _ => true)
    (fun k st => let d := g k in (dadd (fst st) (f k d), andb (snd st) (PrimFloat.is_finite d))) 0 (d0, true).

(* the largest first component of h i, and whether every second one holds *)
Definition maxb (len : int) (h : int -> dy * bool) : dy * bool :=
  loop len (fun _ _ => true)
    (fun i st => let r := h i in (dmax (fst st) (fst r), andb (snd st) (snd r))) 0 (d0, true).

Definition dsub (x y : dy) : dy := dadd x (dneg y).
Definition d1 : dy := (1%Z, 0%Z).

Definition transpose (xa : array (array float)) (n : int) : array float :=
  loop n (fun _ _ => true)
    (fun i T => let row := xa.[i] in
       loop n (fun _ _ => true) (fun j T => T.[j * n + i <- row.[j]]) 0 T) 0 (PArray.make (n * n) zero).

(* S[k] = sum_j |A[k][j]| *)
Definition rowabs (xa : array (array float)) (n : int) : array dy :=
  loop n (fun _ _ => true)
    (fun k S => let row := xa.[k] in S.[k <- dsumf n (fun j => dabs (dec row.[j]))]) 0 (PArray.make n d0).

(* row i of E = I - R A : sum_j |delta_ij - fl(R_i . A_.j)| plus the error
   bound of the n dot products ; every dot product checked finite *)
Definition erow (n : int) (Q AT : array float) (S : array dy) (lamd mud2 : dy) (i : int) : dy * bool :=
  let e := dsumb n (fun j => fdot Q (i * n) AT (j * n) n)
             (fun j d => dabs (dsub (dint (if i =? j then 1%Z else 0%Z)) (dec d))) in
  let rr := dsumf n (fun k => dmul (dabs (dec Q.[i * n + k])) S.[k]) in
  (dadd (dadd (fst e) (dmul lamd rr)) mud2, snd e).

Definition rowR (n : int) (Q : array float) (i : int) : dy * bool :=
  (dsumf n (fun k => dabs (dec Q.[i * n + k])), true).

(* |b_i - fl(A_i . x~)| plus its error bound *)
Definition resid (n : int) (xa : array (array float)) (xb xt : array float) (lamd mud1 : dy) (i : int) : dy * bool :=
  let row := xa.[i] in
  let d := fdot row 0 xt 0 n in
  (dadd (dadd (dabs (dsub (dec xb.[i]) (dec d)))
              (dmul lamd (dsumf n (fun j => dabs (dmul (dec row.[j]) (dec xt.[j]))))))
        mud1,
   PrimFloat.is_finite d).

Definition certify (n : int) (xa : array (array float)) (xb : array float) (AT Q xt : array float) : bool :=
  let nz := i2z n in
  let lamd := ((3 * nz)%Z, (-53)%Z) in
  let mud1 := ((3 * nz)%Z, (-1075)%Z) in
  let mud2 := ((3 * nz * nz)%Z, (-1075)%Z) in
  let S := rowabs xa n in
  let '(eps, ok1) := maxb n (erow n Q AT S lamd mud2) in
  let '(rho, _) := maxb n (rowR n Q) in
  let '(sig, ok2) := maxb n (resid n xa xb xt lamd mud1) in
  andb (andb (andb ok1 ok2) (PArray.length xt =? n))
       (andb (dltb eps d1) (dleb (dadd (dmul (1000%Z, 0%Z) (dmul rho sig)) eps) d1)).

(* exact dot product of floats X[o ..] with integers Y[0 ..] *)
Definition zdot (X : array float) (o : int) (Y : array Z) (len : int) : dy :=
  dsumf len (fun k => dmul (dec X.[o + k]) (dint Y.[k])).

(* y^T A = 0 and y^T b <> 0 *)
Definition chk_incons (AT : array float) (xb : array float) (n : int) (y : array Z) : bool :=
  andb (allf n (fun j => dzero (zdot AT (j * n) y n))) (negb (dzero (zdot xb 0 y n))).

(* A p = q b, A v = 0, q <> 0, v <> 0 *)
Definition chk_mult (xa : array (array float)) (xb : array float) (n : int) (p : array Z) (q : Z)
    (v : array Z) : bool :=
  andb (andb (negb (Z.eqb q 0)) (negb (allf n (fun j => Z.eqb v.[j] 0))))
       (allf n (fun i => let row := xa.[i] in
                         andb (dzero (dsub (zdot row 0 p n) (dmul (dint q) (dec xb.[i]))))
                              (dzero (zdot row 0 v n)))).

(* ------------------------------------------------------------------ *)
(* v4 : the padded certificate of the singular branch                 *)
(* ------------------------------------------------------------------ *)

(* the candidate left-null vector of dropped row t : row r + t of Q,
   rounded to integers over a common denominator *)
Definition yv (Q : array float) (n r t : int) : array Z := fst (ratvec (get_row Q n (r + t)) n).

(* D : flag of every d_t = perm[r + t], t < k, and tix[d_t] := t (the last
   t written) *)
Definition mark_D (perm : array int) (n r k : int) : array bool * array int :=
  loop k (fun _ _ => true)
    (fun t st => let d := perm.[r + t] in ((fst st).[d <- true], (snd st).[d <- t]))
    0 (PArray.make n false, PArray.make n 0).

(* C : flag of every c_t = fc[t], t < k *)
Definition mark_C (fc : array int) (n k : int) : array bool :=
  loop k (fun _ _ => true) (fun t C => C.[fc.[t] <- true]) 0 (PArray.make n false).

(* y is a reduced left-null vector of row d : y^T A = 0, y^T b = 0,
   y_d <> 0, y_i = 0 for every other i in D *)
Definition chk_red (AT xb : array float) (n : int) (y : array Z) (d : int) (Df : array bool) : bool :=
  andb (andb (allf n (fun j => dzero (zdot AT (j * n) y n))) (dzero (zdot xb 0 y n)))
       (andb (negb (Z.eqb y.[d] 0))
             (allf n (fun i => orb (negb Df.[i]) (orb (i =? d) (Z.eqb y.[i] 0))))).

(* over the k dropped rows : does one of them prove the system
   inconsistent, and are all of them reduced left-null vectors (with r < n,
   d_t < n and c_t < n) *)
Definition scan_null (AT xb Q : array float) (perm fc : array int) (Df : array bool) (n r k : int)
    : bool * bool :=
  loop k (fun _ _ => true)
    (fun t s => let y := yv Q n r t in let d := perm.[r + t] in
       (orb (fst s) (chk_incons AT xb n y),
        andb (snd s) (andb (andb (d <? n) (fc.[t] <? n)) (chk_red AT xb n y d Df))))
    0 (false, r <? n).

(* the padded matrix B, entry (i, j) *)
Definition bentry (xa : array (array float)) (Df : array bool) (tix fc : array int) (Cf : array bool)
    (i j : int) : float :=
  if Df.[i] then (if j =? fc.[tix.[i]] then one else zero)
  else if Cf.[j] then zero else xa.[i].[j].

(* B as fresh rows : the one nested table besides the input (steering v4) *)
Definition padB (xa : array (array float)) (n : int) (Df : array bool) (tix fc : array int)
    (Cf : array bool) : array (array float) :=
  tab n (PArray.make 0 zero) (fun i => tab n zero (fun j => bentry xa Df tix fc Cf i j)).

(* the eps < 1 half of [certify] : ||I - Q A||_inf < 1, rigorously *)
Definition certify_inj (n : int) (xa : array (array float)) (AT Q : array float) : bool :=
  let nz := i2z n in
  let lamd := ((3 * nz)%Z, (-53)%Z) in
  let mud2 := ((3 * nz * nz)%Z, (-1075)%Z) in
  let S := rowabs xa n in
  let '(eps, ok1) := maxb n (erow n Q AT S lamd mud2) in
  andb ok1 (dltb eps d1).

(* unverified elimination on B for an approximate inverse, then the
   verified injectivity certificate *)
Definition padded_ok (xa : array (array float)) (n : int) (Df : array bool) (tix fc : array int)
    (Cf : array bool) : bool :=
  let B := padB xa n Df tix fc Cf in
  let w := n + 1 in
  let st := forward n w (col_thr B n) (init_M B (PArray.make n zero) n w) (init_Q n) in
  if fs_r st =? n then
    certify_inj n B (transpose B n) (snd (backsub n w (fs_M st) (fs_Q st)))
  else false.

Definition solve (n : uint) (xa : array (array float)) (xb : array float) : outcome (array float) :=
  let w := n + 1 in
  let st := forward n w (col_thr xa n) (init_M xa xb n w) (init_Q n) in
  let AT := transpose xa n in
  if fs_r st =? n then
    let '(M, Q) := backsub n w (fs_M st) (fs_Q st) in
    let xt := get_col M n w n in
    if certify n xa xb AT Q xt then Unique xt else solve_exact n xa xb
  else
    let M := fs_M st in
    let r := fs_r st in
    let k := if r <? n then n - r else 0 in
    let fc := free_cols (fs_pc st) n r in
    let mD := mark_D (fs_perm st) n r k in
    let Df := fst mD in
    let tix := snd mD in
    let Cf := mark_C fc n k in
    let sc := scan_null AT xb (fs_Q st) (fs_perm st) fc Df n r k in
    if fst sc then Inconsistent
    else if (if snd sc then padded_ok xa n Df tix fc Cf else false) then Multiple
    else
      let f := free_col (fs_pc st) n r in
      let x0 := echelon_solve M (fs_pc st) n w r false (PArray.make n zero) in
      let v := echelon_solve M (fs_pc st) n w r true (PArray.make n zero).[f <- one] in
      let '(p, q) := ratvec x0 n in
      if chk_mult xa xb n p q (fst (ratvec v n)) then Multiple else solve_exact n xa xb.

(* ------------------------------------------------------------------ *)
(* The certificate, machine side                                      *)
(* ------------------------------------------------------------------ *)

Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(* v4 : the padded certificate, machine side                          *)
(* ------------------------------------------------------------------ *)

Open Scope uint63_scope.

Open Scope R_scope.
