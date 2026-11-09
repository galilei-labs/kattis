(* Executable implementation and its required termination dependencies.
   Correctness proofs are in palindromes_proofs.v. *)
(* Implementation of palindromes (palindromes.spec).

   Code.  Manacher over the 2n doubled centres q = a + b (cnt.[q] = number
   of palindromic candidates [q/2 - k, (q+1)/2 + k]); every query [l, r] is
   split by centre parity and at its middle into four clipped sums
   sum_{i < T} min(d_i, i - A + 1)^+, answered offline: queries bucketed by
   T (head/next lists), a sweep over T inserting one centre at a time into
   two Fenwick trees (constant and slope of a piecewise linear function of
   A).  Wrapping 63-bit arithmetic, exact since every answer is < 2^63.
   Termination: erased Acc (Zwf 0) on Z measures, as in the template.  No
   nat, no lists, flat arrays only. *)

From Palindromes.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63 String Ascii PrimString.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* The low bit                                                         *)
(* ------------------------------------------------------------------ *)

Section LowBit.
Local Open Scope Z_scope.

Lemma land2 : forall a b e f, (e = 0 \/ e = 1) -> (f = 0 \/ f = 1) ->
  Z.land (2 * a + e) (2 * b + f) = 2 * Z.land a b + e * f.
Proof.
  intros a b e f He Hf. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec.
  destruct (Z.eq_dec k 0) as [-> | Hk0].
  - destruct He as [-> | ->], Hf as [-> | ->]; rewrite ?Z.add_0_r, ?Z.mul_0_r, ?Z.mul_1_r;
      rewrite ?Z.testbit_even_0, ?Z.testbit_odd_0; reflexivity.
  - replace k with (Z.succ (k - 1)) by lia.
    destruct He as [-> | ->], Hf as [-> | ->]; rewrite ?Z.add_0_r, ?Z.mul_0_r, ?Z.mul_1_r,
      ?Z.add_0_r;
      rewrite ?Z.testbit_even_succ, ?Z.testbit_odd_succ, ?Z.land_spec by lia; reflexivity.
Qed.

Definition lowZ (j : Z) : Z := j - Z.land j (j - 1).

Lemma land_pow : forall c w, 0 <= c -> 0 <= w ->
  Z.land (2 ^ c * (2 * w + 1)) (2 ^ c * (2 * w + 1) - 1) = 2 ^ c * (2 * w + 1) - 2 ^ c.
Proof.
  intros c w Hc Hw. pattern c. apply natlike_ind; [| | exact Hc].
  - change (2 ^ 0) with 1. rewrite !Z.mul_1_l.
    replace (2 * w + 1 - 1) with (2 * w + 0) by lia.
    rewrite land2 by lia. rewrite Z.land_diag. lia.
  - intros x Hx IH. rewrite Z.pow_succ_r by lia.
    set (X := 2 ^ x * (2 * w + 1)) in *.
    replace (2 * 2 ^ x * (2 * w + 1)) with (2 * X + 0) by (unfold X; lia).
    replace (2 * X + 0 - 1) with (2 * (X - 1) + 1) by lia.
    rewrite land2 by lia. rewrite IH. lia.
Qed.

Lemma lowZ_pow : forall c w, 0 <= c -> 0 <= w -> lowZ (2 ^ c * (2 * w + 1)) = 2 ^ c.
Proof. intros c w Hc Hw. unfold lowZ. rewrite land_pow by lia. lia. Qed.

Lemma decomp : forall j, 1 <= j -> exists c w, 0 <= c /\ 0 <= w /\ j = 2 ^ c * (2 * w + 1).
Proof.
  assert (H : forall k : nat, forall j, 1 <= j <= Z.of_nat k ->
            exists c w, 0 <= c /\ 0 <= w /\ j = 2 ^ c * (2 * w + 1)).
  { induction k as [|k IH]; intros j Hj; [lia|].
    destruct (Z.eq_dec (j mod 2) 1) as [E | E].
    - exists 0, (j / 2). change (2 ^ 0) with 1. split; [lia|]. split; [|].
      + apply Z.div_pos; lia.
      + pose proof (Z.div_mod j 2 ltac:(lia)). lia.
    - assert (Hm : j mod 2 = 0) by (pose proof (Z.mod_pos_bound j 2); lia).
      pose proof (Z.div_mod j 2 ltac:(lia)) as Hd.
      destruct (IH (j / 2) ltac:(lia)) as (c & w & Hc & Hw & Hj').
      exists (c + 1), w. split; [lia|]. split; [lia|].
      rewrite Z.pow_add_r by lia. lia. }
  intros j Hj. apply (H (Z.to_nat j)). lia.
Qed.

Lemma low_pos : forall j, 1 <= j -> 1 <= lowZ j <= j.
Proof.
  intros j Hj. destruct (decomp j Hj) as (c & w & Hc & Hw & ->).
  rewrite lowZ_pow by lia. pose proof (Z.pow_pos_nonneg 2 c ltac:(lia) Hc). nia.
Qed.

Lemma low_up : forall j, 1 <= j -> j + lowZ j - lowZ (j + lowZ j) <= j - lowZ j.
Proof.
  intros j Hj. destruct (decomp j Hj) as (c & w & Hc & Hw & ->).
  rewrite lowZ_pow by lia.
  destruct (decomp (w + 1) ltac:(lia)) as (b & v & Hb & Hv & Hwv).
  assert (E : 2 ^ c * (2 * w + 1) + 2 ^ c = 2 ^ (c + 1 + b) * (2 * v + 1)).
  { rewrite !Z.pow_add_r by lia. change (2 ^ 1) with 2. rewrite <- Z.mul_assoc, <- Hwv. lia. }
  rewrite E. rewrite lowZ_pow by lia.
  assert (2 ^ (c + 1) <= 2 ^ (c + 1 + b)) by (apply Z.pow_le_mono_r; lia).
  rewrite Z.pow_add_r in H by lia. change (2 ^ 1) with 2 in H. lia.
Qed.

Lemma low_mid : forall j r, 1 <= j -> 0 < r < lowZ j -> j <= (j + r) - lowZ (j + r).
Proof.
  intros j r Hj Hr. destruct (decomp j Hj) as (c & w & Hc & Hw & ->).
  rewrite lowZ_pow in Hr by lia.
  destruct (decomp r ltac:(lia)) as (b & v & Hb & Hv & ->).
  assert (Hbc : b < c).
  { destruct (Z.lt_ge_cases b c) as [|H]; [lia|].
    assert (2 ^ c <= 2 ^ b) by (apply Z.pow_le_mono_r; lia). nia. }
  assert (Ec : 2 ^ c = 2 ^ b * 2 * 2 ^ (c - b - 1)).
  { replace c with (b + 1 + (c - b - 1)) at 1 by lia.
    rewrite !Z.pow_add_r by lia. change (2 ^ 1) with 2. ring. }
  assert (E : 2 ^ c * (2 * w + 1) + 2 ^ b * (2 * v + 1)
              = 2 ^ b * (2 * (2 ^ (c - b - 1) * (2 * w + 1) + v) + 1))
    by (rewrite Ec; ring).
  rewrite E. rewrite lowZ_pow; [| lia |].
  - rewrite <- E. nia.
  - pose proof (Z.pow_pos_nonneg 2 (c - b - 1) ltac:(lia) ltac:(lia)). nia.
Qed.

End LowBit.

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

(* distance to the top of the word: decreases along any increasing walk *)
Definition mtop (j : int) : Z := (wB - (φ j))%Z.

Lemma top_dec : forall j nj : int, (j <? nj) = true -> Zwf 0 (mtop nj) (mtop j).
Proof.
  intros j nj H. rewrite ltb_spec in H. pose proof (to_Z_bounded nj).
  unfold Zwf, mtop. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Fenwick trees                                                       *)
(* ------------------------------------------------------------------ *)

(* the lowest set bit of j > 0 *)
Definition lowb (j : int) : int := j - (j land (j - 1)).

Lemma land_low : forall j : int, (0 < (φ j))%Z ->
  (φ (j land (j - 1))) = ((φ j) - lowZ (φ j))%Z.
Proof.
  intros j Hj. rewrite land_spec'.
  assert (E : (φ (j - 1)) = ((φ j) - 1)%Z) by sia. rewrite E. unfold lowZ. lia.
Qed.

Lemma sum_dec : forall j : int, (0 <? j) = true -> Zwf 0 (φ (j land (j - 1))) (φ j).
Proof.
  intros j H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  pose proof (land_low j H). pose proof (low_pos (φ j) ltac:(lia)).
  unfold Zwf. lia.
Qed.

(* t.[j] += delta for every j = p, p + low p, ... up to N *)
Fixpoint fen_add (t : array int) (N j delta : int)
    (H : Acc (Zwf 0) (mtop j)) {struct H} : array int :=
  match bdec ((0 <? j) && (j <=? N)) with
  | left _ =>
      let t' := t.[j <- t.[j] + delta] in
      let nj := j + lowb j in
      match bdec (j <? nj) with
      | left Hlt => fen_add t' N nj delta (Acc_inv H (top_dec j nj Hlt))
      | right _ => t'
      end
  | right _ => t
  end.

(* acc + t.[j] + t.[j - low j] + ... *)
Fixpoint fen_sum (t : array int) (j acc : int)
    (H : Acc (Zwf 0) (φ j)) {struct H} : int :=
  match bdec (0 <? j) with
  | left Hj => fen_sum t (j land (j - 1)) (acc + t.[j]) (Acc_inv H (sum_dec j Hj))
  | right _ => acc
  end.

(* ------------------------------------------------------------------ *)
(* Manacher, on the doubled centres q = a + b of the factors s_a..s_b  *)
(* ------------------------------------------------------------------ *)

(* Centre q (0 <= q < 2n) has the candidates [q/2 - k, (q+1)/2 + k],
   k = 0, 1, ...; cnt.[q] is the number of them that are palindromes. *)

Definition imin (a b : int) : int := if a <? b then a else b.

Definition hcond (x : PrimString.string) (n q k : int) : bool :=
  (k <=? (q >> 1)) && (((q + 1) >> 1) + k <? n)
  && (PrimString.get x ((q >> 1) - k) =? PrimString.get x (((q + 1) >> 1) + k)).

Fixpoint expand (x : PrimString.string) (n q k : int)
    (H : Acc (Zwf 0) (gap n k)) {struct H} : int :=
  match bdec (k <? n) with
  | left Hk => if hcond x n q k then expand x n q (k + 1) (Acc_inv H (dec_step n k Hk)) else k
  | right _ => k
  end.

Fixpoint man (x : PrimString.string) (n n2 : int) (cnt : array int) (q Q rb : int)
    (H : Acc (Zwf 0) (gap n2 q)) {struct H} : array int :=
  match bdec (q <? n2) with
  | left Hq =>
      let bq := (q + 1) >> 1 in
      let k0 := if bq <? rb then imin cnt.[Q + Q - q] (rb - bq) else 0 in
      let c := expand x n q k0 (Zwf_well_founded 0 (gap n k0)) in
      if rb <? bq + c
      then man x n n2 cnt.[q <- c] (q + 1) q (bq + c) (Acc_inv H (dec_step n2 q Hq))
      else man x n n2 cnt.[q <- c] (q + 1) Q rb (Acc_inv H (dec_step n2 q Hq))
  | right _ => cnt
  end.

Definition manacher (x : PrimString.string) : array int :=
  let n := PrimString.length x in
  man x n (n + n) (PArray.make (n + n) 0) 0 0 0 (Zwf_well_founded 0 (gap (n + n) 0)).

(* ------------------------------------------------------------------ *)
(* Tabulation                                                          *)
(* ------------------------------------------------------------------ *)

Fixpoint tab_loop (f : int -> int) (n i : int) (a : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi => tab_loop f n (i + 1) a.[i <- f i] (Acc_inv H (dec_step n i Hi))
  | right _ => a
  end.

Definition tab (n : int) (f : int -> int) : array int :=
  tab_loop f n 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)).

(* ------------------------------------------------------------------ *)
(* The offline sweep: buckets of queries, Fenwick trees over the       *)
(* left border                                                         *)
(* ------------------------------------------------------------------ *)

(* Event k (k < m) asks, at slot ts.[k], for the point value at as.[k].
   head.[t] = 1 + the last event of slot t (0: none), next.[k] = 1 + the
   previous event of the slot of k (0: none). *)
Fixpoint build (ts : array int) (m k : int) (head next : array int)
    (H : Acc (Zwf 0) (gap m k)) {struct H} : array int * array int :=
  match bdec (k <? m) with
  | left Hk =>
      let t := ts.[k] in
      let h := head.[t] in
      build ts m (k + 1) head.[t <- k + 1] next.[k <- h] (Acc_inv H (dec_step m k Hk))
  | right _ => (head, next)
  end.

Definition fadd (t : array int) (N j delta : int) : array int :=
  fen_add t N j delta (Zwf_well_founded 0 (mtop j)).

Definition fsum (t : array int) (j : int) : int :=
  fen_sum t j 0 (Zwf_well_founded 0 (φ j)).

(* the point value at a of the function the two trees hold *)
Definition fval (t : array int * array int) (a : int) : int :=
  fsum (fst t) (a + 1) + a * fsum (snd t) (a + 1).

Lemma lt_dec : forall a b : int, (a <? b) = true -> Zwf 0 (φ a) (φ b).
Proof.
  intros a b H. rewrite ltb_spec in H. pose proof (to_Z_bounded a). unfold Zwf. lia.
Qed.

Fixpoint walk (as_ next : array int) (t : array int * array int) (v : array int)
    (ptr : int) (H : Acc (Zwf 0) (φ ptr)) {struct H} : array int :=
  match bdec (0 <? ptr) with
  | left _ =>
      let k := ptr - 1 in
      let nx := next.[k] in
      let v' := v.[k <- fval t as_.[k]] in
      match bdec (nx <? ptr) with
      | left Hlt => walk as_ next t v' nx (Acc_inv H (lt_dec nx ptr Hlt))
      | right _ => v'
      end
  | right _ => v
  end.

(* centre i with radius di: add min(di, i+1, i-A+1)^+ at every A *)
Definition insert (NN : int) (t : array int * array int) (i di : int) : array int * array int :=
  let dd := imin di (i + 1) in
  let lft := i + 1 - dd in
  let t0 := fadd (fst t) NN 1 dd in
  let t0 := fadd t0 NN (lft + 2) lft in
  let t0 := fadd t0 NN (i + 2) (0 - (i + 1)) in
  let t1 := fadd (snd t) NN (lft + 2) (0 - 1) in
  let t1 := fadd t1 NN (i + 2) 1 in
  (t0, t1).

Fixpoint sweep (d as_ head next : array int) (n n1 NN : int) (t : array int * array int)
    (v : array int) (tau : int) (H : Acc (Zwf 0) (gap n1 tau)) {struct H} : array int :=
  match bdec (tau <? n1) with
  | left Ht =>
      let v' := walk as_ next t v head.[tau] (Zwf_well_founded 0 (φ (head.[tau]))) in
      let t' := if tau <? n then insert NN t tau d.[tau] else t in
      sweep d as_ head next n n1 NN t' v' (tau + 1) (Acc_inv H (dec_step n1 tau Ht))
  | right _ => v
  end.

(* v.[k] = sum_{i < ts.[k]} min(d.[i], i - as.[k] + 1)^+ (mod 2^63), k < m *)
Definition lsum_all (n m : int) (d as_ ts : array int) : array int :=
  let hn := build ts m 0 (PArray.make (n + 1) 0) (PArray.make m 0)
                  (Zwf_well_founded 0 (gap m 0)) in
  let NN := n + 2 in
  sweep d as_ (fst hn) (snd hn) n (n + 1) NN
        (PArray.make (NN + 1) 0, PArray.make (NN + 1) 0) (PArray.make m 0) 0
        (Zwf_well_founded 0 (gap (n + 1) 0)).

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* One of the four families of clipped sums: the odd (par = 0) or even
   (par = 1) centres, the left half of every query (rev = false) or its
   right half read backwards (rev = true). *)
Definition fam (n m : int) (cnt xl xr : array int) (par : int) (rev : bool) : array int :=
  let d := tab n (fun i => cnt.[2 * (if rev then n - 1 - i else i) + par]) in
  let as_ := tab m (fun k => if rev then n - (xr.[k] - par) else xl.[k] - 1) in
  let ts := tab m (fun k => let h := (xl.[k] + xr.[k] - par) >> 1 in
                            if rev then n - h else h) in
  lsum_all n m d as_ ts.

Definition palindromes_impl (x : PrimString.string) (xl xr : array uint) : array uint :=
  let n := PrimString.length x in
  let m := PArray.length xl in
  let cnt := manacher x in
  let v0 := fam n m cnt xl xr 0 false in
  let v1 := fam n m cnt xl xr 0 true in
  let v2 := fam n m cnt xl xr 1 false in
  let v3 := fam n m cnt xl xr 1 true in
  tab m (fun k => v0.[k] + v1.[k] + v2.[k] + v3.[k]).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition palindromes : PrimString.string -> array uint -> array uint -> array uint :=
  palindromes_impl.
