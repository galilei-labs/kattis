(* Executable implementation and its required termination dependencies.
   Correctness proofs are in bigfactoring_proofs.v. *)
(* Implementation of bigfactoring (bigfactoring.spec).

   Code.  [fac m lo acc cnt] appends the prime factors of m (no divisor of
   m in [2, lo)) to a flat table acc of CAP = 128 cells, cnt of them used:
   - trial division by d = lo, lo + 1, ..., B0 - 1 (B0 = 1000), stopping
     when d * d exceeds the cofactor r, which is then 1 or a prime;
   - otherwise r >= 10^6 has no factor below 1000, and Miller-Rabin (12
     fixed bases, a heuristic whose verdict is never trusted) decides:
     "probable prime": r - 1 is factored by [fac] itself and a Lucas
     certificate is searched (bases 2, 3, ..., 1001: a^(r-1) = 1 mod r and
     gcd(a^((r-1)/q) - 1, r) = 1 for every prime q of r - 1); "composite":
     Pollard's rho, Brent's variant with batched gcds (batches of 128,
     rounds up to 2^25, 20 retries over c), returns a candidate divisor g
     that is checked (1 < g < r, g | r) before both parts are factored;
   - whenever a certificate or a split fails, the fallback is trial
     division up to the square root (proven, never reached in practice).
   The table is then copied to an array of exactly cnt cells and sorted by
   insertion sort (adjacent swaps).  All bignums are Z; indices, counters
   and retry counts are Uint63 ints.  No list is built.

   Proof.  [lucas] proves Lucas's theorem from scratch (order of a modulo a
   prime divisor p of N, bounded by p - 1 through a pigeonhole on the
   powers of a, NoDup_incl_length); [fac_spec] is a well-founded induction
   on m whose invariant is the table holding L ++ L' with L' prime and of
   product m, and [room] (2^|L| * m <= 2^128) keeping every write in the
   table's 128 cells; the sort keeps the product and the primality of the
   cells and makes adjacent cells ordered.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) _] proof (Z measure: the exponent, the cofactor, a gap of
   Uint63 counters), as in template/polymul1. *)

From Bigfactoring.spec Require Import Prelude.
From StdGalilei Require Import repr.
From StdGalilei Require Import bigint.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Znumtheory Sorted.
Import ListNotations.

Open Scope uint63_scope.
Open Scope Z_scope.
Open Scope bool_scope.

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

Definition gap (m j : int) : Z := (φ m) - (φ j).

Lemma dec_step : forall m i : int,
  (i <? m)%uint63 = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1))%uint63 = (φ i) + 1) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_down : forall k : int,
  (0 <? k)%uint63 = true -> Zwf 0 ((φ (k - 1))%uint63) (φ k).
Proof.
  intros k H. rewrite ltb_spec in H. change ((φ 0)%uint63) with 0 in H.
  assert (H1 : (φ (k - 1))%uint63 = (φ k) - 1) by sia.
  unfold Zwf. lia.
Qed.

Lemma dec_half : forall e : Z, (0 <? e) = true -> Zwf 0 (e / 2) e.
Proof.
  intros e H. apply Z.ltb_lt in H. unfold Zwf.
  split; [lia|]. apply Z.div_lt; lia.
Qed.

Lemma dec_bound : forall B d : Z, (d <? B) = true -> Zwf 0 (B - (d + 1)) (B - d).
Proof. intros B d H. apply Z.ltb_lt in H. unfold Zwf. lia. Qed.

Definition dguard (m d : Z) : bool := (1 <? d) && (0 <? m) && (m mod d =? 0).

Lemma dec_div : forall m d : Z, dguard m d = true -> Zwf 0 (m / d) m.
Proof.
  intros m d H. unfold dguard in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. unfold Zwf.
  split; [lia|]. apply Z.div_lt; lia.
Qed.

Definition guard (x m : Z) : bool := (0 <=? x) && (x <? m).

Lemma guard_ok : forall x m, guard x m = true -> Zwf 0 x m.
Proof.
  intros x m H. unfold guard in H. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Modular exponentiation                                              *)
(* ------------------------------------------------------------------ *)

(* (acc * b ^ e) mod m, square and multiply. *)
Fixpoint pm_loop (b e m acc : Z) (H : Acc (Zwf 0) e) {struct H} : Z :=
  match bdec (0 <? e) with
  | left He =>
      pm_loop (b * b mod m) (e / 2) m (if Z.odd e then acc * b mod m else acc)
        (Acc_inv H (dec_half e He))
  | right _ => acc mod m
  end.

Definition powmod (b e m : Z) : Z := pm_loop (b mod m) e m 1 (Zwf_well_founded 0 e).

(* ------------------------------------------------------------------ *)
(* Miller-Rabin: a heuristic only, never trusted                        *)
(* ------------------------------------------------------------------ *)

(* d odd and s with d * 2^s = the input (for a positive input). *)
Fixpoint strip (d : Z) (s : int) (H : Acc (Zwf 0) d) {struct H} : Z * int :=
  match bdec (0 <? d) with
  | left Hd =>
      if Z.even d then strip (d / 2) (s + 1)%uint63 (Acc_inv H (dec_half d Hd))
      else (d, s)
  | right _ => (d, s)
  end.

(* does one of k successive squarings of x hit n - 1 ? *)
Fixpoint sq_loop (n x : Z) (k : int) (H : Acc (Zwf 0) (φ k)) {struct H} : bool :=
  match bdec (0 <? k)%uint63 with
  | left Hk =>
      let x := x * x mod n in
      if x =? n - 1 then true else sq_loop n x (k - 1)%uint63 (Acc_inv H (dec_down k Hk))
  | right _ => false
  end.

(* n passes the strong probable-prime test to base a *)
Definition mr_base (n d : Z) (s : int) (a : Z) : bool :=
  let x := powmod a d n in
  if orb (x =? 1) (x =? n - 1) then true
  else sq_loop n x (s - 1)%uint63 (Zwf_well_founded 0 _).

Definition miller_rabin (n : Z) : bool :=
  let '(d, s) := strip (n - 1) 0%uint63 (Zwf_well_founded 0 _) in
  mr_base n d s 2 && mr_base n d s 3 && mr_base n d s 5 && mr_base n d s 7 &&
  mr_base n d s 11 && mr_base n d s 13 && mr_base n d s 17 &&
  mr_base n d s 19 && mr_base n d s 23 && mr_base n d s 29 &&
  mr_base n d s 31 && mr_base n d s 37.

(* ------------------------------------------------------------------ *)
(* Pollard's rho, Brent's variant: a heuristic, its result is checked  *)
(* ------------------------------------------------------------------ *)

Definition rho_f (n c y : Z) : Z := (y * y + c) mod n.

(* f applied k times *)
Fixpoint rho_iter (n c y : Z) (k : int) (H : Acc (Zwf 0) (φ k)) {struct H} : Z :=
  match bdec (0 <? k)%uint63 with
  | left Hk => rho_iter n c (rho_f n c y) (k - 1)%uint63 (Acc_inv H (dec_down k Hk))
  | right _ => y
  end.

(* k steps of y := f y, q := q * |x - y| mod n *)
Fixpoint rho_batch (n c x y q : Z) (k : int) (H : Acc (Zwf 0) (φ k)) {struct H}
    : Z * Z :=
  match bdec (0 <? k)%uint63 with
  | left Hk =>
      let y := rho_f n c y in
      rho_batch n c x y (q * Z.abs (x - y) mod n) (k - 1)%uint63
        (Acc_inv H (dec_down k Hk))
  | right _ => (y, q)
  end.

Definition rho_m : int := 128.

Lemma dec_incr : forall r k k' : int,
  ((k <? r)%uint63 && (k <? k')%uint63) = true -> Zwf 0 (gap r k') (gap r k).
Proof.
  intros r k k' H. apply andb_prop in H as [H1 H2].
  rewrite ltb_spec in H1, H2. unfold Zwf, gap. lia.
Qed.

(* the batches of one round of length r, from k on: (g, ys, y, q) *)
Fixpoint rho_inner (n c x y q : Z) (r k : int) (H : Acc (Zwf 0) (gap r k))
    {struct H} : Z * Z * Z * Z :=
  match bdec ((k <? r)%uint63 && (k <? k + rho_m)%uint63) with
  | left Hk =>
      let t := if (r - k <? rho_m)%uint63 then (r - k)%uint63 else rho_m in
      let '(y', q') := rho_batch n c x y q t (Zwf_well_founded 0 _) in
      let g := zgcd q' n in
      if g =? 1 then
        rho_inner n c x y' q' r (k + rho_m)%uint63 (Acc_inv H (dec_incr r k _ Hk))
      else (g, y, y', q')
  | right _ => (1, y, y, q)
  end.

Definition rho_rmax : int := 33554432.  (* 2^25 *)

(* the walk back from ys, one gcd per step *)
Fixpoint rho_back (n c x ys : Z) (k : int) (H : Acc (Zwf 0) (φ k)) {struct H} : Z :=
  match bdec (0 <? k)%uint63 with
  | left Hk =>
      let ys := rho_f n c ys in
      let g := zgcd (Z.abs (x - ys)) n in
      if g =? 1 then rho_back n c x ys (k - 1)%uint63 (Acc_inv H (dec_down k Hk))
      else g
  | right _ => n
  end.

(* the rounds r = 1, 2, 4, ... up to rho_rmax; 0 when none succeeds *)
Fixpoint rho_outer (n c y q : Z) (r : int) (H : Acc (Zwf 0) (gap rho_rmax r))
    {struct H} : Z :=
  let x := y in
  let y := rho_iter n c y r (Zwf_well_founded 0 _) in
  let '(g, ys, y', q') := rho_inner n c x y q r 0 (Zwf_well_founded 0 _) in
  if g =? 1 then
    match bdec ((r <? rho_rmax)%uint63 && (r <? r * 2)%uint63) with
    | left Hr => rho_outer n c y' q' (r * 2)%uint63 (Acc_inv H (dec_incr rho_rmax r _ Hr))
    | right _ => 0
    end
  else if g =? n then rho_back n c x ys (rho_m + 1)%uint63 (Zwf_well_founded 0 _)
  else g.

(* retries with c = c0, c0 + 1, ...; 0 when none succeeds *)
Fixpoint rho_try (n c : Z) (k : int) (H : Acc (Zwf 0) (φ k)) {struct H} : Z :=
  match bdec (0 <? k)%uint63 with
  | left Hk =>
      let g := rho_outer n c 2 1 1 (Zwf_well_founded 0 _) in
      if (1 <? g) && (g <? n) then g
      else rho_try n (c + 1) (k - 1)%uint63 (Acc_inv H (dec_down k Hk))
  | right _ => 0
  end.

(* a candidate divisor of n: checked by the caller *)
Definition rho (n : Z) : Z := rho_try n 1 20%uint63 (Zwf_well_founded 0 _).

(* ------------------------------------------------------------------ *)
(* The factor table: cells 0 .. cnt-1 of an array of CAP cells          *)
(* ------------------------------------------------------------------ *)

Definition CAP : int := 128.

Definition push (acc : array Z) (cnt : int) (p : Z) : array Z * int :=
  (acc.[cnt <- p], (cnt + 1)%uint63).

(* ------------------------------------------------------------------ *)
(* Trial division                                                      *)
(* ------------------------------------------------------------------ *)

(* divide d out of m as long as it divides *)
Fixpoint divout (m d : Z) (acc : array Z) (cnt : int) (H : Acc (Zwf 0) m)
    {struct H} : Z * array Z * int :=
  match bdec (dguard m d) with
  | left Hg =>
      let '(acc', cnt') := push acc cnt d in
      divout (m / d) d acc' cnt' (Acc_inv H (dec_div m d Hg))
  | right _ => (m, acc, cnt)
  end.

(* trial divisors d, d + 1, ..., below B, stopping when d * d > m:
   (m', d', acc', cnt') *)
Fixpoint trial (B m d : Z) (acc : array Z) (cnt : int) (H : Acc (Zwf 0) (B - d))
    {struct H} : Z * Z * array Z * int :=
  match bdec (d <? B) with
  | left Hd =>
      if m <? d * d then (m, d, acc, cnt)
      else
        let '(m', acc', cnt') := divout m d acc cnt (Zwf_well_founded 0 m) in
        trial B m' (d + 1) acc' cnt' (Acc_inv H (dec_bound B d Hd))
  | right _ => (m, d, acc, cnt)
  end.

(* the bound of the first stage of trial division *)
Definition B0 : Z := 1000.

(* the fallback, never reached in a normal run: trial division up to the
   square root, the cofactor left being 1 or a prime *)
Definition fallback (m lo : Z) (acc : array Z) (cnt : int) : array Z * int :=
  let '(r, _, acc', cnt') := trial (m + 2) m lo acc cnt (Zwf_well_founded 0 _) in
  if 1 <? r then push acc' cnt' r else (acc', cnt').

(* ------------------------------------------------------------------ *)
(* Lucas's primality certificate                                       *)
(* ------------------------------------------------------------------ *)

(* for every i < qc: gcd (a^((r-1)/q_i) mod r - 1, r) = 1 *)
Fixpoint all_q (r a : Z) (qs : array Z) (qc i : int) (H : Acc (Zwf 0) (gap qc i))
    {struct H} : bool :=
  match bdec (i <? qc)%uint63 with
  | left Hi =>
      let q := qs.[i] in
      if (0 <? i)%uint63 && (q =? qs.[(i - 1)%uint63]) then
        all_q r a qs qc (i + 1)%uint63 (Acc_inv H (dec_step qc i Hi))
      else if zgcd (powmod a ((r - 1) / q) r - 1) r =? 1 then
        all_q r a qs qc (i + 1)%uint63 (Acc_inv H (dec_step qc i Hi))
      else false
  | right _ => true
  end.

Definition lucas_ok (r a : Z) (qs : array Z) (qc : int) : bool :=
  (powmod a (r - 1) r =? 1) && all_q r a qs qc 0 (Zwf_well_founded 0 _).

(* bases a, a + 1, ..., k of them *)
Fixpoint cert_try (r : Z) (qs : array Z) (qc : int) (a : Z) (k : int)
    (H : Acc (Zwf 0) (φ k)) {struct H} : bool :=
  match bdec (0 <? k)%uint63 with
  | left Hk =>
      if lucas_ok r a qs qc then true
      else cert_try r qs qc (a + 1) (k - 1)%uint63 (Acc_inv H (dec_down k Hk))
  | right _ => false
  end.

Definition certify (r : Z) (qs : array Z) (qc : int) : bool :=
  cert_try r qs qc 2 1000%uint63 (Zwf_well_founded 0 _).

(* ------------------------------------------------------------------ *)
(* The factorisation                                                   *)
(* ------------------------------------------------------------------ *)

(* appends the prime factors of m (m >= 1, no divisor in [2, lo)) to the
   table (acc, cnt) *)
Fixpoint fac (m lo : Z) (acc : array Z) (cnt : int) (H : Acc (Zwf 0) m)
    {struct H} : array Z * int :=
  let '(r, d, acc1, cnt1) := trial B0 m lo acc cnt (Zwf_well_founded 0 _) in
  if r <? d * d then (if 1 <? r then push acc1 cnt1 r else (acc1, cnt1))
  else if miller_rabin r then
    match bdec (guard (r - 1) m) with
    | left G =>
        let '(qs, qc) := fac (r - 1) 2 (PArray.make CAP 0) 0%uint63
                           (Acc_inv H (guard_ok _ _ G)) in
        if certify r qs qc then push acc1 cnt1 r else fallback r d acc1 cnt1
    | right _ => fallback r d acc1 cnt1
    end
  else
    let g := rho r in
    if (1 <? g) && (g <? r) && (r mod g =? 0) then
      match bdec (guard g m), bdec (guard (r / g) m) with
      | left G1, left G2 =>
          let '(acc2, cnt2) := fac g B0 acc1 cnt1 (Acc_inv H (guard_ok _ _ G1)) in
          fac (r / g) B0 acc2 cnt2 (Acc_inv H (guard_ok _ _ G2))
      | _, _ => fallback r d acc1 cnt1
      end
    else fallback r d acc1 cnt1.

(* ------------------------------------------------------------------ *)
(* Output: copy, then insertion sort                                   *)
(* ------------------------------------------------------------------ *)

Fixpoint copy (src dst : array Z) (n i : int) (H : Acc (Zwf 0) (gap n i))
    {struct H} : array Z :=
  match bdec (i <? n)%uint63 with
  | left Hi => copy src dst.[i <- src.[i]] n (i + 1)%uint63 (Acc_inv H (dec_step n i Hi))
  | right _ => dst
  end.

(* moves cell j down to its place *)
Fixpoint sink (a : array Z) (j : int) (H : Acc (Zwf 0) (φ j)) {struct H} : array Z :=
  match bdec (0 <? j)%uint63 with
  | left Hj =>
      let x := a.[(j - 1)%uint63] in
      let y := a.[j] in
      if y <? x then sink a.[(j - 1)%uint63 <- y].[j <- x] (j - 1)%uint63
                       (Acc_inv H (dec_down j Hj))
      else a
  | right _ => a
  end.

Fixpoint isort (a : array Z) (n i : int) (H : Acc (Zwf 0) (gap n i)) {struct H}
    : array Z :=
  match bdec (i <? n)%uint63 with
  | left Hi => isort (sink a i (Zwf_well_founded 0 _)) n (i + 1)%uint63
                 (Acc_inv H (dec_step n i Hi))
  | right _ => a
  end.

Definition bigfactoring_impl (n : Z) : array Z :=
  let '(acc, cnt) := fac n 2 (PArray.make CAP 0) 0%uint63 (Zwf_well_founded 0 _) in
  let out := copy acc (PArray.make cnt 0) cnt 0%uint63 (Zwf_well_founded 0 _) in
  isort out cnt 1%uint63 (Zwf_well_founded 0 _).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition bigfactoring : Z -> array Z := bigfactoring_impl.
