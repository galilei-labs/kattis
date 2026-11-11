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
From StdGalilei Require Import repr bigint.
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

(* ================================================================== *)
(* Prop side                                                           *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Divisors and primes                                                 *)
(* ------------------------------------------------------------------ *)

(* m has no divisor in [2, d) *)
Definition nodiv (m d : Z) : Prop := forall k, 2 <= k < d -> ~ (k | m).

Lemma prime_of_nodiv : forall m,
  1 < m -> (forall k, 2 <= k -> k * k <= m -> ~ (k | m)) -> prime m.
Proof.
  intros m Hm Hk. destruct (prime_dec m) as [Hp | Hp]; [exact Hp|].
  exfalso. destruct (not_prime_divide m Hm Hp) as (x & Hx & [y Hy]).
  assert (Hy1 : 1 < y) by nia.
  destruct (Z.le_gt_cases x y).
  - apply (Hk x); [lia | nia | exists y; lia].
  - apply (Hk y); [lia | nia | exists x; lia].
Qed.

Lemma prime_divisor : forall x, 1 < x -> exists p, prime p /\ (p | x) /\ p <= x.
Proof.
  intros x. induction x as [x IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros Hx. destruct (prime_dec x) as [Hp | Hp].
  - exists x. split; [exact Hp|]. split; [apply Z.divide_refl | lia].
  - destruct (not_prime_divide x Hx Hp) as (y & Hy & Hyx).
    destruct (IH y ltac:(unfold Zwf; lia) ltac:(lia)) as (p & Hp1 & Hp2 & Hp3).
    exists p. split; [exact Hp1|]. split; [eapply Z.divide_trans; eassumption | lia].
Qed.

Lemma nodiv_prime : forall m d, 2 <= d -> (d | m) -> 0 < m -> nodiv m d -> prime d.
Proof.
  intros m d Hd Hdm Hm Hn. apply prime_of_nodiv; [lia|].
  intros k Hk Hkk Hkd. apply (Hn k); [nia|]. eapply Z.divide_trans; eassumption.
Qed.

Lemma nodiv_divisor : forall m m' d, (m' | m) -> nodiv m d -> nodiv m' d.
Proof.
  intros m m' d H Hn k Hk Hkm. apply (Hn k Hk). eapply Z.divide_trans; eassumption.
Qed.

Lemma nodiv_mono : forall m d d', d' <= d -> nodiv m d -> nodiv m d'.
Proof. intros m d d' H Hn k Hk. apply Hn. lia. Qed.

Lemma prime_of_nodiv_sq : forall m d, 0 <= d -> 1 < m -> m < d * d -> nodiv m d -> prime m.
Proof.
  intros m d H0 H1 H2 Hn. apply prime_of_nodiv; [lia|].
  intros k Hk Hkk. apply Hn. split; [lia|].
  destruct (Z.lt_ge_cases k d); [lia|].
  assert (d * d <= k * k) by (apply Z.mul_le_mono_nonneg; lia). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Products                                                            *)
(* ------------------------------------------------------------------ *)

Lemma product_nil : product [] = 1.
Proof. reflexivity. Qed.

Lemma product_cons : forall x l, product (x :: l) = x * product l.
Proof. reflexivity. Qed.

Lemma product_app : forall l l', product (l ++ l') = product l * product l'.
Proof.
  intros l l'. induction l as [| x l IH].
  - rewrite app_nil_l, product_nil. lia.
  - rewrite <- app_comm_cons, !product_cons, IH. lia.
Qed.

Lemma pow2_le_product : forall l, Forall prime l ->
  2 ^ Z.of_nat (List.length l) <= product l.
Proof.
  intros l H. induction H as [| x l Hx Hl IH]; [rewrite product_nil; simpl; lia|].
  pose proof (prime_ge_2 x Hx). rewrite product_cons.
  change (List.length (x :: l)) with (S (List.length l)).
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. nia.
Qed.

Lemma product_pos : forall l, Forall prime l -> 0 < product l.
Proof.
  intros l H. pose proof (pow2_le_product l H).
  pose proof (Z.pow_pos_nonneg 2 (Z.of_nat (List.length l)) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma prime_in_product : forall q l, prime q -> Forall prime l ->
  (q | product l) -> In q l.
Proof.
  intros q l Hq Hl. unfold product. induction Hl as [| x l Hx Hl IH]; simpl; intros Hd.
  - pose proof (prime_ge_2 q Hq). apply Z.divide_pos_le in Hd; lia.
  - destruct (prime_mult q Hq x _ Hd) as [H | H].
    + left. symmetry. apply prime_div_prime; assumption.
    + right. apply IH. exact H.
Qed.

Lemma in_product_divide : forall q l, In q l -> (q | product l).
Proof.
  intros q l. unfold product. induction l as [| x l IH]; simpl; [tauto|].
  intros [-> | H].
  - exists (fold_right Z.mul 1 l). lia.
  - destruct (IH H) as [k Hk]. exists (x * k). rewrite Hk. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Lucas's theorem: a of order N - 1 modulo N makes N prime             *)
(* ------------------------------------------------------------------ *)

Lemma mod1_divide : forall x p, 2 <= p -> x mod p = 1 -> (p | x - 1).
Proof.
  intros x p Hp H. apply Z.mod_divide; [lia|].
  rewrite Zminus_mod, H, (Z.mod_1_l p) by lia. rewrite Z.sub_diag. apply Z.mod_0_l. lia.
Qed.

Lemma divide_mod1 : forall x p, 2 <= p -> (p | x - 1) -> x mod p = 1.
Proof.
  intros x p Hp [k Hk]. replace x with (1 + k * p) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_1_l. lia.
Qed.

Lemma prime_not_div_pow : forall p a, prime p -> ~ (p | a) ->
  forall e, 0 <= e -> ~ (p | a ^ e).
Proof.
  intros p a Hp Ha e He. pose proof (prime_ge_2 p Hp).
  apply (natlike_ind (fun e => ~ (p | a ^ e))); [| | exact He].
  - intros D. rewrite Z.pow_0_r in D. apply Z.divide_pos_le in D; lia.
  - intros e' He' IH D. rewrite Z.pow_succ_r in D by lia.
    destruct (prime_mult p Hp _ _ D); [apply Ha | apply IH]; auto.
Qed.

Lemma pow_mod1_mul : forall p a d k, 2 <= p -> 0 <= d -> 0 <= k ->
  a ^ d mod p = 1 -> a ^ (d * k) mod p = 1.
Proof.
  intros p a d k Hp Hd Hk H. rewrite Z.pow_mul_r by lia.
  rewrite Zpow_facts.Zpower_mod, H, Z.pow_1_l by lia. apply Z.mod_1_l. lia.
Qed.

Lemma order_div : forall p a d e, 2 <= p -> 1 <= d -> a ^ d mod p = 1 ->
  (forall e', 1 <= e' < d -> a ^ e' mod p <> 1) ->
  0 <= e -> a ^ e mod p = 1 -> (d | e).
Proof.
  intros p a d e Hp Hd Had Hmin He Hae.
  pose proof (Z.div_mod e d ltac:(lia)) as Edm.
  pose proof (Z.mod_pos_bound e d ltac:(lia)) as Bm.
  assert (Hq : 0 <= e / d) by (apply Z.div_pos; lia).
  assert (E : a ^ e = a ^ (d * (e / d)) * a ^ (e mod d)).
  { rewrite <- Z.pow_add_r by nia. rewrite <- Edm. reflexivity. }
  pose proof (pow_mod1_mul p a d (e / d) Hp ltac:(lia) Hq Had) as Hk.
  rewrite E, Zmult_mod, Hk, Z.mul_1_l, Z.mod_mod in Hae by lia.
  destruct (Z.eq_dec (e mod d) 0) as [Z0 | Z0].
  - apply Z.mod_divide; lia.
  - exfalso. apply (Hmin (e mod d)); [lia | exact Hae].
Qed.

Lemma bounded_search : forall (P : Z -> Prop) (Pd : forall e, {P e} + {~ P e}) (n : nat),
  (exists e, 1 <= e <= Z.of_nat n /\ P e) \/ (forall e, 1 <= e <= Z.of_nat n -> ~ P e).
Proof.
  intros P Pd n. induction n as [| n [IH | IH]].
  - right. intros e He. lia.
  - left. destruct IH as (e & He & HP). exists e. split; [lia | exact HP].
  - destruct (Pd (Z.of_nat (S n))) as [HP | HP].
    + left. exists (Z.of_nat (S n)). split; [lia | exact HP].
    + right. intros e He. destruct (Z.eq_dec e (Z.of_nat (S n))) as [-> | E]; [exact HP|].
      apply IH. lia.
Qed.

Lemma min_witness : forall (P : Z -> Prop) (Pd : forall e, {P e} + {~ P e}) d0,
  1 <= d0 -> P d0 -> exists d, 1 <= d /\ P d /\ forall e, 1 <= e < d -> ~ P e.
Proof.
  intros P Pd d0. induction d0 as [d0 IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros H1 HP.
  destruct (bounded_search P Pd (Z.to_nat (d0 - 1))) as [(e & He & HPe) | Hn].
  - apply (IH e); [unfold Zwf; lia | lia | exact HPe].
  - exists d0. split; [lia|]. split; [exact HP|]. intros e He. apply Hn. lia.
Qed.

Lemma pigeon : forall p a, prime p -> ~ (p | a) ->
  exists e, 1 <= e <= p - 1 /\ a ^ e mod p = 1.
Proof.
  intros p a Hp Ha. pose proof (prime_ge_2 p Hp) as Hp2.
  destruct (bounded_search (fun e => a ^ e mod p = 1) (fun e => Z.eq_dec _ _)
              (Z.to_nat (p - 1))) as [H | H].
  - rewrite Z2Nat.id in H by lia. exact H.
  - exfalso. set (f := fun i : nat => a ^ Z.of_nat i mod p).
    assert (key : forall i j, (i < j)%nat -> (j < Z.to_nat p)%nat -> f i = f j -> False).
    { intros i j Hij Hj Hf. unfold f in Hf.
      apply (H (Z.of_nat j - Z.of_nat i)); [lia|].
      apply divide_mod1; [lia|].
      assert (E : a ^ Z.of_nat j = a ^ Z.of_nat i * a ^ (Z.of_nat j - Z.of_nat i)).
      { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      assert (D : (p | a ^ Z.of_nat i * (a ^ (Z.of_nat j - Z.of_nat i) - 1))).
      { replace (a ^ Z.of_nat i * (a ^ (Z.of_nat j - Z.of_nat i) - 1))
          with (a ^ Z.of_nat j - a ^ Z.of_nat i) by (rewrite E; ring).
        apply Z.mod_divide; [lia|].
        rewrite Zminus_mod, <- Hf, Z.sub_diag. apply Z.mod_0_l. lia. }
      destruct (prime_mult p Hp _ _ D) as [D1 | D1]; [| exact D1].
      exfalso. exact (prime_not_div_pow p a Hp Ha (Z.of_nat i) ltac:(lia) D1). }
    assert (ND : NoDup (map f (seq 0 (Z.to_nat p)))).
    { apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
      intros x y Hx Hy Hxy. apply in_seq in Hx, Hy.
      destruct (Nat.lt_trichotomy x y) as [Hlt | [Heq | Hgt]].
      - exfalso. apply (key x y); [exact Hlt | lia | exact Hxy].
      - exact Heq.
      - exfalso. apply (key y x); [exact Hgt | lia | symmetry; exact Hxy]. }
    assert (INC : incl (map f (seq 0 (Z.to_nat p)))
                       (map Z.of_nat (seq 1 (Z.to_nat (p - 1))))).
    { intros v Hv. apply in_map_iff in Hv as (i & <- & Hi). apply in_map_iff.
      exists (Z.to_nat (f i)).
      pose proof (Z.mod_pos_bound (a ^ Z.of_nat i) p ltac:(lia)) as B.
      assert (NZ : a ^ Z.of_nat i mod p <> 0).
      { intro E. apply Z.mod_divide in E; [| lia].
        exact (prime_not_div_pow p a Hp Ha (Z.of_nat i) ltac:(lia) E). }
      unfold f. split; [apply Z2Nat.id; lia|]. apply in_seq. lia. }
    pose proof (NoDup_incl_length ND INC) as L.
    rewrite !length_map, !length_seq in L. lia.
Qed.

Lemma pos_factor : forall x y z, z = x * y -> 1 <= z -> 1 <= y -> 1 <= x.
Proof. intros x y z H1 H2 H3. nia. Qed.

Lemma lucas : forall N a Q, 2 <= N -> Forall prime Q -> product Q = N - 1 ->
  a ^ (N - 1) mod N = 1 ->
  (forall q, In q Q -> Z.gcd (a ^ ((N - 1) / q) mod N - 1) N = 1) ->
  prime N.
Proof.
  intros N a Q HN HQ HP Ha Hg.
  assert (Claim : forall p, prime p -> (p | N) -> N <= p).
  { intros p Hp HpN. pose proof (prime_ge_2 p Hp) as Hp2.
    assert (Hap : a ^ (N - 1) mod p = 1).
    { apply divide_mod1; [lia|]. eapply Z.divide_trans; [exact HpN|].
      apply mod1_divide; [lia | exact Ha]. }
    assert (Hna : ~ (p | a)).
    { intros D.
      assert (D1 : (p | a ^ (N - 1))).
      { replace (N - 1) with (Z.succ (N - 2)) by lia.
        rewrite Z.pow_succ_r by lia. apply Z.divide_mul_l. exact D. }
      assert (D2 : (p | a ^ (N - 1) - 1)) by (apply mod1_divide; lia).
      assert (D3 : (p | 1)).
      { replace 1 with (a ^ (N - 1) - (a ^ (N - 1) - 1)) by ring.
        apply Z.divide_sub_r; assumption. }
      apply Z.divide_pos_le in D3; lia. }
    destruct (pigeon p a Hp Hna) as (e0 & He0 & He0').
    destruct (min_witness (fun e => a ^ e mod p = 1) (fun e => Z.eq_dec _ _) e0
                ltac:(lia) He0') as (d & Hd1 & Hd2 & Hd3).
    assert (Hde0 : d <= e0).
    { destruct (Z.le_gt_cases d e0); [lia|]. exfalso. apply (Hd3 e0); [lia | exact He0']. }
    assert (HdN : (d | N - 1)) by (apply (order_div p a d); auto; lia).
    destruct HdN as [g Hg'].
    assert (Hg1 : 1 <= g) by (apply (pos_factor g d (N - 1)); [exact Hg' | lia | lia]).
    destruct (Z.eq_dec g 1) as [E | E].
    { subst g. clear - Hg' Hde0 He0. lia. }
    exfalso. destruct (prime_divisor g ltac:(lia)) as (q & Hq & [g' Hg''] & _).
    pose proof (prime_ge_2 q Hq).
    assert (HqQ : In q Q).
    { apply prime_in_product; auto. rewrite HP, Hg', Hg''. exists (g' * d). ring. }
    assert (Hdiv : (N - 1) / q = d * g').
    { rewrite Hg', Hg''. replace (g' * q * d) with ((d * g') * q) by ring.
      apply Z.div_mul. lia. }
    assert (Hg'0 : 0 <= g').
    { assert (1 <= g') by (apply (pos_factor g' q g); [exact Hg'' | lia | lia]). lia. }
    assert (H1 : a ^ ((N - 1) / q) mod p = 1).
    { rewrite Hdiv. apply pow_mod1_mul; auto; lia. }
    assert (H2 : (p | a ^ ((N - 1) / q) mod N - 1)).
    { rewrite Z.mod_eq by lia.
      replace (a ^ ((N - 1) / q) - N * (a ^ ((N - 1) / q) / N) - 1)
        with ((a ^ ((N - 1) / q) - 1) - N * (a ^ ((N - 1) / q) / N)) by ring.
      apply Z.divide_sub_r; [apply mod1_divide; auto |].
      apply Z.divide_mul_l. exact HpN. }
    assert (H3 : (p | 1)).
    { rewrite <- (Hg q HqQ). apply Z.gcd_greatest; [exact H2 | exact HpN]. }
    apply Z.divide_pos_le in H3; lia. }
  destruct (prime_dec N) as [Hp | Hp]; [exact Hp|]. exfalso.
  destruct (not_prime_divide N ltac:(lia) Hp) as (x & Hx & HxN).
  destruct (prime_divisor x ltac:(lia)) as (p & Hp1 & Hp2 & Hp3).
  pose proof (Claim p Hp1 (Z.divide_trans _ _ _ Hp2 HxN)). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* powmod                                                              *)
(* ------------------------------------------------------------------ *)

Lemma pow_split : forall b k r, 0 <= k -> 0 <= r ->
  b ^ (2 * k + r) = (b * b) ^ k * b ^ r.
Proof.
  intros b k r Hk Hr. rewrite Z.pow_add_r, Z.pow_mul_r by lia.
  rewrite Z.pow_2_r. reflexivity.
Qed.

Lemma pm_loop_spec : forall e (H : Acc (Zwf 0) e) b m acc, 0 < m -> 0 <= e ->
  pm_loop b e m acc H = (acc * b ^ e) mod m.
Proof.
  intros e. induction e as [e IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros H b m acc Hm He. destruct H as [Hacc]. cbn [pm_loop].
  destruct (bdec (0 <? e)) as [Hp | Hp].
  - pose proof Hp as Hp'. apply Z.ltb_lt in Hp'.
    assert (He2 : 0 <= e / 2) by (apply Z.div_pos; lia).
    rewrite IH; [| apply dec_half; exact Hp | lia | exact He2].
    rewrite Z.mul_comm, <- Z.mul_mod_idemp_l, <- Zpow_facts.Zpower_mod by lia.
    rewrite Z.mul_mod_idemp_l by lia.
    assert (Ee : e = 2 * (e / 2) + (if Z.odd e then 1 else 0)).
    { rewrite <- Zmod_odd. apply Z.div_mod. lia. }
    destruct (Z.odd e).
    + rewrite Z.mul_mod_idemp_r by lia. rewrite Ee at 2.
      rewrite pow_split by lia. rewrite Z.pow_1_r. f_equal. ring.
    + rewrite Ee at 2. rewrite pow_split by lia. rewrite Z.pow_0_r. f_equal. ring.
  - apply Z.ltb_ge in Hp. replace e with 0 by lia. rewrite Z.pow_0_r, Z.mul_1_r.
    reflexivity.
Qed.

Lemma powmod_spec : forall b e m, 0 < m -> 0 <= e -> powmod b e m = b ^ e mod m.
Proof.
  intros b e m Hm He. unfold powmod. rewrite pm_loop_spec by lia.
  rewrite Z.mul_1_l. symmetry. apply Zpow_facts.Zpower_mod. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The factor table                                                    *)
(* ------------------------------------------------------------------ *)

(* cells 0 .. cnt-1 of acc hold L *)
Definition tab (acc : array Z) (cnt : int) (L : list Z) : Prop :=
  PArray.length acc = CAP /\ (φ cnt) = Z.of_nat (List.length L) /\
  forall i, (i < List.length L)%nat -> acc.[of_Z (Z.of_nat i)] = nth i L 0.

(* the table has room for the factors of m *)
Definition room (L : list Z) (m : Z) : Prop :=
  2 ^ Z.of_nat (List.length L) * m <= 2 ^ 128.

Lemma zlength_set : forall (t : array Z) (i : int) (b : Z),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set Z t i b). Qed.

Lemma zget_set_same : forall (t : array Z) (i : int) (b : Z),
  (i <? PArray.length t)%uint63 = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same Z t i b H). Qed.

Lemma zget_set_other : forall (t : array Z) (i j : int) (b : Z),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other Z t i j b H). Qed.

Lemma zlength_make : forall (n : int) (b : Z),
  PArray.length (PArray.make n b)
  = if (n <=? PArray.max_length)%uint63 then n else PArray.max_length.
Proof. intros n b. exact (length_make Z n b). Qed.

Lemma CAP_val : (φ CAP) = 128.
Proof. reflexivity. Qed.

Lemma of_Z_small : forall z, 0 <= z < wB -> (φ (of_Z z)) = z.
Proof. intros z Hz. rewrite of_Z_spec. apply Z.mod_small. exact Hz. Qed.

Lemma tab_nil : tab (PArray.make CAP 0) 0%uint63 [].
Proof.
  split; [| split; [reflexivity | intros i Hi; simpl in Hi; lia]].
  rewrite zlength_make. reflexivity.
Qed.

Lemma push_spec : forall acc cnt L p, tab acc cnt L ->
  Z.of_nat (List.length L) < 128 ->
  tab (fst (push acc cnt p)) (snd (push acc cnt p)) (L ++ [p]).
Proof.
  intros acc cnt L p (Hl & Hc & Hg) HL. unfold push, tab; simpl.
  assert (Hc1 : (φ (cnt + 1))%uint63 = (φ cnt) + 1).
  { rewrite add_spec. apply Z.mod_small. change ((φ 1)%uint63) with 1. rewrite Hc.
    change wB with 9223372036854775808. lia. }
  split; [rewrite zlength_set; exact Hl|]. split.
  - rewrite Hc1, length_app, Nat2Z.inj_add, Hc. simpl. lia.
  - intros i Hi. rewrite length_app in Hi. simpl in Hi.
    destruct (Nat.eq_dec i (List.length L)) as [-> | E].
    + assert (Ei : of_Z (Z.of_nat (List.length L)) = cnt).
      { apply to_Z_inj. rewrite of_Z_small; [lia|]. change wB with 9223372036854775808. lia. }
      rewrite Ei, zget_set_same.
      * rewrite nth_middle. reflexivity.
      * rewrite ltb_spec, Hl, CAP_val. lia.
    + rewrite zget_set_other.
      * rewrite app_nth1 by lia. apply Hg. lia.
      * intros Ei. apply (f_equal to_Z) in Ei. rewrite of_Z_small in Ei;
          [lia | change wB with 9223372036854775808; lia].
Qed.

Lemma room_push : forall L m p, room L m -> 2 <= p -> (p | m) -> 1 <= m ->
  Z.of_nat (List.length L) < 128 /\ room (L ++ [p]) (m / p).
Proof.
  intros L m p HR Hp [k Hk] Hm. unfold room in *.
  assert (Hk1 : 1 <= k) by (apply (pos_factor k p m); [exact Hk | lia | lia]).
  assert (Hmp : m / p = k) by (rewrite Hk; apply Z.div_mul; lia).
  rewrite Hmp, length_app, Nat2Z.inj_add. simpl.
  rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r.
  pose proof (Z.pow_pos_nonneg 2 (Z.of_nat (List.length L)) ltac:(lia) ltac:(lia)) as P.
  split.
  - destruct (Z.lt_ge_cases (Z.of_nat (List.length L)) 128) as [|G]; [lia|].
    exfalso. apply (Z.pow_le_mono_r 2) in G; [| lia]. nia.
  - nia.
Qed.

Lemma room_app : forall L L' m m', room L m -> Forall prime L' ->
  product L' * m' = m -> 0 <= m' -> room (L ++ L') m'.
Proof.
  intros L L' m m' HR HP Hm Hm'. unfold room in *.
  rewrite length_app, Nat2Z.inj_add, Z.pow_add_r by lia.
  pose proof (pow2_le_product L' HP).
  pose proof (Z.pow_pos_nonneg 2 (Z.of_nat (List.length L)) ltac:(lia) ltac:(lia)).
  subst m. nia.
Qed.

Lemma room_le : forall L m m', room L m -> 0 <= m' <= m -> room L m'.
Proof.
  intros L m m' HR Hm. unfold room in *.
  pose proof (Z.pow_pos_nonneg 2 (Z.of_nat (List.length L)) ltac:(lia) ltac:(lia)). nia.
Qed.

(* ------------------------------------------------------------------ *)
(* Trial division                                                      *)
(* ------------------------------------------------------------------ *)

Lemma dguard_iff : forall m d, 2 <= d -> 1 <= m -> dguard m d = true <-> (d | m).
Proof.
  intros m d Hd Hm. unfold dguard.
  replace (1 <? d) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (0 <? m) with true by (symmetry; apply Z.ltb_lt; lia). simpl.
  rewrite Z.eqb_eq. apply Z.mod_divide. lia.
Qed.

Lemma divout_spec : forall m (H : Acc (Zwf 0) m) d acc cnt L,
  2 <= d -> 1 <= m -> nodiv m d -> tab acc cnt L -> room L m ->
  forall m' acc' cnt', divout m d acc cnt H = (m', acc', cnt') ->
  exists L', tab acc' cnt' (L ++ L') /\ Forall prime L' /\ product L' * m' = m /\
    1 <= m' /\ nodiv m' (d + 1) /\ room (L ++ L') m'.
Proof.
  intros m. induction m as [m IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros H d acc cnt L Hd Hm Hn Ht Hr m' acc' cnt' E.
  destruct H as [Hacc]. cbn [divout] in E.
  destruct (bdec (dguard m d)) as [Hg | Hg].
  - pose proof Hg as Hdm. apply dguard_iff in Hdm; [| lia | lia].
    destruct (room_push L m d Hr Hd Hdm Hm) as [HL Hr'].
    pose proof (push_spec acc cnt L d Ht HL) as Ht'.
    unfold push in E, Ht'. simpl in Ht'.
    assert (Hpd : prime d) by (apply (nodiv_prime m d); auto; lia).
    destruct Hdm as [k Hk].
    assert (Hk1 : 1 <= k) by (apply (pos_factor k d m); [exact Hk | lia | lia]).
    assert (Hmd : m / d = k) by (rewrite Hk; apply Z.div_mul; lia).
    assert (Hn' : nodiv (m / d) d).
    { rewrite Hmd. apply (nodiv_divisor m k d); [exists d; lia | exact Hn]. }
    destruct (IH (m / d) (dec_div m d Hg) _ d _ _ (L ++ [d]) Hd ltac:(lia) Hn' Ht' Hr'
                 m' acc' cnt' E) as (L'' & H1 & H2 & H3 & H4 & H5 & H6).
    { exists (d :: L''). rewrite <- app_assoc in H1, H6. simpl in H1, H6.
      split; [exact H1|]. split; [constructor; assumption|].
      split; [rewrite product_cons, <- Z.mul_assoc, H3, Hmd; lia|]. split; [exact H4|]. split; assumption. }
  - injection E as <- <- <-. exists []. rewrite app_nil_r.
    split; [exact Ht|]. split; [constructor|]. split; [rewrite product_nil; lia|].
    split; [lia|]. split; [| exact Hr].
    intros k Hk Hkm. destruct (Z.eq_dec k d) as [-> | Ne].
    + apply dguard_iff in Hkm; [| lia | lia]. congruence.
    + apply (Hn k); [lia | exact Hkm].
Qed.

Lemma trial_spec : forall B z d m acc cnt L (H : Acc (Zwf 0) (B - d)),
  B - d = z -> 2 <= d -> 1 <= m -> nodiv m d -> tab acc cnt L -> room L m ->
  forall m' d' acc' cnt', trial B m d acc cnt H = (m', d', acc', cnt') ->
  exists L', tab acc' cnt' (L ++ L') /\ Forall prime L' /\ product L' * m' = m /\
    1 <= m' /\ nodiv m' d' /\ d <= d' /\ (m' < d' * d' \/ B <= d') /\
    room (L ++ L') m'.
Proof.
  intros B z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros d m acc cnt L H Hz Hd Hm Hn Ht Hr m' d' acc' cnt' E.
  destruct H as [Hacc]. cbn [trial] in E.
  destruct (bdec (d <? B)) as [Hb | Hb].
  - destruct (m <? d * d) eqn:Em.
    + injection E as <- <- <- <-. exists []. rewrite app_nil_r.
      apply Z.ltb_lt in Em.
      split; [exact Ht|]. split; [constructor|]. split; [rewrite product_nil; lia|].
      split; [lia|]. split; [exact Hn|]. split; [lia|]. split; [lia | exact Hr].
    + destruct (divout m d acc cnt (Zwf_well_founded 0 m)) as [[m1 acc1] cnt1] eqn:Ed.
      destruct (divout_spec m _ d acc cnt L Hd Hm Hn Ht Hr m1 acc1 cnt1 Ed)
        as (L1 & H1 & H2 & H3 & H4 & H5 & H6).
      edestruct (IH (B - (d + 1)) ltac:(rewrite <- Hz; apply dec_bound; exact Hb)
                   (d + 1) m1 acc1 cnt1 (L ++ L1)) as (L2 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8);
        [reflexivity | lia | exact H4 | exact H5 | exact H1 | exact H6 | exact E |].
      exists (L1 ++ L2). rewrite app_assoc.
      split; [exact G1|]. split; [apply Forall_app; split; assumption|].
      split; [rewrite product_app; nia|]. split; [exact G4|]. split; [exact G5|].
      split; [lia|]. split; [exact G7 | exact G8].
  - injection E as <- <- <- <-. exists []. rewrite app_nil_r.
    apply Z.ltb_ge in Hb.
    split; [exact Ht|]. split; [constructor|]. split; [rewrite product_nil; lia|].
    split; [lia|]. split; [exact Hn|]. split; [lia|]. split; [lia | exact Hr].
Qed.

Lemma product_le : forall L m' m, Forall prime L -> product L * m' = m -> 1 <= m' ->
  m' <= m.
Proof. intros L m' m HP E H. pose proof (product_pos L HP). nia. Qed.

Lemma fallback_spec : forall m lo acc cnt L,
  2 <= lo -> 1 <= m -> nodiv m lo -> tab acc cnt L -> room L m ->
  exists L', tab (fst (fallback m lo acc cnt)) (snd (fallback m lo acc cnt)) (L ++ L') /\
    Forall prime L' /\ product L' = m.
Proof.
  intros m lo acc cnt L Hlo Hm Hn Ht Hr. unfold fallback.
  destruct (trial (m + 2) m lo acc cnt (Zwf_well_founded 0 (m + 2 - lo)))
    as [[[r d] acc1] cnt1] eqn:E.
  destruct (trial_spec (m + 2) _ lo m acc cnt L _ eq_refl Hlo Hm Hn Ht Hr r d acc1 cnt1 E)
    as (L1 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  pose proof (product_le L1 r m H2 H3 H4) as Hrm.
  assert (Hsq : r < d * d) by (destruct H7 as [H7 | H7]; [exact H7 | nia]).
  destruct (1 <? r) eqn:Er.
  - apply Z.ltb_lt in Er.
    assert (Hpr : prime r) by (apply (prime_of_nodiv_sq r d); auto; lia).
    destruct (room_push (L ++ L1) r r H8 ltac:(lia) (Z.divide_refl r) ltac:(lia)) as [HL _].
    pose proof (push_spec acc1 cnt1 (L ++ L1) r H1 HL) as Hp.
    exists (L1 ++ [r]). rewrite app_assoc. split; [exact Hp|].
    split; [apply Forall_app; split; [exact H2 | constructor; [exact Hpr | constructor]]|].
    rewrite product_app, product_cons, product_nil. lia.
  - apply Z.ltb_ge in Er. assert (r = 1) by lia. subst r.
    exists L1. simpl. split; [exact H1|]. split; [exact H2 | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* The certificate check                                               *)
(* ------------------------------------------------------------------ *)

Definition qcond (r a q : Z) : Prop := zgcd (powmod a ((r - 1) / q) r - 1) r = 1.

Lemma all_q_spec : forall r a qs qc z i (H : Acc (Zwf 0) (gap qc i)),
  gap qc i = z ->
  (forall j : int, (φ j) < (φ i) -> qcond r a qs.[j]) ->
  all_q r a qs qc i H = true ->
  forall j : int, (φ j) < (φ qc) -> qcond r a qs.[j].
Proof.
  intros r a qs qc z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i H Hz Hinv E. destruct H as [Hacc]. cbn [all_q] in E.
  destruct (bdec (i <? qc)%uint63) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    assert (Hi1 : (φ (i + 1))%uint63 = (φ i) + 1) by sia.
    assert (Step : qcond r a qs.[i] ->
              forall j : int, (φ j) < (φ (i + 1))%uint63 -> qcond r a qs.[j]).
    { intros Hc j Hj. rewrite Hi1 in Hj. destruct (Z.eq_dec (φ j) (φ i)) as [Ej | Ej].
      - apply to_Z_inj in Ej. subst j. exact Hc.
      - apply Hinv. lia. }
    destruct ((0 <? i)%uint63 && (qs.[i] =? qs.[(i - 1)%uint63])) eqn:Es.
    + apply andb_prop in Es as [Es1 Es2]. rewrite ltb_spec in Es1.
      change ((φ 0)%uint63) with 0 in Es1. apply Z.eqb_eq in Es2.
      eapply IH; [| reflexivity | | exact E].
      * rewrite <- Hz. apply dec_step. exact Hi.
      * apply Step. rewrite Es2. apply Hinv. sia.
    + destruct (zgcd (powmod a ((r - 1) / qs.[i]) r - 1) r =? 1) eqn:Eg; [| discriminate].
      apply Z.eqb_eq in Eg.
      eapply IH; [| reflexivity | | exact E].
      * rewrite <- Hz. apply dec_step. exact Hi.
      * apply Step. exact Eg.
  - intros j Hj. apply Hinv. rewrite <- Bool.not_true_iff_false, ltb_spec in Hi. lia.
Qed.

Lemma cert_try_spec : forall r qs qc z a k (H : Acc (Zwf 0) (φ k)), (φ k) = z ->
  cert_try r qs qc a k H = true -> exists a', lucas_ok r a' qs qc = true.
Proof.
  intros r qs qc z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros a k H Hz E. destruct H as [Hacc]. cbn [cert_try] in E.
  destruct (bdec (0 <? k)%uint63) as [Hk | Hk]; [| discriminate].
  destruct (lucas_ok r a qs qc) eqn:El; [exists a; exact El|].
  eapply IH; [| reflexivity | exact E]. rewrite <- Hz. apply dec_down. exact Hk.
Qed.

Lemma certify_sound : forall r qs qc Q, 2 <= r ->
  tab qs qc Q -> Forall prime Q -> product Q = r - 1 ->
  certify r qs qc = true -> prime r.
Proof.
  intros r qs qc Q Hr (Hl & Hc & Hg) HQ HP E. unfold certify in E.
  destruct (cert_try_spec r qs qc _ 2 1000%uint63 _ eq_refl E) as [a Ea].
  unfold lucas_ok in Ea. apply andb_prop in Ea as [E1 E2].
  apply Z.eqb_eq in E1. rewrite powmod_spec in E1 by lia.
  pose proof (all_q_spec r a qs qc _ 0%uint63 _ eq_refl
                ltac:(intros j Hj; change ((φ 0)%uint63) with 0 in Hj;
                      pose proof (to_Z_bounded j); lia) E2) as Hall.
  apply (lucas r a Q Hr HQ HP E1).
  intros q Hq. destruct (In_nth Q q 0 Hq) as (i & Hi & Hqi).
  assert (Hqp : prime q) by (rewrite Forall_forall in HQ; auto).
  pose proof (prime_ge_2 q Hqp).
  assert (Hj : (φ (of_Z (Z.of_nat i))) < (φ qc)).
  { rewrite of_Z_small; [lia|]. change wB with 9223372036854775808.
    pose proof (to_Z_bounded qc). lia. }
  specialize (Hall _ Hj). unfold qcond in Hall.
  rewrite Hg, Hqi in Hall by exact Hi.
  rewrite zgcd_spec, powmod_spec in Hall; [exact Hall | lia |].
  apply Z.div_pos; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The factorisation                                                   *)
(* ------------------------------------------------------------------ *)

Definition fac_post (L : list Z) (m : Z) (res : array Z * int) : Prop :=
  exists L', tab (fst res) (snd res) (L ++ L') /\ Forall prime L' /\ product L' = m.

Lemma push_prime_ok : forall L L1 acc1 cnt1 r m,
  tab acc1 cnt1 (L ++ L1) -> room (L ++ L1) r -> prime r -> Forall prime L1 ->
  product L1 * r = m -> fac_post L m (push acc1 cnt1 r).
Proof.
  intros L L1 acc1 cnt1 r m Ht Hr Hp HL1 Hm. pose proof (prime_ge_2 r Hp).
  destruct (room_push (L ++ L1) r r Hr ltac:(lia) (Z.divide_refl r) ltac:(lia)) as [HL _].
  pose proof (push_spec acc1 cnt1 (L ++ L1) r Ht HL) as Hp'.
  exists (L1 ++ [r]). rewrite app_assoc. split; [exact Hp'|].
  split; [apply Forall_app; split; [exact HL1 | constructor; [exact Hp | constructor]]|].
  rewrite product_app, product_cons, product_nil. lia.
Qed.

Lemma fallback_ok : forall L L1 acc1 cnt1 r d m,
  2 <= d -> 1 <= r -> nodiv r d ->
  tab acc1 cnt1 (L ++ L1) -> room (L ++ L1) r -> Forall prime L1 ->
  product L1 * r = m -> fac_post L m (fallback r d acc1 cnt1).
Proof.
  intros L L1 acc1 cnt1 r d m Hd Hr Hn Ht Hro HL1 Hm.
  destruct (fallback_spec r d acc1 cnt1 (L ++ L1) Hd Hr Hn Ht Hro) as (L2 & H1 & H2 & H3).
  exists (L1 ++ L2). rewrite app_assoc. split; [exact H1|].
  split; [apply Forall_app; split; assumption|]. rewrite product_app. lia.
Qed.

Lemma room_nil : forall L m m', room L m -> 0 <= m' <= m -> room [] m'.
Proof.
  intros L m m' HR Hm. unfold room in *. cbn [List.length Z.of_nat]. rewrite Z.pow_0_r.
  pose proof (Z.pow_pos_nonneg 2 (Z.of_nat (List.length L)) ltac:(lia) ltac:(lia)). nia.
Qed.

Lemma fac_spec : forall m (H : Acc (Zwf 0) m) lo acc cnt L,
  2 <= lo -> 1 <= m -> nodiv m lo -> tab acc cnt L -> room L m ->
  fac_post L m (fac m lo acc cnt H).
Proof.
  intros m. induction m as [m IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros H lo acc cnt L Hlo Hm Hn Ht Hr. destruct H as [Hacc]. cbn [fac].
  destruct (trial B0 m lo acc cnt (Zwf_well_founded 0 (B0 - lo)))
    as [[[r d] acc1] cnt1] eqn:E.
  destruct (trial_spec B0 _ lo m acc cnt L _ eq_refl Hlo Hm Hn Ht Hr r d acc1 cnt1 E)
    as (L1 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  destruct (r <? d * d) eqn:Esq.
  - apply Z.ltb_lt in Esq. destruct (1 <? r) eqn:E1.
    + apply Z.ltb_lt in E1.
      apply (push_prime_ok L L1 acc1 cnt1 r m H1 H8); [| exact H2 | exact H3].
      apply (prime_of_nodiv_sq r d); auto; lia.
    + apply Z.ltb_ge in E1. assert (r = 1) by lia. subst r.
      exists L1. split; [exact H1|]. split; [exact H2 | lia].
  - apply Z.ltb_ge in Esq.
    assert (HdB : B0 <= d) by (destruct H7; [lia | assumption]).
    assert (Hr2 : B0 * B0 <= r).
    { assert (B0 * B0 <= d * d) by (apply Z.mul_le_mono_nonneg; unfold B0 in *; lia). lia. }
    unfold B0 in Hr2.
    assert (Hrm : r <= m) by (apply (product_le L1 r m); auto).
    destruct (miller_rabin r).
    + destruct (bdec (guard (r - 1) m)) as [G | G].
      * destruct (fac (r - 1) 2 (PArray.make CAP 0) 0%uint63 (Acc_inv (Acc_intro m Hacc) (guard_ok _ _ G)))
          as [qs qc] eqn:Ef.
        assert (A1 : 2 <= 2) by lia.
        assert (A2 : 1 <= r - 1) by lia.
        assert (A3 : nodiv (r - 1) 2) by (intros k Hk; exfalso; lia).
        assert (A4 : room [] (r - 1)) by (apply (room_nil (L ++ L1) r); [exact H8 | lia]).
        destruct (IH (r - 1) (guard_ok _ _ G) (Acc_inv (Acc_intro m Hacc) (guard_ok _ _ G)) 2
                    (PArray.make CAP 0) 0%uint63 [] A1 A2 A3 tab_nil A4)
          as (Q & Q1 & Q2 & Q3).
        rewrite Ef in Q1. simpl in Q1.
        destruct (certify r qs qc) eqn:Ec.
        -- apply (push_prime_ok L L1 acc1 cnt1 r m H1 H8); [| exact H2 | exact H3].
           apply (certify_sound r qs qc Q); auto; lia.
        -- apply (fallback_ok L L1 acc1 cnt1 r d m); auto; lia.
      * apply (fallback_ok L L1 acc1 cnt1 r d m); auto; lia.
    + destruct ((1 <? rho r) && (rho r <? r) && (r mod rho r =? 0)) eqn:Eg.
      * apply andb_prop in Eg as [Eg Eg3]. apply andb_prop in Eg as [Eg1 Eg2].
        apply Z.ltb_lt in Eg1. apply Z.ltb_lt in Eg2. apply Z.eqb_eq in Eg3.
        apply Z.mod_divide in Eg3; [| lia].
        set (g := rho r) in *.
        destruct Eg3 as [h Hh].
        assert (Hh1 : 1 <= h) by (apply (pos_factor h g r); [exact Hh | lia | lia]).
        assert (Hrg : r / g = h) by (rewrite Hh; apply Z.div_mul; lia).
        destruct (bdec (guard g m)) as [G1 | G1]; [| apply (fallback_ok L L1 acc1 cnt1 r d m); auto; lia].
        destruct (bdec (guard (r / g) m)) as [G2 | G2]; [| apply (fallback_ok L L1 acc1 cnt1 r d m); auto; lia].
        assert (HnB : nodiv r B0) by (apply (nodiv_mono r d); auto).
        destruct (fac g B0 acc1 cnt1 (Acc_inv (Acc_intro m Hacc) (guard_ok _ _ G1))) as [acc2 cnt2] eqn:F1.
        destruct (IH g (guard_ok _ _ G1) (Acc_inv (Acc_intro m Hacc) (guard_ok _ _ G1)) B0 acc1 cnt1 (L ++ L1)
                    ltac:(unfold B0; lia) ltac:(lia)
                    ltac:(apply (nodiv_divisor r g B0); [exists h; lia | exact HnB])
                    H1 ltac:(apply (room_le _ r); [exact H8 | lia]))
          as (L2 & K1 & K2 & K3).
        rewrite F1 in K1. simpl in K1.
        destruct (IH (r / g) (guard_ok _ _ G2) (Acc_inv (Acc_intro m Hacc) (guard_ok _ _ G2)) B0 acc2 cnt2
                    ((L ++ L1) ++ L2)
                    ltac:(unfold B0; lia) ltac:(lia)
                    ltac:(apply (nodiv_divisor r (r / g) B0); [exists g; lia | exact HnB])
                    K1 ltac:(apply (room_app (L ++ L1) L2 r); [exact H8 | exact K2 | lia | lia]))
          as (L3 & J1 & J2 & J3).
        exists (L1 ++ L2 ++ L3). rewrite !app_assoc. split; [exact J1|].
        split; [apply Forall_app; split; [apply Forall_app; split |]; assumption|].
        rewrite !product_app, K3, J3, Hrg. lia.
      * apply (fallback_ok L L1 acc1 cnt1 r d m); auto; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Cells of an array, as a list (Prop side only)                       *)
(* ------------------------------------------------------------------ *)

Definition at_ (a : array Z) (k : Z) : Z := a.[of_Z k].

Fixpoint cells (a : array Z) (k : nat) : list Z :=
  match k with
  | O => []
  | S k => cells a k ++ [at_ a (Z.of_nat k)]
  end.

Lemma cells_length : forall a k, List.length (cells a k) = k.
Proof.
  intros a k. induction k as [| k IH]; [reflexivity|].
  simpl. rewrite length_app, IH. simpl. lia.
Qed.

Lemma cells_nth : forall a k i, (i < k)%nat -> nth i (cells a k) 0 = at_ a (Z.of_nat i).
Proof.
  intros a k. induction k as [| k IH]; intros i Hi; [lia|]. simpl.
  destruct (Nat.eq_dec i k) as [-> | E].
  - rewrite app_nth2; rewrite cells_length; [| lia]. rewrite Nat.sub_diag. reflexivity.
  - rewrite app_nth1 by (rewrite cells_length; lia). apply IH. lia.
Qed.

Lemma cells_ext : forall a b k, (forall i, 0 <= i < Z.of_nat k -> at_ a i = at_ b i) ->
  cells a k = cells b k.
Proof.
  intros a b k. induction k as [| k IH]; intros H; [reflexivity|]. simpl.
  rewrite IH by (intros i Hi; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma cells_eq_list : forall a L, (forall i, (i < List.length L)%nat -> at_ a (Z.of_nat i) = nth i L 0) ->
  cells a (List.length L) = L.
Proof.
  intros a L H. apply nth_ext with (d := 0) (d' := 0); [apply cells_length|].
  intros i Hi. rewrite cells_length in Hi. rewrite cells_nth by exact Hi. apply H. exact Hi.
Qed.

(* the product is unchanged by exchanging cells p and p + 1 *)
Lemma cells_swap_product : forall a a' (p K : nat),
  at_ a' (Z.of_nat p) = at_ a (Z.of_nat p + 1) ->
  at_ a' (Z.of_nat p + 1) = at_ a (Z.of_nat p) ->
  (forall i, 0 <= i < Z.of_nat K -> i <> Z.of_nat p -> i <> Z.of_nat p + 1 ->
     at_ a' i = at_ a i) ->
  forall k, (k <= K)%nat -> (k <= p \/ p + 2 <= k)%nat ->
  product (cells a' k) = product (cells a k).
Proof.
  intros a a' p K Hp Hp1 Ho k. induction k as [| k IH]; intros HK Hk; [reflexivity|].
  destruct (Nat.eq_dec (S k) (p + 2)) as [E | E].
  - assert (k = S p) by lia. subst k. simpl.
    rewrite !product_app, !product_cons, !product_nil.
    rewrite (cells_ext a' a p) by (intros i Hi; apply Ho; lia).
    rewrite !Zpos_P_of_succ_nat. unfold Z.succ. rewrite Hp, Hp1. ring.
  - simpl. rewrite !product_app, IH by lia. rewrite Ho by lia. reflexivity.
Qed.

(* sorted from adjacent pairs *)
Lemma sorted_adj : forall l : list Z,
  (forall i, (S i < List.length l)%nat -> nth i l 0 <= nth (S i) l 0) -> Sorted Z.le l.
Proof.
  intros l. induction l as [| x l IH]; intros H; [constructor|].
  constructor.
  - apply IH. intros i Hi. apply (H (S i)). simpl. lia.
  - destruct l as [| y l]; constructor. apply (H 0%nat). simpl. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* copy                                                                *)
(* ------------------------------------------------------------------ *)

Lemma copy_spec : forall src n z dst i (H : Acc (Zwf 0) (gap n i)),
  gap n i = z -> PArray.length dst = n -> (φ i) <= (φ n) ->
  (forall k, 0 <= k < (φ i) -> at_ dst k = at_ src k) ->
  PArray.length (copy src dst n i H) = n /\
  forall k, 0 <= k < (φ n) -> at_ (copy src dst n i H) k = at_ src k.
Proof.
  intros src n z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros dst i H Hz Hl Hi Hinv. destruct H as [Hacc]. cbn [copy].
  destruct (bdec (i <? n)%uint63) as [Hlt | Hlt].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Hi1 : (φ (i + 1))%uint63 = (φ i) + 1) by sia.
    eapply IH; [| reflexivity | | | ].
    + rewrite <- Hz. apply dec_step. exact Hlt.
    + rewrite zlength_set. exact Hl.
    + lia.
    + intros k Hk. rewrite Hi1 in Hk. unfold at_.
      pose proof (to_Z_bounded i). pose proof (to_Z_bounded n).
      destruct (Z.eq_dec k (φ i)) as [-> | E].
      * rewrite of_to_Z, zget_set_same by (rewrite Hl; exact Hlt). reflexivity.
      * rewrite zget_set_other.
        -- apply Hinv. lia.
        -- intros F. apply E. rewrite F, of_Z_small; [reflexivity | lia].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt. split; [exact Hl|].
    intros k Hk. apply Hinv. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Insertion sort                                                      *)
(* ------------------------------------------------------------------ *)

Definition allprime (a : array Z) (n : Z) : Prop := forall k, 0 <= k < n -> prime (at_ a k).

(* the pairs (k, k + 1) with k + 1 <= t are in order *)
Definition adj_upto (a : array Z) (t : Z) : Prop :=
  forall k, 0 <= k -> k + 1 <= t -> at_ a k <= at_ a (k + 1).

Lemma zlength_bound : forall (t : array Z), (φ (PArray.length t)) <= 4194303.
Proof.
  intros t. pose proof (leb_length Z t) as H.
  rewrite leb_spec in H. exact H.
Qed.

Lemma swap_get : forall (a : array Z) (j : int) (x y k : Z),
  0 < (φ j) < (φ (PArray.length a)) -> 0 <= k < wB ->
  at_ (a.[(j - 1)%uint63 <- y].[j <- x]) k =
  if k =? (φ j) then x else if k =? (φ j) - 1 then y else at_ a k.
Proof.
  intros a j x y k Hj Hk. unfold at_.
  assert (Hj1 : (φ (j - 1))%uint63 = (φ j) - 1) by sia.
  destruct (Z.eqb_spec k (φ j)) as [-> | E1].
  - rewrite of_to_Z, zget_set_same; [reflexivity|]. rewrite zlength_set, ltb_spec. lia.
  - rewrite zget_set_other.
    2:{ intros F. apply E1. rewrite F, of_Z_small; [reflexivity | exact Hk]. }
    destruct (Z.eqb_spec k ((φ j) - 1)) as [-> | E2].
    + replace (of_Z ((φ j) - 1)) with (j - 1)%uint63.
      2:{ apply to_Z_inj. rewrite Hj1, of_Z_small; [reflexivity | lia]. }
      rewrite zget_set_same; [reflexivity|]. rewrite ltb_spec. lia.
    + rewrite zget_set_other; [reflexivity|].
      intros F. apply E2. rewrite <- Hj1, F, of_Z_small; [reflexivity | exact Hk].
Qed.

Lemma sink_spec : forall (n i z : Z) (a : array Z) (j : int) (H : Acc (Zwf 0) (φ j)),
  (φ j) = z -> (φ (PArray.length a)) = n -> 0 <= (φ j) <= i -> i < n ->
  (forall k, 0 <= k -> k + 1 <= i -> k + 1 <> (φ j) -> at_ a k <= at_ a (k + 1)) ->
  (0 < (φ j) < i -> at_ a ((φ j) - 1) <= at_ a ((φ j) + 1)) ->
  forall a', sink a j H = a' ->
  PArray.length a' = PArray.length a /\ (allprime a n -> allprime a' n) /\
  product (cells a' (Z.to_nat n)) = product (cells a (Z.to_nat n)) /\ adj_upto a' i.
Proof.
  intros n i z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros a j H Hz Hn Hj Hi Hadj Hext a' E. destruct H as [Hacc]. cbn [sink] in E.
  pose proof (zlength_bound a) as Bn.
  destruct (bdec (0 <? j)%uint63) as [Hj0 | Hj0].
  - pose proof Hj0 as Hj0'. rewrite ltb_spec in Hj0'. change ((φ 0)%uint63) with 0 in Hj0'.
    assert (Hj1 : (φ (j - 1))%uint63 = (φ j) - 1) by sia.
    assert (Ex : a.[(j - 1)%uint63] = at_ a ((φ j) - 1)).
    { unfold at_. f_equal. apply to_Z_inj. rewrite Hj1, of_Z_small; [reflexivity | lia]. }
    assert (Ey : a.[j] = at_ a (φ j)) by (unfold at_; rewrite of_to_Z; reflexivity).
    rewrite Ex, Ey in E.
    destruct (at_ a (φ j) <? at_ a ((φ j) - 1)) eqn:Elt.
    + apply Z.ltb_lt in Elt.
      set (a1 := a.[(j - 1)%uint63 <- at_ a (φ j)].[j <- at_ a ((φ j) - 1)]) in E.
      assert (Hl1 : PArray.length a1 = PArray.length a) by (unfold a1; rewrite !zlength_set; reflexivity).
      assert (G : forall k, 0 <= k < n -> at_ a1 k =
                if k =? (φ j) then at_ a ((φ j) - 1) else if k =? (φ j) - 1 then at_ a (φ j) else at_ a k).
      { intros k Hk. unfold a1. apply swap_get; [lia | change wB with 9223372036854775808; lia]. }
      assert (Hadj1 : forall k, 0 <= k -> k + 1 <= i -> k + 1 <> (φ (j - 1))%uint63 ->
                        at_ a1 k <= at_ a1 (k + 1)).
      { intros k Hk0 Hk1 Hk2. rewrite Hj1 in Hk2. rewrite !G by lia.
        destruct (Z.eqb_spec k (φ j)) as [K1 | K1];
          destruct (Z.eqb_spec k ((φ j) - 1)) as [K2 | K2];
          destruct (Z.eqb_spec (k + 1) (φ j)) as [K3 | K3];
          destruct (Z.eqb_spec (k + 1) ((φ j) - 1)) as [K4 | K4]; try lia.
        - replace k with (φ j) by lia. apply Hext. lia.
        - apply Hadj; lia. }
      assert (Hext1 : 0 < (φ (j - 1))%uint63 < i ->
                      at_ a1 ((φ (j - 1))%uint63 - 1) <= at_ a1 ((φ (j - 1))%uint63 + 1)).
      { rewrite Hj1. intros Hc. rewrite !G by lia.
        destruct (Z.eqb_spec ((φ j) - 1 - 1) (φ j)) as [K1 | K1]; [lia|].
        destruct (Z.eqb_spec ((φ j) - 1 - 1) ((φ j) - 1)) as [K2 | K2]; [lia|].
        destruct (Z.eqb_spec ((φ j) - 1 + 1) (φ j)) as [K3 | K3]; [| lia].
        replace ((φ j) - 1) with ((φ j) - 1 - 1 + 1) at 2 by lia. apply Hadj; lia. }
      destruct (IH ((φ (j - 1))%uint63) ltac:(unfold Zwf; lia) a1 (j - 1)%uint63
                  (Acc_inv (Acc_intro _ Hacc) (dec_down j Hj0)) eq_refl
                  ltac:(rewrite Hl1; exact Hn) ltac:(lia) Hi Hadj1 Hext1 a' E)
        as (R1 & R2 & R3 & R4).
      split; [rewrite R1; exact Hl1|]. split; [| split; [| exact R4]].
        -- intros Hp. apply R2. intros k Hk. rewrite G by lia.
           destruct (k =? (φ j)); [apply Hp; lia|].
           destruct (k =? (φ j) - 1); apply Hp; lia.
        -- rewrite R3. apply (cells_swap_product a a1 (Z.to_nat ((φ j) - 1)) (Z.to_nat n)).
           ++ rewrite Z2Nat.id, G by lia.
              destruct (Z.eqb_spec ((φ j) - 1) (φ j)); [lia|].
              rewrite Z.eqb_refl. f_equal. lia.
           ++ rewrite Z2Nat.id, G by lia. replace ((φ j) - 1 + 1) with (φ j) by lia.
              rewrite Z.eqb_refl. reflexivity.
           ++ intros k Hk Hk1 Hk2. rewrite Z2Nat.id in Hk, Hk1, Hk2 by lia.
              rewrite G by lia.
              destruct (Z.eqb_spec k (φ j)); [lia|].
              destruct (Z.eqb_spec k ((φ j) - 1)); [lia | reflexivity].
           ++ lia.
           ++ right. lia.
    + apply Z.ltb_ge in Elt. subst a'.
      split; [reflexivity|]. split; [auto|]. split; [reflexivity|].
      intros k Hk0 Hk1. destruct (Z.eq_dec (k + 1) (φ j)) as [K | K].
      * replace k with ((φ j) - 1) by lia. replace ((φ j) - 1 + 1) with (φ j) by lia. exact Elt.
      * apply Hadj; assumption.
  - subst a'. rewrite <- Bool.not_true_iff_false, ltb_spec in Hj0.
    change ((φ 0)%uint63) with 0 in Hj0.
    split; [reflexivity|]. split; [auto|]. split; [reflexivity|].
    intros k Hk0 Hk1. apply Hadj; lia.
Qed.

Lemma isort_spec : forall n z a i (H : Acc (Zwf 0) (gap n i)),
  gap n i = z -> PArray.length a = n -> 1 <= (φ i) -> adj_upto a ((φ i) - 1) ->
  forall a', isort a n i H = a' ->
  PArray.length a' = n /\ (allprime a (φ n) -> allprime a' (φ n)) /\
  product (cells a' (Z.to_nat (φ n))) = product (cells a (Z.to_nat (φ n))) /\
  adj_upto a' ((φ n) - 1).
Proof.
  intros n z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros a i H Hz Hl Hi Hadj a' E. destruct H as [Hacc]. cbn [isort] in E.
  unfold adj_upto in Hadj.
  destruct (bdec (i <? n)%uint63) as [Hlt | Hlt].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Hi1 : (φ (i + 1))%uint63 = (φ i) + 1) by sia.
    assert (A1 : forall k, 0 <= k -> k + 1 <= (φ i) -> k + 1 <> (φ i) -> at_ a k <= at_ a (k + 1))
      by (intros k Hk0 Hk1 Hk2; apply Hadj; lia).
    assert (A2 : 0 < (φ i) < (φ i) -> at_ a ((φ i) - 1) <= at_ a ((φ i) + 1)) by (intros; lia).
    destruct (sink_spec (φ n) (φ i) _ a i (Zwf_well_founded 0 (φ i)) eq_refl
                ltac:(rewrite Hl; reflexivity) ltac:(pose proof (to_Z_bounded i); lia) Hlt'
                A1 A2 _ eq_refl) as (S1 & S2 & S3 & S4).
    assert (A3 : adj_upto (sink a i (Zwf_well_founded 0 (φ i))) ((φ (i + 1))%uint63 - 1)).
    { rewrite Hi1. replace ((φ i) + 1 - 1) with (φ i) by lia. exact S4. }
    destruct (IH (gap n (i + 1)%uint63) ltac:(rewrite <- Hz; apply dec_step; exact Hlt)
                (sink a i (Zwf_well_founded 0 (φ i))) (i + 1)%uint63
                (Acc_inv (Acc_intro _ Hacc) (dec_step n i Hlt)) eq_refl
                ltac:(rewrite S1; exact Hl) ltac:(lia) A3 a' E) as (T1 & T2 & T3 & T4).
    split; [exact T1|]. split; [auto|]. split; [rewrite T3; exact S3 | exact T4].
  - subst a'. rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt.
    split; [exact Hl|]. split; [auto|]. split; [reflexivity|].
    intros k Hk0 Hk1. apply Hadj; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma bigfactoring_impl_correct : forall (n : Z) (x : Z),
  valid_input n -> repr x n ->
  exists fs : list Z, repr (bigfactoring_impl x) fs /\ bigfactoring_spec n fs.
Proof.
  intros n x [Hv] Hx. unfold repr, repr_Z in Hx. subst x.
  assert (B24 : 10 ^ 24 <= 2 ^ 128) by (apply Z.leb_le; reflexivity).
  assert (B80 : 10 ^ 24 < 2 ^ 80) by (apply Z.ltb_lt; reflexivity).
  assert (Hroom : room [] n).
  { unfold room. cbn [List.length Z.of_nat]. rewrite Z.pow_0_r. lia. }
  unfold bigfactoring_impl.
  destruct (fac n 2 (PArray.make CAP 0) 0%uint63 (Zwf_well_founded 0 n)) as [acc cnt] eqn:Ef.
  destruct (fac_spec n (Zwf_well_founded 0 n) 2 _ _ [] ltac:(lia) ltac:(lia)
              ltac:(intros k Hk; exfalso; lia) tab_nil Hroom) as (L & HL1 & HL2 & HL3).
  rewrite Ef in HL1. simpl in HL1. destruct HL1 as (Hal & Hc & Hg).
  (* at most 79 factors *)
  assert (HL80 : Z.of_nat (List.length L) < 80).
  { pose proof (pow2_le_product L HL2) as P.
    destruct (Z.lt_ge_cases (Z.of_nat (List.length L)) 80) as [|G]; [assumption|].
    apply (Z.pow_le_mono_r 2) in G; lia. }
  pose proof (to_Z_bounded cnt) as Bc.
  assert (Hmk : PArray.length (PArray.make cnt (0 : Z)) = cnt).
  { rewrite zlength_make.
    replace (cnt <=? PArray.max_length)%uint63 with true; [reflexivity|].
    symmetry. rewrite leb_spec. change (φ PArray.max_length) with 4194303. lia. }
  destruct (copy_spec acc cnt _ (PArray.make cnt 0) 0%uint63 (Zwf_well_founded 0 (gap cnt 0))
              eq_refl Hmk ltac:(change ((φ 0)%uint63) with 0; lia)
              ltac:(intros k Hk; change ((φ 0)%uint63) with 0 in Hk; lia)) as (C1 & C2).
  set (out := copy acc (PArray.make cnt 0) cnt 0%uint63 (Zwf_well_founded 0 (gap cnt 0))) in *.
  assert (A0 : adj_upto out ((φ 1)%uint63 - 1)).
  { intros k Hk0 Hk1. change ((φ 1)%uint63) with 1 in Hk1. lia. }
  destruct (isort_spec cnt _ out 1%uint63 (Zwf_well_founded 0 (gap cnt 1)) eq_refl C1
              ltac:(change ((φ 1)%uint63) with 1; lia) A0 _ eq_refl) as (T1 & T2 & T3 & T4).
  set (res := isort out cnt 1 (Zwf_well_founded 0 (gap cnt 1))) in *.
  assert (Hn : Z.to_nat (φ cnt) = List.length L) by lia.
  rewrite Hn in T3.
  (* the copy holds L *)
  assert (Hout : forall i, (i < List.length L)%nat -> at_ out (Z.of_nat i) = nth i L 0).
  { intros i Hi. rewrite C2 by lia. apply Hg. exact Hi. }
  assert (Hcells : cells out (List.length L) = L) by (apply cells_eq_list; exact Hout).
  assert (Hprime : allprime out (φ cnt)).
  { intros k Hk. replace k with (Z.of_nat (Z.to_nat k)) by lia.
    rewrite Hout by lia. apply Forall_nth; [exact HL2 | lia]. }
  specialize (T2 Hprime).
  set (fs := cells res (List.length L)).
  assert (Hfl : List.length fs = List.length L) by apply cells_length.
  assert (Hlen : Z.of_nat (List.length fs) = (φ (PArray.length res))) by (rewrite T1, Hfl; lia).
  assert (Hget : forall k : nat, (k < List.length fs)%nat ->
            nth_error fs k = Some (res.[of_Z (Z.of_nat k)])).
  { intros k Hk. rewrite (nth_error_nth' fs 0 Hk). f_equal.
    unfold fs. rewrite cells_nth by lia. reflexivity. }
  exists fs. split.
  - split; [exact Hlen|].
    intros k Hk. exists (res.[of_Z (Z.of_nat k)]). split; [exact (Hget k Hk) | reflexivity].
  - split; [| split].
    + apply Forall_forall. intros q Hq. destruct (In_nth fs q 0 Hq) as (i & Hi & <-).
      unfold fs. rewrite cells_nth by lia. apply T2. lia.
    + apply sorted_adj. intros i Hi. unfold fs. rewrite Hfl in Hi.
      rewrite !cells_nth by lia. rewrite Nat2Z.inj_succ. apply T4; lia.
    + unfold fs. rewrite T3, Hcells. exact HL3.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition bigfactoring : Z -> array Z := bigfactoring_impl.

Definition bigfactoring_correct : forall (n : Z) (x : Z),
  valid_input n -> repr x n ->
  exists fs : list Z, repr (bigfactoring x) fs /\ bigfactoring_spec n fs
  := bigfactoring_impl_correct.
