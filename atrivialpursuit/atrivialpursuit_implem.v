(* Executable implementation and its required termination dependencies.
   Correctness proofs are in atrivialpursuit_proofs.v. *)
From Atrivialpursuit.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Znumtheory Permutation.
Import ListNotations.

Unset Lia Cache.
Local Notation length := List.length.
Open Scope bool_scope.
Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ================================================================== *)
(* Part 5. The program                                                 *)
(* ================================================================== *)

Section Code.
Local Open Scope uint63_scope.
Local Open Scope array_scope.


Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma lsr1 : forall e, (φ (e >> 1)) = ((φ e) / 2)%Z.
Proof. intros e. rewrite lsr_spec. reflexivity. Qed.

Lemma dec_step : forall m i : int, (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia. unfold Zwf, gap. lia.
Qed.

Lemma dec_lt : forall x y : int, (y <? x) = true -> Zwf 0 (φ y) (φ x).
Proof. intros x y H. rewrite ltb_spec in H. pose proof (to_Z_bounded y). unfold Zwf. lia. Qed.

Lemma dec_shr : forall e : int, (0 <? e) = true -> Zwf 0 (φ (e >> 1)) (φ e).
Proof.
  intros e H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H. rewrite lsr1. unfold Zwf.
  split; [lia|]. apply Z.div_lt; lia.
Qed.

Lemma dec_mod : forall a b : int, (0 <? b) = true -> Zwf 0 (φ (a mod b)) (φ b).
Proof.
  intros a b H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H. rewrite mod_spec. unfold Zwf.
  split; [lia|]. apply Z.mod_pos_bound; lia.
Qed.

Lemma dec_div : forall x c : int, (1 <? x) = true -> (0 <? c) = true -> Zwf 0 (φ (c / x)) (φ c).
Proof.
  intros x c Hx Hc. rewrite ltb_spec in Hx, Hc. change (φ 0) with 0%Z in Hc. change (φ 1) with 1%Z in Hx.
  rewrite div_spec. unfold Zwf. split; [lia|]. apply Z.div_lt; lia.
Qed.

Lemma dec_isq1 : forall w : int, (1 <? w) = true -> Zwf 0 (φ (w - (w >> 1))) (φ w).
Proof.
  intros w H. rewrite ltb_spec in H. change (φ 1) with 1%Z in H.
  rewrite sub_spec, lsr1. pose proof (to_Z_bounded w).
  assert (1 <= (φ w) / 2)%Z by (apply Z.div_le_lower_bound; lia).
  assert ((φ w) / 2 <= (φ w))%Z by (apply Z.div_le_upper_bound; lia).
  rewrite Z.mod_small by lia. unfold Zwf. lia.
Qed.

Lemma dec_isq2 : forall w : int, (1 <? w) = true -> Zwf 0 (φ (w >> 1)) (φ w).
Proof. intros w H. apply dec_shr. rewrite ltb_spec in *. change (φ 0) with 0%Z. change (φ 1) with 1%Z in H. lia. Qed.

Definition LIM : int := 1000000.

Lemma dec_add : forall i j : int, ((0 <? i) && (i <? LIM)) = true -> (j <? LIM) = true ->
  Zwf 0 (gap LIM (j + i)) (gap LIM j).
Proof.
  intros i j Hi Hj. apply Bool.andb_true_iff in Hi as [H1 H2]. rewrite ltb_spec in H1, H2, Hj.
  change (φ 0) with 0%Z in H1. change (φ LIM) with 1000000%Z in *.
  pose proof (to_Z_bounded j). unfold Zwf, gap.
  assert ((φ (j + i)) = ((φ j) + (φ i))%Z) by sia. change (φ LIM) with 1000000%Z. lia.
Qed.

Lemma dec_shr2 : forall d : int, ((0 <? d) && (d land 1 =? 0)) = true -> Zwf 0 (φ (d >> 1)) (φ d).
Proof. intros d H. apply Bool.andb_true_iff in H as [H _]. apply dec_shr; auto. Qed.

Lemma dec_pred : forall b : int, (0 <? b) = true -> Zwf 0 (φ (b - 1)) (φ b).
Proof.
  intros b H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H. unfold Zwf.
  assert ((φ (b - 1)) = ((φ b) - 1)%Z) by sia. lia.
Qed.

(* --- modular arithmetic ------------------------------------------- *)

(* a * b mod n, through the double-width product *)
Definition mulmod (a b n : int) : int :=
  let (h, l) := mulc a b in snd (diveucl_21 h l n).

Fixpoint pow_loop (b e r n : int) (H : Acc (Zwf 0) (φ e)) {struct H} : int :=
  match bdec (0 <? e) with
  | left He =>
      pow_loop (mulmod b b n) (e >> 1) (if (e land 1) =? 1 then mulmod r b n else r) n
        (Acc_inv H (dec_shr e He))
  | right _ => r
  end.

Definition powmod (b e n : int) : int :=
  pow_loop (b mod n) e (1 mod n) n (Zwf_well_founded 0 _).

Fixpoint gcd_loop (a b : int) (H : Acc (Zwf 0) (φ b)) {struct H} : int :=
  match bdec (0 <? b) with
  | left Hb => gcd_loop b (a mod b) (Acc_inv H (dec_mod a b Hb))
  | right _ => a
  end.

Definition igcd (a b : int) : int := gcd_loop a b (Zwf_well_founded 0 _).

(* integer square root: s^2 <= x < (s + w)^2, w halved *)
Fixpoint isq_loop (x s w : int) (H : Acc (Zwf 0) (φ w)) {struct H} : int :=
  match bdec (1 <? w) with
  | left Hw =>
      let b := w >> 1 in
      let t := s + b in
      if t * t <=? x then isq_loop x t (w - b) (Acc_inv H (dec_isq1 w Hw))
      else isq_loop x s b (Acc_inv H (dec_isq2 w Hw))
  | right _ => s
  end.

Definition isqrt (x : int) : int := isq_loop x 0 2147483648 (Zwf_well_founded 0 _).

(* c = x^k * c', x not dividing c' *)
Fixpoint divfull (x c k : int) (Hx : (1 <? x) = true) (H : Acc (Zwf 0) (φ c)) {struct H}
  : int * int :=
  match bdec (0 <? c) with
  | left Hc =>
      if c mod x =? 0 then divfull x (c / x) (k + 1) Hx (Acc_inv H (dec_div x c Hx Hc))
      else (c, k)
  | right _ => (c, k)
  end.

(* divide every cell of a by x, fully; e collects the exponents *)
Fixpoint divpass (x : int) (Hx : (1 <? x) = true) (a : array int) (n j e : int)
    (H : Acc (Zwf 0) (gap n j)) {struct H} : array int * int :=
  match bdec (j <? n) with
  | left Hj =>
      let c := a.[j] in
      if c mod x =? 0 then
        let ck := divfull x c 0 Hx (Zwf_well_founded 0 _) in
        divpass x Hx a.[j <- fst ck] n (j + 1) (e + snd ck) (Acc_inv H (dec_step n j Hj))
      else divpass x Hx a n (j + 1) e (Acc_inv H (dec_step n j Hj))
  | right _ => (a, e)
  end.

(* --- the sieve ------------------------------------------------------ *)

Fixpoint mark_loop (m : array bool) (i j : int) (Hi : ((0 <? i) && (i <? LIM)) = true)
    (H : Acc (Zwf 0) (gap LIM j)) {struct H} : array bool :=
  match bdec (j <? LIM) with
  | left Hj => mark_loop m.[j <- true] i (j + i) Hi (Acc_inv H (dec_add i j Hi Hj))
  | right _ => m
  end.

Fixpoint sieve_loop (m : array bool) (pr : array int) (np i : int)
    (H : Acc (Zwf 0) (gap LIM i)) {struct H} : array int * int :=
  match bdec (i <? LIM) with
  | left Hi =>
      if m.[i] then sieve_loop m pr np (i + 1) (Acc_inv H (dec_step LIM i Hi))
      else match bdec ((0 <? i) && (i <? LIM)) with
           | left Hi' =>
               sieve_loop (mark_loop m i (i + i) Hi' (Zwf_well_founded 0 _)) pr.[np <- i] (np + 1)
                 (i + 1) (Acc_inv H (dec_step LIM i Hi))
           | right _ => (pr, np)
           end
  | right _ => (pr, np)
  end.

Definition sieve : array int * int :=
  sieve_loop (PArray.make LIM false) (PArray.make LIM 0) 0 2 (Zwf_well_founded 0 _).

(* --- Miller-Rabin: true = proven composite --------------------------- *)

Fixpoint strip2 (d s : int) (H : Acc (Zwf 0) (φ d)) {struct H} : int * int :=
  match bdec ((0 <? d) && (d land 1 =? 0)) with
  | left Hd => strip2 (d >> 1) (s + 1) (Acc_inv H (dec_shr2 d Hd))
  | right _ => (d, s)
  end.

Fixpoint mr_loop (n y i s : int) (H : Acc (Zwf 0) (gap s i)) {struct H} : bool :=
  match bdec (i <? s) with
  | left Hi =>
      if y =? n - 1 then false
      else let y' := mulmod y y n in
           if y' =? 1 then true else mr_loop n y' (i + 1) s (Acc_inv H (dec_step s i Hi))
  | right _ => true
  end.

Definition mr_base (n a : int) : bool :=
  let (d, s) := strip2 (n - 1) 0 (Zwf_well_founded 0 _) in
  let y := powmod a d n in
  if y =? 1 then false else mr_loop n y 0 s (Zwf_well_founded 0 _).

Definition mr_comp (n : int) : bool :=
  mr_base n 2 || mr_base n 3 || mr_base n 5 || mr_base n 7 || mr_base n 11 ||
  mr_base n 13 || mr_base n 17 || mr_base n 19 || mr_base n 23 || mr_base n 29 ||
  mr_base n 31 || mr_base n 37.

(* --- Pocklington ------------------------------------------------------ *)

Inductive bres := BFound | BComp | BFail.

Definition ALIM : int := 1000.

(* a base for the prime q of n - 1 = m, searched from a up *)
Fixpoint find_base (n m q a : int) (H : Acc (Zwf 0) (gap ALIM a)) {struct H} : bres :=
  match bdec (a <? ALIM) with
  | left Ha =>
      if negb (powmod a m n =? 1) then BComp
      else
        let u := powmod a (m / q) n in
        let g := igcd ((u + n - 1) mod n) n in
        if g =? 1 then BFound
        else if g <? n then BComp
        else find_base n m q (a + 1) (Acc_inv H (dec_step ALIM a Ha))
  | right _ => BFail
  end.

(* trial division of m = n - 1 = F * R by the sieve primes, a base for
   every prime found, stopped as soon as F * F > n *)
Fixpoint td_cert (pr : array int) (np k n m F R : int) (H : Acc (Zwf 0) (gap np k)) {struct H}
  : bres * int * int :=
  match bdec (k <? np) with
  | left Hk =>
      if n / F <? F then (BFound, F, R)
      else
        let q := pr.[k] in
        if R mod q =? 0 then
          match bdec (1 <? q) with
          | left Hq =>
              let Rk := divfull q R 0 Hq (Zwf_well_founded 0 _) in
              match find_base n m q 2 (Zwf_well_founded 0 _) with
              | BFound => td_cert pr np (k + 1) n m (F * (R / fst Rk)) (fst Rk)
                            (Acc_inv H (dec_step np k Hk))
              | r => (r, F, R)
              end
          | right _ => (BFail, F, R)
          end
        else td_cert pr np (k + 1) n m F R (Acc_inv H (dec_step np k Hk))
  | right _ => (BFound, F, R)
  end.

(* Pollard rho, Brent's cycle detection, one gcd per block of 128 *)
Fixpoint rho_loop (n c x y q j r b budget : int) (H : Acc (Zwf 0) (φ budget)) {struct H} : int :=
  match bdec (0 <? budget) with
  | left Hb =>
      let y' := (mulmod y y n + c) mod n in
      let diff := if x <? y' then y' - x else x - y' in
      let q' := mulmod q diff n in
      let b' := b + 1 in
      let g := if b' =? 128 then igcd q' n else 1 in
      if negb (g =? 1) then g
      else
        let b'' := if b' =? 128 then 0 else b' in
        let j' := j + 1 in
        if j' =? r then rho_loop n c y' y' q' 0 (r + r) b'' (budget - 1) (Acc_inv H (dec_pred budget Hb))
        else rho_loop n c x y' q' j' r b'' (budget - 1) (Acc_inv H (dec_pred budget Hb))
  | right _ => 1
  end.

Definition RHOC : int := 40.

Fixpoint rho_try (n c : int) (H : Acc (Zwf 0) (gap RHOC c)) {struct H} : int :=
  match bdec (c <? RHOC) with
  | left Hc =>
      let g := rho_loop n c 2 2 1 0 1 0 1048576 (Zwf_well_founded 0 _) in
      if (1 <? g) && (g <? n) && (n mod g =? 0) then g
      else rho_try n (c + 1) (Acc_inv H (dec_step RHOC c Hc))
  | right _ => 0
  end.

Inductive cres := CPrime | CComp | CFail.

Definition T12 : int := 1000000000000.

Definition base_res (b : bres) : cres :=
  match b with BFound => CPrime | BComp => CComp | BFail => CFail end.

(* proven verdict on n (10^12 < n), Pocklington with a recursive certificate *)
Fixpoint certify (pr : array int) (np n : int) (H : Acc (Zwf 0) (φ n)) {struct H} : cres :=
  let m := n - 1 in
  match td_cert pr np 0 n m 1 m (Zwf_well_founded 0 _) with
  | (BComp, _, _) => CComp
  | (BFail, _, _) => CFail
  | (BFound, F, R) =>
      if n / F <? F then CPrime
      else if R <=? 1 then CFail
      else if R <=? T12 then base_res (find_base n m R 2 (Zwf_well_founded 0 _))
      else if mr_comp R then
        let g := rho_try R 1 (Zwf_well_founded 0 _) in
        if (1 <? g) && (g <? R) && (R mod g =? 0) then
          match find_base n m g 2 (Zwf_well_founded 0 _) with
          | BFound =>
              let F' := F * g in
              if n / F' <? F' then CPrime
              else base_res (find_base n m (R / g) 2 (Zwf_well_founded 0 _))
          | BComp => CComp
          | BFail => CFail
          end
        else CFail
      else
        match bdec (R <? n) with
        | left HR =>
            match certify pr np R (Acc_inv H (dec_lt n R HR)) with
            | CPrime => base_res (find_base n m R 2 (Zwf_well_founded 0 _))
            | _ => CFail
            end
        | right _ => CFail
        end
  end.

(* the safety net: trial division up to the square root *)
Fixpoint td_loop (n d : int) (H : Acc (Zwf 0) (gap n d)) {struct H} : bool :=
  match bdec (d <? n) with
  | left Hd =>
      if d * d <=? n then
        if n mod d =? 0 then false else td_loop n (d + 1) (Acc_inv H (dec_step n d Hd))
      else true
  | right _ => true
  end.

(* --- one slot ------------------------------------------------------- *)

Inductive kind := KPrime | KSquare | KSemi.

Definition classify (pr : array int) (np x : int) : kind :=
  if x <=? T12 then KPrime
  else
    let s := isqrt x in
    if s * s =? x then KSquare
    else if mr_comp x then KSemi
    else match certify pr np x (Zwf_well_founded 0 _) with
         | CPrime => KPrime
         | CComp => KSemi
         | CFail => if td_loop x 2 (Zwf_well_founded 0 _) then KPrime else KSemi
         end.

Definition MODP : int := 1000000007.

(* ((e+1)^P - 2 e^P + (e-1)^P) mod 10^9+7 *)
Definition fmod (e P : int) : int :=
  let a := powmod (e + 1) P MODP in
  let b := powmod e P MODP in
  let c := powmod (e - 1) P MODP in
  (a + 2 * (MODP - b) + c) mod MODP.

Definition contrib (pr : array int) (np x e P : int) : int :=
  match classify pr np x with
  | KPrime => fmod e P
  | KSquare => fmod (e + e) P
  | KSemi => let f := fmod e P in mulmod f f MODP
  end.

(* the accumulator after a slot of exponents eg, el *)
Definition step_acc (acc eg el : int) (f : int -> int) : int :=
  if eg =? el then acc else if el <? eg then 0 else mulmod acc (f (el - eg)) MODP.

(* --- phase 1: the sieve primes -------------------------------------- *)

Fixpoint ph1 (pr : array int) (np k : int) (aG aL : array int) (nG nL P acc : int)
    (H : Acc (Zwf 0) (gap np k)) {struct H} : array int * array int * int :=
  match bdec (k <? np) with
  | left Hk =>
      let p := pr.[k] in
      match bdec (1 <? p) with
      | left Hp =>
          let rG := divpass p Hp aG nG 0 0 (Zwf_well_founded 0 _) in
          let rL := divpass p Hp aL nL 0 0 (Zwf_well_founded 0 _) in
          ph1 pr np (k + 1) (fst rG) (fst rL) nG nL P
            (step_acc acc (snd rG) (snd rL) (fun e => fmod e P))
            (Acc_inv H (dec_step np k Hk))
      | right _ => (aG, aL, acc)
      end
  | right _ => (aG, aL, acc)
  end.

(* --- phase 2: the cofactors, one gcd-refined slot at a time ----------- *)

Fixpoint refine (a : array int) (n j x : int) (H : Acc (Zwf 0) (gap n j)) {struct H} : int :=
  match bdec (j <? n) with
  | left Hj =>
      let d := igcd x a.[j] in
      refine a n (j + 1) (if (1 <? d) && (d <? x) then d else x) (Acc_inv H (dec_step n j Hj))
  | right _ => x
  end.

Definition sel_get (sel : bool) (aG aL : array int) (i : int) : int :=
  if sel then aL.[i] else aG.[i].

Fixpoint peel (pr : array int) (np : int) (aG aL : array int) (nG nL : int) (sel : bool)
    (i P acc : int) (H : Acc (Zwf 0) (φ (sel_get sel aG aL i))) {struct H}
  : array int * array int * int :=
  let c := sel_get sel aG aL i in
  match bdec (1 <? c) with
  | left Hc =>
      let x := refine aL nL 0 (refine aG nG 0 c (Zwf_well_founded 0 _)) (Zwf_well_founded 0 _) in
      match bdec (1 <? x) with
      | left Hx =>
          let rG := divpass x Hx aG nG 0 0 (Zwf_well_founded 0 _) in
          let rL := divpass x Hx aL nL 0 0 (Zwf_well_founded 0 _) in
          let acc' := step_acc acc (snd rG) (snd rL) (fun e => contrib pr np x e P) in
          match bdec (sel_get sel (fst rG) (fst rL) i <? c) with
          | left Hd => peel pr np (fst rG) (fst rL) nG nL sel i P acc'
                         (Acc_inv H (dec_lt c _ Hd))
          | right _ => (fst rG, fst rL, acc')
          end
      | right _ => (aG, aL, acc)
      end
  | right _ => (aG, aL, acc)
  end.

Fixpoint ph2 (pr : array int) (np : int) (aG aL : array int) (nG nL : int) (sel : bool)
    (n i P acc : int) (H : Acc (Zwf 0) (gap n i)) {struct H} : array int * array int * int :=
  match bdec (i <? n) with
  | left Hi =>
      let r := peel pr np aG aL nG nL sel i P acc (Zwf_well_founded 0 _) in
      ph2 pr np (fst (fst r)) (snd (fst r)) nG nL sel n (i + 1) P (snd r)
        (Acc_inv H (dec_step n i Hi))
  | right _ => (aG, aL, acc)
  end.

Definition atp_impl (p : uint) (x y : array uint) : uint :=
  let s := sieve in
  let pr := fst s in
  let np := snd s in
  let nG := PArray.length x in
  let nL := PArray.length y in
  let r1 := ph1 pr np 0 (PArray.copy x) (PArray.copy y) nG nL p 1 (Zwf_well_founded 0 _) in
  let r2 := ph2 pr np (fst (fst r1)) (snd (fst r1)) nG nL false nG 0 p (snd r1)
              (Zwf_well_founded 0 _) in
  let r3 := ph2 pr np (fst (fst r2)) (snd (fst r2)) nG nL true nL 0 p (snd r2)
              (Zwf_well_founded 0 _) in
  snd r3.

End Code.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition atrivialpursuit : uint -> array uint -> array uint -> uint := atp_impl.
