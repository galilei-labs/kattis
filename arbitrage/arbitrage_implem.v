(* Executable implementation and its required termination dependencies.
   Correctness proofs are in arbitrage_proofs.v. *)
From Speck Require Import Prelude.
From Stdlib Require Import ZArith NArith QArith Qreals List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf.
From Stdlib Require Sint63.
From StdGalilei Require Import repr.
From StdGalilei Require Import repr_float.
From Flocq Require Core.Core.
Import ListNotations.

Open Scope uint63_scope.
Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* The termination device and the loop combinator                     *)
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
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* -- The 25 primes below 100, and the multiplicity of p in n <= 100. *)
Definition primes : array int :=
  (PArray.make 25 0).[0 <- 2].[1 <- 3].[2 <- 5].[3 <- 7].[4 <- 11].[5 <- 13]
    .[6 <- 17].[7 <- 19].[8 <- 23].[9 <- 29].[10 <- 31].[11 <- 37].[12 <- 41]
    .[13 <- 43].[14 <- 47].[15 <- 53].[16 <- 59].[17 <- 61].[18 <- 67]
    .[19 <- 71].[20 <- 73].[21 <- 79].[22 <- 83].[23 <- 89].[24 <- 97].

Definition dvd1 (n x : int) : int := if n mod x =? 0 then 1 else 0.

(* sum over e = 1..6 of [p^e divides n]: the multiplicity, for n <= 100 *)
Definition mlt (n p : int) : int :=
  let p2 := p * p in let p3 := p2 * p in let p4 := p3 * p in
  let p5 := p4 * p in let p6 := p5 * p in
  dvd1 n p + dvd1 n p2 + dvd1 n p3 + dvd1 n p4 + dvd1 n p5 + dvd1 n p6.

(* -- Exact arithmetic (Z), only in the comparison of two prime products. *)
Lemma dec_half : forall i : int, (i =? 0) = false -> Zwf 0 (to_Z (i / 2)) (to_Z i).
Proof.
  intros i H. assert (to_Z i <> 0%Z).
  { intros E. assert (i = 0) by (apply to_Z_inj; exact E). subst i. discriminate. }
  pose proof (to_Z_bounded i). unfold Zwf. sia.
Qed.

Fixpoint zofi_rec (i : int) (H : Acc (Zwf 0) (to_Z i)) {struct H} : Z :=
  match bdec (i =? 0) with
  | left _ => 0%Z
  | right Hn =>
      let r := zofi_rec (i / 2) (Acc_inv H (dec_half i Hn)) in
      let bit := if i mod 2 =? 0 then 0%Z else 1%Z in
      (2 * r + bit)%Z
  end.

Definition zofi (i : int) : Z := zofi_rec i (Zwf_well_founded 0 (to_Z i)).

(* D_t = dv t: accumulate P = prod_{D_t > 0} p_t^D_t and
   Q = prod_{D_t < 0} p_t^(-D_t); nz records a non-zero D_t *)
Definition ex_step (dv : int -> int) (t : int) (s : bool * Z * Z) : bool * Z * Z :=
  let '(nz, P, Q) := s in
  let d := dv t in
  if Sint63.ltb 0 d then (true, (P * Z.pow (zofi primes.[t]) (zofi d))%Z, Q)
  else if Sint63.ltb d 0 then (true, P, (Q * Z.pow (zofi primes.[t]) (zofi (0 - d)))%Z)
  else s.

(* the product of p_t^(dv t) exceeds 1; zero D is equality *)
Definition exact_gt (dv : int -> int) : bool :=
  let '(nz, P, Q) := loop 25 (fun _ _ => true) (ex_step dv) 0 (false, 1%Z, 1%Z) in
  if nz then Z.ltb Q P else false.

(* -- Float pairs: mantissa in [1, 2], biased binary exponent, rounding count. *)
Definition f_one : float := of_uint63 1.
Definition f_two : float := of_uint63 2.
Definition f_c0 : float := of_uint63 1048576.
Definition f_c1 : float := of_uint63 1048577.
Definition cap : int := 1048576.
Definition BIAS : int := 1073741824.

(* the product of two cells, renormalised *)
Definition mulcell (m1 : float) (e1 n1 : int) (m2 : float) (e2 n2 : int)
    : float * int * int :=
  let p := (m1 * m2)%float in
  let n := n1 + n2 + 2 in
  let n' := if cap <? n then cap + 1 else n in
  if (f_two <=? p)%float then ((p / f_two)%float, e1 + e2 - BIAS + 1, n')
  else (p, e1 + e2 - BIAS, n').

(* the rate b / a as a cell: exponent from the leading bits *)
Definition ratecell (a b : int) : float * int * int :=
  let ha := head0 a in
  let hb := head0 b in
  let num := if ha <? hb then b << (hb - ha) else b in
  let den := if ha <? hb then a else a << (ha - hb) in
  let r := (of_uint63 num / of_uint63 den)%float in
  let e := BIAS + ha - hb in
  if (r <? f_one)%float then ((r * f_two)%float, e - 1, 2) else (r, e, 2).

(* the certified float comparison: Some true when cell 1 is surely the
   larger, Some false when surely the smaller, None when too close or a
   rounding count is beyond the cap *)
Definition fcmp (m1 : float) (e1 n1 : int) (m2 : float) (e2 n2 : int) : option bool :=
  if (cap <? n1) || (cap <? n2) then None
  else if e2 + 2 <=? e1 then Some true
  else if e1 + 2 <=? e2 then Some false
  else
    let x := if e2 <? e1 then (m1 * f_two)%float else m1 in
    let y := if e1 <? e2 then (m2 * f_two)%float else m2 in
    if (y * f_c1 <? x * f_c0)%float then Some true
    else if (x * f_c1 <? y * f_c0)%float then Some false
    else None.

(* -- The tables: one flat c*c table per field, 25 cells per vector. *)
Record tabs := mkT {
  tPR : array bool;    (* the cell holds a product *)
  tMA : array float;   (* mantissa *)
  tEX : array int;     (* biased exponent *)
  tCN : array int;     (* rounding count *)
  tVT : array int      (* exponent vector, at 25 * cell + t *)
}.

Definition wr_head (T : tabs) (q : int) (m : float) (e n : int) (V : array int) : tabs :=
  mkT (tPR T).[q <- true] (tMA T).[q <- m] (tEX T).[q <- e] (tCN T).[q <- n] V.

Definition vadd (bd b1 b2 : int) (V : array int) : array int :=
  loop 25 (fun _ _ => true) (fun t W => W.[bd + t <- W.[b1 + t] + W.[b2 + t]]) 0 V.

Definition vset (bd a b : int) (V : array int) : array int :=
  loop 25 (fun _ _ => true)
    (fun t W => W.[bd + t <- mlt b primes.[t] - mlt a primes.[t]]) 0 V.

(* -- The initial table: the best rate per ordered pair. *)
Definition init_step (c : int) (xs xd xa xb : array int) (r : int) (T : tabs) : tabs :=
  let u := xs.[r] in let v := xd.[r] in let a := xa.[r] in let b := xb.[r] in
  let q := u * c + v in
  let '(m, e, n) := ratecell a b in
  let better :=
    if (tPR T).[q] then
      match fcmp m e n (tMA T).[q] (tEX T).[q] (tCN T).[q] with
      | Some g => g
      | None => exact_gt (fun t => mlt b primes.[t] - mlt a primes.[t] - (tVT T).[25 * q + t])
      end
    else true in
  if better then wr_head T q m e n (vset (25 * q) a b (tVT T)) else T.

(* -- Floyd-Warshall in (max, x), in place, early exit on the diagonal. *)
Definition fw_j (c k i : int) (j : int) (s : tabs * bool) : tabs * bool :=
  let T := fst s in
  if j =? k then s else
  let qkj := k * c + j in
  if (tPR T).[qkj] then
    let qik := i * c + k in
    let qij := i * c + j in
    let '(m, e, n) := mulcell (tMA T).[qik] (tEX T).[qik] (tCN T).[qik]
                              (tMA T).[qkj] (tEX T).[qkj] (tCN T).[qkj] in
    let bik := 25 * qik in let bkj := 25 * qkj in let bij := 25 * qij in
    let ex :=
      if i =? j then
        match fcmp m e n f_one BIAS 0 with
        | Some g => g
        | None => exact_gt (fun t => (tVT T).[bik + t] + (tVT T).[bkj + t])
        end
      else false in
    if ex then (T, true) else
    let better :=
      if (tPR T).[qij] then
        match fcmp m e n (tMA T).[qij] (tEX T).[qij] (tCN T).[qij] with
        | Some g => g
        | None => exact_gt (fun t => (tVT T).[bik + t] + (tVT T).[bkj + t] - (tVT T).[bij + t])
        end
      else true in
    if better then (wr_head T qij m e n (vadd bij bik bkj (tVT T)), false) else s
  else s.

Definition fw_i (c k : int) (i : int) (s : tabs * bool) : tabs * bool :=
  if i =? k then s else
  if (tPR (fst s)).[i * c + k] then loop c (fun _ s => negb (snd s)) (fw_j c k i) 0 s
  else s.

Definition fw_k (c : int) (k : int) (s : tabs * bool) : tabs * bool :=
  loop c (fun _ s => negb (snd s)) (fw_i c k) 0 s.

Definition arbitrage_impl (c : uint) (xs xd xa xb : array uint) : bool :=
  let cc := c * c in
  let T0 := mkT (PArray.make cc false) (PArray.make cc f_one) (PArray.make cc 0)
                (PArray.make cc 0) (PArray.make (25 * cc) 0) in
  let T1 := loop (PArray.length xs) (fun _ _ => true) (init_step c xs xd xa xb) 0 T0 in
  snd (loop c (fun _ s => negb (snd s)) (fw_k c) 0 (T1, false)).

(* ================================================================== *)
(* Part B: walks and the Floyd-Warshall invariant, on the math side    *)
(* ================================================================== *)

Notation lget := Prelude.get.

(* -- the oracle's exact path ------------------------------------------ *)

Notation sZ := Sint63.to_Z.

(* ================================================================== *)
(* Part D: the float pairs and the certified comparison                *)
(* ================================================================== *)

Local Notation bp := (Raux.bpow Zaux.radix2).

Definition arbitrage : uint -> array uint -> array uint -> array uint -> array uint -> bool :=
  arbitrage_impl.
