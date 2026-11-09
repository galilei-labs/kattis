(* Executable implementation and its required termination dependencies.
   Correctness proofs are in bitwise_proofs.v. *)
From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Permutation.
Import ListNotations.

Open Scope Z_scope.
Unset Lia Cache.

(* ================================================================== *)
(* Part 2. The program                                                 *)
(* ================================================================== *)

Open Scope uint63_scope.
Open Scope array_scope.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

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

Lemma dec_down : forall i : int, (0 <? i) = true -> Zwf 0 (φ (i - 1)) (φ i).
Proof.
  intros i H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  assert (H1 : (φ (i - 1)) = ((φ i) - 1)%Z) by sia.
  unfold Zwf. lia.
Qed.

(* the value at position x of the circle unrolled into 2n cells *)
Definition cell (a : array int) (n x : int) : int :=
  if x <? n then a.[x] else a.[x - n].

Definition hasbit (v b : int) : bool := ((v >> b) land 1) =? 1.

(* Q[x] := max(P[x], first position >= x holding bit b, plus one),
   for x = i-1 down to 0 ; nb is that position for x = i *)
Fixpoint scan (a P : array int) (n b i nb : int) (Q : array int)
    (H : Acc (Zwf 0) (φ i)) {struct H} : array int :=
  match bdec (0 <? i) with
  | left Hi =>
      let x := i - 1 in
      let nb' := if hasbit (cell a n x) b then i else nb in
      let p := P.[x] in
      scan a P n b x nb' (Q.[x <- if p <? nb' then nb' else p])
        (Acc_inv H (dec_down i Hi))
  | right _ => Q
  end.

(* the pointers of mask (old mask | 2^b), from those of the old mask *)
Definition newptr (a P Q : array int) (n b : int) : array int :=
  let n2 := 2 * n in
  scan a P n b n2 (n2 + 1) (Q.[n2 <- n2 + 1].[n2 + 1 <- n2 + 1])
    (Zwf_well_founded 0 (φ n2)).

(* one level of the simultaneous walk : the entries (V[i], S[i]), i < w,
   are mapped to (Q[V[i]], S[i]) into (V', S'), an entry equal in value to
   the previous one being merged into it *)
Fixpoint dedup (Q V S : array int) (w i w' : int) (V' S' : array int)
    (H : Acc (Zwf 0) (gap w i)) {struct H} : int * array int * array int :=
  match bdec (i <? w) with
  | left Hi =>
      let v := Q.[V.[i]] in
      let s := S.[i] in
      if andb (0 <? w') (V'.[w' - 1] =? v) then
        dedup Q V S w (i + 1) w' V' (S'.[w' - 1 <- s])
          (Acc_inv H (dec_step w i Hi))
      else
        dedup Q V S w (i + 1) (w' + 1) (V'.[w' <- v]) (S'.[w' <- s])
          (Acc_inv H (dec_step w i Hi))
  | right _ => (w', V', S')
  end.

(* t more levels, ping-ponging between the two pairs of buffers *)
Fixpoint levels (Q : array int) (t w : int) (V S V' S' : array int)
    (H : Acc (Zwf 0) (φ t)) {struct H}
    : int * array int * array int * array int * array int :=
  match bdec (0 <? t) with
  | left Ht =>
      let '(w2, V2, S2) := dedup Q V S w 0 0 V' S' (Zwf_well_founded 0 (gap w 0)) in
      levels Q (t - 1) w2 V2 S2 V S (Acc_inv H (dec_down t Ht))
  | right _ => (w, V, S, V', S')
  end.

Fixpoint check (V S : array int) (n w j : int) (H : Acc (Zwf 0) (gap w j))
    {struct H} : bool :=
  match bdec (j <? w) with
  | left Hj =>
      if V.[j] <=? S.[j] + n then true
      else check V S n w (j + 1) (Acc_inv H (dec_step w j Hj))
  | right _ => false
  end.

Fixpoint init (L j : int) (V S : array int) (H : Acc (Zwf 0) (gap L j))
    {struct H} : array int * array int :=
  match bdec (j <? L) with
  | left Hj => init L (j + 1) (V.[j <- j]) (S.[j <- j]) (Acc_inv H (dec_step L j Hj))
  | right _ => (V, S)
  end.

(* the feasibility test of the mask whose pointers are Q : the starts
   0 .. min(Q[0], n-1) walked k steps together *)
Definition test (Q : array int) (n k : int) (V S V' S' : array int)
    : bool * array int * array int * array int * array int :=
  let f0 := Q.[0] in
  let L1 := (if f0 <? n - 1 then f0 else n - 1) + 1 in
  let '(V1, S1) := init L1 0 V S (Zwf_well_founded 0 (gap L1 0)) in
  let '(w, V2, S2, V3, S3) := levels Q k L1 V1 S1 V' S' (Zwf_well_founded 0 (φ k)) in
  (check V2 S2 n w 0 (Zwf_well_founded 0 (gap w 0)), V2, S2, V3, S3).

(* the greedy, bits b-1 down to 0 *)
Fixpoint bits (a : array int) (n k b ans : int) (P Q V S V' S' : array int)
    (H : Acc (Zwf 0) (φ b)) {struct H} : int :=
  match bdec (0 <? b) with
  | left Hb =>
      let j := b - 1 in
      let Q1 := newptr a P Q n j in
      let '(ok, V1, S1, V2, S2) := test Q1 n k V S V' S' in
      if ok then bits a n k j (ans lor (1 << j)) Q1 P V1 S1 V2 S2 (Acc_inv H (dec_down b Hb))
      else bits a n k j ans P Q1 V1 S1 V2 S2 (Acc_inv H (dec_down b Hb))
  | right _ => ans
  end.

Fixpoint init_ptr (m x : int) (P : array int) (H : Acc (Zwf 0) (gap m x))
    {struct H} : array int :=
  match bdec (x <? m) with
  | left Hx => init_ptr m (x + 1) (P.[x <- x + 1]) (Acc_inv H (dec_step m x Hx))
  | right _ => P
  end.

Definition best_and_impl (k : uint) (a : array uint) : uint :=
  let n := PArray.length a in
  let n2 := 2 * n in
  let P0 := init_ptr (n2 + 1) 0 (PArray.make (n2 + 2) 0)
              (Zwf_well_founded 0 (gap (n2 + 1) 0)) in
  let P := P0.[n2 + 1 <- n2 + 1] in
  bits a n k 30 0 P (PArray.make (n2 + 2) 0)
    (PArray.make n 0) (PArray.make n 0) (PArray.make n 0) (PArray.make n 0)
    (Zwf_well_founded 0 (φ 30)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition best_and : uint -> array uint -> uint := best_and_impl.
