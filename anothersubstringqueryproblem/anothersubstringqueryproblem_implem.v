(* Executable implementation and its required termination dependencies.
   Correctness proofs are in anothersubstringqueryproblem_proofs.v. *)
(* Implementation of anothersubstringqueryproblem
   (anothersubstringqueryproblem.spec).

   Code.  [kth_occurrences x ts ks]:
   1. suffix array of x by prefix doubling ([rounds]): round h sorts the
      identity permutation with a top-down merge sort ([msort]) by the key
      (rank of p, rank of p+h + 1 or 0), then recomputes the ranks from the
      sorted order ([rank_loop]); it stops when 2h >= n or when the ranks
      are pairwise distinct;
   2. a persistent segment tree over the values [0, 2^D) (2^D >= n, D least),
      in three flat arrays (left child, right child, count), node 0 the
      empty tree: version i+1 inserts sa.[i] into version i ([build], [ins]);
   3. per query (t, k): two binary searches ([bs]) over the suffix array for
      the interval [lo, hi) of suffixes that start with t (comparison of t
      with the first |t| characters of a suffix, [cmpt]), then the k-th
      smallest value of versions hi minus lo ([qry]), +1; -1 when
      hi - lo < k.
   Every loop terminates on an erased [Acc (Zwf 0) _] proof; no nat, no Z
   in the code.  See README.md, "Implementation". *)

From Anothersubstringqueryproblem.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import String Ascii.
From Stdlib Require PrimString Sint63.
Import ListNotations.

Open Scope Z_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ================================================================== *)
(* Uint63 / PArray plumbing                                            *)
(* ================================================================== *)

Open Scope uint63_scope.
Open Scope array_scope.

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

Lemma dec_d : forall d : int, (0 <? d) = true -> Zwf 0 (φ (d - 1)) (φ d).
Proof. intros d H. rewrite ltb_spec in H. unfold Zwf. sia. Qed.

Definition midp (lo hi : int) : int := lo + (hi - lo) / 2.

Lemma midp_spec : forall lo hi : int, ((φ lo) < (φ hi))%Z ->
  (φ (midp lo hi)) = ((φ lo) + ((φ hi) - (φ lo)) / 2)%Z.
Proof. intros lo hi H. unfold midp. sia. Qed.

Lemma dec_bl : forall lo hi : int, (lo <? hi) = true ->
  Zwf 0 (gap (midp lo hi) lo) (gap hi lo).
Proof.
  intros lo hi H. rewrite ltb_spec in H. pose proof (midp_spec lo hi H).
  unfold Zwf, gap. split; [lia|]. rewrite H0.
  assert (0 <= ((φ hi) - (φ lo)) / 2 < (φ hi) - (φ lo))%Z by (split; [apply Z.div_pos | apply Z.div_lt]; lia).
  lia.
Qed.

Lemma dec_br : forall lo hi : int, (lo <? hi) = true ->
  Zwf 0 (gap hi (midp lo hi + 1)) (gap hi lo).
Proof.
  intros lo hi H. rewrite ltb_spec in H. pose proof (midp_spec lo hi H).
  assert (0 <= ((φ hi) - (φ lo)) / 2 < (φ hi) - (φ lo))%Z by (split; [apply Z.div_pos | apply Z.div_lt]; lia).
  assert ((φ (midp lo hi + 1)) = (φ (midp lo hi)) + 1)%Z by (rewrite add_spec; pose proof (to_Z_bounded hi); rewrite Z.mod_small; change (φ 1) with 1%Z; lia).
  unfold Zwf, gap. lia.
Qed.

Lemma dec_ml : forall lo hi : int, ((lo <? hi) && (1 <? hi - lo))%bool = true ->
  Zwf 0 (gap (midp lo hi) lo) (gap hi lo).
Proof. intros lo hi H. apply andb_prop in H. apply dec_bl. apply H. Qed.

Lemma dec_mr : forall lo hi : int, ((lo <? hi) && (1 <? hi - lo))%bool = true ->
  Zwf 0 (gap hi (midp lo hi)) (gap hi lo).
Proof.
  intros lo hi H. apply andb_prop in H. destruct H as [H1 H2].
  rewrite ltb_spec in H1. rewrite ltb_spec in H2.
  assert (E : (φ (hi - lo)) = ((φ hi) - (φ lo))%Z) by sia. rewrite E in H2. change (φ 1) with 1%Z in H2.
  pose proof (midp_spec lo hi H1).
  assert (0 < ((φ hi) - (φ lo)) / 2)%Z by (apply Z.div_str_pos; lia).
  unfold Zwf, gap. lia.
Qed.

(* ================================================================== *)
(* Comparing a pattern with the first |t| characters of a suffix       *)
(* ================================================================== *)

Fixpoint cmpt (x t : PrimString.string) (n m p k : int)
    (H : Acc (Zwf 0) (gap m k)) {struct H} : comparison :=
  match bdec (k <? m) with
  | left Hk =>
      if p + k <? n then
        let a := PrimString.get t k in
        let b := PrimString.get x (p + k) in
        if a <? b then Lt
        else if b <? a then Gt
        else cmpt x t n m p (k + 1) (Acc_inv H (dec_step m k Hk))
      else Gt
  | right _ => Eq
  end.

(* ================================================================== *)
(* Merge sort on a segment of an int array, by a boolean preorder      *)
(* ================================================================== *)

Fixpoint copy (a b : array int) (hi k : int)
    (H : Acc (Zwf 0) (gap hi k)) {struct H} : array int :=
  match bdec (k <? hi) with
  | left Hk => copy a b.[k <- a.[k]] hi (k + 1) (Acc_inv H (dec_step hi k Hk))
  | right _ => b
  end.

Fixpoint merge (le : int -> int -> bool) (src dst : array int) (mid hi i j k : int)
    (H : Acc (Zwf 0) (gap hi k)) {struct H} : array int :=
  match bdec (k <? hi) with
  | left Hk =>
      if ((i <? mid) && ((hi <=? j) || le src.[i] src.[j]))%bool then
        merge le src dst.[k <- src.[i]] mid hi (i + 1) j (k + 1)
          (Acc_inv H (dec_step hi k Hk))
      else
        merge le src dst.[k <- src.[j]] mid hi i (j + 1) (k + 1)
          (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.

(* Sorts a.[lo .. hi) in place, b is scratch space. *)
Fixpoint msort (le : int -> int -> bool) (a b : array int) (lo hi : int)
    (H : Acc (Zwf 0) (gap hi lo)) {struct H} : array int * array int :=
  match bdec ((lo <? hi) && (1 <? hi - lo))%bool with
  | left C =>
      let mid := midp lo hi in
      let (a1, b1) := msort le a b lo mid (Acc_inv H (dec_ml lo hi C)) in
      let (a2, b2) := msort le a1 b1 mid hi (Acc_inv H (dec_mr lo hi C)) in
      let b3 := copy a2 b2 hi lo (Zwf_well_founded 0 (gap hi lo)) in
      (merge le b3 a2 mid hi lo mid lo (Zwf_well_founded 0 (gap hi lo)), b3)
  | right _ => (a, b)
  end.

(* --- the identity permutation --- *)

Fixpoint iota_loop (a : array int) (n i : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi => iota_loop a.[i <- i] n (i + 1) (Acc_inv H (dec_step n i Hi))
  | right _ => a
  end.

(* ================================================================== *)
(* Ranks from a sorted permutation                                     *)
(* ================================================================== *)

Fixpoint rank_loop (le : int -> int -> bool) (sa nr : array int) (n i : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi =>
      let p := sa.[i] in
      let q := sa.[i - 1] in
      rank_loop le sa nr.[p <- nr.[q] + (if le p q then 0 else 1)] n (i + 1)
        (Acc_inv H (dec_step n i Hi))
  | right _ => nr
  end.

(* ================================================================== *)
(* Suffix array by prefix doubling                                     *)
(* ================================================================== *)

(* The second key of p at round h: rank of p + h, plus one, or 0 past the end. *)
Definition r2 (rk : array int) (h n p : int) : int :=
  if p + h <? n then rk.[p + h] + 1 else 0.

(* Lexicographic order on (rank of p, second key of p). *)
Definition keyle (rk : array int) (h n : int) (p q : int) : bool :=
  ((rk.[p] <? rk.[q]) || ((rk.[p] =? rk.[q]) && (r2 rk h n p <=? r2 rk h n q)))%bool.

Definition sort_round (rk : array int) (h n : int) : array int :=
  fst (msort (keyle rk h n)
         (iota_loop (PArray.make n 0) n 0 (Zwf_well_founded 0 (gap n 0)))
         (PArray.make n 0) 0 n (Zwf_well_founded 0 (gap n 0))).

Lemma dec_dbl : forall n h b,
  (((0 <? h) && (h <? n)) && ((h <? n - h) && b))%bool = true ->
  Zwf 0 (gap n (h + h)) (gap n h).
Proof.
  intros n h b C. apply andb_prop in C. destruct C as [C1 C2].
  apply andb_prop in C1. apply andb_prop in C2. destruct C1 as [C1 C1']. destruct C2 as [C2 _].
  rewrite ltb_spec in C1, C1', C2. change (φ 0) with 0%Z in C1.
  assert (E : (φ (n - h)) = ((φ n) - (φ h))%Z) by sia. rewrite E in C2.
  unfold Zwf, gap. sia.
Qed.

Fixpoint rounds (n : int) (rk : array int) (h : int)
    (H : Acc (Zwf 0) (gap n h)) {struct H} : array int :=
  let sa := sort_round rk h n in
  let nr := rank_loop (keyle rk h n) sa (PArray.make n 0) n 1
              (Zwf_well_founded 0 (gap n 1)) in
  match bdec (((0 <? h) && (h <? n)) &&
              ((h <? n - h) && negb (nr.[sa.[n - 1]] =? n - 1)))%bool with
  | left C => rounds n nr (h + h) (Acc_inv H (dec_dbl n h _ C))
  | right _ => sa
  end.

(* rank of round 1: the character code *)
Fixpoint init_rk (x : PrimString.string) (rk : array int) (n i : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi => init_rk x rk.[i <- PrimString.get x i] n (i + 1) (Acc_inv H (dec_step n i Hi))
  | right _ => rk
  end.

Definition build_sa (x : PrimString.string) (n : int) : array int :=
  rounds n (init_rk x (PArray.make n 0) n 0 (Zwf_well_founded 0 (gap n 0))) 1
    (Zwf_well_founded 0 (gap n 1)).

(* ================================================================== *)
(* Binary search for the first index of a monotone predicate           *)
(* ================================================================== *)

Fixpoint bs (P : int -> bool) (lo hi : int)
    (H : Acc (Zwf 0) (gap hi lo)) {struct H} : int :=
  match bdec (lo <? hi) with
  | left Hl =>
      if P (midp lo hi) then bs P lo (midp lo hi) (Acc_inv H (dec_bl lo hi Hl))
      else bs P (midp lo hi + 1) hi (Acc_inv H (dec_br lo hi Hl))
  | right _ => lo
  end.

(* ================================================================== *)
(* Persistent segment tree over the values [0, 2^D), in three flat     *)
(* arrays: left child, right child, count.  Node 0 is the empty tree.  *)
(* ================================================================== *)

Fixpoint ins (L R C : array int) (nx x d v : int)
    (H : Acc (Zwf 0) (φ d)) {struct H} : array int * array int * array int :=
  match bdec (0 <? d) with
  | left Hd =>
      let half := 1 << (d - 1) in
      let y := nx + d in
      if v <? half then
        let '(Lq, Rq, Cq) := ins L R C nx L.[x] (d - 1) v (Acc_inv H (dec_d d Hd)) in
        (Lq.[y <- nx + (d - 1)], Rq.[y <- Rq.[x]], Cq.[y <- Cq.[x] + 1])
      else
        let '(Lq, Rq, Cq) := ins L R C nx R.[x] (d - 1) (v - half) (Acc_inv H (dec_d d Hd)) in
        (Lq.[y <- Lq.[x]], Rq.[y <- nx + (d - 1)], Cq.[y <- Cq.[x] + 1])
  | right _ => (L, R, C.[nx <- C.[x] + 1])
  end.

(* the k-th smallest value (k >= 1) stored in b and not in a *)
Fixpoint qry (L R C : array int) (a b d k : int)
    (H : Acc (Zwf 0) (φ d)) {struct H} : int :=
  match bdec (0 <? d) with
  | left Hd =>
      let cl := C.[L.[b]] - C.[L.[a]] in
      if k <=? cl then qry L R C L.[a] L.[b] (d - 1) k (Acc_inv H (dec_d d Hd))
      else (1 << (d - 1)) + qry L R C R.[a] R.[b] (d - 1) (k - cl) (Acc_inv H (dec_d d Hd))
  | right _ => 0
  end.

(* ================================================================== *)
(* Building the versions: roots.[i] holds the values sa.[0 .. i)       *)
(* ================================================================== *)

(* the least d with n <= 2^d (d <= 20) *)
Fixpoint depth_loop (n d : int) (H : Acc (Zwf 0) (gap 20 d)) {struct H} : int :=
  match bdec (d <? 20) with
  | left Hd => if (1 << d) <? n then depth_loop n (d + 1) (Acc_inv H (dec_step 20 d Hd)) else d
  | right _ => d
  end.

Fixpoint build (sa L R C roots : array int) (n D i nx : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int * array int * array int * array int :=
  match bdec (i <? n) with
  | left Hi =>
      let '(Lq, Rq, Cq) := ins L R C nx roots.[i] D sa.[i] (Zwf_well_founded 0 (φ D)) in
      build sa Lq Rq Cq roots.[i + 1 <- nx + D] n D (i + 1) (nx + D + 1)
        (Acc_inv H (dec_step n i Hi))
  | right _ => (L, R, C, roots)
  end.

(* ================================================================== *)
(* One query                                                           *)
(* ================================================================== *)

Definition cmp_at (x t : PrimString.string) (n m : int) (sa : array int) (i : int) : comparison :=
  cmpt x t n m sa.[i] 0 (Zwf_well_founded 0 (gap m 0)).

Definition answer1 (x : PrimString.string) (n : int) (sa L R C roots : array int) (D : int)
    (t : PrimString.string) (k : int) : int :=
  let m := PrimString.length t in
  let lo := bs (fun i => match cmp_at x t n m sa i with Gt => false | _ => true end) 0 n
              (Zwf_well_founded 0 (gap n 0)) in
  let hi := bs (fun i => match cmp_at x t n m sa i with Lt => true | _ => false end) 0 n
              (Zwf_well_founded 0 (gap n 0)) in
  if k <=? hi - lo then qry L R C roots.[lo] roots.[hi] D k (Zwf_well_founded 0 (φ D)) + 1
  else 0 - 1.

(* ================================================================== *)
(* All the queries, and the function                                   *)
(* ================================================================== *)

Fixpoint qloop (x : PrimString.string) (n : int) (sa L R C roots : array int) (D : int)
    (ts : array PrimString.string) (ks : array int) (out : array int) (q Q : int)
    (H : Acc (Zwf 0) (gap Q q)) {struct H} : array int :=
  match bdec (q <? Q) with
  | left Hq =>
      qloop x n sa L R C roots D ts ks
        out.[q <- answer1 x n sa L R C roots D ts.[q] ks.[q]] (q + 1) Q
        (Acc_inv H (dec_step Q q Hq))
  | right _ => out
  end.

Definition kth_occurrences_impl (x : PrimString.string) (ts : array PrimString.string)
    (ks : array uint) : array sint :=
  let n := PrimString.length x in
  let sa := build_sa x n in
  let D := depth_loop n 0 (Zwf_well_founded 0 (gap 20 0)) in
  let M := n * (D + 1) + 1 in
  let '(L, R, C, roots) :=
    build sa (PArray.make M 0) (PArray.make M 0) (PArray.make M 0) (PArray.make (n + 1) 0)
      n D 0 1 (Zwf_well_founded 0 (gap n 0)) in
  let Q := PArray.length ts in
  qloop x n sa L R C roots D ts ks (PArray.make Q 0) 0 Q (Zwf_well_founded 0 (gap Q 0)).

Definition kth_occurrences :
  PrimString.string -> array PrimString.string -> array uint -> array sint :=
  kth_occurrences_impl.
