(* Executable implementation and its required termination dependencies.
   Correctness proofs are in joggers_proofs.v. *)
(* Implementation of joggers (joggers.spec).  See README.md, section
   Implementation, for the algorithm and the structure of the proof. *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Reals Lra Permutation.
Import ListNotations.

Notation getl := Prelude.get.

Open Scope bool_scope.
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

Lemma dec_lt : forall i j : int,
  (i <? j) = true -> Zwf 0 (gap max_int (i + 1)) (gap max_int i).
Proof.
  intros i j H. rewrite ltb_spec in H.
  pose proof (to_Z_bounded j). change (φ max_int) with (wB - 1)%Z.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_down : forall i : int, (0 <? i) = true -> Zwf 0 (φ (i - 1)) (φ i).
Proof.
  intros i H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  assert (H1 : (φ (i - 1)) = ((φ i) - 1)%Z) by sia.
  unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Half-edge k (0 <= k < 2m): trail k seen from a_k when k < m, trail
   k - m seen from b_{k-m} otherwise.  [ep] is its tail, [oth] its head,
   [eid] its trail. *)
Definition ep (xa xb : array int) (m k : int) : int :=
  if k <? m then xa.[k] else xb.[k - m].
Definition oth (xa xb : array int) (m k : int) : int :=
  if k <? m then xb.[k] else xa.[k - m].
Definition eid (m k : int) : int := if k <? m then k else k - m.

(* inl.[x] := true for every lamp x of xl *)
Fixpoint lamp_loop (xl : array int) (L i : int) (inl : array bool)
    (H : Acc (Zwf 0) (gap L i)) {struct H} : array bool :=
  match bdec (i <? L) with
  | left Hi => lamp_loop xl L (i + 1) inl.[xl.[i] <- true]
                 (Acc_inv H (dec_step L i Hi))
  | right _ => inl
  end.

(* degree count: cnt.[w] = number of half-edges with tail w *)
Fixpoint cnt_loop (xa xb : array int) (m K i : int) (cnt : array int)
    (H : Acc (Zwf 0) (gap K i)) {struct H} : array int :=
  match bdec (i <? K) with
  | left Hi =>
      let w := ep xa xb m i in
      cnt_loop xa xb m K (i + 1) cnt.[w <- cnt.[w] + 1]
        (Acc_inv H (dec_step K i Hi))
  | right _ => cnt
  end.

(* CSR offsets (prefix sums) and a copy of them as fill cursors *)
Fixpoint off_loop (cnt : array int) (V v : int) (off cur : array int)
    (H : Acc (Zwf 0) (gap V v)) {struct H} : array int * array int :=
  match bdec (v <? V) with
  | left Hv =>
      let o := off.[v] in
      off_loop cnt V (v + 1) off.[v + 1 <- o + cnt.[v]] cur.[v <- o]
        (Acc_inv H (dec_step V v Hv))
  | right _ => (off, cur)
  end.

(* CSR targets: the half-edges of w at slots off.[w] .. off.[w+1]-1 *)
Fixpoint fill_loop (xa xb : array int) (m K i : int) (cur adj : array int)
    (H : Acc (Zwf 0) (gap K i)) {struct H} : array int :=
  match bdec (i <? K) with
  | left Hi =>
      let w := ep xa xb m i in
      let c := cur.[w] in
      fill_loop xa xb m K (i + 1) cur.[w <- c + 1] adj.[c <- i]
        (Acc_inv H (dec_step K i Hi))
  | right _ => adj
  end.

(* The state of the traversal from the campus. *)
Record bst : Type := Bst {
  vis : array bool;   (* visited *)
  dst : array int;    (* distance from the campus *)
  par : array int;    (* parent intersection *)
  pe  : array int;    (* trail to the parent *)
  ord : array int;    (* visit order (the queue) *)
  tl  : int           (* queue tail *)
}.

(* Scan the slots i .. hi-1 of intersection u (at distance du). *)
Fixpoint scan_loop (xa xb xd : array int) (m : int) (adj : array int)
    (u du hi i : int) (st : bst) (H : Acc (Zwf 0) (gap hi i)) {struct H} : bst :=
  match bdec (i <? hi) with
  | left Hi =>
      let k := adj.[i] in
      let w := oth xa xb m k in
      let st' :=
        if (vis st).[w] then st
        else
          let e := eid m k in
          Bst ((vis st).[w <- true]) ((dst st).[w <- du + xd.[e]])
              ((par st).[w <- u]) ((pe st).[w <- e])
              ((ord st).[tl st <- w]) (tl st + 1) in
      scan_loop xa xb xd m adj u du hi (i + 1) st' (Acc_inv H (dec_step hi i Hi))
  | right _ => st
  end.

(* Breadth-first traversal: pop the queue at h. *)
Fixpoint bfs_loop (xa xb xd : array int) (m : int) (adj off : array int)
    (h : int) (st : bst) (H : Acc (Zwf 0) (gap max_int h)) {struct H} : bst :=
  match bdec (h <? tl st) with
  | left Hh =>
      let u := (ord st).[h] in
      let st' := scan_loop xa xb xd m adj u ((dst st).[u]) off.[u + 1] off.[u] st
                   (Zwf_well_founded 0 _) in
      bfs_loop xa xb xd m adj off (h + 1) st' (Acc_inv H (dec_lt h (tl st) Hh))
  | right _ => st
  end.

(* Bottom-up sweep, in reverse visit order: a used trail from v to its
   parent p with neither end lit gets a new lamp at p. *)
Fixpoint sweep_loop (s : int) (inl : array bool) (ord par dst : array int)
    (i : int) (ch : array bool) (c : int) (H : Acc (Zwf 0) (φ i)) {struct H} : int :=
  match bdec (0 <? i) with
  | left Hi =>
      let v := ord.[i] in
      let p := par.[v] in
      let dp := dst.[p] in
      if (dp + dp <? s) && negb (inl.[v] || ch.[v]) && negb (inl.[p] || ch.[p])
      then sweep_loop s inl ord par dst (i - 1) ch.[p <- true] (c + 1)
             (Acc_inv H (dec_down i Hi))
      else sweep_loop s inl ord par dst (i - 1) ch c (Acc_inv H (dec_down i Hi))
  | right _ => c
  end.

Definition joggers_impl (n s : int) (xa xb xd xl : array int) : int :=
  let m := PArray.length xa in
  let K := m + m in
  let V := n + 1 in
  let inl := lamp_loop xl (PArray.length xl) 0 (PArray.make V false)
               (Zwf_well_founded 0 _) in
  let cnt := cnt_loop xa xb m K 0 (PArray.make V 0) (Zwf_well_founded 0 _) in
  let oc := off_loop cnt V 0 (PArray.make (V + 1) 0) (PArray.make V 0)
              (Zwf_well_founded 0 _) in
  let adj := fill_loop xa xb m K 0 (snd oc) (PArray.make K 0)
               (Zwf_well_founded 0 _) in
  let st0 := Bst ((PArray.make V false).[1 <- true]) (PArray.make V 0)
                 (PArray.make V 0) (PArray.make V 0)
                 ((PArray.make n 0).[0 <- 1]) 1 in
  let st := bfs_loop xa xb xd m adj (fst oc) 0 st0 (Zwf_well_founded 0 _) in
  sweep_loop s inl (ord st) (par st) (dst st) (tl st - 1) (PArray.make V false) 0
    (Zwf_well_founded 0 _).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition joggers : uint -> uint -> array uint -> array uint ->
  array uint -> array uint -> uint := joggers_impl.
