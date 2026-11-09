(* Executable implementation and its required termination dependencies.
   Correctness proofs are in loopycabdrivers_proofs.v. *)
(* Implementation of loopycabdrivers (loopycabdrivers.spec). *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Relations Sorting Permutation.
From Stdlib Require String Ascii PrimString PString.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

Notation pstring := PrimString.string.

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

(* ------------------------------------------------------------------ *)
(* Phase 1: names to dense ids, by a hash table with linear probing    *)
(* ------------------------------------------------------------------ *)

Fixpoint hloop (s : pstring) (n k h : int)
    (H : Acc (Zwf 0) (gap n k)) {struct H} : int :=
  match bdec (k <? n) with
  | left Hk => hloop s n (k + 1) (h * 31 + PrimString.get s k)
                 (Acc_inv H (dec_step n k Hk))
  | right _ => h
  end.

Definition hmask : int := 65535.
Definition hsize : int := 65536.

Definition hash (s : pstring) : int :=
  (hloop s (PrimString.length s) 0 7
     (Zwf_well_founded 0 (gap (PrimString.length s) 0))) land hmask.

(* The first slot p' >= p that is empty or holds s: (p', true) when it
   holds s, (p', false) when it is empty. *)
Fixpoint probe (tbl : array int) (names : array pstring) (s : pstring)
    (T p : int) (H : Acc (Zwf 0) (gap T p)) {struct H} : int * bool :=
  match bdec (p <? T) with
  | left Hp =>
      let e := tbl.[p] in
      if e =? 0 then (p, false)
      else match PrimString.compare names.[e - 1] s with
           | Eq => (p, true)
           | _ => probe tbl names s T (p + 1) (Acc_inv H (dec_step T p Hp))
           end
  | right _ => (p, false)
  end.

Record hstate := HS { ht : array int; hn : array pstring; hc : int }.

Definition lookup (st : hstate) (s : pstring) : hstate * int :=
  let tbl := ht st in
  let T := PArray.length tbl in
  let pf := probe tbl (hn st) s T (hash s) (Zwf_well_founded 0 (gap T (hash s))) in
  let p := fst pf in
  if snd pf then (st, tbl.[p] - 1)
  else (HS tbl.[p <- hc st + 1] (hn st).[hc st <- s] (hc st + 1), hc st).

Fixpoint idloop (x y : array pstring) (m k : int) (st : hstate)
    (is id : array int) (H : Acc (Zwf 0) (gap m k)) {struct H}
    : hstate * array int * array int :=
  match bdec (k <? m) with
  | left Hk =>
      let r1 := lookup st x.[k] in
      let r2 := lookup (fst r1) y.[k] in
      idloop x y m (k + 1) (fst r2) is.[k <- snd r1] id.[k <- snd r2]
        (Acc_inv H (dec_step m k Hk))
  | right _ => (st, is, id)
  end.

(* ------------------------------------------------------------------ *)
(* Phase 2: compressed adjacency (CSR) of m pairs (es k, ed k)         *)
(* ------------------------------------------------------------------ *)

Fixpoint cnt_loop (es : int -> int) (m k : int) (cnt : array int)
    (H : Acc (Zwf 0) (gap m k)) {struct H} : array int :=
  match bdec (k <? m) with
  | left Hk =>
      let u := es k in
      cnt_loop es m (k + 1) cnt.[u <- cnt.[u] + 1] (Acc_inv H (dec_step m k Hk))
  | right _ => cnt
  end.

Fixpoint pre_loop (cnt : array int) (V u : int) (off : array int)
    (H : Acc (Zwf 0) (gap V u)) {struct H} : array int :=
  match bdec (u <? V) with
  | left Hu =>
      pre_loop cnt V (u + 1) off.[u + 1 <- off.[u] + cnt.[u]]
        (Acc_inv H (dec_step V u Hu))
  | right _ => off
  end.

Fixpoint fill_loop (es ed : int -> int) (m k : int) (pos adj : array int)
    (H : Acc (Zwf 0) (gap m k)) {struct H} : array int :=
  match bdec (k <? m) with
  | left Hk =>
      let u := es k in
      let p := pos.[u] in
      fill_loop es ed m (k + 1) pos.[u <- p + 1] adj.[p <- ed k]
        (Acc_inv H (dec_step m k Hk))
  | right _ => adj
  end.

Definition csr (V m : int) (es ed : int -> int) : array int * array int :=
  let cnt := cnt_loop es m 0 (PArray.make V 0) (Zwf_well_founded 0 (gap m 0)) in
  let off := pre_loop cnt V 0 (PArray.make (V + 1) 0) (Zwf_well_founded 0 (gap V 0)) in
  let adj := fill_loop es ed m 0 (PArray.copy off) (PArray.make m 0)
               (Zwf_well_founded 0 (gap m 0)) in
  (off, adj).

(* ------------------------------------------------------------------ *)
(* Phase 3: Kosaraju, first pass: iterative DFS, finishing order       *)
(* ------------------------------------------------------------------ *)

(* The first j in [j0, e) with adj.[j] unmarked, or e. *)
Fixpoint scan (mark adj : array int) (e j : int)
    (H : Acc (Zwf 0) (gap e j)) {struct H} : int :=
  match bdec (j <? e) with
  | left Hj =>
      if mark.[adj.[j]] =? 0 then j
      else scan mark adj e (j + 1) (Acc_inv H (dec_step e j Hj))
  | right _ => e
  end.

Record d1 := D1 { mk : array int; sv : array int; sc : array int;
                  po : array int; sp : int; np : int; rt : int }.

Definition dfs_step (V : int) (off adj : array int) (s : d1) : option d1 :=
  if 0 <? sp s then
    let t := sp s - 1 in
    let u := (sv s).[t] in
    let e := off.[u + 1] in
    let j := scan (mk s) adj e (sc s).[t]
               (Zwf_well_founded 0 (gap e (sc s).[t])) in
    if j <? e then
      let w := adj.[j] in
      Some (D1 (mk s).[w <- 1] (sv s).[sp s <- w]
               (sc s).[t <- j + 1].[sp s <- off.[w]]
               (po s) (sp s + 1) (np s) (rt s))
    else
      Some (D1 (mk s) (sv s) (sc s) (po s).[np s <- u] t (np s + 1) (rt s))
  else if rt s <? V then
    let r := rt s in
    if (mk s).[r] =? 0 then
      Some (D1 (mk s).[r <- 1] (sv s).[0 <- r] (sc s).[0 <- off.[r]]
               (po s) 1 (np s) (r + 1))
    else Some (D1 (mk s) (sv s) (sc s) (po s) (sp s) (np s) (r + 1))
  else None.

Fixpoint dfs (V : int) (off adj : array int) (s : d1) (bound steps : int)
    (H : Acc (Zwf 0) (gap bound steps)) {struct H} : array int :=
  match bdec (steps <? bound) with
  | left Hs =>
      match dfs_step V off adj s with
      | Some s' => dfs V off adj s' bound (steps + 1)
                     (Acc_inv H (dec_step bound steps Hs))
      | None => po s
      end
  | right _ => po s
  end.

(* ------------------------------------------------------------------ *)
(* Phase 4: Kosaraju, second pass: searches on the reversed graph, in  *)
(* decreasing finishing order; labels 1 .. C                           *)
(* ------------------------------------------------------------------ *)

Fixpoint push_preds (radj : array int) (c e j : int) (lab stk : array int)
    (sp : int) (H : Acc (Zwf 0) (gap e j)) {struct H}
    : array int * array int * int :=
  match bdec (j <? e) with
  | left Hj =>
      let w := radj.[j] in
      if lab.[w] =? 0 then
        push_preds radj c e (j + 1) lab.[w <- c] stk.[sp <- w] (sp + 1)
          (Acc_inv H (dec_step e j Hj))
      else push_preds radj c e (j + 1) lab stk sp (Acc_inv H (dec_step e j Hj))
  | right _ => (lab, stk, sp)
  end.

Record d2 := D2 { lb : array int; sk : array int; sq : int; ii : int; cc : int }.

Definition asg_step (roff radj post : array int) (s : d2) : option d2 :=
  if 0 <? sq s then
    let t := sq s - 1 in
    let u := (sk s).[t] in
    let r := push_preds radj (cc s) roff.[u + 1] roff.[u] (lb s) (sk s) t
               (Zwf_well_founded 0 (gap roff.[u + 1] roff.[u])) in
    Some (D2 (fst (fst r)) (snd (fst r)) (snd r) (ii s) (cc s))
  else if 0 <? ii s then
    let i := ii s - 1 in
    let r := post.[i] in
    if (lb s).[r] =? 0 then
      Some (D2 (lb s).[r <- cc s + 1] (sk s).[0 <- r] 1 i (cc s + 1))
    else Some (D2 (lb s) (sk s) (sq s) i (cc s))
  else None.

Fixpoint assign (roff radj post : array int) (s : d2) (bound steps : int)
    (H : Acc (Zwf 0) (gap bound steps)) {struct H} : d2 :=
  match bdec (steps <? bound) with
  | left Hs =>
      match asg_step roff radj post s with
      | Some s' => assign roff radj post s' bound (steps + 1)
                     (Acc_inv H (dec_step bound steps Hs))
      | None => s
      end
  | right _ => s
  end.

(* ------------------------------------------------------------------ *)
(* Phase 5: merge sort of vertex ids by name                           *)
(* ------------------------------------------------------------------ *)

Section Msort.
Variable le : int -> int -> bool.

Fixpoint merge_loop (a t : array int) (mid hi i j k : int)
    (H : Acc (Zwf 0) (gap hi k)) {struct H} : array int :=
  match bdec (k <? hi) with
  | left Hk =>
      if (i <? mid) && ((hi <=? j) || le a.[i] a.[j]) then
        merge_loop a t.[k <- a.[i]] mid hi (i + 1) j (k + 1)
          (Acc_inv H (dec_step hi k Hk))
      else
        merge_loop a t.[k <- a.[j]] mid hi i (j + 1) (k + 1)
          (Acc_inv H (dec_step hi k Hk))
  | right _ => t
  end.

Fixpoint copy_back (t a : array int) (hi k : int)
    (H : Acc (Zwf 0) (gap hi k)) {struct H} : array int :=
  match bdec (k <? hi) with
  | left Hk => copy_back t a.[k <- t.[k]] hi (k + 1) (Acc_inv H (dec_step hi k Hk))
  | right _ => a
  end.

Lemma half_dec1 : forall lo hi : int,
  (lo <? hi) = true -> (1 <? hi - lo) = true ->
  Zwf 0 (gap (lo + (hi - lo) / 2) lo) (gap hi lo).
Proof.
  intros lo hi H1 H2. rewrite ltb_spec in H1, H2. unfold Zwf, gap.
  assert (E : (φ (hi - lo)) = ((φ hi) - (φ lo))%Z) by sia.
  rewrite E in H2. change (φ 1) with 1%Z in H2.
  assert (E2 : (φ (lo + (hi - lo) / 2)) = ((φ lo) + ((φ hi) - (φ lo)) / 2)%Z).
  { rewrite add_spec, div_spec, E. change (φ 2) with 2%Z.
    pose proof (to_Z_bounded hi). pose proof (to_Z_bounded lo).
    rewrite Z.mod_small; [lia|].
    split; [apply Z.add_nonneg_nonneg; [lia| apply Z.div_pos; lia]|].
    assert (((φ hi) - (φ lo)) / 2 <= (φ hi) - (φ lo))%Z by (apply Z.div_le_upper_bound; lia).
    lia. }
  rewrite E2.
  assert (0 <= ((φ hi) - (φ lo)) / 2)%Z by (apply Z.div_pos; lia).
  assert (((φ hi) - (φ lo)) / 2 < (φ hi) - (φ lo))%Z by (apply Z.div_lt; lia).
  lia.
Qed.

Lemma half_dec2 : forall lo hi : int,
  (lo <? hi) = true -> (1 <? hi - lo) = true ->
  Zwf 0 (gap hi (lo + (hi - lo) / 2)) (gap hi lo).
Proof.
  intros lo hi H1 H2. rewrite ltb_spec in H1, H2. unfold Zwf, gap.
  assert (E : (φ (hi - lo)) = ((φ hi) - (φ lo))%Z) by sia.
  rewrite E in H2. change (φ 1) with 1%Z in H2.
  assert (E2 : (φ (lo + (hi - lo) / 2)) = ((φ lo) + ((φ hi) - (φ lo)) / 2)%Z).
  { rewrite add_spec, div_spec, E. change (φ 2) with 2%Z.
    pose proof (to_Z_bounded hi). pose proof (to_Z_bounded lo).
    rewrite Z.mod_small; [lia|].
    split; [apply Z.add_nonneg_nonneg; [lia| apply Z.div_pos; lia]|].
    assert (((φ hi) - (φ lo)) / 2 <= (φ hi) - (φ lo))%Z by (apply Z.div_le_upper_bound; lia).
    lia. }
  rewrite E2.
  assert (0 < ((φ hi) - (φ lo)) / 2)%Z by (apply Z.div_str_pos; lia).
  assert (((φ hi) - (φ lo)) / 2 < (φ hi) - (φ lo))%Z by (apply Z.div_lt; lia).
  lia.
Qed.

Fixpoint msort (a t : array int) (lo hi : int)
    (H : Acc (Zwf 0) (gap hi lo)) {struct H} : array int * array int :=
  match bdec (lo <? hi) with
  | left H1 =>
      match bdec (1 <? hi - lo) with
      | left H2 =>
          let mid := lo + (hi - lo) / 2 in
          let r1 := msort a t lo mid (Acc_inv H (half_dec1 lo hi H1 H2)) in
          let r2 := msort (fst r1) (snd r1) mid hi (Acc_inv H (half_dec2 lo hi H1 H2)) in
          let t3 := merge_loop (fst r2) (snd r2) mid hi lo mid lo
                      (Zwf_well_founded 0 (gap hi lo)) in
          (copy_back t3 (fst r2) hi lo (Zwf_well_founded 0 (gap hi lo)), t3)
      | right _ => (a, t)
      end
  | right _ => (a, t)
  end.

End Msort.

(* ------------------------------------------------------------------ *)
(* Phase 6: the output                                                 *)
(* ------------------------------------------------------------------ *)

Fixpoint iota_loop (n k : int) (a : array int)
    (H : Acc (Zwf 0) (gap n k)) {struct H} : array int :=
  match bdec (k <? n) with
  | left Hk => iota_loop n (k + 1) a.[k <- k] (Acc_inv H (dec_step n k Hk))
  | right _ => a
  end.

Record d3 := D3 { gord : array int; gn : int; av : array pstring; an : int }.

Fixpoint emit_loop (names : array pstring) (lab csz boff badj byname : array int)
    (V k : int) (s : d3) (H : Acc (Zwf 0) (gap V k)) {struct H} : d3 :=
  match bdec (k <? V) with
  | left Hk =>
      let v := byname.[k] in
      let c := lab.[v] in
      if 1 <? csz.[c] then
        if badj.[boff.[c]] =? v then
          emit_loop names lab csz boff badj byname V (k + 1)
            (D3 (gord s).[gn s <- c] (gn s + 1) (av s) (an s))
            (Acc_inv H (dec_step V k Hk))
        else
          emit_loop names lab csz boff badj byname V (k + 1) s
            (Acc_inv H (dec_step V k Hk))
      else
        emit_loop names lab csz boff badj byname V (k + 1)
          (D3 (gord s) (gn s) (av s).[an s <- names.[v]] (an s + 1))
          (Acc_inv H (dec_step V k Hk))
  | right _ => s
  end.

Fixpoint copy_loop (src : array pstring) (n k : int) (dst : array pstring)
    (H : Acc (Zwf 0) (gap n k)) {struct H} : array pstring :=
  match bdec (k <? n) with
  | left Hk => copy_loop src n (k + 1) dst.[k <- src.[k]] (Acc_inv H (dec_step n k Hk))
  | right _ => dst
  end.

Fixpoint inner_loop (names : array pstring) (badj : array int) (st n k : int)
    (g : array pstring) (H : Acc (Zwf 0) (gap n k)) {struct H} : array pstring :=
  match bdec (k <? n) with
  | left Hk =>
      inner_loop names badj st n (k + 1) g.[k <- names.[badj.[st + k]]]
        (Acc_inv H (dec_step n k Hk))
  | right _ => g
  end.

Definition group_arr (names : array pstring) (boff badj : array int) (c : int)
    : array pstring :=
  let st := boff.[c] in
  let n := boff.[c + 1] - st in
  inner_loop names badj st n 0 (PArray.make n (PrimString.make 0 0))
    (Zwf_well_founded 0 (gap n 0)).

Fixpoint groups_loop (names : array pstring) (boff badj gord : array int)
    (G g : int) (out : array (array pstring))
    (H : Acc (Zwf 0) (gap G g)) {struct H} : array (array pstring) :=
  match bdec (g <? G) with
  | left Hg =>
      groups_loop names boff badj gord G (g + 1)
        out.[g <- group_arr names boff badj gord.[g]]
        (Acc_inv H (dec_step G g Hg))
  | right _ => out
  end.

Definition name_le (names : array pstring) (a b : int) : bool :=
  match PrimString.compare names.[a] names.[b] with
  | Gt => false
  | _ => true
  end.

Definition empty_str : pstring := PrimString.make 0 0.

Definition loopy_impl (x y : array pstring)
    : array (array pstring) * array pstring :=
  let m := PArray.length x in
  let st0 := HS (PArray.make (hsize + 2 * m + 1) 0)
                (PArray.make (2 * m + 1) empty_str) 0 in
  let r0 := idloop x y m 0 st0 (PArray.make m 0) (PArray.make m 0)
              (Zwf_well_founded 0 (gap m 0)) in
  let st := fst (fst r0) in
  let is := snd (fst r0) in
  let id := snd r0 in
  let V := hc st in
  let names := hn st in
  let g := csr V m (fun k => is.[k]) (fun k => id.[k]) in
  let gt := csr V m (fun k => id.[k]) (fun k => is.[k]) in
  let bound := 3 * V + 1 in
  let post := dfs V (fst g) (snd g)
                (D1 (PArray.make V 0) (PArray.make V 0) (PArray.make V 0)
                    (PArray.make V 0) 0 0 0)
                bound 0 (Zwf_well_founded 0 (gap bound 0)) in
  let s2 := assign (fst gt) (snd gt) post
              (D2 (PArray.make V 0) (PArray.make V 0) 0 V 0)
              bound 0 (Zwf_well_founded 0 (gap bound 0)) in
  let lab := lb s2 in
  let C := cc s2 in
  let csz := cnt_loop (fun v => lab.[v]) V 0 (PArray.make (C + 1) 0)
               (Zwf_well_founded 0 (gap V 0)) in
  let byname := fst (msort (name_le names) (iota_loop V 0 (PArray.make V 0)
                                              (Zwf_well_founded 0 (gap V 0)))
                       (PArray.make V 0) 0 V (Zwf_well_founded 0 (gap V 0))) in
  let b := csr (C + 1) V (fun k => lab.[byname.[k]]) (fun k => byname.[k]) in
  let s3 := emit_loop names lab csz (fst b) (snd b) byname V 0
              (D3 (PArray.make V 0) 0 (PArray.make V empty_str) 0)
              (Zwf_well_founded 0 (gap V 0)) in
  let avoid := copy_loop (av s3) (an s3) 0 (PArray.make (an s3) empty_str)
                 (Zwf_well_founded 0 (gap (an s3) 0)) in
  let groups := groups_loop names (fst b) (snd b) (gord s3) (gn s3) 0
                  (PArray.make (gn s3) (PArray.make 0 empty_str))
                  (Zwf_well_founded 0 (gap (gn s3) 0)) in
  (groups, avoid).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition loopy_regions : array PrimString.string -> array PrimString.string ->
  array (array PrimString.string) * array PrimString.string := loopy_impl.
