(* Implementation of mazemovement (mazemovement.spec): push-relabel
   maximum flow, first phase, on the dense n x n residual table.
   See README.md, section Implementation, for the design and the proof. *)

From Mazemovement.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Bool Uint63 PArray ZifyUint63 Lia Zwf.
From KattisLib Require Import Cost.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.
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
Elpi complexity sumbool.
Elpi complexity andb.
Elpi complexity negb.
Elpi complexity fst.
Elpi complexity snd.
Elpi complexity bdec.

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Definition wf0 (m i : int) : Acc (Zwf 0) (gap m i) := Zwf_well_founded 0 (gap m i).

(* ------------------------------------------------------------------ *)
(* Euclid's gcd on int                                                 *)
(* ------------------------------------------------------------------ *)

Lemma gcd_dec : forall a b : int, (b =? 0) = false -> Zwf 0 (φ (a mod b)) (φ b).
Proof.
  intros a b Hb. rewrite eqb_false_spec in Hb.
  assert ((φ b) <> 0%Z) by (intro E; apply Hb; apply to_Z_inj; exact E).
  unfold Zwf. rewrite mod_spec. pose proof (to_Z_bounded b). pose proof (to_Z_bounded a).
  pose proof (Z.mod_pos_bound (φ a) (φ b)). lia.
Qed.

Fixpoint gcd_loop (a b : int) (H : Acc (Zwf 0) (φ b)) {struct H} : int :=
  match bdec (b =? 0) with
  | left _ => a
  | right Hb => gcd_loop b (a mod b) (Acc_inv H (gcd_dec a b Hb))
  end.
Elpi complexity gcd_loop.

Definition igcd (a b : int) : int := gcd_loop a b (Zwf_well_founded 0 (φ b)).
Elpi complexity igcd.

(* the capacity of the passage between positions i and j *)
Definition capf (x : array int) (i j : int) : int :=
  if i =? j then 0 else
  let g := igcd x.[i] x.[j] in if 1 <? g then g else 0.
Elpi complexity capf.

(* ------------------------------------------------------------------ *)
(* Setup loops                                                         *)
(* ------------------------------------------------------------------ *)

(* cells (i, j) and (j, i) for j = j0 .. n-1 *)
Fixpoint fill_row (x : array int) (n i : int) (tbl : array int) (j : int)
    (H : Acc (Zwf 0) (gap n j)) {struct H} : array int :=
  match bdec (j <? n) with
  | left Hj =>
      let c := capf x i j in
      fill_row x n i (tbl.[i * n + j <- c].[j * n + i <- c]) (j + 1)
        (Acc_inv H (dec_step n j Hj))
  | right _ => tbl
  end.
Elpi complexity fill_row.

Fixpoint fill_tab (x : array int) (n : int) (tbl : array int) (i : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi =>
      fill_tab x n (fill_row x n i tbl i (wf0 n i)) (i + 1)
        (Acc_inv H (dec_step n i Hi))
  | right _ => tbl
  end.
Elpi complexity fill_tab.

(* position of the smallest / largest number among positions i .. n-1, and best *)
Fixpoint amin (x : array int) (n i best : int) (H : Acc (Zwf 0) (gap n i)) {struct H} : int :=
  match bdec (i <? n) with
  | left Hi => amin x n (i + 1) (if x.[i] <? x.[best] then i else best)
                 (Acc_inv H (dec_step n i Hi))
  | right _ => best
  end.
Elpi complexity amin.

Fixpoint amax (x : array int) (n i best : int) (H : Acc (Zwf 0) (gap n i)) {struct H} : int :=
  match bdec (i <? n) with
  | left Hi => amax x n (i + 1) (if x.[best] <? x.[i] then i else best)
                 (Acc_inv H (dec_step n i Hi))
  | right _ => best
  end.
Elpi complexity amax.

Fixpoint rng_ok (x : array int) (n i : int) (H : Acc (Zwf 0) (gap n i)) {struct H} : bool :=
  match bdec (i <? n) with
  | left Hi => if (2 <=? x.[i]) && (x.[i] <=? 2000000000)
               then rng_ok x n (i + 1) (Acc_inv H (dec_step n i Hi)) else false
  | right _ => true
  end.
Elpi complexity rng_ok.

(* saturating the passages out of s; the queue receives the new active rooms *)
Fixpoint sat (n s t : int) (tbl ex q : array int) (ql v : int)
    (H : Acc (Zwf 0) (gap n v)) {struct H} : array int * array int * array int * int :=
  match bdec (v <? n) with
  | left Hv =>
      let c := tbl.[s * n + v] in
      let tbl1 := tbl.[s * n + v <- 0] in
      let tbl2 := tbl1.[v * n + s <- tbl1.[v * n + s] + c] in
      let ex1 := ex.[v <- c] in
      let b := (0 <? c) && negb (v =? t) && negb (v =? s) in
      let q1 := if b then q.[ql <- v] else q in
      let ql1 := if b then ql + 1 else ql in
      sat n s t tbl2 ex1 q1 ql1 (v + 1) (Acc_inv H (dec_step n v Hv))
  | right _ => (tbl, ex, q, ql)
  end.
Elpi complexity sat.

(* ------------------------------------------------------------------ *)
(* Height loops                                                        *)
(* ------------------------------------------------------------------ *)

(* a.[y] <- F y a.[y] for y = i .. m-1 (written only when it changes) *)
Fixpoint amap (F : int -> int -> int) (a : array int) (i m : int)
    (H : Acc (Zwf 0) (gap m i)) {struct H} : array int :=
  match bdec (i <? m) with
  | left Hi =>
      let o := a.[i] in
      let w := F i o in
      amap F (if w =? o then a else a.[i <- w]) (i + 1) m (Acc_inv H (dec_step m i Hi))
  | right _ => a
  end.
Elpi complexity amap.

(* backward BFS from t, level by level: the vertices of level L relax
   their residual predecessors to L+1 *)
Definition relaxF (tbl : array int) (n b L1 : int) (a o : int) : int :=
  if (0 <? tbl.[a * n + b]) && (L1 <? o) then L1 else o.
Elpi complexity relaxF.

Fixpoint has_val (d : array int) (n L j : int) (H : Acc (Zwf 0) (gap n j)) {struct H} : bool :=
  match bdec (j <? n) with
  | left Hj => if d.[j] =? L then true else has_val d n L (j + 1) (Acc_inv H (dec_step n j Hj))
  | right _ => false
  end.
Elpi complexity has_val.

Fixpoint lscan (tbl : array int) (n L : int) (d : array int) (j : int)
    (H : Acc (Zwf 0) (gap n j)) {struct H} : array int :=
  match bdec (j <? n) with
  | left Hj =>
      lscan tbl n L
        (if d.[j] =? L then amap (relaxF tbl n j (L + 1)) d 0 n (wf0 n 0) else d)
        (j + 1) (Acc_inv H (dec_step n j Hj))
  | right _ => d
  end.
Elpi complexity lscan.

Fixpoint layers (tbl : array int) (n L : int) (d : array int)
    (H : Acc (Zwf 0) (gap n L)) {struct H} : array int :=
  match bdec (L <? n) with
  | left HL =>
      if has_val d n L 0 (wf0 n 0)
      then layers tbl n (L + 1) (lscan tbl n L d 0 (wf0 n 0)) (Acc_inv H (dec_step n L HL))
      else d
  | right _ => d
  end.
Elpi complexity layers.

Definition bfs (tbl : array int) (n t : int) : array int :=
  layers tbl n 0 ((PArray.make n n).[t <- 0]) (wf0 n 0).
Elpi complexity bfs.

Definition maxF (d : array int) (y o : int) : int := if o <? d.[y] then d.[y] else o.
Elpi complexity maxF.

(* global relabeling: the heights become the BFS distances (never lower) *)
Definition glob (tbl : array int) (n t : int) (h : array int) : array int :=
  let d := bfs tbl n t in amap (maxF d) h 0 n (wf0 n 0).
Elpi complexity glob.

Fixpoint cntl (h cnt : array int) (n i : int) (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi => let k := h.[i] in
               cntl h (cnt.[k <- cnt.[k] + 1]) n (i + 1) (Acc_inv H (dec_step n i Hi))
  | right _ => cnt
  end.
Elpi complexity cntl.

Definition count (h : array int) (n : int) : array int :=
  cntl h (PArray.make (n + 1) 0) n 0 (wf0 n 0).
Elpi complexity count.

(* relabel: 1 + the least height of a residual neighbour, at most n *)
Fixpoint rmin (tbl : array int) (n u : int) (h : array int) (b acc : int)
    (H : Acc (Zwf 0) (gap n b)) {struct H} : int :=
  match bdec (b <? n) with
  | left Hb =>
      rmin tbl n u h (b + 1)
        (if (0 <? tbl.[u * n + b]) && (h.[b] + 1 <? acc) then h.[b] + 1 else acc)
        (Acc_inv H (dec_step n b Hb))
  | right _ => acc
  end.
Elpi complexity rmin.

(* gap heuristic: no vertex at height k (checked), lift k < h < n to n *)
Fixpoint no_height (h : array int) (n k i : int) (H : Acc (Zwf 0) (gap n i)) {struct H} : bool :=
  match bdec (i <? n) with
  | left Hi => if h.[i] =? k then false else no_height h n k (i + 1) (Acc_inv H (dec_step n i Hi))
  | right _ => true
  end.
Elpi complexity no_height.

Definition liftF (n k : int) (y o : int) : int := if (k <? o) && (o <? n) then n else o.
Elpi complexity liftF.

Definition lift (h : array int) (n k : int) : array int := amap (liftF n k) h 0 n (wf0 n 0).
Elpi complexity lift.

Fixpoint cnt_lift (h cnt : array int) (n k i : int) (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi =>
      let o := h.[i] in
      cnt_lift h (if (k <? o) && (o <? n) then cnt.[o <- cnt.[o] - 1] else cnt) n k (i + 1)
        (Acc_inv H (dec_step n i Hi))
  | right _ => cnt
  end.
Elpi complexity cnt_lift.

(* ------------------------------------------------------------------ *)
(* Selection                                                           *)
(* ------------------------------------------------------------------ *)

Definition active (ex h : array int) (n s t v : int) : bool :=
  (0 <? ex.[v]) && (h.[v] <? n) && negb (v =? s) && negb (v =? t).
Elpi complexity active.

Fixpoint find_act (ex h : array int) (n s t i : int) (H : Acc (Zwf 0) (gap n i)) {struct H} : int :=
  match bdec (i <? n) with
  | left Hi => if active ex h n s t i then i
               else find_act ex h n s t (i + 1) (Acc_inv H (dec_step n i Hi))
  | right _ => n
  end.
Elpi complexity find_act.

Definition adm (tbl h : array int) (n u v : int) : bool :=
  (0 <? tbl.[u * n + v]) && (h.[u] =? h.[v] + 1).
Elpi complexity adm.

Definition enq_pos (qh ql n : int) : int := let p := qh + ql in if p <? n then p else p - n.
Elpi complexity enq_pos.

(* ------------------------------------------------------------------ *)
(* The main loop                                                       *)
(* ------------------------------------------------------------------ *)

Record st := mkst {
  s_tbl : array int; s_ex : array int; s_h : array int; s_cur : array int;
  s_cnt : array int; s_q : array int; s_qh : int; s_ql : int; s_cu : int; s_rl : int }.
Elpi complexity st.
Elpi complexity s_tbl.
Elpi complexity s_ex.
Elpi complexity s_h.
Elpi complexity s_cur.
Elpi complexity s_cnt.
Elpi complexity s_q.
Elpi complexity s_qh.
Elpi complexity s_ql.
Elpi complexity s_cu.
Elpi complexity s_rl.

Inductive Step (n s t : int) : st -> st -> Prop :=
| step_push : forall tbl ex h cur cnt q qh ql cu rl,
    (cu <? n) = true -> (cur.[cu] <? n) = true -> adm tbl h n cu cur.[cu] = true ->
    Step n s t (mkst tbl ex h cur cnt q qh ql cu rl)
      (let v := cur.[cu] in
       let r := tbl.[cu * n + v] in
       let e := ex.[cu] in
       let d := if e <? r then e else r in
       let tbl1 := tbl.[cu * n + v <- r - d] in
       let tbl2 := tbl1.[v * n + cu <- tbl1.[v * n + cu] + d] in
       let ev := ex.[v] in
       let ex1 := ex.[cu <- e - d] in
       let ex2 := ex1.[v <- ev + d] in
       let b := (ev =? 0) && negb (v =? t) && negb (v =? s) && (ql <? n) in
       let q1 := if b then q.[enq_pos qh ql n <- v] else q in
       let ql1 := if b then ql + 1 else ql in
       let cu1 := if e - d =? 0 then n else cu in
       mkst tbl2 ex2 h cur cnt q1 qh ql1 cu1 rl)
| step_adv : forall tbl ex h cur cnt q qh ql cu rl,
    (cu <? n) = true -> (cur.[cu] <? n) = true -> adm tbl h n cu cur.[cu] = false ->
    Step n s t (mkst tbl ex h cur cnt q qh ql cu rl)
      (mkst tbl ex h (cur.[cu <- cur.[cu] + 1]) cnt q qh ql cu rl)
| step_rel : forall tbl ex h cur cnt q qh ql cu rl,
    (cu <? n) = true -> (cur.[cu] <? n) = false ->
    Step n s t (mkst tbl ex h cur cnt q qh ql cu rl)
      (let oh := h.[cu] in
       let nh := rmin tbl n cu h 0 n (wf0 n 0) in
       let h1 := h.[cu <- nh] in
       let cur1 := cur.[cu <- 0] in
       let co := cnt.[oh] - 1 in
       let cnt1 := cnt.[oh <- co] in
       let cnt2 := cnt1.[nh <- cnt1.[nh] + 1] in
       let g := (co =? 0) && (0 <? oh) && (oh <? n) && no_height h1 n oh 0 (wf0 n 0) in
       let cnt3 := if g then cnt_lift h1 cnt2 n oh 0 (wf0 n 0) else cnt2 in
       let h2 := if g then lift h1 n oh else h1 in
       let rl1 := rl + 1 in
       let gl := n <=? rl1 in
       let h3 := if gl then glob tbl n t h2 else h2 in
       let cur2 := if gl then PArray.make n 0 else cur1 in
       let cnt4 := if gl then count h3 n else cnt3 in
       let rl2 := if gl then 0 else rl1 in
       let cu1 := if h3.[cu] <? n then cu else n in
       mkst tbl ex h3 cur2 cnt4 q qh ql cu1 rl2)
| step_pop : forall tbl ex h cur cnt q qh ql cu rl,
    (cu <? n) = false -> (0 <? ql) = true ->
    Step n s t (mkst tbl ex h cur cnt q qh ql cu rl)
      (let v := q.[qh] in
       let qh1 := if qh + 1 =? n then 0 else qh + 1 in
       let cu1 := if (v <? n) && active ex h n s t v then v else n in
       mkst tbl ex h cur cnt q qh1 (ql - 1) cu1 rl)
| step_scan : forall tbl ex h cur cnt q qh ql cu rl,
    (cu <? n) = false -> (0 <? ql) = false ->
    (find_act ex h n s t 0 (wf0 n 0) <? n) = true ->
    Step n s t (mkst tbl ex h cur cnt q qh ql cu rl)
      (mkst tbl ex h cur cnt q qh ql (find_act ex h n s t 0 (wf0 n 0)) rl).

Definition StepR (n s t : int) (S' S : st) : Prop := Step n s t S S'.

Fixpoint mloop (n s t : int) (tbl ex h cur cnt q : array int) (qh ql cu rl : int)
    (H : Acc (StepR n s t) (mkst tbl ex h cur cnt q qh ql cu rl)) {struct H} : int :=
  match bdec (cu <? n) with
  | left H1 =>
      let v := cur.[cu] in
      match bdec (v <? n) with
      | left H2 =>
          match bdec (adm tbl h n cu v) with
          | left H3 =>
              let r := tbl.[cu * n + v] in
              let e := ex.[cu] in
              let d := if e <? r then e else r in
              let tbl1 := tbl.[cu * n + v <- r - d] in
              let tbl2 := tbl1.[v * n + cu <- tbl1.[v * n + cu] + d] in
              let ev := ex.[v] in
              let ex1 := ex.[cu <- e - d] in
              let ex2 := ex1.[v <- ev + d] in
              let b := (ev =? 0) && negb (v =? t) && negb (v =? s) && (ql <? n) in
              let q1 := if b then q.[enq_pos qh ql n <- v] else q in
              let ql1 := if b then ql + 1 else ql in
              let cu1 := if e - d =? 0 then n else cu in
              mloop n s t tbl2 ex2 h cur cnt q1 qh ql1 cu1 rl
                (Acc_inv H (step_push n s t tbl ex h cur cnt q qh ql cu rl H1 H2 H3))
          | right H3 =>
              mloop n s t tbl ex h (cur.[cu <- v + 1]) cnt q qh ql cu rl
                (Acc_inv H (step_adv n s t tbl ex h cur cnt q qh ql cu rl H1 H2 H3))
          end
      | right H2 =>
          let oh := h.[cu] in
          let nh := rmin tbl n cu h 0 n (wf0 n 0) in
          let h1 := h.[cu <- nh] in
          let cur1 := cur.[cu <- 0] in
          let co := cnt.[oh] - 1 in
          let cnt1 := cnt.[oh <- co] in
          let cnt2 := cnt1.[nh <- cnt1.[nh] + 1] in
          let g := (co =? 0) && (0 <? oh) && (oh <? n) && no_height h1 n oh 0 (wf0 n 0) in
          let cnt3 := if g then cnt_lift h1 cnt2 n oh 0 (wf0 n 0) else cnt2 in
          let h2 := if g then lift h1 n oh else h1 in
          let rl1 := rl + 1 in
          let gl := n <=? rl1 in
          let h3 := if gl then glob tbl n t h2 else h2 in
          let cur2 := if gl then PArray.make n 0 else cur1 in
          let cnt4 := if gl then count h3 n else cnt3 in
          let rl2 := if gl then 0 else rl1 in
          let cu1 := if h3.[cu] <? n then cu else n in
          mloop n s t tbl ex h3 cur2 cnt4 q qh ql cu1 rl2
            (Acc_inv H (step_rel n s t tbl ex h cur cnt q qh ql cu rl H1 H2))
      end
  | right H1 =>
      match bdec (0 <? ql) with
      | left H4 =>
          let v := q.[qh] in
          let qh1 := if qh + 1 =? n then 0 else qh + 1 in
          let cu1 := if (v <? n) && active ex h n s t v then v else n in
          mloop n s t tbl ex h cur cnt q qh1 (ql - 1) cu1 rl
            (Acc_inv H (step_pop n s t tbl ex h cur cnt q qh ql cu rl H1 H4))
      | right H4 =>
          let v := find_act ex h n s t 0 (wf0 n 0) in
          match bdec (v <? n) with
          | left H5 =>
              mloop n s t tbl ex h cur cnt q qh ql v rl
                (Acc_inv H (step_scan n s t tbl ex h cur cnt q qh ql cu rl H1 H4 H5))
          | right _ => ex.[t]
          end
      end
  end.
Elpi complexity mloop.

(* ------------------------------------------------------------------ *)
(* Initial state                                                       *)
(* ------------------------------------------------------------------ *)

Definition nn (x : array int) : int := PArray.length x.
Elpi complexity nn.
Definition ss (x : array int) : int := amin x (nn x) 1 0 (wf0 (nn x) 1).
Elpi complexity ss.
Definition tt (x : array int) : int := amax x (nn x) 1 0 (wf0 (nn x) 1).
Elpi complexity tt.

Definition guard (x : array int) : bool :=
  (2 <=? nn x) && (nn x <=? 1000) && rng_ok x (nn x) 0 (wf0 (nn x) 0) && negb (ss x =? tt x).
Elpi complexity guard.

Definition init_state (x : array int) : st :=
  let n := nn x in
  let s := ss x in
  let t := tt x in
  let tbl0 := fill_tab x n (PArray.make (n * n) 0) 0 (wf0 n 0) in
  let p := sat n s t tbl0 (PArray.make n 0) (PArray.make n 0) 0 0 (wf0 n 0) in
  let h0 := (PArray.make n 0).[s <- n] in
  let h1 := glob (fst (fst (fst p))) n t h0 in
  mkst (fst (fst (fst p))) (snd (fst (fst p))) h1 (PArray.make n 0) (count h1 n)
       (snd (fst p)) 0 (snd p) n 0.
Elpi complexity init_state.

(* ================================================================== *)
(* Proofs                                                              *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma aget_make : forall (n : int) (b : int) (i : int), (PArray.make n b).[i] = b.
Proof. intros. exact (get_make int b n i). Qed.

Lemma alength_make_small : forall (n b : int), ((φ n) <= 4194303)%Z ->
  PArray.length (PArray.make n b) = n.
Proof.
  intros n b H. rewrite alength_make.
  replace (n <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Lemma ltb_true : forall a b : int, (a <? b) = true <-> ((φ a) < (φ b))%Z.
Proof. intros. apply ltb_spec. Qed.

Lemma ltb_false : forall a b : int, (a <? b) = false <-> ((φ b) <= (φ a))%Z.
Proof.
  intros. rewrite <- Bool.not_true_iff_false, ltb_spec. lia.
Qed.

Lemma eqb_true : forall a b : int, (a =? b) = true <-> a = b.
Proof. intros. apply eqb_spec. Qed.

Lemma eqb_false : forall a b : int, (a =? b) = false <-> a <> b.
Proof. intros. apply eqb_false_spec. Qed.

Lemma leb_true : forall a b : int, (a <=? b) = true <-> ((φ a) <= (φ b))%Z.
Proof. intros. apply leb_spec. Qed.

Lemma leb_false : forall a b : int, (a <=? b) = false <-> ((φ b) < (φ a))%Z.
Proof. intros. rewrite <- Bool.not_true_iff_false, leb_spec. lia. Qed.

Lemma int_neq : forall a b : int, (φ a) <> (φ b) -> a <> b.
Proof. intros a b H E. apply H. rewrite E. reflexivity. Qed.

Lemma int_eq : forall a b : int, (φ a) = (φ b) -> a = b.
Proof. intros a b H. apply to_Z_inj. exact H. Qed.

Ltac bnorm :=
  repeat match goal with
  | H : (_ <? _) = true |- _ => apply ltb_true in H
  | H : (_ <? _) = false |- _ => apply ltb_false in H
  | H : (_ <=? _) = true |- _ => apply leb_true in H
  | H : (_ <=? _) = false |- _ => apply leb_false in H
  | H : (_ =? _) = true |- _ => apply eqb_true in H
  | H : (_ =? _) = false |- _ => apply eqb_false in H
  | H : (_ && _) = true |- _ => apply andb_true_iff in H; destruct H
  | H : negb _ = true |- _ => apply negb_true_iff in H
  end.

Ltac bcase e := let E := fresh "E" in destruct e eqn:E; bnorm.

Ltac bnd x := pose proof (to_Z_bounded x).

(* ------------------------------------------------------------------ *)
(* Unfolding lemmas                                                    *)
(* ------------------------------------------------------------------ *)

Lemma gcd_loop_eq : forall a b H, gcd_loop a b H =
  match bdec (b =? 0) with
  | left _ => a
  | right Hb => gcd_loop b (a mod b) (Acc_inv H (gcd_dec a b Hb))
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma fill_row_eq : forall x n i tbl j H, fill_row x n i tbl j H =
  match bdec (j <? n) with
  | left Hj =>
      let c := capf x i j in
      fill_row x n i (tbl.[i * n + j <- c].[j * n + i <- c]) (j + 1)
        (Acc_inv H (dec_step n j Hj))
  | right _ => tbl
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma fill_tab_eq : forall x n tbl i H, fill_tab x n tbl i H =
  match bdec (i <? n) with
  | left Hi =>
      fill_tab x n (fill_row x n i tbl i (wf0 n i)) (i + 1)
        (Acc_inv H (dec_step n i Hi))
  | right _ => tbl
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma amin_eq : forall x n i best H, amin x n i best H =
  match bdec (i <? n) with
  | left Hi => amin x n (i + 1) (if x.[i] <? x.[best] then i else best)
                 (Acc_inv H (dec_step n i Hi))
  | right _ => best
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma amax_eq : forall x n i best H, amax x n i best H =
  match bdec (i <? n) with
  | left Hi => amax x n (i + 1) (if x.[best] <? x.[i] then i else best)
                 (Acc_inv H (dec_step n i Hi))
  | right _ => best
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma rng_ok_eq : forall x n i H, rng_ok x n i H =
  match bdec (i <? n) with
  | left Hi => if (2 <=? x.[i]) && (x.[i] <=? 2000000000)
               then rng_ok x n (i + 1) (Acc_inv H (dec_step n i Hi)) else false
  | right _ => true
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma sat_eq : forall n s t tbl ex q ql v H, sat n s t tbl ex q ql v H =
  match bdec (v <? n) with
  | left Hv =>
      let c := tbl.[s * n + v] in
      let tbl1 := tbl.[s * n + v <- 0] in
      let tbl2 := tbl1.[v * n + s <- tbl1.[v * n + s] + c] in
      let ex1 := ex.[v <- c] in
      let b := (0 <? c) && negb (v =? t) && negb (v =? s) in
      let q1 := if b then q.[ql <- v] else q in
      let ql1 := if b then ql + 1 else ql in
      sat n s t tbl2 ex1 q1 ql1 (v + 1) (Acc_inv H (dec_step n v Hv))
  | right _ => (tbl, ex, q, ql)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma amap_eq : forall F a i m H, amap F a i m H =
  match bdec (i <? m) with
  | left Hi =>
      let o := a.[i] in
      let w := F i o in
      amap F (if w =? o then a else a.[i <- w]) (i + 1) m (Acc_inv H (dec_step m i Hi))
  | right _ => a
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma has_val_eq : forall d n L j H, has_val d n L j H =
  match bdec (j <? n) with
  | left Hj => if d.[j] =? L then true else has_val d n L (j + 1) (Acc_inv H (dec_step n j Hj))
  | right _ => false
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma lscan_eq : forall tbl n L d j H, lscan tbl n L d j H =
  match bdec (j <? n) with
  | left Hj =>
      lscan tbl n L
        (if d.[j] =? L then amap (relaxF tbl n j (L + 1)) d 0 n (wf0 n 0) else d)
        (j + 1) (Acc_inv H (dec_step n j Hj))
  | right _ => d
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma layers_eq : forall tbl n L d H, layers tbl n L d H =
  match bdec (L <? n) with
  | left HL =>
      if has_val d n L 0 (wf0 n 0)
      then layers tbl n (L + 1) (lscan tbl n L d 0 (wf0 n 0)) (Acc_inv H (dec_step n L HL))
      else d
  | right _ => d
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma rmin_eq : forall tbl n u h b acc H, rmin tbl n u h b acc H =
  match bdec (b <? n) with
  | left Hb =>
      rmin tbl n u h (b + 1)
        (if (0 <? tbl.[u * n + b]) && (h.[b] + 1 <? acc) then h.[b] + 1 else acc)
        (Acc_inv H (dec_step n b Hb))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma no_height_eq : forall h n k i H, no_height h n k i H =
  match bdec (i <? n) with
  | left Hi => if h.[i] =? k then false else no_height h n k (i + 1) (Acc_inv H (dec_step n i Hi))
  | right _ => true
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma find_act_eq : forall ex h n s t i H, find_act ex h n s t i H =
  match bdec (i <? n) with
  | left Hi => if active ex h n s t i then i
               else find_act ex h n s t (i + 1) (Acc_inv H (dec_step n i Hi))
  | right _ => n
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Loop specifications                                                 *)
(* ------------------------------------------------------------------ *)

Lemma succ_lt : forall i m : int, ((φ i) < (φ m))%Z -> (φ (i + 1)) = ((φ i) + 1)%Z.
Proof. intros i m H. bnd m. sia. Qed.

Lemma gcd_loop_spec : forall (z : Z) a b H, (φ b) = z ->
  (φ (gcd_loop a b H)) = Z.gcd (φ a) (φ b).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros a b H Hz. rewrite gcd_loop_eq.
  destruct (bdec (b =? 0)) as [Hb | Hb].
  - bnorm. subst b. change (φ 0) with 0%Z. rewrite Z.gcd_0_r.
    bnd a. rewrite Z.abs_eq by lia. reflexivity.
  - rewrite (IH (φ (a mod b))); [ | rewrite <- Hz; apply gcd_dec; exact Hb | reflexivity].
    bnorm. assert ((φ b) <> 0%Z) by (intro E; apply Hb, int_eq; exact E).
    rewrite mod_spec. rewrite Z.gcd_comm, Z.gcd_mod by exact H0. apply Z.gcd_comm.
Qed.

Lemma igcd_spec : forall a b, (φ (igcd a b)) = Z.gcd (φ a) (φ b).
Proof. intros. unfold igcd. apply (gcd_loop_spec (φ b)). reflexivity. Qed.

Lemma capf_sym : forall x i j, capf x i j = capf x j i.
Proof.
  intros x i j. unfold capf.
  assert (E : igcd x.[i] x.[j] = igcd x.[j] x.[i])
    by (apply int_eq; rewrite !igcd_spec; apply Z.gcd_comm).
  rewrite E. destruct (i =? j) eqn:E1, (j =? i) eqn:E2; bnorm; try reflexivity;
    subst; congruence.
Qed.

Lemma capf_diag : forall x i, capf x i i = 0.
Proof. intros. unfold capf. rewrite eqb_refl. reflexivity. Qed.

Lemma capf_le : forall x i j, (0 < (φ (x.[i])))%Z -> ((φ (capf x i j)) <= (φ (x.[i])))%Z.
Proof.
  intros x i j Hp. unfold capf. bnd (x.[i]). bnd (x.[j]).
  destruct (i =? j); [change (φ 0) with 0%Z; lia|].
  destruct (1 <? igcd x.[i] x.[j]) eqn:E; bnorm; [|change (φ 0) with 0%Z; lia].
  rewrite igcd_spec in *.
  apply Z.divide_pos_le; [lia|]. apply Z.gcd_divide_l.
Qed.

Ltac gind z IH := induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).

Lemma amap_spec : forall F m (z : Z) i a H, gap m i = z ->
  ((φ m) <= (φ (PArray.length a)))%Z ->
  PArray.length (amap F a i m H) = PArray.length a /\
  forall y, (amap F a i m H).[y] =
    if (((φ i) <=? (φ y))%Z && ((φ y) <? (φ m))%Z)%bool then F y a.[y] else a.[y].
Proof.
  intros F m z. gind z IH. intros i a H Hz Hl.
  rewrite amap_eq. destruct (bdec (i <? m)) as [Hi | Hi].
  - cbv zeta. pose proof Hi as Hi'. bnorm. pose proof (succ_lt i m Hi') as Hs.
    set (a' := if F i a.[i] =? a.[i] then a else a.[i <- F i a.[i]]).
    assert (La : PArray.length a' = PArray.length a)
      by (unfold a'; destruct (F i a.[i] =? a.[i]); [|apply alength_set]; reflexivity).
    assert (Ga : forall y, a'.[y] = if y =? i then F i a.[i] else a.[y]).
    { intros y. unfold a'. destruct (y =? i) eqn:Ey; bnorm.
      - subst y. destruct (F i a.[i] =? a.[i]) eqn:E; bnorm; [congruence|].
        apply aget_set_same. apply ltb_true. lia.
      - destruct (F i a.[i] =? a.[i]); [reflexivity|]. apply aget_set_other. congruence. }
    destruct (IH (gap m (i + 1))) with (i := i + 1) (a := a') (H := Acc_inv H (dec_step m i Hi))
      as [L1 G1]; [rewrite <- Hz; apply dec_step; exact Hi | reflexivity | rewrite La; exact Hl |].
    split; [rewrite L1; exact La|].
    intros y. rewrite G1, !Ga. rewrite Hs.
    destruct (y =? i) eqn:Ey; bnorm.
    + subst y. replace (((φ i) + 1 <=? (φ i))%Z) with false by lia.
      replace (((φ i) <=? (φ i))%Z && ((φ i) <? (φ m))%Z)%bool with true by lia. reflexivity.
    + assert ((φ y) <> (φ i)) by (intro E; apply Ey, int_eq; exact E).
      destruct (((φ i) + 1 <=? (φ y))%Z) eqn:E1, (((φ i) <=? (φ y))%Z) eqn:E2;
        try (simpl; reflexivity); lia.
  - split; [reflexivity|]. intros y. bnorm.
    destruct (((φ i) <=? (φ y))%Z && ((φ y) <? (φ m))%Z)%bool eqn:E; [|reflexivity].
    lia.
Qed.

Lemma has_val_false : forall d n L (z : Z) j H, gap n j = z ->
  has_val d n L j H = false -> forall y, ((φ j) <= (φ y) < (φ n))%Z -> d.[y] <> L.
Proof.
  intros d n L z. gind z IH. intros j H Hz Hf y Hy.
  rewrite has_val_eq in Hf. destruct (bdec (j <? n)) as [Hj | Hj].
  - destruct (d.[j] =? L) eqn:E; [discriminate|]. apply eqb_false in E.
    pose proof (proj1 (ltb_true _ _) Hj) as Hj'. pose proof (succ_lt j n Hj') as Hs.
    destruct (Z.eq_dec (φ y) (φ j)) as [Ey|Ey].
    + apply int_eq in Ey. subst. exact E.
    + eapply IH; [ | reflexivity | exact Hf | lia]. rewrite <- Hz. apply dec_step. exact Hj.
  - bnorm. lia.
Qed.

Lemma no_height_true : forall h n k (z : Z) i H, gap n i = z ->
  no_height h n k i H = true -> forall y, ((φ i) <= (φ y) < (φ n))%Z -> h.[y] <> k.
Proof.
  intros h n k z. gind z IH. intros i H Hz Hf y Hy.
  rewrite no_height_eq in Hf. destruct (bdec (i <? n)) as [Hj | Hj].
  - destruct (h.[i] =? k) eqn:E; [discriminate|]. apply eqb_false in E.
    pose proof (proj1 (ltb_true _ _) Hj) as Hj'. pose proof (succ_lt i n Hj') as Hs.
    destruct (Z.eq_dec (φ y) (φ i)) as [Ey|Ey].
    + apply int_eq in Ey. subst. exact E.
    + eapply IH; [ | reflexivity | exact Hf | lia]. rewrite <- Hz. apply dec_step. exact Hj.
  - bnorm. lia.
Qed.

Lemma find_act_spec : forall ex h n s t (z : Z) i H, gap n i = z ->
  (((φ (find_act ex h n s t i H)) < (φ n))%Z -> active ex h n s t (find_act ex h n s t i H) = true) /\
  (((φ n) <= (φ (find_act ex h n s t i H)))%Z ->
     forall y, ((φ i) <= (φ y) < (φ n))%Z -> active ex h n s t y = false).
Proof.
  intros ex h n s t z. gind z IH. intros i H Hz.
  rewrite find_act_eq. destruct (bdec (i <? n)) as [Hj | Hj].
  - destruct (active ex h n s t i) eqn:E.
    + split; [intros; exact E|]. intros Hn. bnorm. lia.
    + pose proof Hj as Hj'. bnorm. pose proof (succ_lt i n Hj') as Hs.
      destruct (IH (gap n (i + 1))) with (i := i + 1) (H := Acc_inv H (dec_step n i Hj))
        as [A B]; [rewrite <- Hz; apply dec_step; exact Hj | reflexivity |].
      split; [exact A|]. intros Hn y Hy.
      destruct (Z.eq_dec (φ y) (φ i)) as [Ey|Ey].
      * apply int_eq in Ey. subst. exact E.
      * apply B; [exact Hn | lia].
  - bnorm. split; [lia|]. intros _ y Hy. lia.
Qed.

Lemma rmin_spec : forall tbl n u h,
  ((φ n) <= 4194303)%Z ->
  (forall y, ((φ y) < (φ n))%Z -> ((φ (h.[y])) <= (φ n))%Z) ->
  forall (z : Z) b acc H, gap n b = z ->
  ((φ acc) <= (φ n))%Z ->
  (forall b', ((φ b') < (φ b))%Z -> ((φ b') < (φ n))%Z -> (0 < (φ (tbl.[u * n + b'])))%Z ->
     ((φ acc) <= (φ (h.[b'])) + 1)%Z) ->
  ((φ acc) = (φ n) \/ exists b', ((φ b') < (φ n))%Z /\ (0 < (φ (tbl.[u * n + b'])))%Z /\
     (φ acc) = ((φ (h.[b'])) + 1)%Z) ->
  let r := rmin tbl n u h b acc H in
  ((φ r) <= (φ n))%Z /\
  (forall b', ((φ b') < (φ n))%Z -> (0 < (φ (tbl.[u * n + b'])))%Z -> ((φ r) <= (φ (h.[b'])) + 1)%Z) /\
  ((φ r) = (φ n) \/ exists b', ((φ b') < (φ n))%Z /\ (0 < (φ (tbl.[u * n + b'])))%Z /\
     (φ r) = ((φ (h.[b'])) + 1)%Z).
Proof.
  intros tbl n u h Hn Hh z. gind z IH. intros b acc H Hz Ha Hlo Hw. cbv zeta.
  rewrite rmin_eq. destruct (bdec (b <? n)) as [Hb | Hb].
  - pose proof Hb as Hb'. bnorm. pose proof (succ_lt b n Hb') as Hs.
    pose proof (Hh b Hb') as Hhb.
    assert (Hp : (φ (h.[b] + 1)) = ((φ (h.[b])) + 1)%Z) by (bnd (h.[b]); sia).
    apply (IH (gap n (b + 1))); [rewrite <- Hz; apply dec_step; exact Hb | reflexivity | | | ].
    + destruct ((0 <? tbl.[u * n + b]) && (h.[b] + 1 <? acc)) eqn:E; bnorm; lia.
    + intros b' Hb1 Hb2 Hr. rewrite Hs in Hb1.
      destruct ((0 <? tbl.[u * n + b]) && (h.[b] + 1 <? acc)) eqn:E.
      * bnorm. destruct (Z.eq_dec (φ b') (φ b)) as [Eb|Eb].
        -- apply int_eq in Eb; subst; lia.
        -- specialize (Hlo b' ltac:(lia) Hb2 Hr). lia.
      * destruct (Z.eq_dec (φ b') (φ b)) as [Eb|Eb].
        -- apply int_eq in Eb; subst b'.
           apply andb_false_iff in E. destruct E as [E|E]; bnorm.
           ++ change (φ 0) with 0%Z in E. lia.
           ++ lia.
        -- apply Hlo; auto. lia.
    + destruct ((0 <? tbl.[u * n + b]) && (h.[b] + 1 <? acc)) eqn:E; [|exact Hw].
      bnorm. right. exists b. split; [exact Hb'|]. split; [change (φ 0) with 0%Z in *; lia|]. exact Hp.
  - bnorm. split; [exact Ha|]. split; [|exact Hw].
    intros b' Hb1 Hr. apply Hlo; auto. lia.
Qed.

Lemma amin_spec : forall x n (z : Z) i best H, gap n i = z ->
  ((φ best) < (φ n))%Z ->
  (forall j, ((φ j) < (φ i))%Z -> ((φ j) < (φ n))%Z -> ((φ (x.[best])) <= (φ (x.[j])))%Z) ->
  ((φ (amin x n i best H)) < (φ n))%Z /\
  forall j, ((φ j) < (φ n))%Z -> ((φ (x.[amin x n i best H])) <= (φ (x.[j])))%Z.
Proof.
  intros x n z. gind z IH. intros i best H Hz Hb Hlo.
  rewrite amin_eq. destruct (bdec (i <? n)) as [Hi | Hi].
  - pose proof Hi as Hi'. bnorm. pose proof (succ_lt i n Hi') as Hs.
    apply (IH (gap n (i + 1))); [rewrite <- Hz; apply dec_step; exact Hi | reflexivity | | ].
    + destruct (x.[i] <? x.[best]); assumption.
    + intros j Hj1 Hj2. rewrite Hs in Hj1.
      destruct (x.[i] <? x.[best]) eqn:E; bnorm;
        (destruct (Z.eq_dec (φ j) (φ i)) as [Ej|Ej];
         [apply int_eq in Ej; subst; lia | specialize (Hlo j ltac:(lia) Hj2); lia]).
  - bnorm. split; [exact Hb|]. intros j Hj. apply Hlo; lia.
Qed.

Lemma amax_spec : forall x n (z : Z) i best H, gap n i = z ->
  ((φ best) < (φ n))%Z ->
  (forall j, ((φ j) < (φ i))%Z -> ((φ j) < (φ n))%Z -> ((φ (x.[j])) <= (φ (x.[best])))%Z) ->
  ((φ (amax x n i best H)) < (φ n))%Z /\
  forall j, ((φ j) < (φ n))%Z -> ((φ (x.[j])) <= (φ (x.[amax x n i best H])))%Z.
Proof.
  intros x n z. gind z IH. intros i best H Hz Hb Hlo.
  rewrite amax_eq. destruct (bdec (i <? n)) as [Hi | Hi].
  - pose proof Hi as Hi'. bnorm. pose proof (succ_lt i n Hi') as Hs.
    apply (IH (gap n (i + 1))); [rewrite <- Hz; apply dec_step; exact Hi | reflexivity | | ].
    + destruct (x.[best] <? x.[i]); assumption.
    + intros j Hj1 Hj2. rewrite Hs in Hj1.
      destruct (x.[best] <? x.[i]) eqn:E; bnorm;
        (destruct (Z.eq_dec (φ j) (φ i)) as [Ej|Ej];
         [apply int_eq in Ej; subst; lia | specialize (Hlo j ltac:(lia) Hj2); lia]).
  - bnorm. split; [exact Hb|]. intros j Hj. apply Hlo; lia.
Qed.

Lemma rng_ok_sound : forall x n (z : Z) i H, gap n i = z -> rng_ok x n i H = true ->
  forall j, ((φ i) <= (φ j) < (φ n))%Z -> (2 <= (φ (x.[j])) <= 2000000000)%Z.
Proof.
  intros x n z. gind z IH. intros i H Hz Hr j Hj.
  rewrite rng_ok_eq in Hr. destruct (bdec (i <? n)) as [Hi | Hi].
  - destruct ((2 <=? x.[i]) && (x.[i] <=? 2000000000)) eqn:E; [|discriminate].
    pose proof Hi as Hi'. bnorm. pose proof (succ_lt i n Hi') as Hs.
    destruct (Z.eq_dec (φ j) (φ i)) as [Ej|Ej].
    + apply int_eq in Ej. subst. change (φ 2) with 2%Z in *.
      change (φ 2000000000) with 2000000000%Z in *. lia.
    + eapply IH; [ | reflexivity | exact Hr | lia]. rewrite <- Hz. apply dec_step. exact Hi.
  - bnorm. lia.
Qed.

Lemma rng_ok_complete : forall x n (z : Z) i H, gap n i = z ->
  (forall j, ((φ i) <= (φ j) < (φ n))%Z -> (2 <= (φ (x.[j])) <= 2000000000)%Z) ->
  rng_ok x n i H = true.
Proof.
  intros x n z. gind z IH. intros i H Hz Hr.
  rewrite rng_ok_eq. destruct (bdec (i <? n)) as [Hi | Hi]; [|reflexivity].
  pose proof Hi as Hi'. bnorm. pose proof (succ_lt i n Hi') as Hs.
  destruct (Hr i ltac:(lia)) as [A B].
  replace ((2 <=? x.[i]) && (x.[i] <=? 2000000000)) with true
    by (symmetry; apply andb_true_iff; split; apply leb_true; assumption).
  eapply IH; [ | reflexivity | ]. rewrite <- Hz. apply dec_step. exact Hi.
  intros j Hj. apply Hr. lia.
Qed.

Lemma get_set2 : forall (tbl : array int) p q c d y,
  ((φ p) < (φ (PArray.length tbl)))%Z -> ((φ q) < (φ (PArray.length tbl)))%Z ->
  (tbl.[p <- c].[q <- d]).[y] = if y =? q then d else if y =? p then c else tbl.[y].
Proof.
  intros tbl p q c d y Hp Hq.
  destruct (y =? q) eqn:E1; bnorm.
  - subst y. apply aget_set_same. rewrite alength_set. apply ltb_true. exact Hq.
  - rewrite aget_set_other by congruence.
    destruct (y =? p) eqn:E2; bnorm.
    + subst y. apply aget_set_same. apply ltb_true. exact Hp.
    + apply aget_set_other. congruence.
Qed.

Lemma get_set1 : forall (tbl : array int) p c y,
  ((φ p) < (φ (PArray.length tbl)))%Z ->
  (tbl.[p <- c]).[y] = if y =? p then c else tbl.[y].
Proof.
  intros tbl p c y Hp. destruct (y =? p) eqn:E; bnorm.
  - subst. apply aget_set_same. apply ltb_true. exact Hp.
  - apply aget_set_other. congruence.
Qed.

Lemma idx_inj_Z : forall N a b c d : Z, (0 <= b < N)%Z -> (0 <= d < N)%Z ->
  (a * N + b = c * N + d)%Z -> a = c /\ b = d.
Proof.
  intros N a b c d Hb Hd E.
  assert (A : ((a * N + b) / N = a)%Z).
  { rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
  assert (C : ((c * N + d) / N = c)%Z).
  { rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
  rewrite E in A. split; lia.
Qed.

Section Tables.

Variable n : int.
Hypothesis Hn : (2 <= (φ n) <= 1000)%Z.

Definition RD (tbl : array int) (a b : int) : Z := (φ (tbl.[a * n + b])).

Lemma idx_spec : forall a b, ((φ a) < (φ n))%Z -> ((φ b) < (φ n))%Z ->
  (φ (a * n + b)) = ((φ a) * (φ n) + (φ b))%Z.
Proof.
  intros a b Ha Hb. bnd a. bnd b.
  rewrite add_spec, mul_spec. rewrite (Z.mod_small ((φ a) * (φ n))) by (rewrite wB_val; nia).
  apply Z.mod_small. rewrite wB_val. nia.
Qed.

Lemma idx_lt : forall a b, ((φ a) < (φ n))%Z -> ((φ b) < (φ n))%Z ->
  ((φ (a * n + b)) < (φ n) * (φ n))%Z.
Proof. intros a b Ha Hb. rewrite idx_spec by assumption. bnd b. nia. Qed.

Lemma idx_eq_iff : forall a b c d, ((φ a) < (φ n))%Z -> ((φ b) < (φ n))%Z ->
  ((φ c) < (φ n))%Z -> ((φ d) < (φ n))%Z ->
  (a * n + b = c * n + d) <-> (a = c /\ b = d).
Proof.
  intros a b c d Ha Hb Hc Hd. split.
  - intros E. apply (f_equal to_Z) in E. rewrite !idx_spec in E by assumption.
    bnd b. bnd d. apply idx_inj_Z in E; [|lia|lia]. destruct E as [E1 E2].
    split; apply int_eq; assumption.
  - intros [E1 E2]. subst. reflexivity.
Qed.

Lemma nn_spec : (φ (n * n)) = ((φ n) * (φ n))%Z.
Proof. rewrite mul_spec. apply Z.mod_small. rewrite wB_val. nia. Qed.

Lemma make_nn : forall b : int, PArray.length (PArray.make (n * n) b) = n * n.
Proof. intros. apply alength_make_small. rewrite nn_spec. nia. Qed.

Lemma make_n : forall b : int, PArray.length (PArray.make n b) = n.
Proof. intros. apply alength_make_small. lia. Qed.

Variable x : array int.

Definition cov (i j a b : int) : Prop :=
  ((φ a) < (φ i) \/ (φ b) < (φ i) \/ ((φ a) = (φ i) /\ (φ b) < (φ j)) \/ ((φ b) = (φ i) /\ (φ a) < (φ j)))%Z.

Definition tab_ok (i j : int) (tbl : array int) : Prop :=
  PArray.length tbl = n * n /\
  forall a b, ((φ a) < (φ n))%Z -> ((φ b) < (φ n))%Z ->
    (cov i j a b -> tbl.[a * n + b] = capf x a b) /\
    (~ cov i j a b -> tbl.[a * n + b] = 0).

Lemma fill_row_spec : forall i, ((φ i) < (φ n))%Z ->
  forall (z : Z) j tbl H, gap n j = z -> ((φ i) <= (φ j))%Z -> tab_ok i j tbl ->
  tab_ok i n (fill_row x n i tbl j H).
Proof.
  intros i Hi z. gind z IH. intros j tbl H Hz Hij [Hl Hc].
  rewrite fill_row_eq. destruct (bdec (j <? n)) as [Hj | Hj].
  - cbv zeta. pose proof Hj as Hj'. bnorm. pose proof (succ_lt j n Hj') as Hs.
    apply (IH (gap n (j + 1))); [rewrite <- Hz; apply dec_step; exact Hj | reflexivity | lia |].
    assert (L1 : ((φ (i * n + j)) < (φ (PArray.length tbl)))%Z)
      by (rewrite Hl, nn_spec; apply idx_lt; lia).
    assert (L2 : ((φ (j * n + i)) < (φ (PArray.length tbl)))%Z)
      by (rewrite Hl, nn_spec; apply idx_lt; lia).
    split; [rewrite !alength_set; exact Hl|].
    intros a b Ha Hb. rewrite get_set2 by assumption.
    destruct (a * n + b =? j * n + i) eqn:E1; bnorm.
    + apply idx_eq_iff in E1; try lia. destruct E1; subst a b.
      split; [intros _; apply capf_sym|]. intros C; exfalso; apply C; unfold cov; lia.
    + destruct (a * n + b =? i * n + j) eqn:E2; bnorm.
      * apply idx_eq_iff in E2; try lia. destruct E2; subst a b.
        split; [intros _; reflexivity|]. intros C; exfalso; apply C; unfold cov; lia.
      * assert (N1 : ~ (a = j /\ b = i)) by (rewrite <- idx_eq_iff; try lia; exact E1).
        assert (N2 : ~ (a = i /\ b = j)) by (rewrite <- idx_eq_iff; try lia; exact E2).
        assert (N1' : ~ ((φ a) = (φ j) /\ (φ b) = (φ i)))
          by (intros [A B]; apply N1; split; apply int_eq; assumption).
        assert (N2' : ~ ((φ a) = (φ i) /\ (φ b) = (φ j)))
          by (intros [A B]; apply N2; split; apply int_eq; assumption).
        destruct (Hc a b Ha Hb) as [C1 C2].
        split; intros C; [apply C1 | apply C2]; unfold cov in *; rewrite Hs in *; lia.
  - bnorm. split; [exact Hl|]. intros a b Ha Hb. destruct (Hc a b Ha Hb) as [C1 C2].
    split; intros C; [apply C1 | apply C2]; unfold cov in *; lia.
Qed.

Lemma fill_tab_spec : forall (z : Z) i tbl H, gap n i = z -> ((φ i) <= (φ n))%Z ->
  tab_ok i i tbl -> tab_ok n n (fill_tab x n tbl i H).
Proof.
  intros z. gind z IH. intros i tbl H Hz Hin Ht.
  rewrite fill_tab_eq. destruct (bdec (i <? n)) as [Hi | Hi].
  - pose proof Hi as Hi'. bnorm. pose proof (succ_lt i n Hi') as Hs.
    apply (IH (gap n (i + 1))); [rewrite <- Hz; apply dec_step; exact Hi | reflexivity | lia |].
    pose proof (fill_row_spec i Hi' _ i tbl (wf0 n i) eq_refl ltac:(lia) Ht) as [Hl Hc].
    split; [exact Hl|]. intros a b Ha Hb. destruct (Hc a b Ha Hb) as [C1 C2].
    split; intros C; [apply C1 | apply C2]; unfold cov in *; rewrite Hs in *; lia.
  - bnorm. replace i with n in Ht by (apply int_eq; lia). exact Ht.
Qed.

Lemma table_spec :
  let tbl := fill_tab x n (PArray.make (n * n) 0) 0 (wf0 n 0) in
  PArray.length tbl = n * n /\
  forall a b, ((φ a) < (φ n))%Z -> ((φ b) < (φ n))%Z -> tbl.[a * n + b] = capf x a b.
Proof.
  cbv zeta.
  destruct (fill_tab_spec _ 0 (PArray.make (n * n) 0) (wf0 n 0) eq_refl
              ltac:(change (φ 0) with 0%Z; lia)) as [Hl Hc].
  - split; [apply make_nn|]. intros a b Ha Hb. split.
    + intros C. unfold cov in C. change (φ 0) with 0%Z in C. bnd a; bnd b; lia.
    + intros _. apply aget_make.
  - split; [exact Hl|]. intros a b Ha Hb. apply (Hc a b Ha Hb). unfold cov. lia.
Qed.

End Tables.

(* ------------------------------------------------------------------ *)
(* Finite sums                                                         *)
(* ------------------------------------------------------------------ *)

Fixpoint zsum (f : nat -> Z) (k : nat) : Z :=
  match k with O => 0%Z | S k => (zsum f k + f k)%Z end.

Section Zsum.
Local Open Scope Z_scope.

Lemma zsum_ext : forall f g k, (forall i, (i < k)%nat -> f i = g i) -> zsum f k = zsum g k.
Proof.
  intros f g k. induction k as [|k IH]; intros E; simpl; [reflexivity|].
  rewrite IH by (intros; apply E; lia). rewrite E by lia. reflexivity.
Qed.

Lemma zsum_add : forall f g k, zsum (fun i => f i + g i) k = zsum f k + zsum g k.
Proof. intros f g k. induction k; simpl; lia. Qed.

Lemma zsum_sub : forall f g k, zsum (fun i => f i - g i) k = zsum f k - zsum g k.
Proof. intros f g k. induction k; simpl; lia. Qed.

Lemma zsum_opp : forall f k, zsum (fun i => - f i) k = - zsum f k.
Proof. intros f k. induction k; simpl; lia. Qed.

Lemma zsum_zero : forall f k, (forall i, (i < k)%nat -> f i = 0) -> zsum f k = 0.
Proof.
  intros f k. induction k as [|k IH]; intros E; simpl; [reflexivity|].
  rewrite IH by (intros; apply E; lia). rewrite E by lia. reflexivity.
Qed.

Lemma zsum_le : forall f g k, (forall i, (i < k)%nat -> f i <= g i) -> zsum f k <= zsum g k.
Proof.
  intros f g k. induction k as [|k IH]; intros E; simpl; [lia|].
  specialize (IH ltac:(intros; apply E; lia)). specialize (E k ltac:(lia)). lia.
Qed.

Lemma zsum_nonneg : forall f k, (forall i, (i < k)%nat -> 0 <= f i) -> 0 <= zsum f k.
Proof.
  intros f k. induction k as [|k IH]; intros E; cbn [zsum]; [lia|].
  specialize (IH ltac:(intros; apply E; lia)). specialize (E k ltac:(lia)). lia.
Qed.

Lemma zsum_single : forall p a k, (p < k)%nat ->
  zsum (fun i => if Nat.eqb i p then a else 0) k = a.
Proof.
  intros p a k. induction k as [|k IH]; intros Hp; [lia|]. simpl.
  destruct (Nat.eqb_spec k p).
  - subst. rewrite zsum_zero; [lia|]. intros i Hi.
    destruct (Nat.eqb_spec i p); [lia|reflexivity].
  - rewrite IH by lia. lia.
Qed.

Lemma zsum_swap : forall (F : nat -> nat -> Z) k m,
  zsum (fun i => zsum (fun j => F i j) m) k = zsum (fun j => zsum (fun i => F i j) k) m.
Proof.
  intros F k. induction k as [|k IH]; intros m; simpl.
  - symmetry. apply zsum_zero. intros. reflexivity.
  - rewrite IH. rewrite <- zsum_add. reflexivity.
Qed.

Lemma zsum_pos : forall f k, 0 < zsum f k -> exists i, (i < k)%nat /\ 0 < f i.
Proof.
  intros f k. induction k as [|k IH]; simpl; intros H; [lia|].
  destruct (Z_lt_le_dec 0 (f k)) as [P|P].
  - exists k. split; [lia|exact P].
  - destruct IH as [i [Hi Pi]]; [lia|]. exists i. split; [lia|exact Pi].
Qed.

Lemma zsum_split : forall (p : nat -> bool) f k,
  zsum f k = zsum (fun i => if p i then f i else 0) k + zsum (fun i => if p i then 0 else f i) k.
Proof.
  intros p f k. rewrite <- zsum_add. apply zsum_ext. intros i _. destruct (p i); lia.
Qed.

Lemma zsum_antisym : forall (g : nat -> nat -> Z) k,
  (forall a b, (a < k)%nat -> (b < k)%nat -> g a b = - g b a) ->
  zsum (fun v => zsum (fun a => g a v) k) k = 0.
Proof.
  intros g k E.
  assert (A : zsum (fun v => zsum (fun a => g a v) k) k
            = - zsum (fun v => zsum (fun a => g a v) k) k).
  { rewrite zsum_swap at 1. rewrite <- zsum_opp. apply zsum_ext. intros i Hi.
    rewrite <- zsum_opp. apply zsum_ext. intros j Hj. apply E; assumption. }
  lia.
Qed.

Lemma zsum_bound : forall f k c, (forall i, (i < k)%nat -> f i <= c) -> zsum f k <= Z.of_nat k * c.
Proof.
  intros f k c. induction k as [|k IH]; intros E; cbn [zsum]; [lia|].
  specialize (IH ltac:(intros; apply E; lia)). specialize (E k ltac:(lia)).
  rewrite Nat2Z.inj_succ. nia.
Qed.

Lemma zsum_point : forall f g p k, (p < k)%nat ->
  (forall i, (i < k)%nat -> i <> p -> f i = g i) ->
  zsum f k = zsum g k + (f p - g p).
Proof.
  intros f g p k Hp E.
  assert (zsum (fun i => f i - g i) k = f p - g p).
  { rewrite <- (zsum_single p (f p - g p) k Hp). apply zsum_ext. intros i Hi.
    destruct (Nat.eqb_spec i p); [subst; reflexivity|]. rewrite E by assumption. lia. }
  rewrite zsum_sub in H. lia.
Qed.

End Zsum.

Lemma dec_exists_lt : forall (P : nat -> Prop), (forall v, P v \/ ~ P v) ->
  forall k, (exists v, (v < k)%nat /\ P v) \/ (forall v, (v < k)%nat -> ~ P v).
Proof.
  intros P D k. induction k as [|k IH].
  - right. intros; lia.
  - destruct IH as [[v [Hv Pv]] | N].
    + left. exists v. split; [lia|exact Pv].
    + destruct (D k) as [Pk|Pk].
      * left. exists k. split; [lia|exact Pk].
      * right. intros v Hv. destruct (Nat.eq_dec v k); [subst; exact Pk|]. apply N. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Max-flow min-cut for the final preflow                              *)
(* ------------------------------------------------------------------ *)

Section Flow.
Local Open Scope Z_scope.

Variable N : nat.
Variables s t : nat.
Hypothesis Hs : (s < N)%nat.
Hypothesis Ht : (t < N)%nat.
Hypothesis Hst : s <> t.
Variable c : nat -> nat -> Z.
Hypothesis c_nonneg : forall a b, 0 <= c a b.
Hypothesis c_sym : forall a b, c a b = c b a.
Variable r : nat -> nat -> Z.
Hypothesis r_nonneg : forall a b, (a < N)%nat -> (b < N)%nat -> 0 <= r a b.
Hypothesis r_sym : forall a b, (a < N)%nat -> (b < N)%nat -> r a b + r b a = 2 * c a b.
Variable e : nat -> Z.
Hypothesis e_def : forall v, (v < N)%nat -> v <> s -> e v = zsum (fun a => c a v - r a v) N.
Hypothesis e_nonneg : forall v, (v < N)%nat -> v <> s -> 0 <= e v.
Variable h : nat -> Z.
Hypothesis h_valid : forall a b, (a < N)%nat -> (b < N)%nat -> 0 < r a b -> h a <= h b + 1.
Hypothesis h_s : h s = Z.of_nat N.
Hypothesis h_t : h t = 0.
Hypothesis final : forall v, (v < N)%nat -> v <> s -> v <> t -> 0 < e v -> Z.of_nat N <= h v.
Hypothesis r_t : forall x, (x < N)%nat -> c t x <= r t x.

Definition walk (w : nat -> nat -> Z) : Prop :=
  (forall a b, (a < N)%nat -> (b < N)%nat -> 0 <= w a b <= c a b) /\
  (forall v, (v < N)%nat -> v <> s -> v <> t -> zsum (fun b => w v b) N = zsum (fun b => w b v) N).

Definition wvalue (w : nat -> nat -> Z) : Z := zsum (fun b => w s b) N - zsum (fun b => w b s) N.

(* some height strictly between 0 and N is taken by no vertex *)
Lemma pigeon : exists k, 1 <= k <= Z.of_nat N - 1 /\ forall v, (v < N)%nat -> h v <> k.
Proof.
  destruct (dec_exists_lt (fun k => (forall v, (v < N)%nat -> h v <> Z.of_nat (S k))))
             with (k := (N - 1)%nat) as [[k [Hk P]] | NP].
  - intros k. destruct (dec_exists_lt (fun v => h v = Z.of_nat (S k)) (fun v => Z.eq_decidable (h v) (Z.of_nat (S k))) N)
      as [[v [Hv P]] | P].
    + right. intros A. apply (A v Hv). exact P.
    + left. exact P.
  - exists (Z.of_nat (S k)). split; [lia|exact P].
  - exfalso.
    assert (Hin : forall k, (k < N - 1)%nat -> exists v, (v < N)%nat /\ h v = Z.of_nat (S k)).
    { intros k Hk. specialize (NP k Hk).
      destruct (dec_exists_lt (fun v => h v = Z.of_nat (S k)) (fun v => Z.eq_decidable (h v) (Z.of_nat (S k))) N)
        as [E | E]; [exact E|]. exfalso. apply NP. exact E. }
    set (l := Z.of_nat N :: 0 :: map (fun k => Z.of_nat (S k)) (seq 0 (N - 1))).
    assert (ND : NoDup l).
    { unfold l. constructor; [|constructor].
      - intros [A|A]; [lia|]. apply in_map_iff in A. destruct A as [k [Ek Ik]].
        apply in_seq in Ik. lia.
      - intros A. apply in_map_iff in A. destruct A as [k [Ek Ik]]. lia.
      - apply NoDup_map_NoDup_ForallPairs; [intros a b _ _ E; lia|]. apply seq_NoDup. }
    assert (IN : incl l (map h (seq 0 N))).
    { intros y Hy. apply in_map_iff. unfold l in Hy. destruct Hy as [Hy|[Hy|Hy]].
      - exists s. split; [lia|]. apply in_seq. lia.
      - exists t. split; [lia|]. apply in_seq. lia.
      - apply in_map_iff in Hy. destruct Hy as [k [Ek Ik]]. apply in_seq in Ik.
        destruct (Hin k ltac:(lia)) as [v [Hv Ev]]. exists v. split; [lia|]. apply in_seq. lia. }
    pose proof (NoDup_incl_length ND IN) as LL.
    unfold l in LL. simpl in LL. rewrite length_map, length_seq, length_map, length_seq in LL.
    assert (N >= 2)%nat.
    { destruct (Nat.eq_dec N 0); [lia|]. destruct (Nat.eq_dec N 1); [|lia]. subst. lia. }
    lia.
Qed.

Section Cut.
Variable k : Z.
Hypothesis Hk : 1 <= k <= Z.of_nat N - 1.
Hypothesis Hgap : forall v, (v < N)%nat -> h v <> k.

Definition inS (v : nat) : bool := Z.ltb k (h v).

Lemma cut_sat : forall a b, (a < N)%nat -> (b < N)%nat -> inS a = true -> inS b = false -> r a b = 0.
Proof.
  intros a b Ha Hb A B. unfold inS in *. apply Z.ltb_lt in A. apply Z.ltb_ge in B.
  pose proof (Hgap b Hb). pose proof (r_nonneg a b Ha Hb).
  destruct (Z.eq_dec (r a b) 0) as [E|E]; [exact E|].
  pose proof (h_valid a b Ha Hb ltac:(lia)). lia.
Qed.

Lemma inS_s : inS s = true.
Proof. unfold inS. apply Z.ltb_lt. lia. Qed.

Lemma inS_t : inS t = false.
Proof. unfold inS. apply Z.ltb_ge. lia. Qed.

Definition cutcap : Z :=
  zsum (fun b => if inS b then 0 else zsum (fun a => if inS a then c a b else 0) N) N.

Lemma et_cut : e t = cutcap.
Proof.
  assert (E1 : e t = zsum (fun v => if inS v then 0 else e v) N).
  { rewrite <- (zsum_single t (e t) N Ht). apply zsum_ext. intros v Hv.
    destruct (Nat.eqb_spec v t).
    - subst. rewrite inS_t. reflexivity.
    - destruct (inS v) eqn:Sv; [reflexivity|].
      assert (v <> s) by (intro; subst; rewrite inS_s in Sv; discriminate).
      pose proof (e_nonneg v Hv H). 
      destruct (Z.eq_dec (e v) 0) as [Z0|Z0]; [lia|].
      pose proof (final v Hv H n ltac:(lia)). unfold inS in Sv. apply Z.ltb_ge in Sv. lia. }
  rewrite E1.
  set (g := fun a v => if inS v then 0 else if inS a then 0 else c a v - r a v).
  assert (E2 : zsum (fun v => if inS v then 0 else e v) N
             = zsum (fun v => zsum (fun a => g a v) N) N + cutcap).
  { unfold cutcap. rewrite <- zsum_add. apply zsum_ext. intros v Hv.
    unfold g. destruct (inS v) eqn:Sv.
    - rewrite zsum_zero by (intros; reflexivity). reflexivity.
    - assert (v <> s) by (intro; subst; rewrite inS_s in Sv; discriminate).
      rewrite e_def by assumption. rewrite <- zsum_add. apply zsum_ext. intros a Ha.
      destruct (inS a) eqn:Sa; [|lia]. rewrite cut_sat by assumption. lia. }
  rewrite E2. rewrite zsum_antisym; [lia|].
  intros a b Ha Hb. unfold g. destruct (inS a), (inS b); try lia.
  pose proof (r_sym a b Ha Hb). rewrite (c_sym b a). lia.
Qed.

Lemma walk_cut : forall w, walk w -> wvalue w <= cutcap.
Proof.
  intros w [Wc Wk].
  assert (E1 : wvalue w = zsum (fun a => if inS a then
                 zsum (fun b => w a b) N - zsum (fun b => w b a) N else 0) N).
  { unfold wvalue. rewrite <- (zsum_single s _ N Hs). apply zsum_ext. intros a Ha.
    destruct (Nat.eqb_spec a s).
    - subst. rewrite inS_s. reflexivity.
    - destruct (inS a) eqn:Sa; [|reflexivity].
      assert (a <> t) by (intro; subst; rewrite inS_t in Sa; discriminate).
      rewrite (Wk a Ha n H). lia. }
  set (g := fun b a => if inS a then if inS b then w a b - w b a else 0 else 0).
  assert (E2 : zsum (fun a => if inS a then
                 zsum (fun b => w a b) N - zsum (fun b => w b a) N else 0) N
             = zsum (fun a => zsum (fun b => g b a) N) N +
               zsum (fun a => if inS a then zsum (fun b => if inS b then 0 else w a b - w b a) N else 0) N).
  { rewrite <- zsum_add. apply zsum_ext. intros a Ha. unfold g.
    destruct (inS a).
    - rewrite <- zsum_sub, <- zsum_add. apply zsum_ext. intros b Hb. destruct (inS b); lia.
    - rewrite zsum_zero by (intros; reflexivity). lia. }
  rewrite E1, E2, zsum_antisym.
  2:{ intros a b Ha Hb. unfold g. destruct (inS a), (inS b); lia. }
  assert (E3 : cutcap = zsum (fun a => zsum (fun b =>
                 if inS b then 0 else if inS a then c a b else 0) N) N).
  { unfold cutcap. rewrite zsum_swap. apply zsum_ext. intros b Hb.
    destruct (inS b); [|reflexivity]. rewrite zsum_zero by (intros; reflexivity). reflexivity. }
  rewrite E3. apply zsum_le. intros a Ha.
  destruct (inS a) eqn:Sa.
  - apply zsum_le. intros b Hb. destruct (inS b); [lia|].
    destruct (Wc a b Ha Hb). destruct (Wc b a Hb Ha). lia.
  - apply zsum_nonneg. intros b Hb. destruct (inS b); [lia|]. lia.
Qed.

End Cut.

Theorem flow_upper : forall w, walk w -> wvalue w <= e t.
Proof.
  intros w W. destruct pigeon as [k [Hk Hg]].
  rewrite (et_cut k Hk Hg). apply walk_cut; assumption.
Qed.

(* the stranded excess of the preflow goes back, one unit at a time *)
Definition exs (g : nat -> nat -> Z) (v : nat) : Z := zsum (fun a => g a v) N.

Definition gok (g : nat -> nat -> Z) : Prop :=
  (forall a b, (a < N)%nat -> (b < N)%nat -> g a b = - g b a) /\
  (forall a b, (a < N)%nat -> (b < N)%nat -> g a b <= c a b) /\
  (forall v, (v < N)%nat -> v <> s -> 0 <= exs g v) /\
  (forall x, (x < N)%nat -> g t x <= 0).

Definition pos_mass (g : nat -> nat -> Z) : Z :=
  zsum (fun a => zsum (fun b => Z.max (g a b) 0) N) N.

Definition ind2 (u v a b : nat) : Z := if (Nat.eqb a u && Nat.eqb b v)%bool then 1 else 0.

Lemma zsum_ind2_col : forall u v x, (u < N)%nat ->
  zsum (fun a => ind2 u v a x) N = if Nat.eqb x v then 1 else 0.
Proof.
  intros u v x Hu. unfold ind2. destruct (Nat.eqb_spec x v).
  - subst x. rewrite (zsum_ext _ (fun a => if Nat.eqb a u then 1 else 0)).
    + apply zsum_single. exact Hu.
    + intros a Ha. rewrite andb_true_r. reflexivity.
  - apply zsum_zero. intros a Ha. destruct (Nat.eqb a u); simpl; [|reflexivity].
    replace (Nat.eqb x v) with false by (symmetry; apply Nat.eqb_neq; assumption). reflexivity.
Qed.

Lemma cancel : forall (m : Z) g, pos_mass g = m -> gok g ->
  exists g', gok g' /\ (forall v, (v < N)%nat -> v <> s -> v <> t -> exs g' v = 0) /\
             exs g' t = exs g t.
Proof.
  intros m. induction m as [m IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros g Hm Hg.
  destruct (dec_exists_lt (fun v => v <> s /\ v <> t /\ exs g v <> 0)) with (k := N)
    as [[v [Hv [Vs [Vt Ve]]]] | NE].
  - intros v. destruct (Nat.eq_dec v s), (Nat.eq_dec v t), (Z.eq_dec (exs g v) 0);
      first [right; tauto | left; tauto].
  - destruct Hg as [G1 [G2 [G3 G4]]].
    assert (Pv : 0 < exs g v) by (specialize (G3 v Hv Vs); lia).
    destruct (zsum_pos _ _ Pv) as [u [Hu Pu]].
    assert (Ut : u <> t) by (intro; subst; specialize (G4 v Hv); lia).
    assert (Uv : u <> v) by (intro; subst; specialize (G1 v v Hv Hv); lia).
    set (g' := fun a b => g a b - ind2 u v a b + ind2 v u a b).
    assert (Ex : forall x, (x < N)%nat ->
              exs g' x = exs g x - (if Nat.eqb x v then 1 else 0) + (if Nat.eqb x u then 1 else 0)).
    { intros x Hx. unfold exs, g'. rewrite zsum_add, zsum_sub.
      rewrite (zsum_ind2_col u v x Hu), (zsum_ind2_col v u x Hv). reflexivity. }
    assert (Hg' : gok g').
    { split; [|split; [|split]].
      - intros a b Ha Hb. unfold g', ind2. rewrite (G1 a b Ha Hb).
        destruct (Nat.eqb_spec a u), (Nat.eqb_spec b v), (Nat.eqb_spec a v), (Nat.eqb_spec b u);
          simpl; subst; try lia.
      - intros a b Ha Hb. unfold g', ind2. pose proof (G2 a b Ha Hb). pose proof (c_nonneg a b).
        destruct (Nat.eqb_spec a u), (Nat.eqb_spec b v), (Nat.eqb_spec a v), (Nat.eqb_spec b u);
          simpl; subst; try lia.
        rewrite (G1 v u Hv Hu). lia.
      - intros x Hx Xs. rewrite (Ex x Hx). pose proof (G3 x Hx Xs).
        destruct (Nat.eqb_spec x v), (Nat.eqb_spec x u); subst; lia.
      - intros y Hy. unfold g', ind2. pose proof (G4 y Hy).
        destruct (Nat.eqb_spec t u), (Nat.eqb_spec t v); simpl; try lia; congruence. }
    assert (Pm : pos_mass g' = pos_mass g - 1).
    { unfold pos_mass.
      assert (A : forall a b, (a < N)%nat -> (b < N)%nat ->
                Z.max (g' a b) 0 = Z.max (g a b) 0 - ind2 u v a b).
      { intros a b Ha Hb. unfold g', ind2.
        destruct (Nat.eqb_spec a u), (Nat.eqb_spec b v), (Nat.eqb_spec a v), (Nat.eqb_spec b u);
          simpl; subst; try lia.
        rewrite (G1 v u Hv Hu). lia. }
      rewrite (zsum_ext _ (fun a => zsum (fun b => Z.max (g a b) 0) N - zsum (fun b => ind2 u v a b) N) N).
      2:{ intros a Ha. rewrite <- zsum_sub. apply zsum_ext. intros b Hb. apply A; assumption. }
      rewrite zsum_sub, (zsum_swap (ind2 u v)).
      rewrite (zsum_ext (fun j => zsum (fun i => ind2 u v i j) N) (fun b => if Nat.eqb b v then 1 else 0) N)
        by (intros b Hb; apply zsum_ind2_col; exact Hu).
      rewrite zsum_single by exact Hv. lia. }
    assert (M0 : 0 <= pos_mass g').
    { apply zsum_nonneg. intros a _. apply zsum_nonneg. intros b _. lia. }
    destruct (IH (pos_mass g')) with (g := g') as [g2 [A [B C]]];
      [unfold Zwf; lia | reflexivity | exact Hg' |].
    exists g2. split; [exact A|]. split; [exact B|].
    rewrite C, (Ex t Ht).
    destruct (Nat.eqb_spec t v), (Nat.eqb_spec t u); subst; try congruence. lia.
  - exists g. split; [exact Hg|]. split; [|reflexivity].
    intros v Hv Vs Vt. destruct (Z.eq_dec (exs g v) 0) as [E|E]; [exact E|].
    exfalso. apply (NE v Hv). tauto.
Qed.

Theorem flow_exists : exists w, walk w /\ wvalue w = e t.
Proof.
  set (g0 := fun a b => c a b - r a b).
  assert (G0 : gok g0).
  { split; [|split; [|split]].
    - intros a b Ha Hb. unfold g0. pose proof (r_sym a b Ha Hb). rewrite (c_sym b a). lia.
    - intros a b Ha Hb. unfold g0. pose proof (r_nonneg a b Ha Hb). lia.
    - intros v Hv Vs. unfold exs, g0. rewrite <- e_def by assumption. apply e_nonneg; assumption.
    - intros y Hy. unfold g0. pose proof (r_t y Hy). lia. }
  assert (Et : exs g0 t = e t) by (unfold exs, g0; symmetry; apply e_def; [exact Ht | congruence]).
  destruct (cancel _ g0 eq_refl G0) as [g [[G1 [G2 [G3 G4]]] [Z0 Zt]]].
  exists (fun a b => Z.max (g a b) 0).
  assert (Cons : forall v, (v < N)%nat ->
            zsum (fun b => Z.max (g v b) 0) N - zsum (fun b => Z.max (g b v) 0) N = - exs g v).
  { intros v Hv. unfold exs. rewrite <- zsum_sub, <- zsum_opp. apply zsum_ext. intros b Hb.
    rewrite (G1 b v Hb Hv). lia. }
  split; [split|].
  - intros a b Ha Hb. pose proof (G2 a b Ha Hb). pose proof (c_nonneg a b). lia.
  - intros v Hv Vs Vt. pose proof (Cons v Hv). rewrite (Z0 v Hv Vs Vt) in H. lia.
  - unfold wvalue. rewrite (Cons s Hs).
    assert (T : zsum (fun v => exs g v) N = 0)
      by (unfold exs; apply zsum_antisym; intros; apply G1; assumption).
    rewrite (zsum_ext _ (fun v => (if Nat.eqb v s then exs g s else 0) +
                                  (if Nat.eqb v t then exs g t else 0)) N) in T.
    2:{ intros v Hv. destruct (Nat.eqb_spec v s), (Nat.eqb_spec v t); subst; try congruence; try lia.
        rewrite (Z0 v Hv n n0). lia. }
    rewrite zsum_add, !zsum_single in T by assumption. lia.
Qed.

End Flow.

(* ------------------------------------------------------------------ *)
(* The machine invariant                                               *)
(* ------------------------------------------------------------------ *)

Definition io (k : nat) : int := of_Z (Z.of_nat k).

Lemma io_spec : forall k, (Z.of_nat k < wB)%Z -> (φ (io k)) = Z.of_nat k.
Proof. intros k H. unfold io. rewrite of_Z_spec. apply Z.mod_small. lia. Qed.

Lemma sub_nowrap : forall a b : int, ((φ b) <= (φ a))%Z -> (φ (a - b)) = ((φ a) - (φ b))%Z.
Proof. intros a b H. rewrite sub_spec. apply Z.mod_small. bnd a. bnd b. lia. Qed.

Lemma add_nowrap : forall a b : int, ((φ a) + (φ b) < wB)%Z -> (φ (a + b)) = ((φ a) + (φ b))%Z.
Proof. intros a b H. rewrite add_spec. apply Z.mod_small. bnd a. bnd b. lia. Qed.

Section Machine.

Variables (n s t : int) (cp : int -> int -> Z).
Hypothesis Hn : (2 <= (φ n) <= 1000)%Z.
Hypothesis Hs : ((φ s) < (φ n))%Z.
Hypothesis Ht : ((φ t) < (φ n))%Z.
Hypothesis Hst : s <> t.
Hypothesis cp_sym : forall a b, cp a b = cp b a.
Hypothesis cp_rng : forall a b, (0 <= cp a b <= 2147483648)%Z.
Hypothesis cp_diag : forall a, cp a a = 0%Z.

Local Notation Nn := (Z.to_nat (φ n)).
Local Notation lt a := ((φ a) < (φ n))%Z.
Local Notation RD := (RD n).

Lemma io_lt : forall k, (k < Nn)%nat -> (φ (io k)) = Z.of_nat k /\ lt (io k).
Proof. intros k Hk. rewrite io_spec by (rewrite wB_val; lia). split; lia. Qed.

Lemma io_to : forall u, (0 <= (φ u))%Z -> io (Z.to_nat (φ u)) = u.
Proof.
  intros u H. apply int_eq. rewrite io_spec by (bnd u; rewrite Z2Nat.id by lia; lia).
  apply Z2Nat.id. exact H.
Qed.

Definition isum (F : int -> Z) : Z := zsum (fun k => F (io k)) Nn.

Lemma isum_ext : forall F G, (forall y, lt y -> F y = G y) -> isum F = isum G.
Proof.
  intros F G E. unfold isum. apply zsum_ext. intros k Hk. apply E. apply io_lt. exact Hk.
Qed.

Lemma isum_le : forall F G, (forall y, lt y -> (F y <= G y)%Z) -> (isum F <= isum G)%Z.
Proof.
  intros F G E. unfold isum. apply zsum_le. intros k Hk. apply E. apply io_lt. exact Hk.
Qed.

Lemma isum_nonneg : forall F, (forall y, lt y -> (0 <= F y)%Z) -> (0 <= isum F)%Z.
Proof.
  intros F E. unfold isum. apply zsum_nonneg. intros k Hk. apply E. apply io_lt. exact Hk.
Qed.

Lemma isum_bound : forall F c, (forall y, lt y -> (F y <= c)%Z) -> (isum F <= (φ n) * c)%Z.
Proof.
  intros F c E. unfold isum.
  pose proof (zsum_bound (fun k => F (io k)) Nn c) as B.
  assert (X : Z.of_nat Nn = (φ n)) by lia. rewrite X in B. apply B.
  intros k Hk. apply E. apply io_lt. exact Hk.
Qed.

Lemma isum_point : forall F G u, lt u -> (forall y, lt y -> y <> u -> F y = G y) ->
  isum F = (isum G + (F u - G u))%Z.
Proof.
  intros F G u Hu E. unfold isum. bnd u.
  assert (P : (Z.to_nat (φ u) < Nn)%nat) by lia.
  pose proof (zsum_point (fun k => F (io k)) (fun k => G (io k)) _ Nn P) as Z1.
  cbv beta in Z1. rewrite io_to in Z1 by lia. apply Z1.
  intros k Hk Hne. apply E; [apply io_lt; exact Hk|].
  intro X. apply Hne. subst u. destruct (io_lt k Hk) as [A _]. lia.
Qed.

Lemma isum_point2 : forall F G u v, lt u -> lt v -> u <> v ->
  (forall y, lt y -> y <> u -> y <> v -> F y = G y) ->
  isum F = (isum G + (F u - G u) + (F v - G v))%Z.
Proof.
  intros F G u v Hu Hv Huv E.
  set (M := fun y => if y =? v then G v else F y).
  rewrite (isum_point F M v Hv).
  2:{ intros y Hy Hne. unfold M. replace (y =? v) with false by (symmetry; apply eqb_false; exact Hne).
      reflexivity. }
  rewrite (isum_point M G u Hu).
  2:{ intros y Hy Hne. unfold M. destruct (y =? v) eqn:Ev; bnorm; [subst; reflexivity|].
      apply E; assumption. }
  unfold M. rewrite eqb_refl. replace (u =? v) with false by (symmetry; apply eqb_false; exact Huv).
  lia.
Qed.


Definition colsum (tbl : array int) (v : int) : Z := isum (fun a => (cp a v - RD tbl a v)%Z).

Record TabOK (tbl ex : array int) : Prop := {
  t_ltbl : PArray.length tbl = n * n;
  t_lex : PArray.length ex = n;
  t_sym : forall a b, lt a -> lt b -> (RD tbl a b + RD tbl b a = 2 * cp a b)%Z;
  t_ex : forall v, lt v -> v <> s -> (φ (ex.[v])) = colsum tbl v;
  t_t : forall x, lt x -> (cp t x <= RD tbl t x)%Z }.

Record HOK (tbl h : array int) : Prop := {
  h_len : PArray.length h = n;
  h_valid : forall a b, lt a -> lt b -> (0 < RD tbl a b)%Z -> ((φ (h.[a])) <= (φ (h.[b])) + 1)%Z;
  h_s : (φ (h.[s])) = (φ n);
  h_t : (φ (h.[t])) = 0%Z;
  h_le : forall v, lt v -> ((φ (h.[v])) <= (φ n))%Z }.

Record COK (tbl h cur : array int) : Prop := {
  c_len : PArray.length cur = n;
  c_le : forall v, lt v -> ((φ (cur.[v])) <= (φ n))%Z;
  c_arc : forall u, lt u -> ((φ (h.[u])) < (φ n))%Z -> forall b, ((φ b) < (φ (cur.[u])))%Z ->
            ~ ((0 < RD tbl u b)%Z /\ (φ (h.[u])) = ((φ (h.[b])) + 1)%Z) }.

Definition UOK (ex h : array int) (cu : int) : Prop :=
  lt cu -> (0 < (φ (ex.[cu])))%Z /\ ((φ (h.[cu])) < (φ n))%Z /\ cu <> s /\ cu <> t.

Definition Inv (S : st) : Prop :=
  TabOK (s_tbl S) (s_ex S) /\ HOK (s_tbl S) (s_h S) /\ COK (s_tbl S) (s_h S) (s_cur S) /\
  UOK (s_ex S) (s_h S) (s_cu S).

Lemma RD_bound : forall tbl ex a b, TabOK tbl ex -> lt a -> lt b ->
  (0 <= RD tbl a b <= 2 * cp a b)%Z.
Proof.
  intros tbl ex a b T Ha Hb. pose proof (t_sym _ _ T a b Ha Hb).
  unfold RD in *. bnd (tbl.[a * n + b]). bnd (tbl.[b * n + a]). lia.
Qed.

Lemma ex_bound : forall tbl ex u v, TabOK tbl ex -> lt u -> lt v -> v <> s ->
  ((φ (ex.[v])) + RD tbl u v <= (φ n) * 2147483648)%Z.
Proof.
  intros tbl ex u v T Hu Hv Vs. rewrite (t_ex _ _ T v Hv Vs). unfold colsum.
  rewrite (isum_point _ (fun a => if a =? u then cp u v else (cp a v - RD tbl a v)%Z) u Hu).
  2:{ intros y Hy Hne. replace (y =? u) with false by (symmetry; apply eqb_false; exact Hne). reflexivity. }
  rewrite eqb_refl.
  assert (isum (fun a => if Uint63.eqb a u then cp u v else (cp a v - RD tbl a v)%Z) <= (φ n) * 2147483648)%Z.
  { apply isum_bound. intros y Hy. destruct (y =? u) eqn:E; bnorm.
    - subst. pose proof (cp_rng u v). lia.
    - pose proof (cp_rng y v). pose proof (RD_bound tbl ex y v T Hy Hv). lia. }
  lia.
Qed.

Definition ind (b : bool) (z : Z) : Z := if b then z else 0%Z.

Lemma push_tab : forall tbl ex u v d tbl1 tbl2 ex1 ex2,
  TabOK tbl ex -> lt u -> lt v -> u <> v -> u <> s -> v <> s -> u <> t ->
  (0 < (φ d))%Z -> ((φ d) <= RD tbl u v)%Z -> ((φ d) <= (φ (ex.[u])))%Z ->
  tbl1 = tbl.[u * n + v <- tbl.[u * n + v] - d] ->
  tbl2 = tbl1.[v * n + u <- tbl1.[v * n + u] + d] ->
  ex1 = ex.[u <- ex.[u] - d] -> ex2 = ex1.[v <- ex.[v] + d] ->
  TabOK tbl2 ex2 /\
  (forall a b, lt a -> lt b -> RD tbl2 a b =
     (RD tbl a b - ind (Uint63.eqb a u && Uint63.eqb b v) (φ d) + ind (Uint63.eqb a v && Uint63.eqb b u) (φ d))%Z) /\
  (forall y, (φ (ex2.[y])) = ((φ (ex.[y])) - ind (Uint63.eqb y u) (φ d) + ind (Uint63.eqb y v) (φ d))%Z).
Proof.
  intros tbl ex u v d tbl1 tbl2 ex1 ex2 T Hu Hv Huv Us Vs Ut Hd0 Hd1 Hd2 E1 E2 E3 E4.
  pose proof (t_ltbl _ _ T) as Lt. pose proof (t_lex _ _ T) as Le.
  assert (Pp : ((φ (u * n + v)) < (φ (PArray.length tbl)))%Z) by (rewrite Lt, nn_spec by lia; apply idx_lt; lia).
  assert (Pq : ((φ (v * n + u)) < (φ (PArray.length tbl)))%Z) by (rewrite Lt, nn_spec by lia; apply idx_lt; lia).
  assert (Npq : u * n + v <> v * n + u).
  { intro X. apply idx_eq_iff in X; [destruct X; congruence|lia..]. }
  assert (G1 : tbl1.[v * n + u] = tbl.[v * n + u]) by (subst tbl1; apply aget_set_other; exact Npq).
  assert (V1 : (φ (tbl.[u * n + v] - d)) = (RD tbl u v - (φ d))%Z) by (apply sub_nowrap; exact Hd1).
  pose proof (t_sym _ _ T u v Hu Hv) as Suv. pose proof (cp_rng u v) as Cuv.
  pose proof (RD_bound tbl ex u v T Hu Hv). pose proof (RD_bound tbl ex v u T Hv Hu).
  assert (V2 : (φ (tbl1.[v * n + u] + d)) = (RD tbl v u + (φ d))%Z).
  { rewrite G1. apply add_nowrap. unfold RD in *. rewrite wB_val. lia. }
  assert (RDf : forall a b, lt a -> lt b -> RD tbl2 a b =
     (RD tbl a b - ind (Uint63.eqb a u && Uint63.eqb b v) (φ d) + ind (Uint63.eqb a v && Uint63.eqb b u) (φ d))%Z).
  { intros a b Ha Hb. unfold RD at 1. subst tbl2 tbl1.
    rewrite get_set2 by assumption.
    destruct (a * n + b =? v * n + u) eqn:Q1; bnorm.
    - apply idx_eq_iff in Q1; [|lia..]. destruct Q1; subst a b. rewrite V2. unfold ind.
      rewrite !eqb_refl. replace (v =? u) with false by (symmetry; apply eqb_false; congruence).
      simpl. lia.
    - destruct (a * n + b =? u * n + v) eqn:Q2; bnorm.
      + apply idx_eq_iff in Q2; [|lia..]. destruct Q2; subst a b. rewrite V1. unfold ind.
        rewrite !eqb_refl. replace (u =? v) with false by (symmetry; apply eqb_false; congruence).
        simpl. lia.
      + assert (I1 : (Uint63.eqb a u && Uint63.eqb b v) = false).
        { destruct (a =? u) eqn:A1, (b =? v) eqn:B1; bnorm; try reflexivity. subst. congruence. }
        assert (I2 : (Uint63.eqb a v && Uint63.eqb b u) = false).
        { destruct (a =? v) eqn:A1, (b =? u) eqn:B1; bnorm; try reflexivity. subst. congruence. }
        rewrite I1, I2. unfold ind, RD. lia. }
  assert (V3 : (φ (ex.[u] - d)) = ((φ (ex.[u])) - (φ d))%Z) by (apply sub_nowrap; exact Hd2).
  assert (V4 : (φ (ex.[v] + d)) = ((φ (ex.[v])) + (φ d))%Z).
  { apply add_nowrap. pose proof (ex_bound tbl ex u v T Hu Hv Vs). rewrite wB_val. lia. }
  assert (EXf : forall y, (φ (ex2.[y])) = ((φ (ex.[y])) - ind (Uint63.eqb y u) (φ d) + ind (Uint63.eqb y v) (φ d))%Z).
  { intros y. subst ex2 ex1. unfold ind.
    rewrite get_set2 by (apply ltb_true; rewrite Le; lia).
    destruct (y =? v) eqn:Yv, (y =? u) eqn:Yu; bnorm; subst; try congruence; lia. }
  split; [|split; [exact RDf | exact EXf]].
  split.
  - subst. rewrite !alength_set. exact Lt.
  - subst. rewrite !alength_set. exact Le.
  - intros a b Ha Hb. rewrite !RDf by assumption. pose proof (t_sym _ _ T a b Ha Hb) as Sab.
    rewrite (andb_comm (Uint63.eqb b u) (Uint63.eqb a v)), (andb_comm (Uint63.eqb b v) (Uint63.eqb a u)).
    clear - Sab. lia.
  - intros y Hy Ys. rewrite EXf, (t_ex _ _ T y Hy Ys). unfold colsum, ind.
    destruct (y =? u) eqn:Yu, (y =? v) eqn:Yv; bnorm; try (subst y); try congruence.
    + (* y = u: column u changes at row v *)
      rewrite (isum_point (fun a => cp a u - RD tbl a u)%Z (fun a => cp a u - RD tbl2 a u)%Z v Hv).
      2:{ intros a Ha Hne. rewrite RDf by assumption. unfold ind.
          replace (a =? v) with false by (symmetry; apply eqb_false; exact Hne).
          destruct (a =? u); simpl; [|lia]. replace (u =? v) with false by (symmetry; apply eqb_false; congruence). lia. }
      rewrite RDf by assumption. unfold ind. rewrite eqb_refl, eqb_refl.
      replace (v =? u) with false by (symmetry; apply eqb_false; congruence). simpl. lia.
    + rewrite (isum_point (fun a => cp a v - RD tbl a v)%Z (fun a => cp a v - RD tbl2 a v)%Z u Hu).
      2:{ intros a Ha Hne. rewrite RDf by assumption. unfold ind.
          replace (a =? u) with false by (symmetry; apply eqb_false; exact Hne).
          destruct (a =? v); simpl; [|lia]. replace (v =? u) with false by (symmetry; apply eqb_false; congruence). lia. }
      rewrite RDf by assumption. unfold ind. rewrite eqb_refl, eqb_refl.
      replace (u =? v) with false by (symmetry; apply eqb_false; congruence). simpl. lia.
    + rewrite Z.sub_0_r, Z.add_0_r. apply isum_ext. intros a Ha. rewrite RDf by assumption. unfold ind.
      replace (y =? v) with false by (symmetry; apply eqb_false; congruence).
      replace (y =? u) with false by (symmetry; apply eqb_false; congruence).
      rewrite !andb_false_r. lia.
  - intros y Hy. rewrite RDf by assumption. unfold ind.
    replace (t =? u) with false by (symmetry; apply eqb_false; congruence).
    pose proof (t_t _ _ T y Hy). destruct ((t =? v) && (y =? u)); simpl; lia.
Qed.


(* ---- global relabeling ---- *)

Definition Pd (tbl d : array int) (b : int) : Prop :=
  forall a, lt a -> (0 < RD tbl a b)%Z -> ((φ (d.[a])) <= (φ (d.[b])) + 1)%Z.

Lemma relax_spec : forall tbl d j L1, PArray.length d = n ->
  let d' := amap (relaxF tbl n j L1) d 0 n (wf0 n 0) in
  PArray.length d' = n /\
  forall y, lt y -> (φ (d'.[y])) =
    (if ((0 <? (φ (tbl.[y * n + j])))%Z && ((φ L1) <? (φ (d.[y])))%Z)%bool then (φ L1) else (φ (d.[y]))).
Proof.
  intros tbl d j L1 Ld. cbv zeta.
  destruct (amap_spec (relaxF tbl n j L1) n _ 0 d (wf0 n 0) eq_refl ltac:(rewrite Ld; lia)) as [A B].
  split; [rewrite A; exact Ld|]. intros y Hy. rewrite B. bnd y.
  change (φ 0) with 0%Z.
  replace ((0 <=? (φ y))%Z && ((φ y) <? (φ n))%Z)%bool with true by lia.
  unfold relaxF. destruct (0 <? tbl.[y * n + j]) eqn:E1, (L1 <? d.[y]) eqn:E2; bnorm;
    change (φ 0) with 0%Z in *;
    try (replace ((0 <? (φ (tbl.[y * n + j])))%Z) with true by lia);
    try (replace ((0 <? (φ (tbl.[y * n + j])))%Z) with false by lia);
    try (replace (((φ L1) <? (φ (d.[y])))%Z) with true by lia);
    try (replace (((φ L1) <? (φ (d.[y])))%Z) with false by lia); reflexivity.
Qed.

Lemma lscan_spec : forall tbl L, ((φ L) < (φ n))%Z ->
  forall (z : Z) d j H, gap n j = z ->
  PArray.length d = n ->
  (forall x, lt x -> ((φ (d.[x])) <= (φ n))%Z) ->
  (forall x, lt x -> ((φ (d.[x])) <= (φ L) + 1)%Z \/ (φ (d.[x])) = (φ n)) ->
  (forall b, lt b -> (((φ (d.[b])) < (φ L))%Z \/ ((φ (d.[b])) = (φ L) /\ ((φ b) < (φ j))%Z)) -> Pd tbl d b) ->
  (φ (d.[t])) = 0%Z ->
  let d' := lscan tbl n L d j H in
  PArray.length d' = n /\
  (forall x, lt x -> ((φ (d'.[x])) <= (φ n))%Z) /\
  (forall x, lt x -> ((φ (d'.[x])) <= (φ L) + 1)%Z \/ (φ (d'.[x])) = (φ n)) /\
  (forall b, lt b -> ((φ (d'.[b])) <= (φ L))%Z -> Pd tbl d' b) /\
  (φ (d'.[t])) = 0%Z.
Proof.
  intros tbl L HL z. gind z IH. intros d j H Hz Ld B1 B2 B3 Bt. cbv zeta.
  rewrite lscan_eq. destruct (bdec (j <? n)) as [Hj | Hj].
  - pose proof Hj as Hj'. bnorm. pose proof (succ_lt j n Hj') as Hs1.
    assert (HL1 : (φ (L + 1)) = ((φ L) + 1)%Z) by (apply (succ_lt L n HL)).
    apply (IH (gap n (j + 1))); [rewrite <- Hz; apply dec_step; exact Hj | reflexivity | | | | | ].
    all: destruct (d.[j] =? L) eqn:EjL; bnorm.
    all: try (destruct (relax_spec tbl d j (L + 1) Ld) as [R1 R2]; rewrite ?HL1 in R2).
    + exact R1.
    + exact Ld.
    + intros x Hx. rewrite R2 by exact Hx. specialize (B1 x Hx).
      destruct (_ && _)%bool eqn:E; [|lia]. bnorm. lia.
    + exact B1.
    + intros x Hx. rewrite R2 by exact Hx. specialize (B2 x Hx).
      destruct (_ && _)%bool eqn:E; lia.
    + exact B2.
    + (* the frontier vertex j has been relaxed *)
      assert (Keep : forall y, lt y -> ((φ (d.[y])) <= (φ L) + 1)%Z ->
                (φ ((amap (relaxF tbl n j (L + 1)) d 0 n (wf0 n 0)).[y])) = (φ (d.[y]))).
      { intros y Hy Hle. rewrite R2 by exact Hy. destruct (_ && _)%bool eqn:E; [|reflexivity].
        bnorm. lia. }
      assert (Dec : forall y, lt y ->
                ((φ ((amap (relaxF tbl n j (L + 1)) d 0 n (wf0 n 0)).[y])) <= (φ (d.[y])))%Z).
      { intros y Hy. rewrite R2 by exact Hy. destruct (_ && _)%bool eqn:E; bnorm; lia. }
      intros b Hb Cb.
      assert (Db : (φ ((amap (relaxF tbl n j (L + 1)) d 0 n (wf0 n 0)).[b])) = (φ (d.[b]))).
      { apply Keep; [exact Hb|]. pose proof (Dec b Hb). rewrite R2 in Cb by exact Hb.
        destruct (_ && _)%bool eqn:E in Cb; bnorm; lia. }
      rewrite Db in Cb. rewrite Hs1 in Cb.
      destruct (Z.eq_dec (φ b) (φ j)) as [Ebj|Ebj].
      * apply int_eq in Ebj. subst b. intros a Ha Ra. rewrite Db. rewrite EjL.
        rewrite R2 by exact Ha. unfold RD in Ra.
        destruct (_ && _)%bool eqn:E; bnorm; lia.
      * assert (P0 : Pd tbl d b) by (apply B3; [exact Hb | lia]).
        intros a Ha Ra. rewrite Db. pose proof (Dec a Ha). pose proof (P0 a Ha Ra). lia.
    + intros b Hb Cb. apply B3; [exact Hb|]. rewrite Hs1 in Cb.
      destruct Cb as [X|[X Y]]; [left; exact X|].
      destruct (Z.eq_dec (φ b) (φ j)) as [Ebj|Ebj]; [|right; lia].
      apply int_eq in Ebj. subst b. exfalso. apply EjL. apply int_eq. exact X.
    + rewrite R2 by exact Ht. rewrite Bt. destruct (_ && _)%bool eqn:E; bnorm; lia.
    + exact Bt.
  - bnorm. split; [exact Ld|]. split; [exact B1|]. split; [exact B2|]. split; [|exact Bt].
    intros b Hb Cb. apply B3; [exact Hb|]. lia.
Qed.

Definition FinD (tbl d : array int) : Prop :=
  PArray.length d = n /\ (forall x, lt x -> ((φ (d.[x])) <= (φ n))%Z) /\ (φ (d.[t])) = 0%Z /\
  forall a b, lt a -> lt b -> (0 < RD tbl a b)%Z -> ((φ (d.[a])) <= (φ (d.[b])) + 1)%Z.

Lemma layers_spec : forall tbl (z : Z) L d H, gap n L = z -> ((φ L) <= (φ n))%Z ->
  PArray.length d = n ->
  (forall x, lt x -> ((φ (d.[x])) <= (φ n))%Z) ->
  (forall x, lt x -> ((φ (d.[x])) <= (φ L))%Z \/ (φ (d.[x])) = (φ n)) ->
  (forall b, lt b -> ((φ (d.[b])) < (φ L))%Z -> Pd tbl d b) ->
  (φ (d.[t])) = 0%Z ->
  FinD tbl (layers tbl n L d H).
Proof.
  intros tbl z. gind z IH. intros L d H Hz HLn Ld B1 B2 B3 Bt.
  rewrite layers_eq. destruct (bdec (L <? n)) as [HL | HL].
  - pose proof HL as HL'. bnorm. pose proof (succ_lt L n HL') as Hs1.
    destruct (has_val d n L 0 (wf0 n 0)) eqn:Hv.
    + assert (B2' : forall x, lt x -> ((φ (d.[x])) <= (φ L) + 1)%Z \/ (φ (d.[x])) = (φ n))
        by (intros x Hx; specialize (B2 x Hx); lia).
      assert (B3' : forall b, lt b -> (((φ (d.[b])) < (φ L))%Z \/ ((φ (d.[b])) = (φ L) /\ ((φ b) < (φ 0))%Z)) -> Pd tbl d b)
        by (intros b Hb [X|[X Y]]; [apply B3; auto | change (φ 0) with 0%Z in Y; bnd b; lia]).
      destruct (lscan_spec tbl L HL' _ d 0 (wf0 n 0) eq_refl Ld B1 B2' B3' Bt) as [A [B [C [D E]]]].
      apply (IH (gap n (L + 1))); [rewrite <- Hz; apply dec_step; exact HL | reflexivity | lia |
        exact A | exact B | | | exact E].
      * intros x Hx. rewrite Hs1. apply C. exact Hx.
      * intros b Hb Cb. apply D; [exact Hb | lia].
    + pose proof (has_val_false d n L _ 0 (wf0 n 0) eq_refl Hv) as NV.
      split; [exact Ld|]. split; [exact B1|]. split; [exact Bt|].
      intros a b Ha Hb Rab.
      destruct (B2 b Hb) as [X|X]; [|rewrite X; apply B1 in Ha; lia].
      assert ((φ (d.[b])) <> (φ L)).
      { intro Y. apply (NV b); [change (φ 0) with 0%Z; bnd b; lia | apply int_eq; exact Y]. }
      apply (B3 b Hb); [lia | exact Ha | exact Rab].
  - bnorm. split; [exact Ld|]. split; [exact B1|]. split; [exact Bt|].
    intros a b Ha Hb Rab.
    destruct (Z.eq_dec (φ (d.[b])) (φ n)) as [X|X]; [rewrite X; apply B1 in Ha; lia|].
    apply (B3 b Hb); [pose proof (B1 b Hb); lia | exact Ha | exact Rab].
Qed.
Arguments layers_spec : clear implicits.

Lemma bfs_spec : forall tbl, FinD tbl (bfs tbl n t).
Proof.
  intros tbl. unfold bfs.
  assert (L0 : PArray.length (PArray.make n n) = n) by (apply make_n; lia).
  assert (G0 : forall x, (PArray.make n n).[t <- 0].[x] = if x =? t then 0 else n).
  { intros x. rewrite get_set1 by (rewrite L0; exact Ht). rewrite aget_make. reflexivity. }
  apply (layers_spec tbl _ 0 _ (wf0 n 0) eq_refl); change (φ 0) with 0%Z.
  - lia.
  - rewrite alength_set. exact L0.
  - intros x Hx. rewrite G0. destruct (x =? t); change (φ 0) with 0%Z; lia.
  - intros x Hx. rewrite G0. destruct (x =? t); change (φ 0) with 0%Z; lia.
  - intros b Hb Cb. bnd ((PArray.make n n).[t <- 0].[b]). lia.
  - rewrite G0, eqb_refl. reflexivity.
Qed.

Lemma glob_spec : forall tbl h, HOK tbl h ->
  HOK tbl (glob tbl n t h) /\ forall y, lt y -> ((φ (h.[y])) <= (φ ((glob tbl n t h).[y])))%Z.
Proof.
  intros tbl h Hh. destruct (bfs_spec tbl) as [D1 [D2 [D3 D4]]].
  unfold glob. set (d := bfs tbl n t) in *.
  destruct (amap_spec (maxF d) n _ 0 h (wf0 n 0) eq_refl ltac:(rewrite (h_len _ _ Hh); lia))
    as [A B].
  assert (M : forall y, lt y -> (φ ((amap (maxF d) h 0 n (wf0 n 0)).[y])) = Z.max (φ (h.[y])) (φ (d.[y]))).
  { intros y Hy. rewrite B. change (φ 0) with 0%Z. bnd y.
    replace ((0 <=? (φ y))%Z && ((φ y) <? (φ n))%Z)%bool with true by lia.
    unfold maxF. destruct (h.[y] <? d.[y]) eqn:E; bnorm; lia. }
  split.
  - split.
    + rewrite A. exact (h_len _ _ Hh).
    + intros a b Ha Hb Rab. rewrite !M by assumption.
      pose proof (h_valid _ _ Hh a b Ha Hb Rab). pose proof (D4 a b Ha Hb Rab). lia.
    + rewrite M by exact Hs. rewrite (h_s _ _ Hh). pose proof (D2 s Hs). lia.
    + rewrite M by exact Ht. rewrite (h_t _ _ Hh), D3. reflexivity.
    + intros v Hv. rewrite M by exact Hv. pose proof (h_le _ _ Hh v Hv). pose proof (D2 v Hv). lia.
  - intros y Hy. rewrite M by exact Hy. lia.
Qed.


(* ---- gap heuristic ---- *)

Lemma lift_get : forall h k, PArray.length h = n -> forall y, lt y ->
  (φ ((lift h n k).[y])) = (if (((φ k) <? (φ (h.[y])))%Z && ((φ (h.[y])) <? (φ n))%Z)%bool then (φ n) else (φ (h.[y]))).
Proof.
  intros h k Lh y Hy. unfold lift.
  destruct (amap_spec (liftF n k) n _ 0 h (wf0 n 0) eq_refl ltac:(rewrite Lh; lia)) as [_ B].
  rewrite B. change (φ 0) with 0%Z. bnd y.
  replace ((0 <=? (φ y))%Z && ((φ y) <? (φ n))%Z)%bool with true by lia.
  unfold liftF. destruct (k <? h.[y]) eqn:E1, (h.[y] <? n) eqn:E2; bnorm;
    try (replace (((φ k) <? (φ (h.[y])))%Z) with true by lia);
    try (replace (((φ k) <? (φ (h.[y])))%Z) with false by lia);
    try (replace (((φ (h.[y])) <? (φ n))%Z) with true by lia);
    try (replace (((φ (h.[y])) <? (φ n))%Z) with false by lia); reflexivity.
Qed.

Lemma lift_len : forall h k, PArray.length h = n -> PArray.length (lift h n k) = n.
Proof.
  intros h k Lh. unfold lift.
  destruct (amap_spec (liftF n k) n _ 0 h (wf0 n 0) eq_refl ltac:(rewrite Lh; lia)) as [A _].
  rewrite A. exact Lh.
Qed.

Lemma lift_ok : forall tbl h cur k, HOK tbl h -> COK tbl h cur -> (0 < (φ k))%Z ->
  (forall y, lt y -> (φ (h.[y])) <> (φ k)) ->
  HOK tbl (lift h n k) /\ COK tbl (lift h n k) cur /\
  forall y, lt y -> ((φ (h.[y])) <= (φ ((lift h n k).[y])))%Z.
Proof.
  intros tbl h cur k Hh Hc Hk Hno. pose proof (h_len _ _ Hh) as Lh.
  pose proof (lift_get h k Lh) as G.
  split; [|split].
  - split.
    + apply lift_len. exact Lh.
    + intros a b Ha Hb Rab. rewrite !G by assumption.
      pose proof (h_valid _ _ Hh a b Ha Hb Rab). pose proof (Hno b Hb). pose proof (h_le _ _ Hh b Hb).
      destruct (((φ k) <? (φ (h.[a])))%Z && ((φ (h.[a])) <? (φ n))%Z)%bool eqn:E1,
               (((φ k) <? (φ (h.[b])))%Z && ((φ (h.[b])) <? (φ n))%Z)%bool eqn:E2; lia.
    + rewrite G by exact Hs. rewrite (h_s _ _ Hh).
      replace (((φ n) <? (φ n))%Z) with false by lia. rewrite andb_false_r. reflexivity.
    + rewrite G by exact Ht. rewrite (h_t _ _ Hh).
      replace (((φ k) <? 0)%Z) with false by lia. reflexivity.
    + intros v Hv. rewrite G by exact Hv. pose proof (h_le _ _ Hh v Hv).
      destruct (_ && _)%bool; lia.
  - split; [exact (c_len _ _ _ Hc) | exact (c_le _ _ _ Hc) |].
    intros u Hu Hhu b Hb [Rub Eub].
    pose proof (c_le _ _ _ Hc u Hu). assert (lt b) by lia.
    rewrite (G u Hu) in Hhu, Eub. rewrite (G b H0) in Eub.
    pose proof (h_le _ _ Hh b H0).
    destruct (((φ k) <? (φ (h.[u])))%Z && ((φ (h.[u])) <? (φ n))%Z)%bool eqn:E1; [lia|].
    destruct (((φ k) <? (φ (h.[b])))%Z && ((φ (h.[b])) <? (φ n))%Z)%bool eqn:E2; [lia|].
    apply (c_arc _ _ _ Hc u Hu Hhu b Hb). split; assumption.
  - intros y Hy. rewrite G by exact Hy. pose proof (h_le _ _ Hh y Hy). destruct (_ && _)%bool; lia.
Qed.

(* ---- relabel ---- *)

Lemma relabel_heights : forall tbl ex h cur u (g gl : bool) nh h1 cur1 h2 h3 cur2,
  TabOK tbl ex -> HOK tbl h -> COK tbl h cur -> UOK ex h u -> lt u ->
  ((φ n) <= (φ (cur.[u])))%Z ->
  nh = rmin tbl n u h 0 n (wf0 n 0) -> h1 = h.[u <- nh] -> cur1 = cur.[u <- 0] ->
  h2 = (if g then lift h1 n (h.[u]) else h1) ->
  h3 = (if gl then glob tbl n t h2 else h2) ->
  cur2 = (if gl then PArray.make n 0 else cur1) ->
  (g = true -> (0 < (φ (h.[u])))%Z /\ no_height h1 n (h.[u]) 0 (wf0 n 0) = true) ->
  HOK tbl h3 /\ COK tbl h3 cur2 /\ (forall y, lt y -> ((φ (h.[y])) <= (φ (h3.[y])))%Z) /\
  ((φ (h.[u])) < (φ (h3.[u])))%Z.
Proof.
  intros tbl ex h cur u g gl nh h1 cur1 h2 h3 cur2 T Hh Hc Hu Lu Cu Enh Eh1 Ec1 Eh2 Eh3 Ec2 Eg.
  destruct (Hu Lu) as [U1 [U2 [U3 U4]]].
  pose proof (h_len _ _ Hh) as Lh. pose proof (c_len _ _ _ Hc) as Lc.
  destruct (rmin_spec tbl n u h ltac:(lia) (h_le _ _ Hh) _ 0 n (wf0 n 0) eq_refl ltac:(lia)
              ltac:(intros b' Hb'; change (φ 0) with 0%Z in Hb'; bnd b'; lia)
              ltac:(left; reflexivity)) as [R1 [R2 R3]].
  rewrite <- Enh in R1, R2, R3.
  assert (Strict : ((φ (h.[u])) < (φ nh))%Z).
  { destruct R3 as [R3|[b [Hb [Rb Eb]]]]; [lia|].
    pose proof (h_valid _ _ Hh u b Lu Hb Rb).
    assert (~ ((0 < RD tbl u b)%Z /\ (φ (h.[u])) = ((φ (h.[b])) + 1)%Z))
      by (apply (c_arc _ _ _ Hc u Lu U2); lia).
    unfold RD in *. lia. }
  assert (G1 : forall y, h1.[y] = if y =? u then nh else h.[y])
    by (intros y; subst h1; apply get_set1; rewrite Lh; exact Lu).
  assert (HOK1 : HOK tbl h1).
  { split.
    - subst h1. rewrite alength_set. exact Lh.
    - intros a b Ha Hb Rab. rewrite !G1.
      destruct (a =? u) eqn:Ea, (b =? u) eqn:Eb; bnorm; subst.
      + lia.
      + apply R2; [exact Hb | exact Rab].
      + pose proof (h_valid _ _ Hh a u Ha Lu Rab). lia.
      + apply (h_valid _ _ Hh a b Ha Hb Rab).
    - rewrite G1. replace (s =? u) with false by (symmetry; apply eqb_false; congruence). apply (h_s _ _ Hh).
    - rewrite G1. replace (t =? u) with false by (symmetry; apply eqb_false; congruence). apply (h_t _ _ Hh).
    - intros v Hv. rewrite G1. destruct (v =? u); [exact R1 | apply (h_le _ _ Hh v Hv)]. }
  assert (COK1 : COK tbl h1 cur1).
  { assert (Gc : forall y, cur1.[y] = if y =? u then 0 else cur.[y])
      by (intros y; subst cur1; apply get_set1; rewrite Lc; exact Lu).
    split.
    - subst cur1. rewrite alength_set. exact Lc.
    - intros v Hv. rewrite Gc. destruct (v =? u); [change (φ 0) with 0%Z; lia | apply (c_le _ _ _ Hc v Hv)].
    - intros x Hx Hhx b Hb [Rxb Exb]. rewrite Gc in Hb. rewrite (G1 x) in Hhx, Exb.
      rewrite (G1 b) in Exb.
      destruct (x =? u) eqn:Ex; bnorm; [change (φ 0) with 0%Z in Hb; bnd b; lia|].
      destruct (b =? u) eqn:Eb; bnorm.
      + subst b. pose proof (h_valid _ _ Hh x u Hx Lu Rxb). lia.
      + apply (c_arc _ _ _ Hc x Hx Hhx b Hb). split; assumption. }
  assert (Up1 : forall y, lt y -> ((φ (h.[y])) <= (φ (h1.[y])))%Z).
  { intros y Hy. rewrite G1. destruct (y =? u) eqn:E; bnorm; [subst; lia | lia]. }
  assert (Hu1 : (φ (h1.[u])) = (φ nh)) by (rewrite G1, eqb_refl; reflexivity).
  assert (S2 : HOK tbl h2 /\ COK tbl h2 cur1 /\ forall y, lt y -> ((φ (h1.[y])) <= (φ (h2.[y])))%Z).
  { subst h2. destruct g.
    - destruct (Eg eq_refl) as [K0 K1].
      apply lift_ok; [exact HOK1 | exact COK1 | exact K0 |].
      intros y Hy E. apply (no_height_true h1 n (h.[u]) _ 0 (wf0 n 0) eq_refl K1 y);
        [change (φ 0) with 0%Z; bnd y; lia | apply int_eq; exact E].
    - split; [exact HOK1|]. split; [exact COK1|]. intros; lia. }
  destruct S2 as [HOK2 [COK2 Up2]].
  assert (S3 : HOK tbl h3 /\ COK tbl h3 cur2 /\ forall y, lt y -> ((φ (h2.[y])) <= (φ (h3.[y])))%Z).
  { subst h3 cur2. destruct gl.
    - destruct (glob_spec tbl h2 HOK2) as [A B]. split; [exact A|]. split; [|exact B].
      split.
      + apply make_n. lia.
      + intros v Hv. rewrite aget_make. change (φ 0) with 0%Z. lia.
      + intros x Hx _ b Hb. rewrite aget_make in Hb. change (φ 0) with 0%Z in Hb. bnd b. lia.
    - split; [exact HOK2|]. split; [exact COK2|]. intros; lia. }
  destruct S3 as [HOK3 [COK3 Up3]].
  split; [exact HOK3|]. split; [exact COK3|]. split.
  - intros y Hy. pose proof (Up1 y Hy). pose proof (Up2 y Hy). pose proof (Up3 y Hy). lia.
  - pose proof (Up2 u Lu). pose proof (Up3 u Lu). lia.
Qed.


(* ---- the measure ---- *)

Definition mH (S : st) : Z := isum (fun v => (φ n) - (φ ((s_h S).[v])))%Z.
Definition mP (S : st) : Z :=
  isum (fun v => if v =? s then 0%Z else ((φ ((s_ex S).[v])) * (φ ((s_h S).[v])))%Z).
Definition mC (S : st) : Z := isum (fun v => (φ n) - (φ ((s_cur S).[v])))%Z.
Definition mQ (S : st) : Z := (2 * (φ (s_ql S)) + (if Uint63.ltb (s_cu S) n then 0 else 1))%Z.

Definition lexlt (S' S : st) : Prop :=
  (0 <= mH S' < mH S)%Z \/
  (mH S' = mH S /\ (0 <= mP S' < mP S)%Z) \/
  (mH S' = mH S /\ mP S' = mP S /\ (0 <= mC S' < mC S)%Z) \/
  (mH S' = mH S /\ mP S' = mP S /\ mC S' = mC S /\ (0 <= mQ S' < mQ S)%Z).

Lemma isum_lt : forall F G u, lt u -> (forall y, lt y -> (F y <= G y)%Z) -> (F u < G u)%Z ->
  (isum F < isum G)%Z.
Proof.
  intros F G u Hu Le Lt.
  set (M := fun y => if y =? u then F u else G y).
  rewrite (isum_point G M u Hu).
  2:{ intros y Hy Hne. unfold M. replace (y =? u) with false by (symmetry; apply eqb_false; exact Hne). reflexivity. }
  assert (isum F <= isum M)%Z.
  { apply isum_le. intros y Hy. unfold M. destruct (y =? u) eqn:E; bnorm; [subst; lia | apply Le; exact Hy]. }
  unfold M at 2. rewrite eqb_refl. lia.
Qed.

Lemma mP_nonneg : forall S, (0 <= mP S)%Z.
Proof.
  intros S. apply isum_nonneg. intros y _. destruct (y =? s); [lia|].
  bnd ((s_ex S).[y]). bnd ((s_h S).[y]). nia.
Qed.

Lemma active_iff : forall ex h v, active ex h n s t v = true ->
  (0 < (φ (ex.[v])))%Z /\ ((φ (h.[v])) < (φ n))%Z /\ v <> s /\ v <> t.
Proof.
  intros ex h v A. unfold active in A. bnorm. change (φ 0) with 0%Z in *. tauto.
Qed.

Lemma hp1 : forall tbl h v, HOK tbl h -> lt v -> (φ (h.[v] + 1)) = ((φ (h.[v])) + 1)%Z.
Proof. intros tbl h v Hh Hv. pose proof (h_le _ _ Hh v Hv). apply add_nowrap. change (φ 1) with 1%Z. rewrite wB_val. lia. Qed.

Lemma step_ok : forall S S', Inv S -> Step n s t S S' -> Inv S' /\ lexlt S' S.
Proof.
  intros S S' I HS. destruct HS as
    [tbl ex h cur cnt q qh ql cu rl H1 H2 H3 | tbl ex h cur cnt q qh ql cu rl H1 H2 H3
    | tbl ex h cur cnt q qh ql cu rl H1 H2 | tbl ex h cur cnt q qh ql cu rl H1 H4
    | tbl ex h cur cnt q qh ql cu rl H1 H4 H5];
    destruct I as [T [Hh [Hc Hu]]]; cbn [s_tbl s_ex s_h s_cur s_cu s_ql] in T, Hh, Hc, Hu.
  - (* push *)
    cbv zeta.
    set (v := cur.[cu]) in *.
    set (d := if ex.[cu] <? tbl.[cu * n + v] then ex.[cu] else tbl.[cu * n + v]) in *.
    set (tbl1 := tbl.[cu * n + v <- tbl.[cu * n + v] - d]) in *.
    set (tbl2 := tbl1.[v * n + cu <- tbl1.[v * n + cu] + d]) in *.
    set (ex1 := ex.[cu <- ex.[cu] - d]) in *.
    set (ex2 := ex1.[v <- ex.[v] + d]) in *.
    pose proof H1 as L1. apply ltb_true in L1. pose proof H2 as L2. apply ltb_true in L2.
    unfold adm in H3. apply andb_true_iff in H3. destruct H3 as [A1 A2].
    apply ltb_true in A1. apply eqb_true in A2. change (φ 0) with 0%Z in A1.
    destruct (Hu L1) as [U1 [U2 [U3 U4]]].
    assert (Ah : (φ (h.[cu])) = ((φ (h.[v])) + 1)%Z) by (rewrite A2; apply (hp1 tbl h v Hh L2)).
    assert (Uv : cu <> v) by (intro E; rewrite <- E in Ah; lia).
    assert (Vs : v <> s) by (intro E; pose proof (h_s _ _ Hh) as X; rewrite <- E in X; lia).
    assert (Dd : (φ d) = Z.min (φ (ex.[cu])) (φ (tbl.[cu * n + v]))).
    { unfold d. destruct (ex.[cu] <? tbl.[cu * n + v]) eqn:E; bnorm; lia. }
    destruct (push_tab tbl ex cu v d tbl1 tbl2 ex1 ex2 T L1 L2 Uv U3 Vs U4
                ltac:(lia) ltac:(unfold RD; lia) ltac:(lia) eq_refl eq_refl eq_refl eq_refl)
      as [T2 [RDf EXf]].
    split.
    + unfold Inv. cbn [s_tbl s_ex s_h s_cur s_cu]. split; [exact T2|]. split; [|split].
      * split; [exact (h_len _ _ Hh) | | exact (h_s _ _ Hh) | exact (h_t _ _ Hh) | exact (h_le _ _ Hh)].
        intros a b Ha Hb R. rewrite RDf in R by assumption. unfold ind in R.
        destruct (Uint63.eqb a v && Uint63.eqb b cu) eqn:E.
        -- bnorm. subst a b. lia.
        -- apply (h_valid _ _ Hh a b Ha Hb).
           destruct (Uint63.eqb a cu && Uint63.eqb b v); lia.
      * split; [exact (c_len _ _ _ Hc) | exact (c_le _ _ _ Hc) |].
        intros x Hx Hhx b Hb [R E].
        assert (lt b) by (pose proof (c_le _ _ _ Hc x Hx); lia).
        rewrite RDf in R by assumption. unfold ind in R.
        destruct (Uint63.eqb x v && Uint63.eqb b cu) eqn:E1.
        -- bnorm. subst x b. lia.
        -- apply (c_arc _ _ _ Hc x Hx Hhx b Hb). split; [|exact E].
           destruct (Uint63.eqb x cu && Uint63.eqb b v); lia.
      * cbn [s_ex s_h s_cu]. intros L. destruct (ex.[cu] - d =? 0) eqn:Ez; [lia|].
        apply eqb_false in Ez.
        assert (Sd : (φ (ex.[cu] - d)) = ((φ (ex.[cu])) - (φ d))%Z) by (apply sub_nowrap; lia).
        assert ((φ (ex.[cu] - d)) <> 0%Z) by (intro X; apply Ez; apply int_eq; exact X).
        rewrite EXf. unfold ind. rewrite eqb_refl.
        replace (cu =? v) with false by (symmetry; apply eqb_false; exact Uv).
        split; [lia|]. split; [exact U2|]. split; assumption.
    + right; left. split; [reflexivity|]. split; [apply mP_nonneg|].
      unfold mP. cbn [s_ex s_h].
      rewrite (isum_point2 (fun y => if y =? s then 0%Z else ((φ (ex2.[y])) * (φ (h.[y])))%Z)
                           (fun y => if y =? s then 0%Z else ((φ (ex.[y])) * (φ (h.[y])))%Z) cu v L1 L2 Uv).
      2:{ intros y Hy Y1 Y2. destruct (y =? s); [reflexivity|]. rewrite EXf. unfold ind.
          replace (y =? cu) with false by (symmetry; apply eqb_false; exact Y1).
          replace (y =? v) with false by (symmetry; apply eqb_false; exact Y2).
          rewrite Z.sub_0_r, Z.add_0_r. reflexivity. }
      replace (cu =? s) with false by (symmetry; apply eqb_false; exact U3).
      replace (v =? s) with false by (symmetry; apply eqb_false; exact Vs).
      rewrite !EXf. unfold ind. rewrite !eqb_refl.
      replace (cu =? v) with false by (symmetry; apply eqb_false; exact Uv).
      replace (v =? cu) with false by (symmetry; apply eqb_false; congruence).
      rewrite Ah. nia.
  - (* advance *)
    pose proof H1 as L1. apply ltb_true in L1. pose proof H2 as L2. apply ltb_true in L2.
    set (v := cur.[cu]) in *.
    pose proof (c_len _ _ _ Hc) as Lc.
    assert (Gc : forall y, cur.[cu <- v + 1].[y] = if y =? cu then v + 1 else cur.[y])
      by (intros; apply get_set1; rewrite Lc; exact L1).
    assert (V1 : (φ (v + 1)) = ((φ v) + 1)%Z) by (apply (succ_lt v n); exact L2).
    assert (NA : ~ ((0 < RD tbl cu v)%Z /\ (φ (h.[cu])) = ((φ (h.[v])) + 1)%Z)).
    { unfold adm in H3. intros [R E]. apply andb_false_iff in H3. destruct H3 as [X|X]; bnorm.
      - change (φ 0) with 0%Z in X. unfold RD in R. lia.
      - apply X. apply int_eq. rewrite (hp1 tbl h v Hh L2). exact E. }
    split.
    + split; [exact T|]. split; [exact Hh|]. split; [|exact Hu].
      cbn [s_tbl s_h s_cur]. split.
      * rewrite alength_set. exact Lc.
      * intros y Hy. rewrite Gc. destruct (y =? cu); [lia | apply (c_le _ _ _ Hc y Hy)].
      * intros x Hx Hhx b Hb. rewrite Gc in Hb. destruct (x =? cu) eqn:Ex; bnorm.
        -- subst x. rewrite V1 in Hb. destruct (Z.eq_dec (φ b) (φ v)) as [Eb|Eb].
           ++ apply int_eq in Eb. subst b. exact NA.
           ++ apply (c_arc _ _ _ Hc cu Hx Hhx b). fold v. lia.
        -- apply (c_arc _ _ _ Hc x Hx Hhx b Hb).
    + right; right; left. split; [reflexivity|]. split; [reflexivity|].
      unfold mC. cbn [s_cur]. split.
      * apply isum_nonneg. intros y Hy. rewrite Gc.
        destruct (y =? cu); [lia | pose proof (c_le _ _ _ Hc y Hy); lia].
      * apply isum_lt with cu; [exact L1 | |].
        -- intros y Hy. rewrite Gc. destruct (y =? cu) eqn:E; bnorm; [subst; lia | lia].
        -- rewrite Gc, eqb_refl. lia.
  - (* relabel *)
    pose proof H1 as L1. apply ltb_true in L1. pose proof H2 as L2. apply ltb_false in L2.
    cbv zeta.
    lazymatch goal with |- Inv (mkst _ _ ?h3 ?cur2 _ _ _ _ _ _) /\ _ =>
      set (H3v := h3) in *; set (C2v := cur2) in *;
      pose proof (relabel_heights tbl ex h cur cu _ _ _ _ _ _ H3v C2v T Hh Hc Hu L1 L2
                    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as RH end.
    specialize (RH ltac:(intros G; apply andb_true_iff in G; destruct G as [G G4];
                         apply andb_true_iff in G; destruct G as [G G3];
                         apply andb_true_iff in G; destruct G as [G1 G2];
                         apply ltb_true in G2; change (φ 0) with 0%Z in G2; split; assumption)).
    destruct RH as [HOK3 [COK3 [Up Str]]].
    destruct (Hu L1) as [U1 [U2 [U3 U4]]].
    split.
    + split; [exact T|]. split; [exact HOK3|]. split; [exact COK3|].
      cbn [s_ex s_h s_cu]. intros L. destruct (H3v.[cu] <? n) eqn:E; [|lia].
      apply ltb_true in E. split; [exact U1|]. split; [exact E|]. split; assumption.
    + left. unfold mH; cbn [s_h]. split.
      * apply isum_nonneg. intros y Hy. pose proof (h_le _ _ HOK3 y Hy). lia.
      * apply isum_lt with cu; [exact L1 | intros y Hy; pose proof (Up y Hy); lia | lia].
  - (* pop *)
    cbv zeta.
    split.
    + split; [exact T|]. split; [exact Hh|]. split; [exact Hc|].
      cbn [s_ex s_h s_cu]. intros L.
      destruct ((q.[qh] <? n) && active ex h n s t q.[qh]) eqn:E; [|lia].
      apply andb_true_iff in E. destruct E as [_ E]. apply active_iff. exact E.
    + right; right; right. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      unfold mQ. cbn [s_ql s_cu]. rewrite H1. apply ltb_true in H4. change (φ 0) with 0%Z in H4.
      rewrite sub_nowrap by (change (φ 1) with 1%Z; lia).
      change (φ 1) with 1%Z. bnd ql.
      match goal with |- context [if ?c then 0%Z else 1%Z] => destruct c end; lia.
  - (* scan *)
    destruct (find_act_spec ex h n s t _ 0 (wf0 n 0) eq_refl) as [F1 _].
    split.
    + split; [exact T|]. split; [exact Hh|]. split; [exact Hc|].
      cbn [s_ex s_h s_cu]. intros L. apply active_iff. apply F1. exact L.
    + right; right; right. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      unfold mQ. cbn [s_ql s_cu]. rewrite H1, H5. apply ltb_false in H4.
      change (φ 0) with 0%Z in H4. bnd ql. lia.
Qed.


(* ---- termination ---- *)

Lemma acc_inv : forall S, Inv S -> Acc (StepR n s t) S.
Proof.
  assert (A : forall a b c d S, mH S = a -> mP S = b -> mC S = c -> mQ S = d -> Inv S ->
                Acc (StepR n s t) S).
  { intros a. induction a as [a IHa] using (well_founded_ind (Zwf_well_founded 0)).
    intros b. induction b as [b IHb] using (well_founded_ind (Zwf_well_founded 0)).
    intros c. induction c as [c IHc] using (well_founded_ind (Zwf_well_founded 0)).
    intros d. induction d as [d IHd] using (well_founded_ind (Zwf_well_founded 0)).
    intros S Ea Eb Ec Ed I. constructor. intros S' HS.
    destruct (step_ok S S' I HS) as [I' L]. unfold lexlt in L.
    destruct L as [L|[L|[L|L]]].
    - apply (IHa (mH S')) with (mP S') (mC S') (mQ S'); try reflexivity; [unfold Zwf; lia | exact I'].
    - apply (IHb (mP S')) with (mC S') (mQ S'); try reflexivity; [unfold Zwf; lia | lia | exact I'].
    - apply (IHc (mC S')) with (mQ S'); try reflexivity; [unfold Zwf; lia | lia | lia | exact I'].
    - apply (IHd (mQ S')); try reflexivity; [unfold Zwf; lia | lia | lia | lia | exact I']. }
  intros S I. apply (A _ _ _ _ S eq_refl eq_refl eq_refl eq_refl I).
Qed.

(* ---- the main loop ---- *)

Lemma mloop_spec : forall S, Acc (StepR n s t) S ->
  forall tbl ex h cur cnt q qh ql cu rl (H : Acc (StepR n s t) (mkst tbl ex h cur cnt q qh ql cu rl)),
  S = mkst tbl ex h cur cnt q qh ql cu rl -> Inv S ->
  exists S', Inv S' /\ (forall v, lt v -> active (s_ex S') (s_h S') n s t v = false) /\
             mloop n s t tbl ex h cur cnt q qh ql cu rl H = (s_ex S').[t].
Proof.
  intros S Hacc. induction Hacc as [S _ IH].
  intros tbl ex h cur cnt q qh ql cu rl H ES I. subst S.
  destruct H as [Hf]. cbn [mloop].
  destruct (bdec (cu <? n)) as [H1 | H1].
  - destruct (bdec (cur.[cu] <? n)) as [H2 | H2].
    + destruct (bdec (adm tbl h n cu cur.[cu])) as [H3 | H3].
      * eapply IH; [exact (step_push n s t tbl ex h cur cnt q qh ql cu rl H1 H2 H3) | reflexivity |].
        exact (proj1 (step_ok _ _ I (step_push n s t tbl ex h cur cnt q qh ql cu rl H1 H2 H3))).
      * eapply IH; [exact (step_adv n s t tbl ex h cur cnt q qh ql cu rl H1 H2 H3) | reflexivity |].
        exact (proj1 (step_ok _ _ I (step_adv n s t tbl ex h cur cnt q qh ql cu rl H1 H2 H3))).
    + eapply IH; [exact (step_rel n s t tbl ex h cur cnt q qh ql cu rl H1 H2) | reflexivity |].
      exact (proj1 (step_ok _ _ I (step_rel n s t tbl ex h cur cnt q qh ql cu rl H1 H2))).
  - destruct (bdec (0 <? ql)) as [H4 | H4].
    + eapply IH; [exact (step_pop n s t tbl ex h cur cnt q qh ql cu rl H1 H4) | reflexivity |].
      exact (proj1 (step_ok _ _ I (step_pop n s t tbl ex h cur cnt q qh ql cu rl H1 H4))).
    + destruct (bdec (find_act ex h n s t 0 (wf0 n 0) <? n)) as [H5 | H5].
      * eapply IH; [exact (step_scan n s t tbl ex h cur cnt q qh ql cu rl H1 H4 H5) | reflexivity |].
        exact (proj1 (step_ok _ _ I (step_scan n s t tbl ex h cur cnt q qh ql cu rl H1 H4 H5))).
      * exists (mkst tbl ex h cur cnt q qh ql cu rl). split; [exact I|]. split; [|reflexivity].
        cbn [s_ex s_h]. intros v Hv.
        destruct (find_act_spec ex h n s t _ 0 (wf0 n 0) eq_refl) as [_ F2].
        apply F2; [apply ltb_false; exact H5 | change (φ 0) with 0%Z; bnd v; lia].
Qed.

End Machine.

(* ------------------------------------------------------------------ *)
(* The initial state                                                   *)
(* ------------------------------------------------------------------ *)

Definition cpx (x : array int) (n a b : int) : Z :=
  if (a <? n) && (b <? n) then (φ (capf x a b)) else 0%Z.

Section Init.

Variables (n s t : int) (x : array int).
Hypothesis Hn : (2 <= (φ n) <= 1000)%Z.
Hypothesis Hs : ((φ s) < (φ n))%Z.
Hypothesis Ht : ((φ t) < (φ n))%Z.
Hypothesis Hx : forall j, ((φ j) < (φ n))%Z -> (2 <= (φ (x.[j])) <= 2000000000)%Z.

Local Notation lt a := ((φ a) < (φ n))%Z.
Local Notation cp := (cpx x n).

Lemma cp_sym : forall a b, cp a b = cp b a.
Proof.
  intros a b. unfold cpx. rewrite capf_sym, andb_comm. reflexivity.
Qed.

Lemma cp_rng : forall a b, (0 <= cp a b <= 2147483648)%Z.
Proof.
  intros a b. unfold cpx. destruct ((a <? n) && (b <? n)) eqn:E; [|lia]. bnorm.
  pose proof (capf_le x a b ltac:(specialize (Hx a H); lia)). pose proof (Hx a H).
  bnd (capf x a b). lia.
Qed.

Lemma cp_diag : forall a, cp a a = 0%Z.
Proof. intros a. unfold cpx. rewrite capf_diag. destruct (_ && _); reflexivity. Qed.

Lemma cp_lt : forall a b, lt a -> lt b -> cp a b = (φ (capf x a b)).
Proof.
  intros a b Ha Hb. unfold cpx. replace ((a <? n) && (b <? n)) with true; [reflexivity|].
  symmetry. apply andb_true_iff. split; apply ltb_true; assumption.
Qed.

Definition SV (v a b : int) : Z :=
  ((if Uint63.eqb a s && ((φ b) <? (φ v))%Z then 0 else cp a b) +
   (if Uint63.eqb b s && ((φ a) <? (φ v))%Z then cp a b else 0))%Z.

Lemma sat_spec : forall (z : Z) tbl ex q ql v H, gap n v = z -> ((φ v) <= (φ n))%Z ->
  PArray.length tbl = n * n -> PArray.length ex = n ->
  (forall a b, lt a -> lt b -> (φ (tbl.[a * n + b])) = SV v a b) ->
  (forall y, lt y -> (φ (ex.[y])) = if ((φ y) <? (φ v))%Z then cp s y else 0%Z) ->
  let p := sat n s t tbl ex q ql v H in
  PArray.length (fst (fst (fst p))) = n * n /\ PArray.length (snd (fst (fst p))) = n /\
  (forall a b, lt a -> lt b -> (φ ((fst (fst (fst p))).[a * n + b])) = SV n a b) /\
  (forall y, lt y -> (φ ((snd (fst (fst p))).[y])) = cp s y).
Proof.
  intros z. gind z IH. intros tbl ex q ql v H Hz Hv Lt Le Ct Ce. cbv zeta.
  rewrite sat_eq. destruct (bdec (v <? n)) as [Hvn | Hvn].
  - cbv zeta. pose proof Hvn as Hv'. bnorm. pose proof (succ_lt v n Hv') as Hs1.
    assert (Pp : ((φ (s * n + v)) < (φ (PArray.length tbl)))%Z)
      by (rewrite Lt, nn_spec by lia; apply idx_lt; lia).
    assert (Pq : ((φ (v * n + s)) < (φ (PArray.length tbl)))%Z)
      by (rewrite Lt, nn_spec by lia; apply idx_lt; lia).
    assert (Cc : (φ (tbl.[s * n + v])) = cp s v).
    { rewrite Ct by assumption. unfold SV. rewrite eqb_refl.
      replace ((φ v) <? (φ v))%Z with false by lia. cbn [andb].
      destruct (v =? s) eqn:E; cbn [andb]; [apply eqb_true in E; subst; rewrite cp_diag, Z.ltb_irrefl; lia | lia]. }
    apply (IH (gap n (v + 1))); [rewrite <- Hz; apply dec_step; exact Hvn | reflexivity | lia | | | | ].
    + rewrite !alength_set. exact Lt.
    + rewrite alength_set. exact Le.
    + intros a b Ha Hb. rewrite get_set2 by (rewrite ?alength_set; assumption).
      pose proof (cp_rng a b) as Rab. pose proof (cp_sym a b) as Sab.
      destruct (a * n + b =? v * n + s) eqn:Q1; bnorm.
      * apply idx_eq_iff in Q1; [|lia..]. destruct Q1; subst a b.
        rewrite get_set1 by assumption. unfold SV. rewrite eqb_refl. rewrite Hs1.
        destruct (v * n + s =? s * n + v) eqn:Q2; bnorm.
        -- apply idx_eq_iff in Q2; [|lia..]. destruct Q2 as [Q2 _]; subst v.
           assert (C0 : (φ (tbl.[s * n + s])) = 0%Z) by (rewrite Cc; apply cp_diag).
           rewrite add_nowrap by (change (φ 0) with 0%Z; rewrite C0, wB_val; lia).
           change (φ 0) with 0%Z. rewrite C0.
           rewrite !eqb_refl. replace ((φ s) <? (φ s) + 1)%Z with true by lia. cbn [andb].
           rewrite cp_diag. lia.
        -- assert (Vs : v <> s) by (intro E; subst; apply Q2; reflexivity).
           rewrite add_nowrap.
           ++ rewrite Ct by assumption. rewrite Cc. unfold SV.
              replace (v =? s) with false by (symmetry; apply eqb_false; exact Vs).
              rewrite eqb_refl. replace ((φ v) <? (φ v))%Z with false by lia.
              replace ((φ v) <? (φ v) + 1)%Z with true by lia. cbn [andb]. rewrite (cp_sym s v). lia.
           ++ rewrite Ct by assumption. rewrite Cc. unfold SV.
              replace (v =? s) with false by (symmetry; apply eqb_false; exact Vs).
              rewrite eqb_refl. replace ((φ v) <? (φ v))%Z with false by lia. cbn [andb].
              pose proof (cp_rng v s). pose proof (cp_rng s v). rewrite wB_val. lia.
      * destruct (a * n + b =? s * n + v) eqn:Q2; bnorm.
        -- apply idx_eq_iff in Q2; [|lia..]. destruct Q2; subst a b.
           assert (Vs : v <> s) by (intro E; subst; apply Q1; reflexivity).
           unfold SV. rewrite eqb_refl. rewrite Hs1. replace ((φ v) <? (φ v) + 1)%Z with true by lia.
           replace (v =? s) with false by (symmetry; apply eqb_false; exact Vs). cbn [andb]. reflexivity.
        -- rewrite Ct by assumption. unfold SV. rewrite Hs1.
           assert (N1 : ~ (a = v /\ b = s))
             by (intro X; apply Q1; apply (proj2 (idx_eq_iff n Hn a b v s Ha Hb Hv' Hs)); exact X).
           assert (N2 : ~ (a = s /\ b = v))
             by (intro X; apply Q2; apply (proj2 (idx_eq_iff n Hn a b s v Ha Hb Hs Hv')); exact X).
           destruct (a =? s) eqn:As, (b =? s) eqn:Bs; bnorm; cbn [andb].
           ++ subst a b. replace ((φ s) <? (φ v))%Z with ((φ s) <? (φ v) + 1)%Z; [reflexivity|].
              destruct (Z.eq_dec (φ s) (φ v)) as [E|E]; [apply int_eq in E; exfalso; apply N1; split; congruence | lia].
           ++ subst a. assert ((φ b) <> (φ v)) by (intro E; apply N2; split; [reflexivity|apply int_eq; exact E]).
              replace ((φ b) <? (φ v) + 1)%Z with ((φ b) <? (φ v))%Z by lia. reflexivity.
           ++ subst b. assert ((φ a) <> (φ v)) by (intro E; apply N1; split; [apply int_eq; exact E|reflexivity]).
              replace ((φ a) <? (φ v) + 1)%Z with ((φ a) <? (φ v))%Z by lia. reflexivity.
           ++ reflexivity.
    + intros y Hy. rewrite get_set1 by (rewrite Le; exact Hv'). rewrite Hs1.
      destruct (y =? v) eqn:E; bnorm.
      * subst y. rewrite Cc. replace ((φ v) <? (φ v) + 1)%Z with true by lia. reflexivity.
      * rewrite Ce by exact Hy. assert ((φ y) <> (φ v)) by (intro X; apply E, int_eq; exact X).
        replace ((φ y) <? (φ v) + 1)%Z with ((φ y) <? (φ v))%Z by lia. reflexivity.
  - bnorm. replace v with n in * by (apply int_eq; lia).
    cbn [fst snd]. split; [exact Lt|]. split; [exact Le|]. split; [exact Ct|].
    intros y Hy. rewrite Ce by exact Hy. replace ((φ y) <? (φ n))%Z with true by lia. reflexivity.
Qed.

End Init.

Lemma guard_facts : forall x, guard x = true ->
  (2 <= (φ (nn x)) <= 1000)%Z /\ ((φ (ss x)) < (φ (nn x)))%Z /\ ((φ (tt x)) < (φ (nn x)))%Z /\
  ss x <> tt x /\
  (forall j, ((φ j) < (φ (nn x)))%Z -> (2 <= (φ (x.[j])) <= 2000000000)%Z) /\
  (forall j, ((φ j) < (φ (nn x)))%Z -> ((φ (x.[ss x])) <= (φ (x.[j])))%Z) /\
  (forall j, ((φ j) < (φ (nn x)))%Z -> ((φ (x.[j])) <= (φ (x.[tt x])))%Z).
Proof.
  intros x G. unfold guard in G.
  apply andb_true_iff in G. destruct G as [G G4]. apply andb_true_iff in G. destruct G as [G G3].
  apply andb_true_iff in G. destruct G as [G1 G2]. apply leb_true in G1. apply leb_true in G2.
  apply negb_true_iff in G4. apply eqb_false in G4.
  change (φ 2) with 2%Z in G1. change (φ 1000) with 1000%Z in G2.
  assert (St : forall j, ((φ j) < (φ 1))%Z -> ((φ j) < (φ (nn x)))%Z -> j = 0).
  { intros j A _. change (φ 1) with 1%Z in A. bnd j. apply int_eq. change (φ 0) with 0%Z. lia. }
  destruct (amin_spec x (nn x) _ 1 0 (wf0 (nn x) 1) eq_refl ltac:(change (φ 0) with 0%Z; lia)
              ltac:(intros j A B; rewrite (St j A B); lia)) as [A1 A2].
  destruct (amax_spec x (nn x) _ 1 0 (wf0 (nn x) 1) eq_refl ltac:(change (φ 0) with 0%Z; lia)
              ltac:(intros j A B; rewrite (St j A B); lia)) as [B1 B2].
  split; [lia|]. split; [exact A1|]. split; [exact B1|]. split; [exact G4|].
  split; [|split; [exact A2 | exact B2]].
  intros j Hj. apply (rng_ok_sound x (nn x) _ 0 (wf0 (nn x) 0) eq_refl G3). change (φ 0) with 0%Z.
  bnd j. lia.
Qed.

Lemma Z_gcd_N : forall a b : N, Z.of_N (N.gcd a b) = Z.gcd (Z.of_N a) (Z.of_N b).
Proof. intros [|a] [|b]; reflexivity. Qed.

Section InitInv.

Variable x : array int.
Hypothesis Hg : guard x = true.

Local Notation n := (nn x).
Local Notation s := (ss x).
Local Notation t := (tt x).
Local Notation cp := (cpx x (nn x)).
Local Notation lt a := ((φ a) < (φ (nn x)))%Z.

Lemma init_inv : Inv n s t cp (init_state x).
Proof.
  destruct (guard_facts x Hg) as [Hn [Hs [Ht [Hst [Hx [Hmin Hmax]]]]]].
  unfold init_state. cbv zeta.
  destruct (table_spec n Hn x) as [T1 T2].
  set (tbl0 := fill_tab x n (PArray.make (n * n) 0) 0 (wf0 n 0)) in *.
  assert (L0 : PArray.length (PArray.make n 0) = n) by (apply make_n; exact Hn).
  destruct (sat_spec n s t x Hn Hs Hx _ tbl0 (PArray.make n 0) (PArray.make n 0) 0 0 (wf0 n 0)
              eq_refl ltac:(change (φ 0) with 0%Z; lia) T1 L0) as [P1 [P2 [P3 P4]]].
  { intros a b Ha Hb. rewrite T2 by assumption. unfold SV. change (φ 0) with 0%Z.
    replace ((φ b) <? 0)%Z with false by (bnd b; lia). replace ((φ a) <? 0)%Z with false by (bnd a; lia).
    rewrite !andb_false_r. rewrite cp_lt by assumption. lia. }
  { intros y Hy. rewrite aget_make. change (φ 0) with 0%Z.
    replace ((φ y) <? 0)%Z with false by (bnd y; lia). reflexivity. }
  set (p := sat n s t tbl0 (PArray.make n 0) (PArray.make n 0) 0 0 (wf0 n 0)) in *.
  set (tbl1 := fst (fst (fst p))) in *. set (ex1 := snd (fst (fst p))) in *.
  assert (SVn : forall a b, lt a -> lt b -> RD n tbl1 a b =
            ((if Uint63.eqb a s then 0 else cp a b) + (if Uint63.eqb b s then cp a b else 0))%Z).
  { intros a b Ha Hb. unfold RD. rewrite P3 by assumption. unfold SV.
    replace ((φ b) <? (φ n))%Z with true by lia. replace ((φ a) <? (φ n))%Z with true by lia.
    rewrite !andb_true_r. reflexivity. }
  pose proof (cp_sym n x) as CS. pose proof (cp_rng n s t x Hx) as CR. pose proof (cp_diag n x) as CD.
  (* the table invariant *)
  assert (TT : TabOK n s t cp tbl1 ex1).
  { split; [exact P1 | exact P2 | | | ].
    - intros a b Ha Hb. rewrite !SVn by assumption. rewrite (CS b a).
      destruct (a =? s), (b =? s); lia.
    - intros v Hv Vs. rewrite P4 by exact Hv. unfold colsum.
      rewrite (isum_point n s t Hn Hst _ (fun _ => 0%Z) s Hs).
      + rewrite SVn by assumption. rewrite eqb_refl.
        replace (s =? s) with true by (symmetry; apply eqb_refl).
        replace (v =? s) with false by (symmetry; apply eqb_false; exact Vs).
        assert (isum n (fun _ => 0%Z) = 0%Z) by (unfold isum; apply zsum_zero; reflexivity). lia.
      + intros y Hy Ys. rewrite SVn by assumption.
        replace (y =? s) with false by (symmetry; apply eqb_false; exact Ys).
        replace (v =? s) with false by (symmetry; apply eqb_false; exact Vs). lia.
    - intros y Hy. rewrite SVn by assumption.
      replace (t =? s) with false by (symmetry; apply eqb_false; congruence).
      destruct (y =? s); pose proof (CR t y); lia. }
  (* heights before the first global relabeling *)
  set (h0 := (PArray.make n 0).[s <- n]).
  assert (G0 : forall y, h0.[y] = if y =? s then n else 0)
    by (intros y; unfold h0; rewrite get_set1 by (rewrite L0; exact Hs); rewrite aget_make; reflexivity).
  assert (H0 : HOK n s t tbl1 h0).
  { split.
    - unfold h0. rewrite alength_set. exact L0.
    - intros a b Ha Hb Rab. rewrite !G0. rewrite SVn in Rab by assumption.
      destruct (a =? s) eqn:Ea; bnorm.
      + subst a. destruct (b =? s) eqn:Eb; bnorm; [subst b; rewrite CD in Rab|]; lia.
      + change (φ 0) with 0%Z. destruct (b =? s); [lia|]. change (φ 0) with 0%Z. lia.
    - rewrite G0, eqb_refl. reflexivity.
    - rewrite G0. replace (t =? s) with false by (symmetry; apply eqb_false; congruence). reflexivity.
    - intros v Hv. rewrite G0. destruct (v =? s); change (φ 0) with 0%Z; lia. }
  destruct (glob_spec n s t Hn Hs Ht Hst tbl1 h0 H0) as [H1 _].
  unfold Inv. cbn [s_tbl s_ex s_h s_cur s_cu].
  split; [exact TT|]. split; [exact H1|]. split.
  - split; [exact L0 | |].
    + intros v Hv. rewrite aget_make. change (φ 0) with 0%Z. lia.
    + intros u Hu _ b Hb. rewrite aget_make in Hb. change (φ 0) with 0%Z in Hb. bnd b. lia.
  - cbn [s_cu]. intros L. lia.
Qed.

End InitInv.

Definition acc_init (x : array int) (Hg : guard x = true) :
  Acc (StepR (nn x) (ss x) (tt x))
      (mkst (s_tbl (init_state x)) (s_ex (init_state x)) (s_h (init_state x))
            (s_cur (init_state x)) (s_cnt (init_state x)) (s_q (init_state x))
            (s_qh (init_state x)) (s_ql (init_state x)) (s_cu (init_state x))
            (s_rl (init_state x))).
Proof.
  destruct (guard_facts x Hg) as [Hn [Hs [Ht [Hst [Hx _]]]]].
  apply (acc_inv (nn x) (ss x) (tt x) (cpx x (nn x)) Hn Hs Ht Hst (cp_rng (nn x) 0 0 x Hx)).
  exact (init_inv x Hg).
Qed.

(* ------------------------------------------------------------------ *)
(* The function                                                        *)
(* ------------------------------------------------------------------ *)

Definition mazemovement_impl (x : array uint) : uint :=
  match bdec (guard x) with
  | left Hg =>
      let S := init_state x in
      mloop (nn x) (ss x) (tt x) (s_tbl S) (s_ex S) (s_h S) (s_cur S) (s_cnt S) (s_q S)
            (s_qh S) (s_ql S) (s_cu S) (s_rl S) (acc_init x Hg)
  | right _ => 0
  end.
Elpi complexity mazemovement_impl.

(* ------------------------------------------------------------------ *)
(* Back to the contract                                                *)
(* ------------------------------------------------------------------ *)

Lemma io_back : forall u, io (Z.to_nat (φ u)) = u.
Proof.
  intros u. bnd u. apply int_eq. rewrite io_spec by (rewrite Z2Nat.id; lia).
  apply Z2Nat.id. lia.
Qed.

Lemma io_val : forall k, (Z.of_nat k < 4194304)%Z -> (φ (io k)) = Z.of_nat k.
Proof. intros k Hk. apply io_spec. rewrite wB_val. lia. Qed.

Lemma sb_zsum : forall f m, Z.of_N (sum_below f m) = zsum (fun k => Z.of_N (f (N.of_nat k))) m.
Proof. intros f m. induction m as [|m IH]; simpl; [reflexivity|]. rewrite N2Z.inj_add, IH. reflexivity. Qed.

Lemma minmax : forall x, (1 <= (φ (nn x)))%Z ->
  ((φ (ss x)) < (φ (nn x)))%Z /\ ((φ (tt x)) < (φ (nn x)))%Z /\
  (forall j, ((φ j) < (φ (nn x)))%Z -> ((φ (x.[ss x])) <= (φ (x.[j])))%Z) /\
  (forall j, ((φ j) < (φ (nn x)))%Z -> ((φ (x.[j])) <= (φ (x.[tt x])))%Z).
Proof.
  intros x H1.
  assert (St : forall j, ((φ j) < (φ 1))%Z -> ((φ j) < (φ (nn x)))%Z -> j = 0).
  { intros j A _. change (φ 1) with 1%Z in A. bnd j. apply int_eq. change (φ 0) with 0%Z. lia. }
  destruct (amin_spec x (nn x) _ 1 0 (wf0 (nn x) 1) eq_refl ltac:(change (φ 0) with 0%Z; lia)
              ltac:(intros j A B; rewrite (St j A B); lia)) as [A1 A2].
  destruct (amax_spec x (nn x) _ 1 0 (wf0 (nn x) 1) eq_refl ltac:(change (φ 0) with 0%Z; lia)
              ltac:(intros j A B; rewrite (St j A B); lia)) as [B1 B2].
  unfold ss, tt. tauto.
Qed.

Section Final.

Variable rooms : list N.
Variable x : array int.
Hypothesis Hv : valid_input rooms.
Hypothesis Hr : repr (x : array uint) rooms.

Local Notation L := (List.length rooms).

Lemma f_len : (φ (nn x)) = Z.of_nat L.
Proof. destruct Hr as [Hl _]. symmetry. exact Hl. Qed.

Lemma f_cell : forall k, (k < L)%nat -> Z.of_N (nth k rooms 0%N) = (φ (x.[io k])).
Proof.
  intros k Hk. destruct Hr as [_ Hc]. destruct (Hc k Hk) as [m [Hm Rm]].
  unfold repr, repr_uint in Rm. rewrite (nth_error_nth _ _ _ Hm). rewrite <- Rm.
  rewrite Z2N.id by (apply to_Z_bounded). reflexivity.
Qed.

Lemma f_bounds : (2 <= Z.of_nat L <= 1000)%Z.
Proof. destruct Hv as [Hn _ _ _]. unfold len in Hn. lia. Qed.

Lemma f_range : forall j, ((φ j) < (φ (nn x)))%Z -> (2 <= (φ (x.[j])) <= 2000000000)%Z.
Proof.
  intros j Hj. rewrite f_len in Hj. bnd j.
  rewrite <- (io_back j). rewrite <- f_cell by lia.
  destruct Hv as [_ Hrg _ _]. rewrite Forall_nth in Hrg.
  specialize (Hrg (Z.to_nat (φ j)) 0%N ltac:(lia)). lia.
Qed.

Lemma f_inj : forall a b, (a < L)%nat -> (b < L)%nat -> (φ (x.[io a])) = (φ (x.[io b])) -> a = b.
Proof.
  intros a b Ha Hb E. rewrite <- !f_cell in E by assumption.
  destruct Hv as [_ _ Hu _]. apply (proj1 (NoDup_nth rooms 0%N) Hu a b Ha Hb). lia.
Qed.

Lemma f_guard : guard x = true.
Proof.
  pose proof f_len as Lx. pose proof f_bounds as B.
  destruct (minmax x ltac:(lia)) as [A1 [B1 [A2 B2]]].
  unfold guard. apply andb_true_iff. split; [apply andb_true_iff; split; [apply andb_true_iff; split|]|].
  - apply leb_true. change (φ 2) with 2%Z. lia.
  - apply leb_true. change (φ 1000) with 1000%Z. lia.
  - apply (rng_ok_complete x (nn x) _ 0 (wf0 (nn x) 0) eq_refl). intros j Hj. apply f_range. lia.
  - apply negb_true_iff. apply eqb_false. intros E.
    assert (E0 : (φ (x.[io 0])) = (φ (x.[io 1]))).
    { assert (L0 : ((φ (io 0)) < (φ (nn x)))%Z) by (rewrite io_val by lia; lia).
      assert (L1 : ((φ (io 1)) < (φ (nn x)))%Z) by (rewrite io_val by lia; lia).
      pose proof (A2 _ L0). pose proof (A2 _ L1). pose proof (B2 _ L0). pose proof (B2 _ L1).
      rewrite E in *. lia. }
    apply f_inj in E0; lia.
Qed.

Lemma f_cap : forall a b, (a < L)%nat -> (b < L)%nat ->
  Z.of_N (cap rooms (N.of_nat a) (N.of_nat b)) = cpx x (nn x) (io a) (io b).
Proof.
  intros a b Ha Hb. pose proof f_len as Lx. pose proof f_bounds as B.
  assert (Ia : (φ (io a)) = Z.of_nat a) by (apply io_val; lia).
  assert (Ib : (φ (io b)) = Z.of_nat b) by (apply io_val; lia).
  rewrite cp_lt by lia. unfold cap, capf, room. rewrite !Nnat.Nat2N.id.
  destruct (Nat.eq_dec a b) as [E|E].
  - subst b. rewrite N.eqb_refl, eqb_refl. reflexivity.
  - replace (N.of_nat a =? N.of_nat b)%N with false by (symmetry; apply N.eqb_neq; lia).
    replace (io a =? io b) with false by (symmetry; apply eqb_false; intro X; apply E;
      apply (f_equal to_Z) in X; lia).
    pose proof (igcd_spec x.[io a] x.[io b]) as G.
    rewrite <- (f_cell a Ha), <- (f_cell b Hb), <- Z_gcd_N in G.
    destruct (1 <? igcd x.[io a] x.[io b]) eqn:E1; bnorm; change (φ 1) with 1%Z in *.
    + replace (1 <? N.gcd (nth a rooms 0%N) (nth b rooms 0%N))%N with true by (symmetry; apply N.ltb_lt; lia).
      lia.
    + replace (1 <? N.gcd (nth a rooms 0%N) (nth b rooms 0%N))%N with false by (symmetry; apply N.ltb_ge; lia).
      reflexivity.
Qed.

Theorem mazemovement_impl_correct :
  exists ans : N, repr (mazemovement_impl x) ans /\ mazemovement_spec rooms ans.
Proof.
  pose proof f_guard as Hg.
  destruct (guard_facts x Hg) as [Hn [Hs [Ht [Hst [Hx' [Hmin Hmax]]]]]].
  pose proof f_len as Lx.
  unfold mazemovement_impl. destruct (bdec (guard x)) as [Hg' | Hg']; [|congruence].
  destruct (mloop_spec (nn x) (ss x) (tt x) (cpx x (nn x)) Hn Hs Ht Hst (cp_rng (nn x) 0 0 x Hx')
              _ (acc_init x Hg') _ _ _ _ _ _ _ _ _ _ (acc_init x Hg') eq_refl (init_inv x Hg'))
    as [S' [I' [NA R]]].
  cbv zeta. rewrite R.
  exists (Z.to_N (φ ((s_ex S').[tt x]))). split; [reflexivity|].
  destruct I' as [T [Hh [_ _]]].
  set (n := nn x) in *. set (sn := Z.to_nat (φ (ss x))). set (tn := Z.to_nat (φ (tt x))).
  assert (Ns : io sn = ss x) by apply io_back.
  assert (Nt : io tn = tt x) by apply io_back.
  assert (Hsn : (sn < L)%nat) by lia. assert (Htn : (tn < L)%nat) by lia.
  assert (Hstn : sn <> tn) by (intro E; apply Hst; rewrite <- Ns, <- Nt, E; reflexivity).
  assert (IL : forall k, (k < L)%nat -> ((φ (io k)) < (φ n))%Z /\ (φ (io k)) = Z.of_nat k)
    by (intros k Hk; rewrite io_val by lia; lia).
  intros s' t' Hen Hex.
  (* the entrance and the exit are the code's s and t *)
  assert (Es : s' = N.of_nat sn).
  { destruct Hen as [H1 H2]. unfold len in H1.
    pose proof (H2 (N.of_nat sn) ltac:(unfold len; lia)) as A. unfold room in A.
    rewrite Nnat.Nat2N.id in A. apply N2Z.inj_le in A.
    rewrite !f_cell in A by lia. rewrite Ns in A.
    pose proof (Hmin (io (N.to_nat s')) ltac:(apply IL; lia)).
    assert (N.to_nat s' = sn) by (apply f_inj; [lia | lia | rewrite Ns; lia]). lia. }
  assert (Et : t' = N.of_nat tn).
  { destruct Hex as [H1 H2]. unfold len in H1.
    pose proof (H2 (N.of_nat tn) ltac:(unfold len; lia)) as A. unfold room in A.
    rewrite Nnat.Nat2N.id in A. apply N2Z.inj_le in A.
    rewrite !f_cell in A by lia. rewrite Nt in A.
    pose proof (Hmax (io (N.to_nat t')) ltac:(apply IL; lia)).
    assert (N.to_nat t' = tn) by (apply f_inj; [lia | lia | rewrite Nt; lia]). lia. }
  subst s' t'. clear Hen Hex.
  (* the abstract flow facts *)
  set (cF := fun a b => cpx x n (io a) (io b)).
  set (rF := fun a b => RD n (s_tbl S') (io a) (io b)).
  set (eF := fun v => (φ ((s_ex S').[io v]))).
  set (hF := fun v => (φ ((s_h S').[io v]))).
  assert (NL : Z.to_nat (φ n) = L) by lia.
  assert (c_nonneg : forall a b, (0 <= cF a b)%Z) by (intros; apply (cp_rng n 0 0 x Hx')).
  assert (c_sym : forall a b, cF a b = cF b a) by (intros; apply cp_sym).
  assert (r_nonneg : forall a b, (a < L)%nat -> (b < L)%nat -> (0 <= rF a b)%Z)
    by (intros; unfold rF, RD; apply to_Z_bounded).
  assert (r_sym : forall a b, (a < L)%nat -> (b < L)%nat -> (rF a b + rF b a = 2 * cF a b)%Z)
    by (intros a b Ha Hb; apply (t_sym _ _ _ _ _ _ T); apply IL; assumption).
  assert (e_def : forall v, (v < L)%nat -> v <> sn -> eF v = zsum (fun a => (cF a v - rF a v)%Z) L).
  { intros v Hv1 Vs. unfold eF. rewrite (t_ex _ _ _ _ _ _ T); [| apply IL; exact Hv1 |].
    - unfold colsum, isum. rewrite NL. reflexivity.
    - intros E. apply Vs. rewrite <- Ns in E. apply (f_equal to_Z) in E.
      destruct (IL v Hv1) as [_ A]. destruct (IL sn Hsn) as [_ B]. lia. }
  assert (e_nonneg : forall v, (v < L)%nat -> v <> sn -> (0 <= eF v)%Z)
    by (intros; unfold eF; apply to_Z_bounded).
  assert (r_t : forall y, (y < L)%nat -> (cF tn y <= rF tn y)%Z).
  { intros y Hy. unfold cF, rF. rewrite Nt. apply (t_t _ _ _ _ _ _ T). apply IL. exact Hy. }
  assert (h_valid : forall a b, (a < L)%nat -> (b < L)%nat -> (0 < rF a b)%Z -> (hF a <= hF b + 1)%Z)
    by (intros a b Ha Hb Rab; apply (h_valid _ _ _ _ _ Hh); try apply IL; assumption).
  assert (h_s : hF sn = Z.of_nat L) by (unfold hF; rewrite Ns, (h_s _ _ _ _ _ Hh); lia).
  assert (h_t : hF tn = 0%Z) by (unfold hF; rewrite Nt, (h_t _ _ _ _ _ Hh); reflexivity).
  assert (final : forall v, (v < L)%nat -> v <> sn -> v <> tn -> (0 < eF v)%Z -> (Z.of_nat L <= hF v)%Z).
  { intros v Hv1 Vs Vt Pe. destruct (Z_lt_le_dec (hF v) (Z.of_nat L)) as [Lh|Lh]; [|exact Lh].
    exfalso. destruct (IL v Hv1) as [Lv Iv].
    pose proof (NA (io v) Lv) as A. unfold active in A. unfold eF, hF in *.
    assert (Ds : io v <> ss x) by (intro E; apply Vs; rewrite <- Ns in E; apply (f_equal to_Z) in E;
                                   destruct (IL sn Hsn); lia).
    assert (Dt : io v <> tt x) by (intro E; apply Vt; rewrite <- Nt in E; apply (f_equal to_Z) in E;
                                   destruct (IL tn Htn); lia).
    replace (0 <? (s_ex S').[io v]) with true in A by (symmetry; apply ltb_true; exact Pe).
    replace ((s_h S').[io v] <? n) with true in A by (symmetry; apply ltb_true; lia).
    replace (io v =? ss x) with false in A by (symmetry; apply eqb_false; exact Ds).
    replace (io v =? tt x) with false in A by (symmetry; apply eqb_false; exact Dt).
    discriminate A. }
  assert (Cap : forall a b, (a < L)%nat -> (b < L)%nat -> Z.of_N (cap rooms (N.of_nat a) (N.of_nat b)) = cF a b)
    by (intros; apply f_cap; assumption).
  assert (Ans : Z.of_N (Z.to_N (φ ((s_ex S').[tt x]))) = eF tn)
    by (unfold eF; rewrite Nt; apply Z2N.id; apply to_Z_bounded).
  split.
  - destruct (flow_exists L sn tn Hsn Htn Hstn cF c_nonneg c_sym rF r_nonneg r_sym eF e_def e_nonneg r_t)
      as [w [[Wc Wk] Wv]].
    exists (fun i j => Z.to_N (w (N.to_nat i) (N.to_nat j))). split; [split|].
    + intros i j Hi Hj. unfold len in Hi, Hj.
      destruct (Wc (N.to_nat i) (N.to_nat j) ltac:(lia) ltac:(lia)) as [W1 W2].
      rewrite <- (Cap (N.to_nat i) (N.to_nat j)) in W2 by lia. rewrite !Nnat.N2Nat.id in W2. lia.
    + intros v Hv1 Vs Vt. unfold len in Hv1. apply N2Z.inj. unfold outflow, inflow. rewrite !sb_zsum.
      rewrite (zsum_ext _ (fun k => w (N.to_nat v) k)), (zsum_ext (fun k => Z.of_N (Z.to_N (w (N.to_nat (N.of_nat k)) (N.to_nat v)))) (fun k => w k (N.to_nat v))).
      * apply Wk; lia.
      * intros k Hk. rewrite Nnat.Nat2N.id. apply Z2N.id. apply Wc; lia.
      * intros k Hk. rewrite Nnat.Nat2N.id. apply Z2N.id. apply Wc; lia.
    + unfold entering, outflow, inflow. rewrite !sb_zsum, Ans, <- Wv. unfold wvalue.
      rewrite !Nnat.Nat2N.id.
      rewrite (zsum_ext _ (fun k => w sn k)), (zsum_ext (fun k => Z.of_N (Z.to_N (w (N.to_nat (N.of_nat k)) sn))) (fun k => w k sn)).
      * reflexivity.
      * intros k Hk. rewrite Nnat.Nat2N.id. apply Z2N.id. apply Wc; lia.
      * intros k Hk. rewrite Nnat.Nat2N.id. apply Z2N.id. apply Wc; lia.
  - intros W [Wc Wk]. rewrite Ans.
    set (w := fun a b => Z.of_N (W (N.of_nat a) (N.of_nat b))).
    assert (WW : walk L sn tn cF w).
    { split.
      - intros a b Ha Hb. unfold w. rewrite <- Cap by assumption.
        pose proof (Wc (N.of_nat a) (N.of_nat b) ltac:(unfold len; lia) ltac:(unfold len; lia)). lia.
      - intros v Hv1 Vs Vt.
        pose proof (Wk (N.of_nat v) ltac:(unfold len; lia) ltac:(lia) ltac:(lia)) as K.
        unfold outflow, inflow in K. apply (f_equal Z.of_N) in K. rewrite !sb_zsum in K. exact K. }
    pose proof (flow_upper L sn tn Hsn Htn Hstn cF c_sym rF r_nonneg r_sym eF e_def e_nonneg hF
                  h_valid h_s h_t final r_t w WW) as U.
    unfold wvalue in U. unfold entering, outflow, inflow. rewrite !sb_zsum. exact U.
Qed.

End Final.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition mazemovement : array uint -> uint := mazemovement_impl.
Elpi complexity mazemovement.

Definition mazemovement_correct : forall (rooms : list N) (x : array uint),
  valid_input rooms -> repr x rooms ->
  exists ans : N, repr (mazemovement x) ans /\ mazemovement_spec rooms ans
  := fun rooms x Hv Hr => mazemovement_impl_correct rooms x Hv Hr.

(* ================================================================== *)
(* Complexity: see implementation_README.md, "Complexity".            *)
(* ================================================================== *)

From Stdlib Require Finite.


(* ================================================================== *)
(* The amortised analysis of the main loop                             *)
(* ================================================================== *)

Ltac bnorm' :=
  repeat match goal with
  | H : (_ <? _) = true |- _ => apply ltb_true in H
  | H : (_ <? _) = false |- _ => apply ltb_false in H
  | H : (_ <=? _) = true |- _ => apply leb_true in H
  | H : (_ <=? _) = false |- _ => apply leb_false in H
  | H : (_ =? _) = true |- _ => apply eqb_true in H
  | H : (_ =? _) = false |- _ => apply eqb_false in H
  | H : (_ && _) = true |- _ => apply andb_true_iff in H; destruct H
  | H : negb _ = true |- _ => apply negb_true_iff in H
  end.

Ltac zlia := repeat match goal with x := _ |- _ => clearbody x end;
  repeat match goal with
  | H : @eq int _ _ |- _ => clear H
  | H : @eq bool _ _ |- _ => clear H
  | H : @eq (array int) _ _ |- _ => clear H
  | H : _ \/ _ |- _ => clear H
  | H : _ <-> _ |- _ => clear H
  | H : _ -> _ |- _ => clear H
  end; lia.
Ltac bd x := pose proof (to_Z_bounded x).

(* pigeonhole: m distinct cells of [0, N) avoiding w *)
Lemma pigeon_q (N m : Z) (f : Z -> int) (w : int) :
  (0 <= m)%Z -> (φ w < N)%Z ->
  (forall k, (0 <= k < m)%Z -> (φ (f k) < N)%Z /\ f k <> w) ->
  (forall k1 k2, (0 <= k1 < m)%Z -> (0 <= k2 < m)%Z -> f k1 = f k2 -> k1 = k2) ->
  (m + 1 <= N)%Z.
Proof.
  intros Hm Hw Hf Hi.
  set (L := map (fun k => Z.to_nat (φ (f (Z.of_nat k)))) (seq 0 (Z.to_nat m))).
  assert (ND : NoDup (Z.to_nat (φ w) :: L)).
  { constructor.
    - unfold L. rewrite in_map_iff. intros [k [E Hk]]. apply in_seq in Hk.
      destruct (Hf (Z.of_nat k) ltac:(lia)) as [_ Hne]. apply Hne.
      apply to_Z_inj. bd w. bd (f (Z.of_nat k)). lia.
    - unfold L. apply Finite.Injective_map_NoDup_in; [|apply seq_NoDup].
      intros a b Ha Hb E. apply in_seq in Ha, Hb.
      assert (E' : f (Z.of_nat a) = f (Z.of_nat b)).
      { apply to_Z_inj. bd (f (Z.of_nat a)). bd (f (Z.of_nat b)). lia. }
      apply Hi in E'; lia. }
  assert (IN : incl (Z.to_nat (φ w) :: L) (seq 0 (Z.to_nat N))).
  { intros y Hy. apply in_seq. destruct Hy as [<-|Hy]; [bd w; lia|].
    unfold L in Hy. apply in_map_iff in Hy. destruct Hy as [k [<- Hk]]. apply in_seq in Hk.
    destruct (Hf (Z.of_nat k) ltac:(lia)) as [Hl _]. bd (f (Z.of_nat k)). lia. }
  pose proof (NoDup_incl_length ND IN) as Le.
  cbn [List.length] in Le. unfold L in Le. rewrite length_map, !length_seq in Le. lia.
Qed.

Lemma mod_range (x N : Z) : (0 < N)%Z -> (0 <= x < 2 * N)%Z ->
  (x mod N = if (x <? N)%Z then x else x - N)%Z.
Proof.
  intros HN Hx. destruct (x <? N)%Z eqn:E; rewrite ?Z.ltb_lt, ?Z.ltb_ge in E.
  - apply Z.mod_small. lia.
  - rewrite <- (Z.mod_small (x - N) N) by lia.
    replace x with (x - N + 1 * N)%Z at 1 by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma mod_inj (a k m N : Z) : (0 < N)%Z -> (0 <= k < N)%Z -> (0 <= m < N)%Z ->
  ((a + k) mod N = (a + m) mod N)%Z -> k = m.
Proof.
  intros HN Hk Hm E.
  rewrite <- (Zplus_mod_idemp_l a k), <- (Zplus_mod_idemp_l a m) in E.
  pose proof (Z.mod_pos_bound a N HN).
  rewrite (mod_range (a mod N + k)), (mod_range (a mod N + m)) in E by lia.
  destruct (a mod N + k <? N)%Z eqn:E1, (a mod N + m <? N)%Z eqn:E2;
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in E1, E2. all: lia.
Qed.

Section Arith.
Local Open Scope Z_scope.
Lemma arith_push K N P P' Kc Kc' Q Q' s :
  0 <= K -> 0 <= N -> 0 <= s <= 1 ->
  (s = 0 -> P' + 1 <= P) -> P' <= P + N -> Kc' + s <= Kc -> Q' <= Q + 3 ->
  4 * K * P' + 4 * K * (N + 1) * Kc' + K * Q' + K <= 4 * K * P + 4 * K * (N + 1) * Kc + K * Q.
Proof.
  intros HK HN Hs H1 H2 H3 H4.
  assert (E : 4 * (P - P') + 4 * (N + 1) * (Kc - Kc') + (Q - Q') - 1 >= 0).
  { destruct (Z.eq_dec s 0) as [->|Hs1].
    - specialize (H1 eq_refl). nia.
    - assert (s = 1) by lia. subst. nia. }
  nia.
Qed.
Lemma arith_rel K N P P' Kc Kc' H H' C C' Q Q' r r' (gl : bool) :
  0 <= K -> 2 <= N -> 0 <= C -> 0 <= H' ->
  P' + H' <= P + H -> Kc' + 2 * N * H' <= Kc + 2 * N * H -> H' + 1 <= H -> Q' <= Q + 1 ->
  (if gl then C' <= N * N /\ r' = 0 /\ r + 1 = N else C' <= C + N /\ r' = r + 1) ->
  4 * K * P' + 4 * K * (N + 1) * Kc' + 12 * K * (N + 1) * (N + 1) * H' + K * C' + K * Q'
    + 4 * K * (N + 1) * (N + 1) * r'
  + (K * (N + 1) + (if gl then K * (N + 1) * (N + 1) * (N + 1) else 0))
  <= 4 * K * P + 4 * K * (N + 1) * Kc + 12 * K * (N + 1) * (N + 1) * H + K * C + K * Q
    + 4 * K * (N + 1) * (N + 1) * r.
Proof.
  intros HK HN HC HH' H1 H2 H3 H4 H5.
  set (d := H - H').
  assert (Kd : (N + 1) * (Kc - Kc') >= - (N + 1) * 2 * N * d) by (unfold d; nia).
  assert (E : 4 * (P - P') + 4 * (N + 1) * (Kc - Kc') + 12 * (N + 1) * (N + 1) * (H - H') + (C - C')
              + (Q - Q') + 4 * (N + 1) * (N + 1) * (r - r') - (N + 1)
              - (if gl then (N + 1) * (N + 1) * (N + 1) else 0) >= 0).
  { assert (Md : (4 * N * N + 16 * N + 8) * d >= 4 * N * N + 16 * N + 8) by (unfold d in *; nia).
    destruct gl; destruct H5 as [H5 H6]; [destruct H6 as [H6 H7]|].
    - subst r'. assert (r = N - 1) by lia. subst r.
      unfold d in *. nia.
    - subst r'. unfold d in *. nia. }
  destruct gl; nia.
Qed.
End Arith.

Section Pot.

Variables (n s t : int) (cp : int -> int -> Z).
Hypothesis Hn : (2 <= φ n <= 1000)%Z.
Hypothesis Hs : (φ s < φ n)%Z.
Hypothesis Ht : (φ t < φ n)%Z.
Hypothesis Hst : s <> t.
Hypothesis Hcp : forall a b, (0 <= cp a b <= 2147483648)%Z.
Variable K : Z.
Hypothesis HK : (0 <= K)%Z.

Local Notation lt a := (φ a < φ n)%Z.
Local Notation N := (φ n).

(* wrappers of the sums *)
Lemma Iext F G : (forall y, lt y -> F y = G y) -> isum n F = isum n G.
Proof. apply (isum_ext n s t Hn Hst). Qed.
Lemma Ile F G : (forall y, lt y -> (F y <= G y)%Z) -> (isum n F <= isum n G)%Z.
Proof. apply (isum_le n s t Hn Hst). Qed.
Lemma Inonneg F : (forall y, lt y -> (0 <= F y)%Z) -> (0 <= isum n F)%Z.
Proof. apply (isum_nonneg n s t Hn Hst). Qed.
Lemma Ibound F c : (forall y, lt y -> (F y <= c)%Z) -> (isum n F <= N * c)%Z.
Proof. apply (isum_bound n s t Hn Hst). Qed.
Lemma Ipoint F G u : lt u -> (forall y, lt y -> y <> u -> F y = G y) ->
  isum n F = (isum n G + (F u - G u))%Z.
Proof. apply (isum_point n s t Hn Hst). Qed.
Lemma Ipoint2 F G u v : lt u -> lt v -> u <> v ->
  (forall y, lt y -> y <> u -> y <> v -> F y = G y) ->
  isum n F = (isum n G + (F u - G u) + (F v - G v))%Z.
Proof. apply (isum_point2 n s t Hn Hst). Qed.
Lemma Iadd F G : isum n (fun y => F y + G y)%Z = (isum n F + isum n G)%Z.
Proof. unfold isum. apply zsum_add. Qed.
Lemma Isub F G : isum n (fun y => F y - G y)%Z = (isum n F - isum n G)%Z.
Proof. unfold isum. apply zsum_sub. Qed.
Lemma Iconst c : isum n (fun _ => c) = (N * c)%Z.
Proof.
  unfold isum. assert (forall k, zsum (fun _ => c) k = Z.of_nat k * c)%Z.
  { induction k; cbn [zsum]; lia. }
  rewrite H. f_equal. lia.
Qed.
Lemma Ilt_pt F G u c : lt u -> (forall y, lt y -> (F y <= G y)%Z) -> (F u + c <= G u)%Z ->
  (isum n F + c <= isum n G)%Z.
Proof.
  intros Hu Le Lt.
  set (M := fun y => if y =? u then F u else G y).
  rewrite (Ipoint G M u Hu).
  2:{ intros y Hy Hne. unfold M. replace (y =? u) with false by (symmetry; apply eqb_false; exact Hne). reflexivity. }
  assert (isum n F <= isum n M)%Z.
  { apply Ile. intros y Hy. unfold M. destruct (y =? u) eqn:E; bnorm'; [subst; lia | apply Le; exact Hy]. }
  unfold M at 2. rewrite eqb_refl. lia.
Qed.

(* ---- the potential ---- *)

Definition phv (ex h : array int) (v : int) : Z :=
  if (v =? s) || (v =? t) then 0%Z else if (0 <? φ ex.[v])%Z then φ h.[v] else 0%Z.
Definition mPhi (S : st) : Z := isum n (phv (s_ex S) (s_h S)).
Definition kind (tbl h : array int) (a b : int) : Z :=
  if (0 <? RD n tbl a b)%Z && (φ h.[b] <? φ h.[a])%Z then 1%Z else 0%Z.
Definition mK (S : st) : Z := isum n (fun a => isum n (fun b => kind (s_tbl S) (s_h S) a b)).

Definition Pot (S : st) : Z :=
  (4 * K * mPhi S + 4 * K * (N + 1) * mK S + 12 * K * (N + 1) * (N + 1) * mH n S
   + K * mC n S + K * mQ n S + 4 * K * (N + 1) * (N + 1) * φ (s_rl S))%Z.

Definition scost (S : st) : Z :=
  if (s_cu S <? n)%uint63 then
    (if ((s_cur S).[s_cu S] <? n)%uint63 then K
     else (K * (N + 1) + (if (n <=? s_rl S + 1)%uint63 then K * (N + 1) * (N + 1) * (N + 1) else 0))%Z)
  else K.

(* ---- the queue ---- *)

Definition qpos (qh : int) (k : Z) : int := of_Z ((φ qh + k) mod N).

Record QOK (S : st) : Prop := {
  q_len : PArray.length (s_q S) = n;
  q_qh : lt (s_qh S);
  q_ql : (φ (s_ql S) <= N)%Z;
  q_ent : forall k, (0 <= k < φ (s_ql S))%Z ->
    let v := (s_q S).[qpos (s_qh S) k] in
    lt v /\ (0 < φ (s_ex S).[v])%Z /\ v <> s /\ v <> t /\ v <> s_cu S;
  q_nodup : forall k1 k2, (0 <= k1 < φ (s_ql S))%Z -> (0 <= k2 < φ (s_ql S))%Z ->
    (s_q S).[qpos (s_qh S) k1] = (s_q S).[qpos (s_qh S) k2] -> k1 = k2;
  q_all : forall v, lt v -> active (s_ex S) (s_h S) n s t v = true ->
    v = s_cu S \/ exists k, (0 <= k < φ (s_ql S))%Z /\ (s_q S).[qpos (s_qh S) k] = v;
  q_rl : lt (s_rl S) }.

Lemma qpos_spec qh k : lt qh -> (0 <= k)%Z -> φ (qpos qh k) = ((φ qh + k) mod N)%Z.
Proof.
  intros Hq Hk. unfold qpos. rewrite of_Z_spec. apply Z.mod_small.
  pose proof (Z.mod_pos_bound (φ qh + k) N ltac:(lia)). rewrite wB_val. lia.
Qed.

Lemma qpos_lt qh k : lt qh -> (0 <= k)%Z -> lt (qpos qh k).
Proof. intros. rewrite qpos_spec by assumption. apply Z.mod_pos_bound. lia. Qed.

Lemma qpos_inj qh k m : lt qh -> (0 <= k < N)%Z -> (0 <= m < N)%Z -> qpos qh k = qpos qh m -> k = m.
Proof.
  intros Hq Hk Hm E. apply (f_equal to_Z) in E. rewrite !qpos_spec in E by lia.
  apply (mod_inj (φ qh) k m N); lia.
Qed.

Lemma qpos_0 qh : lt qh -> qpos qh 0 = qh.
Proof.
  intros Hq. apply to_Z_inj. rewrite qpos_spec by lia. rewrite Z.add_0_r. bd qh. apply Z.mod_small. lia.
Qed.

Lemma qpos_next qh k : lt qh -> (0 <= k)%Z ->
  qpos (if qh + 1 =? n then 0 else qh + 1) k = qpos qh (k + 1).
Proof.
  intros Hq Hk. bd qh. assert (E1 : φ (qh + 1) = (φ qh + 1)%Z) by (apply (succ_lt qh n); exact Hq).
  apply to_Z_inj. rewrite (qpos_spec qh) by lia.
  destruct (qh + 1 =? n) eqn:E; bnorm'.
  - rewrite qpos_spec by (change (φ 0) with 0%Z; lia). change (φ 0) with 0%Z.
    apply (f_equal to_Z) in E. rewrite E1 in E.
    replace (φ qh + (k + 1))%Z with (k + 1 * N)%Z by lia. rewrite Z.mod_add by lia.
    try (f_equal; lia).
  - assert (lt (qh + 1)) by (assert (φ (qh + 1) <> N) by (intro X; apply E, to_Z_inj; exact X); lia).
    rewrite qpos_spec by lia. rewrite E1. try (f_equal; lia).
Qed.

Lemma enq_qpos qh ql : lt qh -> (0 <= φ ql < N)%Z -> enq_pos qh ql n = qpos qh (φ ql).
Proof.
  intros Hq Hl. apply to_Z_inj. rewrite qpos_spec by lia. unfold enq_pos.
  bd qh. bd ql.
  assert (E1 : φ (qh + ql) = (φ qh + φ ql)%Z) by (apply add_nowrap; rewrite wB_val; lia).
  rewrite mod_range by lia.
  destruct (qh + ql <? n) eqn:E; bnorm'.
  - replace ((φ qh + φ ql <? N)%Z) with true by lia. exact E1.
  - replace ((φ qh + φ ql <? N)%Z) with false by lia. rewrite sub_nowrap by lia. lia.
Qed.


Lemma enq_read (q : array int) (qh ql v : int) (k : Z) : PArray.length q = n -> lt qh -> (0 <= φ ql < N)%Z -> (0 <= k <= φ ql)%Z ->
  (q.[enq_pos qh ql n <- v]).[qpos qh k] = if (k =? φ ql)%Z then v else q.[qpos qh k].
Proof.
  intros Lq Hq Hl Hk. rewrite enq_qpos by assumption.
  rewrite get_set1 by (rewrite Lq; apply qpos_lt; lia).
  destruct (k =? φ ql)%Z eqn:E; rewrite ?Z.eqb_eq, ?Z.eqb_neq in E.
  - subst k. rewrite eqb_refl. reflexivity.
  - destruct (qpos qh k =? qpos qh (φ ql)) eqn:E2; bnorm'; [|reflexivity].
    apply qpos_inj in E2; lia.
Qed.

Lemma ind_cases b z : ind b z = (if b then z else 0)%Z.
Proof. reflexivity. Qed.

(* the push step *)
Lemma push_case tbl ex h cur cnt q qh ql cu rl :
  Inv n s t cp (mkst tbl ex h cur cnt q qh ql cu rl) ->
  QOK (mkst tbl ex h cur cnt q qh ql cu rl) ->
  (cu <? n) = true -> (cur.[cu] <? n) = true -> adm tbl h n cu cur.[cu] = true ->
  let v := cur.[cu] in
  let d := if ex.[cu] <? tbl.[cu * n + v] then ex.[cu] else tbl.[cu * n + v] in
  let tbl2 := tbl.[cu * n + v <- tbl.[cu * n + v] - d].[v * n + cu <- tbl.[cu * n + v <- tbl.[cu * n + v] - d].[v * n + cu] + d] in
  let ex2 := ex.[cu <- ex.[cu] - d].[v <- ex.[v] + d] in
  let b := (ex.[v] =? 0) && negb (v =? t) && negb (v =? s) && (ql <? n) in
  let q1 := if b then q.[enq_pos qh ql n <- v] else q in
  let ql1 := if b then ql + 1 else ql in
  let cu1 := if ex.[cu] - d =? 0 then n else cu in
  QOK (mkst tbl2 ex2 h cur cnt q1 qh ql1 cu1 rl) /\
  (mPhi (mkst tbl2 ex2 h cur cnt q1 qh ql1 cu1 rl) <= mPhi (mkst tbl ex h cur cnt q qh ql cu rl) + N)%Z /\
  ((ex.[cu] <? tbl.[cu * n + v])%uint63 = true ->
     mPhi (mkst tbl2 ex2 h cur cnt q1 qh ql1 cu1 rl) + 1 <= mPhi (mkst tbl ex h cur cnt q qh ql cu rl))%Z /\
  (mK (mkst tbl2 ex2 h cur cnt q1 qh ql1 cu1 rl)
     + (if (ex.[cu] <? tbl.[cu * n + v])%uint63 then 0 else 1) <= mK (mkst tbl ex h cur cnt q qh ql cu rl))%Z /\
  (mQ n (mkst tbl2 ex2 h cur cnt q1 qh ql1 cu1 rl) <= mQ n (mkst tbl ex h cur cnt q qh ql cu rl) + 3)%Z.
Proof.
  intros I Q H1 H2 H3 v d tbl2 ex2 b q1 ql1 cu1.
  change (cur.[cu]) with v in H2, H3.
  destruct I as [T [Hh [Hc Hu]]]; cbn [s_tbl s_ex s_h s_cur s_cu s_ql] in T, Hh, Hc, Hu.
  destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6 Q7]; cbn [s_q s_qh s_ql s_ex s_h s_cu s_rl] in Q1, Q2, Q3, Q4, Q5, Q6, Q7.
  set (tbl1 := tbl.[cu * n + v <- tbl.[cu * n + v] - d]) in *.
  set (ex1 := ex.[cu <- ex.[cu] - d]) in *.
  pose proof H1 as L1. apply ltb_true in L1. pose proof H2 as L2. apply ltb_true in L2.
  unfold adm in H3. apply andb_true_iff in H3. destruct H3 as [A1 A2].
  apply ltb_true in A1. apply eqb_true in A2. change (φ 0) with 0%Z in A1.
  destruct (Hu L1) as [U1 [U2 [U3 U4]]].
  assert (Ah : (φ (h.[cu])) = ((φ (h.[v])) + 1)%Z) by (rewrite A2; apply (hp1 n s t Hn Hst tbl h v Hh L2)).
  assert (Uv : cu <> v) by (intro E; rewrite <- E in Ah; zlia).
  assert (Vs : v <> s) by (intro E; pose proof (h_s _ _ _ _ _ Hh) as X; rewrite <- E in X; zlia).
  assert (Dd : (φ d) = Z.min (φ (ex.[cu])) (φ (tbl.[cu * n + v]))).
  { unfold d. destruct (ex.[cu] <? tbl.[cu * n + v]) eqn:E; bnorm'; zlia. }
  destruct (push_tab n s t cp Hn Ht Hst Hcp tbl ex cu v d tbl1 tbl2 ex1 ex2 T L1 L2 Uv U3 Vs U4
              ltac:(zlia) ltac:(unfold RD; zlia) ltac:(zlia) eq_refl eq_refl eq_refl eq_refl)
    as [T2 [RDf EXf]].
  assert (EXo : forall y, y <> cu -> y <> v -> ex2.[y] = ex.[y]).
  { intros y Y1 Y2. apply to_Z_inj. rewrite EXf. rewrite !ind_cases.
    replace (y =? cu) with false by (symmetry; apply eqb_false; exact Y1).
    replace (y =? v) with false by (symmetry; apply eqb_false; exact Y2). zlia. }
  assert (EXcu : φ ex2.[cu] = (φ ex.[cu] - φ d)%Z).
  { rewrite EXf, !ind_cases, eqb_refl. replace (cu =? v) with false by (symmetry; apply eqb_false; exact Uv). zlia. }
  assert (EXv : φ ex2.[v] = (φ ex.[v] + φ d)%Z).
  { rewrite EXf, !ind_cases, eqb_refl. replace (v =? cu) with false by (symmetry; apply eqb_false; congruence). zlia. }
  assert (EXge : forall y, y <> cu -> (φ ex.[y] <= φ ex2.[y])%Z).
  { intros y Y. rewrite EXf, !ind_cases. replace (y =? cu) with false by (symmetry; apply eqb_false; exact Y).
    destruct (y =? v); zlia. }
  pose proof (h_le _ _ _ _ _ Hh) as Hle.
  assert (Ecu1 : (cu1 = n /\ φ ex2.[cu] = 0%Z) \/ (cu1 = cu /\ (0 < φ ex2.[cu])%Z)).
  { unfold cu1. destruct (ex.[cu] - d =? 0) eqn:E; bnorm'.
    - left. split; [reflexivity|]. rewrite EXcu. apply (f_equal to_Z) in E. rewrite sub_nowrap in E by zlia.
      change (φ 0) with 0%Z in E. zlia.
    - right. split; [reflexivity|]. rewrite EXcu.
      assert (φ (ex.[cu] - d) <> 0%Z) by (intro X; apply E, to_Z_inj; exact X).
      rewrite sub_nowrap in H by zlia. zlia. }
  (* the queue *)
  assert (Bql : φ ex.[v] = 0%Z -> v <> t -> (φ ql + 1 <= N)%Z).
  { intros E0 Vt. apply (pigeon_q N (φ ql) (fun k => q.[qpos qh k]) v); [bd ql; zlia | exact L2 | |].
    - intros k Hk. destruct (Q4 k Hk) as [W1 [W2 _]]. split; [exact W1|].
      intro X. rewrite X in W2. zlia.
    - intros k1 k2 Hk1 Hk2 E. apply (Q5 k1 k2 Hk1 Hk2 E). }
  assert (Bv : b = true <-> (φ ex.[v] = 0%Z /\ v <> t)).
  { unfold b. split.
    - intros B. apply andb_true_iff in B as [B B4]. apply andb_true_iff in B as [B B3].
      apply andb_true_iff in B as [B1 B2]. apply eqb_true in B1. apply negb_true_iff, eqb_false in B2.
      split; [rewrite B1; reflexivity | exact B2].
    - intros [E0 Vt]. specialize (Bql E0 Vt).
      assert (E0' : ex.[v] = 0) by (apply to_Z_inj; exact E0).
      rewrite E0', eqb_refl. replace (v =? t) with false by (symmetry; apply eqb_false; exact Vt).
      replace (v =? s) with false by (symmetry; apply eqb_false; exact Vs).
      replace (ql <? n) with true by (symmetry; apply ltb_true; zlia). reflexivity. }
  assert (Bq : b = true -> (φ ql < N)%Z) by (intros B; apply Bv in B; destruct B as [B1 B2]; specialize (Bql B1 B2); clear - Bql; zlia).
  assert (Eql1 : φ ql1 = (φ ql + (if b then 1 else 0))%Z).
  { unfold ql1. destruct b eqn:B.
    - apply add_nowrap. specialize (Bq eq_refl). rewrite wB_val. change (φ 1) with 1%Z. zlia.
    - zlia. }
  assert (Rq1 : forall k, (0 <= k < φ ql1)%Z ->
      q1.[qpos qh k] = if (b && (k =? φ ql)%Z)%bool then v else q.[qpos qh k]).
  { intros k Hk. unfold q1. destruct b eqn:B; [|reflexivity]. cbn [andb].
    specialize (Bq eq_refl). apply enq_read; try assumption; bd ql; zlia. }
  assert (Pcu : phv ex h cu = φ h.[cu]).
  { unfold phv. replace (cu =? s) with false by (symmetry; apply eqb_false; exact U3).
    replace (cu =? t) with false by (symmetry; apply eqb_false; exact U4). cbn [orb].
    destruct (Z.ltb_spec 0 (φ ex.[cu])); zlia. }
  assert (Pcu2 : (0 <= phv ex2 h cu <= φ h.[cu])%Z).
  { unfold phv. replace (cu =? s) with false by (symmetry; apply eqb_false; exact U3).
    replace (cu =? t) with false by (symmetry; apply eqb_false; exact U4). cbn [orb].
    bd h.[cu]. destruct (Z.ltb_spec 0 (φ ex2.[cu])); zlia. }
  assert (Pcu3 : (ex.[cu] <? tbl.[cu * n + v]) = true -> phv ex2 h cu = 0%Z).
  { intros NS. assert (Dd2 : φ d = φ ex.[cu]) by (unfold d; rewrite NS; reflexivity).
    unfold phv. replace (cu =? s) with false by (symmetry; apply eqb_false; exact U3).
    replace (cu =? t) with false by (symmetry; apply eqb_false; exact U4). cbn [orb].
    destruct (Z.ltb_spec 0 (φ ex2.[cu])); zlia. }
  assert (Pv : (0 <= phv ex h v)%Z /\ (phv ex2 h v - phv ex h v <= φ h.[v])%Z).
  { unfold phv. replace (v =? s) with false by (symmetry; apply eqb_false; exact Vs). cbn [orb].
    bd h.[v]. destruct (v =? t); [zlia|].
    destruct (Z.ltb_spec 0 (φ ex2.[v])), (Z.ltb_spec 0 (φ ex.[v])); zlia. }
  pose proof (Hle v L2) as Hlev.
  assert (EPhi : mPhi (mkst tbl2 ex2 h cur cnt q1 qh ql1 cu1 rl) =
     (mPhi (mkst tbl ex h cur cnt q qh ql cu rl) + (phv ex2 h cu - phv ex h cu) + (phv ex2 h v - phv ex h v))%Z).
  { unfold mPhi. cbn [s_ex s_h]. apply (Ipoint2 (phv ex2 h) (phv ex h) cu v L1 L2 Uv).
    intros y Hy Y1 Y2. unfold phv. rewrite (EXo y Y1 Y2). reflexivity. }
  split; [|split; [|split; [|split]]].
  - (* QOK *)
    assert (R : forall k, (0 <= k < φ ql1)%Z ->
       ((0 <= k < φ ql)%Z /\ q1.[qpos qh k] = q.[qpos qh k]) \/ (k = φ ql /\ b = true /\ q1.[qpos qh k] = v)).
    { intros k Hk. rewrite (Rq1 k Hk). rewrite Eql1 in Hk. destruct b eqn:B; cbn [andb].
      - destruct (k =? φ ql)%Z eqn:E.
        + right. rewrite Z.eqb_eq in E. auto.
        + left. rewrite Z.eqb_neq in E. split; [zlia|reflexivity].
      - left. split; [zlia|reflexivity]. }
    assert (Rold : forall k, (0 <= k < φ ql)%Z -> (0 <= k < φ ql1)%Z /\ q1.[qpos qh k] = q.[qpos qh k]).
    { intros k Hk. assert (Hk' : (0 <= k < φ ql1)%Z) by (rewrite Eql1; destruct b; zlia).
      split; [exact Hk'|]. destruct (R k Hk') as [[_ X]|[X _]]; [exact X | zlia]. }
    assert (Ecu1' : cu1 = n \/ cu1 = cu) by (destruct Ecu1 as [[X _]|[X _]]; [left|right]; exact X).
    split; cbn [s_q s_qh s_ql s_ex s_h s_cu s_rl].
    + unfold q1. destruct b; [rewrite alength_set|]; exact Q1.
    + exact Q2.
    + rewrite Eql1. destruct b eqn:B; [specialize (Bq eq_refl)|]; zlia.
    + intros k Hk. cbv zeta. destruct (R k Hk) as [[Hk' ->]|[-> [B ->]]].
      * destruct (Q4 k Hk') as [W1 [W2 [W3 [W4 W5]]]].
        split; [exact W1|]. split; [pose proof (EXge _ W5); zlia|]. split; [exact W3|]. split; [exact W4|].
        destruct Ecu1' as [->| ->]; [intro X; rewrite X in W1; zlia | exact W5].
      * apply Bv in B. destruct B as [E0 Vt].
        split; [exact L2|]. split; [rewrite EXv; zlia|]. split; [exact Vs|]. split; [exact Vt|].
        destruct Ecu1' as [->| ->]; [intro X; rewrite X in L2; zlia | congruence].
    + intros k1 k2 Hk1 Hk2 E.
      destruct (R k1 Hk1) as [[Hk1' E1]|[K1 [B1 E1]]], (R k2 Hk2) as [[Hk2' E2]|[K2 [B2 E2]]];
        rewrite E1, E2 in E.
      * exact (Q5 k1 k2 Hk1' Hk2' E).
      * exfalso. apply Bv in B2. destruct B2 as [E0 _]. destruct (Q4 k1 Hk1') as [_ [W2 _]]. rewrite E in W2. zlia.
      * exfalso. apply Bv in B1. destruct B1 as [E0 _]. destruct (Q4 k2 Hk2') as [_ [W2 _]]. rewrite <- E in W2. zlia.
      * zlia.
    + intros w Hw A. apply (active_iff n s t Hn) in A. destruct A as [A1' [A2' [A3' A4']]].
      destruct (Z.eq_dec (φ w) (φ cu)) as [Ew|Ew].
      * apply to_Z_inj in Ew. subst w. left. destruct Ecu1 as [[_ X]|[-> _]]; [zlia | reflexivity].
      * assert (Ew' : w <> cu) by (intro X; apply Ew; rewrite X; reflexivity).
        right. destruct (Z.eq_dec (φ w) (φ v)) as [Ev|Ev].
        -- apply to_Z_inj in Ev. subst w.
           destruct (Z.eq_dec (φ ex.[v]) 0) as [E0|E0].
           ++ assert (B : b = true) by (apply Bv; split; assumption).
              assert (Hk : (0 <= φ ql < φ ql1)%Z) by (rewrite Eql1, B; bd ql; zlia).
              exists (φ ql). split; [exact Hk|].
              destruct (R _ Hk) as [[X _]|[_ [_ X]]]; [zlia | exact X].
           ++ assert (Aw : active ex h n s t v = true).
              { unfold active. bd ex.[v]. apply andb_true_iff; split; [apply andb_true_iff; split; [apply andb_true_iff; split|]|].
                - apply ltb_true. change (φ 0) with 0%Z. zlia.
                - apply ltb_true. exact A2'.
                - apply negb_true_iff, eqb_false. exact A3'.
                - apply negb_true_iff, eqb_false. exact A4'. }
              destruct (Q6 v L2 Aw) as [X|[k [Hk Ek]]]; [congruence|].
              exists k. destruct (Rold k Hk) as [Hk' Ek']. split; [exact Hk'|]. rewrite Ek'. exact Ek.
        -- assert (Ev' : w <> v) by (intro X; apply Ev; rewrite X; reflexivity).
           assert (Aw : active ex h n s t w = true).
           { unfold active. rewrite <- (EXo w Ew' Ev'). bd ex2.[w].
             apply andb_true_iff; split; [apply andb_true_iff; split; [apply andb_true_iff; split|]|].
             - apply ltb_true. change (φ 0) with 0%Z. zlia.
             - apply ltb_true. exact A2'.
             - apply negb_true_iff, eqb_false. exact A3'.
             - apply negb_true_iff, eqb_false. exact A4'. }
           destruct (Q6 w Hw Aw) as [X|[k [Hk Ek]]]; [congruence|].
           exists k. destruct (Rold k Hk) as [Hk' Ek']. split; [exact Hk'|]. rewrite Ek'. exact Ek.
    + exact Q7.
  - (* Phi, general *)
    rewrite EPhi. zlia.
  - (* Phi, non-saturating *)
    intros NS. rewrite EPhi. specialize (Pcu3 NS). zlia.
  - (* kinds *) 
    unfold mK. cbn [s_tbl s_h].
    assert (Kle : forall a b0, lt a -> lt b0 -> (kind tbl2 h a b0 <= kind tbl h a b0)%Z).
    { intros a b0 Ha Hb. unfold kind. rewrite RDf by assumption. rewrite !ind_cases.
      assert (Dpos : (0 <= φ d)%Z) by (bd d; zlia).
      destruct ((a =? v) && (b0 =? cu)) eqn:E2.
      - apply andb_true_iff in E2. destruct E2 as [Ea Eb]. apply eqb_true in Ea, Eb. subst a b0.
        replace (φ h.[cu] <? φ h.[v])%Z with false by (symmetry; apply Z.ltb_ge; zlia).
        rewrite !andb_false_r. zlia.
      - change (if false then φ d else 0%Z) with 0%Z. rewrite Z.add_0_r.
        assert (Le : (RD n tbl a b0 - (if ((a =? cu) && (b0 =? v))%uint63 then φ d else 0) <= RD n tbl a b0)%Z)
          by (destruct ((a =? cu) && (b0 =? v))%uint63; zlia).
        revert Le. generalize (RD n tbl a b0 - (if ((a =? cu) && (b0 =? v))%uint63 then φ d else 0))%Z.
        intros X Le.
        destruct (Z.ltb_spec 0 X), (Z.ltb_spec 0 (RD n tbl a b0)); cbn [andb]; try zlia;
        destruct (φ h.[b0] <? φ h.[a])%Z; zlia. }
    assert (Kcu : (kind tbl2 h cu v + (if (ex.[cu] <? tbl.[cu * n + v])%uint63 then 0 else 1) <= kind tbl h cu v)%Z).
    { unfold kind. rewrite RDf by assumption. rewrite !ind_cases, !eqb_refl.
      replace (cu =? v) with false by (symmetry; apply eqb_false; exact Uv). cbn [andb].
      unfold RD. replace (0 <? φ tbl.[cu * n + v])%Z with true by (symmetry; apply Z.ltb_lt; exact A1).
      replace (φ h.[v] <? φ h.[cu])%Z with true by (symmetry; apply Z.ltb_lt; zlia). cbn [andb].
      destruct (ex.[cu] <? tbl.[cu * n + v]) eqn:E; bnorm'.
      - repeat match goal with |- context [(?a <? ?b)%Z] => destruct (Z.ltb_spec a b) end; cbn [andb]; zlia.
      - replace (φ d) with (φ tbl.[cu * n + v]) by zlia.
        replace (0 <? φ tbl.[cu * n + v] - φ tbl.[cu * n + v] + 0)%Z with false by (symmetry; apply Z.ltb_ge; zlia). cbn [andb]. zlia. }
    apply (Ilt_pt _ _ cu); [exact L1 | intros a Ha; apply Ile; intros b0 Hb; apply Kle; assumption |].
    apply (Ilt_pt _ _ v); [exact L2 | intros b0 Hb; apply Kle; assumption | exact Kcu].
  - (* the queue measure *) 
    unfold mQ. cbn [s_ql s_cu]. rewrite H1, Eql1.
    destruct b; destruct (cu1 <? n); zlia.
Qed.

Lemma adv_case tbl ex h cur cnt q qh ql cu rl :
  Inv n s t cp (mkst tbl ex h cur cnt q qh ql cu rl) ->
  QOK (mkst tbl ex h cur cnt q qh ql cu rl) ->
  (cu <? n) = true -> (cur.[cu] <? n) = true ->
  QOK (mkst tbl ex h (cur.[cu <- cur.[cu] + 1]) cnt q qh ql cu rl) /\
  (mC n (mkst tbl ex h (cur.[cu <- cur.[cu] + 1])%uint63 cnt q qh ql cu rl) + 1
     <= mC n (mkst tbl ex h cur cnt q qh ql cu rl))%Z.
Proof.
  intros I Q H1 H2. destruct I as [T [Hh [Hc Hu]]]; cbn [s_tbl s_ex s_h s_cur s_cu s_ql] in T, Hh, Hc, Hu.
  split.
  - destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6 Q7]. split; assumption.
  - apply ltb_true in H1. apply ltb_true in H2.
    pose proof (c_len _ _ _ _ Hc) as Lc.
    assert (Gc : forall y, cur.[cu <- cur.[cu] + 1].[y] = if y =? cu then cur.[cu] + 1 else cur.[y])
      by (intros; apply get_set1; rewrite Lc; exact H1).
    assert (V1 : (φ (cur.[cu] + 1)) = ((φ cur.[cu]) + 1)%Z) by (apply (succ_lt _ n); exact H2).
    unfold mC. cbn [s_cur]. apply (Ilt_pt _ _ cu); [exact H1| |].
    + intros y Hy. rewrite Gc. destruct (y =? cu) eqn:E; bnorm'; [subst; zlia | zlia].
    + rewrite Gc, eqb_refl. zlia.
Qed.

Lemma pop_case tbl ex h cur cnt q qh ql cu rl :
  QOK (mkst tbl ex h cur cnt q qh ql cu rl) ->
  (cu <? n) = false -> (0 <? ql) = true ->
  let v := q.[qh] in
  let qh1 := if qh + 1 =? n then 0 else qh + 1 in
  let cu1 := if (v <? n) && active ex h n s t v then v else n in
  QOK (mkst tbl ex h cur cnt q qh1 (ql - 1) cu1 rl) /\
  (mQ n (mkst tbl ex h cur cnt q qh1 (ql - 1)%uint63 cu1 rl) + 2 <= mQ n (mkst tbl ex h cur cnt q qh ql cu rl))%Z.
Proof.
  intros Q H1 H4 v qh1 cu1.
  destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6 Q7]; cbn [s_q s_qh s_ql s_ex s_h s_cu s_rl] in Q1, Q2, Q3, Q4, Q5, Q6, Q7.
  apply ltb_false in H1. apply ltb_true in H4. change (φ 0) with 0%Z in H4.
  assert (Eql : φ (ql - 1) = (φ ql - 1)%Z) by (apply sub_nowrap; change (φ 1) with 1%Z; zlia).
  assert (Hqh1 : lt qh1).
  { unfold qh1. destruct (qh + 1 =? n) eqn:E; bnorm'; [change (φ 0) with 0%Z; zlia|].
    pose proof (succ_lt qh n Q2). assert (φ (qh + 1) <> N) by (intro X; apply E, to_Z_inj; exact X). zlia. }
  assert (Sh : forall k, (0 <= k)%Z -> q.[qpos qh1 k] = q.[qpos qh (k + 1)])
    by (intros k Hk; unfold qh1; rewrite qpos_next by assumption; reflexivity).
  assert (V0 : v = q.[qpos qh 0]) by (unfold v; rewrite qpos_0 by exact Q2; reflexivity).
  assert (Ecu1 : cu1 = n \/ cu1 = v) by (unfold cu1; destruct (_ && _)%bool; [right|left]; reflexivity).
  split.
  - split; cbn [s_q s_qh s_ql s_ex s_h s_cu s_rl].
    + exact Q1.
    + exact Hqh1.
    + zlia.
    + intros k Hk. rewrite Eql in Hk. cbv zeta. rewrite Sh by zlia.
      destruct (Q4 (k + 1)%Z ltac:(zlia)) as [W1 [W2 [W3 [W4 _]]]].
      split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|].
      destruct Ecu1 as [->| ->]; [intro X; rewrite X in W1; zlia|].
      rewrite V0. intro X. apply Q5 in X; zlia.
    + intros k1 k2 Hk1 Hk2 E. rewrite Eql in Hk1, Hk2. rewrite !Sh in E by zlia.
      apply Q5 in E; zlia.
    + intros w Hw A. destruct (Q6 w Hw A) as [X|[k [Hk Ek]]].
      * exfalso. subst w. zlia.
      * destruct (Z.eq_dec k 0) as [->|Kn].
        -- left. rewrite <- V0 in Ek. subst w. unfold cu1.
           replace (v <? n) with true by (symmetry; apply ltb_true; exact Hw). rewrite A. reflexivity.
        -- right. exists (k - 1)%Z. split; [zlia|]. rewrite Sh by zlia.
           replace (k - 1 + 1)%Z with k by zlia. exact Ek.
    + exact Q7.
  - unfold mQ. cbn [s_ql s_cu]. rewrite Eql.
    replace (cu <? n) with false by (symmetry; apply ltb_false; exact H1).
    destruct (cu1 <? n); zlia.
Qed.

Lemma scan_case tbl ex h cur cnt q qh ql cu rl :
  QOK (mkst tbl ex h cur cnt q qh ql cu rl) ->
  (cu <? n) = false -> (0 <? ql) = false ->
  (find_act ex h n s t 0 (wf0 n 0) <? n) = true -> False.
Proof.
  intros Q H1 H4 H5. destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6 Q7]; cbn [s_q s_qh s_ql s_ex s_h s_cu s_rl] in *.
  apply ltb_false in H1, H4. apply ltb_true in H5. change (φ 0) with 0%Z in H4.
  destruct (find_act_spec ex h n s t _ 0 (wf0 n 0) eq_refl) as [F1 _].
  specialize (F1 H5).
  destruct (Q6 _ H5 F1) as [X|[k [Hk _]]].
  - rewrite X in H5. zlia.
  - zlia.
Qed.

Definition relS (tbl ex h cur cnt q : array int) (qh ql cu rl : int) : st :=
  let oh := h.[cu] in
  let nh := rmin tbl n cu h 0 n (wf0 n 0) in
  let h1 := h.[cu <- nh] in
  let cur1 := cur.[cu <- 0] in
  let co := cnt.[oh] - 1 in
  let cnt1 := cnt.[oh <- co] in
  let cnt2 := cnt1.[nh <- cnt1.[nh] + 1] in
  let g := (co =? 0) && (0 <? oh) && (oh <? n) && no_height h1 n oh 0 (wf0 n 0) in
  let cnt3 := if g then cnt_lift h1 cnt2 n oh 0 (wf0 n 0) else cnt2 in
  let h2 := if g then lift h1 n oh else h1 in
  let rl1 := rl + 1 in
  let gl := n <=? rl1 in
  let h3 := if gl then glob tbl n t h2 else h2 in
  let cur2 := if gl then PArray.make n 0 else cur1 in
  let cnt4 := if gl then count h3 n else cnt3 in
  let rl2 := if gl then 0 else rl1 in
  let cu1 := if h3.[cu] <? n then cu else n in
  mkst tbl ex h3 cur2 cnt4 q qh ql cu1 rl2.

Lemma rel_case tbl ex h cur cnt q qh ql cu rl :
  Inv n s t cp (mkst tbl ex h cur cnt q qh ql cu rl) ->
  QOK (mkst tbl ex h cur cnt q qh ql cu rl) ->
  (cu <? n) = true -> (cur.[cu] <? n) = false ->
  let S := mkst tbl ex h cur cnt q qh ql cu rl in
  let S' := relS tbl ex h cur cnt q qh ql cu rl in
  QOK S' /\
  (mPhi S' + mH n S' <= mPhi S + mH n S)%Z /\
  (mK S' + 2 * N * mH n S' <= mK S + 2 * N * mH n S)%Z /\
  (mH n S' + 1 <= mH n S)%Z /\
  (mQ n S' <= mQ n S + 1)%Z /\
  (0 <= mC n S)%Z /\ (0 <= mH n S')%Z /\
  (if (n <=? rl + 1)%uint63 then (mC n S' <= N * N)%Z /\ φ (s_rl S') = 0%Z /\ (φ rl + 1 = N)%Z
   else (mC n S' <= mC n S + N)%Z /\ φ (s_rl S') = (φ rl + 1)%Z).
Proof.
  intros I Q H1 H2. cbv zeta.
  destruct I as [T [Hh [Hc Hu]]]; cbn [s_tbl s_ex s_h s_cur s_cu s_ql] in T, Hh, Hc, Hu.
  pose proof H1 as L1. apply ltb_true in L1. pose proof H2 as L2. apply ltb_false in L2.
  unfold relS. cbv zeta.
  lazymatch goal with |- QOK (mkst _ _ ?h3 ?cur2 _ _ _ _ _ _) /\ _ =>
    set (H3v := h3) in *; set (C2v := cur2) in *;
    pose proof (relabel_heights n s t cp Hn Hs Ht Hst tbl ex h cur cu _ _ _ _ _ _ H3v C2v T Hh Hc Hu L1 L2
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as RH end.
  specialize (RH ltac:(intros G; apply andb_true_iff in G; destruct G as [G G4];
                       apply andb_true_iff in G; destruct G as [G G3];
                       apply andb_true_iff in G; destruct G as [G1 G2];
                       apply ltb_true in G2; change (φ 0) with 0%Z in G2; split; assumption)).
  destruct RH as [HOK3 [COK3 [Up Str]]].
  destruct (Hu L1) as [U1 [U2 [U3 U4]]].
  pose proof (h_le _ _ _ _ _ Hh) as Hle. pose proof (h_le _ _ _ _ _ HOK3) as Hle3.
  pose proof (c_le _ _ _ _ Hc) as Cle. pose proof (c_len _ _ _ _ Hc) as Lc.
  set (cu1 := if H3v.[cu] <? n then cu else n).
  assert (Ecu1 : (cu1 = cu /\ lt H3v.[cu]) \/ cu1 = n).
  { unfold cu1. destruct (H3v.[cu] <? n) eqn:E; bnorm'; [left; split; [reflexivity|exact E] | right; reflexivity]. }
  destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6 Q7]; cbn [s_q s_qh s_ql s_ex s_h s_cu s_rl] in Q1, Q2, Q3, Q4, Q5, Q6, Q7.
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - split; cbn [s_q s_qh s_ql s_ex s_h s_cu s_rl].
    + exact Q1.
    + exact Q2.
    + exact Q3.
    + intros k Hk. destruct (Q4 k Hk) as [W1 [W2 [W3 [W4 W5]]]].
      split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|].
      destruct Ecu1 as [[-> _]| ->]; [exact W5 | intro X; rewrite X in W1; zlia].
    + exact Q5.
    + intros w Hw A. apply (active_iff n s t Hn) in A. destruct A as [A1' [A2' [A3' A4']]].
      assert (Aw : active ex h n s t w = true).
      { unfold active. pose proof (Up w Hw).
        apply andb_true_iff; split; [apply andb_true_iff; split; [apply andb_true_iff; split|]|].
        - apply ltb_true. change (φ 0) with 0%Z. zlia.
        - apply ltb_true. zlia.
        - apply negb_true_iff, eqb_false. exact A3'.
        - apply negb_true_iff, eqb_false. exact A4'. }
      destruct (Q6 w Hw Aw) as [X|X]; [left|right; exact X].
      subst w. unfold cu1. replace (H3v.[cu] <? n) with true by (symmetry; apply ltb_true; exact A2'). reflexivity.
    + destruct (n <=? rl + 1) eqn:G; bnorm'.
      * change (φ 0) with 0%Z. zlia.
      * pose proof (succ_lt rl n Q7). zlia.
  - unfold mPhi, mH. cbn [s_ex s_h]. rewrite <- !Iadd. apply Ile. intros y Hy.
    pose proof (Up y Hy). unfold phv. destruct ((y =? s) || (y =? t)); [zlia|].
    destruct (0 <? φ ex.[y])%Z; zlia.
  - unfold mK, mH. cbn [s_tbl s_h].
    assert (D : isum n (fun y => φ H3v.[y] - φ h.[y])%Z =
                (isum n (fun v => N - φ h.[v]) - isum n (fun v => N - φ H3v.[v]))%Z).
    { rewrite <- Isub. apply Iext. intros y Hy. zlia. }
    idtac.
    assert (Ka : forall a, lt a -> (isum n (fun b => kind tbl H3v a b) <=
               isum n (fun b => kind tbl h a b) + N * (φ H3v.[a] - φ h.[a]) + isum n (fun y => φ H3v.[y] - φ h.[y]))%Z).
    { intros a Ha. rewrite <- Iconst, <- !Iadd. apply Ile. intros b Hb.
      pose proof (Up a Ha). pose proof (Up b Hb). unfold kind.
      destruct (0 <? RD n tbl a b)%Z; cbn [andb]; [|zlia].
      destruct (Z.ltb_spec (φ H3v.[b]) (φ H3v.[a])), (Z.ltb_spec (φ h.[b]) (φ h.[a])); zlia. }
    assert (Ks : (isum n (fun a => isum n (fun b => kind tbl H3v a b)) <=
                  isum n (fun a => isum n (fun b => kind tbl h a b) + N * (φ H3v.[a] - φ h.[a]) + isum n (fun y => φ H3v.[y] - φ h.[y])))%Z)
      by (apply Ile; exact Ka).
    rewrite !Iadd, Iconst in Ks.
    assert (Lin : isum n (fun a => N * (φ H3v.[a] - φ h.[a]))%Z = (N * isum n (fun y => φ H3v.[y] - φ h.[y]))%Z).
    { unfold isum. generalize (Z.to_nat N). intros k. induction k; cbn [zsum]; zlia. }
    rewrite Lin in Ks. zlia.
  - unfold mH. cbn [s_h]. apply (Ilt_pt _ _ cu); [exact L1 | intros y Hy; pose proof (Up y Hy); zlia | zlia].
  - unfold mQ. cbn [s_ql s_cu]. rewrite H1. destruct (cu1 <? n); zlia.
  - unfold mC. cbn [s_cur]. apply Inonneg. intros y Hy. pose proof (Cle y Hy). zlia.
  - unfold mH. cbn [s_h]. apply Inonneg. intros y Hy. pose proof (Hle3 y Hy). zlia.
  - unfold C2v. cbn [s_rl]. destruct (n <=? rl + 1) eqn:G; bnorm'.
    + unfold mC. cbn [s_cur]. split; [|split].
      * apply Ibound. intros y Hy. rewrite aget_make. change (φ 0) with 0%Z. zlia.
      * reflexivity.
      * pose proof (succ_lt rl n Q7). zlia.
    + pose proof (succ_lt rl n Q7) as E1. split; [|exact E1].
      unfold mC. cbn [s_cur].
      assert (Gc : forall y, cur.[cu <- 0].[y] = if y =? cu then 0 else cur.[y])
        by (intros; apply get_set1; rewrite Lc; exact L1).
      rewrite (Ipoint _ (fun v => N - φ cur.[v])%Z cu L1).
      * rewrite Gc, eqb_refl. change (φ 0) with 0%Z. pose proof (Cle cu L1). bd cur.[cu]. zlia.
      * intros y Hy Hne. rewrite Gc. replace (y =? cu) with false by (symmetry; apply eqb_false; exact Hne). reflexivity.
Qed.

Lemma mH_e a b h c d e f g i j : mH n (mkst a b h c d e f g i j) = isum n (fun v => N - φ h.[v])%Z.
Proof. reflexivity. Qed.
Lemma mC_e a b h c d e f g i j : mC n (mkst a b h c d e f g i j) = isum n (fun v => N - φ c.[v])%Z.
Proof. reflexivity. Qed.

Lemma amort S S' : Inv n s t cp S -> QOK S -> Step n s t S S' ->
  QOK S' /\ (Pot S' + scost S <= Pot S)%Z.
Proof.
  intros I Q HS. destruct HS as
    [tbl ex h cur cnt q qh ql cu rl H1 H2 H3 | tbl ex h cur cnt q qh ql cu rl H1 H2 H3
    | tbl ex h cur cnt q qh ql cu rl H1 H2 | tbl ex h cur cnt q qh ql cu rl H1 H4
    | tbl ex h cur cnt q qh ql cu rl H1 H4 H5].
  - pose proof (push_case tbl ex h cur cnt q qh ql cu rl I Q H1 H2 H3) as P. cbv zeta in P. cbv zeta.
    destruct P as [P1 [P2 [P3 [P4 P5]]]]. split; [exact P1|].
    assert (Sc : scost (mkst tbl ex h cur cnt q qh ql cu rl) = K) by (unfold scost; cbn [s_cu s_cur]; rewrite H1, H2; reflexivity).
    rewrite Sc. unfold Pot.
    lazymatch type of P4 with (mK ?S2 + ?sv <= mK ?S1)%Z =>
      assert (EH : mH n S2 = mH n S1) by reflexivity;
      assert (EC : mC n S2 = mC n S1) by reflexivity;
      assert (ER : φ (s_rl S2) = φ (s_rl S1)) by reflexivity;
      rewrite EH, EC, ER;
      assert (E := arith_push K N (mPhi S1) (mPhi S2) (mK S1) (mK S2) (mQ n S1) (mQ n S2) sv HK ltac:(zlia));
      revert P2 P3 P4 P5 E; generalize (mPhi S1) (mPhi S2) (mK S1) (mK S2) (mQ n S1) (mQ n S2) (mH n S1) (mC n S1) (φ (s_rl S1)) end.
    intros a1 a2 a3 a4 a5 a6 a7 a8 a9 P2 P3 P4 P5 E.
    assert (X : (4 * K * a2 + 4 * K * (N + 1) * a4 + K * a6 + K <= 4 * K * a1 + 4 * K * (N + 1) * a3 + K * a5)%Z).
    { refine (E _ _ P2 P4 P5).
      - match goal with |- context [if ?b then _ else _] => destruct b end; lia.
      - intros E0. apply P3. revert E0. match goal with |- context [if ?b then _ else _] => destruct b end; [reflexivity | discriminate]. }
    clear -X. nia.
  - pose proof (adv_case tbl ex h cur cnt q qh ql cu rl I Q H1 H2) as [P1 P2].
    split; [exact P1|].
    assert (Sc : scost (mkst tbl ex h cur cnt q qh ql cu rl) = K) by (unfold scost; cbn [s_cu s_cur]; rewrite H1, H2; reflexivity).
    rewrite Sc. unfold Pot.
    lazymatch type of P2 with (mC n ?S2 + 1 <= mC n ?S1)%Z =>
      assert (E1 : mPhi S2 = mPhi S1) by reflexivity;
      assert (E2 : mK S2 = mK S1) by reflexivity;
      assert (E3 : mH n S2 = mH n S1) by reflexivity;
      assert (E4 : mQ n S2 = mQ n S1) by reflexivity;
      assert (E5 : φ (s_rl S2) = φ (s_rl S1)) by reflexivity;
      rewrite E1, E2, E3, E4, E5;
      revert P2; generalize (mC n S1) (mC n S2) end.
    intros c1 c2 P2. clear -HK P2. nia.
  - pose proof (rel_case tbl ex h cur cnt q qh ql cu rl I Q H1 H2) as P. cbv zeta in P.
    change (let oh := h.[cu] in _) with (relS tbl ex h cur cnt q qh ql cu rl).
    destruct P as [P1 [P2 [P3 [P4 [P5 [P6 [P7 P8]]]]]]]. split; [exact P1|].
    assert (Sc : scost (mkst tbl ex h cur cnt q qh ql cu rl) =
       (K * (N + 1) + (if (n <=? rl + 1)%uint63 then K * (N + 1) * (N + 1) * (N + 1) else 0))%Z)
      by (unfold scost; cbn [s_cu s_cur s_rl]; rewrite H1, H2; reflexivity).
    rewrite Sc. unfold Pot.
    set (S1 := mkst tbl ex h cur cnt q qh ql cu rl) in *.
    set (S2 := relS tbl ex h cur cnt q qh ql cu rl) in *.
    change (φ (s_rl S1)) with (φ rl).
    revert P2 P3 P4 P5 P6 P7 P8.
    generalize (mPhi S1) (mPhi S2) (mK S1) (mK S2) (mH n S1) (mH n S2) (mC n S1) (mC n S2) (mQ n S1) (mQ n S2) (φ (s_rl S2)) (n <=? rl + 1)%uint63.
    intros a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 gl P2 P3 P4 P5 P6 P7 P8.
    exact (arith_rel K N a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 (φ rl) a11 gl HK (proj1 Hn) P6 P7 P2 P3 P4 P5 P8).
  - pose proof (pop_case tbl ex h cur cnt q qh ql cu rl Q H1 H4) as P. cbv zeta in P. cbv zeta.
    destruct P as [P1 P2]. split; [exact P1|].
    assert (Sc : scost (mkst tbl ex h cur cnt q qh ql cu rl) = K) by (unfold scost; cbn [s_cu]; rewrite H1; reflexivity).
    rewrite Sc. unfold Pot.
    lazymatch type of P2 with (mQ n ?S2 + 2 <= mQ n ?S1)%Z =>
      assert (E1 : mPhi S2 = mPhi S1) by reflexivity;
      assert (E2 : mK S2 = mK S1) by reflexivity;
      assert (E3 : mH n S2 = mH n S1) by reflexivity;
      assert (E4 : mC n S2 = mC n S1) by reflexivity;
      assert (E5 : φ (s_rl S2) = φ (s_rl S1)) by reflexivity;
      rewrite E1, E2, E3, E4, E5;
      revert P2; generalize (mQ n S1) (mQ n S2) end.
    intros c1 c2 P2. clear -HK P2. nia.
  - exfalso. exact (scan_case tbl ex h cur cnt q qh ql cu rl Q H1 H4 H5).
Qed.

Lemma Pot_bound S : Inv n s t cp S -> QOK S ->
  (Pot S <= 30 * K * ((N + 1) * (N + 1) * (N + 1) * (N + 1)))%Z.
Proof.
  intros I Q. destruct S as [tbl ex h cur cnt q qh ql cu rl].
  destruct I as [T [Hh [Hc Hu]]]; cbn [s_tbl s_ex s_h s_cur s_cu s_ql] in T, Hh, Hc, Hu.
  destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6 Q7]; cbn [s_q s_qh s_ql s_ex s_h s_cu s_rl] in Q1, Q2, Q3, Q4, Q5, Q6, Q7.
  pose proof (h_le _ _ _ _ _ Hh) as Hle. pose proof (c_le _ _ _ _ Hc) as Cle.
  assert (B1 : (0 <= mPhi (mkst tbl ex h cur cnt q qh ql cu rl) <= N * N)%Z).
  { unfold mPhi. cbn [s_ex s_h]. split.
    - apply Inonneg. intros y Hy. unfold phv. bd h.[y]. destruct (_ || _)%bool; [zlia|]. destruct (_ <? _)%Z; zlia.
    - apply Ibound. intros y Hy. unfold phv. pose proof (Hle y Hy). destruct (_ || _)%bool; [zlia|]. destruct (_ <? _)%Z; zlia. }
  assert (B2 : (0 <= mK (mkst tbl ex h cur cnt q qh ql cu rl) <= N * (N * 1))%Z).
  { unfold mK. cbn [s_tbl s_h]. split.
    - apply Inonneg. intros a Ha. apply Inonneg. intros b Hb. unfold kind. destruct (_ && _)%bool; zlia.
    - apply Ibound. intros a Ha. apply Ibound. intros b Hb. unfold kind. destruct (_ && _)%bool; zlia. }
  assert (B3 : (0 <= mH n (mkst tbl ex h cur cnt q qh ql cu rl) <= N * N)%Z).
  { unfold mH. cbn [s_h]. split.
    - apply Inonneg. intros y Hy. pose proof (Hle y Hy). zlia.
    - apply Ibound. intros y Hy. bd h.[y]. zlia. }
  assert (B4 : (0 <= mC n (mkst tbl ex h cur cnt q qh ql cu rl) <= N * N)%Z).
  { unfold mC. cbn [s_cur]. split.
    - apply Inonneg. intros y Hy. pose proof (Cle y Hy). zlia.
    - apply Ibound. intros y Hy. bd cur.[y]. zlia. }
  assert (B5 : (0 <= mQ n (mkst tbl ex h cur cnt q qh ql cu rl) <= 2 * N + 1)%Z).
  { unfold mQ. cbn [s_ql s_cu]. bd ql. destruct (cu <? n); zlia. }
  assert (B6 : (0 <= φ rl < N)%Z) by (bd rl; zlia).
  unfold Pot. cbn [s_rl].
  revert B1 B2 B3 B4 B5 B6.
  generalize (mPhi (mkst tbl ex h cur cnt q qh ql cu rl)) (mK (mkst tbl ex h cur cnt q qh ql cu rl))
    (mH n (mkst tbl ex h cur cnt q qh ql cu rl)) (mC n (mkst tbl ex h cur cnt q qh ql cu rl))
    (mQ n (mkst tbl ex h cur cnt q qh ql cu rl)) (φ rl).
  intros P Kc H C Qm r B1 B2 B3 B4 B5 B6.
  assert (HN : (2 <= N)%Z) by zlia. clear -HK HN B1 B2 B3 B4 B5 B6.
  set (A := (N + 1)%Z). set (X := (A * A)%Z).
  assert (HA : (3 <= A)%Z) by (unfold A; lia).
  assert (HX : (A <= X)%Z) by (unfold X; nia).
  assert (P1 : (P <= X)%Z) by (unfold X, A; nia).
  assert (P2 : (Kc <= X)%Z) by (unfold X, A; nia).
  assert (P3 : (H <= X)%Z) by (unfold X, A; nia).
  assert (P4 : (C <= X)%Z) by (unfold X, A; nia).
  assert (P5 : (Qm <= X)%Z) by (unfold X, A; nia).
  assert (P6 : (r <= X)%Z) by (unfold X, A; nia).
  assert (Q1 : (P <= X * X)%Z) by nia.
  assert (Q2 : (A * Kc <= X * X)%Z) by (apply Z.mul_le_mono_nonneg; lia).
  assert (Q3 : (X * H <= X * X)%Z) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (Q4 : (C <= X * X)%Z) by nia.
  assert (Q5 : (Qm <= X * X)%Z) by nia.
  assert (Q6 : (X * r <= X * X)%Z) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (E : (4 * P + 4 * (A * Kc) + 12 * (X * H) + C + Qm + 4 * (X * r) <= 30 * (X * X))%Z) by lia.
  assert (L : (K * (4 * P + 4 * (A * Kc) + 12 * (X * H) + C + Qm + 4 * (X * r)) <= K * (30 * (X * X)))%Z)
    by (apply Z.mul_le_mono_nonneg_l; [exact HK | exact E]).
  subst X A. clear -L.
  match goal with |- (?G <= ?R)%Z =>
    assert (EQ : G = (K * (4 * P + 4 * ((N + 1) * Kc) + 12 * ((N + 1) * (N + 1) * H) + C + Qm + 4 * ((N + 1) * (N + 1) * r)))%Z) by ring;
    assert (EQ2 : R = (K * (30 * ((N + 1) * (N + 1) * ((N + 1) * (N + 1)))))%Z) by ring end.
  rewrite EQ, EQ2. exact L.
Qed.

Lemma Pot_nonneg S : Inv n s t cp S -> QOK S -> (0 <= Pot S)%Z.
Proof.
  intros I Q. destruct S as [tbl ex h cur cnt q qh ql cu rl].
  destruct I as [T [Hh [Hc Hu]]]; cbn [s_tbl s_ex s_h s_cur s_cu s_ql] in T, Hh, Hc, Hu.
  destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6 Q7]; cbn [s_q s_qh s_ql s_ex s_h s_cu s_rl] in Q1, Q2, Q3, Q4, Q5, Q6, Q7.
  pose proof (h_le _ _ _ _ _ Hh) as Hle. pose proof (c_le _ _ _ _ Hc) as Cle.
  assert (B1 : (0 <= mPhi (mkst tbl ex h cur cnt q qh ql cu rl) <= N * N)%Z).
  { unfold mPhi. cbn [s_ex s_h]. split.
    - apply Inonneg. intros y Hy. unfold phv. bd h.[y]. destruct (_ || _)%bool; [zlia|]. destruct (_ <? _)%Z; zlia.
    - apply Ibound. intros y Hy. unfold phv. pose proof (Hle y Hy). destruct (_ || _)%bool; [zlia|]. destruct (_ <? _)%Z; zlia. }
  assert (B2 : (0 <= mK (mkst tbl ex h cur cnt q qh ql cu rl) <= N * (N * 1))%Z).
  { unfold mK. cbn [s_tbl s_h]. split.
    - apply Inonneg. intros a Ha. apply Inonneg. intros b Hb. unfold kind. destruct (_ && _)%bool; zlia.
    - apply Ibound. intros a Ha. apply Ibound. intros b Hb. unfold kind. destruct (_ && _)%bool; zlia. }
  assert (B3 : (0 <= mH n (mkst tbl ex h cur cnt q qh ql cu rl) <= N * N)%Z).
  { unfold mH. cbn [s_h]. split.
    - apply Inonneg. intros y Hy. pose proof (Hle y Hy). zlia.
    - apply Ibound. intros y Hy. bd h.[y]. zlia. }
  assert (B4 : (0 <= mC n (mkst tbl ex h cur cnt q qh ql cu rl) <= N * N)%Z).
  { unfold mC. cbn [s_cur]. split.
    - apply Inonneg. intros y Hy. pose proof (Cle y Hy). zlia.
    - apply Ibound. intros y Hy. bd cur.[y]. zlia. }
  assert (B5 : (0 <= mQ n (mkst tbl ex h cur cnt q qh ql cu rl) <= 2 * N + 1)%Z).
  { unfold mQ. cbn [s_ql s_cu]. bd ql. destruct (cu <? n); zlia. }
  assert (B6 : (0 <= φ rl < N)%Z) by (bd rl; zlia).
  unfold Pot. cbn [s_rl].
  revert B1 B2 B3 B4 B5 B6.
  generalize (mPhi (mkst tbl ex h cur cnt q qh ql cu rl)) (mK (mkst tbl ex h cur cnt q qh ql cu rl))
    (mH n (mkst tbl ex h cur cnt q qh ql cu rl)) (mC n (mkst tbl ex h cur cnt q qh ql cu rl))
    (mQ n (mkst tbl ex h cur cnt q qh ql cu rl)) (φ rl).
  intros P Kc H C Qm r B1 B2 B3 B4 B5 B6.
  assert (HN : (2 <= N)%Z) by zlia. clear -HK HN B1 B2 B3 B4 B5 B6.
  nia.
Qed.

End Pot.

Section SatQ.
Variables (n s t : int).
Hypothesis Hn : (2 <= φ n <= 1000)%Z.
Local Notation lt a := (φ a < φ n)%Z.
Local Notation N := (φ n).

Definition SQ (v : int) (ex q : array int) (ql : int) : Prop :=
  PArray.length ex = n /\ PArray.length q = n /\ (φ ql <= φ v)%Z /\
  (forall k, (0 <= k < φ ql)%Z -> let w := q.[of_Z k] in
     lt w /\ (φ w < φ v)%Z /\ (0 < φ ex.[w])%Z /\ w <> s /\ w <> t) /\
  (forall k1 k2, (0 <= k1 < k2)%Z -> (k2 < φ ql)%Z -> (φ q.[of_Z k1] < φ q.[of_Z k2])%Z) /\
  (forall w, (φ w < φ v)%Z -> (0 < φ ex.[w])%Z -> w <> s -> w <> t ->
     exists k, (0 <= k < φ ql)%Z /\ q.[of_Z k] = w).

Lemma of_Z_phi k : (0 <= k < wB)%Z -> φ (of_Z k) = k.
Proof. intros. rewrite of_Z_spec. apply Z.mod_small. exact H. Qed.

Lemma sat_queue : forall (z : Z) tbl ex q ql v H, gap n v = z -> (φ v <= N)%Z ->
  SQ v ex q ql ->
  let p := sat n s t tbl ex q ql v H in SQ n (snd (fst (fst p))) (snd (fst p)) (snd p).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros tbl ex q ql v H Hz Hv [S1 [S2 [S3 [S4 [S5 S6]]]]]. cbv zeta.
  rewrite sat_eq. destruct (bdec (v <? n)) as [Hvn | Hvn].
  - cbv zeta. pose proof Hvn as Hv'. apply ltb_true in Hv'. pose proof (succ_lt v n Hv') as Hs1.
    apply (IH (gap n (v + 1))); [rewrite <- Hz; apply dec_step; exact Hvn | reflexivity | zlia |].
    set (c := tbl.[s * n + v]).
    set (b := (0 <? c) && negb (v =? t) && negb (v =? s)).
    assert (Gex : forall w, ex.[v <- c].[w] = if w =? v then c else ex.[w])
      by (intros; apply get_set1; rewrite S1; exact Hv').
    assert (Eb : b = true <-> (0 < φ c)%Z /\ v <> t /\ v <> s).
    { unfold b. rewrite !andb_true_iff, negb_true_iff, negb_true_iff, ltb_true, !eqb_false.
      change (φ 0) with 0%Z. tauto. }
    assert (Eql : φ (if b then ql + 1 else ql) = (φ ql + if b then 1 else 0)%Z).
    { destruct b; [|zlia]. apply add_nowrap. change (φ 1) with 1%Z. rewrite wB_val. zlia. }
    assert (Rq : forall k, (0 <= k < φ ql)%Z -> (if b then q.[ql <- v] else q).[of_Z k] = q.[of_Z k]).
    { intros k Hk. destruct b; [|reflexivity]. apply aget_set_other. intro X.
      apply (f_equal to_Z) in X. rewrite of_Z_phi in X by (rewrite wB_val; zlia). zlia. }
    assert (Rn : (q.[ql <- v]).[of_Z (φ ql)] = v).
    { rewrite of_to_Z. apply aget_set_same. apply ltb_true. rewrite S2. zlia. }
    assert (Bq : b = true -> (φ ql < N)%Z) by (intros; zlia).
    assert (Gex' : forall w, w <> v -> ex.[v <- c].[w] = ex.[w])
      by (intros w Hw; rewrite Gex; replace (w =? v) with false by (symmetry; apply eqb_false; exact Hw); reflexivity).
    assert (Gexv : ex.[v <- c].[v] = c) by (rewrite Gex, eqb_refl; reflexivity).
    split; [|split; [|split; [|split; [|split]]]].
    + rewrite alength_set. exact S1.
    + destruct b; [rewrite alength_set|]; exact S2.
    + rewrite Eql, Hs1. destruct b; zlia.
    + intros k Hk. cbv zeta. rewrite Eql in Hk.
      destruct (Z.lt_ge_cases k (φ ql)) as [Hk'|Hk'].
      * rewrite (Rq k ltac:(zlia)). destruct (S4 k ltac:(zlia)) as [W1 [W2 [W3 [W4 W5]]]].
        assert (q.[of_Z k] <> v) by (intro X; rewrite X in W2; zlia).
        rewrite Gex' by assumption. rewrite Hs1. split; [exact W1|]. split; [zlia|]. split; [exact W3|]. split; assumption.
      * destruct b eqn:B; [|zlia]. assert (k = φ ql) by zlia. subst k. rewrite Rn, Gexv, Hs1.
        destruct (proj1 Eb eq_refl) as [B1 [B2 B3]]. split; [exact Hv'|]. split; [zlia|]. split; [exact B1|]. split; assumption.
    + intros k1 k2 Hk Hk2. rewrite Eql in Hk2.
      destruct (Z.lt_ge_cases k2 (φ ql)) as [Hk'|Hk'].
      * rewrite !Rq by zlia. apply S5; zlia.
      * destruct b eqn:B; [|zlia]. assert (k2 = φ ql) by zlia. subst k2. rewrite Rn, (Rq k1 ltac:(zlia)).
        destruct (S4 k1 ltac:(zlia)) as [_ [W2 _]]. exact W2.
    + intros w Hw He Ws Wt. rewrite Hs1 in Hw.
      destruct (Z.eq_dec (φ w) (φ v)) as [E|E].
      * apply to_Z_inj in E. subst w. rewrite Gexv in He.
        assert (B : b = true) by (apply Eb; auto).
        exists (φ ql). split; [rewrite Eql, B; bd ql; zlia|]. rewrite B. exact Rn.
      * assert (w <> v) by (intro X; apply E; rewrite X; reflexivity).
        rewrite Gex' in He by assumption. destruct (S6 w ltac:(zlia) He Ws Wt) as [k [Hk Ek]].
        exists k. split; [rewrite Eql; destruct b; zlia|]. rewrite Rq by exact Hk. exact Ek.
  - apply ltb_false in Hvn. replace v with n in * by (apply to_Z_inj; zlia). cbn [fst snd].
    split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|exact S6].
Qed.
End SatQ.

Lemma init_qok x : guard x = true -> QOK (nn x) (ss x) (tt x) (init_state x).
Proof.
  intros Hg. destruct (guard_facts x Hg) as [Hn [Hs [Ht [Hst [Hx _]]]]].
  unfold init_state. cbv zeta.
  set (n := nn x) in *. set (s := ss x) in *. set (t := tt x) in *.
  assert (S0 : SQ n s t 0 (PArray.make n 0) (PArray.make n 0) 0).
  { split; [apply make_n; exact Hn|]. split; [apply make_n; exact Hn|].
    change (φ 0) with 0%Z. split; [zlia|]. split; [intros; zlia|]. split; [intros; zlia|].
    intros w Hw. bd w. zlia. }
  pose proof (sat_queue n s t Hn _ (fill_tab x n (PArray.make (n * n) 0) 0 (wf0 n 0)) _ _ _ _ (wf0 n 0) eq_refl ltac:(change (φ 0) with 0%Z; zlia) S0) as SQn.
  cbv zeta in SQn. set (p := sat _ _ _ _ _ _ _ _ _) in *. destruct SQn as [S1 [S2 [S3 [S4 [S5 S6]]]]].
  assert (P0 : forall k, (0 <= k < φ (snd p))%Z -> qpos n 0 k = of_Z k).
  { intros k Hk. unfold qpos. f_equal. change (φ 0) with 0%Z. rewrite Z.add_0_l. apply Z.mod_small. zlia. }
  split; cbn [s_q s_qh s_ql s_ex s_h s_cu s_rl].
  - exact S2.
  - change (φ 0) with 0%Z. zlia.
  - exact S3.
  - intros k Hk. cbv zeta. rewrite P0 by exact Hk. destruct (S4 k Hk) as [W1 [_ [W3 [W4 W5]]]].
    split; [exact W1|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|].
    intro X. rewrite X in W1. zlia.
  - intros k1 k2 Hk1 Hk2 E. rewrite !P0 in E by assumption.
    destruct (Z.lt_total k1 k2) as [L|[L|L]]; [|exact L|].
    + pose proof (S5 k1 k2 ltac:(zlia) ltac:(zlia)). rewrite E in H. zlia.
    + pose proof (S5 k2 k1 ltac:(zlia) ltac:(zlia)). rewrite E in H. zlia.
  - intros w Hw A. apply (active_iff n s t Hn) in A. destruct A as [A1 [_ [A3 A4]]].
    right. destruct (S6 w Hw A1 A3 A4) as [k [Hk Ek]]. exists k. split; [exact Hk|]. rewrite P0 by exact Hk. exact Ek.
  - change (φ 0) with 0%Z. zlia.
Qed.


From Stdlib Require Import ssreflect.

#[local] Arguments Uint63.to_Z : simpl never.
#[local] Arguments gap : simpl never.
#[local] Arguments gcd_loop_cost : simpl never.
#[local] Arguments igcd_cost : simpl never.
#[local] Arguments capf_cost : simpl never.
#[local] Arguments fill_row_cost : simpl never.
#[local] Arguments fill_tab_cost : simpl never.
#[local] Arguments amin_cost : simpl never.
#[local] Arguments amax_cost : simpl never.
#[local] Arguments rng_ok_cost : simpl never.
#[local] Arguments sat_cost : simpl never.
#[local] Arguments amap_cost : simpl never.
#[local] Arguments relaxF_cost : simpl never.
#[local] Arguments has_val_cost : simpl never.
#[local] Arguments lscan_cost : simpl never.
#[local] Arguments layers_cost : simpl never.
#[local] Arguments bfs_cost : simpl never.
#[local] Arguments maxF_cost : simpl never.
#[local] Arguments glob_cost : simpl never.
#[local] Arguments cntl_cost : simpl never.
#[local] Arguments count_cost : simpl never.
#[local] Arguments rmin_cost : simpl never.
#[local] Arguments no_height_cost : simpl never.
#[local] Arguments liftF_cost : simpl never.
#[local] Arguments lift_cost : simpl never.
#[local] Arguments cnt_lift_cost : simpl never.
#[local] Arguments active_cost : simpl never.
#[local] Arguments find_act_cost : simpl never.
#[local] Arguments adm_cost : simpl never.
#[local] Arguments enq_pos_cost : simpl never.
#[local] Arguments mloop_cost : simpl never.
#[local] Arguments nn_cost : simpl never.
#[local] Arguments ss_cost : simpl never.
#[local] Arguments tt_cost : simpl never.
#[local] Arguments guard_cost : simpl never.
#[local] Arguments init_state_cost : simpl never.



Ltac strip_ex X := lazymatch X with extract ?Y _ _ => strip_ex Y | ?f _ _ _ => f | _ => X end.
Ltac prim_simpl := repeat match goal with |- context [@cost ?T ?X] =>
  let h := strip_ex X in
  first [constr_eq h set_cost | constr_eq h make_cost];
  let v := eval lazy in (@cost T X) in change (@cost T X) with v end.

Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. unfold bdec_cost; destruct w; cbn; lia. Qed.

Lemma gap_S m k c : (Z.to_nat (gap m k) <= S c)%nat -> (k <? m) = true -> (Z.to_nat (gap m (k + 1)) <= c)%nat.
Proof.
  intros Hc e. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in *.
  assert (φ (k + 1) = (φ k + 1)%Z) by (zify; Z.to_euclidean_division_equations; lia). lia.
Qed.
Lemma gap_0 m k : (Z.to_nat (gap m k) <= 0)%nat -> (k <? m) = true -> False.
Proof.
  intros Hc e. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in *. lia.
Qed.

Lemma has_val_time d dC n nC L LC j jC H HC :
  (cost (extract (extract (extract (extract (has_val_cost stepsCM d dC) n nC) L LC) j jC) H HC)
     <= 30 * Z.to_nat (gap n j) + 10)%nat.
Proof.
  unfold has_val_cost. cbn.
  match goal with |- context [@cost ?T (?G d dC n nC L LC j jC H HC)] =>
    assert (HG : forall k j jC H HC, (Z.to_nat (gap n j) <= k)%nat ->
       (cost (G d dC n nC L LC j jC H HC) <= 30 * k + 10)%nat) end.
  { induction k as [|k IH]; intros j' jC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (j' <? n) (bool_w (j' <? n))) as HB;
      cost_destruct (bdec (j' <? n)); cost_simpl.
    - exfalso. exact (gap_0 _ _ Hk e).
    - lia.
    - cost_destruct (d.[j'] =? L); cost_simpl; [lia|].
      match goal with |- context [@cost ?T (?G' d dC n nC L LC (j' + 1)%uint63 ?w ?hh ?ee)] =>
          have HI := (IH (j' + 1)%uint63 w hh ee (gap_S _ _ _ Hk e) : (@cost T (G' d dC n nC L LC (j' + 1)%uint63 w hh ee) <= _)%nat) end.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G d dC n nC L LC j jC H HC)] =>
    exact (HG _ j jC H HC (le_n _) : (@cost T (G d dC n nC L LC j jC H HC) <= _)%nat) end.
Qed.

Lemma amap_time F FC a aC i iC m mC H HC KF :
  (forall y yC o oC, cost (FC y yC) + cost (extract (FC y yC) o oC) <= KF)%nat ->
  (cost (extract (extract (extract (extract (amap_cost stepsCM F FC) a aC) i iC) m mC) H HC)
     <= (KF + 50) * Z.to_nat (gap m i) + 10)%nat.
Proof.
  intros HF.
  unfold amap_cost. cbn.
  match goal with |- context [@cost ?T (?G F FC a aC i iC m mC H HC)] =>
    assert (HG : forall k a aC i iC H HC, (Z.to_nat (gap m i) <= k)%nat ->
       (cost (G F FC a aC i iC m mC H HC) <= (KF + 50) * k + 10)%nat) end.
  { induction k as [|k IH]; intros a' aC' i' iC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (i' <? m) (bool_w (i' <? m))) as HB;
      cost_destruct (bdec (i' <? m)); cost_simpl.
    - exfalso. exact (gap_0 _ _ Hk e).
    - lia.
    - have HF1 := HF i' iC' a'.[i'] (array_elems aC' i').
      cost_destruct (F i' a'.[i'] =? a'.[i']); cost_simpl; prim_simpl; cost_align HF1;
      match goal with |- context [@cost ?T (?G' F FC ?a2 ?aC2 (i' + 1)%uint63 ?w m mC ?hh ?ee)] =>
          have HI := (IH a2 aC2 (i' + 1)%uint63 w hh ee (gap_S _ _ _ Hk e) : (@cost T (G' F FC a2 aC2 (i' + 1)%uint63 w m mC hh ee) <= _)%nat) end;
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G F FC a aC i iC m mC H HC)] =>
    exact (HG _ a aC i iC H HC (le_n _) : (@cost T (G F FC a aC i iC m mC H HC) <= _)%nat) end.
Qed.



Ltac depth_of f X := lazymatch X with
  | extract ?Y _ _ => let d := depth_of f Y in constr:(S d)
  | f _ _ _ => constr:(O)
  | f _ _ _ _ => constr:(O)
  end.
Ltac zl f n := repeat match goal with |- context [@cost ?T ?X] =>
  let d := depth_of f X in
  let b := eval compute in (Nat.ltb d n) in
  lazymatch b with true => change (@cost T X) with 0%nat end end.

Ltac fin_if := repeat (rewrite cost_if; cbn beta iota);
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn; lia.

Lemma andb_time1 b w : (cost (andb_cost stepsCM b w) = 0)%nat.
Proof. reflexivity. Qed.
Lemma andb_time2 b w c wc : (cost (extract (andb_cost stepsCM b w) c wc) <= 1)%nat.
Proof. unfold andb_cost. destruct w; cbn; lia. Qed.

Lemma relaxF_time tbl tblC n nC b bC L1 L1C a aC o oC :
  (cost (extract (extract (extract (extract (relaxF_cost stepsCM tbl tblC) n nC) b bC) L1 L1C) a aC)
   + cost (extract (extract (extract (extract (extract (relaxF_cost stepsCM tbl tblC) n nC) b bC) L1 L1C) a aC) o oC) <= 40)%nat.
Proof.
  unfold relaxF_cost. cost_simpl. fin_if.
Qed.

Lemma gap0 n : Z.to_nat (gap n 0) = Z.to_nat (φ n).
Proof. unfold gap. change (φ 0) with 0%Z. f_equal. lia. Qed.

Ltac gen_amap KF HF := match goal with |- context [@cost ?T (extract (extract (extract (extract (amap_cost _ ?F ?FC) ?a ?aC) ?i ?iC) ?m ?mC) ?H ?HC)] =>
    let Hc := fresh "Hamap" in
    have Hc := (amap_time F FC a aC i iC m mC H HC KF ltac:(intros; HF) : (@cost T (extract (extract (extract (extract (amap_cost _ F FC) a aC) i iC) m mC) H HC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (extract (extract (amap_cost _ F FC) a aC) i iC) m mC) H HC)); intros ? Hc end.

Lemma lscan_time tbl tblC n nC L LC d dC j jC H HC :
  (cost (extract (extract (extract (extract (extract (lscan_cost stepsCM tbl tblC) n nC) L LC) d dC) j jC) H HC)
     <= (Z.to_nat (φ n) * 90 + 100) * Z.to_nat (gap n j) + 10)%nat.
Proof.
  unfold lscan_cost. cbn.
  match goal with |- context [@cost ?T (?G tbl tblC n nC L LC d dC j jC H HC)] =>
    assert (HG : forall k d dC j jC H HC, (Z.to_nat (gap n j) <= k)%nat ->
       (cost (G tbl tblC n nC L LC d dC j jC H HC) <= (Z.to_nat (φ n) * 90 + 100) * k + 10)%nat) end.
  { induction k as [|k IH]; intros d' dC' j' jC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (j' <? n) (bool_w (j' <? n))) as HB;
      cost_destruct (bdec (j' <? n)); cost_simpl.
    - exfalso. exact (gap_0 _ _ Hk e).
    - lia.
    - cost_destruct (d'.[j'] =? L); cost_simpl.
      + zl relaxF_cost 5%nat. zl amap_cost 4%nat. gen_amap 40%nat ltac:(apply relaxF_time). rewrite gap0 in Hamap.
        match goal with |- context [@cost ?T (?G' tbl tblC n nC L LC ?d2 ?dC2 (j' + 1)%uint63 ?w ?hh ?ee)] =>
          have HI := (IH d2 dC2 (j' + 1)%uint63 w hh ee (gap_S _ _ _ Hk e) : (@cost T (G' tbl tblC n nC L LC d2 dC2 (j' + 1)%uint63 w hh ee) <= _)%nat) end.
        nia.
      + match goal with |- context [@cost ?T (?G' tbl tblC n nC L LC ?d2 ?dC2 (j' + 1)%uint63 ?w ?hh ?ee)] =>
          have HI := (IH d2 dC2 (j' + 1)%uint63 w hh ee (gap_S _ _ _ Hk e) : (@cost T (G' tbl tblC n nC L LC d2 dC2 (j' + 1)%uint63 w hh ee) <= _)%nat) end.
        nia.
    - lia. }
  match goal with |- context [@cost ?T (?G tbl tblC n nC L LC d dC j jC H HC)] =>
    exact (HG _ d dC j jC H HC (le_n _) : (@cost T (G tbl tblC n nC L LC d dC j jC H HC) <= _)%nat) end.
Qed.

Lemma amin_time x xC n nC i iC best bestC H HC :
  (cost (extract (extract (extract (extract (amin_cost stepsCM x xC) n nC) i iC) best bestC) H HC) <= 100 * Z.to_nat (gap n i) + 10)%nat.
Proof.
  unfold amin_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC n nC i iC best bestC H HC)] =>
    assert (HG : forall kk i iC best bestC H HC, (Z.to_nat (gap n i) <= kk)%nat ->
       (cost (G x xC n nC i iC best bestC H HC) <= 100 * kk + 10)%nat) end.
  { induction kk as [|kk IH]; intros i' iC' best' bestC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (i' <? n) (bool_w (i' <? n))) as HB;
      cost_destruct (bdec (i' <? n)); cost_simpl.
    - exfalso. exact (gap_0 _ _ Hk e).
    - lia.
    - cost_destruct (x.[i'] <? x.[best']); cost_simpl; match goal with |- context [@cost ?T (?G' x xC n nC (i' + 1)%uint63 ?w ?best2 ?bestC2 ?hh ?ee)] => have HI := (IH (i' + 1)%uint63 w best2 bestC2 hh ee (gap_S _ _ _ Hk e) : (@cost T (G' x xC n nC (i' + 1)%uint63 w best2 bestC2 hh ee) <= _)%nat) end; lia.
    - lia. }
  match goal with |- context [@cost ?T (?G x xC n nC i iC best bestC H HC)] =>
    exact (HG _ i iC best bestC H HC (le_n _) : (@cost T (G x xC n nC i iC best bestC H HC) <= _)%nat) end.
Qed.

Lemma amax_time x xC n nC i iC best bestC H HC :
  (cost (extract (extract (extract (extract (amax_cost stepsCM x xC) n nC) i iC) best bestC) H HC) <= 100 * Z.to_nat (gap n i) + 10)%nat.
Proof.
  unfold amax_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC n nC i iC best bestC H HC)] =>
    assert (HG : forall kk i iC best bestC H HC, (Z.to_nat (gap n i) <= kk)%nat ->
       (cost (G x xC n nC i iC best bestC H HC) <= 100 * kk + 10)%nat) end.
  { induction kk as [|kk IH]; intros i' iC' best' bestC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (i' <? n) (bool_w (i' <? n))) as HB;
      cost_destruct (bdec (i' <? n)); cost_simpl.
    - exfalso. exact (gap_0 _ _ Hk e).
    - lia.
    - cost_destruct (x.[best'] <? x.[i']); cost_simpl; match goal with |- context [@cost ?T (?G' x xC n nC (i' + 1)%uint63 ?w ?best2 ?bestC2 ?hh ?ee)] => have HI := (IH (i' + 1)%uint63 w best2 bestC2 hh ee (gap_S _ _ _ Hk e) : (@cost T (G' x xC n nC (i' + 1)%uint63 w best2 bestC2 hh ee) <= _)%nat) end; lia.
    - lia. }
  match goal with |- context [@cost ?T (?G x xC n nC i iC best bestC H HC)] =>
    exact (HG _ i iC best bestC H HC (le_n _) : (@cost T (G x xC n nC i iC best bestC H HC) <= _)%nat) end.
Qed.

Lemma rng_ok_time x xC n nC i iC H HC :
  (cost (extract (extract (extract (rng_ok_cost stepsCM x xC) n nC) i iC) H HC) <= 100 * Z.to_nat (gap n i) + 10)%nat.
Proof.
  unfold rng_ok_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC n nC i iC H HC)] =>
    assert (HG : forall kk i iC H HC, (Z.to_nat (gap n i) <= kk)%nat ->
       (cost (G x xC n nC i iC H HC) <= 100 * kk + 10)%nat) end.
  { induction kk as [|kk IH]; intros i' iC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (i' <? n) (bool_w (i' <? n))) as HB;
      cost_destruct (bdec (i' <? n)); cost_simpl.
    - exfalso. exact (gap_0 _ _ Hk e).
    - lia.
    - cost_destruct (2 <=? x.[i']); cost_simpl; try cost_destruct (x.[i'] <=? 2000000000); cost_simpl; first [lia | match goal with |- context [@cost ?T (?G' x xC n nC (i' + 1)%uint63 ?w ?hh ?ee)] => have HI := (IH (i' + 1)%uint63 w hh ee (gap_S _ _ _ Hk e) : (@cost T (G' x xC n nC (i' + 1)%uint63 w hh ee) <= _)%nat) end; lia].
    - lia. }
  match goal with |- context [@cost ?T (?G x xC n nC i iC H HC)] =>
    exact (HG _ i iC H HC (le_n _) : (@cost T (G x xC n nC i iC H HC) <= _)%nat) end.
Qed.

Lemma cntl_time h hC cnt cntC n nC i iC H HC :
  (cost (extract (extract (extract (extract (cntl_cost stepsCM h hC) cnt cntC) n nC) i iC) H HC) <= 100 * Z.to_nat (gap n i) + 10)%nat.
Proof.
  unfold cntl_cost. cbn.
  match goal with |- context [@cost ?T (?G h hC cnt cntC n nC i iC H HC)] =>
    assert (HG : forall kk cnt cntC i iC H HC, (Z.to_nat (gap n i) <= kk)%nat ->
       (cost (G h hC cnt cntC n nC i iC H HC) <= 100 * kk + 10)%nat) end.
  { induction kk as [|kk IH]; intros cnt' cntC' i' iC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (i' <? n) (bool_w (i' <? n))) as HB;
      cost_destruct (bdec (i' <? n)); cost_simpl.
    - exfalso. exact (gap_0 _ _ Hk e).
    - lia.
    - prim_simpl; match goal with |- context [@cost ?T (?G' h hC ?cnt2 ?cntC2 n nC (i' + 1)%uint63 ?w ?hh ?ee)] => have HI := (IH cnt2 cntC2 (i' + 1)%uint63 w hh ee (gap_S _ _ _ Hk e) : (@cost T (G' h hC cnt2 cntC2 n nC (i' + 1)%uint63 w hh ee) <= _)%nat) end; lia.
    - lia. }
  match goal with |- context [@cost ?T (?G h hC cnt cntC n nC i iC H HC)] =>
    exact (HG _ cnt cntC i iC H HC (le_n _) : (@cost T (G h hC cnt cntC n nC i iC H HC) <= _)%nat) end.
Qed.

Lemma no_height_time h hC n nC k kC i iC H HC :
  (cost (extract (extract (extract (extract (no_height_cost stepsCM h hC) n nC) k kC) i iC) H HC) <= 100 * Z.to_nat (gap n i) + 10)%nat.
Proof.
  unfold no_height_cost. cbn.
  match goal with |- context [@cost ?T (?G h hC n nC k kC i iC H HC)] =>
    assert (HG : forall kk i iC H HC, (Z.to_nat (gap n i) <= kk)%nat ->
       (cost (G h hC n nC k kC i iC H HC) <= 100 * kk + 10)%nat) end.
  { induction kk as [|kk IH]; intros i' iC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (i' <? n) (bool_w (i' <? n))) as HB;
      cost_destruct (bdec (i' <? n)); cost_simpl.
    - exfalso. exact (gap_0 _ _ Hk e).
    - lia.
    - cost_destruct (h.[i'] =? k); cost_simpl; [lia | match goal with |- context [@cost ?T (?G' h hC n nC k kC (i' + 1)%uint63 ?w ?hh ?ee)] => have HI := (IH (i' + 1)%uint63 w hh ee (gap_S _ _ _ Hk e) : (@cost T (G' h hC n nC k kC (i' + 1)%uint63 w hh ee) <= _)%nat) end; lia].
    - lia. }
  match goal with |- context [@cost ?T (?G h hC n nC k kC i iC H HC)] =>
    exact (HG _ i iC H HC (le_n _) : (@cost T (G h hC n nC k kC i iC H HC) <= _)%nat) end.
Qed.

Lemma cnt_lift_time h hC cnt cntC n nC k kC i iC H HC :
  (cost (extract (extract (extract (extract (extract (cnt_lift_cost stepsCM h hC) cnt cntC) n nC) k kC) i iC) H HC) <= 100 * Z.to_nat (gap n i) + 10)%nat.
Proof.
  unfold cnt_lift_cost. cbn.
  match goal with |- context [@cost ?T (?G h hC cnt cntC n nC k kC i iC H HC)] =>
    assert (HG : forall kk cnt cntC i iC H HC, (Z.to_nat (gap n i) <= kk)%nat ->
       (cost (G h hC cnt cntC n nC k kC i iC H HC) <= 100 * kk + 10)%nat) end.
  { induction kk as [|kk IH]; intros cnt' cntC' i' iC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (i' <? n) (bool_w (i' <? n))) as HB;
      cost_destruct (bdec (i' <? n)); cost_simpl.
    - exfalso. exact (gap_0 _ _ Hk e).
    - lia.
    - cost_destruct (k <? h.[i']); cost_simpl; try cost_destruct (h.[i'] <? n); cost_simpl; prim_simpl; match goal with |- context [@cost ?T (?G' h hC ?cnt2 ?cntC2 n nC k kC (i' + 1)%uint63 ?w ?hh ?ee)] => have HI := (IH cnt2 cntC2 (i' + 1)%uint63 w hh ee (gap_S _ _ _ Hk e) : (@cost T (G' h hC cnt2 cntC2 n nC k kC (i' + 1)%uint63 w hh ee) <= _)%nat) end; lia.
    - lia. }
  match goal with |- context [@cost ?T (?G h hC cnt cntC n nC k kC i iC H HC)] =>
    exact (HG _ cnt cntC i iC H HC (le_n _) : (@cost T (G h hC cnt cntC n nC k kC i iC H HC) <= _)%nat) end.
Qed.

Lemma rmin_time tbl tblC n nC u uC h hC b bC acc accC H HC :
  (cost (extract (extract (extract (extract (extract (extract (rmin_cost stepsCM tbl tblC) n nC) u uC) h hC) b bC) acc accC) H HC) <= 100 * Z.to_nat (gap n b) + 10)%nat.
Proof.
  unfold rmin_cost. cbn.
  match goal with |- context [@cost ?T (?G tbl tblC n nC u uC h hC b bC acc accC H HC)] =>
    assert (HG : forall kk b bC acc accC H HC, (Z.to_nat (gap n b) <= kk)%nat ->
       (cost (G tbl tblC n nC u uC h hC b bC acc accC H HC) <= 100 * kk + 10)%nat) end.
  { induction kk as [|kk IH]; intros b' bC' acc' accC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (b' <? n) (bool_w (b' <? n))) as HB;
      cost_destruct (bdec (b' <? n)); cost_simpl.
    - exfalso. exact (gap_0 _ _ Hk e).
    - lia.
    - cost_destruct (0 <? tbl.[u * n + b']); cost_simpl; try cost_destruct (h.[b'] + 1 <? acc'); cost_simpl; match goal with |- context [@cost ?T (?G' tbl tblC n nC u uC h hC (b' + 1)%uint63 ?w ?acc2 ?accC2 ?hh ?ee)] => have HI := (IH (b' + 1)%uint63 w acc2 accC2 hh ee (gap_S _ _ _ Hk e) : (@cost T (G' tbl tblC n nC u uC h hC (b' + 1)%uint63 w acc2 accC2 hh ee) <= _)%nat) end; lia.
    - lia. }
  match goal with |- context [@cost ?T (?G tbl tblC n nC u uC h hC b bC acc accC H HC)] =>
    exact (HG _ b bC acc accC H HC (le_n _) : (@cost T (G tbl tblC n nC u uC h hC b bC acc accC H HC) <= _)%nat) end.
Qed.



Ltac gen_has_val := repeat match goal with |- context [@cost ?T (extract (extract (extract (extract (has_val_cost _ ?d ?dC) ?n ?nC) ?L ?LC) ?j ?jC) ?H ?HC)] =>
    let Hc := fresh "Hhas_val" in
    have Hc := (has_val_time d dC n nC L LC j jC H HC : (@cost T (extract (extract (extract (extract (has_val_cost stepsCM d dC) n nC) L LC) j jC) H HC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (extract (extract (has_val_cost stepsCM d dC) n nC) L LC) j jC) H HC)); intros ? Hc end.
Ltac gen_lscan := repeat match goal with |- context [@cost ?T (extract (extract (extract (extract (extract (lscan_cost _ ?tbl ?tblC) ?n ?nC) ?L ?LC) ?d ?dC) ?j ?jC) ?H ?HC)] =>
    let Hc := fresh "Hlscan" in
    have Hc := (lscan_time tbl tblC n nC L LC d dC j jC H HC : (@cost T (extract (extract (extract (extract (extract (lscan_cost stepsCM tbl tblC) n nC) L LC) d dC) j jC) H HC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (extract (extract (extract (lscan_cost stepsCM tbl tblC) n nC) L LC) d dC) j jC) H HC)); intros ? Hc end.
Ltac gen_amin := repeat match goal with |- context [@cost ?T (extract (extract (extract (extract (amin_cost _ ?x ?xC) ?n ?nC) ?i ?iC) ?best ?bestC) ?H ?HC)] =>
    let Hc := fresh "Hamin" in
    have Hc := (amin_time x xC n nC i iC best bestC H HC : (@cost T (extract (extract (extract (extract (amin_cost stepsCM x xC) n nC) i iC) best bestC) H HC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (extract (extract (amin_cost stepsCM x xC) n nC) i iC) best bestC) H HC)); intros ? Hc end.
Ltac gen_amax := repeat match goal with |- context [@cost ?T (extract (extract (extract (extract (amax_cost _ ?x ?xC) ?n ?nC) ?i ?iC) ?best ?bestC) ?H ?HC)] =>
    let Hc := fresh "Hamax" in
    have Hc := (amax_time x xC n nC i iC best bestC H HC : (@cost T (extract (extract (extract (extract (amax_cost stepsCM x xC) n nC) i iC) best bestC) H HC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (extract (extract (amax_cost stepsCM x xC) n nC) i iC) best bestC) H HC)); intros ? Hc end.
Ltac gen_rng_ok := repeat match goal with |- context [@cost ?T (extract (extract (extract (rng_ok_cost _ ?x ?xC) ?n ?nC) ?i ?iC) ?H ?HC)] =>
    let Hc := fresh "Hrng_ok" in
    have Hc := (rng_ok_time x xC n nC i iC H HC : (@cost T (extract (extract (extract (rng_ok_cost stepsCM x xC) n nC) i iC) H HC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (extract (rng_ok_cost stepsCM x xC) n nC) i iC) H HC)); intros ? Hc end.
Ltac gen_cntl := repeat match goal with |- context [@cost ?T (extract (extract (extract (extract (cntl_cost _ ?h ?hC) ?cnt ?cntC) ?n ?nC) ?i ?iC) ?H ?HC)] =>
    let Hc := fresh "Hcntl" in
    have Hc := (cntl_time h hC cnt cntC n nC i iC H HC : (@cost T (extract (extract (extract (extract (cntl_cost stepsCM h hC) cnt cntC) n nC) i iC) H HC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (extract (extract (cntl_cost stepsCM h hC) cnt cntC) n nC) i iC) H HC)); intros ? Hc end.
Ltac gen_no_height := repeat match goal with |- context [@cost ?T (extract (extract (extract (extract (no_height_cost _ ?h ?hC) ?n ?nC) ?k ?kC) ?i ?iC) ?H ?HC)] =>
    let Hc := fresh "Hno_height" in
    have Hc := (no_height_time h hC n nC k kC i iC H HC : (@cost T (extract (extract (extract (extract (no_height_cost stepsCM h hC) n nC) k kC) i iC) H HC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (extract (extract (no_height_cost stepsCM h hC) n nC) k kC) i iC) H HC)); intros ? Hc end.
Ltac gen_cnt_lift := repeat match goal with |- context [@cost ?T (extract (extract (extract (extract (extract (cnt_lift_cost _ ?h ?hC) ?cnt ?cntC) ?n ?nC) ?k ?kC) ?i ?iC) ?H ?HC)] =>
    let Hc := fresh "Hcnt_lift" in
    have Hc := (cnt_lift_time h hC cnt cntC n nC k kC i iC H HC : (@cost T (extract (extract (extract (extract (extract (cnt_lift_cost stepsCM h hC) cnt cntC) n nC) k kC) i iC) H HC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (extract (extract (extract (cnt_lift_cost stepsCM h hC) cnt cntC) n nC) k kC) i iC) H HC)); intros ? Hc end.
Ltac gen_rmin := repeat match goal with |- context [@cost ?T (extract (extract (extract (extract (extract (extract (rmin_cost _ ?tbl ?tblC) ?n ?nC) ?u ?uC) ?h ?hC) ?b ?bC) ?acc ?accC) ?H ?HC)] =>
    let Hc := fresh "Hrmin" in
    have Hc := (rmin_time tbl tblC n nC u uC h hC b bC acc accC H HC : (@cost T (extract (extract (extract (extract (extract (extract (rmin_cost stepsCM tbl tblC) n nC) u uC) h hC) b bC) acc accC) H HC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (extract (extract (extract (extract (rmin_cost stepsCM tbl tblC) n nC) u uC) h hC) b bC) acc accC) H HC)); intros ? Hc end.

Lemma negb_time b w : (cost (negb_cost stepsCM b w) <= 2)%nat.
Proof. unfold negb_cost. destruct w; cbn; lia. Qed.
Ltac gen_negb := repeat match goal with |- context [@cost ?T (negb_cost stepsCM ?b ?w)] =>
    let Hc := fresh "Hnegb" in
    have Hc := (negb_time b w : (@cost T (negb_cost stepsCM b w) <= _)%nat);
    revert Hc; generalize (@cost T (negb_cost stepsCM b w)); intros ? Hc end.
Ltac fin_if2 := gen_negb; repeat (rewrite cost_if; cbn beta iota);
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn; lia.

Lemma active_time ex exC h hC n nC s sC t tC v vC :
  (cost (extract (extract (extract (extract (extract (active_cost stepsCM ex exC) h hC) n nC) s sC) t tC) v vC) <= 60)%nat.
Proof. unfold active_cost. cost_simpl. fin_if2. Qed.
Ltac gen_active := repeat match goal with |- context [@cost ?T (extract (extract (extract (extract (extract (active_cost _ ?ex ?exC) ?h ?hC) ?n ?nC) ?s ?sC) ?t ?tC) ?v ?vC)] =>
    let Hc := fresh "Hactive" in
    have Hc := (active_time ex exC h hC n nC s sC t tC v vC : (@cost T (extract (extract (extract (extract (extract (active_cost stepsCM ex exC) h hC) n nC) s sC) t tC) v vC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (extract (extract (extract (active_cost stepsCM ex exC) h hC) n nC) s sC) t tC) v vC)); intros ? Hc end.

Lemma adm_time tbl tblC h hC n nC u uC v vC :
  (cost (extract (extract (extract (extract (adm_cost stepsCM tbl tblC) h hC) n nC) u uC) v vC) <= 60)%nat.
Proof. unfold adm_cost. cost_simpl. fin_if2. Qed.

Lemma enq_pos_time qh qhC ql qlC n nC :
  (cost (extract (extract (enq_pos_cost stepsCM qh qhC) ql qlC) n nC) <= 30)%nat.
Proof. unfold enq_pos_cost. cost_simpl. fin_if. Qed.

Lemma maxF_time d dC y yC o oC :
  (cost (extract (maxF_cost stepsCM d dC) y yC) + cost (extract (extract (maxF_cost stepsCM d dC) y yC) o oC) <= 40)%nat.
Proof. unfold maxF_cost. cost_simpl. fin_if. Qed.

Lemma liftF_time n nC k kC y yC o oC :
  (cost (extract (extract (liftF_cost stepsCM n nC) k kC) y yC) + cost (extract (extract (extract (liftF_cost stepsCM n nC) k kC) y yC) o oC) <= 40)%nat.
Proof. unfold liftF_cost. cost_simpl. fin_if. Qed.

Lemma layers_time tbl tblC n nC L LC d dC H HC :
  (cost (extract (extract (extract (extract (layers_cost stepsCM tbl tblC) n nC) L LC) d dC) H HC) <= Z.to_nat (gap n L) * ((Z.to_nat (φ n) * 90 + 100) * Z.to_nat (φ n) + Z.to_nat (φ n) * 30 + 100) + 10)%nat.
Proof.
  unfold layers_cost. cbn.
  match goal with |- context [@cost ?T (?G tbl tblC n nC L LC d dC H HC)] =>
    assert (HG : forall kk L LC d dC H HC, (Z.to_nat (gap n L) <= kk)%nat ->
       (cost (G tbl tblC n nC L LC d dC H HC) <= kk * ((Z.to_nat (φ n) * 90 + 100) * Z.to_nat (φ n) + Z.to_nat (φ n) * 30 + 100) + 10)%nat) end.
  { induction kk as [|kk IH]; intros L' LC' d' dC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (L' <? n) (bool_w (L' <? n))) as HB;
      cost_destruct (bdec (L' <? n)); cost_simpl.
    - exfalso. exact (gap_0 _ _ Hk e).
    - lia.
    - zl has_val_cost 4%nat. gen_has_val. rewrite gap0 in Hhas_val. cost_destruct (has_val d' n L' 0 (wf0 n 0)); cost_simpl; [zl lscan_cost 5%nat; gen_lscan; rewrite gap0 in Hlscan; match goal with |- context [@cost ?T (?G' tbl tblC n nC (L' + 1)%uint63 ?w ?d2 ?dC2 ?hh ?ee)] => have HI := (IH (L' + 1)%uint63 w d2 dC2 hh ee (gap_S _ _ _ Hk e) : (@cost T (G' tbl tblC n nC (L' + 1)%uint63 w d2 dC2 hh ee) <= _)%nat) end; nia | lia].
    - lia. }
  match goal with |- context [@cost ?T (?G tbl tblC n nC L LC d dC H HC)] =>
    exact (HG _ L LC d dC H HC (le_n _) : (@cost T (G tbl tblC n nC L LC d dC H HC) <= _)%nat) end.
Qed.

Lemma find_act_time ex exC h hC n nC s sC t tC i iC H HC :
  (cost (extract (extract (extract (extract (extract (extract (find_act_cost stepsCM ex exC) h hC) n nC) s sC) t tC) i iC) H HC) <= 100 * Z.to_nat (gap n i) + 10)%nat.
Proof.
  unfold find_act_cost. cbn.
  match goal with |- context [@cost ?T (?G ex exC h hC n nC s sC t tC i iC H HC)] =>
    assert (HG : forall kk i iC H HC, (Z.to_nat (gap n i) <= kk)%nat ->
       (cost (G ex exC h hC n nC s sC t tC i iC H HC) <= 100 * kk + 10)%nat) end.
  { induction kk as [|kk IH]; intros i' iC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (i' <? n) (bool_w (i' <? n))) as HB;
      cost_destruct (bdec (i' <? n)); cost_simpl.
    - exfalso. exact (gap_0 _ _ Hk e).
    - lia.
    - zl active_cost 6%nat. gen_active. cost_destruct (active ex h n s t i'); cost_simpl; [lia | match goal with |- context [@cost ?T (?G' ex exC h hC n nC s sC t tC (i' + 1)%uint63 ?w ?hh ?ee)] => have HI := (IH (i' + 1)%uint63 w hh ee (gap_S _ _ _ Hk e) : (@cost T (G' ex exC h hC n nC s sC t tC (i' + 1)%uint63 w hh ee) <= _)%nat) end; lia].
    - lia. }
  match goal with |- context [@cost ?T (?G ex exC h hC n nC s sC t tC i iC H HC)] =>
    exact (HG _ i iC H HC (le_n _) : (@cost T (G ex exC h hC n nC s sC t tC i iC H HC) <= _)%nat) end.
Qed.



Ltac gen_layers := repeat match goal with |- context [@cost ?T (extract (extract (extract (extract (layers_cost _ ?tbl ?tblC) ?n ?nC) ?L ?LC) ?d ?dC) ?H ?HC)] =>
    let Hc := fresh "Hlayers" in
    have Hc := (layers_time tbl tblC n nC L LC d dC H HC : (@cost T (extract (extract (extract (extract (layers_cost stepsCM tbl tblC) n nC) L LC) d dC) H HC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (extract (extract (layers_cost stepsCM tbl tblC) n nC) L LC) d dC) H HC)); intros ? Hc end.
Ltac gen_find_act := repeat match goal with |- context [@cost ?T (extract (extract (extract (extract (extract (extract (find_act_cost _ ?ex ?exC) ?h ?hC) ?n ?nC) ?s ?sC) ?t ?tC) ?i ?iC) ?H ?HC)] =>
    let Hc := fresh "Hfind_act" in
    have Hc := (find_act_time ex exC h hC n nC s sC t tC i iC H HC : (@cost T (extract (extract (extract (extract (extract (extract (find_act_cost stepsCM ex exC) h hC) n nC) s sC) t tC) i iC) H HC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (extract (extract (extract (extract (find_act_cost stepsCM ex exC) h hC) n nC) s sC) t tC) i iC) H HC)); intros ? Hc end.
Ltac gen_adm := repeat match goal with |- context [@cost ?T (extract (extract (extract (extract (adm_cost _ ?tbl ?tblC) ?h ?hC) ?n ?nC) ?u ?uC) ?v ?vC)] =>
    let Hc := fresh "Hadm" in
    have Hc := (adm_time tbl tblC h hC n nC u uC v vC : (@cost T (extract (extract (extract (extract (adm_cost stepsCM tbl tblC) h hC) n nC) u uC) v vC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (extract (extract (adm_cost stepsCM tbl tblC) h hC) n nC) u uC) v vC)); intros ? Hc end.
Ltac gen_enq_pos := repeat match goal with |- context [@cost ?T (extract (extract (enq_pos_cost _ ?qh ?qhC) ?ql ?qlC) ?n ?nC)] =>
    let Hc := fresh "Henq_pos" in
    have Hc := (enq_pos_time qh qhC ql qlC n nC : (@cost T (extract (extract (enq_pos_cost stepsCM qh qhC) ql qlC) n nC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (enq_pos_cost stepsCM qh qhC) ql qlC) n nC)); intros ? Hc end.

Lemma bfs_time tbl tblC n nC t tC :
  (cost (extract (extract (bfs_cost stepsCM tbl tblC) n nC) t tC) <= Z.to_nat (φ n) * ((Z.to_nat (φ n) * 90 + 100) * Z.to_nat (φ n) + Z.to_nat (φ n) * 30 + 100) + 40)%nat.
Proof.
  unfold bfs_cost. cost_simpl. prim_simpl. zl layers_cost 4%nat. gen_layers. rewrite gap0 in Hlayers. lia.
Qed.
Ltac gen_bfs := repeat match goal with |- context [@cost ?T (extract (extract (bfs_cost _ ?tbl ?tblC) ?n ?nC) ?t ?tC)] =>
    let Hc := fresh "Hbfs" in
    have Hc := (bfs_time tbl tblC n nC t tC : (@cost T (extract (extract (bfs_cost stepsCM tbl tblC) n nC) t tC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (bfs_cost stepsCM tbl tblC) n nC) t tC)); intros ? Hc end.

Lemma glob_time tbl tblC n nC t tC h hC :
  (cost (extract (extract (extract (glob_cost stepsCM tbl tblC) n nC) t tC) h hC)
   <= Z.to_nat (φ n) * ((Z.to_nat (φ n) * 90 + 100) * Z.to_nat (φ n) + Z.to_nat (φ n) * 30 + 100) + Z.to_nat (φ n) * 90 + 100)%nat.
Proof.
  unfold glob_cost. cost_simpl. zl bfs_cost 2%nat. gen_bfs. zl maxF_cost 1%nat. zl amap_cost 4%nat.
  gen_amap 40%nat ltac:(apply maxF_time). rewrite gap0 in Hamap. lia.
Qed.

Lemma lift_time h hC n nC k kC :
  (cost (extract (extract (lift_cost stepsCM h hC) n nC) k kC) <= Z.to_nat (φ n) * 90 + 100)%nat.
Proof.
  unfold lift_cost. cost_simpl. zl liftF_cost 2%nat. zl amap_cost 4%nat.
  gen_amap 40%nat ltac:(apply liftF_time). rewrite gap0 in Hamap. lia.
Qed.

Lemma count_time h hC n nC :
  (cost (extract (count_cost stepsCM h hC) n nC) <= Z.to_nat (φ n) * 100 + 100)%nat.
Proof.
  unfold count_cost. cost_simpl. prim_simpl. zl cntl_cost 4%nat. gen_cntl. rewrite gap0 in Hcntl. lia.
Qed.
Ltac gen_glob := repeat match goal with |- context [@cost ?T (extract (extract (extract (glob_cost _ ?tbl ?tblC) ?n ?nC) ?t ?tC) ?h ?hC)] =>
    let Hc := fresh "Hglob" in
    have Hc := (glob_time tbl tblC n nC t tC h hC : (@cost T (extract (extract (extract (glob_cost stepsCM tbl tblC) n nC) t tC) h hC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (extract (glob_cost stepsCM tbl tblC) n nC) t tC) h hC)); intros ? Hc end.
Ltac gen_lift := repeat match goal with |- context [@cost ?T (extract (extract (lift_cost _ ?h ?hC) ?n ?nC) ?k ?kC)] =>
    let Hc := fresh "Hlift" in
    have Hc := (lift_time h hC n nC k kC : (@cost T (extract (extract (lift_cost stepsCM h hC) n nC) k kC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (lift_cost stepsCM h hC) n nC) k kC)); intros ? Hc end.
Ltac gen_count := repeat match goal with |- context [@cost ?T (extract (count_cost _ ?h ?hC) ?n ?nC)] =>
    let Hc := fresh "Hcount" in
    have Hc := (count_time h hC n nC : (@cost T (extract (count_cost stepsCM h hC) n nC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (count_cost stepsCM h hC) n nC)); intros ? Hc end.



Ltac fix_of f := let b := eval cbv beta delta [f] in (f stepsCM) in
  match b with context [?F] => is_fix F; exact F end.
Definition mloop_fix := ltac:(fix_of mloop_cost).

Ltac head_of t := lazymatch t with ?f _ => head_of f | _ => t end.
Ltac pair_rec F := repeat match goal with |- context [?t] =>
  let h := head_of t in constr_eq h F;
  lazymatch type of t with CostM _ =>
    let r := fresh "r" in let Er := fresh "Er" in
    remember t as r eqn:Er; destruct r as [? ?] end end.
Lemma bdec_expr_time b (mb : CostM (bool_cost stepsCM b)) :
  (cost (expr_app (pure (bdec_cost stepsCM)) b mb) <= cost mb + 3)%nat.
Proof.
  rewrite cost_expr_app cost_pure. pose proof (bdec_time b (extract mb)). cbn [extract pure]. lia.
Qed.
Ltac hide_bdec := match goal with |- context [@cost ?T (expr_app (pure (bdec_cost stepsCM)) ?b ?mb)] =>
  let Hb := fresh "Hbd" in
  have Hb := (bdec_expr_time b mb : (@cost T (expr_app (pure (bdec_cost stepsCM)) b mb) <= _)%nat);
  revert Hb; generalize (@cost T (expr_app (pure (bdec_cost stepsCM)) b mb)); intros ? Hb;
  cbn in Hb end.


Ltac rnd t := rewrite ?cost_cast ?cost_expr_step ?cost_expr_seq; hide_bdec; cost_destruct t; cbn beta iota zeta delta [Acc_inv].

Ltac zlH f n H := repeat match type of H with context [@cost ?T ?X] =>
  let d := depth_of f X in
  let b := eval compute in (Nat.ltb d n) in
  lazymatch b with true => change (@cost T X) with 0%nat in H end end.

Ltac zl_all := zl adm_cost 5%nat; zl enq_pos_cost 3%nat; zl active_cost 6%nat; zl rmin_cost 7%nat;
  zl no_height_cost 5%nat; zl cnt_lift_cost 6%nat; zl lift_cost 3%nat; zl glob_cost 4%nat;
  zl count_cost 2%nat; zl find_act_cost 7%nat.
Ltac gen_all := gen_adm; gen_enq_pos; gen_active; gen_rmin; gen_no_height; gen_cnt_lift; gen_lift; gen_glob;
  gen_count; gen_find_act; gen_negb.


Ltac procH H := rewrite ?cost_price ?cost_step ?extract_step in H.
Ltac genH_adm H := match type of H with context [@cost ?T (extract (extract (extract (extract (adm_cost _ ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC)] =>
  let Hc := fresh "Hadm" in
  have Hc := (adm_time a aC b bC c cC d dC e eC : (@cost T (extract (extract (extract (extract (adm_cost stepsCM a aC) b bC) c cC) d dC) e eC) <= _)%nat) end.
Ltac genH_find_act H := match type of H with context [@cost ?T (extract (extract (extract (extract (extract (extract (find_act_cost _ ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC)] =>
  let Hc := fresh "Hfa" in
  have Hc := (find_act_time a aC b bC c cC d dC e eC f fC g gC : (@cost T (extract (extract (extract (extract (extract (extract (find_act_cost stepsCM a aC) b bC) c cC) d dC) e eC) f fC) g gC) <= _)%nat) end.
Lemma if_same_nat (b : bool) (x : nat) : (if b then x else x) = x.
Proof. destruct b; reflexivity. Qed.
Ltac fin_br := repeat (rewrite cost_if; cbn beta iota); cbn [cost]; rewrite ?if_same_nat;
  repeat match goal with |- context [match ?b with true => ?x | false => ?y end] =>
    let Hif := fresh "Hif" in
    assert (Hif : ((if b then x else y) <= x + y)%nat) by (destruct b; lia);
    revert Hif; generalize (if b then x else y); intros ? Hif end; cbn [cost] in *.

Lemma glob_le M : (M * ((M * 90 + 100) * M + M * 30 + 100) + M * 90 + 100 <= (M + 1) * (M + 1) * (M + 1) * 400)%nat.
Proof. nia. Qed.

Ltac get_rec IH St I' Q' :=
  match goal with Er : (?c0, ?a0) = mloop_fix _ ?nC1 _ ?sC1 _ ?tC1 ?tb ?tbC ?e1 ?eC ?h1 ?hC1 ?cr ?crC ?cn ?cnC ?q1 ?qC1 ?qh1 ?qhC1 ?ql1 ?qlC1 ?cu1 ?cuC1 ?rl1 ?rlC1 ?H1 ?HC1 |- _ =>
    let HI := fresh "HI" in
    have HI := IH _ St I' Q' nC1 sC1 tC1 tb tbC e1 eC h1 hC1 cr crC cn cnC q1 qC1 qh1 qhC1 ql1 qlC1 cu1 cuC1 rl1 rlC1 H1 HC1 eq_refl;
    rewrite <- Er in HI; cbn [cost] in HI; clear Er end.
Section ML.
Variables (n s t : int) (cp : int -> int -> Z).
Hypothesis Hn : (2 <= φ n <= 1000)%Z.
Hypothesis Hs : (φ s < φ n)%Z.
Hypothesis Ht : (φ t < φ n)%Z.
Hypothesis Hst : s <> t.
Hypothesis Hcp : forall a b, (0 <= cp a b <= 2147483648)%Z.

Lemma mloop_time : forall S, Acc (StepR n s t) S -> Inv n s t cp S -> QOK n s t S ->
  forall nC sC tC tbl tblC ex exC h hC cur curC cnt cntC q qC qh qhC ql qlC cu cuC rl rlC H HC,
  S = mkst tbl ex h cur cnt q qh ql cu rl ->
  (Z.of_nat (cost (mloop_fix n nC s sC t tC tbl tblC ex exC h hC cur curC cnt cntC q qC qh qhC ql qlC cu cuC rl rlC H HC))
     <= Pot n s t 1000 S + 1000 * (φ n + 1))%Z.
Proof.
  intros S A. induction A as [S _ IH].
  intros I Q nC sC tC tbl tblC ex exC h hC cur curC cnt cntC q qC qh qhC ql qlC cu cuC rl rlC H HC ES. subst S.
  assert (PN : (0 <= Pot n s t 1000 (mkst tbl ex h cur cnt q qh ql cu rl))%Z) by (eapply Pot_nonneg; eauto; lia).
  assert (EM : Z.of_nat (Z.to_nat (φ n)) = φ n) by lia.
  destruct H as [g].
  cost_unfold_fix. cbn beta iota zeta.
  rnd (bdec (cu <? n)).
  - rnd (bdec (cur.[cu] <? n)).
    + rnd (bdec (adm tbl h n cu cur.[cu])).
      * (* push *)
        pair_rec mloop_fix.
        pose proof (step_push n s t tbl ex h cur cnt q qh ql cu rl e e0 e1) as St.
        destruct (step_ok n s t cp Hn Hs Ht Hst Hcp _ _ I St) as [I' _].
        destruct (amort n s t cp Hn Hs Ht Hst Hcp 1000 ltac:(lia) _ _ I Q St) as [Q' Am].
        get_rec IH St I' Q'.
        unfold scost in Am. cbn [s_cu s_cur] in Am. rewrite e e0 in Am.
        match goal with |- (Z.of_nat (cost (?c0, _) + _) <= _)%Z => idtac | _ => idtac end.
        match type of HI with (Z.of_nat ?c0 <= _)%Z =>
          apply (Z.le_trans _ (Z.of_nat (c0 + 1000))); [|lia] end.
        apply Nat2Z.inj_le. cost_simpl. zl_all. gen_all. prim_simpl.
        procH Hbd1. zlH adm_cost 4%nat Hbd1. genH_adm Hbd1.
        fin_br; lia.
      * (* advance *)
        pair_rec mloop_fix.
        pose proof (step_adv n s t tbl ex h cur cnt q qh ql cu rl e e0 e1) as St.
        destruct (step_ok n s t cp Hn Hs Ht Hst Hcp _ _ I St) as [I' _].
        destruct (amort n s t cp Hn Hs Ht Hst Hcp 1000 ltac:(lia) _ _ I Q St) as [Q' Am].
        get_rec IH St I' Q'.
        unfold scost in Am. cbn [s_cu s_cur] in Am. rewrite e e0 in Am.
        match type of HI with (Z.of_nat ?c0 <= _)%Z =>
          apply (Z.le_trans _ (Z.of_nat (c0 + 1000))); [|lia] end.
        apply Nat2Z.inj_le. cost_simpl. zl_all. gen_all. prim_simpl.
        procH Hbd1. zlH adm_cost 4%nat Hbd1. genH_adm Hbd1.
        fin_br; lia.
    + (* relabel *)
      pair_rec mloop_fix.
      pose proof (step_rel n s t tbl ex h cur cnt q qh ql cu rl e e0) as St.
      destruct (step_ok n s t cp Hn Hs Ht Hst Hcp _ _ I St) as [I' _].
      destruct (amort n s t cp Hn Hs Ht Hst Hcp 1000 ltac:(lia) _ _ I Q St) as [Q' Am].
      get_rec IH St I' Q'.
      unfold scost in Am. cbn [s_cu s_cur s_rl] in Am. rewrite e e0 in Am.
      match type of HI with (Z.of_nat ?c0 <= _)%Z =>
        apply (Z.le_trans _ (Z.of_nat (c0 + (Z.to_nat (φ n) + 1) * 1000 + (if (n <=? rl + 1)%uint63 then (Z.to_nat (φ n) + 1) * (Z.to_nat (φ n) + 1) * (Z.to_nat (φ n) + 1) * 1000 else 0)%nat)));
        [|match type of Am with (?P1 + _ <= _)%Z => revert HI Am; generalize P1; intros p1 HI Am end; clear -HI Am PN EM Hn; destruct (n <=? rl + 1)%uint63; nia] end.
      apply Nat2Z.inj_le. clear St I' Q' HI Am IH.
      cost_simpl. clear i. zl_all. gen_all. prim_simpl.
      rewrite ?gap0 in Hrmin Hno_height Hcnt_lift.
      pose proof (Nat.le_trans _ _ _ Hglob (glob_le (Z.to_nat (φ n)))) as HG. clear Hglob.
      revert HG. generalize ((Z.to_nat (φ n) + 1) * (Z.to_nat (φ n) + 1) * (Z.to_nat (φ n) + 1))%nat. intros Q3 HG.
      cost_destruct (n <=? rl + 1); cost_simpl;
      fin_br; lia.
  - rnd (bdec (0 <? ql)).
    + (* pop *)
      pair_rec mloop_fix.
      pose proof (step_pop n s t tbl ex h cur cnt q qh ql cu rl e e0) as St.
      destruct (step_ok n s t cp Hn Hs Ht Hst Hcp _ _ I St) as [I' _].
      destruct (amort n s t cp Hn Hs Ht Hst Hcp 1000 ltac:(lia) _ _ I Q St) as [Q' Am].
      get_rec IH St I' Q'.
      unfold scost in Am. cbn [s_cu] in Am. rewrite e in Am.
      match type of HI with (Z.of_nat ?c0 <= _)%Z =>
        apply (Z.le_trans _ (Z.of_nat (c0 + 1000))); [|lia] end.
      apply Nat2Z.inj_le. clear St I' Q' HI Am IH. cost_simpl. clear i. zl_all. gen_all. prim_simpl.
      fin_br; destruct (qh + 1 =? n); lia.
    + rnd (bdec (find_act ex h n s t 0 (wf0 n 0) <? n)).
      * exfalso. eapply scan_case; eauto.
      * apply (Z.le_trans _ (Z.of_nat ((Z.to_nat (φ n) + 1) * 1000))); [|nia].
        apply Nat2Z.inj_le. cost_simpl. zl_all. gen_all. prim_simpl.
        rewrite gap0 in Hfind_act. lia.
Qed.
End ML.




Lemma eqb0_false (r : int) : (r =? 0)%uint63 = false -> φ r <> 0%Z.
Proof.
  intros H E. assert (r = 0%uint63) by (apply to_Z_inj; exact E). subst. discriminate.
Qed.
Lemma mod_half (a b : Z) : (0 < b <= a)%Z -> (2 * (a mod b) <= a)%Z.
Proof.
  intros Hb. pose proof (Z.mod_pos_bound a b ltac:(lia)).
  pose proof (Z.div_mod a b ltac:(lia)).
  assert (1 <= a / b)%Z by (apply Z.div_le_lower_bound; lia).
  nia.
Qed.
Lemma halve (a b : Z) (k : nat) : (0 < b <= a)%Z ->
  (a * b < 2 ^ Z.of_nat (S k))%Z -> (b * (a mod b) < 2 ^ Z.of_nat k)%Z.
Proof.
  intros Hb Hlt. pose proof (mod_half a b Hb). pose proof (Z.mod_pos_bound a b ltac:(lia)).
  rewrite Nat2Z.inj_succ Z.pow_succ_r in Hlt; [lia|]. nia.
Qed.

Lemma gcd_ord_time a aC b bC H HC k :
  (φ b <= φ a)%Z -> (φ a * φ b < 2 ^ Z.of_nat k)%Z ->
  (cost (extract (extract (gcd_loop_cost stepsCM a aC) b bC) H HC) <= 50 * k + 60)%nat.
Proof.
  unfold gcd_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G a aC b bC H HC)] =>
    assert (HG : forall j a aC b bC H HC,
       (φ b <= φ a)%Z -> (φ a * φ b < 2 ^ Z.of_nat j)%Z ->
       (cost (G a aC b bC H HC) <= 50 * j + 60)%nat) end.
  { clear H HC. induction j as [|j IH]; intros a' aC' b' bC' [g] HC' Hle Hlt;
      cost_simpl;
      pose proof (bdec_time (b' =? 0)%uint63 (bool_w (b' =? 0)%uint63)) as HB;
      cost_destruct (bdec (b' =? 0)%uint63); cost_simpl.
    - lia.
    - exfalso. pose proof (to_Z_bounded b'). pose proof (to_Z_bounded a').
      pose proof (eqb0_false b' e).
      change (2 ^ Z.of_nat 0)%Z with 1%Z in Hlt. nia.
    - lia.
    - pose proof (to_Z_bounded b'). pose proof (to_Z_bounded a').
      pose proof (eqb0_false b' e).
      assert (Hle' : (φ (a' mod b') <= φ b')%Z).
      { rewrite Uint63.mod_spec. pose proof (Z.mod_pos_bound (φ a') (φ b')). lia. }
      assert (Hlt' : (φ b' * φ (a' mod b') < 2 ^ Z.of_nat j)%Z).
      { rewrite Uint63.mod_spec. apply halve; [lia|exact Hlt]. }
      match goal with |- context [@cost ?T (?G' b' ?w1 (a' mod b')%uint63 ?w2 ?hh ?ee)] =>
        have HI := (IH b' w1 (a' mod b')%uint63 w2 hh ee
                    : _ -> _ -> (@cost T (G' b' w1 (a' mod b')%uint63 w2 hh ee) <= _)%nat) end.
      specialize (HI Hle' Hlt'). lia. }
  match goal with |- context [@cost ?T (?G a aC b bC H HC)] =>
    exact (HG _ a aC b bC H HC : _ -> _ -> (@cost T (G a aC b bC H HC) <= _)%nat) end.
Qed.

Lemma gcd_time a aC b bC H HC k :
  (φ a * φ b < 2 ^ Z.of_nat k)%Z ->
  (cost (extract (extract (gcd_loop_cost stepsCM a aC) b bC) H HC) <= 50 * k + 120)%nat.
Proof.
  intros Hlt. destruct (Z.le_gt_cases (φ b) (φ a)) as [Hle|Hgt].
  { pose proof (gcd_ord_time a aC b bC H HC k Hle Hlt). lia. }
  pose proof (to_Z_bounded b). pose proof (to_Z_bounded a).
  assert (Hm : φ (a mod b) = φ a).
  { rewrite Uint63.mod_spec. apply Z.mod_small. lia. }
  destruct H as [g].
  unfold gcd_loop_cost. cost_simpl.
  pose proof (bdec_time (b =? 0)%uint63 (bool_w (b =? 0)%uint63)) as HB.
  cost_destruct (bdec (b =? 0)%uint63); cost_simpl.
  - lia.
  - assert (Hle' : (φ (a mod b) <= φ b)%Z) by lia.
    assert (Hlt' : (φ b * φ (a mod b) < 2 ^ Z.of_nat k)%Z) by (rewrite Hm; lia).
    match goal with |- context [@cost ?T (?G' b ?w1 (a mod b)%uint63 ?w2 ?hh ?ee)] =>
      have HI := (gcd_ord_time b w1 (a mod b)%uint63 w2 hh ee k
                  : _ -> _ -> (@cost T (G' b w1 (a mod b)%uint63 w2 hh ee) <= _)%nat) end.
    specialize (HI Hle' Hlt'). lia.
Qed.

Lemma prod126 a b : (φ a * φ b < 2 ^ Z.of_nat 126)%Z.
Proof.
  pose proof (to_Z_bounded a) as Ba. pose proof (to_Z_bounded b) as Bb.
  change wB with (2 ^ 63)%Z in Ba, Bb.
  assert (E : (2 ^ Z.of_nat 126 = 2 ^ 63 * 2 ^ 63)%Z) by reflexivity. rewrite E. nia.
Qed.

Lemma igcd_time a aC b bC :
  (cost (extract (igcd_cost stepsCM a aC) b bC) <= 100 * 70)%nat.
Proof.
  unfold igcd_cost. cost_simpl. zl gcd_loop_cost 2%nat.
  match goal with |- context [@cost ?T (extract (extract (gcd_loop_cost _ a ?aC1) b ?bC1) ?H ?HC)] =>
    have Hc := (gcd_time a aC1 b bC1 H HC 126 (prod126 a b) : (@cost T (extract (extract (gcd_loop_cost stepsCM a aC1) b bC1) H HC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (gcd_loop_cost stepsCM a aC1) b bC1) H HC)); intros ? Hc end.
  lia.
Qed.
Ltac gen_igcd := repeat match goal with |- context [@cost ?T (extract (igcd_cost _ ?a ?aC) ?b ?bC)] =>
    let Hc := fresh "Higcd" in
    have Hc := (igcd_time a aC b bC : (@cost T (extract (igcd_cost stepsCM a aC) b bC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (igcd_cost stepsCM a aC) b bC)); intros ? Hc end.



Lemma capf_time x xC i iC j jC :
  (cost (extract (extract (capf_cost stepsCM x xC) i iC) j jC) <= 100 * 71)%nat.
Proof.
  unfold capf_cost. cost_simpl. cost_destruct (i =? j); cost_simpl; [lia|]. zl igcd_cost 1%nat. gen_igcd. cost_destruct (1 <? igcd x.[i] x.[j]); cost_simpl; lia.
Qed.
Ltac gen_capf := repeat match goal with |- context [@cost ?T (extract (extract (capf_cost _ ?x ?xC) ?i ?iC) ?j ?jC)] =>
    let Hc := fresh "Hcapf" in
    have Hc := (capf_time x xC i iC j jC : (@cost T (extract (extract (capf_cost stepsCM x xC) i iC) j jC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (capf_cost stepsCM x xC) i iC) j jC)); intros ? Hc end.

Lemma gap_le n i : (Z.to_nat (gap n i) <= Z.to_nat (φ n))%nat.
Proof. unfold gap. pose proof (to_Z_bounded i). lia. Qed.

Lemma fill_row_time x xC n nC i iC tbl tblC j jC H HC :
  (cost (extract (extract (extract (extract (extract (fill_row_cost stepsCM x xC) n nC) i iC) tbl tblC) j jC) H HC) <= Z.to_nat (gap n j) * (100 * 80) + 10)%nat.
Proof.
  unfold fill_row_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC n nC i iC tbl tblC j jC H HC)] =>
    assert (HG : forall kk tbl tblC j jC H HC, (Z.to_nat (gap n j) <= kk)%nat ->
       (cost (G x xC n nC i iC tbl tblC j jC H HC) <= kk * (100 * 80) + 10)%nat) end.
  { induction kk as [|kk IH]; intros tbl' tblC' j' jC' [g] HC' Hk;
      match goal with |- (_ <= ?R)%nat => remember R as RR eqn:ERR end; cost_simpl;
      pose proof (bdec_time (j' <? n) (bool_w (j' <? n))) as HB;
      cost_destruct (bdec (j' <? n)); cost_simpl.
    - exfalso. exact (gap_0 _ _ Hk e).
    - lia.
    - zl capf_cost 2%nat. gen_capf. prim_simpl. match goal with |- context [@cost ?T (?G' x xC n nC i iC ?tbl2 ?tblC2 (j' + 1)%uint63 ?w ?hh ?ee)] => have HI := (IH tbl2 tblC2 (j' + 1)%uint63 w hh ee (gap_S _ _ _ Hk e) : (@cost T (G' x xC n nC i iC tbl2 tblC2 (j' + 1)%uint63 w hh ee) <= _)%nat) end. lia.
    - lia. }
  match goal with |- context [@cost ?T (?G x xC n nC i iC tbl tblC j jC H HC)] =>
    exact (HG _ tbl tblC j jC H HC (le_n _) : (@cost T (G x xC n nC i iC tbl tblC j jC H HC) <= _)%nat) end.
Qed.
Ltac gen_fill_row := repeat match goal with |- context [@cost ?T (extract (extract (extract (extract (extract (fill_row_cost _ ?x ?xC) ?n ?nC) ?i ?iC) ?tbl ?tblC) ?j ?jC) ?H ?HC)] =>
    let Hc := fresh "Hfill_row" in
    have Hc := (fill_row_time x xC n nC i iC tbl tblC j jC H HC : (@cost T (extract (extract (extract (extract (extract (fill_row_cost stepsCM x xC) n nC) i iC) tbl tblC) j jC) H HC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (extract (extract (extract (fill_row_cost stepsCM x xC) n nC) i iC) tbl tblC) j jC) H HC)); intros ? Hc end.

Lemma fill_tab_time x xC n nC tbl tblC i iC H HC :
  (cost (extract (extract (extract (extract (fill_tab_cost stepsCM x xC) n nC) tbl tblC) i iC) H HC) <= Z.to_nat (gap n i) * (Z.to_nat (φ n) * (100 * 80) + 100) + 10)%nat.
Proof.
  unfold fill_tab_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC n nC tbl tblC i iC H HC)] =>
    assert (HG : forall kk tbl tblC i iC H HC, (Z.to_nat (gap n i) <= kk)%nat ->
       (cost (G x xC n nC tbl tblC i iC H HC) <= kk * (Z.to_nat (φ n) * (100 * 80) + 100) + 10)%nat) end.
  { induction kk as [|kk IH]; intros tbl' tblC' i' iC' [g] HC' Hk;
      match goal with |- (_ <= ?R)%nat => remember R as RR eqn:ERR end; cost_simpl;
      pose proof (bdec_time (i' <? n) (bool_w (i' <? n))) as HB;
      cost_destruct (bdec (i' <? n)); cost_simpl.
    - exfalso. exact (gap_0 _ _ Hk e).
    - lia.
    - zl fill_row_cost 5%nat. gen_fill_row. pose proof (gap_le n i'). match goal with |- context [@cost ?T (?G' x xC n nC ?tbl2 ?tblC2 (i' + 1)%uint63 ?w ?hh ?ee)] => have HI := (IH tbl2 tblC2 (i' + 1)%uint63 w hh ee (gap_S _ _ _ Hk e) : (@cost T (G' x xC n nC tbl2 tblC2 (i' + 1)%uint63 w hh ee) <= _)%nat) end. nia.
    - lia. }
  match goal with |- context [@cost ?T (?G x xC n nC tbl tblC i iC H HC)] =>
    exact (HG _ tbl tblC i iC H HC (le_n _) : (@cost T (G x xC n nC tbl tblC i iC H HC) <= _)%nat) end.
Qed.
Ltac gen_fill_tab := repeat match goal with |- context [@cost ?T (extract (extract (extract (extract (fill_tab_cost _ ?x ?xC) ?n ?nC) ?tbl ?tblC) ?i ?iC) ?H ?HC)] =>
    let Hc := fresh "Hfill_tab" in
    have Hc := (fill_tab_time x xC n nC tbl tblC i iC H HC : (@cost T (extract (extract (extract (extract (fill_tab_cost stepsCM x xC) n nC) tbl tblC) i iC) H HC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (extract (extract (fill_tab_cost stepsCM x xC) n nC) tbl tblC) i iC) H HC)); intros ? Hc end.

Lemma sat_time n nC s sC t tC tbl tblC ex exC q qC ql qlC v vC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (sat_cost stepsCM n nC) s sC) t tC) tbl tblC) ex exC) q qC) ql qlC) v vC) H HC) <= Z.to_nat (gap n v) * (300) + 10)%nat.
Proof.
  unfold sat_cost. cbn.
  match goal with |- context [@cost ?T (?G n nC s sC t tC tbl tblC ex exC q qC ql qlC v vC H HC)] =>
    assert (HG : forall kk tbl tblC ex exC q qC ql qlC v vC H HC, (Z.to_nat (gap n v) <= kk)%nat ->
       (cost (G n nC s sC t tC tbl tblC ex exC q qC ql qlC v vC H HC) <= kk * (300) + 10)%nat) end.
  { induction kk as [|kk IH]; intros tbl' tblC' ex' exC' q' qC' ql' qlC' v' vC' [g] HC' Hk;
      match goal with |- (_ <= ?R)%nat => remember R as RR eqn:ERR end; cost_simpl;
      pose proof (bdec_time (v' <? n) (bool_w (v' <? n))) as HB;
      cost_destruct (bdec (v' <? n)); cost_simpl.
    - exfalso. exact (gap_0 _ _ Hk e).
    - lia.
    - cost_destruct (0 <? tbl'.[s * n + v']); cost_simpl; try cost_destruct (v' =? t); cost_simpl; try cost_destruct (v' =? s); cost_simpl; prim_simpl; gen_negb; match goal with |- context [@cost ?T (?G' n nC s sC t tC ?tbl2 ?tblC2 ?ex2 ?exC2 ?q2 ?qC2 ?ql2 ?qlC2 (v' + 1)%uint63 ?w ?hh ?ee)] => have HI := (IH tbl2 tblC2 ex2 exC2 q2 qC2 ql2 qlC2 (v' + 1)%uint63 w hh ee (gap_S _ _ _ Hk e) : (@cost T (G' n nC s sC t tC tbl2 tblC2 ex2 exC2 q2 qC2 ql2 qlC2 (v' + 1)%uint63 w hh ee) <= _)%nat) end; lia.
    - lia. }
  match goal with |- context [@cost ?T (?G n nC s sC t tC tbl tblC ex exC q qC ql qlC v vC H HC)] =>
    exact (HG _ tbl tblC ex exC q qC ql qlC v vC H HC (le_n _) : (@cost T (G n nC s sC t tC tbl tblC ex exC q qC ql qlC v vC H HC) <= _)%nat) end.
Qed.
Ltac gen_sat := repeat match goal with |- context [@cost ?T (extract (extract (extract (extract (extract (extract (extract (extract (sat_cost _ ?n ?nC) ?s ?sC) ?t ?tC) ?tbl ?tblC) ?ex ?exC) ?q ?qC) ?ql ?qlC) ?v ?vC) ?H ?HC)] =>
    let Hc := fresh "Hsat" in
    have Hc := (sat_time n nC s sC t tC tbl tblC ex exC q qC ql qlC v vC H HC : (@cost T (extract (extract (extract (extract (extract (extract (extract (extract (sat_cost stepsCM n nC) s sC) t tC) tbl tblC) ex exC) q qC) ql qlC) v vC) H HC) <= _)%nat);
    revert Hc; generalize (@cost T (extract (extract (extract (extract (extract (extract (extract (extract (sat_cost stepsCM n nC) s sC) t tC) tbl tblC) ex exC) q qC) ql qlC) v vC) H HC)); intros ? Hc end.




Lemma nn_time x xC : (cost (nn_cost stepsCM x xC) <= 10)%nat.
Proof. unfold nn_cost. cost_simpl. lia. Qed.
Ltac gen_nn := repeat match goal with |- context [@cost ?T (nn_cost _ ?x ?xC)] =>
    let Hc := fresh "Hnn" in
    have Hc := (nn_time x xC : (@cost T (nn_cost stepsCM x xC) <= _)%nat);
    revert Hc; generalize (@cost T (nn_cost stepsCM x xC)); intros ? Hc end.



Lemma ss_time x xC : (cost (ss_cost stepsCM x xC) <= Z.to_nat (φ (PArray.length x)) * 100 + 50)%nat.
Proof.
  unfold ss_cost. cost_simpl. gen_nn. zl amin_cost 4%nat. gen_amin.
  pose proof (gap_le (PArray.length x) 1). lia.
Qed.
Lemma tt_time x xC : (cost (tt_cost stepsCM x xC) <= Z.to_nat (φ (PArray.length x)) * 100 + 50)%nat.
Proof.
  unfold tt_cost. cost_simpl. gen_nn. zl amax_cost 4%nat. gen_amax.
  pose proof (gap_le (PArray.length x) 1). lia.
Qed.
Ltac gen_ss := repeat match goal with |- context [@cost ?T (ss_cost _ ?x ?xC)] =>
    let Hc := fresh "Hss" in
    have Hc := (ss_time x xC : (@cost T (ss_cost stepsCM x xC) <= _)%nat);
    revert Hc; generalize (@cost T (ss_cost stepsCM x xC)); intros ? Hc end.
Ltac gen_tt := repeat match goal with |- context [@cost ?T (tt_cost _ ?x ?xC)] =>
    let Hc := fresh "Htt" in
    have Hc := (tt_time x xC : (@cost T (tt_cost stepsCM x xC) <= _)%nat);
    revert Hc; generalize (@cost T (tt_cost stepsCM x xC)); intros ? Hc end.

Lemma guard_time x xC : (cost (guard_cost stepsCM x xC) <= Z.to_nat (φ (PArray.length x)) * 400 + 400)%nat.
Proof.
  unfold guard_cost. cost_simpl. gen_nn. gen_ss. gen_tt. zl rng_ok_cost 3%nat. gen_rng_ok. gen_negb.
  pose proof (gap_le (PArray.length x) 0). fin_br; lia.
Qed.
Ltac gen_guard := repeat match goal with |- context [@cost ?T (guard_cost _ ?x ?xC)] =>
    let Hc := fresh "Hguard" in
    have Hc := (guard_time x xC : (@cost T (guard_cost stepsCM x xC) <= _)%nat);
    revert Hc; generalize (@cost T (guard_cost stepsCM x xC)); intros ? Hc end.

Lemma init_state_time x xC :
  (cost (init_state_cost stepsCM x xC) <= (Z.to_nat (φ (PArray.length x)) + 1) * (Z.to_nat (φ (PArray.length x)) + 1) * (Z.to_nat (φ (PArray.length x)) + 1) * (100 * 100))%nat.
Proof.
  unfold init_state_cost. cost_simpl. gen_nn. gen_ss. gen_tt. zl fill_tab_cost 4%nat. gen_fill_tab.
  zl sat_cost 8%nat. gen_sat. zl glob_cost 4%nat. gen_glob. zl count_cost 2%nat. gen_count. prim_simpl.
  match goal with |- context [@extract ?CM ?T ?X] => lazymatch T with prod_cost _ _ _ _ _ (sat ?a ?b ?c ?d ?e ?f ?g ?h ?i) =>
    generalize (@extract CM T X); generalize (sat a b c d e f g h i) end end.
  intros o w. destruct w as [p1 p1C ql qlC].
  destruct p1C as [p2 p2C q qC]. destruct p2C as [tb tbC ex exC].
  cbn [cost projT1 projT2 fst snd]. prim_simpl.
  rewrite !gap0 in Hfill_tab Hsat.
  revert Hss Htt Hfill_tab Hsat Hglob Hcount. generalize (Z.to_nat (φ (PArray.length x))). intros M. intros. nia.
Qed.


#[local] Arguments Uint63.to_Z : simpl never.
#[local] Arguments gap : simpl never.
#[local] Arguments gcd_loop_cost : simpl never.
#[local] Arguments igcd_cost : simpl never.
#[local] Arguments capf_cost : simpl never.
#[local] Arguments fill_row_cost : simpl never.
#[local] Arguments fill_tab_cost : simpl never.
#[local] Arguments amin_cost : simpl never.
#[local] Arguments amax_cost : simpl never.
#[local] Arguments rng_ok_cost : simpl never.
#[local] Arguments sat_cost : simpl never.
#[local] Arguments amap_cost : simpl never.
#[local] Arguments relaxF_cost : simpl never.
#[local] Arguments has_val_cost : simpl never.
#[local] Arguments lscan_cost : simpl never.
#[local] Arguments layers_cost : simpl never.
#[local] Arguments bfs_cost : simpl never.
#[local] Arguments maxF_cost : simpl never.
#[local] Arguments glob_cost : simpl never.
#[local] Arguments cntl_cost : simpl never.
#[local] Arguments count_cost : simpl never.
#[local] Arguments rmin_cost : simpl never.
#[local] Arguments no_height_cost : simpl never.
#[local] Arguments liftF_cost : simpl never.
#[local] Arguments lift_cost : simpl never.
#[local] Arguments cnt_lift_cost : simpl never.
#[local] Arguments active_cost : simpl never.
#[local] Arguments find_act_cost : simpl never.
#[local] Arguments adm_cost : simpl never.
#[local] Arguments enq_pos_cost : simpl never.
#[local] Arguments mloop_cost : simpl never.
#[local] Arguments nn_cost : simpl never.
#[local] Arguments ss_cost : simpl never.
#[local] Arguments tt_cost : simpl never.
#[local] Arguments guard_cost : simpl never.
#[local] Arguments init_state_cost : simpl never.


Ltac gen_init_state := repeat match goal with |- context [@cost ?T (init_state_cost _ ?x ?xC)] =>
    let Hc := fresh "Hinit_state" in
    have Hc := (init_state_time x xC : (@cost T (init_state_cost stepsCM x xC) <= _)%nat);
    revert Hc; generalize (@cost T (init_state_cost stepsCM x xC)); intros ? Hc end.

#[local] Arguments nn : simpl never.
#[local] Arguments ss : simpl never.
#[local] Arguments tt : simpl never.
#[local] Arguments guard : simpl never.
#[local] Arguments init_state : simpl never.
#[local] Arguments mloop : simpl never.
#[local] Arguments acc_init : simpl never.
Ltac gen_bdec := repeat match goal with |- context [@cost ?T (bdec_cost stepsCM ?b ?w)] =>
    let Hc := fresh "Hbdec" in
    have Hc := (bdec_time b w : (@cost T (bdec_cost stepsCM b w) <= _)%nat);
    revert Hc; generalize (@cost T (bdec_cost stepsCM b w)); intros ? Hc end.
Lemma proj_bound_tbl S w : (cost (s_tbl_cost stepsCM S w) <= 2)%nat. Proof. destruct w; cbn; lia. Qed.
Lemma proj_bound_ex S w : (cost (s_ex_cost stepsCM S w) <= 2)%nat. Proof. destruct w; cbn; lia. Qed.
Lemma proj_bound_h S w : (cost (s_h_cost stepsCM S w) <= 2)%nat. Proof. destruct w; cbn; lia. Qed.
Lemma proj_bound_cur S w : (cost (s_cur_cost stepsCM S w) <= 2)%nat. Proof. destruct w; cbn; lia. Qed.
Lemma proj_bound_cnt S w : (cost (s_cnt_cost stepsCM S w) <= 2)%nat. Proof. destruct w; cbn; lia. Qed.
Lemma proj_bound_q S w : (cost (s_q_cost stepsCM S w) <= 2)%nat. Proof. destruct w; cbn; lia. Qed.
Lemma proj_bound_qh S w : (cost (s_qh_cost stepsCM S w) <= 2)%nat. Proof. destruct w; cbn; lia. Qed.
Lemma proj_bound_ql S w : (cost (s_ql_cost stepsCM S w) <= 2)%nat. Proof. destruct w; cbn; lia. Qed.
Lemma proj_bound_cu S w : (cost (s_cu_cost stepsCM S w) <= 2)%nat. Proof. destruct w; cbn; lia. Qed.
Lemma proj_bound_rl S w : (cost (s_rl_cost stepsCM S w) <= 2)%nat. Proof. destruct w; cbn; lia. Qed.
Ltac gen_proj := repeat match goal with
  | |- context [@cost ?T (?P stepsCM ?S ?w)] =>
    let Hc := fresh "Hproj" in
    first [ have Hc := (proj_bound_tbl S w : (@cost T (P stepsCM S w) <= _)%nat)
          | have Hc := (proj_bound_ex S w : (@cost T (P stepsCM S w) <= _)%nat)
          | have Hc := (proj_bound_h S w : (@cost T (P stepsCM S w) <= _)%nat)
          | have Hc := (proj_bound_cur S w : (@cost T (P stepsCM S w) <= _)%nat)
          | have Hc := (proj_bound_cnt S w : (@cost T (P stepsCM S w) <= _)%nat)
          | have Hc := (proj_bound_q S w : (@cost T (P stepsCM S w) <= _)%nat)
          | have Hc := (proj_bound_qh S w : (@cost T (P stepsCM S w) <= _)%nat)
          | have Hc := (proj_bound_ql S w : (@cost T (P stepsCM S w) <= _)%nat)
          | have Hc := (proj_bound_cu S w : (@cost T (P stepsCM S w) <= _)%nat)
          | have Hc := (proj_bound_rl S w : (@cost T (P stepsCM S w) <= _)%nat) ];
    revert Hc; generalize (@cost T (P stepsCM S w)); intros ? Hc end.

Lemma bdec_bound b w : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. apply bdec_time. Qed.

Local Strategy opaque [init_state guard ss tt nn mloop acc_init amin amax rng_ok fill_tab sat glob count].
Lemma impl_time x xC : guard x = true ->
  (cost (mazemovement_impl_cost stepsCM x xC) <=
   (Z.to_nat (φ (PArray.length x)) + 1) * (Z.to_nat (φ (PArray.length x)) + 1) * (Z.to_nat (φ (PArray.length x)) + 1) * (Z.to_nat (φ (PArray.length x)) + 1) * (1000 * 50))%nat.
Proof.
  intros Hg. match goal with |- (_ <= ?R)%nat => remember R as RR eqn:ERR end.
  unfold mazemovement_impl_cost. cost_simpl. gen_guard. gen_bdec.
  cost_destruct (bdec (guard x)); cost_simpl; [|congruence].
  zl mloop_cost 13%nat. gen_init_state. gen_nn. gen_ss. gen_tt. gen_proj.
  destruct (guard_facts x Hg) as [Hn [Hs [Ht [Hst [Hx _]]]]].
  set (S0 := mkst (s_tbl (init_state x)) (s_ex (init_state x)) (s_h (init_state x)) (s_cur (init_state x))
               (s_cnt (init_state x)) (s_q (init_state x)) (s_qh (init_state x)) (s_ql (init_state x))
               (s_cu (init_state x)) (s_rl (init_state x))).
  assert (E0 : S0 = init_state x) by (unfold S0; destruct (init_state x); reflexivity).
  assert (I0 : Inv (nn x) (ss x) (tt x) (cpx x (nn x)) S0) by (rewrite E0; exact (init_inv x Hg)).
  assert (Q0 : QOK (nn x) (ss x) (tt x) S0) by (rewrite E0; exact (init_qok x Hg)).
  match goal with |- context [@cost ?T ?X] => lazymatch X with (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (mloop_cost _ ?n ?nC) ?s ?sC) ?t ?tC) ?tb ?tbC) ?e1 ?eC) ?h1 ?hC) ?cr ?crC) ?cn ?cnC) ?q1 ?qC) ?qh1 ?qhC) ?ql1 ?qlC) ?cu1 ?cuC) ?rl1 ?rlC) ?H ?HC) =>
    have HM := mloop_time n s t (cpx x (nn x)) Hn Hs Ht Hst (cp_rng (nn x) 0 0 x Hx) S0 (acc_init x e) I0 Q0
                 nC sC tC tb tbC e1 eC h1 hC cr crC cn cnC q1 qC qh1 qhC ql1 qlC cu1 cuC rl1 rlC H HC eq_refl;
    change (cost (mloop_fix n nC s sC t tC tb tbC e1 eC h1 hC cr crC cn cnC q1 qC qh1 qhC ql1 qlC cu1 cuC rl1 rlC H HC))
      with (@cost T X) in HM;
    revert HM; generalize (@cost T X); intros m HM end end.
  assert (PB : (Pot (nn x) (ss x) (tt x) 1000 S0 <= 30 * 1000 * ((φ (nn x) + 1) * (φ (nn x) + 1) * (φ (nn x) + 1) * (φ (nn x) + 1)))%Z)
    by (eapply Pot_bound; eauto; lia).
  change (nn x) with (PArray.length x) in HM, PB.
  assert (EM : Z.of_nat (Z.to_nat (φ (PArray.length x))) = φ (PArray.length x))
    by (pose proof (to_Z_bounded (PArray.length x)); lia).
  revert HM PB. generalize (Pot (PArray.length x) (ss x) (tt x) 1000 S0). intros P HM PB.
  set (M := Z.to_nat (φ (PArray.length x))) in *.
  assert (Hm : (m <= (M + 1) * (M + 1) * (M + 1) * (M + 1) * (1000 * 30) + (M + 1) * 1000)%nat).
  { rewrite <- EM in HM, PB. clear - HM PB. nia. }
  subst RR. clearbody M.
  assert (F1 : (1 <= (M + 1) * (M + 1) * (M + 1))%nat) by nia.
  assert (F2 : ((M + 1) * (M + 1) * (M + 1) <= (M + 1) * (M + 1) * (M + 1) * (M + 1))%nat) by nia.
  assert (F3 : (M + 1 <= (M + 1) * (M + 1) * (M + 1))%nat) by nia.
  revert Hm Hinit_state F1 F2 F3.
  generalize ((M + 1) * (M + 1) * (M + 1) * (M + 1))%nat. intros Q4. generalize ((M + 1) * (M + 1) * (M + 1))%nat. intros Q3. intros.
  repeat match goal with H : _ |- _ => lazymatch type of H with (_ <= _)%nat => fail | nat => fail | _ => clear H end end.
  lia.
Qed.


Theorem mazemovement_time : exists c1 c2 : nat,
  forall (rooms : list N) (rooms_arr : array uint),
  valid_input rooms -> repr rooms_arr rooms ->
  (cost1 mazemovement_cost rooms_arr <= c1 * ((size rooms_arr + 1) * (size rooms_arr + 1) * (size rooms_arr + 1) * (size rooms_arr + 1)) + c2)%nat.
Proof.
  exists (1000 * 50)%nat, 0%nat. intros rooms x Hv Hr.
  pose proof (f_guard rooms x Hv Hr) as Hg.
  match goal with |- (_ <= ?R)%nat => remember R as RR eqn:ERR end.
  unfold cost1, mazemovement_cost.
  match goal with |- (@cost ?T ?X <= _)%nat =>
    pose proof (impl_time x (witness x) Hg : (@cost T X <= _)%nat) as Hi;
    revert Hi; generalize (@cost T X); intros c Hi end.
  assert (Hi' : (c <= (size x + 1) * (size x + 1) * (size x + 1) * (size x + 1) * (1000 * 50))%nat) by exact Hi.
  subst RR. clear Hi. revert Hi'. generalize (size x + 1)%nat. intros P Hi.
  revert Hi. generalize (P * P * P * P)%nat. intros Q Hi. lia.
Qed.
