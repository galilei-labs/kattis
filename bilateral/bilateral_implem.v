(* Executable implementation and its required termination dependencies.
   Correctness proofs are in bilateral_proofs.v. *)
(* Implementation of bilateral (bilateral.spec).

   A minimum vertex cover of the bipartite team graph by König's theorem:
   CSR adjacency, maximum matching by augmenting paths (one breadth-first
   alternating search from all free left vertices per phase, augmentation
   along the parent pointers), König's cover read off the failed search.
   The friend (1009) is preferred by computing the cover twice, on the
   graph without the friend's teams (C') and on the whole graph (C): if
   |C'| + 1 <= |C|, C' plus the friend is a smallest invitation, otherwise
   no smallest invitation contains the friend.  Flat Uint63 arrays only;
   every loop terminates on an erased Acc. *)

From Bilateral.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
Import ListNotations.

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

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Vertices: Stockholm employee 1000 + u is left vertex u, London employee
   2000 + v is right vertex v, u, v < NV.  A mate >= NV means "free". *)
Definition NV : int := 1000.
Definition NP : int := 1001.
Definition NM : int := 2000.

(* Degree of every left vertex, over the teams not owned by ex. *)
Fixpoint deg_loop (x : array int) (ex m k : int) (d : array int)
    (H : Acc (Zwf 0) (gap m k)) {struct H} : array int :=
  match bdec (k <? m) with
  | left Hk =>
      let a := x.[k] in
      deg_loop x ex m (k + 1)
        (if a =? ex then d else let u := a - 1000 in d.[u <- d.[u] + 1])
        (Acc_inv H (dec_step m k Hk))
  | right _ => d
  end.

(* Prefix sums: o.[u+1] = o.[u] + d.[u]. *)
Fixpoint off_loop (d : array int) (u : int) (o : array int)
    (H : Acc (Zwf 0) (gap NV u)) {struct H} : array int :=
  match bdec (u <? NV) with
  | left Hu => off_loop d (u + 1) o.[u + 1 <- o.[u] + d.[u]]
                 (Acc_inv H (dec_step NV u Hu))
  | right _ => o
  end.

(* Placement of the targets, pos being the cursors. *)
Fixpoint fill_loop (x y : array int) (ex m k : int) (pos tg : array int)
    (H : Acc (Zwf 0) (gap m k)) {struct H} : array int :=
  match bdec (k <? m) with
  | left Hk =>
      let a := x.[k] in
      if a =? ex then fill_loop x y ex m (k + 1) pos tg (Acc_inv H (dec_step m k Hk))
      else
        let u := a - 1000 in
        let p := pos.[u] in
        fill_loop x y ex m (k + 1) pos.[u <- p + 1] tg.[p <- y.[k] - 2000]
          (Acc_inv H (dec_step m k Hk))
  | right _ => tg
  end.

(* The free left vertices are the roots of the search: queue Q, positions
   qp (0 = not visited, i+1 = at queue position i). *)
Fixpoint root_loop (mL : array int) (u : int) (Q qp : array int) (t : int)
    (H : Acc (Zwf 0) (gap NV u)) {struct H} : array int * array int * int :=
  match bdec (u <? NV) with
  | left Hu =>
      if mL.[u] <? NV then root_loop mL (u + 1) Q qp t (Acc_inv H (dec_step NV u Hu))
      else root_loop mL (u + 1) Q.[t <- u] qp.[u <- t + 1] (t + 1)
             (Acc_inv H (dec_step NV u Hu))
  | right _ => (Q, qp, t)
  end.

Inductive sres :=
| SFound (v : int) (qp pr : array int)
| SCont (Q qp pr : array int) (t : int).

(* The neighbours tg.[p], p in [p, pe), of left vertex u; pr.[v] = parent + 1
   (0 = right vertex not visited). *)
Fixpoint scan (tg mR : array int) (u pe p : int) (Q qp pr : array int) (t : int)
    (H : Acc (Zwf 0) (gap pe p)) {struct H} : sres :=
  match bdec (p <? pe) with
  | left Hp =>
      let v := tg.[p] in
      if pr.[v] =? 0 then
        let pr := pr.[v <- u + 1] in
        let w := mR.[v] in
        if w <? NV then
          if qp.[w] =? 0 then
            scan tg mR u pe (p + 1) Q.[t <- w] qp.[w <- (t + 1)%uint63] pr (t + 1)
              (Acc_inv H (dec_step pe p Hp))
          else scan tg mR u pe (p + 1) Q qp pr t (Acc_inv H (dec_step pe p Hp))
        else SFound v qp pr
      else scan tg mR u pe (p + 1) Q qp pr t (Acc_inv H (dec_step pe p Hp))
  | right _ => SCont Q qp pr t
  end.

Inductive bres :=
| BFound (v : int) (qp pr : array int)
| BFail (qp pr : array int).

(* Breadth-first alternating search from all the roots at once. *)
Fixpoint bfs (off tg mR : array int) (h t : int) (Q qp pr : array int)
    (H : Acc (Zwf 0) (gap NV h)) {struct H} : bres :=
  match bdec (h <? NV) with
  | left Hh =>
      if h <? t then
        let u := Q.[h] in
        match scan tg mR u off.[u + 1] off.[u] Q qp pr t
                (Zwf_well_founded 0 (gap off.[u + 1] off.[u])) with
        | SFound v qp pr => BFound v qp pr
        | SCont Q qp pr t => bfs off tg mR (h + 1) t Q qp pr (Acc_inv H (dec_step NV h Hh))
        end
      else BFail qp pr
  | right _ => BFail qp pr
  end.

Definition wmeas (qp pr : array int) (v : int) : Z := (φ (qp.[pr.[v] - 1])).

Lemma wdec : forall qp pr v v',
  (qp.[pr.[v'] - 1] <? qp.[pr.[v] - 1]) = true ->
  Zwf 0 (wmeas qp pr v') (wmeas qp pr v).
Proof.
  intros qp pr v v' H. rewrite ltb_spec in H. unfold Zwf, wmeas.
  pose proof (to_Z_bounded (qp.[pr.[v'] - 1])). lia.
Qed.

(* Augmentation along the parent pointers, from the free right vertex v. *)
Fixpoint walk (qp pr : array int) (v : int) (mL mR : array int)
    (H : Acc (Zwf 0) (wmeas qp pr v)) {struct H} : array int * array int :=
  let u := pr.[v] - 1 in
  let old := mL.[u] in
  let mL' := mL.[u <- v] in
  let mR' := mR.[v <- u] in
  if old <? NV then
    match bdec (qp.[pr.[old] - 1] <? qp.[pr.[v] - 1]) with
    | left Hd => walk qp pr old mL' mR' (Acc_inv H (wdec qp pr v old Hd))
    | right _ => (mL', mR')
    end
  else (mL', mR').

(* Augment until a search fails; return that search's marks. *)
Fixpoint phases (off tg : array int) (it : int) (mL mR : array int)
    (H : Acc (Zwf 0) (gap NP it)) {struct H} : array int * array int :=
  match bdec (it <? NP) with
  | left Hi =>
      let '(Q, qp, t) := root_loop mL 0 (PArray.make NV 0) (PArray.make NV 0) 0
                           (Zwf_well_founded 0 (gap NV 0)) in
      match bfs off tg mR 0 t Q qp (PArray.make NV 0) (Zwf_well_founded 0 (gap NV 0)) with
      | BFound v qp pr =>
          let '(mL, mR) := walk qp pr v mL mR (Zwf_well_founded 0 (wmeas qp pr v)) in
          phases off tg (it + 1) mL mR (Acc_inv H (dec_step NP it Hi))
      | BFail qp pr => (qp, pr)
      end
  | right _ => (PArray.make NV 0, PArray.make NV 0)
  end.

(* König's cover: the unvisited left vertices and the visited right ones;
   vertex index i < 2000 is employee 1000 + i. *)
Fixpoint mark_loop (qp pr : array int) (i : int) (mk : array int)
    (H : Acc (Zwf 0) (gap NM i)) {struct H} : array int :=
  match bdec (i <? NM) with
  | left Hi =>
      mark_loop qp pr (i + 1)
        (if i <? NV then (if qp.[i] =? 0 then mk.[i <- 1] else mk)
         else (if pr.[i - NV] =? 0 then mk else mk.[i <- 1]))
        (Acc_inv H (dec_step NM i Hi))
  | right _ => mk
  end.

(* A minimum vertex cover of the teams not owned by ex. *)
Definition engine (x y : array int) (ex : int) : array int :=
  let m := PArray.length x in
  let d := deg_loop x ex m 0 (PArray.make NV 0) (Zwf_well_founded 0 (gap m 0)) in
  let off := off_loop d 0 (PArray.make NP 0) (Zwf_well_founded 0 (gap NV 0)) in
  let pos := off_loop d 0 (PArray.make NP 0) (Zwf_well_founded 0 (gap NV 0)) in
  let tg := fill_loop x y ex m 0 pos (PArray.make m 0) (Zwf_well_founded 0 (gap m 0)) in
  let '(qp, pr) := phases off tg 0 (PArray.make NV NV) (PArray.make NV NV)
                     (Zwf_well_founded 0 (gap NP 0)) in
  mark_loop qp pr 0 (PArray.make NM 0) (Zwf_well_founded 0 (gap NM 0)).

Fixpoint cnt_loop (mk : array int) (i c : int)
    (H : Acc (Zwf 0) (gap NM i)) {struct H} : int :=
  match bdec (i <? NM) with
  | left Hi =>
      cnt_loop mk (i + 1) (if mk.[i] =? 0 then c else c + 1) (Acc_inv H (dec_step NM i Hi))
  | right _ => c
  end.

Fixpoint out_loop (mk : array int) (i p : int) (out : array int)
    (H : Acc (Zwf 0) (gap NM i)) {struct H} : array int :=
  match bdec (i <? NM) with
  | left Hi =>
      if mk.[i] =? 0 then out_loop mk (i + 1) p out (Acc_inv H (dec_step NM i Hi))
      else out_loop mk (i + 1) (p + 1) out.[p <- 1000 + i] (Acc_inv H (dec_step NM i Hi))
  | right _ => out
  end.

Definition count_marks (mk : array int) : int :=
  cnt_loop mk 0 0 (Zwf_well_founded 0 (gap NM 0)).

Definition build (mk : array int) : array int :=
  out_loop mk 0 0 (PArray.make (count_marks mk) 0) (Zwf_well_founded 0 (gap NM 0)).

Definition bilateral_impl (x y : array uint) : array uint :=
  let mk1 := engine x y 1009 in
  let mk0 := engine x y 0 in
  build (if count_marks mk1 + 1 <=? count_marks mk0 then mk1.[9 <- 1] else mk0).

(* ------------------------------------------------------------------ *)
(* Plumbing: arrays read as functions Z -> Z, counting                 *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.
Open Scope bool_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition bilateral : array uint -> array uint -> array uint := bilateral_impl.
