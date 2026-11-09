(* Executable implementation and its required termination dependencies.
   Correctness proofs are in minspantree_proofs.v. *)
(* Implementation of minspantree (minspantree.spec): Kruskal. *)

From Minspantree.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import FinFun.
From Stdlib Require Import Permutation.
From Stdlib Require Sint63.
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

Lemma dec_lt : forall m lo hi : int,
  (lo <? m) = true -> (lo <? hi) = true -> Zwf 0 (gap m hi) (gap m lo).
Proof.
  intros m lo hi H1 H2. rewrite ltb_spec in H1, H2. unfold Zwf, gap. lia.
Qed.

(* the measure of find: the rank of the node, from above *)
Definition rgap (rk : array int) (v : int) : Z := (wB - (φ (rk.[v])))%Z.

Lemma rdec : forall (rk : array int) (v u : int),
  (rk.[v] <? rk.[u]) = true -> Zwf 0 (rgap rk u) (rgap rk v).
Proof.
  intros rk v u H. rewrite ltb_spec in H. unfold Zwf, rgap.
  pose proof (to_Z_bounded (rk.[v])). pose proof (to_Z_bounded (rk.[u])). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* a.[k] := k for k = i .. m-1 *)
Fixpoint iota_loop (m i : int) (a : array int)
    (H : Acc (Zwf 0) (gap m i)) {struct H} : array int :=
  match bdec (i <? m) with
  | left Hi => iota_loop m (i + 1) a.[i <- i] (Acc_inv H (dec_step m i Hi))
  | right _ => a
  end.

Definition iota (m : int) : array int :=
  iota_loop m 0 (PArray.make m 0) (Zwf_well_founded 0 (gap m 0)).

(* Merge src[i..iend) and src[j..jend) into dst[k..kend), by signed
   weight ws.[_] of the indices. *)
Fixpoint merge_loop (ws src : array int) (iend jend kend : int)
    (i j k : int) (dst : array int)
    (H : Acc (Zwf 0) (gap kend k)) {struct H} : array int :=
  match bdec (k <? kend) with
  | left Hk =>
      if (if i <? iend then
            (if j <? jend then Sint63.leb ws.[src.[i]] ws.[src.[j]] else true)
          else false)
      then merge_loop ws src iend jend kend (i + 1) j (k + 1) dst.[k <- src.[i]]
             (Acc_inv H (dec_step kend k Hk))
      else merge_loop ws src iend jend kend i (j + 1) (k + 1) dst.[k <- src.[j]]
             (Acc_inv H (dec_step kend k Hk))
  | right _ => dst
  end.

(* x + w, capped at m *)
Definition step_end (m w x : int) : int := if w <? m - x then x + w else m.

(* One pass: merge the consecutive runs of width w of src, from lo on. *)
Fixpoint pass_loop (ws src : array int) (m w lo : int) (dst : array int)
    (H : Acc (Zwf 0) (gap m lo)) {struct H} : array int :=
  match bdec (lo <? m) with
  | left Hlo =>
      let mid := step_end m w lo in
      let hi := step_end m w mid in
      match bdec (lo <? hi) with
      | left Hlh =>
          pass_loop ws src m w hi
            (merge_loop ws src mid hi hi lo mid lo dst
               (Zwf_well_founded 0 (gap hi lo)))
            (Acc_inv H (dec_lt m lo hi Hlo Hlh))
      | right _ => dst
      end
  | right _ => dst
  end.

(* Bottom-up merge sort: widths w, 2w, 4w, ... *)
Fixpoint sort_loop (ws : array int) (m w : int) (src dst : array int)
    (H : Acc (Zwf 0) (gap m w)) {struct H} : array int :=
  match bdec (w <? m) with
  | left Hw =>
      match bdec (w <? w + w) with
      | left Hww =>
          sort_loop ws m (w + w)
            (pass_loop ws src m w 0 dst (Zwf_well_founded 0 (gap m 0)))
            src (Acc_inv H (dec_lt m w (w + w) Hw Hww))
      | right _ => src
      end
  | right _ => src
  end.

Definition sort_edges (ws : array int) (m : int) : array int :=
  sort_loop ws m 1 (iota m) (PArray.make m 0) (Zwf_well_founded 0 (gap m 1)).

(* Union-find: the root of v; along a parent link the rank increases
   strictly (checked, which gives the measure). *)
Fixpoint find (par rk : array int) (v : int)
    (H : Acc (Zwf 0) (rgap rk v)) {struct H} : int :=
  let u := par.[v] in
  if u =? v then v
  else match bdec (rk.[v] <? rk.[u]) with
       | left Hr => find par rk u (Acc_inv H (rdec rk v u Hr))
       | right _ => v
       end.

Definition findr (par rk : array int) (v : int) : int :=
  find par rk v (Zwf_well_founded 0 (rgap rk v)).

(* The scan of the sorted edges ord.[q], ord.[q+1], ... *)
Fixpoint scan (n : int) (us vs ws ord : array int) (m : int)
    (q : int) (par rk out : array int) (cnt cost : int)
    (H : Acc (Zwf 0) (gap m q)) {struct H} : option (int * array int) :=
  match bdec (q <? m) with
  | left Hq =>
      let e := ord.[q] in
      let a := findr par rk us.[e] in
      let b := findr par rk vs.[e] in
      if a =? b then
        scan n us vs ws ord m (q + 1) par rk out cnt cost
          (Acc_inv H (dec_step m q Hq))
      else
        let ra := rk.[a] in
        let rb := rk.[b] in
        if ra <? rb then
          scan n us vs ws ord m (q + 1) par.[a <- b] rk out.[cnt <- e]
            (cnt + 1) (cost + ws.[e]) (Acc_inv H (dec_step m q Hq))
        else if rb <? ra then
          scan n us vs ws ord m (q + 1) par.[b <- a] rk out.[cnt <- e]
            (cnt + 1) (cost + ws.[e]) (Acc_inv H (dec_step m q Hq))
        else
          scan n us vs ws ord m (q + 1) par.[a <- b] rk.[b <- rb + 1]
            out.[cnt <- e] (cnt + 1) (cost + ws.[e])
            (Acc_inv H (dec_step m q Hq))
  | right _ => if cnt =? n - 1 then Some (cost, out) else None
  end.

Definition mst_impl (n : int) (us vs ws : array int) : option (int * array int) :=
  let m := PArray.length us in
  scan n us vs ws (sort_edges ws m) m 0 (iota n) (PArray.make n 0)
    (PArray.make (n - 1) 0) 0 0 (Zwf_well_founded 0 (gap m 0)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition mst : uint -> array uint -> array uint -> array sint ->
                 option (sint * array uint) := mst_impl.
