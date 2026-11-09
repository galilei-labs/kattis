(* Executable implementation and its required termination dependencies.
   Correctness proofs are in kingpinescape_proofs.v. *)
(* Implementation of kingpinescape (kingpinescape.spec): tree augmentation
   by leaf pairing.

   Code.  deg[v] is counted from the two columns (cnt_loop, once per
   column); pos = prefix sums of deg (pre_loop); the adjacency is a flat CSR
   table adj of the 2(n-1) half-edges (half-edge j < m is passageway j seen
   from ea[j], half-edge m + j the same passageway seen from eb[j]), filled
   by counting sort (fill_loop, once per column); after it, the slots of v
   are adj[pos[v] - deg[v] .. pos[v] - 1] and the other end of half-edge hh
   is [other].  The root is the first vertex of degree >= 2 (root_loop; 0
   when there is none, i.e. n = 2).  dfs_loop is the depth-first traversal
   with an explicit stack stk[0 .. sp-1] (a vertex is marked when pushed);
   every popped vertex of degree 1 is appended to lv, so lv lists the L
   leaves in visiting order.  The answer pairs lv[i] with lv[i + L/2] for
   i < L - L/2 (out_loop).  Every array is threaded linearly.  h is not
   read: making the network bridgeless is what the contract asks.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) (gap _ _)] proof, as in template/polymul1.

   Proof.  The math side works over a "traversal" (Section Tree): the visiting
   order ord, ghost parent pointers par and parent passageways pe, with
   par(v) visited before v and, for consecutive vertices of ord, par of the
   later one an ancestor-or-self of the earlier one.  From that: pe is a
   bijection from the non-root vertices onto the passageways (pigeonhole,
   so the input is a simple tree without any use of route uniqueness),
   subtrees are contiguous in ord, leaves of a subtree are an interval of
   the leaf order, a proper non-empty interval is crossed by the pairing
   (cross), so every tree edge lies on a cycle (cross_edge) and the network
   is safe (tree_spec).  Minimality: a leaf's only passageway blocked, the
   leaf can only leave by a new passageway, so 2|F| >= L (leaf_needs).
   The machine side (Section Machine) proves each loop against those ghost
   objects (cnt_spec, pre_spec, fill_spec, nb_spec, dfs_spec, out_spec). *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Permutation.
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

(* deg[col[j]] += 1 for j = i .. m-1 *)
Fixpoint cnt_loop (col : array int) (m i : int) (deg : array int)
    (H : Acc (Zwf 0) (gap m i)) {struct H} : array int :=
  match bdec (i <? m) with
  | left Hi =>
      let v := col.[i] in
      cnt_loop col m (i + 1) deg.[v <- deg.[v] + 1] (Acc_inv H (dec_step m i Hi))
  | right _ => deg
  end.

(* pos[v] = acc + deg[i] + ... + deg[v-1] for v = i .. n-1 *)
Fixpoint pre_loop (deg : array int) (n i acc : int) (pos : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi =>
      pre_loop deg n (i + 1) (acc + deg.[i]) pos.[i <- acc]
        (Acc_inv H (dec_step n i Hi))
  | right _ => pos
  end.

(* half-edge base+j (at vertex col[j]) goes to slot pos[col[j]], which then
   moves on *)
Fixpoint fill_loop (col : array int) (base m i : int) (pos adj : array int)
    (H : Acc (Zwf 0) (gap m i)) {struct H} : array int * array int :=
  match bdec (i <? m) with
  | left Hi =>
      let v := col.[i] in
      let p := pos.[v] in
      fill_loop col base m (i + 1) pos.[v <- p + 1] adj.[p <- base + i]
        (Acc_inv H (dec_step m i Hi))
  | right _ => (pos, adj)
  end.

(* the other end of half-edge hh *)
Definition other (ea eb : array int) (m hh : int) : int :=
  if hh <? m then eb.[hh] else ea.[hh - m].

(* the neighbours, through slots s .. e-1, of the vertex being visited:
   every unmarked one is marked and pushed *)
Fixpoint nb_loop (ea eb adj : array int) (m e s : int)
    (mark stk : array int) (sp : int)
    (H : Acc (Zwf 0) (gap e s)) {struct H} : array int * array int * int :=
  match bdec (s <? e) with
  | left Hs =>
      let w := other ea eb m adj.[s] in
      if mark.[w] =? 0 then
        nb_loop ea eb adj m e (s + 1) mark.[w <- 1] stk.[sp <- w] (sp + 1)
          (Acc_inv H (dec_step e s Hs))
      else
        nb_loop ea eb adj m e (s + 1) mark stk sp
          (Acc_inv H (dec_step e s Hs))
  | right _ => (mark, stk, sp)
  end.

(* the depth-first traversal, explicit stack stk[0 .. sp-1]; the leaves are
   listed in lv[0 .. L-1] in visiting order *)
Fixpoint dfs_loop (ea eb adj deg pos : array int) (n m t : int)
    (mark stk : array int) (sp : int) (lv : array int) (L : int)
    (H : Acc (Zwf 0) (gap n t)) {struct H} : array int * int :=
  match bdec (t <? n) with
  | left Ht =>
      if 0 <? sp then
        let v := stk.[sp - 1] in
        let dv := deg.[v] in
        let e := pos.[v] in
        let lv' := if dv =? 1 then lv.[L <- v] else lv in
        let L' := if dv =? 1 then L + 1 else L in
        match nb_loop ea eb adj m e (e - dv) mark stk (sp - 1)
                (Zwf_well_founded 0 (gap e (e - dv))) with
        | (mark', stk', sp') =>
            dfs_loop ea eb adj deg pos n m (t + 1) mark' stk' sp' lv' L'
              (Acc_inv H (dec_step n t Ht))
        end
      else (lv, L)
  | right _ => (lv, L)
  end.

(* the first vertex of degree at least 2, or 0 *)
Fixpoint root_loop (deg : array int) (n i : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : int :=
  match bdec (i <? n) with
  | left Hi =>
      if 2 <=? deg.[i] then i
      else root_loop deg n (i + 1) (Acc_inv H (dec_step n i Hi))
  | right _ => 0
  end.

(* xs[i] = lv[i], ys[i] = lv[i + a] for i .. c-1 *)
Fixpoint out_loop (lv : array int) (a c i : int) (xs ys : array int)
    (H : Acc (Zwf 0) (gap c i)) {struct H} : array int * array int :=
  match bdec (i <? c) with
  | left Hi =>
      out_loop lv a c (i + 1) xs.[i <- lv.[i]] ys.[i <- lv.[i + a]]
        (Acc_inv H (dec_step c i Hi))
  | right _ => (xs, ys)
  end.

Definition kingpin_impl (n h : int) (ea eb : array int) : array int * array int :=
  let m := n - 1 in
  let deg0 := cnt_loop ea m 0 (PArray.make n 0) (Zwf_well_founded 0 (gap m 0)) in
  let deg := cnt_loop eb m 0 deg0 (Zwf_well_founded 0 (gap m 0)) in
  let pos0 := pre_loop deg n 0 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)) in
  match fill_loop ea 0 m 0 pos0 (PArray.make (m + m) 0)
          (Zwf_well_founded 0 (gap m 0)) with
  | (pos1, adj1) =>
    match fill_loop eb m m 0 pos1 adj1 (Zwf_well_founded 0 (gap m 0)) with
    | (pos, adj) =>
      let r := root_loop deg n 0 (Zwf_well_founded 0 (gap n 0)) in
      let mark := (PArray.make n 0).[r <- 1] in
      let stk := (PArray.make n 0).[0 <- r] in
      match dfs_loop ea eb adj deg pos n m 0 mark stk 1 (PArray.make n 0) 0
              (Zwf_well_founded 0 (gap n 0)) with
      | (lv, L) =>
        let a := L >> 1 in
        let c := L - a in
        out_loop lv a c 0 (PArray.make c 0) (PArray.make c 0)
          (Zwf_well_founded 0 (gap c 0))
      end
    end
  end.

(* ------------------------------------------------------------------ *)
(* Routes: reaches is an equivalence, monotone in the passageways      *)
(* ------------------------------------------------------------------ *)

Open Scope N_scope.

(* ------------------------------------------------------------------ *)
(* The loops                                                           *)
(* ------------------------------------------------------------------ *)

Open Scope uint63_scope.

Open Scope N_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition kingpin_escape :
  uint -> uint -> array uint -> array uint -> array uint * array uint := kingpin_impl.
