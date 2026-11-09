(* Executable implementation and its required termination dependencies.
   Correctness proofs are in joinstrings_proofs.v. *)
(* Implementation of joinstrings (joinstrings.spec): linked-list
   splicing, then one balanced concatenation.

   Code.  The strings are the nodes 0 .. n-1 (node u is S_(u+1)).  Two flat
   int tables: [nx] (the successor of a node in its list) and [tl] (the
   last node of the list headed by a node).  Operation "a b" with
   x = a - 1, y = b - 1 sets nx[tl[x]] := y and tl[x] := tl[y]: the list of
   y is spliced after the list of x in O(1), no character is touched.  The
   remaining string is the list of r = a_(N-1) - 1 (node 0 when N = 1): it
   is walked once into a flat table [ord] of its nodes, and the output is
   the balanced concatenation [build lo hi] = cat (build lo mid)
   (build mid hi) of the strings of ord[0 .. c), O(L log N).

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) measure] proof, as in template/polymul1.  Every table is
   threaded linearly (each [set] on the latest version); xs, xa, xb are
   only read. *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import String Ascii.
From Stdlib Require PrimString PString.
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

Definition split_ok (lo hi : int) : bool := (lo <? hi) && (1 <? hi - lo).

Definition mid_of (lo hi : int) : int := lo + (hi - lo) / 2.

Lemma dec_left : forall lo hi : int,
  split_ok lo hi = true -> Zwf 0 (gap (mid_of lo hi) lo) (gap hi lo).
Proof.
  intros lo hi H. unfold split_ok in H.
  apply andb_prop in H. destruct H as [H1 H2].
  rewrite ltb_spec in H1, H2. unfold Zwf, gap, mid_of.
  pose proof (to_Z_bounded lo). pose proof (to_Z_bounded hi).
  assert (E : (φ (hi - lo)) = ((φ hi) - (φ lo))%Z) by sia.
  rewrite E in H2. change (φ 1) with 1%Z in H2. sia.
Qed.

Lemma dec_right : forall lo hi : int,
  split_ok lo hi = true -> Zwf 0 (gap hi (mid_of lo hi)) (gap hi lo).
Proof.
  intros lo hi H. unfold split_ok in H.
  apply andb_prop in H. destruct H as [H1 H2].
  rewrite ltb_spec in H1, H2. unfold Zwf, gap, mid_of.
  pose proof (to_Z_bounded lo). pose proof (to_Z_bounded hi).
  assert (E : (φ (hi - lo)) = ((φ hi) - (φ lo))%Z) by sia.
  rewrite E in H2. change (φ 1) with 1%Z in H2. sia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* tl[i] := i for i = k .. n-1: every node is a one-node list. *)
Fixpoint init_loop (n k : int) (tl : array int)
    (H : Acc (Zwf 0) (gap n k)) {struct H} : array int :=
  match bdec (k <? n) with
  | left Hk => init_loop n (k + 1) tl.[k <- k] (Acc_inv H (dec_step n k Hk))
  | right _ => tl
  end.

(* Operations k .. m-1: splice the list of y = b-1 after the list of
   x = a-1. *)
Fixpoint ops_loop (xa xb : array int) (m k : int) (nx tl : array int)
    (H : Acc (Zwf 0) (gap m k)) {struct H} : array int * array int :=
  match bdec (k <? m) with
  | left Hk =>
      let x := xa.[k] - 1 in
      let y := xb.[k] - 1 in
      let ty := tl.[y] in
      let tx := tl.[x] in
      ops_loop xa xb m (k + 1) nx.[tx <- y] tl.[x <- ty]
        (Acc_inv H (dec_step m k Hk))
  | right _ => (nx, tl)
  end.

(* Walk the list from cur to its last node t, writing the nodes into
   ord[i ..]; returns ord and the number of nodes. *)
Fixpoint walk (nx : array int) (t n cur i : int) (ord : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int * int :=
  match bdec (i <? n) with
  | left Hi =>
      if cur =? t then (ord.[i <- cur], i + 1)
      else walk nx t n nx.[cur] (i + 1) ord.[i <- cur]
             (Acc_inv H (dec_step n i Hi))
  | right _ => (ord, i)
  end.

(* The concatenation of the strings of the nodes ord[lo .. hi), balanced. *)
Fixpoint build (xs : array PrimString.string) (ord : array int) (lo hi : int)
    (H : Acc (Zwf 0) (gap hi lo)) {struct H} : PrimString.string :=
  match bdec (split_ok lo hi) with
  | left Hlt =>
      PrimString.cat
        (build xs ord lo (mid_of lo hi) (Acc_inv H (dec_left lo hi Hlt)))
        (build xs ord (mid_of lo hi) hi (Acc_inv H (dec_right lo hi Hlt)))
  | right _ => xs.[ord.[lo]]
  end.

Definition root_of (xa : array int) (m : int) : int :=
  if m =? 0 then 0 else xa.[m - 1] - 1.

Definition joinstrings_impl (xs : array PrimString.string) (xa xb : array uint)
    : PrimString.string :=
  let n := PArray.length xs in
  let m := PArray.length xa in
  let tl0 := init_loop n 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)) in
  let nt := ops_loop xa xb m 0 (PArray.make n 0) tl0
              (Zwf_well_founded 0 (gap m 0)) in
  let nx := fst nt in
  let tl := snd nt in
  let r := root_of xa m in
  let oc := walk nx tl.[r] n r 0 (PArray.make n 0)
              (Zwf_well_founded 0 (gap n 0)) in
  build xs (fst oc) 0 (snd oc) (Zwf_well_founded 0 (gap (snd oc) 0)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition joinstrings :
  array PrimString.string -> array uint -> array uint -> PrimString.string
  := joinstrings_impl.
