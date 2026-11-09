(* Executable implementation and its required termination dependencies.
   Correctness proofs are in gcpc_proofs.v. *)
(* Implementation of gcpc (gcpc.spec): an order-statistic AVL tree.

   Code.  Every team k (1 <= k <= n) has a key, one 63-bit word that
   encodes its score and its number,
       key = (C - solved) * 2^44 + penalty * 2^17 + k,     C = 2^17 - 1,
   so that the keys are pairwise distinct and a smaller key is a better
   score (more solved problems, or as many and a smaller penalty; the team
   number only breaks ties).  The current key of every team lives in one
   flat array [keys] indexed by team; all n keys live in an AVL tree
   (an inductive, updated functionally, every node carrying its subtree
   size and height; the balancing function is the one of OCaml's Set).
   An event (a, q) deletes team a's old key from the tree, inserts the new
   one, old - 2^44 + q * 2^17, and the rank of team 1 is one plus the
   number of keys below key(1) - 1 (the keys whose score is better),
   counted with the subtree sizes along one root-to-leaf path.
   The bounds of the contract (solved <= 10^5 < 2^17, penalty <=
   10^8 < 2^27, k <= 10^5 < 2^17) keep the key below 2^62.

   Termination: the two loops (initialisation over the teams, the events)
   recurse structurally on an erased [Acc (Zwf 0) (gap m i)] proof as in
   template/polymul1; the tree functions recurse structurally on the
   tree.  No nat, no Z, no list in the code.

   Proof.  The tree is read through its in-order list [elements]: [ok]
   says the size fields are right, [sorted] that the list is strictly
   increasing.  The balancing function does not change the in-order list,
   so insert / delete are the list functions [ins_list] / [del_list] and
   their effect on the multiset of keys is a [Permutation].  The loop
   invariant says that the keys of the tree are, up to permutation, the
   keys of the teams 1..n after the first j events, and the rank query
   then counts, through the encoding, the teams with a better score. *)

From Gcpc.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Permutation.
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
(* The AVL tree with subtree sizes                                     *)
(* ------------------------------------------------------------------ *)

(* Node l k r size height *)
Inductive tree : Set :=
| Leaf : tree
| Node : tree -> int -> tree -> int -> int -> tree.

Definition height (t : tree) : int :=
  match t with Leaf => 0 | Node _ _ _ _ h => h end.

Definition size (t : tree) : int :=
  match t with Leaf => 0 | Node _ _ _ s _ => s end.

Definition mk (l : tree) (k : int) (r : tree) : tree :=
  Node l k r (size l + size r + 1)
    (if height l <? height r then height r + 1 else height l + 1).

(* The rebalancing of OCaml's Set.bal: l and r differ in height by at most
   3 on entry. *)
Definition bal (l : tree) (k : int) (r : tree) : tree :=
  let hl := height l in
  let hr := height r in
  if hr + 2 <? hl then
    match l with
    | Leaf => mk l k r
    | Node ll lk lr _ _ =>
        if height lr <=? height ll then mk ll lk (mk lr k r)
        else match lr with
             | Leaf => mk l k r
             | Node lrl lrk lrr _ _ => mk (mk ll lk lrl) lrk (mk lrr k r)
             end
    end
  else if hl + 2 <? hr then
    match r with
    | Leaf => mk l k r
    | Node rl rk rr _ _ =>
        if height rl <=? height rr then mk (mk l k rl) rk rr
        else match rl with
             | Leaf => mk l k r
             | Node rll rlk rlr _ _ => mk (mk l k rll) rlk (mk rlr rk rr)
             end
    end
  else mk l k r.

Fixpoint insert (x : int) (t : tree) : tree :=
  match t with
  | Leaf => mk Leaf x Leaf
  | Node l k r _ _ =>
      if x <? k then bal (insert x l) k r
      else if k <? x then bal l k (insert x r)
      else t
  end.

(* The minimum of Node l k r, and the tree without it. *)
Fixpoint remove_min (l : tree) (k : int) (r : tree) : int * tree :=
  match l with
  | Leaf => (k, r)
  | Node ll lk lr _ _ =>
      let (m, l') := remove_min ll lk lr in (m, bal l' k r)
  end.

Definition merge (l r : tree) : tree :=
  match l, r with
  | Leaf, _ => r
  | _, Leaf => l
  | _, Node rl rk rr _ _ => let (m, r') := remove_min rl rk rr in bal l m r'
  end.

Fixpoint delete (x : int) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l k r _ _ =>
      if x <? k then bal (delete x l) k r
      else if k <? x then bal l k (delete x r)
      else merge l r
  end.

(* The number of keys below q (OS-RANK). *)
Fixpoint count_lt (q : int) (t : tree) : int :=
  match t with
  | Leaf => 0
  | Node l k r _ _ =>
      if k <? q then size l + 1 + count_lt q r else count_lt q l
  end.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Definition KD : int := 17592186044416.        (* 2^44 *)
Definition KE : int := 131072.                (* 2^17 *)
Definition K0 : int := 2305825417027649536.   (* (2^17 - 1) * 2^44 *)

(* Teams k .. n1 - 1 receive their initial key K0 + k (score (0, 0)),
   in [keys] and in the tree. *)
Fixpoint init_loop (n1 k : int) (keys : array int) (T : tree)
    (H : Acc (Zwf 0) (gap n1 k)) {struct H} : array int * tree :=
  match bdec (k <? n1) with
  | left Hk =>
      let key := K0 + k in
      init_loop n1 (k + 1) keys.[k <- key] (insert key T)
        (Acc_inv H (dec_step n1 k Hk))
  | right _ => (keys, T)
  end.

(* Events j .. m - 1: team a = xt.[j] solves a problem with penalty
   xp.[j]; out.[j] receives the rank of team 1 after it. *)
Fixpoint ev_loop (xt xp : array int) (m j : int) (keys : array int) (T : tree)
    (out : array int) (H : Acc (Zwf 0) (gap m j)) {struct H} : array int :=
  match bdec (j <? m) with
  | left Hj =>
      let a := xt.[j] in
      let old := keys.[a] in
      let new := old - KD + xp.[j] * KE in
      let keys' := keys.[a <- new] in
      let T' := insert new (delete old T) in
      let ans := count_lt (keys'.[1] - 1) T' + 1 in
      ev_loop xt xp m (j + 1) keys' T' out.[j <- ans]
        (Acc_inv H (dec_step m j Hj))
  | right _ => out
  end.

Definition gcpc_impl (n : uint) (xt xp : array uint) : array uint :=
  let m := PArray.length xt in
  let n1 := n + 1 in
  let (keys, T) :=
    init_loop n1 1 (PArray.make n1 0) Leaf (Zwf_well_founded 0 (gap n1 1)) in
  ev_loop xt xp m 0 keys T (PArray.make m 0) (Zwf_well_founded 0 (gap m 0)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition gcpc : uint -> array uint -> array uint -> array uint := gcpc_impl.
