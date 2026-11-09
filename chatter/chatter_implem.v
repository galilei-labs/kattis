(* Executable implementation and its required termination dependencies.
   Correctness proofs are in chatter_proofs.v. *)
(* Implementation of chatter (chatter.spec): see README.md, section
   Implementation. *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Relations Sorted.
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

Lemma dec_cnt : forall k : int,
  (0 <? k) = true -> Zwf 0 (φ (k - 1)) (φ k).
Proof.
  intros k H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  unfold Zwf. sia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* one step of the generator *)
Definition nx (a b c r : int) : int := (r * a + b) mod c.

(* Draws the next chat from generator state r: returns the new state and
   the two people.  At most [bud] attempts; the proof shows that bud = c+1
   is never exhausted on a valid input. *)
Fixpoint redraw (n a b c r bud : int) (H : Acc (Zwf 0) (φ bud)) {struct H}
    : int * int * int :=
  match bdec (0 <? bud) with
  | left Hb =>
      let r1 := nx a b c r in
      let r2 := nx a b c r1 in
      let x := r1 mod n in
      let y := r2 mod n in
      if x =? y then redraw n a b c r2 (bud - 1) (Acc_inv H (dec_cnt bud Hb))
      else (r2, x, y)
  | right _ => (r, 0, 0)
  end.

(* Walks [cnt] members of a list from [q] along [nxt], pointing each to
   [big]. *)
Fixpoint relabel (nxt : array int) (big q cnt : int) (rep : array int)
    (H : Acc (Zwf 0) (φ cnt)) {struct H} : array int :=
  match bdec (0 <? cnt) with
  | left Hc =>
      relabel nxt big (nxt.[q]) (cnt - 1) (rep.[q <- big])
        (Acc_inv H (dec_cnt cnt Hc))
  | right _ => rep
  end.

(* Appends the list of root [small] to the list of root [big]. *)
Definition merge (big small : int) (rep nxt tl sz : array int)
    : array int * array int * array int * array int :=
  let rep' := relabel nxt big small (sz.[small]) rep
                (Zwf_well_founded 0 (φ (sz.[small]))) in
  let nxt' := nxt.[tl.[big] <- small] in
  let tl' := tl.[big <- tl.[small]] in
  let sz' := sz.[big <- sz.[big] + sz.[small]] in
  (rep', nxt', tl', sz').

(* Weighted union of the sets of x and y. *)
Definition union (x y : int) (rep nxt tl sz : array int)
    : array int * array int * array int * array int :=
  let px := rep.[x] in
  let py := rep.[y] in
  if px =? py then (rep, nxt, tl, sz)
  else if sz.[py] <? sz.[px] then merge px py rep nxt tl sz
  else merge py px rep nxt tl sz.

(* The k remaining chats of the day. *)
Fixpoint sim (n a b c r k : int) (rep nxt tl sz : array int)
    (H : Acc (Zwf 0) (φ k)) {struct H} : array int * array int :=
  match bdec (0 <? k) with
  | left Hk =>
      let '(r', x, y) := redraw n a b c r (c + 1)
                           (Zwf_well_founded 0 (φ (c + 1))) in
      let '(rep', nxt', tl', sz') := union x y rep nxt tl sz in
      sim n a b c r' (k - 1) rep' nxt' tl' sz' (Acc_inv H (dec_cnt k Hk))
  | right _ => (rep, sz)
  end.

(* rep and tl start as the identity. *)
Fixpoint init (n i : int) (rep tl : array int) (H : Acc (Zwf 0) (gap n i))
    {struct H} : array int * array int :=
  match bdec (i <? n) with
  | left Hi => init n (i + 1) (rep.[i <- i]) (tl.[i <- i]) (Acc_inv H (dec_step n i Hi))
  | right _ => (rep, tl)
  end.

(* Counts the groups (their first member in index order) and tallies their
   sizes into cnt. *)
Fixpoint tally (n i : int) (rep sz seen cnt : array int) (g : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : int * array int :=
  match bdec (i <? n) with
  | left Hi =>
      let ro := rep.[i] in
      if seen.[ro] =? 0 then
        let s := sz.[ro] in
        tally n (i + 1) rep sz (seen.[ro <- 1]) (cnt.[s <- cnt.[s] + 1]) (g + 1)
          (Acc_inv H (dec_step n i Hi))
      else tally n (i + 1) rep sz seen cnt g (Acc_inv H (dec_step n i Hi))
  | right _ => (g, cnt)
  end.

(* The number of sizes n-i, i < n, with a nonzero count. *)
Fixpoint countd (n i : int) (cnt : array int) (d : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : int :=
  match bdec (i <? n) with
  | left Hi =>
      countd n (i + 1) cnt (if 0 <? cnt.[n - i] then d + 1 else d)
        (Acc_inv H (dec_step n i Hi))
  | right _ => d
  end.

(* Writes (s, cnt.[s]) for the sizes s = n, n-1, ..., 1 of nonzero count. *)
Fixpoint fill (n i j : int) (cnt : array int) (out : array (int * int))
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array (int * int) :=
  match bdec (i <? n) with
  | left Hi =>
      let s := n - i in
      let v := cnt.[s] in
      if 0 <? v then
        fill n (i + 1) (j + 1) cnt (out.[j <- (s, v)]) (Acc_inv H (dec_step n i Hi))
      else fill n (i + 1) j cnt out (Acc_inv H (dec_step n i Hi))
  | right _ => out
  end.

Definition chatter_impl (n r a b c : uint) : uint * array (uint * uint) :=
  let '(rep0, tl0) := init n 0 (PArray.make n 0) (PArray.make n 0)
                        (Zwf_well_founded 0 (gap n 0)) in
  let '(rep, sz) := sim n a b c r n rep0 (PArray.make n 0) tl0 (PArray.make n 1)
                      (Zwf_well_founded 0 (φ n)) in
  let '(g, cnt) := tally n 0 rep sz (PArray.make n 0) (PArray.make (n + 1) 0) 0
                     (Zwf_well_founded 0 (gap n 0)) in
  let d := countd n 0 cnt 0 (Zwf_well_founded 0 (gap n 0)) in
  (g, fill n 0 0 cnt (PArray.make d (0, 0)) (Zwf_well_founded 0 (gap n 0))).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition chatter : uint -> uint -> uint -> uint -> uint -> uint * array (uint * uint)
  := chatter_impl.
