(* Executable implementation and its required termination dependencies.
   Correctness proofs are in intersectingrectangles_proofs.v. *)
(* Implementation of intersectingrectangles (intersectingrectangles.spec):
   a plane sweep over the rectangles' edges, CLRS 33.2 specialised to
   axis-parallel segments.

   Code.  One AVL tree type [tree] (key, value, height: three ints; keys
   compared as signed integers) serves twice.
   - The event queue.  Rectangle i gives two events: its left side at
     x = x1.[i] (value i) and its right side at x = x2.[i] (value n + i).
     The 2n events are inserted into an AVL tree keyed by x, and the sweep
     is an in-order traversal of that tree: a tree sort, O(n log n) in the
     worst case (all x values are distinct, so no key collides).
   - The sweep-line status: the y values of the horizontal edges crossed
     by the sweep line, an AVL tree keyed by y (value unused).
   At a left event of rectangle i, the status is queried for a key
   strictly between y1.[i] and y2.[i] (the left side of i crosses a
   horizontal edge), then y1.[i], y2.[i] are inserted; at a right event
   they are removed, then the status is queried the same way.  The sweep
   stops at the first crossing.  All operations are O(log n).

   Why this decides the contract: all x values are distinct and all y
   values are distinct, so two boundaries meet iff a vertical side of one
   rectangle strictly crosses a horizontal side of the other
   ([geometry]).

   Termination: the tree functions recurse structurally on the tree; the
   insertion loop recurses on an erased [Acc (Zwf 0) (gap n i)] proof, the
   template's device.  No nat, no Z in the code. *)

From Intersectingrectangles.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Reals Sorted.
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

(* ------------------------------------------------------------------ *)
(* AVL trees over int keys (signed order), with an int payload          *)
(* ------------------------------------------------------------------ *)

Inductive tree : Set :=
| Leaf : tree
| Node : tree -> int -> int -> tree -> int -> tree.

Definition height (t : tree) : int :=
  match t with Leaf => 0 | Node _ _ _ _ h => h end.

Definition hmax (a b : int) : int := if a <? b then b else a.

Definition node (l : tree) (k v : int) (r : tree) : tree :=
  Node l k v r (hmax (height l) (height r) + 1).

Definition bal (l : tree) (k v : int) (r : tree) : tree :=
  let hl := height l in
  let hr := height r in
  if hr + 2 <? hl then
    match l with
    | Leaf => node l k v r
    | Node ll lk lv lr _ =>
        if height lr <=? height ll then node ll lk lv (node lr k v r)
        else match lr with
             | Leaf => node l k v r
             | Node lrl lrk lrv lrr _ =>
                 node (node ll lk lv lrl) lrk lrv (node lrr k v r)
             end
    end
  else if hl + 2 <? hr then
    match r with
    | Leaf => node l k v r
    | Node rl rk rv rr _ =>
        if height rl <=? height rr then node (node l k v rl) rk rv rr
        else match rl with
             | Leaf => node l k v r
             | Node rll rlk rlv rlr _ =>
                 node (node l k v rll) rlk rlv (node rlr rk rv rr)
             end
    end
  else node l k v r.

Fixpoint insert (k v : int) (t : tree) : tree :=
  match t with
  | Leaf => Node Leaf k v Leaf 1
  | Node l k' v' r h =>
      if Sint63.ltb k k' then bal (insert k v l) k' v' r
      else if Sint63.ltb k' k then bal l k' v' (insert k v r)
      else Node l k v r h
  end.

Fixpoint remove_min (l : tree) (k v : int) (r : tree) : int * int * tree :=
  match l with
  | Leaf => (k, v, r)
  | Node ll lk lv lr _ =>
      let '(mk, mv, l') := remove_min ll lk lv lr in (mk, mv, bal l' k v r)
  end.

Definition merge (l r : tree) : tree :=
  match l with
  | Leaf => r
  | Node _ _ _ _ _ =>
      match r with
      | Leaf => l
      | Node rl rk rv rr _ =>
          let '(mk, mv, r') := remove_min rl rk rv rr in bal l mk mv r'
      end
  end.

Fixpoint remove (k : int) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l k' v' r _ =>
      if Sint63.ltb k k' then bal (remove k l) k' v' r
      else if Sint63.ltb k' k then bal l k' v' (remove k r)
      else merge l r
  end.

(* Is there a key strictly between lo and hi? *)
Fixpoint between (lo hi : int) (t : tree) : bool :=
  match t with
  | Leaf => false
  | Node l k _ r _ =>
      if Sint63.leb k lo then between lo hi r
      else if Sint63.leb hi k then between lo hi l
      else true
  end.

(* ------------------------------------------------------------------ *)
(* The sweep                                                           *)
(* ------------------------------------------------------------------ *)

(* Events of rectangles i, i+1, ..., n-1 into the event tree. *)
Fixpoint build (x1 x2 : array sint) (n i : int) (t : tree)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : tree :=
  match bdec (i <? n) with
  | left Hi =>
      build x1 x2 n (i + 1) (insert x2.[i] (n + i) (insert x1.[i] i t))
        (Acc_inv H (dec_step n i Hi))
  | right _ => t
  end.

(* One event: v < n is the left side of rectangle v, v >= n the right
   side of rectangle v - n.  None: a crossing was found. *)
Definition step (n : int) (y1 y2 : array sint) (v : int) (s : tree)
    : option tree :=
  if v <? n then
    let lo := y1.[v] in
    let hi := y2.[v] in
    if between lo hi s then None else Some (insert hi 0 (insert lo 0 s))
  else
    let i := v - n in
    let lo := y1.[i] in
    let hi := y2.[i] in
    let s' := remove hi (remove lo s) in
    if between lo hi s' then None else Some s'.

(* In-order traversal of the event tree, threading the status. *)
Fixpoint sweep (n : int) (y1 y2 : array sint) (t s : tree) : option tree :=
  match t with
  | Leaf => Some s
  | Node l _ v r _ =>
      match sweep n y1 y2 l s with
      | None => None
      | Some s1 =>
          match step n y1 y2 v s1 with
          | None => None
          | Some s2 => sweep n y1 y2 r s2
          end
      end
  end.

Definition intersecting_rectangles_impl (x1 y1 x2 y2 : array sint) : bool :=
  let n := PArray.length x1 in
  let ev := build x1 x2 n 0 Leaf (Zwf_well_founded 0 (gap n 0)) in
  match sweep n y1 y2 ev Leaf with
  | None => true
  | Some _ => false
  end.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition intersecting_rectangles :
  array sint -> array sint -> array sint -> array sint -> bool :=
  intersecting_rectangles_impl.
