(* Executable implementation and its required termination dependencies.
   Correctness proofs are in selfbalancingbst_proofs.v. *)
(* Implementation of selfbalancingbst (selfbalancingbst.spec): an
   order-statistic red-black tree, persistent, one per instance.

   Code.  [tree] is a red-black tree whose nodes carry the colour, the key,
   the value and the subtree size (CLRS 13 and 14.1).  Every node is built
   by [node], which recomputes the size from the two children, so rank,
   k-th and size read the sizes and never walk the tree.  Insertion is
   Okasaki's balance on the way up ([lbal]/[rbal]); deletion is Kahrs'
   functional red-black delete ([del], [append], [lbalS]/[rbalS]), the
   algorithm of Stdlib's MSetRBT, here with values and sizes.  The trees
   are purely functional, so the copy command shares the source tree in
   O(1).  The 1001 instances (index 0 unused) live in two flat PArrays,
   the trees and the cursors (an option key, re-searched from the root
   when used); the commands are read in one left-to-right pass, the arrays
   and the output array threaded linearly.  A first pass counts the output
   lines (r, g, z) to allocate the output.

   Termination: structural recursion on the tree for the tree operations;
   the two command loops recurse on an erased [Acc (Zwf 0) (gap q j)]
   proof, as in template/polymul1.  No nat, no Z in the code.

   Proof.  [elements t] is the in-order list of (key, value) pairs read
   through Sint63.to_Z; every tree operation is proven against the spec's
   list operation on [elements] (given that the list is sorted by key, an
   invariant all operations preserve as a consequence), and [wf] says that
   every stored size is the sum of its children's plus one, which makes
   the size field the length of [elements] modulo 2^63.  The colours are
   not part of any invariant: the balance is the algorithm's business, the
   contract only needs the contents. *)

From Selfbalancingbst.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* The trees                                                           *)
(* ------------------------------------------------------------------ *)

Inductive color := Red | Black.

(* Node colour left key value size right. *)
Inductive tree :=
| Leaf
| Node (c : color) (l : tree) (k v s : int) (r : tree).

Definition size (t : tree) : int :=
  match t with Leaf => 0 | Node _ _ _ _ s _ => s end.

Definition node (c : color) (l : tree) (k v : int) (r : tree) : tree :=
  Node c l k v (size l + size r + 1) r.

Definition key_lt (a b : int) : bool := Sint63.ltb a b.

Definition makeBlack (t : tree) : tree :=
  match t with Leaf => Leaf | Node _ l k v s r => Node Black l k v s r end.

Definition makeRed (t : tree) : tree :=
  match t with Leaf => Leaf | Node _ l k v s r => Node Red l k v s r end.

Definition lbal (l : tree) (k v : int) (r : tree) : tree :=
  match l with
  | Node Red (Node Red a x vx _ b) y vy _ c =>
      node Red (node Black a x vx b) y vy (node Black c k v r)
  | Node Red a x vx _ (Node Red b y vy _ c) =>
      node Red (node Black a x vx b) y vy (node Black c k v r)
  | _ => node Black l k v r
  end.

Definition rbal (l : tree) (k v : int) (r : tree) : tree :=
  match r with
  | Node Red (Node Red b y vy _ c) z vz _ d =>
      node Red (node Black l k v b) y vy (node Black c z vz d)
  | Node Red b y vy _ (Node Red c z vz _ d) =>
      node Red (node Black l k v b) y vy (node Black c z vz d)
  | _ => node Black l k v r
  end.

Definition rbal' (l : tree) (k v : int) (r : tree) : tree :=
  match r with
  | Node Red b y vy _ (Node Red c z vz _ d) =>
      node Red (node Black l k v b) y vy (node Black c z vz d)
  | Node Red (Node Red b y vy _ c) z vz _ d =>
      node Red (node Black l k v b) y vy (node Black c z vz d)
  | _ => node Black l k v r
  end.

(* Insertion below the root (the root is blackened by [insert]). *)
Fixpoint ins (x vx : int) (t : tree) : tree :=
  match t with
  | Leaf => node Red Leaf x vx Leaf
  | Node c l y vy _ r =>
      if key_lt x y then
        match c with
        | Red => node Red (ins x vx l) y vy r
        | Black => lbal (ins x vx l) y vy r
        end
      else if x =? y then t
      else
        match c with
        | Red => node Red l y vy (ins x vx r)
        | Black => rbal l y vy (ins x vx r)
        end
  end.

Definition insert_t (x vx : int) (t : tree) : tree := makeBlack (ins x vx t).

(* Kahrs' deletion. *)
Definition lbalS (l : tree) (k v : int) (r : tree) : tree :=
  match l with
  | Node Red a x vx _ b => node Red (node Black a x vx b) k v r
  | _ =>
      match r with
      | Node Black a y vy _ b => rbal' l k v (node Red a y vy b)
      | Node Red (Node Black a y vy _ b) z vz _ c =>
          node Red (node Black l k v a) y vy (rbal' b z vz (makeRed c))
      | _ => node Red l k v r
      end
  end.

Definition rbalS (l : tree) (k v : int) (r : tree) : tree :=
  match r with
  | Node Red b y vy _ c => node Red l k v (node Black b y vy c)
  | _ =>
      match l with
      | Node Black a x vx _ b => lbal (node Red a x vx b) k v r
      | Node Red a x vx _ (Node Black b y vy _ c) =>
          node Red (lbal (makeRed a) x vx b) y vy (node Black c k v r)
      | _ => node Red l k v r
      end
  end.

Fixpoint append (l : tree) : tree -> tree :=
  match l with
  | Leaf => fun r => r
  | Node lc ll lx lv _ lr =>
      fix append_l (r : tree) : tree :=
        match r with
        | Leaf => l
        | Node rc rl rx rv _ rr =>
            match lc, rc with
            | Red, Red =>
                let lrl := append lr rl in
                match lrl with
                | Node Red lr' x vx _ rl' =>
                    node Red (node Red ll lx lv lr') x vx (node Red rl' rx rv rr)
                | _ => node Red ll lx lv (node Red lrl rx rv rr)
                end
            | Black, Black =>
                let lrl := append lr rl in
                match lrl with
                | Node Red lr' x vx _ rl' =>
                    node Red (node Black ll lx lv lr') x vx (node Black rl' rx rv rr)
                | _ => lbalS ll lx lv (node Black lrl rx rv rr)
                end
            | Black, Red => node Red (append_l rl) rx rv rr
            | Red, Black => node Red ll lx lv (append lr r)
            end
        end
  end.

Fixpoint del (x : int) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node _ a y vy _ b =>
      if key_lt x y then
        match a with
        | Node Black _ _ _ _ _ => lbalS (del x a) y vy b
        | _ => node Red (del x a) y vy b
        end
      else if x =? y then append a b
      else
        match b with
        | Node Black _ _ _ _ _ => rbalS a y vy (del x b)
        | _ => node Red a y vy (del x b)
        end
  end.

Definition delete_t (x : int) (t : tree) : tree := makeBlack (del x t).

(* The queries: each returns a key (or nothing). *)
Fixpoint find_t (x : int) (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k _ _ r =>
      if key_lt x k then find_t x l
      else if x =? k then Some k
      else find_t x r
  end.

(* the first key >= x *)
Fixpoint lower_t (x : int) (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k _ _ r =>
      if key_lt k x then lower_t x r
      else match lower_t x l with Some z => Some z | None => Some k end
  end.

(* the first key > x *)
Fixpoint upper_t (x : int) (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k _ _ r =>
      if key_lt x k then
        match upper_t x l with Some z => Some z | None => Some k end
      else upper_t x r
  end.

(* the last key < x *)
Fixpoint pred_t (x : int) (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k _ _ r =>
      if key_lt k x then
        match pred_t x r with Some z => Some z | None => Some k end
      else pred_t x l
  end.

Fixpoint front_t (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k _ _ _ =>
      match front_t l with Some z => Some z | None => Some k end
  end.

Fixpoint back_t (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ _ k _ _ r =>
      match back_t r with Some z => Some z | None => Some k end
  end.

(* the key at 0-based position n, through the sizes *)
Fixpoint kth_t (n : int) (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k _ _ r =>
      let sl := size l in
      if n <? sl then kth_t n l
      else if n =? sl then Some k
      else kth_t (n - sl - 1) r
  end.

(* the number of keys < x, through the sizes *)
Fixpoint rank_t (x : int) (t : tree) : int :=
  match t with
  | Leaf => 0
  | Node _ l k _ _ r =>
      if key_lt x k then rank_t x l
      else if x =? k then size l
      else size l + 1 + rank_t x r
  end.

Fixpoint lookup_t (x : int) (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k v _ r =>
      if key_lt x k then lookup_t x l
      else if x =? k then Some v
      else lookup_t x r
  end.

(* the value of key x becomes w (same shape, same sizes) *)
Fixpoint setv_t (x w : int) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node c l k v s r =>
      if key_lt x k then Node c (setv_t x w l) k v s r
      else if x =? k then Node c l k w s r
      else Node c l k v s (setv_t x w r)
  end.

(* ------------------------------------------------------------------ *)
(* The command loop                                                    *)
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

Definition is_out (op : int) : bool := (op =? 114) || (op =? 103) || (op =? 122).

(* acc + the number of output commands among j .. q-1 *)
Fixpoint count_loop (ops : array int) (q j acc : int)
    (H : Acc (Zwf 0) (gap q j)) {struct H} : int :=
  match bdec (j <? q) with
  | left Hj =>
      count_loop ops q (j + 1) (if is_out ops.[j] then acc + 1 else acc)
        (Acc_inv H (dec_step q j Hj))
  | right _ => acc
  end.

Definition on_cur (cur : option int) (f : int -> option int) : option int :=
  match cur with None => None | Some c => f c end.

(* One command on the instance array T, the cursor array C and the output
   array O, whose next free cell is p. *)
Definition exec (T : array tree) (C : array (option int))
    (O : array (option int)) (p id op x y : int)
    : array tree * array (option int) * array (option int) * int :=
  let t := T.[id] in
  let cur := C.[id] in
  if op =? 97 then (T.[id <- T.[x]], C.[id <- None], O, p)
  else if op =? 63 then (T, C.[id <- find_t x t], O, p)
  else if op =? 108 then (T, C.[id <- lower_t x t], O, p)
  else if op =? 117 then (T, C.[id <- upper_t x t], O, p)
  else if op =? 105 then (T.[id <- insert_t x y t], C.[id <- Some x], O, p)
  else if op =? 101 then
    (T.[id <- match cur with None => t | Some c => delete_t c t end],
     C.[id <- None], O, p)
  else if op =? 102 then (T, C.[id <- front_t t], O, p)
  else if op =? 98 then (T, C.[id <- back_t t], O, p)
  else if op =? 62 then (T, C.[id <- on_cur cur (fun c => upper_t c t)], O, p)
  else if op =? 60 then (T, C.[id <- on_cur cur (fun c => pred_t c t)], O, p)
  else if op =? 107 then
    (T, C.[id <- if Sint63.ltb x 0 then None else kth_t x t], O, p)
  else if op =? 114 then
    (T, C, O.[p <- on_cur cur (fun c => Some (rank_t c t))], p + 1)
  else if op =? 103 then
    (T, C, O.[p <- on_cur cur (fun c => lookup_t c t)], p + 1)
  else if op =? 115 then
    (T.[id <- match cur with None => t | Some c => setv_t c x t end], C, O, p)
  else if op =? 122 then (T, C, O.[p <- Some (size t)], p + 1)
  else (T, C, O, p).

Fixpoint run_loop (ids ops xs ys : array int) (q j : int)
    (T : array tree) (C : array (option int)) (O : array (option int)) (p : int)
    (H : Acc (Zwf 0) (gap q j)) {struct H} : array (option int) :=
  match bdec (j <? q)%uint63 with
  | left Hj =>
      let '(T', C', O', p') := exec T C O p ids.[j] ops.[j] xs.[j] ys.[j] in
      run_loop ids ops xs ys q (j + 1)%uint63 T' C' O' p'
        (Acc_inv H (dec_step q j Hj))
  | right _ => O
  end.

Definition run_impl (ids ops : array uint) (xs ys : array sint)
    : array (option sint) :=
  let q := PArray.length ids in
  let n := count_loop ops q 0 0 (Zwf_well_founded 0 (gap q 0)) in
  run_loop ids ops xs ys q 0 (PArray.make 1001 Leaf) (PArray.make 1001 None)
    (PArray.make n None) 0 (Zwf_well_founded 0 (gap q 0)).

(* ------------------------------------------------------------------ *)
(* Prop side: the tree layer                                           *)
(* ------------------------------------------------------------------ *)

Local Notation zs := Sint63.to_Z.

Arguments lbal : simpl never.
Arguments rbal : simpl never.
Arguments rbal' : simpl never.
Arguments makeRed : simpl never.

Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition run_commands :
  array uint -> array uint -> array sint -> array sint -> array (option sint)
  := run_impl.
