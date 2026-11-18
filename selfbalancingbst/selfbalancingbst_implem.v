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
   through Sint63.to_Z; every tree operation is proven against a private
   list operation on [elements] (given that the list is sorted by key, an
   invariant all operations preserve as a consequence), and [wf] says that
   every stored size is the sum of its children's plus one, which makes
   the size field the length of [elements] modulo 2^63.  The colours are
   not part of any invariant: the balance is the algorithm's business, the
   contract only needs the contents. The private list execution then
   refines the public inductive relation on finite maps and cursors. *)

From Selfbalancingbst.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63.
From KattisLib Require Import Cost.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* Private sorted-list model used to reuse the tree refinement lemmas.
   It is proof-only: none of these definitions is called by the runtime. *)
Module Reference.
Definition entries := list (Z * Z).
Definition inst := (entries * option Z)%type.
Fixpoint first_key (p : Z -> bool) (l : entries) : option Z :=
  match l with [] => None | (k, _) :: rest => if p k then Some k else first_key p rest end.
Fixpoint insert (k v : Z) (l : entries) : entries :=
  match l with [] => [(k,v)] | (k',v') :: rest =>
    if Z.ltb k k' then (k,v) :: l else if Z.eqb k k' then l
    else (k',v') :: insert k v rest end.
Definition erase (k : Z) (l : entries) : entries :=
  filter (fun e => negb (Z.eqb (fst e) k)) l.
Definition set_value (k v : Z) (l : entries) : entries :=
  map (fun e => if Z.eqb (fst e) k then (k,v) else e) l.
Definition lookup (k : Z) (l : entries) : option Z :=
  option_map snd (find (fun e => Z.eqb (fst e) k) l).
Definition rank (k : Z) (l : entries) : Z :=
  Z.of_nat (List.length (filter (fun e => Z.ltb (fst e) k) l)).
Definition kth (k : Z) (l : entries) : option Z :=
  if Z.leb 0 k then option_map fst (nth_error l (Z.to_nat k)) else None.
Definition on_cursor (c : option Z) (f : Z -> option Z) : option Z :=
  match c with None => None | Some k => f k end.
Definition state := N -> inst.
Definition init : state := fun _ => ([], None).
Definition command := (N * N * Z * Z)%type.
Definition step (s : state) (line : command) : state * list (option Z) :=
  let '(id, op, x, y) := line in
  let '(l, c) := s id in
  let update (i : inst) : state := fun j => if N.eqb j id then i else s j in
  let move c' := (update (l, c'), @nil (option Z)) in
  let say o := (s, [o]) in
  match op with
  | 97%N => (update (fst (s (Z.to_N x)), None), [])
  | 63%N => move (first_key (fun k => Z.eqb k x) l)
  | 108%N => move (first_key (fun k => Z.leb x k) l)
  | 117%N => move (first_key (fun k => Z.ltb x k) l)
  | 105%N => (update (insert x y l, Some x), [])
  | 101%N => (update (match c with None => l | Some k => erase k l end, None), [])
  | 102%N => move (first_key (fun _ => true) l)
  | 98%N => move (first_key (fun _ => true) (rev l))
  | 62%N => move (on_cursor c (fun k => first_key (fun j => Z.ltb k j) l))
  | 60%N => move (on_cursor c (fun k => first_key (fun j => Z.ltb j k) (rev l)))
  | 107%N => move (kth x l)
  | 114%N => say (option_map (fun k => rank k l) c)
  | 103%N => say (on_cursor c (fun k => lookup k l))
  | 115%N => (update (match c with None => l | Some k => set_value k x l end, c), [])
  | 122%N => say (Some (Z.of_nat (List.length l)))
  | _ => (s, [])
  end.
Fixpoint replay (s : state) (lines : list command) : list (option Z) :=
  match lines with [] => [] | line :: rest =>
    let '(s', out) := step s line in out ++ replay s' rest end.
Definition args_ok (op : N) (x y : Z) : Prop :=
  match op with
  | 63%N | 108%N | 117%N | 115%N | 107%N => Prelude.int32 x /\ y = 0%Z
  | 105%N => Prelude.int32 x /\ Prelude.int32 y
  | 97%N => (1 <= x <= 1000)%Z /\ y = 0%Z
  | _ => x = 0%Z /\ y = 0%Z
  end.
End Reference.
Import Reference.

(* A constant-size dispatch tuple, local to the implementation. There are
   no encoded input columns or extra command arrays. *)
Definition encode_operation {U S : Type} (zero : S) (source : U -> S)
    (op : operation U S) : uint * S * S :=
  match op with
  | CopyFrom id => (97, source id, zero)
  | FindKey k => (63, k, zero)
  | LowerBound k => (108, k, zero)
  | UpperBound k => (117, k, zero)
  | Insert k v => (105, k, v)
  | Erase => (101, zero, zero)
  | First => (102, zero, zero)
  | Last => (98, zero, zero)
  | NextKey => (62, zero, zero)
  | PreviousKey => (60, zero, zero)
  | SelectRank k => (107, k, zero)
  | GetRank => (114, zero, zero)
  | GetValue => (103, zero, zero)
  | SetValue v => (115, v, zero)
  | GetSize => (122, zero, zero)
  end.
Elpi complexity encode_operation.
Arguments encode_operation_cost : simpl never.

Definition encode_machine (line : machine_command) : uint * uint * sint * sint :=
  let '(id, op) := line in
  let '(code, x, y) := encode_operation 0 (fun id => id) op in (id, code, x, y).
Elpi complexity encode_machine.
Arguments encode_machine_cost : simpl never.

Definition encode_math (line : Prelude.command) : Reference.command :=
  let '(id, op) := line in
  let '(code, x, y) := encode_operation 0%Z Z.of_N op in
  (id, Z.to_N (φ code), x, y).

(* ------------------------------------------------------------------ *)
(* The trees                                                           *)
(* ------------------------------------------------------------------ *)

Inductive color := Red | Black.

(* Node colour left key value size right. *)
Inductive tree :=
| Leaf
| Node (c : color) (l : tree) (k v s : int) (r : tree).

Elpi complexity color.
Elpi complexity tree.

Definition size (t : tree) : int :=
  match t with Leaf => 0 | Node _ _ _ _ s _ => s end.
Elpi complexity size.
Arguments size_cost : simpl never.

Definition node (c : color) (l : tree) (k v : int) (r : tree) : tree :=
  Node c l k v (size l + size r + 1) r.
Elpi complexity node.
Arguments node_cost : simpl never.

Definition key_lt (a b : int) : bool := Sint63.ltb a b.
Elpi complexity key_lt.
Arguments key_lt_cost : simpl never.

Definition makeBlack (t : tree) : tree :=
  match t with Leaf => Leaf | Node _ l k v s r => Node Black l k v s r end.
Elpi complexity makeBlack.
Arguments makeBlack_cost : simpl never.

Definition makeRed (t : tree) : tree :=
  match t with Leaf => Leaf | Node _ l k v s r => Node Red l k v s r end.
Elpi complexity makeRed.
Arguments makeRed_cost : simpl never.

Definition lbal (l : tree) (k v : int) (r : tree) : tree :=
  match l with
  | Node Red (Node Red a x vx _ b) y vy _ c =>
      node Red (node Black a x vx b) y vy (node Black c k v r)
  | Node Red a x vx _ (Node Red b y vy _ c) =>
      node Red (node Black a x vx b) y vy (node Black c k v r)
  | _ => node Black l k v r
  end.
Elpi complexity lbal.
Arguments lbal_cost : simpl never.

Definition rbal (l : tree) (k v : int) (r : tree) : tree :=
  match r with
  | Node Red (Node Red b y vy _ c) z vz _ d =>
      node Red (node Black l k v b) y vy (node Black c z vz d)
  | Node Red b y vy _ (Node Red c z vz _ d) =>
      node Red (node Black l k v b) y vy (node Black c z vz d)
  | _ => node Black l k v r
  end.
Elpi complexity rbal.
Arguments rbal_cost : simpl never.

Definition rbal' (l : tree) (k v : int) (r : tree) : tree :=
  match r with
  | Node Red b y vy _ (Node Red c z vz _ d) =>
      node Red (node Black l k v b) y vy (node Black c z vz d)
  | Node Red (Node Red b y vy _ c) z vz _ d =>
      node Red (node Black l k v b) y vy (node Black c z vz d)
  | _ => node Black l k v r
  end.
Elpi complexity rbal'.
Arguments rbal'_cost : simpl never.

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
Elpi complexity ins.
Arguments ins_cost : simpl never.

Definition insert_t (x vx : int) (t : tree) : tree := makeBlack (ins x vx t).
Elpi complexity insert_t.
Arguments insert_t_cost : simpl never.

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
Elpi complexity lbalS.
Arguments lbalS_cost : simpl never.

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
Elpi complexity rbalS.
Arguments rbalS_cost : simpl never.

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
Elpi complexity append.
Arguments append_cost : simpl never.

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
Elpi complexity del.
Arguments del_cost : simpl never.

Definition delete_t (x : int) (t : tree) : tree := makeBlack (del x t).
Elpi complexity delete_t.
Arguments delete_t_cost : simpl never.

(* The queries: each returns a key (or nothing). *)
Fixpoint find_t (x : int) (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k _ _ r =>
      if key_lt x k then find_t x l
      else if x =? k then Some k
      else find_t x r
  end.
Elpi complexity find_t.
Arguments find_t_cost : simpl never.

(* the first key >= x *)
Fixpoint lower_t (x : int) (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k _ _ r =>
      if key_lt k x then lower_t x r
      else match lower_t x l with Some z => Some z | None => Some k end
  end.
Elpi complexity lower_t.
Arguments lower_t_cost : simpl never.

(* the first key > x *)
Fixpoint upper_t (x : int) (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k _ _ r =>
      if key_lt x k then
        match upper_t x l with Some z => Some z | None => Some k end
      else upper_t x r
  end.
Elpi complexity upper_t.
Arguments upper_t_cost : simpl never.

(* the last key < x *)
Fixpoint pred_t (x : int) (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k _ _ r =>
      if key_lt k x then
        match pred_t x r with Some z => Some z | None => Some k end
      else pred_t x l
  end.
Elpi complexity pred_t.
Arguments pred_t_cost : simpl never.

Fixpoint front_t (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k _ _ _ =>
      match front_t l with Some z => Some z | None => Some k end
  end.
Elpi complexity front_t.
Arguments front_t_cost : simpl never.

Fixpoint back_t (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ _ k _ _ r =>
      match back_t r with Some z => Some z | None => Some k end
  end.
Elpi complexity back_t.
Arguments back_t_cost : simpl never.

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
Elpi complexity kth_t.
Arguments kth_t_cost : simpl never.

(* the number of keys < x, through the sizes *)
Fixpoint rank_t (x : int) (t : tree) : int :=
  match t with
  | Leaf => 0
  | Node _ l k _ _ r =>
      if key_lt x k then rank_t x l
      else if x =? k then size l
      else size l + 1 + rank_t x r
  end.
Elpi complexity rank_t.
Arguments rank_t_cost : simpl never.

Fixpoint lookup_t (x : int) (t : tree) : option int :=
  match t with
  | Leaf => None
  | Node _ l k v _ r =>
      if key_lt x k then lookup_t x l
      else if x =? k then Some v
      else lookup_t x r
  end.
Elpi complexity lookup_t.
Arguments lookup_t_cost : simpl never.

(* the value of key x becomes w (same shape, same sizes) *)
Fixpoint setv_t (x w : int) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node c l k v s r =>
      if key_lt x k then Node c (setv_t x w l) k v s r
      else if x =? k then Node c l k w s r
      else Node c l k v s (setv_t x w r)
  end.
Elpi complexity setv_t.
Arguments setv_t_cost : simpl never.

(* ------------------------------------------------------------------ *)
(* The command loop                                                    *)
(* ------------------------------------------------------------------ *)

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.
Elpi complexity sumbool.
Elpi complexity bdec.
Arguments bdec_cost : simpl never.

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Definition is_out (op : int) : bool := (op =? 114) || (op =? 103) || (op =? 122).
Elpi complexity orb.
Elpi complexity is_out.
Arguments is_out_cost : simpl never.

Definition output_command (line : machine_command) : bool :=
  let '(_, op) := line in
  match op with GetRank | GetValue | GetSize => true | _ => false end.
Elpi complexity output_command.
Arguments output_command_cost : simpl never.

(* acc + the number of output commands among j .. q-1 *)
Fixpoint count_loop (ops : array machine_command) (q j acc : int)
    (H : Acc (Zwf 0) (gap q j)) {struct H} : int :=
  match bdec (j <? q) with
  | left Hj =>
      count_loop ops q (j + 1) (if output_command ops.[j] then acc + 1 else acc)
        (Acc_inv H (dec_step q j Hj))
  | right _ => acc
  end.
Elpi complexity count_loop.
Arguments count_loop_cost : simpl never.

Definition on_cur (cur : option int) (f : int -> option int) : option int :=
  match cur with None => None | Some c => f c end.
Elpi complexity on_cur.
Arguments on_cur_cost : simpl never.

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
Elpi complexity exec.
Arguments exec_cost : simpl never.

Fixpoint run_loop (commands : array machine_command) (q j : int)
    (T : array tree) (C : array (option int)) (O : array (option int)) (p : int)
    (H : Acc (Zwf 0) (gap q j)) {struct H} : array (option int) :=
  match bdec (j <? q)%uint63 with
  | left Hj =>
      let '(id, op, x, y) := encode_machine commands.[j] in
      let '(T', C', O', p') := exec T C O p id op x y in
      run_loop commands q (j + 1)%uint63 T' C' O' p'
        (Acc_inv H (dec_step q j Hj))
  | right _ => O
  end.
Elpi complexity run_loop.
Arguments run_loop_cost : simpl never.

Definition run_impl (commands : array machine_command)
    : array (option sint) :=
  let q := PArray.length commands in
  let n := count_loop commands q 0 0 (Zwf_well_founded 0 (gap q 0)) in
  run_loop commands q 0 (PArray.make 1001 Leaf) (PArray.make 1001 None)
    (PArray.make n None) 0 (Zwf_well_founded 0 (gap q 0)).
Elpi complexity run_impl.
Arguments run_impl_cost : simpl never.

(* ------------------------------------------------------------------ *)
(* Prop side: the tree layer                                           *)
(* ------------------------------------------------------------------ *)

Local Notation zs := Sint63.to_Z.

Fixpoint elements (t : tree) : entries :=
  match t with
  | Leaf => []
  | Node _ l k v _ r => elements l ++ (zs k, zs v) :: elements r
  end.

Fixpoint wf (t : tree) : Prop :=
  match t with
  | Leaf => True
  | Node _ l _ _ s r => wf l /\ wf r /\ s = size l + size r + 1
  end.

Ltac lnorm := repeat progress (simpl; rewrite <- ?app_assoc); reflexivity.
Ltac des := repeat match goal with
  | |- context [match ?t with _ => _ end] => destruct t
  end.
Ltac wfsolve := unfold node, makeRed, makeBlack in *; simpl in *; intuition.

Lemma elements_node : forall c l k v r,
  elements (node c l k v r) = elements l ++ (zs k, zs v) :: elements r.
Proof. reflexivity. Qed.

Lemma wf_node : forall c l k v r, wf l -> wf r -> wf (node c l k v r).
Proof. intros; simpl; auto. Qed.

Lemma elements_makeBlack : forall t, elements (makeBlack t) = elements t.
Proof. destruct t; reflexivity. Qed.
Lemma elements_makeRed : forall t, elements (makeRed t) = elements t.
Proof. destruct t; reflexivity. Qed.
Lemma wf_makeBlack : forall t, wf t -> wf (makeBlack t).
Proof. destruct t; simpl; auto. Qed.
Lemma wf_makeRed : forall t, wf t -> wf (makeRed t).
Proof. destruct t; simpl; auto. Qed.

Lemma elements_lbal : forall l k v r,
  elements (lbal l k v r) = elements l ++ (zs k, zs v) :: elements r.
Proof. intros; unfold lbal; des; lnorm. Qed.
Lemma elements_rbal : forall l k v r,
  elements (rbal l k v r) = elements l ++ (zs k, zs v) :: elements r.
Proof. intros; unfold rbal; des; lnorm. Qed.
Lemma elements_rbal' : forall l k v r,
  elements (rbal' l k v r) = elements l ++ (zs k, zs v) :: elements r.
Proof. intros; unfold rbal'; des; lnorm. Qed.

Lemma wf_lbal : forall l k v r, wf l -> wf r -> wf (lbal l k v r).
Proof. intros; unfold lbal; des; wfsolve. Qed.
Lemma wf_rbal : forall l k v r, wf l -> wf r -> wf (rbal l k v r).
Proof. intros; unfold rbal; des; wfsolve. Qed.
Lemma wf_rbal' : forall l k v r, wf l -> wf r -> wf (rbal' l k v r).
Proof. intros; unfold rbal'; des; wfsolve. Qed.

Arguments lbal : simpl never.
Arguments rbal : simpl never.
Arguments rbal' : simpl never.
Arguments makeRed : simpl never.

Ltac lnorm2 := repeat progress (simpl; rewrite ?elements_lbal, ?elements_rbal',
  ?elements_node, ?elements_makeRed, <- ?app_assoc); reflexivity.

Lemma elements_lbalS : forall l k v r,
  elements (lbalS l k v r) = elements l ++ (zs k, zs v) :: elements r.
Proof.
  intros; unfold lbalS; des;
    lnorm2.
Qed.
Lemma elements_rbalS : forall l k v r,
  elements (rbalS l k v r) = elements l ++ (zs k, zs v) :: elements r.
Proof.
  intros; unfold rbalS; des;
    lnorm2.
Qed.
Lemma wf_lbalS : forall l k v r, wf l -> wf r -> wf (lbalS l k v r).
Proof.
  intros; unfold lbalS; des; try apply wf_rbal'; try apply wf_node;
    try apply wf_rbal'; try apply wf_makeRed; wfsolve.
Qed.
Lemma wf_rbalS : forall l k v r, wf l -> wf r -> wf (rbalS l k v r).
Proof.
  intros; unfold rbalS; des; try apply wf_lbal; try apply wf_node;
    try apply wf_lbal; try apply wf_makeRed; wfsolve.
Qed.

Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* Sorted lists of entries                                             *)
(* ------------------------------------------------------------------ *)

Definition keys_lt (c : Z) (l : entries) : Prop := Forall (fun e => fst e < c) l.
Definition keys_gt (c : Z) (l : entries) : Prop := Forall (fun e => c < fst e) l.

Fixpoint srt (l : entries) : Prop :=
  match l with
  | [] => True
  | e :: l' => keys_gt (fst e) l' /\ srt l'
  end.

Lemma keys_gt_weaken : forall a b l, a <= b -> keys_gt b l -> keys_gt a l.
Proof.
  intros a b l H1 H2. unfold keys_gt in *. eapply Forall_impl; [|exact H2].
  intros e He; simpl in He; lia.
Qed.

Lemma keys_lt_weaken : forall a b l, b <= a -> keys_lt b l -> keys_lt a l.
Proof.
  intros a b l H1 H2. unfold keys_lt in *. eapply Forall_impl; [|exact H2].
  intros e He; simpl in He; lia.
Qed.

Lemma srt_app : forall a e b,
  srt (a ++ e :: b) <->
  srt a /\ srt b /\ keys_lt (fst e) a /\ keys_gt (fst e) b.
Proof.
  induction a as [|x a IH]; intros e b; simpl.
  - unfold keys_lt. intuition.
  - rewrite IH. unfold keys_gt, keys_lt. rewrite Forall_app, !Forall_cons_iff.
    split.
    + intros [[H1 [H2 H3]] [H4 [H5 [H6 H7]]]]. intuition.
    + intros [[H1 H2] [H3 [H4 H5]]].
      destruct H4 as [H4 H4'].
      repeat split; auto.
      eapply Forall_impl; [|exact H5]. intros e' He'. simpl in *. lia.
Qed.

Lemma srt_node : forall l k v r,
  srt (elements l ++ (k, v) :: elements r) ->
  srt (elements l) /\ srt (elements r) /\
  keys_lt k (elements l) /\ keys_gt k (elements r).
Proof. intros l k v r H. apply srt_app in H. exact H. Qed.

Lemma Forall_insert : forall (P : Z * Z -> Prop) k v l,
  P (k, v) -> Forall P l -> Forall P (insert k v l).
Proof.
  intros P k v l Hk. induction l as [|[k' v'] l IH]; intros Hl; simpl.
  - constructor; auto.
  - inversion Hl; subst.
    destruct (k <? k') eqn:E1; [constructor; auto|].
    destruct (k =? k') eqn:E2; [constructor; auto|]. constructor; auto.
Qed.

Lemma srt_insert : forall k v l, srt l -> srt (insert k v l).
Proof.
  intros k v l. induction l as [|[k' v'] l IH]; intros Hl; simpl.
  - split; [constructor | exact I].
  - destruct Hl as [Hg Hs].
    destruct (k <? k') eqn:E1.
    + apply Z.ltb_lt in E1. simpl. split; [|split; auto].
      constructor; [simpl; lia|]. eapply keys_gt_weaken; [|exact Hg]. simpl; lia.
    + destruct (k =? k') eqn:E2; [simpl; split; auto|].
      apply Z.ltb_ge in E1. apply Z.eqb_neq in E2. simpl. split; [|auto].
      apply Forall_insert; [simpl; lia | exact Hg].
Qed.

Lemma length_insert : forall k v l, (List.length (insert k v l) <= S (List.length l))%nat.
Proof.
  intros k v l. induction l as [|[k' v'] l IH]; simpl; [lia|].
  destruct (k <? k'); [simpl; lia|]. destruct (k =? k'); simpl; lia.
Qed.

Lemma insert_app_lt : forall k v a x b, k < fst x ->
  insert k v (a ++ x :: b) = insert k v a ++ x :: b.
Proof.
  intros k v a x b H. induction a as [|[k' v'] a IH]; simpl.
  - destruct x as [kx vx]; simpl in H.
    replace (k <? kx) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - destruct (k <? k'); [reflexivity|]. destruct (k =? k'); [reflexivity|].
    rewrite IH. reflexivity.
Qed.

Lemma insert_app_gt : forall k v a b, keys_lt k a ->
  insert k v (a ++ b) = a ++ insert k v b.
Proof.
  intros k v a b H. induction a as [|[k' v'] a IH]; simpl; [reflexivity|].
  inversion H; subst. simpl in *.
  replace (k <? k') with false by (symmetry; apply Z.ltb_ge; lia).
  replace (k =? k') with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite IH by auto. reflexivity.
Qed.

Lemma erase_app : forall c a b, erase c (a ++ b) = erase c a ++ erase c b.
Proof. intros. unfold erase. apply filter_app. Qed.

Lemma erase_none : forall c a, Forall (fun e => fst e <> c) a -> erase c a = a.
Proof.
  intros c a H. unfold erase. induction H as [|e a He Ha IH]; simpl; [reflexivity|].
  replace (fst e =? c) with false by (symmetry; apply Z.eqb_neq; exact He).
  simpl. rewrite IH. reflexivity.
Qed.

Lemma keys_lt_ne : forall c a, keys_lt c a -> Forall (fun e => fst e <> c) a.
Proof. intros c a H. eapply Forall_impl; [|exact H]. intros e He; simpl in He; lia. Qed.
Lemma keys_gt_ne : forall c a, keys_gt c a -> Forall (fun e => fst e <> c) a.
Proof. intros c a H. eapply Forall_impl; [|exact H]. intros e He; simpl in He; lia. Qed.

Lemma Forall_filter' : forall (P : Z * Z -> Prop) f l,
  Forall P l -> Forall P (filter f l).
Proof.
  intros P f l H. induction H as [|e l He Hl IH]; simpl; [constructor|].
  destruct (f e); [constructor|]; auto.
Qed.

Lemma srt_filter : forall f l, srt l -> srt (filter f l).
Proof.
  intros f l. induction l as [|e l IH]; intros Hl; simpl; [exact I|].
  destruct Hl as [Hg Hs]. destruct (f e); simpl; auto.
  split; auto. apply Forall_filter'. exact Hg.
Qed.

Lemma length_erase : forall c l, (List.length (erase c l) <= List.length l)%nat.
Proof. intros. unfold erase. apply filter_length_le. Qed.

Lemma first_key_app : forall p a b,
  first_key p (a ++ b) =
  match first_key p a with Some z => Some z | None => first_key p b end.
Proof.
  intros p a b. induction a as [|[k v] a IH]; simpl; [reflexivity|].
  destruct (p k); [reflexivity | exact IH].
Qed.

Lemma first_key_none : forall (p : Z -> bool) a,
  Forall (fun e => p (fst e) = false) a -> first_key p a = None.
Proof.
  intros p a H. induction H as [|[k v] a He Ha IH]; simpl in *; [reflexivity|].
  rewrite He. exact IH.
Qed.

(* ------------------------------------------------------------------ *)
(* Keys                                                                *)
(* ------------------------------------------------------------------ *)

Lemma key_trichotomy : forall x y : int,
  (key_lt x y = true /\ zs x < zs y) \/
  (key_lt x y = false /\ (x =? y)%uint63 = true /\ zs x = zs y) \/
  (key_lt x y = false /\ (x =? y)%uint63 = false /\ zs y < zs x).
Proof.
  intros x y. unfold key_lt.
  destruct (Sint63.ltb x y) eqn:E1.
  - left. split; [reflexivity|]. apply Sint63.ltb_spec. exact E1.
  - right. assert (H1 : ~ zs x < zs y)
      by (intro H; apply Sint63.ltb_spec in H; congruence).
    destruct (x =? y)%uint63 eqn:E2.
    + left. apply eqb_spec in E2. subst. auto.
    + right. repeat split; auto.
      assert (zs x <> zs y); [|lia].
      intro H. apply Sint63.to_Z_inj in H. subst.
      rewrite eqb_refl in E2. discriminate.
Qed.

Ltac kcase x y :=
  destruct (key_trichotomy x y) as [[E1 Hxy]|[[E1 [E2 Hxy]]|[E1 [E2 Hxy]]]];
  rewrite ?E1, ?E2.

(* ------------------------------------------------------------------ *)
(* Insertion                                                           *)
(* ------------------------------------------------------------------ *)

Lemma elements_ins : forall x vx t, srt (elements t) ->
  elements (ins x vx t) = insert (zs x) (zs vx) (elements t).
Proof.
  intros x vx t. induction t as [|c l IHl y vy s r IHr]; intros Hs;
    [reflexivity|].
  cbn [elements] in Hs. apply srt_node in Hs. destruct Hs as [Hl [Hr [Hlt Hgt]]].
  cbn [ins elements]. kcase x y.
  - assert (H : elements (match c with
                          | Red => node Red (ins x vx l) y vy r
                          | Black => lbal (ins x vx l) y vy r end)
                = elements (ins x vx l) ++ (zs y, zs vy) :: elements r)
      by (destruct c; [apply elements_node | apply elements_lbal]).
    rewrite H, IHl by exact Hl.
    rewrite insert_app_lt by (simpl; lia). reflexivity.
  - rewrite insert_app_gt by (rewrite Hxy; exact Hlt).
    cbn [insert]. rewrite Hxy, Z.ltb_irrefl, Z.eqb_refl. reflexivity.
  - assert (H : elements (match c with
                          | Red => node Red l y vy (ins x vx r)
                          | Black => rbal l y vy (ins x vx r) end)
                = elements l ++ (zs y, zs vy) :: elements (ins x vx r))
      by (destruct c; [apply elements_node | apply elements_rbal]).
    rewrite H, IHr by exact Hr.
    rewrite insert_app_gt by (eapply keys_lt_weaken; [|exact Hlt]; lia).
    cbn [insert].
    replace (zs x <? zs y) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (zs x =? zs y) with false by (symmetry; apply Z.eqb_neq; lia).
    reflexivity.
Qed.

Lemma wf_ins : forall x vx t, wf t -> wf (ins x vx t).
Proof.
  intros x vx t. induction t as [|c l IHl y vy s r IHr]; intros Hw;
    [simpl; auto|].
  pose proof Hw as Hw'. cbn [wf] in Hw'. destruct Hw' as [Hl [Hr _]].
  cbn [ins]. destruct (key_lt x y); [|destruct (x =? y)%uint63; [exact Hw|]];
    destruct c; auto using wf_node, wf_lbal, wf_rbal.
Qed.

Lemma elements_insert_t : forall x vx t, srt (elements t) ->
  elements (insert_t x vx t) = insert (zs x) (zs vx) (elements t).
Proof. intros. unfold insert_t. rewrite elements_makeBlack. apply elements_ins; auto. Qed.

Lemma wf_insert_t : forall x vx t, wf t -> wf (insert_t x vx t).
Proof. intros. unfold insert_t. apply wf_makeBlack, wf_ins; auto. Qed.

(* ------------------------------------------------------------------ *)
(* Deletion                                                            *)
(* ------------------------------------------------------------------ *)

Lemma append_NN : forall lc ll lx lv ls lr rc rl rx rv rs rr,
  append (Node lc ll lx lv ls lr) (Node rc rl rx rv rs rr) =
  match lc, rc with
  | Red, Red =>
      match append lr rl with
      | Node Red lr' x vx _ rl' =>
          node Red (node Red ll lx lv lr') x vx (node Red rl' rx rv rr)
      | lrl => node Red ll lx lv (node Red lrl rx rv rr)
      end
  | Black, Black =>
      match append lr rl with
      | Node Red lr' x vx _ rl' =>
          node Red (node Black ll lx lv lr') x vx (node Black rl' rx rv rr)
      | lrl => lbalS ll lx lv (node Black lrl rx rv rr)
      end
  | Black, Red => node Red (append (Node lc ll lx lv ls lr) rl) rx rv rr
  | Red, Black => node Red ll lx lv (append lr (Node rc rl rx rv rs rr))
  end.
Proof.
  intros. destruct lc, rc; try reflexivity;
    simpl; destruct (append lr rl) as [|[] ? ? ? ? ?]; reflexivity.
Qed.

Ltac red_case :=
  match goal with
  | IHm : elements (Node Red ?a (?x) (?vx) _ ?b) = elements ?lr ++ elements ?rl |- _ =>
      cbn [elements] in IHm;
      assert (K : forall T, elements a ++ (zs x, zs vx) :: elements b ++ T
                            = elements lr ++ elements rl ++ T)
        by (intro T; rewrite app_comm_cons, app_assoc, IHm, <- app_assoc; reflexivity);
      rewrite !elements_node; cbn [elements];
      repeat progress (simpl; rewrite <- ?app_assoc); rewrite K; reflexivity
  end.

Lemma elements_append : forall l r,
  elements (append l r) = elements l ++ elements r.
Proof.
  induction l as [|lc ll IHll lx lv ls lr IHlr]; intros r; [reflexivity|].
  induction r as [|rc rl IHrl rx rv rs rr IHrr].
  - simpl. rewrite app_nil_r. reflexivity.
  - rewrite append_NN. pose proof (IHlr rl) as IHm.
    remember (append lr rl) as m eqn:Em. clear Em.
    destruct lc, rc.
    + destruct m as [|[] a x vx s b];
        [rewrite !elements_node, IHm; lnorm | red_case | rewrite !elements_node, IHm; lnorm].
    + rewrite !elements_node, IHlr. lnorm.
    + rewrite !elements_node, IHrl. lnorm.
    + destruct m as [|[] a x vx s b];
        [rewrite elements_lbalS, !elements_node, IHm; lnorm | red_case
        | rewrite elements_lbalS, !elements_node, IHm; lnorm].
Qed.

Lemma wf_append : forall l r, wf l -> wf r -> wf (append l r).
Proof.
  induction l as [|lc ll IHll lx lv ls lr IHlr]; intros r Hl Hr; [exact Hr|].
  revert Hr. induction r as [|rc rl IHrl rx rv rs rr IHrr]; intros Hr; [exact Hl|].
  rewrite append_NN.
  pose proof Hl as Hl'. pose proof Hr as Hr'. cbn [wf] in Hl', Hr'.
  destruct Hl' as [Hll [Hlr _]]. destruct Hr' as [Hrl [Hrr _]].
  pose proof (IHlr rl Hlr Hrl) as Wm.
  remember (append lr rl) as m eqn:Em. clear Em.
  destruct lc, rc.
  - destruct m as [|[] a x vx s b]; wfsolve.
  - apply wf_node; [exact Hll|]. apply IHlr; auto.
  - apply wf_node; [apply IHrl; exact Hrl | exact Hrr].
  - destruct m as [|[] a x vx s b]; try (apply wf_lbalS); wfsolve.
Qed.

Lemma erase_cons : forall c e l,
  erase c (e :: l) = if fst e =? c then erase c l else e :: erase c l.
Proof. intros. unfold erase. simpl. destruct (fst e =? c); reflexivity. Qed.

Lemma elements_del : forall x t, srt (elements t) ->
  elements (del x t) = erase (zs x) (elements t).
Proof.
  intros x t. induction t as [|c a IHa y vy s b IHb]; intros Hs; [reflexivity|].
  cbn [elements] in Hs. apply srt_node in Hs. destruct Hs as [Ha [Hb [Hlt Hgt]]].
  cbn [del elements]. rewrite erase_app, erase_cons. cbn [fst]. kcase x y.
  - assert (H : elements (match a with
                          | Node Black _ _ _ _ _ => lbalS (del x a) y vy b
                          | _ => node Red (del x a) y vy b end)
                = elements (del x a) ++ (zs y, zs vy) :: elements b)
      by (destruct a as [|[] ? ? ? ? ?];
          [apply elements_node | apply elements_node | apply elements_lbalS]).
    rewrite H, IHa by exact Ha.
    replace (zs y =? zs x) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite (erase_none _ (elements b)); [reflexivity|].
    apply keys_gt_ne. eapply keys_gt_weaken; [|exact Hgt]. lia.
  - rewrite elements_append, Hxy, Z.eqb_refl.
    rewrite (erase_none _ (elements a)) by (apply keys_lt_ne; exact Hlt).
    rewrite (erase_none _ (elements b)) by (apply keys_gt_ne; exact Hgt).
    reflexivity.
  - assert (H : elements (match b with
                          | Node Black _ _ _ _ _ => rbalS a y vy (del x b)
                          | _ => node Red a y vy (del x b) end)
                = elements a ++ (zs y, zs vy) :: elements (del x b))
      by (destruct b as [|[] ? ? ? ? ?];
          [apply elements_node | apply elements_node | apply elements_rbalS]).
    rewrite H, IHb by exact Hb.
    replace (zs y =? zs x) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite (erase_none _ (elements a)); [reflexivity|].
    apply keys_lt_ne. eapply keys_lt_weaken; [|exact Hlt]. lia.
Qed.

Lemma wf_del : forall x t, wf t -> wf (del x t).
Proof.
  intros x t. induction t as [|c a IHa y vy s b IHb]; intros Hw; [exact I|].
  pose proof Hw as Hw'. cbn [wf] in Hw'. destruct Hw' as [Ha [Hb _]].
  cbn [del]. destruct (key_lt x y).
  - destruct a as [|[] ? ? ? ? ?]; auto using wf_node, wf_lbalS.
  - destruct (x =? y)%uint63; [apply wf_append; auto|].
    destruct b as [|[] ? ? ? ? ?]; auto using wf_node, wf_rbalS.
Qed.

Lemma elements_delete_t : forall x t, srt (elements t) ->
  elements (delete_t x t) = erase (zs x) (elements t).
Proof. intros. unfold delete_t. rewrite elements_makeBlack. apply elements_del; auto. Qed.

Lemma wf_delete_t : forall x t, wf t -> wf (delete_t x t).
Proof. intros. unfold delete_t. apply wf_makeBlack, wf_del; auto. Qed.

(* ------------------------------------------------------------------ *)
(* Setting a value                                                     *)
(* ------------------------------------------------------------------ *)

Lemma set_value_none : forall c v l, Forall (fun e => fst e <> c) l ->
  set_value c v l = l.
Proof.
  intros c v l H. unfold set_value. induction H as [|e l He Hl IH]; simpl;
    [reflexivity|].
  replace (fst e =? c) with false by (symmetry; apply Z.eqb_neq; exact He).
  rewrite IH. reflexivity.
Qed.

Lemma set_value_app : forall c v a b,
  set_value c v (a ++ b) = set_value c v a ++ set_value c v b.
Proof. intros. unfold set_value. apply map_app. Qed.

Lemma elements_setv : forall x w t, srt (elements t) ->
  elements (setv_t x w t) = set_value (zs x) (zs w) (elements t).
Proof.
  intros x w t. induction t as [|c l IHl y vy s r IHr]; intros Hs; [reflexivity|].
  cbn [elements] in Hs. apply srt_node in Hs. destruct Hs as [Hl [Hr [Hlt Hgt]]].
  cbn [setv_t elements]. rewrite set_value_app. unfold set_value at 2.
  cbn [map fst]. fold (set_value (zs x) (zs w) (elements r)). kcase x y.
  - cbn [elements]. rewrite IHl by exact Hl.
    replace (zs y =? zs x) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite (set_value_none _ _ (elements r)); [reflexivity|].
    apply keys_gt_ne. eapply keys_gt_weaken; [|exact Hgt]. lia.
  - cbn [elements]. rewrite Hxy, Z.eqb_refl.
    rewrite (set_value_none _ _ (elements l)) by (apply keys_lt_ne; exact Hlt).
    rewrite (set_value_none _ _ (elements r)) by (apply keys_gt_ne; exact Hgt).
    reflexivity.
  - cbn [elements]. rewrite IHr by exact Hr.
    replace (zs y =? zs x) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite (set_value_none _ _ (elements l)); [reflexivity|].
    apply keys_lt_ne. eapply keys_lt_weaken; [|exact Hlt]. lia.
Qed.

Lemma size_setv : forall x w t, size (setv_t x w t) = size t.
Proof.
  intros x w [|c l k v s r]; [reflexivity|]. cbn [setv_t].
  destruct (key_lt x k); [reflexivity|]. destruct (x =? k)%uint63; reflexivity.
Qed.

Lemma wf_setv : forall x w t, wf t -> wf (setv_t x w t).
Proof.
  intros x w t. induction t as [|c l IHl y vy s r IHr]; intros Hw; [exact I|].
  cbn [wf] in Hw. destruct Hw as [Hl [Hr Hs]].
  cbn [setv_t]. destruct (key_lt x y); [|destruct (x =? y)%uint63];
    cbn [wf]; rewrite ?size_setv; auto.
Qed.

Lemma length_set_value : forall c v l, List.length (set_value c v l) = List.length l.
Proof. intros. unfold set_value. apply length_map. Qed.

Lemma srt_set_value : forall c v l, srt l -> srt (set_value c v l).
Proof.
  intros c v l. unfold set_value.
  assert (Hk : forall e, fst (if fst e =? c then (c, v) else e) = fst e).
  { intros e. destruct (fst e =? c) eqn:E; [apply Z.eqb_eq in E; simpl; lia|reflexivity]. }
  induction l as [|e l IH]; intros Hs; simpl; [exact I|].
  destruct Hs as [Hg Hs]. split; auto.
  rewrite Hk. unfold keys_gt in *. apply Forall_map.
  eapply Forall_impl; [|exact Hg]. intros e' He'. rewrite Hk. exact He'.
Qed.

(* ------------------------------------------------------------------ *)
(* The queries                                                         *)
(* ------------------------------------------------------------------ *)

Lemma key_lt_true : forall a b, key_lt a b = true -> zs a < zs b.
Proof. intros a b H. apply Sint63.ltb_spec. exact H. Qed.

Lemma key_lt_false : forall a b, key_lt a b = false -> zs b <= zs a.
Proof.
  intros a b H. destruct (Z.le_gt_cases (zs b) (zs a)) as [L|L]; [exact L|].
  apply Sint63.ltb_spec in L. unfold key_lt in H. congruence.
Qed.

Ltac kcase2 a b :=
  let E := fresh "E" in
  destruct (key_lt a b) eqn:E;
  [apply key_lt_true in E | apply key_lt_false in E].

Ltac fkn H :=
  apply first_key_none; eapply Forall_impl; [|exact H];
  let kk := fresh "kk" in let vv := fresh "vv" in let Hk := fresh "Hk" in
  intros [kk vv] Hk; simpl in *;
  first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; lia.

Lemma Forall_rev' : forall (P : Z * Z -> Prop) l, Forall P l -> Forall P (rev l).
Proof. intros. apply Forall_rev. exact H. Qed.

Lemma rev_node : forall (l : entries) e r,
  rev (l ++ e :: r) = rev r ++ e :: rev l.
Proof. intros. rewrite rev_app_distr. simpl. rewrite <- app_assoc. reflexivity. Qed.

Lemma find_t_spec : forall x t, srt (elements t) ->
  option_map zs (find_t x t) = first_key (fun k => k =? zs x) (elements t).
Proof.
  intros x t. induction t as [|c l IHl y vy s r IHr]; intros Hs; [reflexivity|].
  cbn [elements] in Hs. apply srt_node in Hs. destruct Hs as [Hl [Hr [Hlt Hgt]]].
  cbn [find_t elements]. rewrite first_key_app. cbn [first_key]. kcase x y.
  - rewrite IHl by exact Hl. destruct (first_key _ (elements l)); [reflexivity|].
    replace (zs y =? zs x) with false by (symmetry; apply Z.eqb_neq; lia).
    symmetry. fkn Hgt.
  - replace (first_key _ (elements l)) with (@None Z) by (symmetry; fkn Hlt).
    rewrite Hxy, Z.eqb_refl. reflexivity.
  - replace (first_key _ (elements l)) with (@None Z) by (symmetry; fkn Hlt).
    replace (zs y =? zs x) with false by (symmetry; apply Z.eqb_neq; lia).
    apply IHr. exact Hr.
Qed.

Lemma lower_t_spec : forall x t, srt (elements t) ->
  option_map zs (lower_t x t) = first_key (fun k => zs x <=? k) (elements t).
Proof.
  intros x t. induction t as [|c l IHl y vy s r IHr]; intros Hs; [reflexivity|].
  cbn [elements] in Hs. apply srt_node in Hs. destruct Hs as [Hl [Hr [Hlt Hgt]]].
  cbn [lower_t elements]. rewrite first_key_app. cbn [first_key]. kcase2 y x.
  - replace (first_key _ (elements l)) with (@None Z) by (symmetry; fkn Hlt).
    replace (zs x <=? zs y) with false by (symmetry; apply Z.leb_gt; lia).
    apply IHr. exact Hr.
  - rewrite <- IHl by exact Hl. destruct (lower_t x l); [reflexivity|].
    replace (zs x <=? zs y) with true by (symmetry; apply Z.leb_le; lia).
    reflexivity.
Qed.

Lemma upper_t_spec : forall x t, srt (elements t) ->
  option_map zs (upper_t x t) = first_key (fun k => zs x <? k) (elements t).
Proof.
  intros x t. induction t as [|c l IHl y vy s r IHr]; intros Hs; [reflexivity|].
  cbn [elements] in Hs. apply srt_node in Hs. destruct Hs as [Hl [Hr [Hlt Hgt]]].
  cbn [upper_t elements]. rewrite first_key_app. cbn [first_key]. kcase2 x y.
  - rewrite <- IHl by exact Hl. destruct (upper_t x l); [reflexivity|].
    replace (zs x <? zs y) with true by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
  - replace (first_key _ (elements l)) with (@None Z) by (symmetry; fkn Hlt).
    replace (zs x <? zs y) with false by (symmetry; apply Z.ltb_ge; lia).
    apply IHr. exact Hr.
Qed.

Lemma pred_t_spec : forall x t, srt (elements t) ->
  option_map zs (pred_t x t) = first_key (fun k => k <? zs x) (rev (elements t)).
Proof.
  intros x t. induction t as [|c l IHl y vy s r IHr]; intros Hs; [reflexivity|].
  cbn [elements] in Hs. apply srt_node in Hs. destruct Hs as [Hl [Hr [Hlt Hgt]]].
  apply Forall_rev' in Hlt. apply Forall_rev' in Hgt.
  cbn [pred_t elements]. rewrite rev_node, first_key_app. cbn [first_key]. kcase2 y x.
  - rewrite <- IHr by exact Hr. destruct (pred_t x r); [reflexivity|].
    replace (zs y <? zs x) with true by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
  - replace (first_key _ (rev (elements r))) with (@None Z) by (symmetry; fkn Hgt).
    replace (zs y <? zs x) with false by (symmetry; apply Z.ltb_ge; lia).
    apply IHl. exact Hl.
Qed.

Lemma front_t_spec : forall t,
  option_map zs (front_t t) = first_key (fun _ => true) (elements t).
Proof.
  induction t as [|c l IHl y vy s r IHr]; [reflexivity|].
  cbn [front_t elements]. rewrite first_key_app, <- IHl.
  destruct (front_t l); reflexivity.
Qed.

Lemma back_t_spec : forall t,
  option_map zs (back_t t) = first_key (fun _ => true) (rev (elements t)).
Proof.
  induction t as [|c l IHl y vy s r IHr]; [reflexivity|].
  cbn [back_t elements]. rewrite rev_node, first_key_app, <- IHr.
  destruct (back_t r); reflexivity.
Qed.

Lemma find_app' : forall (f : Z * Z -> bool) a b,
  find f (a ++ b) = match find f a with Some e => Some e | None => find f b end.
Proof.
  intros f a b. induction a as [|e a IH]; simpl; [reflexivity|].
  destruct (f e); [reflexivity | exact IH].
Qed.

Lemma find_none : forall (f : Z * Z -> bool) a,
  Forall (fun e => f e = false) a -> find f a = None.
Proof.
  intros f a H. induction H as [|e a He Ha IH]; simpl; [reflexivity|].
  rewrite He. exact IH.
Qed.

Ltac fdn H :=
  apply find_none; eapply Forall_impl; [|exact H];
  let kk := fresh "kk" in let vv := fresh "vv" in let Hk := fresh "Hk" in
  intros [kk vv] Hk; simpl in *; apply Z.eqb_neq; lia.

Lemma lookup_t_spec : forall x t, srt (elements t) ->
  option_map zs (lookup_t x t) = lookup (zs x) (elements t).
Proof.
  intros x t. induction t as [|c l IHl y vy s r IHr]; intros Hs; [reflexivity|].
  cbn [elements] in Hs. apply srt_node in Hs. destruct Hs as [Hl [Hr [Hlt Hgt]]].
  unfold lookup in *. cbn [lookup_t elements]. rewrite find_app'. cbn [find fst].
  kcase x y.
  - rewrite IHl by exact Hl. destruct (find _ (elements l)); [reflexivity|].
    replace (zs y =? zs x) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (find _ (elements r)) with (@None (Z * Z)) by (symmetry; fdn Hgt).
    reflexivity.
  - replace (find _ (elements l)) with (@None (Z * Z)) by (symmetry; fdn Hlt).
    rewrite Hxy, Z.eqb_refl. reflexivity.
  - replace (find _ (elements l)) with (@None (Z * Z)) by (symmetry; fdn Hlt).
    replace (zs y =? zs x) with false by (symmetry; apply Z.eqb_neq; lia).
    apply IHr. exact Hr.
Qed.

(* ------------------------------------------------------------------ *)
(* Sizes, k-th and rank                                                *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma size_wf : forall t, wf t ->
  (φ (size t)) = Z.of_nat (List.length (elements t)) mod wB.
Proof.
  induction t as [|c l IHl y vy s r IHr]; intros Hw; [reflexivity|].
  cbn [wf] in Hw. destruct Hw as [Hl [Hr Hs]].
  cbn [size elements]. rewrite Hs, !add_spec, IHl, IHr by assumption.
  change (φ 1)%uint63 with 1. rewrite length_app. cbn [List.length].
  rewrite Nat2Z.inj_add, Nat2Z.inj_succ.
  generalize (Z.of_nat (List.length (elements l))) (Z.of_nat (List.length (elements r))).
  intros A B. rewrite wB_val. Z.to_euclidean_division_equations. lia.
Qed.

Lemma size_len : forall t, wf t ->
  Z.of_nat (List.length (elements t)) < wB ->
  (φ (size t)) = Z.of_nat (List.length (elements t)).
Proof. intros t Hw Hl. rewrite size_wf by exact Hw. apply Z.mod_small. lia. Qed.

Lemma kth_t_spec : forall t n, wf t ->
  Z.of_nat (List.length (elements t)) < wB ->
  option_map zs (kth_t n t) = option_map fst (nth_error (elements t) (Z.to_nat (φ n))).
Proof.
  induction t as [|c l IHl y vy s r IHr]; intros n Hw Hb.
  - simpl. destruct (Z.to_nat (φ n)); reflexivity.
  - cbn [wf] in Hw. destruct Hw as [Hl [Hr _]].
    cbn [elements] in Hb |- *. rewrite length_app in Hb. cbn [List.length] in Hb.
    assert (Hsl : (φ (size l)) = Z.of_nat (List.length (elements l)))
      by (apply size_len; [exact Hl | lia]).
    pose proof (to_Z_bounded n) as Bn.
    cbn [kth_t].
    destruct (n <? size l)%uint63 eqn:E1.
    + rewrite ltb_spec in E1. rewrite nth_error_app1 by lia. apply IHl; [exact Hl | lia].
    + rewrite <- Bool.not_true_iff_false, ltb_spec in E1.
      destruct (n =? size l)%uint63 eqn:E2.
      * apply eqb_spec in E2. subst n.
        rewrite nth_error_app2 by lia.
        replace (Z.to_nat (φ (size l)) - List.length (elements l))%nat with 0%nat by lia.
        reflexivity.
      * assert (Hne : (φ n) <> (φ (size l)))
          by (intro E; apply to_Z_inj in E; rewrite E, eqb_refl in E2; discriminate).
        assert (Hsub : (φ (n - size l - 1)) = (φ n) - Z.of_nat (List.length (elements l)) - 1)
          by (rewrite <- Hsl; sia).
        rewrite IHr by (first [exact Hr | lia]).
        rewrite nth_error_app2 by lia.
        replace (Z.to_nat (φ n) - List.length (elements l))%nat
          with (S (Z.to_nat (φ (n - size l - 1)))) by lia.
        reflexivity.
Qed.

Lemma filter_none' : forall (f : Z * Z -> bool) l,
  Forall (fun e => f e = false) l -> filter f l = [].
Proof.
  intros f l H. induction H as [|e l He Hl IH]; simpl; [reflexivity|].
  rewrite He. exact IH.
Qed.

Lemma filter_all' : forall (f : Z * Z -> bool) l,
  Forall (fun e => f e = true) l -> filter f l = l.
Proof.
  intros f l H. induction H as [|e l He Hl IH]; simpl; [reflexivity|].
  rewrite He, IH. reflexivity.
Qed.

Lemma rank_t_spec : forall x t, wf t -> srt (elements t) ->
  Z.of_nat (List.length (elements t)) < wB ->
  (φ (rank_t x t)) = rank (zs x) (elements t).
Proof.
  intros x t. induction t as [|c l IHl y vy s r IHr]; intros Hw Hs Hb;
    [reflexivity|].
  cbn [wf] in Hw. destruct Hw as [Hl [Hr _]].
  cbn [elements] in Hs, Hb |- *. rewrite length_app in Hb. cbn [List.length] in Hb.
  apply srt_node in Hs. destruct Hs as [Sl [Sr [Hlt Hgt]]].
  assert (Hsl : (φ (size l)) = Z.of_nat (List.length (elements l)))
    by (apply size_len; [exact Hl | lia]).
  unfold rank. rewrite filter_app. cbn [filter fst]. rewrite length_app.
  cbn [rank_t]. kcase x y.
  - replace (zs y <? zs x) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite (filter_none' _ (elements r)).
    + rewrite IHl by (first [assumption | lia]). unfold rank. simpl. lia.
    + eapply Forall_impl; [|exact Hgt]. intros [kk vv] Hk; simpl in *.
      apply Z.ltb_ge; lia.
  - replace (zs y <? zs x) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite (filter_none' _ (elements r)).
    + rewrite (filter_all' _ (elements l)).
      * rewrite Hsl. simpl. lia.
      * eapply Forall_impl; [|exact Hlt]. intros [kk vv] Hk; simpl in *.
        apply Z.ltb_lt; lia.
    + eapply Forall_impl; [|exact Hgt]. intros [kk vv] Hk; simpl in *.
      apply Z.ltb_ge; lia.
  - replace (zs y <? zs x) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite (filter_all' _ (elements l)).
    + rewrite !add_spec, Hsl, IHr by (first [assumption | lia]).
      unfold rank. change (φ 1)%uint63 with 1.
      pose proof (filter_length_le (fun e => fst e <? zs x) (elements r)).
      cbn [List.length].
      rewrite Z.mod_small by lia. rewrite Z.mod_small by lia. lia.
    + eapply Forall_impl; [|exact Hlt]. intros [kk vv] Hk; simpl in *.
      apply Z.ltb_lt; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The instances                                                       *)
(* ------------------------------------------------------------------ *)

Lemma slength_set : forall (A : Set) (t : array A) i (a : A),
  PArray.length t.[i <- a] = PArray.length t.
Proof. intros. exact (PArray.length_set A t i a). Qed.
Lemma sget_set_same : forall (A : Set) (t : array A) i (a : A),
  (i <? PArray.length t)%uint63 = true -> t.[i <- a].[i] = a.
Proof. intros A t i a H. exact (PArray.get_set_same A t i a H). Qed.
Lemma sget_set_other : forall (A : Set) (t : array A) i j (a : A),
  i <> j -> t.[i <- a].[j] = t.[j].
Proof. intros A t i j a H. exact (PArray.get_set_other A t i j a H). Qed.
Lemma sget_make : forall (A : Set) (a : A) n i, (PArray.make n a).[i] = a.
Proof. intros. exact (PArray.get_make A a n i). Qed.
Lemma slength_make : forall (A : Set) n (a : A),
  PArray.length (PArray.make n a)
  = if (n <=? PArray.max_length)%uint63 then n else PArray.max_length.
Proof. intros. exact (PArray.length_make A n a). Qed.

(* Instance i is represented by tree t and cursor c, with at most b keys. *)
Definition inst_ok (i : inst) (t : tree) (c : option int) (b : Z) : Prop :=
  wf t /\ srt (elements t) /\ Z.of_nat (List.length (elements t)) <= b /\
  fst i = elements t /\ snd i = option_map zs c.

Record rel (s : state) (T : array tree) (C : array (option int)) (b : Z) : Prop := {
  rel_T : PArray.length T = 1001%uint63;
  rel_C : PArray.length C = 1001%uint63;
  rel_i : forall id : N, (id <= 1000)%N ->
            inst_ok (s id) T.[of_Z (Z.of_N id)] C.[of_Z (Z.of_N id)] b
}.

Definition upd (s : state) (id : N) (i : inst) : state :=
  fun j => if N.eqb j id then i else s j.

Lemma inst_ok_weaken : forall i t c b b', b <= b' -> inst_ok i t c b -> inst_ok i t c b'.
Proof. unfold inst_ok. intuition lia. Qed.

Lemma rel_weaken : forall s T C b b', b <= b' -> rel s T C b -> rel s T C b'.
Proof.
  intros s T C b b' Hb [H1 H2 H3]. constructor; auto.
  intros id Hid. eapply inst_ok_weaken; [exact Hb | auto].
Qed.

Lemma idx_eq : forall (idm : int) (id : N), (φ idm) = Z.of_N id -> of_Z (Z.of_N id) = idm.
Proof. intros idm id H. rewrite <- H. apply of_to_Z. Qed.

Lemma idx_ne : forall (idm : int) (id id' : N), (φ idm) = Z.of_N id ->
  (id' <= 1000)%N -> id' <> id -> idm <> of_Z (Z.of_N id').
Proof.
  intros idm id id' H Hb Hne E. apply Hne.
  assert ((φ idm) = (φ (of_Z (Z.of_N id')))) by (rewrite E; reflexivity).
  rewrite of_Z_spec, Z.mod_small in H0 by (rewrite wB_val; lia). lia.
Qed.

Lemma rel_set : forall s T C b b' (idm : int) (id : N) i t c,
  rel s T C b -> b <= b' -> (φ idm) = Z.of_N id -> (id <= 1000)%N ->
  inst_ok i t c b' ->
  rel (fun j => if N.eqb j id then i else s j) T.[idm <- t] C.[idm <- c] b'.
Proof.
  intros s T C b b' idm id i t c [HT HC Hi] Hb Hid Hidb Hok.
  assert (Hlt : (idm <? 1001)%uint63 = true) by (rewrite ltb_spec; change (φ 1001)%uint63 with 1001; lia).
  constructor.
  - rewrite slength_set. exact HT.
  - rewrite slength_set. exact HC.
  - intros id' Hid'. destruct (N.eqb_spec id' id) as [E|E].
    + subst id'. rewrite (idx_eq idm id Hid).
      rewrite !sget_set_same by (rewrite ?HT, ?HC; exact Hlt). exact Hok.
    + rewrite !sget_set_other by (apply (idx_ne idm id id'); auto).
      eapply inst_ok_weaken; [exact Hb | apply Hi; exact Hid'].
Qed.

Lemma rel_setC : forall s T C b b' (idm : int) (id : N) i c,
  rel s T C b -> b <= b' -> (φ idm) = Z.of_N id -> (id <= 1000)%N ->
  inst_ok i T.[idm] c b' ->
  rel (fun j => if N.eqb j id then i else s j) T C.[idm <- c] b'.
Proof.
  intros s T C b b' idm id i c [HT HC Hi] Hb Hid Hidb Hok.
  assert (Hlt : (idm <? 1001)%uint63 = true) by (rewrite ltb_spec; change (φ 1001)%uint63 with 1001; lia).
  constructor.
  - exact HT.
  - rewrite slength_set. exact HC.
  - intros id' Hid'. destruct (N.eqb_spec id' id) as [E|E].
    + subst id'. rewrite (idx_eq idm id Hid).
      rewrite !sget_set_same by (rewrite ?HT, ?HC; exact Hlt). exact Hok.
    + rewrite !sget_set_other by (apply (idx_ne idm id id'); auto).
      eapply inst_ok_weaken; [exact Hb | apply Hi; exact Hid'].
Qed.

Lemma rel_setT : forall s T C b b' (idm : int) (id : N) i t,
  rel s T C b -> b <= b' -> (φ idm) = Z.of_N id -> (id <= 1000)%N ->
  inst_ok i t C.[idm] b' ->
  rel (fun j => if N.eqb j id then i else s j) T.[idm <- t] C b'.
Proof.
  intros s T C b b' idm id i t [HT HC Hi] Hb Hid Hidb Hok.
  assert (Hlt : (idm <? 1001)%uint63 = true) by (rewrite ltb_spec; change (φ 1001)%uint63 with 1001; lia).
  constructor.
  - rewrite slength_set. exact HT.
  - exact HC.
  - intros id' Hid'. destruct (N.eqb_spec id' id) as [E|E].
    + subst id'. rewrite (idx_eq idm id Hid).
      rewrite !sget_set_same by (rewrite ?HT, ?HC; exact Hlt). exact Hok.
    + rewrite !sget_set_other by (apply (idx_ne idm id id'); auto).
      eapply inst_ok_weaken; [exact Hb | apply Hi; exact Hid'].
Qed.

Lemma rel_get : forall s T C b (idm : int) (id : N),
  rel s T C b -> (φ idm) = Z.of_N id -> (id <= 1000)%N ->
  inst_ok (s id) T.[idm] C.[idm] b.
Proof.
  intros s T C b idm id [_ _ Hi] Hid Hb. rewrite <- (idx_eq idm id Hid). auto.
Qed.

Lemma rel_init : rel init (PArray.make 1001 Leaf) (PArray.make 1001 None) 0.
Proof.
  constructor; [reflexivity | reflexivity |].
  intros id Hid. rewrite !sget_make. unfold inst_ok, init. simpl. intuition lia.
Qed.

(* ------------------------------------------------------------------ *)
(* One command                                                         *)
(* ------------------------------------------------------------------ *)

Lemma zs_small : forall a : int, 0 <= (φ a) < 2 ^ 62 -> zs a = (φ a).
Proof.
  intros a H. rewrite Sint63.to_Z_cmodwB. apply Sint63.cmod_small.
  rewrite wB_val. lia.
Qed.

Lemma phi_nonneg : forall a : int, 0 <= zs a -> (φ a) = zs a.
Proof.
  intros a H. rewrite <- Sint63.to_Z_mod_Uint63to_Z. apply Z.mod_small.
  pose proof (Sint63.to_Z_bounded a) as B.
  change (Sint63Axioms.to_Z Sint63.max_int) with 4611686018427387903 in B.
  rewrite wB_val. lia.
Qed.

Lemma repr_opt : forall (v : option int) (m : option Z),
  option_map zs v = m -> repr (v : option sint) m.
Proof.
  intros [a|] [m|] H; cbv [repr repr_option repr_sint]; simpl in *;
    try discriminate; try injection H; auto.
Qed.

Definition out_ok (o : list (option Z)) (O O' : array (option int)) (p p' : int) : Prop :=
  (o = [] /\ O' = O /\ p' = p) \/
  (exists (m : option Z) (v : option int),
     o = [m] /\ repr (v : option sint) m /\ O' = O.[p <- v] /\ p' = (p + 1)%uint63).

Definition valid_ops : list N :=
  [97; 63; 108; 117; 105; 101; 102; 98; 62; 60; 114; 107; 103; 115; 122]%N.

Ltac mv :=
  split; [|left; auto];
  eapply rel_setC; [eassumption | lia | eassumption | lia |];
  match goal with tt := ?v : tree |- _ => change v with tt end;
  unfold inst_ok; simpl; repeat split; auto; try lia; symmetry.

Lemma exec_correct : forall s T C O p b (idm opm xm ym : int) (id op : N) (x y : Z)
    s' o T' C' O' p',
  rel s T C b -> b < 4194304 ->
  (φ idm) = Z.of_N id -> (1 <= id <= 1000)%N ->
  (φ opm) = Z.of_N op -> In op valid_ops ->
  zs xm = x -> zs ym = y -> args_ok op x y ->
   Reference.step s (id, op, x, y) = (s', o) ->
  exec T C O p idm opm xm ym = (T', C', O', p') ->
  rel s' T' C' (b + 1) /\ out_ok o O O' p p'.
Proof.
  intros s T C O p b idm opm xm ym id op x y s' o T' C' O' p'
    Hr Hb Hid Hidb Hop Hin Hx Hy Ha Hs He.
  pose proof (rel_get s T C b idm id Hr Hid ltac:(lia)) as Hi.
  destruct Hi as (Wt & St & Lt & Ft & Ct).
  set (t := T.[idm]) in *. set (cur := C.[idm]) in *.
  assert (Lt' : Z.of_nat (List.length (elements t)) < wB) by (rewrite wB_val; lia).
  unfold Reference.step in Hs. destruct (s id) as [tm cm] eqn:Es. simpl in Ft, Ct. subst tm cm.
  unfold valid_ops in Hin.
  repeat destruct Hin as [Hin|Hin]; [| | | | | | | | | | | | | | | destruct Hin];
    subst op; unfold args_ok in Ha;
    (assert (Eop : opm = of_Z (Z.of_N _)) by (rewrite <- Hop; symmetry; apply of_to_Z));
    simpl in Eop; subst opm;
    unfold exec in He; simpl in He; fold t cur in He;
    injection He as <- <- <- <-; injection Hs as <- <-; subst x y;
    assert (Ecur : C.[idm] = cur) by reflexivity; clearbody cur.
  - (* a *)
    assert (Hxm : (φ xm) = zs xm) by (apply phi_nonneg; lia).
    pose proof (rel_get s T C b xm (Z.to_N (zs xm)) Hr ltac:(lia) ltac:(lia))
      as (W2 & S2 & L2 & F2 & C2).
    split; [|left; auto].
    eapply rel_set; [exact Hr | lia | exact Hid | lia |].
    unfold inst_ok; simpl; repeat split; auto; lia.
  - (* ? *) mv. apply find_t_spec. exact St.
  - (* l *) mv. apply lower_t_spec. exact St.
  - (* u *) mv. apply upper_t_spec. exact St.
  - (* i *)
    split; [|left; auto].
    eapply rel_set; [exact Hr | lia | exact Hid | lia |].
    pose proof (length_insert (zs xm) (zs ym) (elements t)).
    unfold inst_ok; simpl; rewrite elements_insert_t by exact St;
      repeat split; auto using wf_insert_t, srt_insert; lia.
  - (* e *)
    split; [|left; auto].
    eapply rel_set; [exact Hr | lia | exact Hid | lia |].
    destruct cur as [c|]; simpl.
    + pose proof (length_erase (zs c) (elements t)).
      unfold inst_ok; simpl; rewrite elements_delete_t by exact St;
        repeat split; auto using wf_delete_t; [apply srt_filter; exact St | lia].
    + unfold inst_ok; simpl; repeat split; auto; lia.
  - (* f *) mv. apply front_t_spec.
  - (* b *) mv. apply back_t_spec.
  - (* > *) mv. destruct cur as [c|]; [apply upper_t_spec; exact St | reflexivity].
  - (* < *) mv. destruct cur as [c|]; [apply pred_t_spec; exact St | reflexivity].
  - (* r *)
    split; [apply (rel_weaken s T C b); [lia | exact Hr]|].
    right. eexists; eexists; split; [reflexivity|]. split; [|split; reflexivity].
    apply repr_opt. destruct cur as [c|]; [|reflexivity]. simpl. f_equal.
    pose proof (rank_t_spec c t Wt St Lt') as Hk.
    pose proof (filter_length_le (fun e => fst e <? zs c) (elements t)).
    unfold rank in Hk. rewrite zs_small; [exact Hk | lia].
  - (* k *) mv. unfold kth.
    destruct (Sint63.ltb xm 0) eqn:E.
    + apply Sint63.ltb_spec in E. rewrite Sint63.to_Z_0 in E. change (zs xm < 0) in E.
      replace (0 <=? zs xm) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    + assert (E' : 0 <= zs xm).
      { destruct (Z.le_gt_cases 0 (zs xm)) as [L|L]; [exact L|].
        rewrite <- Sint63.to_Z_0 in L. apply Sint63.ltb_spec in L. congruence. }
      replace (0 <=? zs xm) with true by (symmetry; apply Z.leb_le; lia).
      rewrite <- (phi_nonneg xm E'). apply kth_t_spec; assumption.
  - (* g *)
    split; [apply (rel_weaken s T C b); [lia | exact Hr]|].
    right. eexists; eexists; split; [reflexivity|]. split; [|split; reflexivity].
    apply repr_opt. destruct cur as [c|]; [|reflexivity]. simpl.
    apply lookup_t_spec. exact St.
  - (* s *)
    split; [|left; auto].
    eapply rel_setT; [exact Hr | lia | exact Hid | lia |].
    destruct cur as [c|]; simpl.
    + unfold inst_ok; simpl; rewrite elements_setv by exact St;
        repeat split; auto using wf_setv, srt_set_value;
        rewrite ?length_set_value, ?Ecur; [lia | reflexivity].
    + unfold inst_ok; simpl; rewrite Ecur; repeat split; auto; lia.
  - (* z *)
    split; [apply (rel_weaken s T C b); [lia | exact Hr]|].
    right. eexists; eexists; split; [reflexivity|]. split; [|split; reflexivity].
    apply repr_opt. simpl. f_equal.
    rewrite zs_small; rewrite size_len by assumption; [reflexivity | lia].
Qed.

Lemma step_len : forall s id op x y (opm : int),
  (φ opm) = Z.of_N op -> In op valid_ops ->
  List.length (snd (Reference.step s (id, op, x, y))) = if is_out opm then 1%nat else 0%nat.
Proof.
  intros s id op x y opm Hop Hin.
  unfold Reference.step. destruct (s id) as [t cur].
  unfold valid_ops in Hin.
  repeat destruct Hin as [Hin|Hin]; [| | | | | | | | | | | | | | | destruct Hin];
    subst op;
    (assert (Eop : opm = of_Z (Z.of_N _)) by (rewrite <- Hop; symmetry; apply of_to_Z));
    simpl in Eop; subst opm; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The loops                                                           *)
(* ------------------------------------------------------------------ *)

Lemma of_nat_phi : forall j : int, Uint63.of_nat (Z.to_nat (φ j)) = j.
Proof.
  intros j. rewrite Z2Nat.id by (pose proof (to_Z_bounded j); lia). apply of_to_Z.
Qed.

Lemma repr_get_u : forall (x : array uint) (l : list N) k, repr x l ->
  (k < List.length l)%nat -> (φ (x.[Uint63.of_nat k])) = Z.of_N (nth k l 0%N).
Proof.
  intros x l k [Hl Hc] Hk. destruct (Hc k Hk) as (m & Hm & Hr).
  rewrite (nth_error_nth _ _ _ Hm). unfold repr, repr_uint in Hr.
  rewrite <- Hr. rewrite Z2N.id by (apply to_Z_bounded). reflexivity.
Qed.

Lemma repr_get_s : forall (x : array sint) (l : list Z) k, repr x l ->
  (k < List.length l)%nat -> zs (x.[Uint63.of_nat k]) = nth k l 0.
Proof.
  intros x l k [Hl Hc] Hk. destruct (Hc k Hk) as (m & Hm & Hr).
  rewrite (nth_error_nth _ _ _ Hm). unfold repr, repr_sint in Hr.
  rewrite <- Hr. reflexivity.
Qed.

Lemma repr_len : forall {A M} `{Repr A M} (x : array A) (l : list M), repr x l ->
  (φ (PArray.length x)) = Z.of_nat (List.length l).
Proof. intros A M R x l [Hl _]. symmetry. exact Hl. Qed.

Lemma alength_bound : forall (A : Set) (t : array A), (φ (PArray.length t)) <= 4194303.
Proof.
  intros A t. pose proof (PArray.leb_length A t) as H.
  rewrite leb_spec in H. exact H.
Qed.

Lemma count_loop_eq : forall ops q j acc H,
  count_loop ops q j acc H =
  match bdec (j <? q)%uint63 with
  | left Hj =>
      count_loop ops q (j + 1)%uint63 (if output_command ops.[j] then (acc + 1)%uint63 else acc)
        (Acc_inv H (dec_step q j Hj))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma run_loop_eq : forall commands q j T C O p H,
  run_loop commands q j T C O p H =
  match bdec (j <? q)%uint63 with
  | left Hj =>
      let '(id, op, x, y) := encode_machine commands.[j] in
      let '(T', C', O', p') := exec T C O p id op x y in
      run_loop commands q (j + 1)%uint63 T' C' O' p'
        (Acc_inv H (dec_step q j Hj))
  | right _ => O
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma encode_repr : forall (machine : machine_command) (mathematical : Prelude.command),
  repr machine mathematical -> operation_valid (snd mathematical) ->
  let '(idm, opm, xm, ym) := encode_machine machine in
  let '(id, op, x, y) := encode_math mathematical in
  (φ idm) = Z.of_N id /\ (φ opm) = Z.of_N op /\ In op valid_ops /\
  zs xm = x /\ zs ym = y /\ args_ok op x y.
Proof.
  intros [idm mo] [id op] [Hid Hop] Hv.
  cbn [fst snd] in Hid, Hop, Hv.
  assert (Hi : (φ idm) = Z.of_N id).
  { cbv [repr repr_uint] in Hid. rewrite <- Hid, Z2N.id by apply to_Z_bounded. reflexivity. }
  destruct mo; destruct op; cbn [repr repr_operation] in Hop; try contradiction;
    cbn [snd operation_valid] in Hv;
    cbn [encode_machine encode_math encode_operation];
    change (φ 0)%uint63 with 0 in *;
    cbn [Z.to_N] in *;
    unfold valid_ops, args_ok;
    cbv [repr repr_sint repr_uint] in Hop.
  all: repeat match goal with
    | |- context [φ ?c] =>
      tryif is_var c then fail else
      let v := eval vm_compute in (φ c) in change (φ c) with v
    end.
  all: cbn [Z.to_N Z.of_N In] in *.
  all: try solve [rewrite ?Sint63.to_Z_0; intuition].
  change (Z.to_N (φ source) = source0) in Hop.
  assert (Hsource : (φ source) = Z.of_N source0).
  { rewrite <- Hop, Z2N.id by apply to_Z_bounded. reflexivity. }
  assert (Hs : zs source = Z.of_N source0).
  { rewrite zs_small; [exact Hsource | lia]. }
  rewrite Hs, Sint63.to_Z_0. repeat split; intuition lia.
Qed.

Lemma output_encode : forall line,
  let '(_, code, _, _) := encode_machine line in
  is_out code = output_command line.
Proof. intros [id op]; destruct op; reflexivity. Qed.

Section Loops.

Variables (lines : list Prelude.command) (ca : array machine_command).
Hypothesis Hv : valid_input lines.
Hypothesis Hca : repr ca lines.

Let n := List.length lines.

Definition cmdf (k : nat) : command :=
  encode_math (nth k lines (0%N, GetSize)).

Definition cmds_from (j : nat) : list command := map cmdf (seq j (n - j)).

Lemma cmds_from_S : forall j, (j < n)%nat -> cmds_from j = cmdf j :: cmds_from (S j).
Proof.
  intros j Hj. unfold cmds_from. replace (n - j)%nat with (S (n - S j)) by lia.
  reflexivity.
Qed.

Lemma cmds_from_n : forall j, (n <= j)%nat -> cmds_from j = [].
Proof. intros j Hj. unfold cmds_from. replace (n - j)%nat with 0%nat by lia. reflexivity. Qed.

Lemma command_at : forall k, (k < n)%nat ->
  repr ca.[Uint63.of_nat k] (nth k lines (0%N, GetSize)) /\
  (1 <= fst (nth k lines (0%N, GetSize)) <= 1000)%N /\
  operation_valid (snd (nth k lines (0%N, GetSize))).
Proof.
  intros k Hk. split.
  - destruct Hca as [_ Hc]. destruct (Hc k Hk) as (c & Hc' & Hr).
    rewrite (nth_error_nth _ _ _ Hc'). exact Hr.
  - exact (proj1 (Forall_nth _ _) Hv k (0%N, GetSize) Hk).
Qed.

Lemma command_step_len : forall k s, (k < n)%nat ->
  List.length (snd (Reference.step s (cmdf k))) =
    if output_command ca.[Uint63.of_nat k] then 1%nat else 0%nat.
Proof.
  intros k s Hk. destruct (command_at k Hk) as [Hr [_ Hv']].
  pose proof (encode_repr _ _ Hr Hv') as Hf.
  pose proof (output_encode ca.[Uint63.of_nat k]) as Ho.
  destruct (encode_machine ca.[Uint63.of_nat k]) as [[[idm opm] xm] ym].
  unfold cmdf. destruct (encode_math _) as [[[id op] x] y].
  destruct Hf as [Hi [Hop [Hin _]]]. rewrite <- Ho.
  exact (step_len s id op x y opm Hop Hin).
Qed.

Lemma replay_len : forall j s,
  (List.length (replay s (cmds_from j)) <= n - j)%nat.
Proof.
  intros j. remember (n - j)%nat as m eqn:Em. revert j Em.
  induction m as [|m IH]; intros j Em s.
  - rewrite cmds_from_n by lia. simpl. lia.
  - rewrite cmds_from_S by lia. cbn [replay].
    destruct (Reference.step s (cmdf j)) as [s' o] eqn:Es.
    pose proof (command_step_len j s ltac:(lia)) as Hl.
    rewrite Es in Hl. simpl in Hl.
    pose proof (IH (S j) ltac:(lia) s') as IH'.
    rewrite length_app. destruct (output_command _); lia.
Qed.

Lemma count_loop_spec : forall (q : int), (φ q) = Z.of_nat n ->
  forall z j acc H s, gap q j = z -> (φ j) <= (φ q) -> (φ acc) <= (φ j) ->
  (φ (count_loop ca q j acc H))
  = (φ acc) + Z.of_nat (List.length (replay s (cmds_from (Z.to_nat (φ j))))).
Proof.
  intros q Hq z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j acc H s Hz Hjq Hacc.
  pose proof (to_Z_bounded j) as Bj.
  pose proof (replay_len (Z.to_nat (φ j)) s) as Hle.
  rewrite count_loop_eq.
  destruct (bdec (j <? q)%uint63) as [Hj | Hj].
  - pose proof Hj as Hj'. rewrite ltb_spec in Hj'.
    assert (Hj1 : (φ (j + 1))%uint63 = (φ j) + 1) by sia.
    rewrite cmds_from_S by lia. cbn [replay].
    destruct (Reference.step s (cmdf (Z.to_nat (φ j)))) as [s' o] eqn:Es.
    pose proof (command_step_len (Z.to_nat (φ j)) s ltac:(lia)) as Hl.
    rewrite of_nat_phi, Es in Hl. simpl in Hl.
    pose proof (replay_len (S (Z.to_nat (φ j))) s') as Hle'.
    rewrite (IH (gap q (j + 1)%uint63)) with (s := s');
      [| rewrite <- Hz; apply dec_step; exact Hj | reflexivity | lia |].
    + replace (Z.to_nat (φ (j + 1))%uint63) with (S (Z.to_nat (φ j))) by lia.
      rewrite length_app.
      rewrite Hl.
      destruct (output_command _).
      * assert ((φ (acc + 1))%uint63 = (φ acc) + 1) by sia. lia.
      * lia.
    + pose proof (to_Z_bounded q). destruct (output_command _); [sia | lia].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hj.
    rewrite cmds_from_n by lia. simpl. lia.
Qed.

Lemma n_bound : Z.of_nat n <= 4194303.
Proof.
  assert (H0 : (φ (PArray.length ca)) <= 4194303) by exact (alength_bound machine_command ca).
  assert (H : Z.of_nat (List.length lines) = (φ (PArray.length@{Set} ca)))
    by (destruct Hca as [Hl _]; exact Hl).
  unfold n. lia.
Qed.

Lemma run_loop_spec : forall (q : int), (φ q) = Z.of_nat n ->
  forall z j T C O p H s, gap q j = z -> (φ j) <= (φ q) -> rel s T C (φ j) ->
  (φ p) + Z.of_nat (List.length (replay s (cmds_from (Z.to_nat (φ j)))))
    = (φ (PArray.length O)) ->
  PArray.length (run_loop ca q j T C O p H) = PArray.length O /\
  (forall i, (φ i) < (φ p) -> (run_loop ca q j T C O p H).[i] = O.[i]) /\
  (forall k, (k < List.length (replay s (cmds_from (Z.to_nat (φ j)))))%nat ->
     exists m, nth_error (replay s (cmds_from (Z.to_nat (φ j)))) k = Some m /\
        repr ((run_loop ca q j T C O p H).[of_Z ((φ p) + Z.of_nat k)]
               : option sint) m).
Proof.
  intros q Hq z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j T C O p H s Hz Hjq Hrel Hlen.
  pose proof (to_Z_bounded j) as Bj. pose proof (to_Z_bounded p) as Bp.
  pose proof n_bound as Hnb. pose proof (alength_bound (option int) O) as BO.
  rewrite run_loop_eq.
  destruct (bdec (j <? q)%uint63) as [Hj | Hj].
  - pose proof Hj as Hj'. rewrite ltb_spec in Hj'.
    assert (Hj1 : (φ (j + 1))%uint63 = (φ j) + 1) by sia.
    remember (Z.to_nat (φ j)) as k eqn:Ek.
    assert (Hk : (k < n)%nat) by lia.
    assert (Ej : Uint63.of_nat k = j) by (subst k; apply of_nat_phi).
    destruct (command_at k Hk) as [Hcmd [Hidb Hv']].
    rewrite Ej in Hcmd.
    pose proof (encode_repr _ _ Hcmd Hv') as Hf.
    destruct (encode_machine ca.[j]) as [[[idm opm] xm] ym] eqn:Em.
    destruct (encode_math (nth k lines (0%N, GetSize))) as [[[id op] x] y] eqn:Ec.
    destruct Hf as [Hid [Hop [Hin [Hx [Hy Ha]]]]].
    assert (Eid : fst (nth k lines (0%N, GetSize)) = id).
    { destruct (nth k lines (0%N, GetSize)) as [i oper].
      unfold encode_math in Ec. destruct (encode_operation _ _ oper) as [[co xx] yy].
      inversion Ec. reflexivity. }
    rewrite Eid in Hidb.
    rewrite cmds_from_S in Hlen |- * by exact Hk. cbn [replay] in Hlen |- *.
    unfold cmdf in Hlen |- *. rewrite Ec in Hlen |- *.
    destruct (Reference.step s (id, op, x, y)) as [s' o] eqn:Hs.
    match goal with |- context [exec ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8] =>
      destruct (exec a1 a2 a3 a4 a5 a6 a7 a8) as [[[T' C'] O'] p'] eqn:He end.
    destruct (exec_correct s T C O p (φ j) _ _ _ _
                 id op x y
                s' o T' C' O' p' Hrel ltac:(lia) Hid Hidb Hop Hin Hx Hy Ha Hs He)
      as [Hrel' Hout].
    rewrite <- Hj1 in Hrel'.
    assert (Ek1 : Z.to_nat (φ (j + 1))%uint63 = S k) by lia.
    rewrite length_app in Hlen.
    assert (Hlen' : (φ p') + Z.of_nat (List.length (replay s' (cmds_from (S k))))
                    = (φ (PArray.length O'))).
    { destruct Hout as [[-> [-> ->]] | (m & v & -> & Hr & -> & ->)].
      - simpl in Hlen. lia.
      - rewrite slength_set. simpl in Hlen.
        assert ((φ (p + 1))%uint63 = (φ p) + 1) by sia. lia. }
    rewrite <- Ek1 in Hlen'.
    destruct (IH (gap q (j + 1)%uint63) ltac:(rewrite <- Hz; apply dec_step; exact Hj)
                (j + 1)%uint63 T' C' O' p' (Acc_inv H (dec_step q j Hj)) s'
                eq_refl ltac:(lia) Hrel' Hlen') as [IH1 [IH2 IH3]].
    rewrite Ek1 in IH3.
    destruct Hout as [[-> [-> ->]] | (m & v & -> & Hr & -> & ->)].
    + split; [exact IH1|]. split; [exact IH2|]. exact IH3.
    + assert (Hp1 : (φ (p + 1))%uint63 = (φ p) + 1).
      { simpl in Hlen. sia. }
      assert (Hpl : (p <? PArray.length O)%uint63 = true)
        by (rewrite ltb_spec; simpl in Hlen; lia).
      split; [rewrite IH1; apply slength_set|].
      split.
      * intros i Hi. rewrite IH2 by lia. apply sget_set_other.
        intro E. subst i. lia.
      * intros [|k'] Hk'.
        -- exists m. split; [reflexivity|].
           rewrite Z.add_0_r, of_to_Z, IH2 by lia.
           rewrite sget_set_same by exact Hpl. exact Hr.
        -- simpl in Hk'. destruct (IH3 k' ltac:(lia)) as (m' & Hm' & Hr').
           exists m'. split; [exact Hm'|].
           replace ((φ p) + Z.of_nat (S k')) with ((φ (p + 1))%uint63 + Z.of_nat k') by lia.
           exact Hr'.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hj.
    rewrite cmds_from_n by lia. simpl.
    split; [reflexivity|]. split; [reflexivity|]. intros k Hk. lia.
Qed.

Lemma run_impl_reference :
  repr (run_impl ca) (replay init (cmds_from 0)).
Proof.
  pose proof n_bound as Hnb.
  set (q := PArray.length ca).
  assert (Hq : (φ q) = Z.of_nat n) by exact (repr_len ca lines Hca).
  set (cnt := count_loop ca q 0 0 (Zwf_well_founded 0 (gap q 0))).
  assert (Hcnt : (φ cnt) = Z.of_nat (List.length (replay init (cmds_from 0)))).
  { unfold cnt. rewrite (count_loop_spec q Hq _ 0%uint63 0%uint63 _ init eq_refl)
      by (change (φ 0)%uint63 with 0; lia).
    reflexivity. }
  pose proof (replay_len 0 init) as Hrl.
  assert (HO : PArray.length (PArray.make cnt (@None int)) = cnt).
  { rewrite slength_make.
    replace (cnt <=? PArray.max_length)%uint63 with true; [reflexivity|].
    symmetry. rewrite leb_spec. change (φ PArray.max_length) with 4194303. lia. }
  destruct (run_loop_spec q Hq _ 0%uint63 (PArray.make 1001 Leaf) (PArray.make 1001 None)
              (PArray.make cnt None) 0%uint63 (Zwf_well_founded 0 (gap q 0)) init
              eq_refl ltac:(change (φ 0)%uint63 with 0; lia) rel_init
              ltac:(rewrite HO, Hcnt; reflexivity))
    as [R1 [_ R3]].
  change (run_impl ca) with
    (run_loop ca q 0 (PArray.make 1001 Leaf) (PArray.make 1001 None)
       (PArray.make cnt None) 0 (Zwf_well_founded 0 (gap q 0))).
  split.
  - assert (HL : Z.of_nat (List.length (replay init (cmds_from 0)))
                 = (φ (PArray.length (run_loop ca q 0 (PArray.make 1001 Leaf)
                       (PArray.make 1001 None) (PArray.make cnt None) 0
                       (Zwf_well_founded 0 (gap q 0))))))
      by (rewrite R1, HO; symmetry; exact Hcnt).
    exact HL.
  - intros k Hk. destruct (R3 k Hk) as (m & Hm & Hr).
    exists m. split; [exact Hm | exact Hr].
Qed.

End Loops.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition run_commands :
  array machine_command -> array (option sint)
   := run_impl.
Elpi complexity run_commands.

(* ------------------------------------------------------------------ *)
(* Refinement of the private list model to the public map relation      *)
(* ------------------------------------------------------------------ *)

Definition contents (l : entries) : key_map := fun k => lookup k l.
Definition abstract_instance (i : inst) : instance :=
  MapInstance (contents (fst i)) (snd i).
Definition good_instance (i : inst) : Prop :=
  srt (fst i) /\
  match snd i with None => True | Some k => In k (map fst (fst i)) end.
Definition good_state (s : Reference.state) : Prop := forall id, good_instance (s id).
Definition state_refines (s : Reference.state) (a : Prelude.state) : Prop :=
  forall id, a id = abstract_instance (s id).

Lemma sorted_keys_nodup l : srt l -> NoDup (map fst l).
Proof.
  induction l as [|[k v] l IH]; simpl; intros H; [constructor|].
  destruct H as [Hg Hs]. constructor; [|auto].
  intros Hin. apply in_map_iff in Hin as [[k' v'] [E Hin]]. simpl in E; subst k'.
  apply (proj1 (Forall_forall _ _) Hg) in Hin. simpl in Hin. lia.
Qed.

Lemma lookup_member l k v : srt l -> (lookup k l = Some v <-> In (k,v) l).
Proof.
  induction l as [|[a b] l IH]; simpl; intros H; [unfold lookup; simpl; intuition discriminate|].
  destruct H as [Hg Hs]. unfold lookup at 1. simpl.
  destruct (a =? k)%Z eqn:E.
  - apply Z.eqb_eq in E; subst a. simpl. split.
    + intro H; inversion H; auto.
    + intros [H|H]; [inversion H; reflexivity|].
      apply (proj1 (Forall_forall _ _) Hg) in H. simpl in H. lia.
  - apply Z.eqb_neq in E. change (lookup k l = Some v <-> (a,b) = (k,v) \/ In (k,v) l).
    rewrite IH by exact Hs. split; [auto|]. intros [H|H]; [inversion H; contradiction|exact H].
Qed.

Lemma present_keys l k : srt l ->
  (present (contents l) k <-> In k (map fst l)).
Proof.
  intros Hs. unfold present, contents. split.
  - intros [v Hv]. apply lookup_member in Hv; [apply in_map with (f := fst) in Hv; exact Hv|auto].
  - intros Hin. apply in_map_iff in Hin as [[k' v] [E Hin]]. simpl in E; subst k'.
    exists v. apply lookup_member; auto.
Qed.

Lemma list_cardinality l p P : srt l -> (forall k, p k = true <-> P k) ->
  cardinality (contents l) P
    (Z.of_nat (List.length (filter (fun e => p (fst e)) l))).
Proof.
  intros Hs Hp. exists (map fst (filter (fun e => p (fst e)) l)).
  split; [apply sorted_keys_nodup, srt_filter; exact Hs|]. split; [|rewrite length_map; reflexivity].
  intros k. rewrite present_keys by exact Hs. split.
  - intros Hin. apply in_map_iff in Hin as [[a b] [E Hin]]. simpl in E; subst a.
    apply filter_In in Hin as [Hin Hpk]. split; [apply in_map with (f := fst) in Hin; exact Hin|apply Hp; exact Hpk].
  - intros [Hin Hpk]. apply in_map_iff in Hin as [[a b] [E Hin]]. simpl in E; subst a.
    apply in_map_iff. exists (k,b). split; [reflexivity|]. apply filter_In. split; auto. apply Hp; exact Hpk.
Qed.

Lemma all_cardinality l : srt l ->
  cardinality (contents l) (fun _ => True) (Z.of_nat (List.length l)).
Proof.
  intros Hs. pose proof (list_cardinality l (fun _ => true) (fun _ => True) Hs ltac:(intuition)) as H.
  change (filter (fun _ : Z * Z => true) l) with (filter (fun _ => true) l) in H.
  rewrite filter_all' in H by (apply Forall_forall; auto). exact H.
Qed.

Lemma rank_cardinality l k : srt l ->
  cardinality (contents l) (fun other => other < k) (rank k l).
Proof.
  intro Hs. exact (list_cardinality l (fun other => Z.ltb other k)
    (fun other => other < k) Hs (fun other => Z.ltb_lt other k)).
Qed.

Lemma cardinality_unique m P a b : cardinality m P a -> cardinality m P b -> a = b.
Proof.
  intros [ka [Na [Ha Ea]]] [kb [Nb [Hb Eb]]].
  assert (La : (List.length ka <= List.length kb)%nat).
  { apply NoDup_incl_length; auto. intros k Hk. apply Hb, Ha; exact Hk. }
  assert (Lb : (List.length kb <= List.length ka)%nat).
  { apply NoDup_incl_length; auto. intros k Hk. apply Ha, Hb; exact Hk. }
  lia.
Qed.

Lemma abstract_valid i : good_instance i -> instance_valid (abstract_instance i).
Proof.
  destruct i as [l c]. intros [Hs Hc]. split.
  - exists (Z.of_nat (List.length l)). apply all_cardinality; exact Hs.
  - destruct c; simpl in *; auto. apply present_keys; auto.
Qed.

Lemma first_some_split p l k : first_key p l = Some k ->
  exists a v b, l = a ++ (k,v) :: b /\ p k = true /\
    Forall (fun e => p (fst e) = false) a.
Proof.
  induction l as [|[x v] l IH]; simpl; [discriminate|].
  destruct (p x) eqn:E.
  - intro H; inversion H; subst x. exists [], v, l. simpl; auto.
  - intro H. destruct (IH H) as [a [w [b [El [Pk Pa]]]]].
    exists ((x,v)::a), w, b. simpl. split; [congruence|]. split; auto.
Qed.

Lemma first_none_all p l : first_key p l = None ->
  Forall (fun e => p (fst e) = false) l.
Proof.
  induction l as [|[x v] l IH]; simpl; [auto|].
  destruct (p x) eqn:E; [discriminate|]. intro H. constructor; auto.
Qed.

Lemma least_first l p P : srt l -> (forall k, p k = true <-> P k) ->
  least_key (contents l) P (first_key p l).
Proof.
  intros Hs Hp. destruct (first_key p l) as [k|] eqn:E.
  - destruct (first_some_split p l k E) as [a [v [b [El [Pk Pa]]]]]. subst l.
    pose proof (proj1 (srt_app a (k,v) b) Hs) as [_ [_ [Lt Gt]]].
    split; [apply present_keys; auto; apply in_map_iff; exists (k,v); split; [reflexivity|apply in_or_app; right; left; reflexivity]|].
    split; [apply Hp; exact Pk|]. intros other Hother Pother.
    apply present_keys in Hother; auto. apply in_map_iff in Hother as [[x w] [Ex Hin]]. simpl in Ex; subst x.
    apply in_app_or in Hin as [Hin|Hin].
    + pose proof (proj1 (Forall_forall _ _) Pa (other,w) Hin) as Hfalse.
      simpl in Hfalse. apply Hp in Pother. congruence.
    + destruct Hin as [Hin|Hin]; [inversion Hin; lia|].
      pose proof (proj1 (Forall_forall _ _) Gt (other,w) Hin). simpl in H. lia.
  - intros k Hk Pk. apply present_keys in Hk; auto.
    apply in_map_iff in Hk as [[x v] [Ex Hin]]. simpl in Ex; subst x.
    pose proof (proj1 (Forall_forall _ _) (first_none_all p l E) (k,v) Hin) as Hfalse.
    simpl in Hfalse. apply Hp in Pk. congruence.
Qed.

Lemma greatest_first l p P : srt l -> (forall k, p k = true <-> P k) ->
  greatest_key (contents l) P (first_key p (rev l)).
Proof.
  intros Hs Hp. destruct (first_key p (rev l)) as [k|] eqn:E.
  - destruct (first_some_split p (rev l) k E) as [a [v [b [El [Pk Pa]]]]].
    assert (El' : l = rev b ++ (k,v) :: rev a).
    { apply (f_equal (@rev (Z * Z))) in El. rewrite rev_involutive, rev_app_distr in El.
      simpl in El. rewrite <- app_assoc in El. exact El. }
    subst l. pose proof (proj1 (srt_app (rev b) (k,v) (rev a)) Hs) as [_ [_ [Lt Gt]]].
    split; [apply present_keys; auto; apply in_map_iff; exists (k,v); split; [reflexivity|apply in_or_app; right; left; reflexivity]|].
    split; [apply Hp; exact Pk|]. intros other Hother Pother.
    apply present_keys in Hother; auto. apply in_map_iff in Hother as [[x w] [Ex Hin]]. simpl in Ex; subst x.
    apply in_app_or in Hin as [Hin|Hin].
    + pose proof (proj1 (Forall_forall _ _) Lt (other,w) Hin). simpl in H. lia.
    + destruct Hin as [Hin|Hin]; [inversion Hin; lia|].
      apply in_rev in Hin.
      pose proof (proj1 (Forall_forall _ _) Pa (other,w) Hin) as Hfalse.
      simpl in Hfalse. apply Hp in Pother. congruence.
  - intros k Hk Pk. apply present_keys in Hk; auto.
    apply in_map_iff in Hk as [[x v] [Ex Hin]]. simpl in Ex; subst x.
    assert (Hin' : In (k,v) (rev l)) by (apply (proj1 (in_rev l (k,v))); exact Hin).
    pose proof (proj1 (Forall_forall _ _) (first_none_all p (rev l) E) (k,v) Hin') as Hfalse.
    simpl in Hfalse. apply Hp in Pk. congruence.
Qed.

Lemma rank_split a k v b : srt (a ++ (k,v) :: b) ->
  rank k (a ++ (k,v) :: b) = Z.of_nat (List.length a).
Proof.
  intros Hs. apply srt_app in Hs as [_ [_ [Lt Gt]]].
  unfold rank. rewrite filter_app. simpl. rewrite Z.ltb_irrefl.
  rewrite (filter_all' _ a), (filter_none' _ b).
  - rewrite app_nil_r. reflexivity.
  - eapply Forall_impl; [|exact Gt]. intros [x w] H; simpl in *.
    apply Z.ltb_ge; lia.
  - eapply Forall_impl; [|exact Lt]. intros [x w] H; simpl in *.
    apply Z.ltb_lt; exact H.
Qed.

Lemma kth_iff l index k : srt l ->
  (kth index l = Some k <-> present (contents l) k /\ rank k l = index).
Proof.
  intros Hs. split.
  - unfold kth. destruct (0 <=? index)%Z eqn:E; [apply Z.leb_le in E|discriminate].
    destruct (nth_error l (Z.to_nat index)) as [[key value]|] eqn:En; [|discriminate].
    simpl. intros H; inversion H; subst key.
    apply nth_error_split in En as [a [b [El La]]]. subst l.
    split.
    + apply present_keys; auto. apply in_map_iff. exists (k,value). split; [reflexivity|].
      apply in_or_app; right; left; reflexivity.
    + rewrite rank_split by exact Hs. rewrite La, Z2Nat.id; auto.
  - intros [Hk Hr]. apply present_keys in Hk; auto.
    apply in_map_iff in Hk as [[key value] [Ek Hin]]. simpl in Ek; subst key.
    apply in_split in Hin as [a [b El]]. subst l.
    rewrite rank_split in Hr by exact Hs. subst index.
    unfold kth. replace (0 <=? Z.of_nat (List.length a))%Z with true by (symmetry; apply Z.leb_le; lia).
    rewrite Nat2Z.id, nth_error_app2 by lia.
    rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma kth_select l index : srt l ->
  least_key (contents l)
    (fun k => cardinality (contents l) (fun other => other < k) index) (kth index l).
Proof.
  intros Hs. destruct (kth index l) as [k|] eqn:E.
  - apply kth_iff in E as [Hk Hr]; auto. split; auto. split.
    + rewrite <- Hr. apply rank_cardinality; exact Hs.
    + intros other Ho Hc.
      assert (Hrank : rank other l = index)
        by (eapply cardinality_unique; [apply rank_cardinality; exact Hs|exact Hc]).
      assert (Ek : kth index l = Some k) by (apply kth_iff; auto).
      assert (Eo : kth index l = Some other) by (apply kth_iff; auto).
      assert (k = other) by congruence. lia.
  - intros k Hk Hc.
    assert (Hr : rank k l = index)
      by (eapply cardinality_unique; [apply rank_cardinality; exact Hs|exact Hc]).
    assert (Ek : kth index l = Some k) by (apply kth_iff; auto). congruence.
Qed.

Lemma contents_changes l after key : srt l -> srt after ->
  (forall other value, other <> key -> (In (other,value) after <-> In (other,value) l)) ->
  changes_only (contents l) (contents after) key.
Proof.
  intros Hs Ha Hmembers other Hne. unfold contents.
  destruct (lookup other after) as [v|] eqn:Ea.
  - apply lookup_member in Ea; auto. apply Hmembers in Ea; auto.
    symmetry. apply lookup_member; auto.
  - destruct (lookup other l) as [v|] eqn:El; auto.
    apply lookup_member in El; auto. apply Hmembers in El; auto.
    apply (proj2 (lookup_member after other v Ha)) in El. congruence.
Qed.

Lemma insert_other l key value other old : other <> key ->
  (In (other,old) (insert key value l) <-> In (other,old) l).
Proof.
  intros Hne. induction l as [|[k v] l IH]; simpl.
  - intuition congruence.
  - destruct (key <? k)%Z; [simpl; intuition congruence|].
    destruct (key =? k)%Z; [simpl; tauto|]. simpl. rewrite IH. tauto.
Qed.

Lemma insert_new_member l key value : ~ In key (map fst l) ->
  In (key,value) (insert key value l).
Proof.
  induction l as [|[k v] l IH]; simpl; [auto|]. intros Hnot.
  destruct (key <? k)%Z; [simpl; auto|].
  destruct (key =? k)%Z eqn:E.
  - apply Z.eqb_eq in E; subst k. exfalso; apply Hnot; auto.
  - simpl. right. apply IH. tauto.
Qed.

Lemma insert_existing l key value : srt l -> present (contents l) key ->
  insert key value l = l.
Proof.
  induction l as [|[k v] l IH]; intros Hs Hkey.
  - apply present_keys in Hkey; auto. contradiction.
  - destruct Hs as [Hg Hs]. apply present_keys in Hkey; [|split; assumption]. simpl in Hkey |- *.
    destruct (key <? k)%Z eqn:E.
    + apply Z.ltb_lt in E. exfalso. destruct Hkey as [H|H]; [lia|].
      apply in_map_iff in H as [[a b] [Ea Hin]]. simpl in Ea; subst a.
      pose proof (proj1 (Forall_forall _ _) Hg (key,b) Hin). simpl in H. lia.
    + destruct (key =? k)%Z eqn:Ek; auto. f_equal. apply IH; auto.
      apply present_keys; auto. destruct Hkey as [H|H]; auto. apply Z.eqb_neq in Ek; lia.
Qed.

Lemma erase_other l key other value : other <> key ->
  (In (other,value) (erase key l) <-> In (other,value) l).
Proof.
  intro Hne. unfold erase. rewrite filter_In. simpl.
  rewrite Bool.negb_true_iff, Z.eqb_neq. tauto.
Qed.

Lemma erase_absent l key : srt l -> contents (erase key l) key = None.
Proof.
  intros Hs. unfold contents. destruct (lookup key (erase key l)) as [v|] eqn:E; auto.
  apply lookup_member in E; [|apply srt_filter; exact Hs].
  unfold erase in E. apply filter_In in E as [_ Hfalse]. simpl in Hfalse.
  rewrite Z.eqb_refl in Hfalse. discriminate.
Qed.

Lemma set_other l key value other old : other <> key ->
  (In (other,old) (set_value key value l) <-> In (other,old) l).
Proof.
  intros Hne. unfold set_value. rewrite in_map_iff. split.
  - intros [[k v] [E Hin]]. simpl in E. destruct (k =? key)%Z eqn:Ek.
    + apply Z.eqb_eq in Ek. inversion E; subst; congruence.
    + inversion E; subst; exact Hin.
  - intro Hin. exists (other,old). split; auto. simpl.
    rewrite (proj2 (Z.eqb_neq other key) Hne). reflexivity.
Qed.

Lemma set_present l key value : srt l -> present (contents l) key ->
  contents (set_value key value l) key = Some value.
Proof.
  intros Hs Hkey. apply present_keys in Hkey; auto.
  apply in_map_iff in Hkey as [[k v] [E Hin]]. simpl in E; subst k.
  unfold contents. apply lookup_member; [apply srt_set_value; exact Hs|].
  unfold set_value. apply in_map_iff. exists (key,v). split; auto. simpl. rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma selects_present op l old selected :
  selects op (contents l) old selected ->
  match selected with None => True | Some k => present (contents l) k end.
Proof.
  intros H. inversion H; subst; try destruct selected; simpl in *; tauto.
Qed.

Lemma selection_result op l c selected : srt l ->
  selects op (contents l) c selected ->
  good_instance (l,selected) /\
  action op (abstract_instance (l,c)) (abstract_instance (l,selected)) [].
Proof.
  intros Hs Hselect. split; [split; simpl; auto|apply ActSelect; exact Hselect].
  pose proof (selects_present _ _ _ _ Hselect) as Hpresent.
  destruct selected; simpl in *; auto. apply present_keys; auto.
Qed.

Definition local_action (op : operation N Z) (current : inst) : inst * list (option Z) :=
  let '(l,c) := current in
  match op with
  | CopyFrom _ => (current, [])
  | FindKey key => ((l, first_key (fun k => Z.eqb k key) l), [])
  | LowerBound key => ((l, first_key (fun k => Z.leb key k) l), [])
  | UpperBound key => ((l, first_key (fun k => Z.ltb key k) l), [])
  | Insert key value => ((insert key value l, Some key), [])
  | Erase => ((match c with None => l | Some key => erase key l end, None), [])
  | First => ((l, first_key (fun _ => true) l), [])
  | Last => ((l, first_key (fun _ => true) (rev l)), [])
  | NextKey => ((l, on_cursor c (fun key => first_key (fun k => Z.ltb key k) l)), [])
  | PreviousKey => ((l, on_cursor c (fun key => first_key (fun k => Z.ltb k key) (rev l))), [])
  | SelectRank index => ((l, kth index l), [])
  | GetRank => (current, [option_map (fun key => rank key l) c])
  | GetValue => (current, [on_cursor c (fun key => lookup key l)])
  | SetValue value => ((match c with None => l | Some key => set_value key value l end, c), [])
  | GetSize => (current, [Some (Z.of_nat (List.length l))])
  end.

Lemma local_refines op current :
  (match op with CopyFrom _ => False | _ => True end) ->
  good_instance current ->
  let '(after, output) := local_action op current in
  good_instance after /\ action op (abstract_instance current) (abstract_instance after) output.
Proof.
  destruct current as [l c]. intros Hnot [Hs Hc]. destruct op;
    cbn [local_action]; try contradiction.
  - apply selection_result; auto. apply SelectFind, least_first; auto. intros; apply Z.eqb_eq.
  - apply selection_result; auto. apply SelectLower, least_first; auto. intros; apply Z.leb_le.
  - apply selection_result; auto. apply SelectUpper, least_first; auto. intros; apply Z.ltb_lt.
  - destruct (lookup key l) as [existing|] eqn:E.
    + assert (Hp : present (contents l) key) by (exists existing; exact E).
      rewrite insert_existing by assumption. split; [split; simpl; auto; apply present_keys; auto|].
      apply ActInsertExisting with existing. exact E.
    + assert (Hnew : srt (insert key value l)) by (apply srt_insert; exact Hs).
      assert (Hp : contents (insert key value l) key = Some value).
      { unfold contents. apply lookup_member; auto. apply insert_new_member.
        intro Hin. apply (proj2 (present_keys l key Hs)) in Hin.
        destruct Hin as [v Ev]. unfold contents in Ev. congruence. }
      split.
      * split; simpl; auto. apply present_keys; auto. exists value; exact Hp.
      * apply ActInsertNew; auto. apply contents_changes; auto. intros; apply insert_other; auto.
  - destruct c as [key|]; simpl in *.
    + split; [split; simpl; auto; apply srt_filter; exact Hs|].
      apply ActErase; [apply erase_absent; auto|]. apply contents_changes; auto.
      * apply srt_filter; exact Hs.
      * intros; apply erase_other; auto.
    + split; [split; auto|apply ActEraseUnset].
  - apply selection_result; auto. apply SelectFirst, least_first; auto. intuition.
  - apply selection_result; auto. apply SelectLast, greatest_first; auto. intuition.
  - destruct c as [key|]; simpl in *; apply selection_result; auto.
    + apply SelectNext, least_first; auto. intros; apply Z.ltb_lt.
    + apply SelectNextUnset.
  - destruct c as [key|]; simpl in *; apply selection_result; auto.
    + apply SelectPrevious, greatest_first; auto. intros; apply Z.ltb_lt.
    + apply SelectPreviousUnset.
  - apply selection_result; auto. apply SelectIndex, kth_select; exact Hs.
  - split; [split; auto|]. destruct c; simpl; [apply ActRank, rank_cardinality; auto|apply ActRankUnset].
  - split; [split; auto|]. destruct c as [key|]; simpl in *; [|apply ActGetUnset].
    assert (Hp : present (contents l) key) by (apply present_keys; auto).
    destruct Hp as [value E]. unfold contents in E. rewrite E. apply ActGet; exact E.
  - destruct c as [key|]; simpl in *.
    + assert (Hp : present (contents l) key) by (apply present_keys; auto).
      pose proof (set_present l key value Hs Hp) as Hnew.
      split.
      * split; simpl; [apply srt_set_value; auto|].
        apply present_keys; [apply srt_set_value; auto|]. exists value; exact Hnew.
      * apply ActSet; auto. apply contents_changes; auto.
        -- apply srt_set_value; auto.
        -- intros; apply set_other; auto.
    + split; [split; auto|apply ActSetUnset].
  - split; [split; auto|]. apply ActSize, all_cardinality; exact Hs.
Qed.

Lemma reference_local s id op :
  (match op with CopyFrom _ => False | _ => True end) ->
  let '(after, output) := local_action op (s id) in
  let '(s', output') := Reference.step s (encode_math (id,op)) in
  output' = output /\ forall j,
    s' j = if N.eqb j id then after else s j.
Proof.
  intros Hnot. destruct op; try contradiction;
    cbn [encode_math encode_operation].
  all: repeat match goal with |- context [φ ?c] =>
    tryif is_var c then fail else
    let v := eval vm_compute in (φ c) in change (φ c) with v end.
  all: cbn [Z.to_N Reference.step local_action];
    destruct (s id) as [l c] eqn:E; cbn [fst snd]; split; [reflexivity|].
  all: intro j; try reflexivity.
  all: destruct (N.eqb j id) eqn:Ej; [|reflexivity];
    apply N.eqb_eq in Ej; subst j; exact E.
Qed.

Lemma reference_step_refines s a id op : good_state s -> state_refines s a ->
  let '(s', output) := Reference.step s (encode_math (id,op)) in
  exists a', good_state s' /\ state_refines s' a' /\
    Prelude.step a (id,op) a' output.
Proof.
  intros Hg Hr. destruct op.
  { cbn [encode_math encode_operation].
    change (Z.to_N (φ 97)) with 97%N.
    cbn [Reference.step]. rewrite N2Z.id.
    destruct (s id) as [l c] eqn:E. cbn [fst snd].
    exists (replace_instance a id (MapInstance (bindings (a source)) None)).
    split.
    + intro j. destruct (N.eqb j id) eqn:Ej; [|apply Hg].
      split; simpl; [exact (proj1 (Hg source))|exact I].
    + split.
      * intro j. unfold replace_instance. destruct (N.eqb j id) eqn:Ej; [|apply Hr].
        rewrite Hr. destruct (s source) as [sl sc]. reflexivity.
      * apply StepCopy. rewrite Hr. apply abstract_valid, Hg. }
  all: match goal with |- let '(_,_) := Reference.step ?s (encode_math (?id,?op)) in _ =>
    pose proof (local_refines op (s id) I (Hg id)) as Hl;
    pose proof (reference_local s id op I) as He;
    destruct (local_action op (s id)) as [after emitted] eqn:Ea;
    destruct (Reference.step s (encode_math (id,op))) as [s' emitted'] eqn:Es;
    destruct Hl as [Hgood Hact]; destruct He as [Eout Epoint]; subst emitted';
    exists (replace_instance a id (abstract_instance after)); split
    end.
  all: first
    [ solve [intro j; rewrite Epoint; destruct (N.eqb j id); [exact Hgood|apply Hg]]
    | split;
      [ intro j; unfold replace_instance; rewrite Epoint; destruct (N.eqb j id); [reflexivity|apply Hr]
      | apply StepAction; [rewrite Hr; apply abstract_valid, Hg|rewrite Hr; exact Hact|apply abstract_valid; exact Hgood] ] ].
Qed.

Lemma replay_refines lines s a : good_state s -> state_refines s a ->
  exists final, executes a lines final (replay s (map encode_math lines)).
Proof.
  revert s a. induction lines as [|[id op] rest IH]; intros s a Hg Hr; simpl.
  - exists a. constructor.
  - pose proof (reference_step_refines s a id op Hg Hr) as Hstep.
    destruct (Reference.step s (encode_math (id,op))) as [s' emitted] eqn:E.
    destruct Hstep as [a' [Hg' [Hr' Hstep]]].
    destruct (IH s' a' Hg' Hr') as [final Hrest].
    exists final. fold (encode_math (id,op)). rewrite E. econstructor; eauto.
Qed.

Lemma enumerate_list {A : Type} (l : list A) default :
  map (fun i => nth i l default) (seq 0 (List.length l)) = l.
Proof.
  induction l as [|x l IH]; simpl; auto. f_equal.
  rewrite <- (seq_shift (List.length l) 0), map_map. simpl. exact IH.
Qed.

Theorem run_commands_correct commands commands_arr :
  valid_input commands -> repr commands_arr commands ->
  exists output : list (option Z), repr (run_commands commands_arr) output /\
    run_commands_spec commands output.
Proof.
  intros Hv Ha.
  exists (replay Reference.init (map encode_math commands)). split.
  - unfold run_commands. pose proof (run_impl_reference commands commands_arr Hv Ha) as H.
    unfold cmds_from, cmdf in H. simpl in H. rewrite Nat.sub_0_r in H.
    rewrite <- map_map in H. rewrite enumerate_list in H. exact H.
  - unfold run_commands_spec. apply replay_refines.
    + intro id. split; simpl; auto.
    + intro id. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Cost: the bound run_commands_time                                   *)
(* ------------------------------------------------------------------ *)

(* The cost translations are next to each definition above (Elpi
   complexity, callee first; run_commands_cost is the line just above).
   Plan of the proof:
   - every tree operation costs at most a constant times the depth of
     its tree argument (find_t_time, ins_time, del_time, ...; append
     l r: the sum of the two depths), the balancing helpers a constant;
     the recursion of each translation is unfolded once with its fix
     set aside as an opaque G (set, cbn, fold, clearbody), so that the
     rewrites of cost_simpl never traverse the fix bodies;
   - exec costs at most 2000 * depth of the instance's tree + 500;
   - the trees of the instance array stay red-black with at most j
     nodes after j commands (inv, exec_inv: Okasaki insertion and
     Kahrs deletion preserve the red-black invariant, the proofs of
     Stdlib's MSetRBT redone on these trees), hence a depth at most
     2 log2 (j + 1) + 1 (inv_height);
   - run_loop costs at most D q = (2 log2 q + 1) * 2000 + 1000 per
     command, count_loop 60; run_commands_time with c1 = 5000,
     c2 = 1000. *)

(* The red-black invariant (Prop only) *)

Fixpoint height (t : tree) : nat :=
  match t with Leaf => 0 | Node _ l _ _ _ r => S (Nat.max (height l) (height r)) end.

(* ------------------------------------------------------------------ *)
(* Prop side: the red-black invariant, for the cost bound              *)
(* ------------------------------------------------------------------ *)

Definition notred (t : tree) : Prop :=
  match t with Node Red _ _ _ _ _ => False | _ => True end.
Definition isblack (t : tree) : Prop :=
  match t with Node Black _ _ _ _ _ => True | _ => False end.
Definition notblack (t : tree) : Prop :=
  match t with Node Black _ _ _ _ _ => False | _ => True end.

Inductive rbt : nat -> tree -> Prop :=
| RB_Leaf : rbt 0 Leaf
| RB_Rd n l k v s r :
    notred l -> notred r -> rbt n l -> rbt n r -> rbt n (Node Red l k v s r)
| RB_Bk n l k v s r : rbt n l -> rbt n r -> rbt (S n) (Node Black l k v s r).

Inductive rrt (n : nat) : tree -> Prop :=
| RR_Rd l k v s r : rbt n l -> rbt n r -> rrt n (Node Red l k v s r).

Inductive arbt (n : nat) (t : tree) : Prop :=
| ARB_RB : rbt n t -> arbt n t
| ARB_RR : rrt n t -> arbt n t.

#[local] Hint Constructors rbt rrt arbt : core.
#[local] Hint Extern 0 (notred _) => (exact I) : core.
#[local] Hint Extern 0 (notblack _) => (exact I) : core.
#[local] Hint Extern 0 (isblack _) => (exact I) : core.

Ltac invrb := repeat match goal with
  | H : False |- _ => destruct H
  | H : notred (Node Red _ _ _ _ _) |- _ => destruct H
  | H : isblack (Node Red _ _ _ _ _) |- _ => destruct H
  | H : isblack Leaf |- _ => destruct H
  | H : notblack (Node Black _ _ _ _ _) |- _ => destruct H
  | H : rbt _ Leaf |- _ => inversion H; subst; clear H
  | H : rbt _ (Node _ _ _ _ _ _) |- _ => inversion H; subst; clear H
  | H : rrt _ _ |- _ => inversion H; subst; clear H
  | H : arbt _ _ |- _ => destruct H
  end.

Ltac invrb0 := repeat match goal with
  | H : False |- _ => destruct H
  | H : notred (Node Red _ _ _ _ _) |- _ => destruct H
  | H : isblack (Node Red _ _ _ _ _) |- _ => destruct H
  | H : isblack Leaf |- _ => destruct H
  | H : notblack (Node Black _ _ _ _ _) |- _ => destruct H
  | H : rbt _ Leaf |- _ => inversion H; subst; clear H
  | H : rbt _ (Node _ _ _ _ _ _) |- _ => inversion H; subst; clear H
  | H : rrt _ _ |- _ => inversion H; subst; clear H
  end.

Ltac rbauto := unfold node, makeBlack; cbn [notred notblack isblack]; eauto 10.

Lemma rr_nrr_rb n l k v s r :
  rbt n l -> rbt n r -> notred l -> notred r -> rbt n (Node Red l k v s r).
Proof. auto. Qed.

Lemma arb_nr_rb n t : arbt n t -> notred t -> rbt n t.
Proof. intros H Hn; destruct H as [H|H]; [exact H|]; invrb. Qed.

Lemma makeBlack_rb n t : arbt n t -> exists m, rbt m (makeBlack t).
Proof.
  destruct t as [|[] l k v s r]; intros H.
  - exists 0%nat; auto.
  - exists (S n). invrb; rbauto.
  - exists n. invrb; rbauto.
Qed.

Lemma makeRed_rr n t : rbt (S n) t -> notred t -> rrt n (makeRed t).
Proof. destruct t as [|[] l k v s r]; intros H Hn; invrb; unfold makeRed; rbauto. Qed.

Ltac dtree t := destruct t as [|[] ? ? ? ? ?].

Ltac desm := repeat match goal with |- context [match ?t with _ => _ end] => is_var t; destruct t end.

Lemma lbal_rb n l k v r : arbt n l -> rbt n r -> rbt (S n) (lbal l k v r).
Proof. intros Hl Hr. unfold lbal. desm; invrb; rbauto. Qed.

Lemma rbal_rb n l k v r : rbt n l -> arbt n r -> rbt (S n) (rbal l k v r).
Proof. intros Hl Hr. unfold rbal. desm; invrb; rbauto. Qed.

Lemma rbal'_rb n l k v r : rbt n l -> arbt n r -> rbt (S n) (rbal' l k v r).
Proof. intros Hl Hr. unfold rbal'. desm; invrb; rbauto. Qed.

#[local] Hint Resolve lbal_rb rbal_rb rbal'_rb makeRed_rr arb_nr_rb : core.

Lemma lbalS_rb n l k v r :
  arbt n l -> rbt (S n) r -> notred r -> rbt (S n) (lbalS l k v r).
Proof. intros Hl Hr Hn. unfold lbalS. desm; invrb; rbauto. Qed.

Lemma lbalS_arb n l k v r :
  arbt n l -> rbt (S n) r -> arbt (S n) (lbalS l k v r).
Proof. intros Hl Hr. unfold lbalS. desm; invrb; rbauto. Qed.

Lemma rbalS_rb n l k v r :
  rbt (S n) l -> notred l -> arbt n r -> rbt (S n) (rbalS l k v r).
Proof. intros Hl Hn Hr. unfold rbalS. desm; invrb; rbauto. Qed.

Lemma rbalS_arb n l k v r :
  rbt (S n) l -> arbt n r -> arbt (S n) (rbalS l k v r).
Proof. intros Hl Hr. unfold rbalS. desm; invrb; rbauto. Qed.

#[local] Hint Resolve lbalS_rb lbalS_arb rbalS_rb rbalS_arb : core.

Lemma ins_rb x vx n t : rbt n t ->
  arbt n (ins x vx t) /\ (notred t -> rbt n (ins x vx t)).
Proof.
  induction 1 as [|n l k v s r Hnl Hnr Hl IHl Hr IHr|n l k v s r Hl IHl Hr IHr].
  - simpl. split; intros; rbauto.
  - simpl. destruct IHl as [IHl1 IHl2], IHr as [IHr1 IHr2].
    destruct (key_lt x k); [|destruct (x =? k)%uint63]; (split; [|intros Hf; destruct Hf]); unfold node; auto 6.
  - simpl. destruct IHl as [IHl1 IHl2], IHr as [IHr1 IHr2].
    destruct (key_lt x k); [|destruct (x =? k)%uint63]; split; intros; rbauto.
Qed.

Lemma insert_rb x vx t : (exists n, rbt n t) -> exists n, rbt n (insert_t x vx t).
Proof. intros [n H]. apply (makeBlack_rb n). apply ins_rb, H. Qed.

Lemma append_rb : forall l r n, rbt n l -> rbt n r ->
  arbt n (append l r) /\ (notred l -> notred r -> rbt n (append l r)).
Proof.
  induction l as [|lc ll IHll lx lv ls lr IHlr]; intros r n Hl Hr.
  - simpl. split; intros; auto.
  - induction r as [|rc rl IHrl rx rv rs rr IHrr].
    + simpl. split; intros; auto.
    + rewrite append_NN.
      destruct lc, rc.
      * (* Red Red *)
        invrb0. destruct (IHlr rl n) as [A B]; auto.
        specialize (B ltac:(auto) ltac:(auto)).
        remember (append lr rl) as m eqn:Em. clear Em.
        destruct m as [|[] a x vx s b]; invrb0; split; intros; invrb0; rbauto.
      * (* Red Black *)
        destruct (IHlr (Node Black rl rx rv rs rr) n) as [A B];
          [inversion Hl; assumption | exact Hr |].
        specialize (B ltac:(inversion Hl; assumption) I).
        split; intros; invrb0; rbauto.
      * (* Black Red *)
        invrb0. destruct IHrl as [A B]; auto.
        split; intros; invrb0; rbauto.
      * (* Black Black *)
        invrb0.
        match goal with H : rbt ?m lr |- _ => destruct (IHlr rl m) as [A B]; auto end.
        remember (append lr rl) as w eqn:Ew. clear Ew.
        destruct w as [|[] a x vx s b]; try (destruct A as [A|A]; inversion A; subst; clear A); invrb0; split; intros; rbauto.
Qed.

Lemma del_rb x t : forall n,
  (rbt (S n) t -> isblack t -> arbt n (del x t)) /\
  (rbt n t -> notblack t -> rbt n (del x t)).
Proof.
  induction t as [|c l IHl k v s r IHr]; intros n.
  - split; intros H1 H2; invrb0; simpl; auto.
  - split; intros H1 H2; destruct c; invrb0; simpl.
    + (* black root, rbt n l, rbt n r *)
      destruct (key_lt x k); [|destruct (x =? k)%uint63].
      * destruct l as [|[] ll lk lv ls lr].
        -- invrb0. apply ARB_RR. unfold node. constructor; simpl; auto.
        -- apply ARB_RR. unfold node. constructor; auto.
           apply (proj2 (IHl n)); auto.
        -- invrb0. apply lbalS_arb; auto.
           apply (proj1 (IHl _)); auto.
      * apply (append_rb l r n); auto.
      * destruct r as [|[] rl rk rv rs rr].
        -- invrb0. apply ARB_RR. unfold node. constructor; simpl; auto.
        -- apply ARB_RR. unfold node. constructor; auto.
           apply (proj2 (IHr n)); auto.
        -- invrb0. apply rbalS_arb; auto.
           apply (proj1 (IHr _)); auto.
    + (* red root *)
      destruct (key_lt x k); [|destruct (x =? k)%uint63].
      * destruct l as [|[] ll lk lv ls lr].
        -- invrb0. unfold node. simpl. auto.
        -- simpl in *. contradiction.
        -- invrb0. apply lbalS_rb; auto.
           apply (proj1 (IHl _)); auto.
      * apply (append_rb l r n); auto.
      * destruct r as [|[] rl rk rv rs rr].
        -- invrb0. unfold node. simpl. auto.
        -- simpl in *. contradiction.
        -- invrb0. apply rbalS_rb; auto.
           apply (proj1 (IHr _)); auto.
Qed.

Lemma delete_rb x t : (exists n, rbt n t) -> exists n, rbt n (delete_t x t).
Proof.
  intros [n H]. unfold delete_t.
  destruct t as [|[] l k v s r].
  - apply (makeBlack_rb n). left. apply (proj2 (del_rb x Leaf n)); auto.
  - apply (makeBlack_rb n). left. apply (proj2 (del_rb x _ n)); simpl; auto.
  - destruct n as [|n]; [inversion H|].
    apply (makeBlack_rb n). apply (proj1 (del_rb x _ n)); simpl; auto.
Qed.

Lemma setv_notred x w t : notred t -> notred (setv_t x w t).
Proof.
  destruct t as [|c l k v s r]; simpl; auto.
  destruct (key_lt x k); [|destruct (x =? k)%uint63]; exact (fun H => H).
Qed.

Lemma setv_rb x w n t : rbt n t -> rbt n (setv_t x w t).
Proof.
  induction 1; simpl; auto.
  - destruct (key_lt x k); [|destruct (x =? k)%uint63]; constructor; auto using setv_notred.
  - destruct (key_lt x k); [|destruct (x =? k)%uint63]; constructor; auto.
Qed.

(* the number of nodes, and the depth *)
Definition nodes (t : tree) : nat := List.length (elements t).

Lemma nodes_Node c l k v s r : nodes (Node c l k v s r) = (nodes l + S (nodes r))%nat.
Proof. unfold nodes. simpl. rewrite List.length_app. reflexivity. Qed.

Lemma nodes_node c l k v r : nodes (node c l k v r) = (nodes l + S (nodes r))%nat.
Proof. apply nodes_Node. Qed.

Lemma nodes_lbal l k v r : nodes (lbal l k v r) = (nodes l + S (nodes r))%nat.
Proof. unfold nodes. rewrite elements_lbal, List.length_app. reflexivity. Qed.
Lemma nodes_rbal l k v r : nodes (rbal l k v r) = (nodes l + S (nodes r))%nat.
Proof. unfold nodes. rewrite elements_rbal, List.length_app. reflexivity. Qed.
Lemma nodes_lbalS l k v r : nodes (lbalS l k v r) = (nodes l + S (nodes r))%nat.
Proof. unfold nodes. rewrite elements_lbalS, List.length_app. reflexivity. Qed.
Lemma nodes_rbalS l k v r : nodes (rbalS l k v r) = (nodes l + S (nodes r))%nat.
Proof. unfold nodes. rewrite elements_rbalS, List.length_app. reflexivity. Qed.
Lemma nodes_append l r : nodes (append l r) = (nodes l + nodes r)%nat.
Proof. unfold nodes. rewrite elements_append, List.length_app. reflexivity. Qed.
Lemma nodes_makeBlack t : nodes (makeBlack t) = nodes t.
Proof. unfold nodes. rewrite elements_makeBlack. reflexivity. Qed.

Lemma nodes_ins x vx t : (nodes (ins x vx t) <= S (nodes t))%nat.
Proof.
  induction t as [|c l IHl k v s r IHr]; [reflexivity|].
  simpl. destruct (key_lt x k); [|destruct (x =? k)%uint63]; [destruct c| |destruct c];
    rewrite ?nodes_node, ?nodes_lbal, ?nodes_rbal, ?nodes_Node; lia.
Qed.

Lemma nodes_insert_t x vx t : (nodes (insert_t x vx t) <= S (nodes t))%nat.
Proof. unfold insert_t. rewrite nodes_makeBlack. apply nodes_ins. Qed.

Lemma nodes_del x t : (nodes (del x t) <= nodes t)%nat.
Proof.
  induction t as [|c l IHl k v s r IHr]; [reflexivity|].
  simpl. destruct (key_lt x k); [|destruct (x =? k)%uint63].
  - destruct l as [|[] ? ? ? ? ?]; rewrite ?nodes_node, ?nodes_lbalS, ?nodes_Node in *; lia.
  - rewrite nodes_append, nodes_Node. lia.
  - destruct r as [|[] ? ? ? ? ?]; rewrite ?nodes_node, ?nodes_rbalS, ?nodes_Node in *; lia.
Qed.

Lemma nodes_delete_t x t : (nodes (delete_t x t) <= nodes t)%nat.
Proof. unfold delete_t. rewrite nodes_makeBlack. apply nodes_del. Qed.

Lemma nodes_setv x w t : nodes (setv_t x w t) = nodes t.
Proof.
  induction t as [|c l IHl k v s r IHr]; [reflexivity|].
  simpl. destruct (key_lt x k); [|destruct (x =? k)%uint63]; rewrite !nodes_Node; lia.
Qed.

Lemma height_rb n t : rbt n t -> (height t <= 2 * n + 1)%nat /\ (notred t -> (height t <= 2 * n)%nat).
Proof.
  induction 1 as [|n l k v s r Hnl Hnr Hl IHl Hr IHr|n l k v s r Hl IHl Hr IHr]; simpl.
  - lia.
  - destruct IHl as [_ A], IHr as [_ B]. specialize (A Hnl). specialize (B Hnr).
    split; [lia | intros []].
  - destruct IHl as [A _], IHr as [B _]. split; intros; lia.
Qed.

Lemma pow_nodes n t : rbt n t -> (2 ^ n <= S (nodes t))%nat.
Proof.
  induction 1; rewrite ?nodes_Node; simpl; lia.
Qed.

Lemma height_log t : (exists n, rbt n t) -> (height t <= 2 * Nat.log2 (S (nodes t)) + 1)%nat.
Proof.
  intros [n H]. destruct (height_rb n t H) as [A _].
  assert (n <= Nat.log2 (S (nodes t)))%nat.
  { rewrite <- (Nat.log2_pow2 n) by lia. apply Nat.log2_le_mono. apply pow_nodes, H. }
  lia.
Qed.

(* the trees of the instance array: red-black, at most b nodes each *)
Definition inv (b : nat) (T : array tree) : Prop :=
  forall i, (exists n, rbt n T.[i]) /\ (nodes T.[i] <= b)%nat.

Lemma inv_mono b b' T : (b <= b')%nat -> inv b T -> inv b' T.
Proof. intros Hb H i. destruct (H i) as [A B]. split; [exact A | lia]. Qed.

Lemma inv_set b T id v : inv b T -> (exists n, rbt n v) -> (nodes v <= b)%nat ->
  inv b T.[id <- v].
Proof.
  intros H Hv Hn i.
  destruct (id =? i)%uint63 eqn:Heq.
  1: apply Uint63.eqb_spec in Heq; subst i.
  2: assert (Hne : id <> i) by (intro; subst; rewrite Uint63.eqb_refl in Heq; discriminate).
  - destruct (id <? PArray.length T)%uint63 eqn:Hlt.
    + rewrite PArray.get_set_same; [auto | exact Hlt].
    + rewrite (PArray.get_out_of_bounds _ _ id).
      * rewrite PArray.default_set. rewrite <- (PArray.get_out_of_bounds _ T id). apply H.
        exact Hlt.
      * rewrite PArray.length_set. exact Hlt.
  - rewrite PArray.get_set_other; [apply H | exact Hne].
Qed.

Lemma inv_init : inv 0 (PArray.make 1001 Leaf).
Proof.
  intros i. rewrite PArray.get_make. split; [exists 0%nat; constructor | reflexivity].
Qed.

Lemma exec_inv b T C O p id op x y :
  inv b T -> inv (S b) (fst (fst (fst (exec T C O p id op x y)))).
Proof.
  intros H. pose proof (inv_mono b (S b) T ltac:(lia) H) as H'.
  unfold exec.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
    cbn [fst]; try exact H'.
  - apply inv_set; [exact H' | apply H | apply H'].
  - apply inv_set; [exact H' | apply insert_rb, H |].
    pose proof (nodes_insert_t x y T.[id]). pose proof (proj2 (H id)). lia.
  - destruct C.[id] as [c|].
    + apply inv_set; [exact H' | apply delete_rb, H |].
      pose proof (nodes_delete_t c T.[id]). pose proof (proj2 (H' id)). lia.
    + apply inv_set; [exact H' | apply H | apply H'].
  - destruct C.[id] as [c|].
    + apply inv_set; [exact H' | |].
      * destruct (proj1 (H id)) as [n Hn]. exists n. apply setv_rb, Hn.
      * rewrite nodes_setv. apply H'.
    + apply inv_set; [exact H' | apply H | apply H'].
Qed.

Lemma inv_height b T i : inv b T -> (height T.[i] <= 2 * Nat.log2 (S b) + 1)%nat.
Proof.
  intros H. destruct (H i) as [A B].
  pose proof (height_log _ A).
  assert (Nat.log2 (S (nodes T.[i])) <= Nat.log2 (S b))%nat by (apply Nat.log2_le_mono; lia).
  lia.
Qed.

From Stdlib Require Import ssreflect.

Lemma size_time t (tC : tree_cost stepsCM t) : (cost (size_cost stepsCM t tC) <= 3)%nat.
Proof. unfold size_cost. destruct tC; cost_simpl; lia. Qed.

Lemma key_lt_time1 a aC : (cost (key_lt_cost stepsCM a aC) = 0)%nat.
Proof. reflexivity. Qed.
Lemma key_lt_time a aC b bC : (cost (extract (key_lt_cost stepsCM a aC) b bC) <= 3)%nat.
Proof. unfold key_lt_cost. cost_simpl. lia. Qed.

(* restate a hypothesis about a recursive call with the goal's own term:
   the goal's cost term ending with the witness w *)
Ltac align_ih H w :=
  match type of H with (@cost _ _ <= ?B)%nat =>
    match goal with |- context [@cost ?T (?G w)] =>
       let H' := fresh "I" in pose proof (H : (@cost T (G w) <= B)%nat) as H'; clear H end end.

Ltac gen_bound T X L :=
  let Hc := fresh "Hc" in
  pose proof (L : (@cost T X <= _)%nat) as Hc;
  revert Hc; generalize (@cost T X); intros ? Hc.

Ltac gen_costs := repeat match goal with |- context [@cost ?T ?X] =>
  match X with
  | extract (key_lt_cost stepsCM ?a ?aC) ?b ?bC => gen_bound T X (key_lt_time a aC b bC)
  | key_lt_cost stepsCM ?a ?aC => change (@cost T X) with 0%nat
  end end.

Lemma find_t_time x xC t (tC : tree_cost stepsCM t) :
  (cost (extract (find_t_cost stepsCM x xC) t tC) <= height t * 20 + 5)%nat.
Proof.
  unfold find_t_cost. induction tC; cost_simpl. lia.
  simpl height. gen_costs.
  cost_destruct (ltsb x k); cost_simpl.
  - align_ih IHtC1 tC1. lia.
  - cost_destruct (x =? k)%uint63; cost_simpl. lia. align_ih IHtC2 tC2. lia.
Qed.

Lemma node_time c cC l lC k kC v vC r rC :
  (cost (extract (extract (extract (extract (node_cost stepsCM c cC) l lC) k kC) v vC) r rC) <= 20)%nat.
Proof.
  unfold node_cost. cost_simpl.
  pose proof (size_time l lC). pose proof (size_time r rC). lia.
Qed.

Lemma makeBlack_time t tC : (cost (makeBlack_cost stepsCM t tC) <= 3)%nat.
Proof. unfold makeBlack_cost. destruct tC; cost_simpl; lia. Qed.

Ltac head_const X :=
  lazymatch X with
  | extract ?Y _ _ => head_const Y
  | ?f stepsCM _ _ => is_const f
  end.
Ltac zero_partial := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch type of X with CostM (forall _, _) => head_const X; change (@cost T X) with 0%nat end end.

(* destruct the witness of a tree or colour variable the goal matches on *)
Ltac wdestr1 := match goal with
  | |- context [match ?t with _ => _ end] => is_var t;
      match goal with
      | w : tree_cost _ t |- _ => destruct w
      | w : color_cost _ t |- _ => destruct w
      end
  end.

Ltac gen_costs2 := repeat match goal with |- context [@cost ?T ?X] =>
  match X with
  | extract (key_lt_cost stepsCM ?a ?aC) ?b ?bC => gen_bound T X (key_lt_time a aC b bC)
  | extract (extract (extract (extract (node_cost stepsCM ?c ?cC) ?l ?lC) ?k ?kC) ?v ?vC) ?r ?rC =>
      gen_bound T X (node_time c cC l lC k kC v vC r rC)
  | size_cost stepsCM ?t ?tC => gen_bound T X (size_time t tC)
  | makeBlack_cost stepsCM ?t ?tC => gen_bound T X (makeBlack_time t tC)
  end end.

Ltac bdestr1 := match goal with
  | |- context [match ?b with _ => _ end] =>
      lazymatch type of b with bool => idtac end;
      lazymatch b with true => fail | false => fail | _ => idtac end;
      cost_destruct b
  end.

Ltac align_all := repeat match goal with
  | H : (@cost _ ?M <= _)%nat |- _ =>
      lazymatch M with
      | context [extract ?F ?t ?w] => align_ih H w
      | _ => fail
      end
  end.

Ltac fin := repeat (first [ progress zero_partial | progress gen_costs2
                          | wdestr1; cost_simpl | bdestr1; cost_simpl ]).

Ltac const_time := cost_simpl; repeat (wdestr1; cost_simpl); zero_partial; gen_costs2; lia.

Lemma lbal_time l lC k kC v vC r rC :
  (cost (extract (extract (extract (lbal_cost stepsCM l lC) k kC) v vC) r rC) <= 100)%nat.
Proof. unfold lbal_cost. const_time. Qed.

Lemma rbal_time l lC k kC v vC r rC :
  (cost (extract (extract (extract (rbal_cost stepsCM l lC) k kC) v vC) r rC) <= 100)%nat.
Proof. unfold rbal_cost. const_time. Qed.

Ltac gen_tree := repeat match goal with |- context [@cost ?T ?X] =>
  match X with
  | extract (extract (extract (lbal_cost stepsCM ?l ?lC) ?k ?kC) ?v ?vC) ?r ?rC =>
      gen_bound T X (lbal_time l lC k kC v vC r rC)
  | extract (extract (extract (rbal_cost stepsCM ?l ?lC) ?k ?kC) ?v ?vC) ?r ?rC =>
      gen_bound T X (rbal_time l lC k kC v vC r rC)
  end end.

Ltac fin2 := repeat (first [ progress zero_partial | progress gen_costs2 | progress gen_tree
                          | wdestr1; cost_simpl | bdestr1; cost_simpl ]).

Lemma height_node c l k v s r : height (Node c l k v s r) = S (Nat.max (height l) (height r)).
Proof. reflexivity. Qed.

Ltac cost_simpl_nofix :=
  cbn; cost_reduce; fold_cost; repeat (cost_rewrite; cost_reduce); cbn; fold_cost.

Ltac odestr1 := match goal with
  | |- context [match ?o with Some _ => _ | None => _ end] =>
      lazymatch type of o with option _ => idtac end;
      lazymatch o with Some _ => fail | None => fail | _ => idtac end;
      is_var o; match goal with w : option_cost _ _ _ o |- _ => destruct w end
  | |- context [match ?o with Some _ => _ | None => _ end] =>
      lazymatch type of o with option _ => idtac end;
      lazymatch o with Some _ => fail | None => fail | _ => idtac end;
      let E := fresh "E" in cost_destruct_witness o as [? ?|] eqn:E
  end.

Ltac fin3 := repeat (first [ progress zero_partial | progress gen_costs2 | progress gen_tree
                          | wdestr1; cost_simpl_nofix | bdestr1; cost_simpl_nofix
                          | odestr1; cost_simpl_nofix ]).

Ltac align_gen H w :=
  match type of H with (@cost _ _ <= ?B)%nat =>
    match goal with |- context [@cost ?T (?G w)] =>
       let Hc := fresh "Hc" in pose proof (H : (@cost T (G w) <= B)%nat) as Hc; clear H;
       revert Hc; generalize (@cost T (G w)); intros ? Hc end end.
Ltac align_IH := repeat match goal with H : (@cost _ (?F ?w) <= _)%nat |- _ =>
   lazymatch type of w with tree_cost _ _ => idtac end; align_gen H w end.

(* one-argument-before-the-tree recursion: set G to the fix *)
Ltac rec_case G := unfold G; cost_unfold_fix; try fold G; clearbody G; cost_simpl_nofix; fin3;
  align_IH.

Lemma ins_time x xC vx vxC t (tC : tree_cost stepsCM t) :
  (cost (extract (extract (ins_cost stepsCM x xC) vx vxC) t tC) <= height t * 150 + 30)%nat.
Proof.
  unfold ins_cost. cbn.
  match goal with |- context [?F x xC vx vxC t tC] => set (G := F) end.
  induction tC.
  { unfold G. cost_simpl. fin3. lia. }
  unfold G. cost_unfold_fix. fold G. clearbody G.
  cost_simpl_nofix. fin3.
  all: try align_ih IHtC1 tC1; try align_ih IHtC2 tC2; lia.
Qed.

Lemma insert_t_time x xC vx vxC t (tC : tree_cost stepsCM t) :
  (cost (extract (extract (insert_t_cost stepsCM x xC) vx vxC) t tC) <= height t * 150 + 40)%nat.
Proof.
  unfold insert_t_cost. cost_simpl. zero_partial.
  match goal with |- context [@cost ?T ?X] => match X with
    extract (extract (ins_cost stepsCM ?x ?xC) ?vx ?vxC) ?t ?tC => gen_bound T X (ins_time x xC vx vxC t tC) end end.
  gen_costs2. lia.
Qed.

Lemma makeRed_time t tC : (cost (makeRed_cost stepsCM t tC) <= 3)%nat.
Proof. unfold makeRed_cost. destruct tC; cost_simpl; lia. Qed.

Lemma rbal'_time l lC k kC v vC r rC :
  (cost (extract (extract (extract (rbal'_cost stepsCM l lC) k kC) v vC) r rC) <= 100)%nat.
Proof. unfold rbal'_cost. const_time. Qed.

Ltac gen_tree ::= repeat match goal with |- context [@cost ?T ?X] =>
  match X with
  | extract (extract (extract (lbal_cost stepsCM ?l ?lC) ?k ?kC) ?v ?vC) ?r ?rC =>
      gen_bound T X (lbal_time l lC k kC v vC r rC)
  | extract (extract (extract (rbal_cost stepsCM ?l ?lC) ?k ?kC) ?v ?vC) ?r ?rC =>
      gen_bound T X (rbal_time l lC k kC v vC r rC)
  | extract (extract (extract (rbal'_cost stepsCM ?l ?lC) ?k ?kC) ?v ?vC) ?r ?rC =>
      gen_bound T X (rbal'_time l lC k kC v vC r rC)
  | makeRed_cost stepsCM ?t ?tC => gen_bound T X (makeRed_time t tC)
  end end.

Lemma lbalS_time l lC k kC v vC r rC :
  (cost (extract (extract (extract (lbalS_cost stepsCM l lC) k kC) v vC) r rC) <= 300)%nat.
Proof. unfold lbalS_cost. cost_simpl. fin3. all: lia. Qed.

Lemma rbalS_time l lC k kC v vC r rC :
  (cost (extract (extract (extract (rbalS_cost stepsCM l lC) k kC) v vC) r rC) <= 300)%nat.
Proof. unfold rbalS_cost. cost_simpl. fin3. all: lia. Qed.

Ltac spec_IH := repeat match goal with
  | H : forall (a : int) (aC : int_cost _ a), _ |- context [@cost _ (?Gf ?a ?aC ?t ?w)] =>
      lazymatch type of H with context [w] => specialize (H a aC) end
  end.

Lemma lower_t_time x xC t (tC : tree_cost stepsCM t) :
  (cost (extract (lower_t_cost stepsCM x xC) t tC) <= height t * 30 + 10)%nat.
Proof.
  unfold lower_t_cost. cbn.
  match goal with |- context [?F x xC t tC] => set (G := F) end.
  induction tC; rec_case G; lia.
Qed.

Lemma upper_t_time x xC t (tC : tree_cost stepsCM t) :
  (cost (extract (upper_t_cost stepsCM x xC) t tC) <= height t * 30 + 10)%nat.
Proof.
  unfold upper_t_cost. cbn.
  match goal with |- context [?F x xC t tC] => set (G := F) end.
  induction tC; rec_case G; lia.
Qed.

Lemma pred_t_time x xC t (tC : tree_cost stepsCM t) :
  (cost (extract (pred_t_cost stepsCM x xC) t tC) <= height t * 30 + 10)%nat.
Proof.
  unfold pred_t_cost. cbn.
  match goal with |- context [?F x xC t tC] => set (G := F) end.
  induction tC; rec_case G; lia.
Qed.

Lemma front_t_time  t (tC : tree_cost stepsCM t) :
  (cost (front_t_cost stepsCM t tC) <= height t * 30 + 10)%nat.
Proof.
  unfold front_t_cost. cbn.
  match goal with |- context [?F  t tC] => set (G := F) end.
  induction tC; rec_case G; lia.
Qed.

Lemma back_t_time  t (tC : tree_cost stepsCM t) :
  (cost (back_t_cost stepsCM t tC) <= height t * 30 + 10)%nat.
Proof.
  unfold back_t_cost. cbn.
  match goal with |- context [?F  t tC] => set (G := F) end.
  induction tC; rec_case G; lia.
Qed.

Lemma kth_t_time n nC t (tC : tree_cost stepsCM t) :
  (cost (extract (kth_t_cost stepsCM n nC) t tC) <= height t * 30 + 10)%nat.
Proof.
  unfold kth_t_cost. cbn.
  match goal with |- context [?F n nC t tC] => set (G := F) end.
  revert n nC; induction tC; intros n nC.
  { rec_case G; lia. }
  unfold G; cost_unfold_fix; try fold G; clearbody G; cost_simpl_nofix; fin3.
  all: spec_IH; align_IH; lia.
Qed.

Lemma rank_t_time x xC t (tC : tree_cost stepsCM t) :
  (cost (extract (rank_t_cost stepsCM x xC) t tC) <= height t * 30 + 10)%nat.
Proof.
  unfold rank_t_cost. cbn.
  match goal with |- context [?F x xC t tC] => set (G := F) end.
  induction tC; rec_case G; lia.
Qed.

Lemma lookup_t_time x xC t (tC : tree_cost stepsCM t) :
  (cost (extract (lookup_t_cost stepsCM x xC) t tC) <= height t * 30 + 10)%nat.
Proof.
  unfold lookup_t_cost. cbn.
  match goal with |- context [?F x xC t tC] => set (G := F) end.
  induction tC; rec_case G; lia.
Qed.

Lemma setv_t_time x xC w wC t (tC : tree_cost stepsCM t) :
  (cost (extract (extract (setv_t_cost stepsCM x xC) w wC) t tC) <= height t * 30 + 10)%nat.
Proof.
  unfold setv_t_cost. cbn.
  match goal with |- context [?F x xC w wC t tC] => set (G := F) end.
  induction tC; rec_case G; lia.
Qed.

(* The original functions stay folded in the cost goals from here on (the
   types of the translations mention them): cbn would unfold them there. *)
Arguments append : simpl never.
Arguments del : simpl never.
Arguments node : simpl never.
Arguments lbalS : simpl never.
Arguments rbalS : simpl never.
Arguments size : simpl never.
Arguments exec : simpl never.
Arguments run_loop : simpl never.
Arguments count_loop : simpl never.

Ltac gen_tree ::= repeat match goal with |- context [@cost ?T ?X] =>
  match X with
  | extract (extract (extract (lbal_cost stepsCM ?l ?lC) ?k ?kC) ?v ?vC) ?r ?rC =>
      gen_bound T X (lbal_time l lC k kC v vC r rC)
  | extract (extract (extract (rbal_cost stepsCM ?l ?lC) ?k ?kC) ?v ?vC) ?r ?rC =>
      gen_bound T X (rbal_time l lC k kC v vC r rC)
  | extract (extract (extract (rbal'_cost stepsCM ?l ?lC) ?k ?kC) ?v ?vC) ?r ?rC =>
      gen_bound T X (rbal'_time l lC k kC v vC r rC)
  | extract (extract (extract (lbalS_cost stepsCM ?l ?lC) ?k ?kC) ?v ?vC) ?r ?rC =>
      gen_bound T X (lbalS_time l lC k kC v vC r rC)
  | extract (extract (extract (rbalS_cost stepsCM ?l ?lC) ?k ?kC) ?v ?vC) ?r ?rC =>
      gen_bound T X (rbalS_time l lC k kC v vC r rC)
  | makeRed_cost stepsCM ?t ?tC => gen_bound T X (makeRed_time t tC)
  end end.

Ltac tdestr1 := match goal with
  | |- context [match ?t with Leaf => _ | Node _ _ _ _ _ _ => _ end] =>
      lazymatch type of t with tree => idtac end;
      lazymatch t with Leaf => fail | Node _ _ _ _ _ _ => fail | _ => idtac end;
      assert_fails is_var t;
      let E := fresh "E" in cost_destruct_witness t as [|? ? ? ? ? ? ? ? ? ? ? ?] eqn:E
  end.

Ltac spec_IHt := repeat match goal with
  | H : forall (a : tree) (aC : tree_cost _ a), (@cost _ (extract ?M a aC) <= _)%nat
    |- context [@cost ?T (extract ?M ?b ?bC)] => gen_bound T (extract M b bC) (H b bC)
  end.

Ltac fin4 := repeat (first [ progress zero_partial | progress gen_costs2 | progress gen_tree
                          | progress spec_IHt | progress align_IH
                          | wdestr1; cost_simpl_nofix | bdestr1; cost_simpl_nofix
                          | tdestr1; cost_simpl_nofix ]).

Lemma append_time l lC r rC :
  (cost (extract (append_cost stepsCM l lC) r rC) <= (height l + height r) * 400 + 50)%nat.
Proof.
  unfold append_cost. cbn.
  match goal with |- context [extract (?F l lC) r rC] => set (G := F) end.
  assert (G1 : forall l lC, (cost (G l lC) <= 3)%nat).
  { intros l' lC'; destruct lC'; unfold G; cost_simpl_nofix; lia. }
  revert r rC; induction lC as [|c cC ll llC IHl k kC v vC s sC lr lrC IHr]; intros r rC.
  { unfold G; cost_simpl_nofix; lia. }
  unfold G. cbn. try fold G. clearbody G.
  match goal with |- context [@cost _ (?F r rC)] => set (H := F) end.
  induction rC as [|rc rcC rl rlC IHrl rk rkC rv rvC rs rsC rr rrC IHrr].
  { unfold H. cost_simpl_nofix. lia. }
  unfold H. cbn. try fold H. clearbody H.
  cost_simpl_nofix.
  repeat match goal with |- context [@cost ?T (G ?a ?aC)] => gen_bound T (G a aC) (G1 a aC) end.
  fin4;
  repeat match goal with |- context [@cost ?T (G ?a ?aC)] => gen_bound T (G a aC) (G1 a aC) end.
  all: cbn [height] in *; try lia.
Qed.

Lemma append_time1 l lC : (cost (append_cost stepsCM l lC) <= 3)%nat.
Proof. unfold append_cost. destruct lC; cost_simpl_nofix; lia. Qed.

Ltac gen_tree ::= repeat match goal with |- context [@cost ?T ?X] =>
  match X with
  | extract (extract (extract (lbal_cost stepsCM ?l ?lC) ?k ?kC) ?v ?vC) ?r ?rC =>
      gen_bound T X (lbal_time l lC k kC v vC r rC)
  | extract (extract (extract (rbal_cost stepsCM ?l ?lC) ?k ?kC) ?v ?vC) ?r ?rC =>
      gen_bound T X (rbal_time l lC k kC v vC r rC)
  | extract (extract (extract (rbal'_cost stepsCM ?l ?lC) ?k ?kC) ?v ?vC) ?r ?rC =>
      gen_bound T X (rbal'_time l lC k kC v vC r rC)
  | extract (extract (extract (lbalS_cost stepsCM ?l ?lC) ?k ?kC) ?v ?vC) ?r ?rC =>
      gen_bound T X (lbalS_time l lC k kC v vC r rC)
  | extract (extract (extract (rbalS_cost stepsCM ?l ?lC) ?k ?kC) ?v ?vC) ?r ?rC =>
      gen_bound T X (rbalS_time l lC k kC v vC r rC)
  | makeRed_cost stepsCM ?t ?tC => gen_bound T X (makeRed_time t tC)
  | extract (append_cost stepsCM ?l ?lC) ?r ?rC => gen_bound T X (append_time l lC r rC)
  | append_cost stepsCM ?l ?lC => gen_bound T X (append_time1 l lC)
  end end.

Lemma del_time x xC t (tC : tree_cost stepsCM t) :
  (cost (extract (del_cost stepsCM x xC) t tC) <= height t * 1000 + 100)%nat.
Proof.
  unfold del_cost. cbn.
  match goal with |- context [?F x xC t tC] => set (G := F) end.
  induction tC.
  { unfold G; cost_simpl_nofix; lia. }
  unfold G. cbn. try fold G. clearbody G.
  cost_simpl_nofix. fin4.
  all: cbn [height] in *; lia.
Qed.

Lemma delete_t_time x xC t (tC : tree_cost stepsCM t) :
  (cost (extract (delete_t_cost stepsCM x xC) t tC) <= height t * 1000 + 110)%nat.
Proof.
  unfold delete_t_cost. cost_simpl_nofix. zero_partial.
  match goal with |- context [@cost ?T ?X] => match X with
    extract (del_cost stepsCM ?x ?xC) ?t ?tC => gen_bound T X (del_time x xC t tC) end end.
  gen_costs2. lia.
Qed.

Lemma on_cur_time cur curC f fC B :
  (forall c cC, cost (fC c cC) <= B)%nat ->
  (cost (extract (on_cur_cost stepsCM cur curC) f fC) <= B + 5)%nat.
Proof.
  intros HB. unfold on_cur_cost. destruct curC; cost_simpl_nofix.
  - match goal with |- context [fC ?a ?b] => pose proof (HB a b) end. lia.
  - lia.
Qed.

Lemma is_out_time o oC : (cost (is_out_cost stepsCM o oC) <= 30)%nat.
Proof. unfold is_out_cost. cost_simpl_nofix. fin3. all: lia. Qed.

Lemma output_command_time line lineC :
  (cost (output_command_cost stepsCM line lineC) <= 5)%nat.
Proof.
  destruct lineC as [id idC op opC]. destruct opC;
    unfold output_command_cost; cost_simpl_nofix; lia.
Qed.

Lemma encode_machine_time line lineC :
  (cost (encode_machine_cost stepsCM line lineC) <= 20)%nat.
Proof.
  destruct lineC as [id idC op opC]. destruct opC;
    unfold encode_machine_cost, encode_operation_cost; cost_simpl_nofix; lia.
Qed.

Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; unfold bdec_cost; cost_simpl_nofix; lia. Qed.

Ltac gen_q :=
  repeat match goal with |- context [@cost ?T ?X] =>
  match X with
  | extract (find_t_cost stepsCM ?x ?xC) ?t ?tC => gen_bound T X (find_t_time x xC t tC)
  | extract (lower_t_cost stepsCM ?x ?xC) ?t ?tC => gen_bound T X (lower_t_time x xC t tC)
  | extract (upper_t_cost stepsCM ?x ?xC) ?t ?tC => gen_bound T X (upper_t_time x xC t tC)
  | extract (pred_t_cost stepsCM ?x ?xC) ?t ?tC => gen_bound T X (pred_t_time x xC t tC)
  | extract (kth_t_cost stepsCM ?x ?xC) ?t ?tC => gen_bound T X (kth_t_time x xC t tC)
  | extract (rank_t_cost stepsCM ?x ?xC) ?t ?tC => gen_bound T X (rank_t_time x xC t tC)
  | extract (lookup_t_cost stepsCM ?x ?xC) ?t ?tC => gen_bound T X (lookup_t_time x xC t tC)
  | extract (extract (setv_t_cost stepsCM ?x ?xC) ?w ?wC) ?t ?tC => gen_bound T X (setv_t_time x xC w wC t tC)
  | extract (extract (insert_t_cost stepsCM ?x ?xC) ?w ?wC) ?t ?tC => gen_bound T X (insert_t_time x xC w wC t tC)
  | extract (delete_t_cost stepsCM ?x ?xC) ?t ?tC => gen_bound T X (delete_t_time x xC t tC)
  | front_t_cost stepsCM ?t ?tC => gen_bound T X (front_t_time t tC)
  | back_t_cost stepsCM ?t ?tC => gen_bound T X (back_t_time t tC)
  | extract (extract (extract (set_cost stepsCM _ _) _ _) _ _) _ _ => change (@cost T X) with 1%nat
  end end.

Lemma exec_time T TC C CC O OC p pC id idC op opC x xC y yC :
  (cost (extract (extract (extract (extract (extract (extract (extract
     (exec_cost stepsCM T TC) C CC) O OC) p pC) id idC) op opC) x xC) y yC)
   <= height T.[id] * 2000 + 500)%nat.
Proof.
  unfold exec_cost, on_cur_cost. cost_simpl_nofix.
  generalize (array_elems CC id). generalize C.[id]. intros cur cw.
  repeat (first [ progress zero_partial | progress gen_costs2 | progress gen_q
                | bdestr1; cost_simpl_nofix | odestr1; cost_simpl_nofix ]).
  all: lia.
Qed.

Definition D (q : int) : nat := ((2 * Nat.log2 (Z.to_nat (φ q)) + 1) * 2000 + 1000)%nat.
Arguments D : simpl never.

Lemma run_loop_time commands commandsC q qC j jC T TC C CC O OC p pC H HC :
  inv (Z.to_nat (φ j)) T ->
  (cost (extract (extract (extract (extract (extract (extract (extract
     (run_loop_cost stepsCM commands commandsC) q qC) j jC) T TC) C CC) O OC) p pC) H HC)
   <= Z.to_nat (gap q j) * D q + 10)%nat.
Proof.
  unfold run_loop_cost. cbn.
  match goal with |- context [?F commands commandsC q qC j jC T TC C CC O OC p pC H HC] =>
    set (G := F) end.
  intros Hinv.
  enough (HG : forall k j jC T TC C CC O OC p pC H HC, (Z.to_nat (gap q j) <= k)%nat ->
    inv (Z.to_nat (φ j)) T ->
    (cost (G commands commandsC q qC j jC T TC C CC O OC p pC H HC)
     <= Z.to_nat (gap q j) * D q + 10)%nat) by (apply (HG (Z.to_nat (gap q j))); auto).
  clear j jC T TC C CC O OC p pC H HC Hinv.
  induction k as [|k IH]; intros j jC T TC C CC O OC p pC [g] HC Hk Hinv;
    unfold G; cbn; try fold G; cost_simpl_nofix;
    match goal with |- context [@cost ?Ty (bdec_cost stepsCM ?b ?w)] =>
      gen_bound Ty (bdec_cost stepsCM b w) (bdec_time b w) end;
    cost_destruct (bdec (j <? q)%uint63); cost_simpl_nofix.
  - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hk. lia.
  - lia.
  - zero_partial.
    match goal with |- context [@cost ?Ty (encode_machine_cost stepsCM ?line ?lineC)] =>
      gen_bound Ty (encode_machine_cost stepsCM line lineC) (encode_machine_time line lineC) end.
    cost_destruct_witness (encode_machine commands.[j]) as [a aC y yC] eqn:Em.
    cost_simpl_nofix.
    repeat (match goal with |- context [match ?v with pair _ _ => _ end] => is_var v;
       match goal with w : prod_cost _ _ _ _ _ v |- _ => destruct w end end; cost_simpl_nofix).
    match goal with |- context [@cost ?Ty ?X] => match X with
      extract (extract (extract (extract (extract (extract (extract (exec_cost stepsCM ?T ?TC) ?C ?CC) ?O ?OC) ?p ?pC) ?i ?iC) ?o ?oC) ?x ?xC) ?y ?yC =>
      gen_bound Ty X (exec_time T TC C CC O OC p pC i iC o oC x xC y yC) end end.
    match goal with |- context [exec_cost stepsCM _ _] => idtac end.
    match goal with |- context [extract (extract (extract (extract (extract (extract (extract
        (exec_cost stepsCM T TC) C CC) O OC) p pC) ?id ?idC) ?op ?opC) ?x ?xC) ?yy ?yyC] =>
      pose proof (exec_inv _ T C O p id op x yy Hinv) as Hinv';
      cost_destruct_witness (exec T C O p id op x yy) as [result resultC p' p'C] eqn:E
    end.
    cost_simpl_nofix.
    repeat (match goal with |- context [match ?v with pair _ _ => _ end] => is_var v;
       match goal with w : prod_cost _ _ _ _ _ v |- _ => destruct w end end; cost_simpl_nofix).
    cbn [fst] in Hinv'.
    assert (Hj1 : φ (j + 1)%uint63 = (φ j + 1)%Z).
    { pose proof (proj1 (Uint63.ltb_spec _ _) e). pose proof (Uint63.to_Z_bounded q).
      pose proof (Uint63.to_Z_bounded j).
      rewrite Uint63.add_spec. change (φ 1%uint63) with 1%Z. apply Z.mod_small. lia. }
    pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt.
    pose proof (Uint63.to_Z_bounded j) as Bj.
    assert (Hgap : Z.to_nat (gap q j) = S (Z.to_nat (gap q (j + 1)))).
    { unfold gap. rewrite Hj1. lia. }
    assert (Hk' : (Z.to_nat (gap q (j + 1)) <= k)%nat) by lia.
    assert (Hinv'' : inv (Z.to_nat (φ (j + 1)%uint63)) a0).
    { assert (Z.to_nat (φ j + 1) = S (Z.to_nat (φ j))) as X by lia.
      rewrite Hj1. rewrite X. exact Hinv'. }
    match goal with |- context [@cost ?Ty (G commands commandsC q qC ?j' ?jC' ?T' ?TC' ?C' ?CC' ?O' ?OC' ?p' ?pC' ?H' ?HC')] =>
      gen_bound Ty (G commands commandsC q qC j' jC' T' TC' C' CC' O' OC' p' pC' H' HC')
        (IH j' jC' T' TC' C' CC' O' OC' p' pC' H' HC' Hk' Hinv'') end.
    match type of Hc1 with context [height T.[?id]] =>
      pose proof (inv_height _ T id Hinv) as Hh end.
    assert (Hlog : (Nat.log2 (S (to_nat j)) <= Nat.log2 (Z.to_nat (φ q)))%nat).
    { apply Nat.log2_le_mono. change (to_nat j) with (Z.to_nat (φ j)). lia. }
    assert (HD : D q = ((2 * Nat.log2 (Z.to_nat (φ q)) + 1) * 2000 + 1000)%nat) by reflexivity.
    rewrite Hgap. rewrite Nat.mul_succ_l.
    clear Hj1 Hgap E.
    zero_partial.
    lia.
  - lia.
Qed.

Lemma count_loop_time ops opsC q qC j jC acc accC H HC :
  (cost (extract (extract (extract (extract (count_loop_cost stepsCM ops opsC) q qC) j jC) acc accC) H HC)
   <= Z.to_nat (gap q j) * 60 + 10)%nat.
Proof.
  unfold count_loop_cost. cbn.
  match goal with |- context [?F ops opsC q qC j jC acc accC H HC] => set (G := F) end.
  enough (HG : forall k j jC acc accC H HC, (Z.to_nat (gap q j) <= k)%nat ->
    (cost (G ops opsC q qC j jC acc accC H HC) <= Z.to_nat (gap q j) * 60 + 10)%nat)
    by (apply (HG (Z.to_nat (gap q j))); auto).
  clear j jC acc accC H HC.
  induction k as [|k IH]; intros j jC acc accC [g] HC Hk;
    unfold G; cbn; try fold G; cost_simpl_nofix;
    match goal with |- context [@cost ?Ty (bdec_cost stepsCM ?b ?w)] =>
      gen_bound Ty (bdec_cost stepsCM b w) (bdec_time b w) end;
    cost_destruct (bdec (j <? q)%uint63); cost_simpl_nofix.
  - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hk. lia.
  - lia.
  - zero_partial.
    match goal with |- context [@cost ?Ty (output_command_cost stepsCM ?o ?oC)] =>
      gen_bound Ty (output_command_cost stepsCM o oC) (output_command_time o oC) end.
    assert (Hj1 : φ (j + 1)%uint63 = (φ j + 1)%Z).
    { pose proof (proj1 (Uint63.ltb_spec _ _) e). pose proof (Uint63.to_Z_bounded q).
      pose proof (Uint63.to_Z_bounded j).
      rewrite Uint63.add_spec. change (φ 1%uint63) with 1%Z. apply Z.mod_small. lia. }
    pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt.
    pose proof (Uint63.to_Z_bounded j) as Bj.
    assert (Hgap : Z.to_nat (gap q j) = S (Z.to_nat (gap q (j + 1)))).
    { unfold gap. rewrite Hj1. lia. }
    assert (Hk' : (Z.to_nat (gap q (j + 1)) <= k)%nat) by lia.
    repeat (bdestr1; cost_simpl_nofix);
    match goal with |- context [@cost ?Ty (G ops opsC q qC ?j' ?jC' ?a' ?aC' ?H' ?HC')] =>
      gen_bound Ty (G ops opsC q qC j' jC' a' aC' H' HC') (IH j' jC' a' aC' H' HC' Hk') end;
    rewrite Hgap; clear Hj1 Hgap; lia.
  - lia.
Qed.

Theorem run_commands_time : exists c1 c2 : nat,
  forall (commands : list Prelude.command) (commands_arr : array machine_command),
  valid_input commands -> repr commands_arr commands ->
  run_commands_time_spec c1 c2 (Cost.size commands_arr) (cost1 run_commands_cost commands_arr).
Proof.
  exists 5000%nat, 1000%nat.
  intros commands a Hv Ha. unfold run_commands_time_spec.
  remember (5000 * ((Cost.size a + 1) * (Nat.log2 (Cost.size a) + 1)) + 1000)%nat as R eqn:HR.
  unfold cost1, run_commands_cost, run_impl_cost.
  cost_simpl_nofix. zero_partial.
  match goal with |- context [@cost ?Ty ?X] => match X with
    extract (extract (extract (extract (extract (extract (extract
     (run_loop_cost stepsCM ?i ?iC) ?q ?qC) ?j ?jC) ?T ?TC) ?C ?CC) ?O ?OC) ?p ?pC) ?H ?HC =>
     gen_bound Ty X (run_loop_time i iC q qC j jC T TC C CC O OC p pC H HC ltac:(exact inv_init)) end end.
  match goal with |- context [@cost ?Ty ?X] => match X with
    extract (extract (extract (extract (count_loop_cost stepsCM ?o ?oC) ?q ?qC) ?j ?jC) ?a ?aC) ?H ?HC =>
     gen_bound Ty X (count_loop_time o oC q qC j jC a aC H HC) end end.
  repeat match goal with |- context [@cost ?Ty ?X] => match X with
    | extract (extract (make_cost _ _ _) _ _) _ _ => change (@cost Ty X) with 1%nat end end.
  assert (Hq : Z.to_nat (gap (PArray.length a) 0) = Cost.size a).
  { unfold gap. change (φ 0%uint63) with 0%Z. rewrite Z.sub_0_r.
    reflexivity. }
  assert (HD : D (PArray.length a) = ((2 * Nat.log2 (Z.to_nat (φ (PArray.length a))) + 1) * 2000 + 1000)%nat) by reflexivity.
  assert (Hq' : Z.to_nat (φ (PArray.length a)) = Cost.size a).
  { rewrite <- Hq. unfold gap. change (φ 0%uint63) with 0%Z. rewrite Z.sub_0_r. reflexivity. }
  replace (Z.to_nat (gap (PArray.length a) 0)) with (Cost.size a) in Hc by (symmetry; exact Hq).
  replace (D (PArray.length a)) with
    ((2 * Nat.log2 (Cost.size a) + 1) * 2000 + 1000)%nat in Hc by reflexivity.
  replace (Z.to_nat (gap (PArray.length a) 0)) with (Cost.size a) in Hc0 by (symmetry; exact Hq).
  subst R. set (L := Nat.log2 (Cost.size a)) in *. set (m := Cost.size a) in *.
  clear - Hc Hc0. nia.
Qed.
