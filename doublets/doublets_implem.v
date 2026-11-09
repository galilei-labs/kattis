(* Executable implementation and its required termination dependencies.
   Correctness proofs are in doublets_proofs.v. *)
(* Implementation of doublets (doublets.spec), steering v2.

   Code.  [doublets xd xs xt] builds, once per call:
   - a word table: wl.[i] = length of word i, and a chained hash table on
     whole words (heads wb, links wn), used to find the index of a query's
     source and target words;
   - the wildcard-key index: entry e = 16 i + p stands for word i with
     position p masked (p < length of word i <= 16).  A chained hash table
     on the masked keys (heads bk, links bn; the key is hashed without being
     materialised and compared by [keq] at insertion, once) gives every
     entry a class id cls.[e], the first entry inserted with the same key;
     the entries of class c are chained from hd.[c] through cn.
   Then one BFS per query from its source word index, on int arrays only:
   distances (D, dist + 1, 0 = unvisited), parents P, queue Q, and a
   per-class mark M so that a class chain is walked at most once per query.
   No letter is read and no hash is computed during a search.  The chain is
   read back from the parent pointers into the dictionary's own strings.
   Chain pointers are stored + 1 (0 = end of chain).

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) _] proof (a gap to a bound, or a decreasing pointer). *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import String Ascii.
From Stdlib Require PrimString PString Sint63.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

Notation pstring := PrimString.string.

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

Lemma dec_ptr : forall a b : int, (a <? b) = true -> Zwf 0 (φ a) (φ b).
Proof.
  intros a b H. rewrite ltb_spec in H. pose proof (to_Z_bounded a).
  unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Hashing and comparing masked keys (build time only)                 *)
(* ------------------------------------------------------------------ *)

(* hash of x with position p masked, positions j .. len-1 still to go *)
Fixpoint hloop (x : pstring) (p len j h : int)
    (H : Acc (Zwf 0) (gap len j)) {struct H} : int :=
  match bdec (j <? len) with
  | left Hj =>
      hloop x p len (j + 1)
        (h * 31 + (if j =? p then 1 else PrimString.get x j + 2))
        (Acc_inv H (dec_step len j Hj))
  | right _ => h
  end.

Definition khash (m : int) (x : pstring) (p : int) : int :=
  let len := PrimString.length x in
  (hloop x p len 0 7 (Zwf_well_founded 0 (gap len 0))) mod m.

(* x and y agree at every position j .. len-1 other than p *)
Fixpoint kloop (x y : pstring) (p len j : int)
    (H : Acc (Zwf 0) (gap len j)) {struct H} : bool :=
  match bdec (j <? len) with
  | left Hj =>
      if orb (j =? p) (PrimString.get x j =? PrimString.get y j)
      then kloop x y p len (j + 1) (Acc_inv H (dec_step len j Hj))
      else false
  | right _ => true
  end.

Definition keq (x y : pstring) (p : int) : bool :=
  let len := PrimString.length x in
  if len =? PrimString.length y
  then kloop x y p len 0 (Zwf_well_founded 0 (gap len 0))
  else false.

(* ------------------------------------------------------------------ *)
(* Chained hash tables: walking a chain                                *)
(* ------------------------------------------------------------------ *)

(* the first pointer of the chain from ptr whose entry passes test, or 0 *)
Fixpoint find (nx : array int) (test : int -> bool) (ptr : int)
    (H : Acc (Zwf 0) (φ ptr)) {struct H} : int :=
  if ptr =? 0 then 0
  else if test (ptr - 1) then ptr
  else match bdec (nx.[ptr - 1] <? ptr) with
       | left Hl => find nx test nx.[ptr - 1] (Acc_inv H (dec_ptr _ _ Hl))
       | right _ => 0
       end.

Definition M_key : int := 1048576.
Definition M_word : int := 65536.

(* ------------------------------------------------------------------ *)
(* The word table                                                      *)
(* ------------------------------------------------------------------ *)

Fixpoint wbuild (xd : array pstring) (n i : int) (wl wb wn : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H}
    : array int * array int * array int :=
  match bdec (i <? n) with
  | left Hi =>
      let w := xd.[i] in
      let h := khash M_word w (PrimString.length w) in
      let old := wb.[h] in
      wbuild xd n (i + 1) wl.[i <- PrimString.length w] wb.[h <- i + 1]
        wn.[i <- old] (Acc_inv H (dec_step n i Hi))
  | right _ => (wl, wb, wn)
  end.

Definition wtest (xd : array pstring) (q : pstring) (y : int) : bool :=
  match PrimString.compare xd.[y] q with Eq => true | _ => false end.

(* the index of q in the dictionary, + 1, or 0 *)
Definition lookup (xd : array pstring) (wb wn : array int) (q : pstring) : int :=
  let h := khash M_word q (PrimString.length q) in
  let ptr := wb.[h] in
  find wn (wtest xd q) ptr (Zwf_well_founded 0 (φ ptr)).

(* ------------------------------------------------------------------ *)
(* The wildcard-key classes                                            *)
(* ------------------------------------------------------------------ *)

Definition ktest (xd : array pstring) (w : pstring) (p : int) (y : int) : bool :=
  andb (y mod 16 =? p) (keq xd.[y >> 4] w p).

Fixpoint build (xd : array pstring) (N16 e : int) (cls bk bn hd cn : array int)
    (H : Acc (Zwf 0) (gap N16 e)) {struct H}
    : array int * array int * array int :=
  match bdec (e <? N16) with
  | left He =>
      let w := xd.[e >> 4] in
      let p := e mod 16 in
      if p <? PrimString.length w then
        let h := khash M_key w p in
        let old := bk.[h] in
        let r := find bn (ktest xd w p) old (Zwf_well_founded 0 (φ old)) in
        let c := if r =? 0 then e else cls.[r - 1] in
        let oldc := hd.[c] in
        build xd N16 (e + 1) cls.[e <- c] bk.[h <- e + 1] bn.[e <- old]
          hd.[c <- e + 1] cn.[e <- oldc] (Acc_inv H (dec_step N16 e He))
      else build xd N16 (e + 1) cls bk bn hd cn (Acc_inv H (dec_step N16 e He))
  | right _ => (cls, hd, cn)
  end.

(* ------------------------------------------------------------------ *)
(* The search                                                          *)
(* ------------------------------------------------------------------ *)

(* the search state: distances + 1, parents, queue, queue tail, class marks.
   A tuple behind a notation, not a record nor a type definition: the
   classic extraction prints a declared type's array fields malformed. *)
Notation bst := (array int * array int * array int * int * array int)%type.
Definition mkb (D P Q : array int) (T : int) (M : array int) : bst := (D, P, Q, T, M).
Definition sD (s : bst) : array int := let '(D, _, _, _, _) := s in D.
Definition sP (s : bst) : array int := let '(_, P, _, _, _) := s in P.
Definition sQ (s : bst) : array int := let '(_, _, Q, _, _) := s in Q.
Definition sT (s : bst) : int := let '(_, _, _, T, _) := s in T.
Definition sM (s : bst) : array int := let '(_, _, _, _, M) := s in M.

(* visit the words of the class chain from ptr, from node u (D.[u] = du) *)
Fixpoint cwalk (cn : array int) (u du ptr : int) (s : bst)
    (H : Acc (Zwf 0) (φ ptr)) {struct H} : bst :=
  if ptr =? 0 then s
  else
    let e := ptr - 1 in
    let v := e >> 4 in
    let s' := if (sD s).[v] =? 0
              then mkb (sD s).[v <- du + 1] (sP s).[v <- u]
                       (sQ s).[sT s <- v] (sT s + 1) (sM s)
              else s in
    match bdec (cn.[e] <? ptr) with
    | left Hl => cwalk cn u du cn.[e] s' (Acc_inv H (dec_ptr _ _ Hl))
    | right _ => s'
    end.

(* the classes of the entries base + p, p < len, of node u *)
Fixpoint ploop (cls hd cn : array int) (u du base len p : int) (s : bst)
    (H : Acc (Zwf 0) (gap len p)) {struct H} : bst :=
  match bdec (p <? len) with
  | left Hp =>
      let c := cls.[base + p] in
      if (sM s).[c] =? 0 then
        let s1 := cwalk cn u du hd.[c] s (Zwf_well_founded 0 (φ (hd.[c]))) in
        ploop cls hd cn u du base len (p + 1)
          (mkb (sD s1) (sP s1) (sQ s1) (sT s1) (sM s1).[c <- 1])
          (Acc_inv H (dec_step len p Hp))
      else ploop cls hd cn u du base len (p + 1) s
             (Acc_inv H (dec_step len p Hp))
  | right _ => s
  end.

Fixpoint bfs (cls hd cn wl : array int) (n qh : int) (s : bst)
    (H : Acc (Zwf 0) (gap n qh)) {struct H} : bst :=
  match bdec (qh <? n) with
  | left Hq =>
      if qh <? sT s then
        let u := (sQ s).[qh] in
        let len := wl.[u] in
        let s' := ploop cls hd cn u (sD s).[u] (u * 16) len 0 s
                    (Zwf_well_founded 0 (gap len 0)) in
        bfs cls hd cn wl n (qh + 1) s' (Acc_inv H (dec_step n qh Hq))
      else s
  | right _ => s
  end.

Definition bfs_from (cls hd cn wl : array int) (n N16 s0 : int) : bst :=
  bfs cls hd cn wl n 0
    (mkb (PArray.make n 0).[s0 <- 1] (PArray.make n 0)
         (PArray.make n 0).[0 <- s0] 1 (PArray.make N16 0))
    (Zwf_well_founded 0 (gap n 0)).

(* cells 0 .. D.[v] - 1 of out receive the chain from the source to v *)
Fixpoint recon (xd : array pstring) (D P : array int) (v : int)
    (out : array pstring) (H : Acc (Zwf 0) (φ (D.[v]))) {struct H}
    : array pstring :=
  let out' := out.[D.[v] - 1 <- xd.[v]] in
  if D.[v] <=? 1 then out'
  else match bdec (D.[P.[v]] <? D.[v]) with
       | left Hl => recon xd D P P.[v] out' (Acc_inv H (dec_ptr _ _ Hl))
       | right _ => out'
       end.

(* the answer for a source of index s0 and a target tgt other than its word *)
Definition answer2 (xd : array pstring) (n N16 : int)
    (cls hd cn wl wb wn : array int) (s0 : int) (tgt : pstring)
    : option (array pstring) :=
  let rt := lookup xd wb wn tgt in
  if rt =? 0 then None
  else
    let t := rt - 1 in
    let st := bfs_from cls hd cn wl n N16 s0 in
    let dt := (sD st).[t] in
    if dt =? 0 then None
    else Some (recon xd (sD st) (sP st) t (PArray.make dt xd.[t])
                 (Zwf_well_founded 0 (φ ((sD st).[t])))).

Definition answer1 (xd : array pstring) (n N16 : int)
    (cls hd cn wl wb wn : array int) (src tgt : pstring)
    : option (array pstring) :=
  let rs := lookup xd wb wn src in
  if rs =? 0 then None
  else
    let s0 := rs - 1 in
    match PrimString.compare src tgt with
    | Eq => Some (PArray.make 1 xd.[s0])
    | _ => answer2 xd n N16 cls hd cn wl wb wn s0 tgt
    end.

Fixpoint qloop (xd xs xt : array pstring) (n N16 : int)
    (cls hd cn wl wb wn : array int) (nq q : int)
    (out : array (option (array pstring)))
    (H : Acc (Zwf 0) (gap nq q)) {struct H} : array (option (array pstring)) :=
  match bdec (q <? nq) with
  | left Hq =>
      qloop xd xs xt n N16 cls hd cn wl wb wn nq (q + 1)
        out.[q <- answer1 xd n N16 cls hd cn wl wb wn xs.[q] xt.[q]]
        (Acc_inv H (dec_step nq q Hq))
  | right _ => out
  end.

Definition doublets_impl (xd xs xt : array pstring)
    : array (option (array pstring)) :=
  let n := PArray.length xd in
  let N16 := n * 16 in
  let '(wl, wb, wn) :=
    wbuild xd n 0 (PArray.make n 0) (PArray.make M_word 0) (PArray.make n 0)
      (Zwf_well_founded 0 (gap n 0)) in
  let '(cls, hd, cn) :=
    build xd N16 0 (PArray.make N16 0) (PArray.make M_key 0)
      (PArray.make N16 0) (PArray.make N16 0) (PArray.make N16 0)
      (Zwf_well_founded 0 (gap N16 0)) in
  let nq := PArray.length xs in
  qloop xd xs xt n N16 cls hd cn wl wb wn nq 0 (PArray.make nq None)
    (Zwf_well_founded 0 (gap nq 0)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition doublets :
  array PrimString.string -> array PrimString.string ->
  array PrimString.string -> array (option (array PrimString.string))
  := doublets_impl.
