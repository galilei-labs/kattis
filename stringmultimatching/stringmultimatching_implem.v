(* Executable implementation and its required termination dependencies.
   Correctness proofs are in stringmultimatching_proofs.v. *)
(* Implementation of stringmultimatching (stringmultimatching.spec):
   Aho-Corasick, one automaton for all the patterns.

   Code.
   - [sums]: total length P and maximum length L of the patterns.
   - The trie is built LEVEL BY LEVEL ([rounds] / [round_loop]): at depth d
     every pattern still longer than d (the active list, compacted in place
     in one array) moves one character down from its current node,
     creating the child if absent.  Nodes are therefore numbered in
     breadth-first order (depth non-decreasing with the index).  Sparse
     transitions: the children of a node are a linked list (first child
     tfc, next sibling tns, edge character tchr), all flat [array int]s of
     size P+1; node 0 is the root.
   - [plist_loop]: the patterns ending at each node, as a linked list
     (fp / np, pattern numbers plus one, 0 ends a list) -- duplicate
     patterns share a node.
   - [fail_loop]: failure and output (dictionary-suffix) links, nodes in
     index order (= breadth-first order), by the failure walk [walk].
   - [scan]: the single left-to-right pass over the text, read through
     PrimString.get; at each position the output chain is walked and every
     pattern of every node on it is reported.  [scan] is generic in the
     action; it runs twice: [f_cnt] counts the occurrences of each pattern,
     then the rows are allocated at their exact sizes ([alloc_loop]) and
     [f_fill] writes the positions in place.  All arrays threaded linearly.
   Termination: every loop recurses on an erased [Acc (Zwf 0)] proof of a
   Z measure (an index gap, or the node / list element itself, which
   decreases along tns, np, failure and output links -- checked at run
   time, proven never to fail).

   Proof.  A ghost word W v for every node; [TrieInv] (prefix-closed,
   injective, depth monotone in the index, child lists = children);
   [FailOK] / [OutOK] for the links; [Longest]: the state after a text
   prefix X is the deepest node whose word is a suffix of X; the per-pattern
   lists of reported positions are abstracted by a relation R in
   [scan_spec], instantiated by [Rcnt] and [Rfill]. *)

From Stringmultimatching.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require PrimString String Ascii.
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

Lemma dec_lt : forall x y : int, (y <? x) = true -> Zwf 0 (φ y) (φ x).
Proof.
  intros x y H. rewrite ltb_spec in H. pose proof (to_Z_bounded y). unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* The trie: node 0 is the root, nodes 1 .. tn-1 the others.  A node v
   > 0 has its parent tpar.[v], the character tchr.[v] of the edge from
   its parent, its depth tdep.[v]; the children of a node u form a linked
   list tfc.[u], tns.[tfc.[u]], ... ended by 0 (the root is nobody's
   child). *)
Record trie := mkT {
  tchr : array int; tpar : array int; tfc : array int; tns : array int;
  tdep : array int; tn : int }.

(* The child of u along c in the sibling list starting at v, or 0. *)
Fixpoint lookup_from (chr ns : array int) (c v : int)
    (H : Acc (Zwf 0) (φ v)) {struct H} : int :=
  match bdec (v =? 0) with
  | left _ => 0
  | right _ =>
      if chr.[v] =? c then v else
      let nx := ns.[v] in
      match bdec (nx <? v) with
      | left Hn => lookup_from chr ns c nx (Acc_inv H (dec_lt v nx Hn))
      | right _ => 0
      end
  end.

Definition lookup (t : trie) (u c : int) : int :=
  let v := (tfc t).[u] in
  lookup_from (tchr t) (tns t) c v (Zwf_well_founded 0 (φ v)).

(* The child of u along c, created if absent. *)
Definition add_child (t : trie) (u c : int) : trie * int :=
  let v := lookup t u c in
  if v =? 0 then
    let n := tn t in
    let old := (tfc t).[u] in
    let du := (tdep t).[u] in
    (mkT (tchr t).[n <- c] (tpar t).[n <- u] (tfc t).[u <- n]
         (tns t).[n <- old] (tdep t).[n <- du + 1] (n + 1), n)
  else (t, v).

(* The construction state: the active patterns act.[0 .. bw-1] (those
   still longer than the current depth), the current node of every
   pattern, the trie. *)
Record bstate := mkB { bact : array int; bcur : array int; bw : int; bt : trie }.

(* One round, at depth d: every active pattern act.[k], k = k .. na-1,
   moves one character down the trie; the patterns that go on are
   compacted into act.[0 .. bw-1]. *)
Fixpoint round_loop (pats : array PrimString.string) (d na k : int)
    (st : bstate) (H : Acc (Zwf 0) (gap na k)) {struct H} : bstate :=
  match bdec (k <? na) with
  | left Hk =>
      let act := bact st in
      let i := act.[k] in
      let s := pats.[i] in
      let cur := bcur st in
      let tv := add_child (bt st) cur.[i] (PrimString.get s d) in
      let cur' := cur.[i <- snd tv] in
      let w := bw st in
      if d + 1 <? PrimString.length s then
        round_loop pats d na (k + 1) (mkB act.[w <- i] cur' (w + 1) (fst tv))
          (Acc_inv H (dec_step na k Hk))
      else
        round_loop pats d na (k + 1) (mkB act cur' w (fst tv))
          (Acc_inv H (dec_step na k Hk))
  | right _ => st
  end.

(* Rounds d, d+1, .., L-1. *)
Fixpoint rounds (pats : array PrimString.string) (L d : int) (st : bstate)
    (H : Acc (Zwf 0) (gap L d)) {struct H} : bstate :=
  match bdec (d <? L) with
  | left Hd =>
      let st' := round_loop pats d (bw st) 0 (mkB (bact st) (bcur st) 0 (bt st))
                   (Zwf_well_founded 0 (gap (bw st) 0)) in
      rounds pats L (d + 1) st' (Acc_inv H (dec_step L d Hd))
  | right _ => st
  end.

(* The total and the maximum length of the patterns i .. m-1. *)
Fixpoint sums (pats : array PrimString.string) (m i P L : int)
    (H : Acc (Zwf 0) (gap m i)) {struct H} : int * int :=
  match bdec (i <? m) with
  | left Hi =>
      let l := PrimString.length pats.[i] in
      sums pats m (i + 1) (P + l) (if L <? l then l else L)
        (Acc_inv H (dec_step m i Hi))
  | right _ => (P, L)
  end.

(* a.[j] = j for j = i .. m-1. *)
Fixpoint iota (m i : int) (a : array int) (H : Acc (Zwf 0) (gap m i))
    {struct H} : array int :=
  match bdec (i <? m) with
  | left Hi => iota m (i + 1) a.[i <- i] (Acc_inv H (dec_step m i Hi))
  | right _ => a
  end.

(* The patterns of every node: a linked list fp.[v], np.[fp.[v]], ...
   of pattern numbers plus one, ended by 0. *)
Fixpoint plist_loop (cur : array int) (m i : int) (fp np : array int)
    (H : Acc (Zwf 0) (gap m i)) {struct H} : array int * array int :=
  match bdec (i <? m) with
  | left Hi =>
      let v := cur.[i] in
      let old := fp.[v] in
      plist_loop cur m (i + 1) fp.[v <- i + 1] np.[i + 1 <- old]
        (Acc_inv H (dec_step m i Hi))
  | right _ => (fp, np)
  end.

(* From node x, the deepest node whose word is (x's word, or a proper
   suffix of it, followed by c) -- the failure walk. *)
Fixpoint walk (t : trie) (fl : array int) (c x : int)
    (H : Acc (Zwf 0) (φ x)) {struct H} : int :=
  let y := lookup t x c in
  match bdec (y =? 0) with
  | right _ => y
  | left _ =>
      match bdec (x =? 0) with
      | left _ => 0
      | right _ =>
          let x' := fl.[x] in
          match bdec (x' <? x) with
          | left Hx => walk t fl c x' (Acc_inv H (dec_lt x x' Hx))
          | right _ => 0
          end
      end
  end.

(* Failure and output links of nodes v .. N-1, in index order (which is
   breadth-first order). *)
Fixpoint fail_loop (t : trie) (fp : array int) (N v : int) (fl out : array int)
    (H : Acc (Zwf 0) (gap N v)) {struct H} : array int * array int :=
  match bdec (v <? N) with
  | left Hv =>
      let u := (tpar t).[v] in
      let c := (tchr t).[v] in
      let f := if u =? 0 then 0
               else let x := fl.[u] in walk t fl c x (Zwf_well_founded 0 (φ x)) in
      let o := if fp.[f] =? 0 then out.[f] else f in
      fail_loop t fp N (v + 1) fl.[v <- f] out.[v <- o]
        (Acc_inv H (dec_step N v Hv))
  | right _ => (fl, out)
  end.

Section Scan.
  Variable Sx : Type.
  (* f s i p : record that pattern i occurs at position p *)
  Variable f : Sx -> int -> int -> Sx.
  Variable t : trie.
  Variables fl out fp np : array int.
  Variable txt : PrimString.string.

  (* every pattern of the list e, np.[e], ... occurs at p *)
  Fixpoint emit_list (p e : int) (s : Sx) (H : Acc (Zwf 0) (φ e)) {struct H} : Sx :=
    match bdec (e =? 0) with
    | left _ => s
    | right _ =>
        let s' := f s (e - 1) p in
        let e' := np.[e] in
        match bdec (e' <? e) with
        | left He => emit_list p e' s' (Acc_inv H (dec_lt e e' He))
        | right _ => s'
        end
    end.

  (* the patterns of x and of its output chain end at je - 1 *)
  Fixpoint emit_chain (je x : int) (s : Sx) (H : Acc (Zwf 0) (φ x)) {struct H} : Sx :=
    match bdec (x =? 0) with
    | left _ => s
    | right _ =>
        let e := fp.[x] in
        let s' := emit_list (je - (tdep t).[x]) e s (Zwf_well_founded 0 (φ e)) in
        let o := out.[x] in
        match bdec (o <? x) with
        | left Ho => emit_chain je o s' (Acc_inv H (dec_lt x o Ho))
        | right _ => s'
        end
    end.

  (* the text pass, from position j in state st *)
  Fixpoint scan (n j st : int) (s : Sx) (H : Acc (Zwf 0) (gap n j)) {struct H} : Sx :=
    match bdec (j <? n) with
    | left Hj =>
        let st' := walk t fl (PrimString.get txt j) st (Zwf_well_founded 0 (φ st)) in
        let s' := emit_chain (j + 1) st' s (Zwf_well_founded 0 (φ st')) in
        scan n (j + 1) st' s' (Acc_inv H (dec_step n j Hj))
    | right _ => s
    end.
End Scan.

Definition f_cnt (cnt : array int) (i _p : int) : array int :=
  let c := cnt.[i] in cnt.[i <- c + 1].

Definition f_fill (st : array (array int) * array int) (i p : int)
    : array (array int) * array int :=
  let rows := fst st in
  let ptr := snd st in
  let k := ptr.[i] in
  let row := rows.[i] in
  (rows.[i <- row.[k <- p]], ptr.[i <- k + 1]).

(* rows.[i] := make cnt.[i] 0 for i = i .. m-1 *)
Fixpoint alloc_loop (cnt : array int) (m i : int) (rows : array (array int))
    (H : Acc (Zwf 0) (gap m i)) {struct H} : array (array int) :=
  match bdec (i <? m) with
  | left Hi =>
      alloc_loop cnt m (i + 1) rows.[i <- PArray.make cnt.[i] 0]
        (Acc_inv H (dec_step m i Hi))
  | right _ => rows
  end.

Definition multimatch_impl (pats : array PrimString.string) (txt : PrimString.string)
    : array (array uint) :=
  let m := PArray.length pats in
  let PL := sums pats m 0 0 0 (Zwf_well_founded 0 (gap m 0)) in
  let cap := fst PL + 1 in
  let L := snd PL in
  let t0 := mkT (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0)
                (PArray.make cap 0) (PArray.make cap 0) 1 in
  let act0 := iota m 0 (PArray.make m 0) (Zwf_well_founded 0 (gap m 0)) in
  let st := rounds pats L 0 (mkB act0 (PArray.make m 0) m t0)
              (Zwf_well_founded 0 (gap L 0)) in
  let t := bt st in
  let pl := plist_loop (bcur st) m 0 (PArray.make cap 0) (PArray.make (m + 1) 0)
              (Zwf_well_founded 0 (gap m 0)) in
  let fp := fst pl in
  let np := snd pl in
  let fo := fail_loop t fp (tn t) 1 (PArray.make cap 0) (PArray.make cap 0)
              (Zwf_well_founded 0 (gap (tn t) 1)) in
  let fl := fst fo in
  let out := snd fo in
  let n := PrimString.length txt in
  let cnt := scan _ f_cnt t fl out fp np txt n 0 0 (PArray.make m 0)
               (Zwf_well_founded 0 (gap n 0)) in
  let rows := alloc_loop cnt m 0 (PArray.make m (PArray.make 0 0))
                (Zwf_well_founded 0 (gap m 0)) in
  fst (scan _ f_fill t fl out fp np txt n 0 0 (rows, PArray.make m 0)
         (Zwf_well_founded 0 (gap n 0))).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition multimatch : array PrimString.string -> PrimString.string ->
                        array (array uint) := multimatch_impl.
