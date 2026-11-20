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
From KattisLib Require Import Cost.
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
Elpi complexity sumbool.
Elpi complexity bdec.
Elpi complexity fst.
Elpi complexity snd.

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
Elpi complexity trie.
Elpi complexity tchr.
Elpi complexity tpar.
Elpi complexity tfc.
Elpi complexity tns.
Elpi complexity tdep.
Elpi complexity tn.

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
Elpi complexity lookup_from.
Arguments lookup_from_cost : simpl never.

Definition lookup (t : trie) (u c : int) : int :=
  let v := (tfc t).[u] in
  lookup_from (tchr t) (tns t) c v (Zwf_well_founded 0 (φ v)).
Elpi complexity lookup.
Arguments lookup_cost : simpl never.

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
Elpi complexity add_child.
Arguments add_child_cost : simpl never.

(* The construction state: the active patterns act.[0 .. bw-1] (those
   still longer than the current depth), the current node of every
   pattern, the trie. *)
Record bstate := mkB { bact : array int; bcur : array int; bw : int; bt : trie }.
Elpi complexity bstate.
Elpi complexity bact.
Elpi complexity bcur.
Elpi complexity bw.
Elpi complexity bt.

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
Elpi complexity round_loop.
Arguments round_loop_cost : simpl never.

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
Elpi complexity rounds.
Arguments rounds_cost : simpl never.

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
Elpi complexity sums.
Arguments sums_cost : simpl never.

(* a.[j] = j for j = i .. m-1. *)
Fixpoint iota (m i : int) (a : array int) (H : Acc (Zwf 0) (gap m i))
    {struct H} : array int :=
  match bdec (i <? m) with
  | left Hi => iota m (i + 1) a.[i <- i] (Acc_inv H (dec_step m i Hi))
  | right _ => a
  end.
Elpi complexity iota.
Arguments iota_cost : simpl never.

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
Elpi complexity plist_loop.
Arguments plist_loop_cost : simpl never.

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
Elpi complexity walk.
Arguments walk_cost : simpl never.

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
Elpi complexity fail_loop.
Arguments fail_loop_cost : simpl never.

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
Elpi complexity emit_list.
Arguments emit_list_cost : simpl never.
Elpi complexity emit_chain.
Arguments emit_chain_cost : simpl never.
Elpi complexity scan.
Arguments scan_cost : simpl never.

Definition f_cnt (cnt : array int) (i _p : int) : array int :=
  let c := cnt.[i] in cnt.[i <- c + 1].
Elpi complexity f_cnt.
Arguments f_cnt_cost : simpl never.

Definition f_fill (st : array (array int) * array int) (i p : int)
    : array (array int) * array int :=
  let rows := fst st in
  let ptr := snd st in
  let k := ptr.[i] in
  let row := rows.[i] in
  (rows.[i <- row.[k <- p]], ptr.[i <- k + 1]).
Elpi complexity f_fill.
Arguments f_fill_cost : simpl never.

(* rows.[i] := make cnt.[i] 0 for i = i .. m-1 *)
Fixpoint alloc_loop (cnt : array int) (m i : int) (rows : array (array int))
    (H : Acc (Zwf 0) (gap m i)) {struct H} : array (array int) :=
  match bdec (i <? m) with
  | left Hi =>
      alloc_loop cnt m (i + 1) rows.[i <- PArray.make cnt.[i] 0]
        (Acc_inv H (dec_step m i Hi))
  | right _ => rows
  end.
Elpi complexity alloc_loop.
Arguments alloc_loop_cost : simpl never.

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
Elpi complexity multimatch_impl.
Arguments multimatch_impl_cost : simpl never.

(* ================================================================== *)
(* Prop side                                                           *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alength_bound : forall A (t : array A), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros A t. pose proof (leb_length A t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma alength_make : forall A (n : int) (b : A),
  ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n b) = n.
Proof.
  intros A n b H. rewrite length_make.
  replace (n <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  ((φ i) < (φ (PArray.length t)))%Z -> t.[i <- b].[i] = b.
Proof. intros t i b H. apply (get_set_same int t i b). apply ltb_spec. exact H. Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma aget_make : forall (n i b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

Lemma amake_len : forall (n b : int), ((φ n) <= 4194303)%Z ->
  PArray.length (PArray.make n b) = n.
Proof. intros n b H. exact (alength_make int n b H). Qed.

Lemma int_eq_dec : forall x y : int, {x = y} + {x <> y}.
Proof.
  intros x y. destruct (x =? y) eqn:E.
  - left. apply eqb_spec. exact E.
  - right. intro F. apply eqb_spec in F. congruence.
Defined.

Lemma neq_phi : forall x y : int, x <> y -> (φ x) <> (φ y).
Proof. intros x y H E. apply H. apply to_Z_inj. exact E. Qed.

Lemma eqb_true : forall x y : int, (x =? y) = true -> x = y.
Proof. intros x y H. apply eqb_spec. exact H. Qed.

Lemma eqb_false : forall x y : int, (x =? y) = false -> x <> y.
Proof. intros x y H E. subst. rewrite eqb_refl in H. discriminate. Qed.

Lemma ltb_true : forall x y : int, (x <? y) = true -> ((φ x) < (φ y))%Z.
Proof. intros x y H. apply ltb_spec. exact H. Qed.

Lemma ltb_false : forall x y : int, (x <? y) = false -> ((φ y) <= (φ x))%Z.
Proof.
  intros x y H. rewrite <- Bool.not_true_iff_false, ltb_spec in H. lia.
Qed.

Lemma phi_bnd : forall x : int, (0 <= (φ x) < wB)%Z.
Proof. exact to_Z_bounded. Qed.

Lemma phi0 : (φ 0) = 0%Z.
Proof. reflexivity. Qed.

Lemma phi1 : (φ 1) = 1%Z.
Proof. reflexivity. Qed.

Lemma phi_of_Z : forall z : Z, (0 <= z < wB)%Z -> (φ (of_Z z)) = z.
Proof. intros z H. rewrite of_Z_spec. apply Z.mod_small. exact H. Qed.

Lemma phi_add1 : forall x : int, ((φ x) + 1 < wB)%Z -> (φ (x + 1)) = ((φ x) + 1)%Z.
Proof. intros x H. sia. Qed.

Lemma phi_inj : forall x y : int, (φ x) = (φ y) -> x = y.
Proof. exact to_Z_inj. Qed.

(* ------------------------------------------------------------------ *)
(* Linked lists through an array of next pointers                      *)
(* ------------------------------------------------------------------ *)

Inductive Reach (ns : array int) : int -> int -> Prop :=
| R_here : forall a, a <> 0 -> Reach ns a a
| R_next : forall a b, a <> 0 -> Reach ns ns.[a] b -> Reach ns a b.

Lemma Reach_nz : forall ns a b, Reach ns a b -> a <> 0 /\ b <> 0.
Proof.
  intros ns a b H. induction H as [a Ha | a b Ha H [_ IH]]; auto.
Qed.

Lemma Reach_0 : forall ns b, ~ Reach ns 0 b.
Proof. intros ns b H. apply Reach_nz in H. tauto. Qed.

Lemma Reach_cons : forall ns a b, a <> 0 ->
  (Reach ns a b <-> b = a \/ Reach ns ns.[a] b).
Proof.
  intros ns a b Ha. split.
  - intros H. inversion H; subst; auto.
  - intros [E | H]; [subst; constructor; exact Ha | apply R_next; auto].
Qed.

Lemma Reach_le : forall (ns : array int) (K : Z),
  (forall x, (0 < (φ x) <= K)%Z -> ((φ (ns.[x])) < (φ x))%Z) ->
  forall a b, ((φ a) <= K)%Z -> Reach ns a b -> ((φ b) <= (φ a))%Z.
Proof.
  intros ns K HK a b Ha H. induction H as [a Ha0 | a b Ha0 H IH]; [lia|].
  assert (0 < (φ a))%Z by (pose proof (phi_bnd a); pose proof (neq_phi _ _ Ha0); rewrite phi0 in *; lia).
  pose proof (HK a ltac:(lia)). specialize (IH ltac:(lia)). lia.
Qed.

Lemma Reach_frame : forall ns a e y b,
  (forall x, Reach ns a x -> x <> e) ->
  (Reach ns.[e <- y] a b <-> Reach ns a b).
Proof.
  intros ns a e y b Hx. split.
  - intros H. induction H as [a Ha | a b Ha H IH].
    + constructor. exact Ha.
    + assert (Hae : a <> e) by (apply Hx; constructor; exact Ha).
      assert (E : ns.[e <- y].[a] = ns.[a]) by (apply aget_set_other; intro F; apply Hae; symmetry; exact F).
      rewrite E in H, IH.
      apply R_next; [exact Ha|]. apply IH.
      intros x Hr. apply Hx. apply R_next; assumption.
  - intros H. induction H as [a Ha | a b Ha H IH].
    + constructor. exact Ha.
    + assert (Hae : a <> e) by (apply Hx; constructor; exact Ha).
      apply R_next; [exact Ha|].
      assert (E : ns.[e <- y].[a] = ns.[a]) by (apply aget_set_other; intro F; apply Hae; symmetry; exact F).
      rewrite E.
      apply IH. intros x Hr. apply Hx. apply R_next; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Suffixes                                                            *)
(* ------------------------------------------------------------------ *)

Definition suffix (y X : list Z) : Prop := exists z, X = z ++ y.

Lemma suffix_skipn : forall y X, suffix y X <->
  (List.length y <= List.length X)%nat /\ skipn (List.length X - List.length y) X = y.
Proof.
  intros y X. split.
  - intros [z ->]. rewrite length_app.
    replace (List.length z + List.length y - List.length y)%nat with (List.length z) by lia.
    split; [lia|]. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
  - intros [Hl Hs]. exists (firstn (List.length X - List.length y) X).
    rewrite <- Hs at 2. symmetry. apply firstn_skipn.
Qed.

Lemma suffix_length : forall y X, suffix y X -> (List.length y <= List.length X)%nat.
Proof. intros y X [z ->]. rewrite length_app. lia. Qed.

Lemma suffix_refl : forall X, suffix X X.
Proof. intros X. exists []. reflexivity. Qed.

Lemma suffix_nil : forall X, suffix [] X.
Proof. intros X. exists X. rewrite app_nil_r. reflexivity. Qed.

Lemma suffix_trans : forall a b c, suffix a b -> suffix b c -> suffix a c.
Proof.
  intros a b c [z1 ->] [z2 ->]. exists (z2 ++ z1). rewrite app_assoc. reflexivity.
Qed.

Lemma suffix_both : forall a b X, suffix a X -> suffix b X ->
  (List.length a <= List.length b)%nat -> suffix a b.
Proof.
  intros a b X Ha Hb Hl.
  apply suffix_skipn in Ha as [Ha1 Ha2]. apply suffix_skipn in Hb as [Hb1 Hb2].
  apply suffix_skipn. split; [exact Hl|].
  set (la := List.length a) in *. set (lb := List.length b) in *.
  set (lx := List.length X) in *.
  rewrite <- Hb2, skipn_skipn. rewrite <- Ha2. f_equal. lia.
Qed.

Lemma suffix_eq : forall a b X, suffix a X -> suffix b X ->
  List.length a = List.length b -> a = b.
Proof.
  intros a b X Ha Hb Hl.
  apply suffix_skipn in Ha as [_ Ha2]. apply suffix_skipn in Hb as [_ Hb2].
  rewrite Hl in Ha2. congruence.
Qed.

Lemma suffix_snoc : forall y a X c,
  suffix (y ++ [a]) (X ++ [c]) <-> a = c /\ suffix y X.
Proof.
  intros y a X c. split.
  - intros [z Hz]. rewrite app_assoc in Hz. apply app_inj_tail in Hz as [H1 H2].
    split; [symmetry; exact H2 | exists z; exact H1].
  - intros [-> [z ->]]. exists z. rewrite app_assoc. reflexivity.
Qed.

Lemma suffix_snoc_cases : forall w X c, suffix w (X ++ [c]) ->
  w = [] \/ exists y, w = y ++ [c] /\ suffix y X.
Proof.
  intros w X c H. destruct (list_eq_dec Z.eq_dec w []) as [-> | Hn]; [left; reflexivity|].
  destruct (exists_last Hn) as (y & a & ->).
  right. apply suffix_snoc in H as [-> H]. exists y. split; [reflexivity | exact H].
Qed.

(* ------------------------------------------------------------------ *)
(* The trie invariant                                                  *)
(* ------------------------------------------------------------------ *)

(* W v is the word of node v, a ghost. *)
Definition IsNode (t : trie) (W : int -> list Z) (y : list Z) : Prop :=
  exists z, ((φ z) < (φ (tn t)))%Z /\ W z = y.

Record TrieInv (t : trie) (cap : Z) (W : int -> list Z) : Prop := {
  ti_lchr : (φ (PArray.length (tchr t))) = cap;
  ti_lpar : (φ (PArray.length (tpar t))) = cap;
  ti_lfc : (φ (PArray.length (tfc t))) = cap;
  ti_lns : (φ (PArray.length (tns t))) = cap;
  ti_ldep : (φ (PArray.length (tdep t))) = cap;
  ti_n : (1 <= (φ (tn t)) <= cap)%Z;
  ti_root : W 0 = [];
  ti_par : forall v, (0 < (φ v) < (φ (tn t)))%Z ->
     ((φ ((tpar t).[v])) < (φ v))%Z /\ W v = W ((tpar t).[v]) ++ [(φ ((tchr t).[v]))];
  ti_dep : forall v, ((φ v) < (φ (tn t)))%Z ->
     (φ ((tdep t).[v])) = Z.of_nat (List.length (W v));
  ti_inj : forall u v, ((φ u) < (φ (tn t)))%Z -> ((φ v) < (φ (tn t)))%Z -> W u = W v -> u = v;
  ti_mono : forall u v, ((φ u) < (φ (tn t)))%Z -> ((φ v) < (φ (tn t)))%Z -> ((φ u) <= (φ v))%Z ->
     (List.length (W u) <= List.length (W v))%nat;
  ti_ns : forall v, (0 < (φ v) < (φ (tn t)))%Z -> ((φ ((tns t).[v])) < (φ v))%Z;
  ti_ch : forall u, ((φ u) < (φ (tn t)))%Z -> forall v,
     Reach (tns t) ((tfc t).[u]) v <-> ((0 < (φ v) < (φ (tn t)))%Z /\ (tpar t).[v] = u);
  ti_fresh : forall u, ((φ (tn t)) <= (φ u) < cap)%Z -> (tfc t).[u] = 0;
}.

Lemma pos_of_nz : forall v : int, v <> 0 -> (0 < (φ v))%Z.
Proof.
  intros v H. pose proof (phi_bnd v). pose proof (neq_phi _ _ H). rewrite phi0 in *. lia.
Qed.

Lemma nz_of_pos : forall v : int, (0 < (φ v))%Z -> v <> 0.
Proof. intros v H E. subst. rewrite phi0 in H. lia. Qed.

Lemma ti_cap : forall t cap W, TrieInv t cap W -> (cap <= 4194303)%Z.
Proof.
  intros t cap W Ht. rewrite <- (ti_lchr _ _ _ Ht). exact (alength_bound int (tchr t)).
Qed.

Lemma ti_word_nz : forall t cap W v, TrieInv t cap W -> (0 < (φ v) < (φ (tn t)))%Z ->
  W v <> [].
Proof.
  intros t cap W v Ht Hv E. destruct (ti_par _ _ _ Ht v Hv) as [_ E2].
  rewrite E in E2. destruct (W (tpar t).[v]); discriminate.
Qed.

Lemma ti_nil : forall t cap W v, TrieInv t cap W -> ((φ v) < (φ (tn t)))%Z ->
  W v = [] -> v = 0.
Proof.
  intros t cap W v Ht Hv E. destruct (int_eq_dec v 0) as [|Hn]; [assumption|].
  exfalso. apply (ti_word_nz t cap W v Ht); [|exact E].
  split; [apply pos_of_nz; exact Hn | exact Hv].
Qed.

Lemma ti_lt : forall t cap W u v, TrieInv t cap W ->
  ((φ u) < (φ (tn t)))%Z -> ((φ v) < (φ (tn t)))%Z ->
  (List.length (W u) < List.length (W v))%nat -> ((φ u) < (φ v))%Z.
Proof.
  intros t cap W u v Ht Hu Hv Hl.
  destruct (Z_lt_le_dec (φ u) (φ v)) as [|H]; [assumption|].
  pose proof (ti_mono _ _ _ Ht v u Hv Hu H). lia.
Qed.

Lemma ti_depth_le : forall t cap W, TrieInv t cap W ->
  forall v, ((φ v) < (φ (tn t)))%Z -> (Z.of_nat (List.length (W v)) <= (φ v))%Z.
Proof.
  intros t cap W Ht.
  assert (forall z v, (φ v) = z -> ((φ v) < (φ (tn t)))%Z -> (Z.of_nat (List.length (W v)) <= (φ v))%Z);
    [|intros v; apply (H (φ v) v eq_refl)].
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros v Hz Hv. destruct (int_eq_dec v 0) as [-> | Hn].
  - rewrite (ti_root _ _ _ Ht). simpl. lia.
  - pose proof (pos_of_nz v Hn) as Hp.
    destruct (ti_par _ _ _ Ht v ltac:(lia)) as [Hpv Ew].
    pose proof (phi_bnd ((tpar t).[v])).
    assert (IH' := IH (φ ((tpar t).[v])) ltac:(unfold Zwf; lia) _ eq_refl ltac:(lia)).
    rewrite Ew, length_app. simpl. lia.
Qed.

Lemma isnode_prefix : forall t cap W y a, TrieInv t cap W ->
  IsNode t W (y ++ [a]) -> IsNode t W y.
Proof.
  intros t cap W y a Ht [z [Hz Ew]].
  assert (Hz0 : z <> 0).
  { intro E. subst. rewrite (ti_root _ _ _ Ht) in Ew. destruct y; discriminate. }
  pose proof (pos_of_nz z Hz0).
  destruct (ti_par _ _ _ Ht z ltac:(lia)) as [Hp Ew2].
  rewrite Ew in Ew2. apply app_inj_tail in Ew2 as [E1 _].
  exists ((tpar t).[z]). split; [lia | symmetry; exact E1].
Qed.

(* ------------------------------------------------------------------ *)
(* lookup                                                              *)
(* ------------------------------------------------------------------ *)

Lemma lookup_from_eq : forall chr ns c v H,
  lookup_from chr ns c v H =
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
Proof. intros. destruct H. reflexivity. Qed.

Lemma lookup_from_spec : forall chr ns c v H,
  (forall x, Reach ns v x -> ((φ (ns.[x])) < (φ x))%Z) ->
  (lookup_from chr ns c v H <> 0 ->
     Reach ns v (lookup_from chr ns c v H) /\ chr.[lookup_from chr ns c v H] = c) /\
  (lookup_from chr ns c v H = 0 -> forall x, Reach ns v x -> chr.[x] <> c).
Proof.
  intros chr ns c.
  assert (G : forall z v H, (φ v) = z ->
    (forall x, Reach ns v x -> ((φ (ns.[x])) < (φ x))%Z) ->
    (lookup_from chr ns c v H <> 0 ->
       Reach ns v (lookup_from chr ns c v H) /\ chr.[lookup_from chr ns c v H] = c) /\
    (lookup_from chr ns c v H = 0 -> forall x, Reach ns v x -> chr.[x] <> c));
    [|intros v H; exact (G _ v H eq_refl)].
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros v H Hz Hd. rewrite lookup_from_eq.
  destruct (bdec (v =? 0)) as [E | E].
  - apply eqb_true in E. subst v. split; [tauto|].
    intros _ x Hr. exfalso. exact (Reach_0 _ _ Hr).
  - apply eqb_false in E.
    destruct (chr.[v] =? c) eqn:Ec.
    + apply eqb_true in Ec. split; [intros _; split; [constructor; exact E | exact Ec]|].
      intros F. contradiction.
    + apply eqb_false in Ec. cbv zeta.
      destruct (bdec (ns.[v] <? v)) as [Hn | Hn].
      * pose proof (ltb_true _ _ Hn) as Hn'.
        assert (Hd' : forall x, Reach ns ns.[v] x -> ((φ (ns.[x])) < (φ x))%Z)
          by (intros x Hr; apply Hd; apply R_next; assumption).
        destruct (IH (φ (ns.[v])) ltac:(rewrite <- Hz; apply dec_lt; exact Hn)
                    (ns.[v]) (Acc_inv H (dec_lt v ns.[v] Hn)) eq_refl Hd') as [IH1 IH2].
        split.
        -- intros Hy. destruct (IH1 Hy) as [Hr Hc]. split; [apply R_next; assumption | exact Hc].
        -- intros Hy x Hr. apply (Reach_cons ns v x E) in Hr as [-> | Hr]; [exact Ec|].
           exact (IH2 Hy x Hr).
      * exfalso. pose proof (ltb_false _ _ Hn).
        pose proof (Hd v ltac:(constructor; exact E)). lia.
Qed.

Lemma lookup_spec : forall t cap W u c, TrieInv t cap W -> ((φ u) < (φ (tn t)))%Z ->
  (lookup t u c <> 0 ->
     (0 < (φ (lookup t u c)) < (φ (tn t)))%Z /\ W (lookup t u c) = W u ++ [(φ c)]) /\
  (lookup t u c = 0 -> ~ IsNode t W (W u ++ [(φ c)])).
Proof.
  intros t cap W u c Ht Hu. unfold lookup.
  set (v0 := (tfc t).[u]).
  assert (Hd : forall x, Reach (tns t) v0 x -> ((φ ((tns t).[x])) < (φ x))%Z).
  { intros x Hr. apply (ti_ch _ _ _ Ht u Hu x) in Hr as [Hx _]. apply (ti_ns _ _ _ Ht). exact Hx. }
  destruct (lookup_from_spec (tchr t) (tns t) c v0 (Zwf_well_founded 0 (φ v0)) Hd) as [H1 H2].
  set (y := lookup_from (tchr t) (tns t) c v0 (Zwf_well_founded 0 (φ v0))) in *.
  split.
  - intros Hy. destruct (H1 Hy) as [Hr Hc].
    apply (ti_ch _ _ _ Ht u Hu y) in Hr as [Hy' Hp].
    split; [exact Hy'|]. destruct (ti_par _ _ _ Ht y Hy') as [_ Ew].
    rewrite Ew, Hp, Hc. reflexivity.
  - intros Hy [z [Hz Ew]].
    assert (Hz0 : z <> 0).
    { intro E. subst. rewrite (ti_root _ _ _ Ht) in Ew. destruct (W u); discriminate. }
    pose proof (pos_of_nz z Hz0).
    destruct (ti_par _ _ _ Ht z ltac:(lia)) as [Hp Ew2].
    rewrite Ew in Ew2. apply app_inj_tail in Ew2 as [E1 E2].
    pose proof (phi_bnd ((tpar t).[z])).
    assert (Epar : (tpar t).[z] = u)
      by (apply (ti_inj _ _ _ Ht); [lia | exact Hu | symmetry; exact E1]).
    apply (H2 Hy z).
    + apply (ti_ch _ _ _ Ht u Hu z). split; [lia | exact Epar].
    + apply phi_inj. symmetry. exact E2.
Qed.

Lemma ilen_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof. intros t. exact (alength_bound int t). Qed.

(* ------------------------------------------------------------------ *)
(* add_child                                                           *)
(* ------------------------------------------------------------------ *)

Lemma add_child_spec : forall t cap W u c, TrieInv t cap W -> ((φ u) < (φ (tn t)))%Z ->
  ((φ (tn t)) < cap)%Z ->
  (forall x, ((φ x) < (φ (tn t)))%Z -> (List.length (W x) <= S (List.length (W u)))%nat) ->
  exists W', TrieInv (fst (add_child t u c)) cap W' /\
    (forall x, ((φ x) < (φ (tn t)))%Z -> W' x = W x) /\
    ((φ (tn (fst (add_child t u c)))) = (φ (tn t)) \/
     (φ (tn (fst (add_child t u c)))) = (φ (tn t)) + 1)%Z /\
    ((φ (snd (add_child t u c))) < (φ (tn (fst (add_child t u c)))))%Z /\
    W' (snd (add_child t u c)) = W u ++ [(φ c)] /\
    (forall x, ((φ x) < (φ (tn (fst (add_child t u c)))))%Z ->
       ((φ x) < (φ (tn t)))%Z \/ W' x = W u ++ [(φ c)]).
Proof.
  intros t cap W u c Ht Hu Hcap Hdep.
  destruct (lookup_spec t cap W u c Ht Hu) as [L1 L2].
  pose proof (ti_cap _ _ _ Ht) as Hcap4.
  unfold add_child. destruct (lookup t u c =? 0) eqn:E.
  2:{ apply eqb_false in E. destruct (L1 E) as [Hy Ew].
      exists W. simpl. split; [exact Ht|]. split; [reflexivity|].
      split; [left; reflexivity|]. split; [lia|]. split; [exact Ew|].
      intros x Hx. left. exact Hx. }
  apply eqb_true in E. specialize (L2 E).
  pose proof (ti_n _ _ _ Ht) as Hn.
  set (n := tn t) in *.
  assert (Hn1 : (φ (n + 1)) = ((φ n) + 1)%Z) by (apply phi_add1; rewrite wB_val; lia).
  set (Wn := W u ++ [(φ c)]).
  set (W' := fun x => if x =? n then Wn else W x).
  assert (W'n : W' n = Wn) by (unfold W'; rewrite eqb_refl; reflexivity).
  assert (W'o : forall x, x <> n -> W' x = W x)
    by (intros x Hx; unfold W'; destruct (x =? n) eqn:Ex; [apply eqb_true in Ex; contradiction | reflexivity]).
  assert (Hlt_n : forall x, ((φ x) < (φ n))%Z -> x <> n) by (intros x Hx F; subst; lia).
  assert (Hun : u <> n) by (apply Hlt_n; exact Hu).
  exists W'. simpl.
  assert (Hlfc : (φ (PArray.length (tfc t))) = cap) by exact (ti_lfc _ _ _ Ht).
  assert (Hlns : (φ (PArray.length (tns t))) = cap) by exact (ti_lns _ _ _ Ht).
  assert (Hlpar : (φ (PArray.length (tpar t))) = cap) by exact (ti_lpar _ _ _ Ht).
  assert (Hlchr : (φ (PArray.length (tchr t))) = cap) by exact (ti_lchr _ _ _ Ht).
  assert (Hldep : (φ (PArray.length (tdep t))) = cap) by exact (ti_ldep _ _ _ Ht).
  (* children of an old node are old nodes *)
  assert (Hold : forall u', ((φ u') < (φ n))%Z -> forall x, Reach (tns t) ((tfc t).[u']) x -> x <> n).
  { intros u' Hu' x Hr. apply (ti_ch _ _ _ Ht u' Hu' x) in Hr as [Hx _]. apply Hlt_n. lia. }
  split; [constructor; simpl | ].
  - rewrite alength_set. exact Hlchr.
  - rewrite alength_set. exact Hlpar.
  - rewrite alength_set. exact Hlfc.
  - rewrite alength_set. exact Hlns.
  - rewrite alength_set. exact Hldep.
  - lia.
  - rewrite W'o by (intro F; rewrite <- F, phi0 in Hn; lia).
    exact (ti_root _ _ _ Ht).
  - intros v Hv. rewrite Hn1 in Hv. destruct (int_eq_dec v n) as [-> | Hvn].
    + rewrite aget_set_same by lia. rewrite aget_set_same by lia.
      rewrite W'n, W'o by exact Hun. split; [exact Hu | reflexivity].
    + rewrite aget_set_other by (intro F; apply Hvn; symmetry; exact F).
      rewrite aget_set_other by (intro F; apply Hvn; symmetry; exact F).
      assert (Hv' : (0 < (φ v) < (φ n))%Z) by (pose proof (neq_phi _ _ Hvn); lia).
      destruct (ti_par _ _ _ Ht v Hv') as [Hp Ew].
      rewrite W'o by exact Hvn. rewrite W'o by (apply Hlt_n; lia).
      split; [exact Hp | exact Ew].
  - intros v Hv. rewrite Hn1 in Hv. destruct (int_eq_dec v n) as [-> | Hvn].
    + rewrite aget_set_same by lia. rewrite W'n.
      unfold Wn. rewrite length_app. simpl.
      pose proof (ti_depth_le _ _ _ Ht u Hu).
      assert (Hd : (φ ((tdep t).[u])) = Z.of_nat (List.length (W u))) by exact (ti_dep _ _ _ Ht u Hu).
      rewrite phi_add1 by (rewrite Hd, wB_val; lia). rewrite Hd. lia.
    + rewrite aget_set_other by (intro F; apply Hvn; symmetry; exact F).
      rewrite W'o by exact Hvn. apply (ti_dep _ _ _ Ht). pose proof (neq_phi _ _ Hvn). lia.
  - intros x y Hx Hy Exy. rewrite Hn1 in Hx, Hy.
    destruct (int_eq_dec x n) as [-> | Hxn]; destruct (int_eq_dec y n) as [-> | Hyn];
      [reflexivity | | | ].
    + exfalso. rewrite W'n, W'o in Exy by exact Hyn. apply L2.
      exists y. split; [pose proof (neq_phi _ _ Hyn); lia | symmetry; exact Exy].
    + exfalso. rewrite W'n, W'o in Exy by exact Hxn. apply L2.
      exists x. split; [pose proof (neq_phi _ _ Hxn); lia | exact Exy].
    + rewrite W'o in Exy by exact Hxn. rewrite W'o in Exy by exact Hyn.
      apply (ti_inj _ _ _ Ht); [pose proof (neq_phi _ _ Hxn) | pose proof (neq_phi _ _ Hyn) | ]; [lia|lia|exact Exy].
  - intros x y Hx Hy Hxy. rewrite Hn1 in Hx, Hy.
    destruct (int_eq_dec y n) as [-> | Hyn].
    + rewrite W'n. unfold Wn. rewrite length_app. simpl.
      destruct (int_eq_dec x n) as [-> | Hxn]; [rewrite W'n; unfold Wn; rewrite length_app; simpl; lia|].
      rewrite W'o by exact Hxn. pose proof (Hdep x ltac:(pose proof (neq_phi _ _ Hxn); lia)). lia.
    + destruct (int_eq_dec x n) as [-> | Hxn]; [exfalso; pose proof (neq_phi _ _ Hyn); lia|].
      rewrite W'o by exact Hxn. rewrite W'o by exact Hyn.
      apply (ti_mono _ _ _ Ht); [pose proof (neq_phi _ _ Hxn) | pose proof (neq_phi _ _ Hyn) | ]; lia.
  - intros v Hv. rewrite Hn1 in Hv. destruct (int_eq_dec v n) as [-> | Hvn].
    + rewrite aget_set_same by lia.
      destruct (int_eq_dec ((tfc t).[u]) 0) as [E0 | E0]; [rewrite E0, phi0; lia|].
      assert (Hr : Reach (tns t) ((tfc t).[u]) ((tfc t).[u])) by (constructor; exact E0).
      apply (ti_ch _ _ _ Ht u Hu) in Hr. lia.
    + rewrite aget_set_other by (intro F; apply Hvn; symmetry; exact F).
      apply (ti_ns _ _ _ Ht). pose proof (neq_phi _ _ Hvn). lia.
  - intros u' Hu' v. rewrite Hn1 in Hu' |- *.
    destruct (int_eq_dec u' u) as [-> | Hu'u].
    + rewrite aget_set_same by lia.
      assert (Hn0 : n <> 0) by (apply nz_of_pos; lia).
      rewrite (Reach_cons _ n v Hn0).
      rewrite aget_set_same by lia.
      rewrite (Reach_frame (tns t) ((tfc t).[u]) n ((tfc t).[u]) v (Hold u Hu)).
      rewrite (ti_ch _ _ _ Ht u Hu v).
      destruct (int_eq_dec v n) as [-> | Hvn].
      * rewrite aget_set_same by lia. split; [intros _; split; [lia | reflexivity] | intros _; left; reflexivity].
      * rewrite aget_set_other by (intro F; apply Hvn; symmetry; exact F).
        pose proof (neq_phi _ _ Hvn). split.
        -- intros [F | [H1 H2]]; [contradiction | split; [lia | exact H2]].
        -- intros [H1 H2]. right. split; [lia | exact H2].
    + rewrite aget_set_other by (intro F; apply Hu'u; symmetry; exact F).
      destruct (int_eq_dec u' n) as [-> | Hu'n].
      * rewrite (ti_fresh _ _ _ Ht n ltac:(lia)). split; [intros F; exfalso; exact (Reach_0 _ _ F)|].
        intros [Hv Hp]. exfalso. destruct (int_eq_dec v n) as [-> | Hvn].
        -- rewrite aget_set_same in Hp by lia. exact (Hun Hp).
        -- rewrite aget_set_other in Hp by (intro F; apply Hvn; symmetry; exact F).
           pose proof (neq_phi _ _ Hvn).
           destruct (ti_par _ _ _ Ht v ltac:(lia)) as [Hpv _]. rewrite Hp in Hpv. lia.
      * assert (Hu'' : ((φ u') < (φ n))%Z) by (pose proof (neq_phi _ _ Hu'n); lia).
        rewrite (Reach_frame (tns t) ((tfc t).[u']) n ((tfc t).[u]) v (Hold u' Hu'')).
        rewrite (ti_ch _ _ _ Ht u' Hu'' v).
        destruct (int_eq_dec v n) as [-> | Hvn].
        -- rewrite aget_set_same by lia. split.
           ++ intros [H1 H2]. lia.
           ++ intros [_ H2]. exfalso. exact (Hu'u (eq_sym H2)).
        -- rewrite aget_set_other by (intro F; apply Hvn; symmetry; exact F).
           pose proof (neq_phi _ _ Hvn). split; intros [H1 H2]; split; auto; lia.
  - intros u' Hu'. rewrite Hn1 in Hu'.
    rewrite aget_set_other by (intro F; subst; lia).
    apply (ti_fresh _ _ _ Ht). lia.
  - split; [intros x Hx; apply W'o; apply Hlt_n; exact Hx|].
    split; [right; exact Hn1|].
    split; [rewrite Hn1; lia|].
    split; [exact W'n|].
    intros x Hx. rewrite Hn1 in Hx. destruct (int_eq_dec x n) as [-> | Hxn]; [right; exact W'n|].
    left. pose proof (neq_phi _ _ Hxn). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Words of primitive strings, index lists, sums                       *)
(* ------------------------------------------------------------------ *)

(* the character codes of a primitive string *)
Definition pstr (s : PrimString.string) : list Z :=
  map (fun k => (φ (PrimString.get s (of_Z (Z.of_nat k)))))
      (seq 0 (Z.to_nat (φ (PrimString.length s)))).

Lemma pstr_len : forall s, Z.of_nat (List.length (pstr s)) = (φ (PrimString.length s)).
Proof.
  intros s. unfold pstr. rewrite length_map, length_seq.
  pose proof (phi_bnd (PrimString.length s)). lia.
Qed.

Lemma pstr_nth : forall s (k : int), ((φ k) < (φ (PrimString.length s)))%Z ->
  nth (Z.to_nat (φ k)) (pstr s) 0%Z = (φ (PrimString.get s k)).
Proof.
  intros s k Hk. unfold pstr. pose proof (phi_bnd k).
  set (g := fun k0 : nat => (φ (PrimString.get s (of_Z (Z.of_nat k0))))).
  rewrite nth_indep with (d' := g 0%nat) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. unfold g. simpl. f_equal. f_equal.
  apply phi_inj. rewrite phi_of_Z; lia.
Qed.

Lemma firstn_snoc : forall (l : list Z) d, (d < List.length l)%nat ->
  firstn (S d) l = firstn d l ++ [nth d l 0%Z].
Proof.
  induction l as [| a l IH]; intros d Hd; simpl in Hd; [lia|].
  destruct d as [| d]; [reflexivity|].
  change (firstn (S (S d)) (a :: l)) with (a :: firstn (S d) l).
  rewrite IH by lia. reflexivity.
Qed.

Lemma firstn_snoc_gen : forall {A} (l : list A) d x, (d < List.length l)%nat ->
  firstn (S d) l = firstn d l ++ [nth d l x].
Proof.
  intros A. induction l as [| a l IH]; intros d x Hd; simpl in Hd; [lia|].
  destruct d as [| d]; [reflexivity|].
  change (firstn (S (S d)) (a :: l)) with (a :: firstn (S d) l).
  rewrite (IH d x) by lia. reflexivity.
Qed.

Definition iseq (m : Z) : list int :=
  map (fun k => of_Z (Z.of_nat k)) (seq 0 (Z.to_nat m)).

Lemma iseq_len : forall m, List.length (iseq m) = Z.to_nat m.
Proof. intros m. unfold iseq. rewrite length_map, length_seq. reflexivity. Qed.

Lemma iseq_In : forall m i, (m < wB)%Z -> (In i (iseq m) <-> ((φ i) < m)%Z).
Proof.
  intros m i Hm. unfold iseq. rewrite in_map_iff. split.
  - intros [k [<- Hk]]. apply in_seq in Hk. rewrite phi_of_Z; lia.
  - intros Hi. exists (Z.to_nat (φ i)). pose proof (phi_bnd i). split.
    + apply phi_inj. rewrite phi_of_Z; lia.
    + apply in_seq. lia.
Qed.

Lemma iseq_NoDup : forall m, (m < wB)%Z -> NoDup (iseq m).
Proof.
  intros m Hm. unfold iseq. apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
  intros a b Ha Hb E. apply in_seq in Ha, Hb.
  assert (E' : (φ (of_Z (Z.of_nat a))) = (φ (of_Z (Z.of_nat b)))) by (rewrite E; reflexivity).
  rewrite !phi_of_Z in E' by lia. lia.
Qed.

Definition zsum (f : int -> Z) (l : list int) : Z :=
  fold_right (fun i a => (f i + a)%Z) 0%Z l.

Lemma zsum_app : forall f l1 l2, zsum f (l1 ++ l2) = (zsum f l1 + zsum f l2)%Z.
Proof. intros f l1 l2. induction l1 as [| a l IH]; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Lemma zsum_ext : forall f g l, (forall i, f i = g i) -> zsum f l = zsum g l.
Proof. intros f g l H. induction l as [| a l IH]; simpl; [reflexivity|]. rewrite IH, H. reflexivity. Qed.

Lemma zsum_le : forall f g l, (forall i, In i l -> (f i <= g i)%Z) -> (zsum f l <= zsum g l)%Z.
Proof.
  intros f g l H. induction l as [| a l IH]; simpl; [lia|].
  pose proof (H a (or_introl eq_refl)). specialize (IH (fun i Hi => H i (or_intror Hi))). lia.
Qed.

Lemma zsum_nonneg : forall f l, (forall i, In i l -> (0 <= f i)%Z) -> (0 <= zsum f l)%Z.
Proof.
  intros f l H. induction l as [| a l IH]; simpl; [lia|].
  pose proof (H a (or_introl eq_refl)). specialize (IH (fun i Hi => H i (or_intror Hi))). lia.
Qed.

Lemma zsum_min_step : forall (p : int -> Z) (d : Z) l,
  zsum (fun i => Z.min (p i) (d + 1)) l =
  (zsum (fun i => Z.min (p i) d) l + Z.of_nat (List.length (filter (fun i => d <? p i)%Z l)))%Z.
Proof.
  intros p d l. induction l as [| a l IH]; simpl; [reflexivity|].
  rewrite IH. destruct (d <? p a)%Z eqn:E; simpl.
  - rewrite Z.ltb_lt in E. lia.
  - rewrite Z.ltb_ge in E. lia.
Qed.

Lemma in_firstn' : forall {A} k (l : list A) x, In x (firstn k l) -> In x l.
Proof. intros A k l x H. rewrite <- (firstn_skipn k l). apply in_or_app. left. exact H. Qed.

Lemma nth_not_in_firstn : forall {A} (l : list A) k x, NoDup l -> (k < List.length l)%nat ->
  ~ In (nth k l x) (firstn k l).
Proof.
  intros A l k x Hl Hk Hin.
  destruct (In_nth _ _ x Hin) as [j [Hj Ej]].
  rewrite length_firstn in Hj. rewrite nth_firstn in Ej.
  destruct (Nat.ltb_spec j k); [|lia].
  rewrite NoDup_nth in Hl. specialize (Hl j k ltac:(lia) Hk (Ej)). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The construction of the trie, level by level                        *)
(* ------------------------------------------------------------------ *)

Lemma round_loop_eq : forall pats d na k st H,
  round_loop pats d na k st H =
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
Proof. intros. destruct H. reflexivity. Qed.

Lemma rounds_eq : forall pats L d st H,
  rounds pats L d st H =
  match bdec (d <? L) with
  | left Hd =>
      let st' := round_loop pats d (bw st) 0 (mkB (bact st) (bcur st) 0 (bt st))
                   (Zwf_well_founded 0 (gap (bw st) 0)) in
      rounds pats L (d + 1) st' (Acc_inv H (dec_step L d Hd))
  | right _ => st
  end.
Proof. intros. destruct H. reflexivity. Qed.

Section Build.
  Variable pats : array PrimString.string.

  Definition m : Z := (φ (PArray.length pats)).
  Definition pw (i : int) : list Z := pstr pats.[i].
  Definition plen (i : int) : Z := (φ (PrimString.length pats.[i])).
  Definition Ld (d : nat) : list int := filter (fun i => Z.of_nat d <? plen i)%Z (iseq m).
  Definition sumd (d : nat) : Z := zsum (fun i => Z.min (plen i) (Z.of_nat d)) (iseq m).
  Definition Ptot : Z := zsum plen (iseq m).
  Definition Lk (d k : nat) : list int :=
    filter (fun i => Z.of_nat (S d) <? plen i)%Z (firstn k (Ld d)).

  Lemma m_bound : (0 <= m <= 4194303)%Z.
  Proof.
    unfold m. pose proof (phi_bnd (PArray.length pats)).
    assert (H0 : ((φ (PArray.length@{Set} pats)) <= 4194303)%Z) by exact (alength_bound _ pats). lia.
  Qed.

  Lemma plen_len : forall i, Z.of_nat (List.length (pw i)) = plen i.
  Proof. intros i. apply pstr_len. Qed.

  Lemma plen_bnd : forall i, (0 <= plen i < wB)%Z.
  Proof. intros i. apply phi_bnd. Qed.

  Lemma Ld_In : forall d i, In i (Ld d) <-> ((φ i) < m)%Z /\ (Z.of_nat d < plen i)%Z.
  Proof.
    intros d i. unfold Ld. rewrite filter_In, iseq_In by (pose proof m_bound; rewrite wB_val; lia).
    rewrite Z.ltb_lt. reflexivity.
  Qed.

  Lemma Ld_NoDup : forall d, NoDup (Ld d).
  Proof.
    intros d. apply NoDup_filter. apply iseq_NoDup. pose proof m_bound; rewrite wB_val; lia.
  Qed.

  Lemma Ld_len : forall d, (Z.of_nat (List.length (Ld d)) <= m)%Z.
  Proof.
    intros d. unfold Ld. pose proof (filter_length_le (fun i => Z.of_nat d <? plen i)%Z (iseq m)).
    rewrite iseq_len in H. pose proof m_bound. lia.
  Qed.

  Lemma sumd_S : forall d, sumd (S d) = (sumd d + Z.of_nat (List.length (Ld d)))%Z.
  Proof.
    intros d. unfold sumd, Ld. rewrite <- zsum_min_step.
    apply zsum_ext. intros i. f_equal. lia.
  Qed.

  Lemma sumd_le : forall d, (sumd d <= Ptot)%Z.
  Proof.
    intros d. unfold sumd, Ptot. apply zsum_le. intros i _. lia.
  Qed.

  Lemma sumd_0 : sumd 0 = 0%Z.
  Proof.
    unfold sumd. rewrite (zsum_ext _ (fun _ => 0%Z)).
    - induction (iseq m) as [| a l IH]; simpl; [reflexivity|]. rewrite IH. reflexivity.
    - intros i. pose proof (plen_bnd i). lia.
  Qed.

  (* every node is a prefix of a pattern (the root: the empty word) *)
  Definition Pref (t : trie) (W : int -> list Z) : Prop :=
    forall x, ((φ x) < (φ (tn t)))%Z ->
      W x = [] \/ exists i, ((φ i) < m)%Z /\ exists r, pw i = W x ++ r.

  Definition RI (cap : Z) (d k : nat) (st : bstate) : Prop :=
    exists W, TrieInv (bt st) cap W /\ Pref (bt st) W /\
    (forall x, ((φ x) < (φ (tn (bt st))))%Z -> (List.length (W x) <= S d)%nat) /\
    ((φ (tn (bt st))) <= 1 + sumd d + Z.of_nat k)%Z /\
    (φ (PArray.length (bcur st))) = m /\ (φ (PArray.length (bact st))) = m /\
    (forall i, In i (firstn k (Ld d)) ->
       ((φ ((bcur st).[i])) < (φ (tn (bt st))))%Z /\ W ((bcur st).[i]) = firstn (S d) (pw i)) /\
    (forall i, ((φ i) < m)%Z -> ~ In i (firstn k (Ld d)) ->
       ((φ ((bcur st).[i])) < (φ (tn (bt st))))%Z /\ W ((bcur st).[i]) = firstn d (pw i)) /\
    (forall j : int, (Z.of_nat k <= (φ j) < Z.of_nat (List.length (Ld d)))%Z ->
       (bact st).[j] = nth (Z.to_nat (φ j)) (Ld d) 0) /\
    (φ (bw st)) = Z.of_nat (List.length (Lk d k)) /\
    (forall j : int, ((φ j) < (φ (bw st)))%Z -> (bact st).[j] = nth (Z.to_nat (φ j)) (Lk d k) 0).

  Definition round_next (dm : int) (st : bstate) (km : int) : bstate :=
    let act := bact st in
    let i := act.[km] in
    let s := pats.[i] in
    let cur := bcur st in
    let tv := add_child (bt st) cur.[i] (PrimString.get s dm) in
    let cur' := cur.[i <- snd tv] in
    let w := bw st in
    if dm + 1 <? PrimString.length s then mkB act.[w <- i] cur' (w + 1) (fst tv)
    else mkB act cur' w (fst tv).

  Lemma round_loop_step : forall cap, cap = (1 + Ptot)%Z ->
    forall d dm, (φ dm) = Z.of_nat d -> forall na, (φ na) = Z.of_nat (List.length (Ld d)) ->
    forall k km st, (φ km) = Z.of_nat k -> (km <? na) = true -> RI cap d k st ->
    RI cap d (S k) (round_next dm st km).
  Proof.
    intros cap Hcap d dm Hdm na Hna k km st Hkm Hlt HI. unfold round_next.
    pose proof (ltb_true _ _ Hlt) as Hlt'.
    assert (Hk : (k <= List.length (Ld d))%nat) by lia.
    destruct HI as (W & Ht & HPf & Hdp & HN & Hlc & Hla & Hc1 & Hc2 & Ha1 & Hw & Ha2).
    pose proof m_bound as Hm.
    pose proof (Ld_len d) as HLd.
    set (act := bact st). set (cur := bcur st). set (t := bt st). fold act cur t in Ht, Hdp, HN, Hlc, Hla, Hc1, Hc2, Ha1, Hw, Ha2.
    cbv zeta.
    assert (Ei : act.[km] = nth k (Ld d) 0)
      by (rewrite (Ha1 km ltac:(lia)); f_equal; lia).
    set (i := act.[km]) in *.
    assert (Hin : In i (Ld d)) by (rewrite Ei; apply nth_In; lia).
    pose proof Hin as Hin'. apply Ld_In in Hin' as [Him Hid].
    assert (Hnin : ~ In i (firstn k (Ld d)))
      by (rewrite Ei; apply nth_not_in_firstn; [apply Ld_NoDup | lia]).
    destruct (Hc2 i Him Hnin) as [Hu HWu].
    set (u := cur.[i]) in *.
    pose proof (plen_len i) as Hpl.
    assert (HlWu : List.length (W u) = d)
      by (rewrite HWu, length_firstn; lia).
    set (c := PrimString.get pats.[i] dm).
    assert (Hc : nth d (pw i) 0%Z = (φ c)).
    { unfold c. rewrite <- pstr_nth by (unfold plen in Hid; lia). unfold pw. f_equal. lia. }
    assert (HSd : firstn (S d) (pw i) = W u ++ [(φ c)])
      by (rewrite HWu, <- Hc; apply firstn_snoc; lia).
    pose proof (sumd_S d) as HS. pose proof (sumd_le (S d)) as HSle.
    destruct (add_child_spec t cap W u c Ht Hu ltac:(lia) ltac:(intros x Hx; rewrite HlWu; apply Hdp; exact Hx))
      as (W' & Ht' & HWo & HN' & Hv & HWv & Hnew).
    set (tv := add_child t u c) in *.
    set (v := snd tv) in *.
    set (t' := fst tv) in *.
    pose proof (ti_n _ _ _ Ht) as HN1.
    assert (Hlcur : (φ (PArray.length cur)) = m) by exact Hlc.
    assert (Hlact : (φ (PArray.length act)) = m) by exact Hla.
    assert (Hfk : firstn (S k) (Ld d) = firstn k (Ld d) ++ [i])
      by (rewrite Ei; apply firstn_snoc_gen; lia).
    assert (Hkm1 : (φ (km + 1)) = Z.of_nat (S k)) by (rewrite phi_add1; [lia | rewrite wB_val; lia]).
    assert (Hlenk : (S k <= List.length (Ld d))%nat) by lia.
    (* the common part of the new invariant: trie, depths, cur *)
    assert (Hcur : forall i', ((φ i') < m)%Z ->
      (In i' (firstn (S k) (Ld d)) ->
        ((φ (cur.[i <- v].[i'])) < (φ (tn t')))%Z /\ W' (cur.[i <- v].[i']) = firstn (S d) (pw i')) /\
      (~ In i' (firstn (S k) (Ld d)) ->
        ((φ (cur.[i <- v].[i'])) < (φ (tn t')))%Z /\ W' (cur.[i <- v].[i']) = firstn d (pw i'))).
    { intros i' Hi'. rewrite Hfk. destruct (int_eq_dec i' i) as [-> | Hne].
      - rewrite aget_set_same by lia. split.
        + intros _. split; [exact Hv | rewrite HWv, HSd; reflexivity].
        + intros F. exfalso. apply F. apply in_or_app. right. left. reflexivity.
      - rewrite aget_set_other by (intro F; apply Hne; symmetry; exact F).
        assert (Hno : In i' (firstn k (Ld d) ++ [i]) <-> In i' (firstn k (Ld d))).
        { rewrite in_app_iff. simpl. split; [intros [H1 | [H1 | []]]; [exact H1 | congruence] | intros H1; left; exact H1]. }
        rewrite Hno. split.
        + intros H1. destruct (Hc1 i' H1) as [H2 H3]. split; [lia | rewrite HWo by exact H2; exact H3].
        + intros H1. destruct (Hc2 i' Hi' H1) as [H2 H3]. split; [lia | rewrite HWo by exact H2; exact H3]. }
    assert (Hdp' : forall x, ((φ x) < (φ (tn t')))%Z -> (List.length (W' x) <= S d)%nat).
    { intros x Hx. destruct (Hnew x Hx) as [Hx' | Ex].
      - rewrite HWo by exact Hx'. apply Hdp. exact Hx'.
      - rewrite Ex, length_app, HlWu. simpl. lia. }
    assert (HN'' : ((φ (tn t')) <= 1 + sumd d + Z.of_nat (S k))%Z) by lia.
    assert (HLk : Lk d (S k) = Lk d k ++ (if (Z.of_nat (S d) <? plen i)%Z then [i] else [])).
    { unfold Lk. rewrite Hfk, filter_app. simpl. destruct (Z.of_nat (S d) <? plen i)%Z; reflexivity. }
    assert (Hwk : (List.length (Lk d k) <= k)%nat).
    { unfold Lk. pose proof (filter_length_le (fun i0 => Z.of_nat (S d) <? plen i0)%Z (firstn k (Ld d))) as Hfl.
      rewrite length_firstn in Hfl. lia. }
    assert (Hlcur' : (φ (PArray.length cur.[i <- v])) = m) by (rewrite alength_set; exact Hlcur).
    assert (HPf' : Pref t' W').
    { intros x Hx. destruct (Hnew x Hx) as [Hx' | Ex].
      - rewrite HWo by exact Hx'. apply HPf. exact Hx'.
      - right. exists i. split; [exact Him|]. exists (skipn (S d) (pw i)).
        rewrite Ex, <- HSd. symmetry. apply firstn_skipn. }
    destruct (dm + 1 <? PrimString.length pats.[i]) eqn:Eb.
    - (* the pattern goes on *)
      apply ltb_true in Eb. rewrite phi_add1 in Eb by (unfold plen in Hid; rewrite Hdm; lia).
      assert (Eb' : (Z.of_nat (S d) <? plen i)%Z = true) by (apply Z.ltb_lt; unfold plen; lia).
      rewrite Eb' in HLk.
      exists W'. cbn [bt bcur bact bw]. split; [exact Ht'|]. split; [exact HPf'|]. split; [exact Hdp'|]. split; [exact HN''|].
      split; [exact Hlcur'|]. split; [rewrite alength_set; exact Hlact|].
      split; [intros i' Hi'; apply (Hcur i'); [exact (proj1 (proj1 (Ld_In d i') ltac:(eapply in_firstn'; exact Hi'))) | exact Hi']|].
      split; [intros i' Hi' Hn; apply (Hcur i' Hi'); exact Hn|].
      split.
      + intros j Hj. rewrite aget_set_other by (intro F; subst j; rewrite Hw in Hj; lia).
        apply Ha1. lia.
      + split.
        * rewrite HLk, length_app. simpl. rewrite phi_add1 by (rewrite Hw, wB_val; lia). lia.
        * intros j Hj. rewrite HLk.
          rewrite phi_add1 in Hj by (rewrite Hw, wB_val; lia).
          destruct (int_eq_dec j (bw st)) as [-> | Hjw].
          -- rewrite aget_set_same by lia. rewrite Hw. rewrite Nat2Z.id.
             rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
          -- rewrite aget_set_other by (intro F; apply Hjw; symmetry; exact F).
             pose proof (neq_phi _ _ Hjw).
             rewrite app_nth1 by lia. apply Ha2. lia.
    - (* the pattern ends here *)
      apply ltb_false in Eb. rewrite phi_add1 in Eb by (unfold plen in Hid; rewrite Hdm; lia).
      assert (Eb' : (Z.of_nat (S d) <? plen i)%Z = false) by (apply Z.ltb_ge; unfold plen; lia).
      rewrite Eb', app_nil_r in HLk.
      exists W'. cbn [bt bcur bact bw]. split; [exact Ht'|]. split; [exact HPf'|]. split; [exact Hdp'|]. split; [exact HN''|].
      split; [exact Hlcur'|]. split; [exact Hlact|].
      split; [intros i' Hi'; apply (Hcur i'); [exact (proj1 (proj1 (Ld_In d i') ltac:(eapply in_firstn'; exact Hi'))) | exact Hi']|].
      split; [intros i' Hi' Hn; apply (Hcur i' Hi'); exact Hn|].
      split; [intros j Hj; apply Ha1; lia|].
      rewrite HLk. split; [exact Hw | exact Ha2].
  Qed.

  Lemma round_loop_spec : forall cap, cap = (1 + Ptot)%Z ->
    forall d dm, (φ dm) = Z.of_nat d -> forall na, (φ na) = Z.of_nat (List.length (Ld d)) ->
    forall z k km st H, gap na km = z -> (φ km) = Z.of_nat k ->
    (k <= List.length (Ld d))%nat -> RI cap d k st ->
    RI cap d (List.length (Ld d)) (round_loop pats dm na km st H).
  Proof.
    intros cap Hcap d dm Hdm na Hna z.
    induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros k km st H Hz Hkm Hk HI. rewrite round_loop_eq.
    destruct (bdec (km <? na)) as [Hlt | Hge].
    2:{ apply ltb_false in Hge. replace (List.length (Ld d)) with k by lia. exact HI. }
    pose proof (ltb_true _ _ Hlt) as Hlt'.
    pose proof (round_loop_step cap Hcap d dm Hdm na Hna k km st Hkm Hlt HI) as HS.
    pose proof m_bound as Hm. pose proof (Ld_len d) as HLd.
    assert (Hkm1 : (φ (km + 1)) = Z.of_nat (S k)) by (rewrite phi_add1; [lia | rewrite wB_val; lia]).
    unfold round_next in HS. cbv zeta in HS |- *.
    destruct (dm + 1 <? PrimString.length pats.[(bact st).[km]]);
      (eapply IH; [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | exact Hkm1 | lia | exact HS]).
  Qed.

  Definition RS (cap : Z) (d : nat) (st : bstate) : Prop :=
    exists W, TrieInv (bt st) cap W /\ Pref (bt st) W /\
    (forall x, ((φ x) < (φ (tn (bt st))))%Z -> (List.length (W x) <= d)%nat) /\
    ((φ (tn (bt st))) <= 1 + sumd d)%Z /\
    (φ (PArray.length (bcur st))) = m /\ (φ (PArray.length (bact st))) = m /\
    (forall i, ((φ i) < m)%Z ->
       ((φ ((bcur st).[i])) < (φ (tn (bt st))))%Z /\ W ((bcur st).[i]) = firstn d (pw i)) /\
    (φ (bw st)) = Z.of_nat (List.length (Ld d)) /\
    (forall j : int, ((φ j) < (φ (bw st)))%Z -> (bact st).[j] = nth (Z.to_nat (φ j)) (Ld d) 0).

  Lemma filter_filter_imp : forall (f g : int -> bool) l,
    (forall x, f x = true -> g x = true) -> filter f (filter g l) = filter f l.
  Proof.
    intros f g l H. induction l as [| a l IH]; simpl; [reflexivity|].
    destruct (g a) eqn:Eg; simpl.
    - destruct (f a); rewrite IH; reflexivity.
    - destruct (f a) eqn:Ef; [rewrite (H a Ef) in Eg; discriminate | exact IH].
  Qed.

  Lemma Lk_full : forall d, Lk d (List.length (Ld d)) = Ld (S d).
  Proof.
    intros d. unfold Lk. rewrite firstn_all. unfold Ld at 1.
    apply filter_filter_imp. intros x Hx. apply Z.ltb_lt. apply Z.ltb_lt in Hx. lia.
  Qed.

  Lemma round_step : forall cap, cap = (1 + Ptot)%Z ->
    forall d dm, (φ dm) = Z.of_nat d -> forall st, RS cap d st ->
    RS cap (S d) (round_loop pats dm (bw st) 0 (mkB (bact st) (bcur st) 0 (bt st))
                    (Zwf_well_founded 0 (gap (bw st) 0))).
  Proof.
    intros cap Hcap d dm Hdm st HS.
    destruct HS as (W & Ht & HPf & Hdp & HN & Hlc & Hla & Hc & Hw & Ha).
    assert (HI : RI cap d 0 (mkB (bact st) (bcur st) 0 (bt st))).
    { exists W. cbn [bt bcur bact bw]. split; [exact Ht|]. split; [exact HPf|].
      split; [intros x Hx; specialize (Hdp x Hx); lia|].
      split; [lia|]. split; [exact Hlc|]. split; [exact Hla|].
      split; [intros i []|].
      split; [intros i Hi _; exact (Hc i Hi)|].
      split; [intros j Hj; apply Ha; lia|].
      split; [reflexivity|]. intros j Hj. rewrite phi0 in Hj. pose proof (phi_bnd j). lia. }
    pose proof (round_loop_spec cap Hcap d dm Hdm (bw st) Hw _ 0%nat 0
                  (mkB (bact st) (bcur st) 0 (bt st)) (Zwf_well_founded 0 (gap (bw st) 0))
                  eq_refl phi0 ltac:(lia) HI) as HR.
    set (st' := round_loop _ _ _ _ _ _) in *.
    destruct HR as (W' & Ht' & HPf' & Hdp' & HN' & Hlc' & Hla' & Hc1 & Hc2 & _ & Hw' & Ha2).
    exists W'. split; [exact Ht'|]. split; [exact HPf'|]. split; [exact Hdp'|].
    split; [rewrite sumd_S; lia|]. split; [exact Hlc'|]. split; [exact Hla'|].
    split.
    - intros i Hi. destruct (in_dec int_eq_dec i (Ld d)) as [Hin | Hnin].
      + apply Hc1. rewrite firstn_all. exact Hin.
      + rewrite firstn_all in Hc2. destruct (Hc2 i Hi Hnin) as [H1 H2].
        split; [exact H1|]. rewrite H2.
        assert (Hp : (plen i <= Z.of_nat d)%Z).
        { destruct (Z_le_gt_dec (plen i) (Z.of_nat d)) as [|Hg]; [assumption|].
          exfalso. apply Hnin. apply Ld_In. lia. }
        pose proof (plen_len i). rewrite !firstn_all2 by lia. reflexivity.
    - rewrite <- Lk_full. split; [exact Hw' | exact Ha2].
  Qed.

  Lemma rounds_spec : forall cap, cap = (1 + Ptot)%Z ->
    forall L, (forall i, ((φ i) < m)%Z -> (plen i <= (φ L))%Z) ->
    forall z d dm st H, gap L dm = z -> (φ dm) = Z.of_nat d -> (Z.of_nat d <= (φ L))%Z ->
    RS cap d st ->
    exists W, TrieInv (bt (rounds pats L dm st H)) cap W /\ Pref (bt (rounds pats L dm st H)) W /\
      (φ (PArray.length (bcur (rounds pats L dm st H)))) = m /\
      forall i, ((φ i) < m)%Z ->
        ((φ ((bcur (rounds pats L dm st H)).[i])) < (φ (tn (bt (rounds pats L dm st H)))))%Z /\
        W ((bcur (rounds pats L dm st H)).[i]) = pw i.
  Proof.
    intros cap Hcap L HL z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros d dm st H Hz Hdm HdL HS. rewrite rounds_eq.
    destruct (bdec (dm <? L)) as [Hlt | Hge].
    - pose proof (ltb_true _ _ Hlt) as Hlt'. cbv zeta.
      eapply IH; [ | reflexivity | | | apply (round_step cap Hcap d dm Hdm st HS)].
      + rewrite <- Hz. apply dec_step. exact Hlt.
      + rewrite phi_add1 by (pose proof (phi_bnd L); lia). lia.
      + rewrite Nat2Z.inj_succ. lia.
    - apply ltb_false in Hge.
      destruct HS as (W & Ht & HPf & _ & _ & Hlc & _ & Hc & _).
      exists W. split; [exact Ht|]. split; [exact HPf|]. split; [exact Hlc|].
      intros i Hi. destruct (Hc i Hi) as [H1 H2]. split; [exact H1|].
      rewrite H2. apply firstn_all2. pose proof (plen_len i). pose proof (HL i Hi). lia.
  Qed.

  Lemma iseq_S : forall k, (0 <= k)%Z -> iseq (k + 1) = iseq k ++ [of_Z k].
  Proof.
    intros k Hk. unfold iseq. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
    rewrite seq_S, map_app. simpl. f_equal. f_equal. f_equal. lia.
  Qed.

  Lemma iseq_nth : forall k (j : int), ((φ j) < k)%Z -> (k < wB)%Z ->
    nth (Z.to_nat (φ j)) (iseq k) 0 = j.
  Proof.
    intros k j Hj Hk. unfold iseq. pose proof (phi_bnd j).
    set (g := fun k0 : nat => of_Z (Z.of_nat k0)).
    rewrite nth_indep with (d' := g 0%nat) by (rewrite length_map, length_seq; lia).
    rewrite map_nth, seq_nth by lia. unfold g. apply phi_inj. rewrite phi_of_Z; lia.
  Qed.

  Lemma zsum_iseq_mono : forall (f : int -> Z), (forall i, (0 <= f i)%Z) ->
    forall n r, (zsum f (iseq (Z.of_nat n)) <= zsum f (iseq (Z.of_nat (n + r))))%Z.
  Proof.
    intros f Hf n r. induction r as [| r IH]; [rewrite Nat.add_0_r; lia|].
    replace (Z.of_nat (n + S r)) with (Z.of_nat (n + r) + 1)%Z by lia.
    rewrite iseq_S, zsum_app by lia. simpl. pose proof (Hf (of_Z (Z.of_nat (n + r)))). lia.
  Qed.

  Lemma zsum_iseq_le : forall (f : int -> Z), (forall i, (0 <= f i)%Z) ->
    forall k, (0 <= k <= m)%Z -> (zsum f (iseq k) <= zsum f (iseq m))%Z.
  Proof.
    intros f Hf k Hk. pose proof m_bound.
    replace k with (Z.of_nat (Z.to_nat k)) by lia.
    replace m with (Z.of_nat (Z.to_nat k + (Z.to_nat m - Z.to_nat k))) by lia.
    apply zsum_iseq_mono. exact Hf.
  Qed.

  Lemma sums_eq : forall mm i P L H,
    sums pats mm i P L H =
    match bdec (i <? mm) with
    | left Hi =>
        let l := PrimString.length pats.[i] in
        sums pats mm (i + 1) (P + l) (if L <? l then l else L)
          (Acc_inv H (dec_step mm i Hi))
    | right _ => (P, L)
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Lemma sums_spec : (Ptot < 4194303)%Z ->
    forall z i P L H, gap (PArray.length pats) i = z -> ((φ i) <= m)%Z ->
    (φ P) = zsum plen (iseq (φ i)) ->
    (forall i', ((φ i') < (φ i))%Z -> (plen i' <= (φ L))%Z) ->
    (φ (fst (sums pats (PArray.length pats) i P L H))) = Ptot /\
    forall i', ((φ i') < m)%Z -> (plen i' <= (φ (snd (sums pats (PArray.length pats) i P L H))))%Z.
  Proof.
    intros HP z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros i P L H Hz Hi HPi HLi. rewrite sums_eq.
    pose proof m_bound as Hm.
    destruct (bdec (i <? PArray.length pats)) as [Hlt | Hge].
    - pose proof (ltb_true _ _ Hlt) as Hlt'. cbv zeta. fold m in Hlt'.
      pose proof (phi_bnd i).
      assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply phi_add1; rewrite wB_val; lia).
      assert (HS : zsum plen (iseq ((φ i) + 1)) = (zsum plen (iseq (φ i)) + plen i)%Z).
      { rewrite iseq_S, zsum_app by lia. simpl. rewrite of_to_Z. lia. }
      assert (Hle : (zsum plen (iseq ((φ i) + 1)) <= Ptot)%Z)
        by (apply zsum_iseq_le; [intros j; apply plen_bnd | lia]).
      pose proof (zsum_nonneg plen (iseq (φ i)) (fun j _ => proj1 (plen_bnd j))).
      apply IH with (y := gap (PArray.length pats) (i + 1)); [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | lia | |].
      + rewrite Hi1, HS, add_spec, HPi.
        change (φ (PrimString.length pats.[i])) with (plen i).
        apply Z.mod_small. pose proof (plen_bnd i). rewrite HS in Hle. rewrite wB_val. lia.
      + intros i' Hi'. rewrite Hi1 in Hi'.
        destruct (L <? PrimString.length pats.[i]) eqn:EL.
        * apply ltb_true in EL. destruct (int_eq_dec i' i) as [-> | Hne]; [unfold plen; lia|].
          pose proof (neq_phi _ _ Hne). pose proof (HLi i' ltac:(lia)). lia.
        * apply ltb_false in EL. destruct (int_eq_dec i' i) as [-> | Hne]; [unfold plen; lia|].
          pose proof (neq_phi _ _ Hne). apply HLi. lia.
    - apply ltb_false in Hge. fold m in Hge. simpl.
      replace (φ i) with m in HPi by lia.
      split; [exact HPi|]. intros i' Hi'. apply HLi. lia.
  Qed.

  Lemma iota_eq : forall mm i a H,
    iota mm i a H =
    match bdec (i <? mm) with
    | left Hi => iota mm (i + 1) a.[i <- i] (Acc_inv H (dec_step mm i Hi))
    | right _ => a
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Lemma iota_spec : forall mm z i a H, gap mm i = z ->
    PArray.length a = mm -> ((φ i) <= (φ mm))%Z ->
    (forall j, ((φ j) < (φ i))%Z -> a.[j] = j) ->
    PArray.length (iota mm i a H) = mm /\
    forall j, ((φ j) < (φ mm))%Z -> (iota mm i a H).[j] = j.
  Proof.
    intros mm z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros i a H Hz Ha Hi Hj. rewrite iota_eq.
    destruct (bdec (i <? mm)) as [Hlt | Hge].
    - pose proof (ltb_true _ _ Hlt) as Hlt'. pose proof (ilen_bound a).
      assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply phi_add1; rewrite wB_val; lia).
      apply IH with (y := gap mm (i + 1)); [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | rewrite alength_set; exact Ha | lia |].
      intros j Hj'. rewrite Hi1 in Hj'. destruct (int_eq_dec j i) as [-> | Hne].
      + apply aget_set_same. rewrite Ha. exact Hlt'.
      + rewrite aget_set_other by (intro F; apply Hne; symmetry; exact F).
        pose proof (neq_phi _ _ Hne). apply Hj. lia.
    - apply ltb_false in Hge. split; [exact Ha|]. intros j Hj'. apply Hj. lia.
  Qed.

  Lemma filter_all : forall (f : int -> bool) l, (forall x, In x l -> f x = true) -> filter f l = l.
  Proof.
    intros f l H. induction l as [| a l IH]; simpl; [reflexivity|].
    rewrite (H a (or_introl eq_refl)). rewrite IH; [reflexivity|]. intros x Hx. apply H. right. exact Hx.
  Qed.

  Lemma Ld0 : (forall i, ((φ i) < m)%Z -> (0 < plen i)%Z) -> Ld 0 = iseq m.
  Proof.
    intros Hp. unfold Ld. apply filter_all. intros x Hx.
    apply iseq_In in Hx; [|pose proof m_bound; rewrite wB_val; lia].
    apply Z.ltb_lt. apply Hp. exact Hx.
  Qed.

  (* The whole construction. *)
  Lemma build_spec :
    (forall i, ((φ i) < m)%Z -> (0 < plen i)%Z) -> (Ptot < 4194303)%Z ->
    let mm := PArray.length pats in
    let PL := sums pats mm 0 0 0 (Zwf_well_founded 0 (gap mm 0)) in
    let cap := fst PL + 1 in
    let L := snd PL in
    let t0 := mkT (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0)
                  (PArray.make cap 0) (PArray.make cap 0) 1 in
    let act0 := iota mm 0 (PArray.make mm 0) (Zwf_well_founded 0 (gap mm 0)) in
    let st := rounds pats L 0 (mkB act0 (PArray.make mm 0) mm t0)
                (Zwf_well_founded 0 (gap L 0)) in
    (φ cap) = (1 + Ptot)%Z /\
    exists W, TrieInv (bt st) (1 + Ptot) W /\ Pref (bt st) W /\
      (φ (PArray.length (bcur st))) = m /\
      forall i, ((φ i) < m)%Z ->
        ((φ ((bcur st).[i])) < (φ (tn (bt st))))%Z /\ W ((bcur st).[i]) = pw i.
  Proof.
    intros Hpos HP. cbv zeta.
    pose proof m_bound as Hm.
    pose proof (zsum_nonneg plen (iseq m) (fun j _ => proj1 (plen_bnd j))) as HP0.
    fold Ptot in HP0.
    destruct (sums_spec HP _ 0 0 0 (Zwf_well_founded 0 (gap (PArray.length pats) 0)) eq_refl
                ltac:(rewrite phi0; lia) ltac:(rewrite phi0; reflexivity)
                ltac:(intros i' Hi'; rewrite phi0 in Hi'; pose proof (phi_bnd i'); lia)) as [HPs HLs].
    set (PL := sums _ _ _ _ _ _) in *.
    assert (Hcap : (φ (fst PL + 1)) = (1 + Ptot)%Z) by (rewrite phi_add1; [lia | rewrite wB_val; lia]).
    split; [exact Hcap|].
    set (cap := fst PL + 1) in *.
    assert (Hmk : forall b : int, PArray.length (PArray.make cap b) = cap) by (intros b; apply amake_len; lia).
    assert (Hmm : PArray.length (PArray.make (PArray.length pats) 0) = PArray.length pats).
    { apply amake_len. exact (proj2 m_bound). }
    destruct (iota_spec (PArray.length pats) _ 0 (PArray.make (PArray.length pats) 0)
                (Zwf_well_founded 0 (gap (PArray.length pats) 0)) eq_refl Hmm
                ltac:(rewrite phi0; pose proof (phi_bnd (PArray.length pats)); lia)
                ltac:(intros j Hj; rewrite phi0 in Hj; pose proof (phi_bnd j); lia)) as [Hla Hia].
    set (act0 := iota _ _ _ _) in *.
    set (t0 := mkT _ _ _ _ _ 1).
    assert (HS0 : RS (1 + Ptot) 0 (mkB act0 (PArray.make (PArray.length pats) 0) (PArray.length pats) t0)).
    { exists (fun _ => []). cbn [bt bcur bact bw]. unfold t0. cbn [tn tchr tpar tfc tns tdep].
      split; [constructor; cbn [tn tchr tpar tfc tns tdep] |].
      - rewrite Hmk. exact Hcap.
      - rewrite Hmk. exact Hcap.
      - rewrite Hmk. exact Hcap.
      - rewrite Hmk. exact Hcap.
      - rewrite Hmk. exact Hcap.
      - rewrite phi1. lia.
      - reflexivity.
      - intros v Hv. rewrite phi1 in Hv. lia.
      - intros v Hv. rewrite aget_make. reflexivity.
      - intros u v Hu Hv _. rewrite phi1 in Hu, Hv. apply phi_inj.
        pose proof (phi_bnd u). pose proof (phi_bnd v). lia.
      - intros u v _ _ _. reflexivity.
      - intros v Hv. rewrite phi1 in Hv. lia.
      - intros u Hu v. rewrite aget_make. split; [intros F; exfalso; exact (Reach_0 _ _ F)|].
        rewrite phi1. lia.
      - intros u _. apply aget_make.
      - split; [intros x _; left; reflexivity|].
        split; [intros x _; simpl; lia|].
        split; [rewrite phi1, sumd_0; lia|].
        split; [rewrite Hmm; reflexivity|].
        split; [unfold m; exact (f_equal to_Z Hla)|].
        split; [intros i Hi; rewrite aget_make, phi0, phi1; split; [lia | reflexivity]|].
        split; [rewrite (Ld0 Hpos), iseq_len, Z2Nat.id by lia; reflexivity|].
        intros j Hj. rewrite (Ld0 Hpos). unfold act0. rewrite Hia by exact Hj.
        symmetry. apply iseq_nth; [exact Hj | rewrite wB_val; lia]. }
    assert (HLb : forall i, ((φ i) < m)%Z -> (plen i <= (φ (snd PL)))%Z) by exact HLs.
    exact (rounds_spec (1 + Ptot) eq_refl (snd PL) HLb _ 0%nat 0 _ (Zwf_well_founded 0 (gap (snd PL) 0))
             eq_refl phi0 ltac:(pose proof (phi_bnd (snd PL)); lia) HS0).
  Qed.

  (* ---------------------------------------------------------------- *)
  (* The automaton, over the finished trie                             *)
  (* ---------------------------------------------------------------- *)

  Section Auto.
  Variable t : trie.
  Variable cap : Z.
  Variable W : int -> list Z.
  Variable cur : array int.
  Hypothesis Ht : TrieInv t cap W.
  Hypothesis Hlcur : (φ (PArray.length cur)) = m.
  Hypothesis Hcur : forall i, ((φ i) < m)%Z -> ((φ (cur.[i])) < (φ (tn t)))%Z /\ W (cur.[i]) = pw i.
  Hypothesis Hpos : forall i, ((φ i) < m)%Z -> (0 < plen i)%Z.
  Hypothesis Hm1 : (m < 4194303)%Z.

  Let N := tn t.

  Lemma plist_loop_eq : forall mm i fp np H,
    plist_loop cur mm i fp np H =
    match bdec (i <? mm) with
    | left Hi =>
        let v := cur.[i] in
        let old := fp.[v] in
        plist_loop cur mm (i + 1) fp.[v <- i + 1] np.[i + 1 <- old]
          (Acc_inv H (dec_step mm i Hi))
    | right _ => (fp, np)
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Definition PLI (i : Z) (fp np : array int) : Prop :=
    (φ (PArray.length fp)) = cap /\ (φ (PArray.length np)) = (m + 1)%Z /\
    (forall v, ((φ v) < (φ N))%Z -> forall e,
       Reach np (fp.[v]) e <-> ((1 <= (φ e) <= i)%Z /\ cur.[e - 1] = v)) /\
    (forall e, (1 <= (φ e) <= i)%Z -> ((φ (np.[e])) < (φ e))%Z) /\
    (forall v, ((φ v) < (φ N))%Z -> ((φ (fp.[v])) <= i)%Z).

  Lemma phi_sub1 : forall e : int, (1 <= (φ e))%Z -> (φ (e - 1)) = ((φ e) - 1)%Z.
  Proof. intros e He. sia. Qed.

  Lemma plist_loop_spec : forall z i fp np H, gap (PArray.length pats) i = z ->
    ((φ i) <= m)%Z -> PLI (φ i) fp np ->
    PLI m (fst (plist_loop cur (PArray.length pats) i fp np H))
          (snd (plist_loop cur (PArray.length pats) i fp np H)).
  Proof.
    intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros i fp np H Hz Hi HI. rewrite plist_loop_eq.
    pose proof m_bound as Hm.
    destruct (bdec (i <? PArray.length pats)) as [Hlt | Hge].
    2:{ apply ltb_false in Hge. fold m in Hge. simpl. replace m with (φ i) by lia. exact HI. }
    pose proof (ltb_true _ _ Hlt) as Hlt'. fold m in Hlt'. cbv zeta.
    destruct HI as (Hlf & Hln & P1 & P2 & P3).
    pose proof (phi_bnd i).
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply phi_add1; rewrite wB_val; lia).
    destruct (Hcur i Hlt') as [Hv _].
    set (v := cur.[i]) in *.
    pose proof (ti_n _ _ _ Ht) as HN. fold N in HN.
    assert (He1 : (i + 1) - 1 = i) by (apply phi_inj; rewrite phi_sub1; lia).
    apply IH with (y := gap (PArray.length pats) (i + 1));
      [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | lia |].
    rewrite Hi1. split; [|split; [|split; [|split]]].
    - rewrite alength_set. exact Hlf.
    - rewrite alength_set. exact Hln.
    - intros v' Hv' e.
      assert (Hfr : forall a, ((φ a) <= (φ i))%Z ->
                (forall x, Reach np a x -> x <> i + 1)).
      { intros a Ha x Hr F. subst x.
        pose proof (Reach_le np (φ i) (fun x Hx => P2 x ltac:(lia)) a (i + 1) Ha Hr). lia. }
      destruct (int_eq_dec v' v) as [-> | Hne].
      + rewrite aget_set_same by lia.
        assert (He0 : i + 1 <> 0) by (apply nz_of_pos; lia).
        rewrite (Reach_cons _ _ e He0). rewrite aget_set_same by lia.
        rewrite (Reach_frame np (fp.[v]) (i + 1) (fp.[v]) e (Hfr _ (P3 v Hv))).
        rewrite (P1 v Hv e). split.
        * intros [-> | [H1 H2]]; [split; [lia | rewrite He1; reflexivity] | split; [lia | exact H2]].
        * intros [H1 H2]. destruct (Z.eq_dec (φ e) ((φ i) + 1)) as [E | E].
          -- left. apply phi_inj. rewrite Hi1. exact E.
          -- right. split; [lia | exact H2].
      + rewrite aget_set_other by (intro F; apply Hne; symmetry; exact F).
        rewrite (Reach_frame np (fp.[v']) (i + 1) (fp.[v]) e (Hfr _ (P3 v' Hv'))).
        rewrite (P1 v' Hv' e). split.
        * intros [H1 H2]. split; [lia | exact H2].
        * intros [H1 H2]. split; [|exact H2].
          destruct (Z.eq_dec (φ e) ((φ i) + 1)) as [E | E]; [|lia].
          exfalso. apply Hne.
          assert (Hei : e - 1 = i) by (apply phi_inj; rewrite phi_sub1 by lia; lia).
          rewrite <- H2, Hei. reflexivity.
    - intros e He. destruct (int_eq_dec e (i + 1)) as [-> | Hne].
      + rewrite aget_set_same by lia. pose proof (P3 v Hv). lia.
      + rewrite aget_set_other by (intro F; apply Hne; symmetry; exact F).
        apply P2. assert ((φ e) <> (φ i) + 1)%Z by (intro F; apply Hne; apply phi_inj; lia). lia.
    - intros v' Hv'. destruct (int_eq_dec v' v) as [-> | Hne].
      + rewrite aget_set_same by lia. lia.
      + rewrite aget_set_other by (intro F; apply Hne; symmetry; exact F).
        pose proof (P3 v' Hv'). lia.
  Qed.

  Section Links.
  Variables fp np : array int.
  Hypothesis Hlfp : (φ (PArray.length fp)) = cap.
  Hypothesis HP1 : forall v, ((φ v) < (φ N))%Z -> forall e,
    Reach np (fp.[v]) e <-> ((1 <= (φ e) <= m)%Z /\ cur.[e - 1] = v).
  Hypothesis HP2 : forall e, (1 <= (φ e) <= m)%Z -> ((φ (np.[e])) < (φ e))%Z.

  Definition Term (x : int) : Prop := exists i, ((φ i) < m)%Z /\ cur.[i] = x.

  Lemma term_fp : forall v, ((φ v) < (φ N))%Z -> (fp.[v] <> 0 <-> Term v).
  Proof.
    intros v Hv. split.
    - intros Hn. assert (Hr : Reach np (fp.[v]) (fp.[v])) by (constructor; exact Hn).
      apply (HP1 v Hv) in Hr as [H1 H2]. exists (fp.[v] - 1). split; [|exact H2].
      rewrite phi_sub1 by lia. lia.
    - intros [i [Hi Hc]] E. pose proof (phi_bnd i).
      assert (Hr : (1 <= (φ (i + 1)) <= m)%Z /\ cur.[(i + 1) - 1] = v).
      { assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply phi_add1; rewrite wB_val; lia).
        split; [lia|]. replace ((i + 1) - 1) with i; [exact Hc|].
        apply phi_inj. rewrite phi_sub1; lia. }
      apply (HP1 v Hv) in Hr. rewrite E in Hr. exact (Reach_0 _ _ Hr).
  Qed.

  Lemma term_word : forall x, ((φ x) < (φ N))%Z -> Term x -> exists i, ((φ i) < m)%Z /\ W x = pw i.
  Proof.
    intros x Hx [i [Hi Hc]]. exists i. split; [exact Hi|].
    destruct (Hcur i Hi) as [_ E]. rewrite <- Hc. exact E.
  Qed.

  Lemma pw_term : forall i x, ((φ i) < m)%Z -> ((φ x) < (φ N))%Z -> W x = pw i -> Term x.
  Proof.
    intros i x Hi Hx E. exists i. split; [exact Hi|].
    destruct (Hcur i Hi) as [H1 H2]. apply (ti_inj _ _ _ Ht); [exact H1 | exact Hx | congruence].
  Qed.

  Lemma pw_node : forall i, ((φ i) < m)%Z -> IsNode t W (pw i).
  Proof. intros i Hi. destruct (Hcur i Hi) as [H1 H2]. exists (cur.[i]). split; assumption. Qed.

  Definition FailOK (fl : array int) (x : int) : Prop :=
    ((φ (fl.[x])) < (φ N))%Z /\ suffix (W (fl.[x])) (W x) /\
    (List.length (W (fl.[x])) < List.length (W x))%nat /\
    forall y, suffix y (W x) -> (List.length y < List.length (W x))%nat -> IsNode t W y ->
      (List.length y <= List.length (W (fl.[x])))%nat.

  Definition OutOK (out : array int) (x : int) : Prop :=
    ((φ (out.[x])) < (φ N))%Z /\
    (out.[x] <> 0 -> Term (out.[x]) /\ suffix (W (out.[x])) (W x) /\
                    (List.length (W (out.[x])) < List.length (W x))%nat) /\
    (forall i, ((φ i) < m)%Z -> suffix (pw i) (W x) ->
       (List.length (pw i) < List.length (W x))%nat ->
       (List.length (pw i) <= List.length (W (out.[x])))%nat).

  Lemma walk_eq : forall fl c x H,
    walk t fl c x H =
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
  Proof. intros. destruct H. reflexivity. Qed.

  Lemma walk_spec : forall fl X c (B : nat),
    (forall x, (0 < (φ x) < (φ N))%Z -> (List.length (W x) < B)%nat -> FailOK fl x) ->
    forall z x H, (φ x) = z -> ((φ x) < (φ N))%Z -> suffix (W x) X -> (List.length (W x) < B)%nat ->
    (forall y, suffix y X -> (List.length y < B)%nat -> IsNode t W (y ++ [(φ c)]) ->
       (List.length y <= List.length (W x))%nat) ->
    ((φ (walk t fl c x H)) < (φ N))%Z /\
    (W (walk t fl c x H) = [] \/
     exists y, W (walk t fl c x H) = y ++ [(φ c)] /\ suffix y X /\ (List.length y < B)%nat) /\
    (forall y, suffix y X -> (List.length y < B)%nat -> IsNode t W (y ++ [(φ c)]) ->
       (S (List.length y) <= List.length (W (walk t fl c x H)))%nat).
  Proof.
    intros fl X c B HF z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros x H Hz Hx HxX HxB Hmax. rewrite walk_eq. cbv zeta.
    destruct (lookup_spec t cap W x c Ht Hx) as [L1 L2].
    pose proof (ti_n _ _ _ Ht) as HN. fold N in HN.
    destruct (bdec (lookup t x c =? 0)) as [E | E].
    - apply eqb_true in E. specialize (L2 E).
      destruct (bdec (x =? 0)) as [E0 | E0].
      + apply eqb_true in E0. subst x. rewrite (ti_root _ _ _ Ht) in *.
        split; [rewrite phi0; lia|]. split; [left; reflexivity|].
        intros y Hy HyB Hn. exfalso. specialize (Hmax y Hy HyB Hn). simpl in Hmax.
        destruct y; [|simpl in Hmax; lia]. exact (L2 Hn).
      + apply eqb_false in E0. pose proof (pos_of_nz x E0) as Hx0.
        destruct (HF x ltac:(lia) HxB) as (Hf1 & Hf2 & Hf3 & Hf4).
        assert (Hfx : ((φ (fl.[x])) < (φ x))%Z) by (apply (ti_lt _ _ _ _ _ Ht); [exact Hf1 | exact Hx | exact Hf3]).
        destruct (bdec (fl.[x] <? x)) as [Hlt | Hge].
        2:{ exfalso. apply ltb_false in Hge. lia. }
        apply IH with (y := (φ (fl.[x]))); [rewrite <- Hz; apply dec_lt; exact Hlt | reflexivity | exact Hf1 | | lia |].
        * exact (suffix_trans _ _ _ Hf2 HxX).
        * intros y Hy HyB Hn. pose proof (Hmax y Hy HyB Hn) as Hle.
          pose proof (suffix_both y (W x) X Hy HxX Hle) as Hyx.
          destruct (Nat.eq_dec (List.length y) (List.length (W x))) as [Eq | Ne].
          -- exfalso. apply L2. rewrite <- (suffix_eq y (W x) X Hy HxX Eq). exact Hn.
          -- apply Hf4; [exact Hyx | lia | exact (isnode_prefix _ _ _ _ _ Ht Hn)].
    - apply eqb_false in E. destruct (L1 E) as [Hy Ew].
      split; [lia|]. split; [right; exists (W x); split; [exact Ew | split; assumption]|].
      intros y Hy2 HyB Hn. rewrite Ew, length_app. simpl. pose proof (Hmax y Hy2 HyB Hn). lia.
  Qed.

  Lemma fail_loop_eq : forall fp' NN v fl out H,
    fail_loop t fp' NN v fl out H =
    match bdec (v <? NN) with
    | left Hv =>
        let u := (tpar t).[v] in
        let c := (tchr t).[v] in
        let f := if u =? 0 then 0
                 else let x := fl.[u] in walk t fl c x (Zwf_well_founded 0 (φ x)) in
        let o := if fp'.[f] =? 0 then out.[f] else f in
        fail_loop t fp' NN (v + 1) fl.[v <- f] out.[v <- o]
          (Acc_inv H (dec_step NN v Hv))
    | right _ => (fl, out)
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Definition FI (v : Z) (fl out : array int) : Prop :=
    (φ (PArray.length fl)) = cap /\ (φ (PArray.length out)) = cap /\
    (forall x, (0 < (φ x) < v)%Z -> FailOK fl x) /\
    (forall x, ((φ x) < v)%Z -> OutOK out x).

  Lemma FailOK_set : forall fl x v f, x <> v -> FailOK fl x -> FailOK fl.[v <- f] x.
  Proof.
    intros fl x v f Hne H. unfold FailOK in *.
    rewrite aget_set_other by (intro F; apply Hne; symmetry; exact F). exact H.
  Qed.

  Lemma OutOK_set : forall out x v o, x <> v -> OutOK out x -> OutOK out.[v <- o] x.
  Proof.
    intros out x v o Hne H. unfold OutOK in *.
    rewrite aget_set_other by (intro F; apply Hne; symmetry; exact F). exact H.
  Qed.

  Lemma fail_loop_spec : forall z v fl out H, gap N v = z ->
    (1 <= (φ v) <= (φ N))%Z -> FI (φ v) fl out ->
    FI (φ N) (fst (fail_loop t fp N v fl out H)) (snd (fail_loop t fp N v fl out H)).
  Proof.
    intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros v fl out H Hz Hv HI. rewrite fail_loop_eq.
    pose proof (ti_n _ _ _ Ht) as HN. fold N in HN. pose proof (ti_cap _ _ _ Ht) as Hcap4.
    destruct (bdec (v <? N)) as [Hlt | Hge].
    2:{ apply ltb_false in Hge. simpl. replace (φ N) with (φ v) by lia. exact HI. }
    pose proof (ltb_true _ _ Hlt) as Hlt'. cbv zeta.
    destruct HI as (Hlfl & Hlout & HF & HO).
    assert (Hv1 : (φ (v + 1)) = ((φ v) + 1)%Z) by (apply phi_add1; rewrite wB_val; lia).
    destruct (ti_par _ _ _ Ht v ltac:(lia)) as [Hpu Ewv].
    set (u := (tpar t).[v]) in *. set (c := (tchr t).[v]) in *.
    pose proof (phi_bnd u) as Hu0.
    assert (HlWv : List.length (W v) = S (List.length (W u))) by (rewrite Ewv, length_app; simpl; lia).
    (* the failure link of v *)
    set (f := if u =? 0 then 0 else walk t fl c (fl.[u]) (Zwf_well_founded 0 (φ (fl.[u])))).
    assert (HFv : ((φ f) < (φ N))%Z /\ suffix (W f) (W v) /\ (List.length (W f) < List.length (W v))%nat /\
       forall y, suffix y (W v) -> (List.length y < List.length (W v))%nat -> IsNode t W y ->
         (List.length y <= List.length (W f))%nat).
    { unfold f. destruct (u =? 0) eqn:Eu.
      - apply eqb_true in Eu. rewrite Eu in Ewv, HlWv. rewrite (ti_root _ _ _ Ht) in *.
        split; [rewrite phi0; lia|]. split; [apply suffix_nil|]. split; [simpl; lia|].
        intros y _ Hy _. simpl in *. lia.
      - apply eqb_false in Eu. pose proof (pos_of_nz u Eu).
        destruct (HF u ltac:(lia)) as (Hf1 & Hf2 & Hf3 & Hf4).
        destruct (walk_spec fl (W u) c (List.length (W u))
                   ltac:(intros x Hx HxB; apply HF; split; [lia|];
                         apply (ti_lt _ _ _ _ _ Ht); [lia | lia | lia])
                   _ (fl.[u]) (Zwf_well_founded 0 (φ (fl.[u]))) eq_refl Hf1 Hf2 Hf3
                   ltac:(intros y Hy HyB Hn; apply Hf4; [exact Hy | exact HyB | exact (isnode_prefix _ _ _ _ _ Ht Hn)]))
          as (Hr1 & Hr2 & Hr3).
        set (r := walk _ _ _ _ _) in *.
        split; [exact Hr1|]. split; [|split].
        + destruct Hr2 as [E | (y & E & Hy & HyB)]; rewrite E; [apply suffix_nil|].
          rewrite Ewv. apply suffix_snoc. split; [reflexivity | exact Hy].
        + destruct Hr2 as [E | (y & E & Hy & HyB)]; rewrite E; simpl; [lia|].
          rewrite length_app. simpl. lia.
        + intros y' Hy' Hl Hn. rewrite Ewv in Hy'.
          destruct (suffix_snoc_cases y' (W u) (φ c) Hy') as [-> | (y & -> & Hy)]; [simpl; lia|].
          rewrite length_app in Hl |- *. simpl in Hl |- *.
          pose proof (Hr3 y Hy ltac:(lia) Hn). lia. }
    destruct HFv as (Hf1 & Hf2 & Hf3 & Hf4).
    assert (Hfv : ((φ f) < (φ v))%Z) by (apply (ti_lt _ _ _ _ _ Ht); [exact Hf1 | lia | exact Hf3]).
    destruct (HO f Hfv) as (Ho1 & Ho2 & Ho3).
    set (o := if fp.[f] =? 0 then out.[f] else f).
    assert (Hpw_f : forall i, ((φ i) < m)%Z -> suffix (pw i) (W v) ->
              (List.length (pw i) < List.length (W v))%nat -> (List.length (pw i) <= List.length (W f))%nat)
      by (intros i Hi Hs Hl; apply Hf4; [exact Hs | exact Hl | apply pw_node; exact Hi]).
    assert (HOv : OutOK out.[v <- o] v).
    { unfold OutOK. rewrite aget_set_same by lia. unfold o.
      destruct (fp.[f] =? 0) eqn:Ef.
      - apply eqb_true in Ef.
        assert (Hnt : ~ Term f) by (intro T; apply (proj2 (term_fp f Hf1)) in T; exact (T Ef)).
        split; [exact Ho1|]. split.
        + intros Hn. destruct (Ho2 Hn) as (T & S1 & S2).
          split; [exact T|]. split; [exact (suffix_trans _ _ _ S1 Hf2) | lia].
        + intros i Hi Hs Hl. pose proof (Hpw_f i Hi Hs Hl) as Hle.
          pose proof (suffix_both _ _ _ Hs Hf2 Hle) as Hsf.
          destruct (Nat.eq_dec (List.length (pw i)) (List.length (W f))) as [Eq | Ne].
          * exfalso. apply Hnt. apply (pw_term i f Hi Hf1).
            symmetry. exact (suffix_eq _ _ _ Hs Hf2 Eq).
          * apply Ho3; [exact Hi | exact Hsf | lia].
      - apply eqb_false in Ef.
        split; [exact Hf1|]. split.
        + intros _. split; [apply (term_fp f Hf1); exact Ef | split; [exact Hf2 | exact Hf3]].
        + exact Hpw_f. }
    apply IH with (y := gap N (v + 1)); [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | lia |].
    rewrite Hv1. split; [rewrite alength_set; exact Hlfl|]. split; [rewrite alength_set; exact Hlout|].
    split.
    - intros x Hx. destruct (int_eq_dec x v) as [-> | Hne].
      + unfold FailOK. rewrite aget_set_same by lia. split; [exact Hf1|]. split; [exact Hf2|].
        split; [exact Hf3 | exact Hf4].
      + apply FailOK_set; [exact Hne|]. apply HF. pose proof (neq_phi _ _ Hne). lia.
    - intros x Hx. destruct (int_eq_dec x v) as [-> | Hne]; [exact HOv|].
      apply OutOK_set; [exact Hne|]. apply HO. pose proof (neq_phi _ _ Hne). lia.
  Qed.

  (* -------------------------------------------------------------- *)
  (* The text pass                                                   *)
  (* -------------------------------------------------------------- *)

  Definition suffixb (y X : list Z) : bool :=
    if list_eq_dec Z.eq_dec (skipn (List.length X - List.length y) X) y
    then (List.length y <=? List.length X)%nat else false.

  Lemma suffixb_spec : forall y X, suffixb y X = true <-> suffix y X.
  Proof.
    intros y X. rewrite suffix_skipn. unfold suffixb.
    destruct (list_eq_dec Z.eq_dec _ _) as [E | E].
    - rewrite Nat.leb_le. tauto.
    - split; [discriminate | tauto].
  Qed.

  Lemma Reach_trans : forall ns a b c, Reach ns a b -> Reach ns b c -> Reach ns a c.
  Proof.
    intros ns a b c H1. induction H1 as [a Ha | a b Ha H IH]; intros H2; [exact H2|].
    apply R_next; [exact Ha | apply IH; exact H2].
  Qed.

  Section ScanProof.
  Variables fl out : array int.
  Hypothesis HFI : FI (φ N) fl out.
  Variable txt : PrimString.string.

  Definition T : list Z := pstr txt.
  Definition occb (i : int) (j : nat) : bool := suffixb (pw i) (firstn (S j) T).
  Definition pos (j : nat) (i : int) : Z := (Z.of_nat j + 1 - plen i)%Z.
  Definition Acc_ (j : nat) (i : int) : list Z :=
    map (fun j' => pos j' i) (filter (occb i) (seq 0 j)).
  Definition Full (i : int) : list Z := Acc_ (List.length T) i.

  Lemma Acc_S : forall j i, Acc_ (S j) i = Acc_ j i ++ (if occb i j then [pos j i] else []).
  Proof.
    intros j i. unfold Acc_. rewrite seq_S, filter_app, map_app. simpl.
    destruct (occb i j); reflexivity.
  Qed.

  Lemma Acc_prefix : forall j i, (j <= List.length T)%nat -> exists rest, Acc_ j i ++ rest = Full i.
  Proof.
    intros j i Hj. unfold Full, Acc_.
    replace (List.length T) with (j + (List.length T - j))%nat by lia.
    rewrite seq_app, filter_app, map_app. eexists. reflexivity.
  Qed.

  Definition Longest (X : list Z) (st : int) : Prop :=
    ((φ st) < (φ N))%Z /\ suffix (W st) X /\
    forall z, ((φ z) < (φ N))%Z -> suffix (W z) X -> (List.length (W z) <= List.length (W st))%nat.

  Variable Sx : Type.
  Variable R : Sx -> (int -> list Z) -> Prop.
  Variable f : Sx -> int -> int -> Sx.
  Hypothesis R_ext : forall s A B, (forall i, ((φ i) < m)%Z -> A i = B i) -> R s A -> R s B.
  Hypothesis Hf : forall s A i p, R s A -> ((φ i) < m)%Z ->
    (exists rest, A i ++ [(φ p)] ++ rest = Full i) ->
    R (f s i p) (fun i' => if i' =? i then A i ++ [(φ p)] else A i').

  (* during the step at text position j: the patterns of E have been
     recorded at j, the others not yet *)
  Definition EmInv (j : nat) (E : int -> Prop) (s : Sx) : Prop :=
    exists A, R s A /\ forall i, ((φ i) < m)%Z ->
      (E i /\ A i = Acc_ j i ++ [pos j i]) \/ (~ E i /\ A i = Acc_ j i).

  Lemma EmInv_iff : forall j E E' s, (forall i, ((φ i) < m)%Z -> (E i <-> E' i)) ->
    EmInv j E s -> EmInv j E' s.
  Proof.
    intros j E E' s HE [A [HR HA]]. exists A. split; [exact HR|].
    intros i Hi. rewrite <- (HE i Hi). exact (HA i Hi).
  Qed.

  Lemma emit_list_eq : forall p e s H,
    emit_list Sx f np p e s H =
    match bdec (e =? 0) with
    | left _ => s
    | right _ =>
        let s' := f s (e - 1) p in
        let e' := np.[e] in
        match bdec (e' <? e) with
        | left He => emit_list Sx f np p e' s' (Acc_inv H (dec_lt e e' He))
        | right _ => s'
        end
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Lemma emit_list_spec : forall j x p (E0 : int -> Prop),
    (j < List.length T)%nat -> ((φ x) < (φ N))%Z ->
    (φ p) = (Z.of_nat j + 1 - Z.of_nat (List.length (W x)))%Z ->
    (forall i, ((φ i) < m)%Z -> E0 i -> cur.[i] <> x) ->
    (forall i, ((φ i) < m)%Z -> cur.[i] = x -> occb i j = true) ->
    forall z e s H, (φ e) = z -> (e = 0 \/ Reach np (fp.[x]) e) ->
    EmInv j (fun i => E0 i \/ (cur.[i] = x /\ ~ Reach np e (i + 1))) s ->
    EmInv j (fun i => E0 i \/ cur.[i] = x) (emit_list Sx f np p e s H).
  Proof.
    intros j x p E0 Hj Hx Hp Hdis Hocc z.
    induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros e s H Hz He HI. rewrite emit_list_eq.
    pose proof m_bound as Hm.
    destruct (bdec (e =? 0)) as [E | E].
    - apply eqb_true in E. subst e. refine (EmInv_iff j _ _ s _ HI).
      intros i Hi. split; [intros [H1 | [H1 _]]; [left | right]; assumption|].
      intros [H1 | H1]; [left; exact H1 | right; split; [exact H1 | apply Reach_0]].
    - apply eqb_false in E. cbv zeta.
      destruct He as [He | He]; [contradiction|].
      pose proof He as He'. apply (HP1 x Hx e) in He' as [He1 He2].
      set (i0 := e - 1) in *.
      assert (Hi0 : (φ i0) = ((φ e) - 1)%Z) by (apply phi_sub1; lia).
      assert (Hi0m : ((φ i0) < m)%Z) by lia.
      assert (He0 : i0 + 1 = e) by (apply phi_inj; rewrite phi_add1; [lia | rewrite wB_val; lia]).
      destruct HI as [A [HR HA]].
      assert (HAi0 : A i0 = Acc_ j i0).
      { destruct (HA i0 Hi0m) as [[[F | [_ F]] _] | [_ E2]]; [| | exact E2].
        - exfalso. exact (Hdis i0 Hi0m F He2).
        - exfalso. apply F. rewrite He0. constructor. exact E. }
      assert (Hpos0 : pos j i0 = (φ p)).
      { unfold pos. rewrite Hp. destruct (Hcur i0 Hi0m) as [_ Ew]. rewrite He2 in Ew.
        rewrite Ew, plen_len. reflexivity. }
      assert (Hpre : exists rest, A i0 ++ [(φ p)] ++ rest = Full i0).
      { destruct (Acc_prefix (S j) i0 ltac:(lia)) as [rest Hrest].
        exists rest. rewrite HAi0, <- Hrest, Acc_S, (Hocc i0 Hi0m He2), Hpos0, <- app_assoc. reflexivity. }
      pose proof (Hf s A i0 p HR Hi0m Hpre) as HR'.
      pose proof (HP2 e ltac:(lia)) as Hne.
      destruct (bdec (np.[e] <? e)) as [Hlt | Hge].
      2:{ exfalso. apply ltb_false in Hge. lia. }
      apply IH with (y := (φ (np.[e]))); [rewrite <- Hz; apply dec_lt; exact Hlt | reflexivity | |].
      + destruct (int_eq_dec (np.[e]) 0) as [E0' | E0']; [left; exact E0'|].
        right. apply (Reach_trans _ _ e); [exact He | apply R_next; [exact E | constructor; exact E0']].
      + exists (fun i' => if i' =? i0 then A i0 ++ [(φ p)] else A i'). split; [exact HR'|].
        intros i Hi. destruct (int_eq_dec i i0) as [-> | Hii].
        * rewrite eqb_refl. left. split; [right; split; [exact He2|] | rewrite HAi0, Hpos0; reflexivity].
          intro Hr. rewrite He0 in Hr.
          pose proof (Reach_le np m (fun x0 Hx0 => HP2 x0 ltac:(lia)) (np.[e]) e ltac:(lia) Hr). lia.
        * replace (i =? i0) with false by (symmetry; apply eqb_false_spec; exact Hii).
          assert (Hie : i + 1 <> e).
          { intro F. apply Hii. apply phi_inj. rewrite Hi0. rewrite <- F.
            rewrite phi_add1; [lia | rewrite wB_val; lia]. }
          assert (Hiff : Reach np e (i + 1) <-> Reach np (np.[e]) (i + 1)).
          { rewrite (Reach_cons np e (i + 1) E). split; [intros [F | F]; [contradiction | exact F] | intros F; right; exact F]. }
          destruct (HA i Hi) as [[H1 H2] | [H1 H2]]; [left | right]; (split; [|exact H2]).
          -- destruct H1 as [H1 | [H1 H3]]; [left; exact H1 | right; split; [exact H1 | rewrite <- Hiff; exact H3]].
          -- intros [H3 | [H3 H4]]; apply H1; [left; exact H3 | right; split; [exact H3 | rewrite Hiff; exact H4]].
  Qed.

  Lemma emit_chain_eq : forall je x s H,
    emit_chain Sx f t out fp np je x s H =
    match bdec (x =? 0) with
    | left _ => s
    | right _ =>
        let e := fp.[x] in
        let s' := emit_list Sx f np (je - (tdep t).[x]) e s (Zwf_well_founded 0 (φ e)) in
        let o := out.[x] in
        match bdec (o <? x) with
        | left Ho => emit_chain Sx f t out fp np je o s' (Acc_inv H (dec_lt x o Ho))
        | right _ => s'
        end
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Definition Em (q x i : int) : Prop :=
    suffix (pw i) (W q) /\ (List.length (W x) < List.length (pw i))%nat.

  Lemma emit_chain_spec : forall j q je, (j < List.length T)%nat ->
    Longest (firstn (S j) T) q -> (φ je) = (Z.of_nat j + 1)%Z ->
    forall z x s H, (φ x) = z -> ((φ x) < (φ N))%Z -> suffix (W x) (W q) ->
    EmInv j (Em q x) s ->
    EmInv j (fun i => suffix (pw i) (W q)) (emit_chain Sx f t out fp np je x s H).
  Proof.
    intros j q je Hj [Hq1 [Hq2 Hq3]] Hje z.
    induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros x s H Hz Hx Hxq HI. rewrite emit_chain_eq.
    destruct HFI as (_ & _ & _ & HO).
    pose proof m_bound as Hm.
    destruct (bdec (x =? 0)) as [E | E].
    - apply eqb_true in E. subst x. refine (EmInv_iff j _ _ s _ HI).
      intros i Hi. unfold Em. rewrite (ti_root _ _ _ Ht). simpl.
      pose proof (Hpos i Hi). pose proof (plen_len i). split; [tauto|]. intros H3. split; [exact H3 | lia].
    - apply eqb_false in E. cbv zeta. pose proof (pos_of_nz x E) as Hx0.
      assert (HlX : List.length (firstn (S j) T) = S j) by (rewrite length_firstn; lia).
      pose proof (suffix_length _ _ Hxq) as Hl1. pose proof (suffix_length _ _ Hq2) as Hl2.
      assert (Hp : (φ (je - (tdep t).[x])) = (Z.of_nat j + 1 - Z.of_nat (List.length (W x)))%Z).
      { rewrite sub_spec, (ti_dep _ _ _ Ht x Hx), Hje. apply Z.mod_small. rewrite wB_val.
        lia. }
      assert (Hdis : forall i, ((φ i) < m)%Z -> Em q x i -> cur.[i] <> x).
      { intros i Hi [_ Hlt] Hc. destruct (Hcur i Hi) as [_ Ew]. rewrite Hc in Ew. rewrite Ew in Hlt. lia. }
      assert (Hocc : forall i, ((φ i) < m)%Z -> cur.[i] = x -> occb i j = true).
      { intros i Hi Hc. unfold occb. apply suffixb_spec. destruct (Hcur i Hi) as [_ Ew].
        rewrite Hc in Ew. rewrite <- Ew. exact (suffix_trans _ _ _ Hxq Hq2). }
      assert (HI' : EmInv j (fun i => Em q x i \/ (cur.[i] = x /\ ~ Reach np (fp.[x]) (i + 1))) s).
      { refine (EmInv_iff j _ _ s _ HI). intros i Hi. split; [intros H1; left; exact H1|].
        intros [H1 | [H1 H2]]; [exact H1|]. exfalso. apply H2. apply (HP1 x Hx).
        pose proof (phi_bnd i).
        assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply phi_add1; rewrite wB_val; lia).
        split; [lia|]. replace ((i + 1) - 1) with i; [exact H1|].
        apply phi_inj. rewrite phi_sub1; lia. }
      pose proof (emit_list_spec j x _ (Em q x) Hj Hx Hp Hdis Hocc _ (fp.[x])
                    s (Zwf_well_founded 0 (φ (fp.[x]))) eq_refl
                    ltac:(destruct (int_eq_dec (fp.[x]) 0) as [E0 | E0]; [left; exact E0 | right; constructor; exact E0])
                    HI') as HL.
      set (s' := emit_list _ _ _ _ _ _ _) in *.
      destruct (HO x Hx) as (Ho1 & Ho2 & Ho3).
      assert (Hox : ((φ (out.[x])) < (φ x))%Z).
      { destruct (int_eq_dec (out.[x]) 0) as [E0 | E0]; [rewrite E0, phi0; lia|].
        destruct (Ho2 E0) as (_ & _ & Hlt). apply (ti_lt _ _ _ _ _ Ht); [exact Ho1 | exact Hx | exact Hlt]. }
      destruct (bdec (out.[x] <? x)) as [Hlt | Hge].
      2:{ exfalso. apply ltb_false in Hge. lia. }
      apply IH with (y := (φ (out.[x]))); [rewrite <- Hz; apply dec_lt; exact Hlt | reflexivity | exact Ho1 | |].
      + destruct (int_eq_dec (out.[x]) 0) as [E0 | E0]; [rewrite E0, (ti_root _ _ _ Ht); apply suffix_nil|].
        destruct (Ho2 E0) as (_ & S1 & _). exact (suffix_trans _ _ _ S1 Hxq).
      + refine (EmInv_iff j _ _ s' _ HL). intros i Hi. unfold Em.
        assert (HWo : (List.length (W (out.[x])) < List.length (W x))%nat).
        { destruct (int_eq_dec (out.[x]) 0) as [E0 | E0]; [|exact (proj2 (proj2 (Ho2 E0)))].
          rewrite E0, (ti_root _ _ _ Ht). simpl.
          destruct (List.length (W x)) eqn:El; [|lia]. exfalso.
          apply E. apply (ti_nil _ _ _ x Ht Hx). destruct (W x); [reflexivity | discriminate]. }
        destruct (Hcur i Hi) as [Hci Ewi].
        split.
        * intros [[H1 H2] | H1]; [split; [exact H1 | lia]|].
          rewrite H1 in Ewi. rewrite <- Ewi. split; [exact Hxq | exact HWo].
        * intros [H1 H2].
          destruct (Nat.lt_ge_cases (List.length (W x)) (List.length (pw i))) as [Hlt' | Hge'];
            [left; split; assumption|].
          right. pose proof (suffix_both _ _ _ H1 Hxq Hge') as Hsx.
          destruct (Nat.eq_dec (List.length (pw i)) (List.length (W x))) as [Eq | Ne].
          -- apply (ti_inj _ _ _ Ht); [exact Hci | exact Hx |].
             rewrite Ewi. exact (suffix_eq _ _ _ H1 Hxq Eq).
          -- exfalso. pose proof (Ho3 i Hi Hsx ltac:(lia)). lia.
  Qed.

  Lemma scan_eq : forall n j st s H,
    scan Sx f t fl out fp np txt n j st s H =
    match bdec (j <? n) with
    | left Hj =>
        let st' := walk t fl (PrimString.get txt j) st (Zwf_well_founded 0 (φ st)) in
        let s' := emit_chain Sx f t out fp np (j + 1) st' s (Zwf_well_founded 0 (φ st')) in
        scan Sx f t fl out fp np txt n (j + 1) st' s' (Acc_inv H (dec_step n j Hj))
    | right _ => s
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Lemma scan_spec : forall n, (φ n) = Z.of_nat (List.length T) ->
    forall z jm j st s H, gap n jm = z -> (φ jm) = Z.of_nat j -> (j <= List.length T)%nat ->
    Longest (firstn j T) st -> R s (Acc_ j) ->
    R (scan Sx f t fl out fp np txt n jm st s H) Full.
  Proof.
    intros n Hn z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros jm j st s H Hz Hjm Hj HL HR. rewrite scan_eq.
    pose proof HFI as (_ & _ & HF & _).
    destruct (bdec (jm <? n)) as [Hlt | Hge].
    2:{ apply ltb_false in Hge. replace j with (List.length T) in HR by lia. exact HR. }
    pose proof (ltb_true _ _ Hlt) as Hlt'. cbv zeta.
    assert (Hj' : (j < List.length T)%nat) by lia.
    assert (Hjm1 : (φ (jm + 1)) = (Z.of_nat j + 1)%Z) by (rewrite phi_add1; [lia | rewrite wB_val; pose proof (phi_bnd n); lia]).
    set (c := PrimString.get txt jm).
    assert (Hc : nth j T 0%Z = (φ c)).
    { unfold c, T. rewrite <- pstr_nth by (rewrite <- pstr_len; fold T; lia). f_equal. lia. }
    assert (HX : firstn (S j) T = firstn j T ++ [(φ c)]) by (rewrite <- Hc; apply firstn_snoc; exact Hj').
    destruct HL as (Hs1 & Hs2 & Hs3).
    destruct (walk_spec fl (firstn j T) c (S (List.length (firstn j T)))
                (fun x Hx _ => HF x Hx) _ st (Zwf_well_founded 0 (φ st)) eq_refl Hs1 Hs2
                ltac:(pose proof (suffix_length _ _ Hs2); lia)
                ltac:(intros y Hy _ Hn'; destruct (isnode_prefix _ _ _ _ _ Ht Hn') as [zz [Hzz Ew]];
                      rewrite <- Ew; apply Hs3; [exact Hzz | rewrite Ew; exact Hy]))
      as (Hr1 & Hr2 & Hr3).
    set (q := walk _ _ _ _ _) in *.
    assert (HLq : Longest (firstn (S j) T) q).
    { rewrite HX. split; [exact Hr1|]. split.
      - destruct Hr2 as [E | (y & E & Hy & _)]; rewrite E; [apply suffix_nil|].
        apply suffix_snoc. split; [reflexivity | exact Hy].
      - intros zz Hzz Hs. destruct (suffix_snoc_cases _ _ _ Hs) as [E | (y & E & Hy)];
          [rewrite E; simpl; lia|].
        rewrite E, length_app. simpl. rewrite Nat.add_1_r.
        apply Hr3; [exact Hy | pose proof (suffix_length _ _ Hy); lia | exists zz; split; [exact Hzz | exact E]]. }
    pose proof HLq as (Hq1 & Hq2 & Hq3).
    assert (HI : EmInv j (Em q q) s).
    { exists (Acc_ j). split; [exact HR|]. intros i Hi. right. split; [|reflexivity].
      intros [H1 H2]. pose proof (suffix_length _ _ H1). lia. }
    pose proof (emit_chain_spec j q (jm + 1) Hj' HLq Hjm1 _ q s (Zwf_well_founded 0 (φ q))
                  eq_refl Hq1 (suffix_refl _) HI) as HE.
    set (s' := emit_chain _ _ _ _ _ _ _ _ _ _) in *.
    destruct HE as [A [HRA HA]].
    apply IH with (y := gap n (jm + 1)) (j := S j);
      [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | rewrite Hjm1; lia | lia | exact HLq |].
    apply (R_ext s' A); [|exact HRA].
    intros i Hi. rewrite Acc_S.
    assert (Hoc : occb i j = true <-> suffix (pw i) (W q)).
    { unfold occb. rewrite suffixb_spec. split; [|intros H1; exact (suffix_trans _ _ _ H1 Hq2)].
      intros H1. destruct (Hcur i Hi) as [Hci Ewi].
      apply (suffix_both _ _ _ H1 Hq2). rewrite <- Ewi. apply Hq3; [exact Hci | rewrite Ewi; exact H1]. }
    destruct (HA i Hi) as [[H1 H2] | [H1 H2]].
    - rewrite (proj2 Hoc H1). exact H2.
    - destruct (occb i j) eqn:Eo; [exfalso; apply H1; apply Hoc; reflexivity|].
      rewrite app_nil_r. exact H2.
  Qed.

  End ScanProof.

  End Links.
  End Auto.

  (* ---------------------------------------------------------------- *)
  (* The two instances of the text pass: counting, filling            *)
  (* ---------------------------------------------------------------- *)

  Section Rows.
  Variable txt : PrimString.string.
  Hypothesis HT : (Z.of_nat (List.length (T txt)) <= 4194303)%Z.

  Lemma Full_len : forall i, (List.length (Full txt i) <= List.length (T txt))%nat.
  Proof.
    intros i. unfold Full, Acc_. rewrite length_map.
    etransitivity; [apply filter_length_le|]. rewrite length_seq. lia.
  Qed.

  Lemma prefix_len : forall (a b c : list Z), a ++ b = c -> (List.length a <= List.length c)%nat.
  Proof. intros a b c <-. rewrite length_app. lia. Qed.

  Definition Rcnt (cnt : array int) (A : int -> list Z) : Prop :=
    (φ (PArray.length cnt)) = m /\
    forall i, ((φ i) < m)%Z -> (φ (cnt.[i])) = Z.of_nat (List.length (A i)).

  Lemma Rcnt_ext : forall s A B, (forall i, ((φ i) < m)%Z -> A i = B i) -> Rcnt s A -> Rcnt s B.
  Proof.
    intros s A B HAB [H1 H2]. split; [exact H1|]. intros i Hi. rewrite <- HAB by exact Hi. apply H2. exact Hi.
  Qed.

  Lemma Rcnt_f : forall s A i p, Rcnt s A -> ((φ i) < m)%Z ->
    (exists rest, A i ++ [(φ p)] ++ rest = Full txt i) ->
    Rcnt (f_cnt s i p) (fun i' => if i' =? i then A i ++ [(φ p)] else A i').
  Proof.
    intros s A i p [H1 H2] Hi [rest Hr]. unfold f_cnt.
    pose proof (Full_len i) as HF. pose proof (prefix_len (A i ++ [(φ p)]) rest _ ltac:(rewrite <- app_assoc; exact Hr)) as Hl.
    rewrite length_app in Hl. simpl in Hl.
    split; [rewrite alength_set; exact H1|].
    intros i' Hi'. destruct (int_eq_dec i' i) as [-> | Hne].
    - rewrite eqb_refl, aget_set_same by lia. rewrite length_app. simpl.
      rewrite phi_add1; [rewrite H2 by exact Hi; lia | rewrite H2 by exact Hi; rewrite wB_val; lia].
    - replace (i' =? i) with false by (symmetry; apply eqb_false_spec; exact Hne).
      rewrite aget_set_other by (intro F; apply Hne; symmetry; exact F). apply H2. exact Hi'.
  Qed.

  Definition Rfill (st : array (array int) * array int) (A : int -> list Z) : Prop :=
    (φ (PArray.length (fst st))) = m /\ (φ (PArray.length (snd st))) = m /\
    forall i, ((φ i) < m)%Z ->
      (φ ((snd st).[i])) = Z.of_nat (List.length (A i)) /\
      (φ (PArray.length ((fst st).[i]))) = Z.of_nat (List.length (Full txt i)) /\
      forall k, ((φ k) < Z.of_nat (List.length (A i)))%Z ->
        (φ ((fst st).[i].[k])) = nth (Z.to_nat (φ k)) (A i) 0%Z.

  Lemma Rfill_ext : forall s A B, (forall i, ((φ i) < m)%Z -> A i = B i) -> Rfill s A -> Rfill s B.
  Proof.
    intros s A B HAB (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    intros i Hi. rewrite <- HAB by exact Hi. apply H3. exact Hi.
  Qed.

  Lemma aalength_set : forall (t : array (array int)) (i : int) (b : array int),
    PArray.length t.[i <- b] = PArray.length t.
  Proof. intros t i b. exact (length_set (array int) t i b). Qed.

  Lemma aaget_set_same : forall (t : array (array int)) (i : int) (b : array int),
    ((φ i) < (φ (PArray.length t)))%Z -> t.[i <- b].[i] = b.
  Proof. intros t i b H. apply (get_set_same (array int) t i b). apply ltb_spec. exact H. Qed.

  Lemma aaget_set_other : forall (t : array (array int)) (i j : int) (b : array int),
    i <> j -> t.[i <- b].[j] = t.[j].
  Proof. intros t i j b H. exact (get_set_other (array int) t i j b H). Qed.

  Lemma Rfill_f : forall s A i p, Rfill s A -> ((φ i) < m)%Z ->
    (exists rest, A i ++ [(φ p)] ++ rest = Full txt i) ->
    Rfill (f_fill s i p) (fun i' => if i' =? i then A i ++ [(φ p)] else A i').
  Proof.
    intros [rows ptr] A i p (H1 & H2 & H3) Hi [rest Hr]. unfold f_fill. cbn [fst snd] in *.
    pose proof (Full_len i) as HF. pose proof (prefix_len (A i ++ [(φ p)]) rest _ ltac:(rewrite <- app_assoc; exact Hr)) as Hl.
    rewrite length_app in Hl. simpl in Hl.
    destruct (H3 i Hi) as (Hp & Hlr & Hc).
    unfold Rfill. cbn [fst snd].
    split; [rewrite aalength_set; exact H1|]. split; [rewrite alength_set; exact H2|].
    intros i' Hi'. destruct (int_eq_dec i' i) as [-> | Hne].
    - rewrite eqb_refl, aaget_set_same by lia. rewrite aget_set_same by lia.
      rewrite length_app. simpl.
      split; [rewrite phi_add1; [lia | rewrite wB_val; lia]|].
      split; [rewrite alength_set; exact Hlr|].
      intros k Hk. destruct (int_eq_dec k (ptr.[i])) as [-> | Hk'].
      + rewrite aget_set_same by lia. rewrite Hp, Nat2Z.id, app_nth2 by lia.
        rewrite Nat.sub_diag. reflexivity.
      + rewrite aget_set_other by (intro F; apply Hk'; symmetry; exact F).
        pose proof (neq_phi _ _ Hk'). rewrite app_nth1 by lia. apply Hc. lia.
    - replace (i' =? i) with false by (symmetry; apply eqb_false_spec; exact Hne).
      rewrite aaget_set_other by (intro F; apply Hne; symmetry; exact F).
      rewrite aget_set_other by (intro F; apply Hne; symmetry; exact F). apply H3. exact Hi'.
  Qed.

  Lemma alloc_loop_eq : forall cnt mm i rows H,
    alloc_loop cnt mm i rows H =
    match bdec (i <? mm) with
    | left Hi =>
        alloc_loop cnt mm (i + 1) rows.[i <- PArray.make cnt.[i] 0]
          (Acc_inv H (dec_step mm i Hi))
    | right _ => rows
    end.
  Proof. intros. destruct H. reflexivity. Qed.

  Lemma alloc_loop_spec : forall cnt (len : int -> Z),
    (forall i, ((φ i) < m)%Z -> (φ (cnt.[i])) = len i /\ (len i <= 4194303)%Z) ->
    forall z i rows H, gap (PArray.length pats) i = z -> ((φ i) <= m)%Z ->
    (φ (PArray.length rows)) = m ->
    (forall i', ((φ i') < (φ i))%Z -> (φ (PArray.length (rows.[i']))) = len i') ->
    (φ (PArray.length (alloc_loop cnt (PArray.length pats) i rows H))) = m /\
    forall i', ((φ i') < m)%Z ->
      (φ (PArray.length ((alloc_loop cnt (PArray.length pats) i rows H).[i']))) = len i'.
  Proof.
    intros cnt len Hcnt z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros i rows H Hz Hi Hl Hr. rewrite alloc_loop_eq.
    pose proof m_bound as Hm.
    destruct (bdec (i <? PArray.length pats)) as [Hlt | Hge].
    - pose proof (ltb_true _ _ Hlt) as Hlt'. fold m in Hlt'.
      assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by (apply phi_add1; rewrite wB_val; lia).
      apply IH with (y := gap (PArray.length pats) (i + 1));
        [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | lia | rewrite aalength_set; exact Hl |].
      intros i' Hi'. rewrite Hi1 in Hi'. destruct (int_eq_dec i' i) as [-> | Hne].
      + rewrite aaget_set_same by lia. destruct (Hcnt i Hlt') as [E1 E2].
        rewrite amake_len by lia. exact E1.
      + rewrite aaget_set_other by (intro F; apply Hne; symmetry; exact F).
        apply Hr. pose proof (neq_phi _ _ Hne). lia.
    - apply ltb_false in Hge. fold m in Hge. split; [exact Hl|]. intros i' Hi'. apply Hr. lia.
  Qed.

  End Rows.
End Build.

(* ------------------------------------------------------------------ *)
(* The whole program, on the machine side                              *)
(* ------------------------------------------------------------------ *)

Lemma aamake_len : forall (n : int) (b : array int), ((φ n) <= 4194303)%Z ->
  PArray.length (PArray.make n b) = n.
Proof. intros n b H. exact (alength_make (array int) n b H). Qed.

Lemma Acc_0 : forall pats txt i, Acc_ pats txt 0 i = [].
Proof. reflexivity. Qed.

Lemma impl_core : forall pats txt,
  (forall i, ((φ i) < m pats)%Z -> (0 < plen pats i)%Z) -> (Ptot pats < 4194303)%Z ->
  (m pats < 4194303)%Z -> (Z.of_nat (List.length (T txt)) <= 4194303)%Z ->
  (φ (PArray.length (multimatch_impl pats txt))) = m pats /\
  forall i, ((φ i) < m pats)%Z ->
    (φ (PArray.length ((multimatch_impl pats txt).[i]))) =
      Z.of_nat (List.length (Full pats txt i)) /\
    forall k, ((φ k) < Z.of_nat (List.length (Full pats txt i)))%Z ->
      (φ ((multimatch_impl pats txt).[i].[k])) = nth (Z.to_nat (φ k)) (Full pats txt i) 0%Z.
Proof.
  intros pats txt Hpos HP Hm1 HT.
  pose proof (build_spec pats Hpos HP) as B. cbv zeta in B.
  destruct B as [Hcap [W [Ht [HPf [Hlc Hcur]]]]].
  unfold multimatch_impl. cbv zeta.
  set (st := rounds _ _ _ _ _) in *.
  set (cap := sums _ _ _ _ _ _) in *.
  set (t := bt st) in *. set (cur := bcur st) in *.
  pose proof (m_bound pats) as Hm.
  pose proof (ti_n _ _ _ Ht) as HN.
  assert (Hmk : forall b : int, PArray.length (PArray.make (fst cap + 1) b) = fst cap + 1)
    by (intros b; apply amake_len; lia).
  assert (Hm1' : (φ (PArray.length pats + 1)) = (m pats + 1)%Z) by (apply phi_add1; unfold m in *; rewrite wB_val; lia).
  (* the pattern lists *)
  assert (HPL0 : PLI pats t (1 + Ptot pats) cur (φ 0) (PArray.make (fst cap + 1) 0)
                   (PArray.make (PArray.length pats + 1) 0)).
  { split; [rewrite Hmk; exact Hcap|].
    split; [rewrite amake_len; [exact Hm1' | rewrite Hm1'; lia]|].
    split; [|split].
    - intros v Hv e. rewrite aget_make. split; [intros F; exfalso; exact (Reach_0 _ _ F)|].
      rewrite phi0. lia.
    - intros e He. rewrite phi0 in He. lia.
    - intros v _. rewrite aget_make, phi0. lia. }
  pose proof (plist_loop_spec pats t _ W cur Ht Hcur Hm1 _ 0 _ _
                (Zwf_well_founded 0 (gap (PArray.length pats) 0)) eq_refl ltac:(rewrite phi0; lia) HPL0)
    as (Hlfp & Hlnp & HP1 & HP2 & _).
  set (pl := plist_loop _ _ _ _ _ _) in *.
  (* the failure and output links *)
  assert (HFI1 : FI pats t (1 + Ptot pats) W cur (φ 1) (PArray.make (fst cap + 1) 0) (PArray.make (fst cap + 1) 0)).
  { split; [rewrite Hmk; exact Hcap|]. split; [rewrite Hmk; exact Hcap|].
    split; [intros x Hx; rewrite phi1 in Hx; lia|].
    intros x Hx. rewrite phi1 in Hx.
    assert (x = 0) by (apply phi_inj; pose proof (phi_bnd x); rewrite phi0; lia). subst x.
    unfold OutOK. rewrite aget_make. split; [rewrite phi0; lia|]. split; [intros F; exfalso; apply F; reflexivity|].
    intros i _ _ Hl. rewrite (ti_root _ _ _ Ht) in Hl. simpl in Hl. lia. }
  pose proof (fail_loop_spec pats t _ W cur Ht Hcur Hm1 (fst pl) (snd pl) HP1 _ 1 _ _
                (Zwf_well_founded 0 (gap (tn t) 1)) eq_refl ltac:(rewrite phi1; lia) HFI1) as HFI.
  set (fo := fail_loop _ _ _ _ _ _ _) in *.
  (* the two text passes *)
  assert (Hn : (φ (PrimString.length txt)) = Z.of_nat (List.length (T txt))) by (unfold T; rewrite pstr_len; reflexivity).
  assert (HL0 : Longest t W (firstn 0 (T txt)) 0).
  { split; [rewrite phi0; lia|]. split; [rewrite (ti_root _ _ _ Ht); apply suffix_nil|].
    intros z _ Hs. apply suffix_length in Hs. simpl in Hs. lia. }
  assert (Hmm : (φ (PArray.length (PArray.make (PArray.length pats) 0))) = m pats)
    by (rewrite amake_len; [reflexivity | unfold m in *; lia]).
  pose proof (scan_spec pats t _ W cur Ht Hcur Hpos Hm1 (fst pl) (snd pl) HP1 HP2 (fst fo) (snd fo) HFI txt
                (array int) (Rcnt pats) f_cnt (Rcnt_ext pats) (Rcnt_f pats txt HT)
                (PrimString.length txt) Hn _ 0 0%nat 0 (PArray.make (PArray.length pats) 0)
                (Zwf_well_founded 0 (gap (PrimString.length txt) 0)) eq_refl phi0 ltac:(lia) HL0
                ltac:(split; [exact Hmm | intros i _; rewrite aget_make, phi0, Acc_0; reflexivity]))
    as [_ Hcnt].
  set (cnt := scan _ _ _ _ _ _ _ _ _ _ _ _ _) in Hcnt.
  assert (Hmr : (φ (PArray.length (PArray.make (PArray.length pats) (PArray.make 0 0)))) = m pats)
    by (rewrite aamake_len; [reflexivity | unfold m in *; lia]).
  pose proof (alloc_loop_spec pats txt cnt (fun i => Z.of_nat (List.length (Full pats txt i)))
                ltac:(intros i Hi; split; [exact (Hcnt i Hi) | pose proof (Full_len pats txt i); lia])
                _ 0 (PArray.make (PArray.length pats) (PArray.make 0 0))
                (Zwf_well_founded 0 (gap (PArray.length pats) 0)) eq_refl ltac:(rewrite phi0; lia)
                Hmr
                ltac:(intros i' Hi'; rewrite phi0 in Hi'; pose proof (phi_bnd i'); lia))
    as [Hlr Hlr2].
  set (rows := alloc_loop _ _ _ _ _) in *.
  assert (HR0 : Rfill pats txt (rows, PArray.make (PArray.length pats) 0) (Acc_ pats txt 0)).
  { split; [exact Hlr|]. split; [exact Hmm|].
    intros i Hi. cbn [fst snd]. rewrite aget_make, phi0, Acc_0. simpl.
    split; [reflexivity|]. split; [exact (Hlr2 i Hi)|]. intros k Hk. pose proof (phi_bnd k). lia. }
  pose proof (scan_spec pats t _ W cur Ht Hcur Hpos Hm1 (fst pl) (snd pl) HP1 HP2 (fst fo) (snd fo) HFI txt
                _ (Rfill pats txt) f_fill (Rfill_ext pats txt) (Rfill_f pats txt HT)
                (PrimString.length txt) Hn _ 0 0%nat 0 _
                (Zwf_well_founded 0 (gap (PrimString.length txt) 0)) eq_refl phi0 ltac:(lia) HL0 HR0)
    as (HF1 & _ & HF3).
  split; [exact HF1|].
  intros i Hi. destruct (HF3 i Hi) as (_ & H2 & H3). split; [exact H2 | exact H3].
Qed.

(* ------------------------------------------------------------------ *)
(* From the machine side to the contract                               *)
(* ------------------------------------------------------------------ *)

(* the character codes of a math string *)
Fixpoint codes (s : String.string) : list Z :=
  match s with
  | String.EmptyString => []
  | String.String a s' => Z.of_N (Ascii.N_of_ascii a) :: codes s'
  end.

Lemma codes_len : forall s, List.length (codes s) = String.length s.
Proof. induction s as [| a s IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma codes_app : forall s1 s2, codes (String.append s1 s2) = codes s1 ++ codes s2.
Proof. induction s1 as [| a s IH]; intros s2; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma codes_nth : forall s k c, String.get k s = Some c ->
  nth k (codes s) 0%Z = Z.of_N (Ascii.N_of_ascii c).
Proof.
  induction s as [| a s IH]; intros k c H; [discriminate|].
  destruct k as [| k]; simpl in H |- *; [injection H as <-; reflexivity | apply IH; exact H].
Qed.

Lemma codes_inj : forall a b, codes a = codes b -> a = b.
Proof.
  induction a as [| x a IH]; intros [| y b] H; simpl in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [|apply IH; exact H2].
  apply N2Z.inj in H1. rewrite <- (Ascii.ascii_N_embedding x), <- (Ascii.ascii_N_embedding y), H1.
  reflexivity.
Qed.

Lemma codes_split : forall s A B, codes s = A ++ B ->
  exists s1 s2, s = String.append s1 s2 /\ codes s1 = A /\ codes s2 = B.
Proof.
  induction s as [| a s IH]; intros A B H.
  - destruct A; [|discriminate]. simpl in H. exists String.EmptyString, String.EmptyString.
    split; [reflexivity|]. split; [reflexivity | exact H].
  - destruct A as [| x A].
    + exists String.EmptyString, (String.String a s). split; [reflexivity|]. split; [reflexivity | exact H].
    + simpl in H. injection H as H1 H2. destruct (IH A B H2) as (s1 & s2 & E & E1 & E2).
      exists (String.String a s1), s2. subst s. split; [reflexivity|]. split; [simpl; rewrite E1, H1; reflexivity | exact E2].
Qed.

Lemma pstr_codes : forall (x : PrimString.string) (s : String.string), repr x s -> pstr x = codes s.
Proof.
  intros x s [Hl Hc]. apply nth_ext with (d := 0%Z) (d' := 0%Z).
  - pose proof (pstr_len x). rewrite codes_len. lia.
  - intros k Hk. pose proof (pstr_len x) as Hlx.
    assert (Hk' : (k < String.length s)%nat) by lia.
    destruct (Hc k Hk') as [c [Hg Hr]].
    rewrite (codes_nth s k c Hg).
    assert (Hb : (Z.of_nat k < wB)%Z) by (pose proof (phi_bnd (PrimString.length x)); lia).
    pose proof (pstr_nth x (of_Z (Z.of_nat k))) as Hn.
    rewrite phi_of_Z in Hn by lia. rewrite Nat2Z.id in Hn. rewrite Hn by lia.
    unfold repr, repr_uint in Hr. pose proof (phi_bnd (PrimString.get x (of_Z (Z.of_nat k)))).
    rewrite <- Hr. lia.
Qed.

Lemma occurs_codes : forall pat txt p, occurs_at pat txt p <->
  exists PRE POST, codes txt = PRE ++ codes pat ++ POST /\ N.of_nat (List.length PRE) = p.
Proof.
  intros pat txt p. split.
  - intros (pre & post & E & Hp). exists (codes pre), (codes post). subst txt.
    rewrite !codes_app. split; [reflexivity|]. rewrite codes_len. exact Hp.
  - intros (PRE & POST & E & Hp).
    destruct (codes_split txt PRE (codes pat ++ POST) E) as (s1 & s2 & E1 & C1 & C2).
    destruct (codes_split s2 (codes pat) POST C2) as (s3 & s4 & E3 & C3 & C4).
    apply codes_inj in C3. subst. exists s1, s4. split; [reflexivity|].
    unfold slen. rewrite <- codes_len. reflexivity.
Qed.

Lemma list_occ : forall (P Tl : list Z) (p : N), P <> [] ->
  ((exists j, (j < List.length Tl)%nat /\ suffix P (firstn (S j) Tl) /\
              p = Z.to_N (Z.of_nat j + 1 - Z.of_nat (List.length P))) <->
   exists PRE POST, Tl = PRE ++ P ++ POST /\ N.of_nat (List.length PRE) = p).
Proof.
  intros P Tl p HP. split.
  - intros (j & Hj & [Z0 HZ] & Hp). exists Z0, (skipn (S j) Tl).
    assert (Hl : List.length (firstn (S j) Tl) = S j) by (rewrite length_firstn; lia).
    split.
    + rewrite <- (firstn_skipn (S j) Tl) at 1. rewrite HZ, app_assoc. reflexivity.
    + rewrite HZ, length_app in Hl. rewrite Hp. lia.
  - intros (PRE & POST & E & Hp).
    assert (HlP : (1 <= List.length P)%nat) by (destruct P; [contradiction | simpl; lia]).
    exists (List.length PRE + List.length P - 1)%nat. subst Tl. rewrite !length_app.
    split; [lia|]. split.
    + exists PRE. replace (S (List.length PRE + List.length P - 1)) with (List.length (PRE ++ P))
        by (rewrite length_app; lia).
      rewrite app_assoc, firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
    + rewrite <- Hp. lia.
Qed.

Lemma filter_seq_sorted : forall (f : nat -> bool) n a t u,
  (t < u < List.length (filter f (seq a n)))%nat ->
  (nth t (filter f (seq a n)) 0%nat < nth u (filter f (seq a n)) 0%nat)%nat.
Proof.
  intros f n. induction n as [| n IH]; intros a t u Htu; simpl in *; [lia|].
  destruct (f a) eqn:Ef; simpl in Htu |- *.
  - destruct t as [| t]; destruct u as [| u]; try lia.
    + assert (Hin : In (nth u (filter f (seq (S a) n)) 0%nat) (filter f (seq (S a) n))) by (apply nth_In; lia).
      apply filter_In in Hin as [Hin _]. apply in_seq in Hin. lia.
    + apply IH. lia.
  - apply IH. exact Htu.
Qed.

Lemma map_sorted : forall (L : list nat) (g : nat -> N),
  (forall t u, (t < u < List.length L)%nat -> (nth t L 0%nat < nth u L 0%nat)%nat) ->
  (forall a b, In a L -> In b L -> (a < b)%nat -> (g a < g b)%N) ->
  forall t u, (t < u < List.length L)%nat -> (nth t (map g L) 0%N < nth u (map g L) 0%N)%N.
Proof.
  intros L g HL Hg t u Htu.
  rewrite (nth_indep (map g L) 0%N (g 0%nat)) by (rewrite length_map; lia).
  rewrite (nth_indep (map g L) 0%N (g 0%nat) (n := u)) by (rewrite length_map; lia).
  rewrite !map_nth. apply Hg; [apply nth_In; lia | apply nth_In; lia | apply HL; exact Htu].
Qed.

Lemma zsum_ext_in : forall f g l, (forall i, In i l -> f i = g i) -> zsum f l = zsum g l.
Proof.
  intros f g l H. induction l as [| a l IH]; simpl; [reflexivity|].
  rewrite IH by (intros i Hi; apply H; right; exact Hi). rewrite H by (left; reflexivity). reflexivity.
Qed.

Lemma zsum_iseq_list : forall (l : list String.string) n, (n <= List.length l)%nat ->
  (Z.of_nat n < wB)%Z ->
  zsum (fun i => Z.of_nat (String.length (nth (Z.to_nat (φ i)) l String.EmptyString))) (iseq (Z.of_nat n))
  = Z.of_nat (list_sum (map String.length (firstn n l))).
Proof.
  intros l n. induction n as [| n IH]; intros Hn Hw; [reflexivity|].
  replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z by lia.
  rewrite iseq_S, zsum_app by lia. rewrite IH by lia.
  rewrite (firstn_snoc_gen l n String.EmptyString) by lia.
  rewrite map_app, list_sum_app. unfold zsum at 1. cbn [fold_right map list_sum].
  rewrite phi_of_Z by lia. rewrite Nat2Z.id. lia.
Qed.

Lemma zsum_one : forall l, zsum (fun _ => 1%Z) l = Z.of_nat (List.length l).
Proof.
  induction l as [| a l IH]; [reflexivity|].
  change (zsum (fun _ => 1%Z) (a :: l)) with (1 + zsum (fun _ => 1%Z) l)%Z.
  rewrite IH. cbn [List.length]. lia.
Qed.

Lemma nth_map_seq : forall {A} (f : nat -> A) n k d, (k < n)%nat -> nth k (map f (seq 0 n)) d = f k.
Proof.
  intros A f n k d Hk. rewrite nth_indep with (d' := f 0%nat) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma multimatch_impl_correct : forall (pats : list String.string) (txt : String.string)
    (xp : array PrimString.string) (xt : PrimString.string),
  valid_input pats txt -> repr xp pats -> repr xt txt ->
  exists rows : list (list N), repr (multimatch_impl xp xt) rows /\ multimatch_spec pats txt rows.
Proof.
  intros pats txt xp xt Hv Hxp Hxt.
  destruct Hv as [Hvp Hvtot Hvt].
  pose proof Hxp as [Hlp Hcp].
  assert (Hm : m xp = Z.of_nat (List.length pats)) by (unfold m; symmetry; exact Hlp).
  pose proof (m_bound xp) as Hmb.
  assert (Hpw : forall k, (k < List.length pats)%nat ->
            pw xp (of_Z (Z.of_nat k)) = codes (nth k pats String.EmptyString)).
  { intros k Hk. destruct (Hcp k Hk) as [s [Hs Hr]]. rewrite (nth_error_nth _ _ _ Hs).
    unfold pw. apply pstr_codes. exact Hr. }
  assert (Hpw' : forall i, ((φ i) < m xp)%Z ->
            pw xp i = codes (nth (Z.to_nat (φ i)) pats String.EmptyString)).
  { intros i Hi. rewrite <- Hpw by lia. f_equal. apply phi_inj. rewrite phi_of_Z.
    - pose proof (phi_bnd i). lia.
    - pose proof (phi_bnd i). rewrite wB_val. lia. }
  assert (Hplen : forall i, ((φ i) < m xp)%Z ->
            plen xp i = Z.of_nat (String.length (nth (Z.to_nat (φ i)) pats String.EmptyString))).
  { intros i Hi. rewrite <- plen_len, Hpw', codes_len by exact Hi. reflexivity. }
  assert (HT : T xt = codes txt) by (unfold T; apply pstr_codes; exact Hxt).
  assert (Hpos : forall i, ((φ i) < m xp)%Z -> (0 < plen xp i)%Z).
  { intros i Hi. rewrite Hplen by exact Hi. rewrite Forall_forall in Hvp.
    assert (Hin : In (nth (Z.to_nat (φ i)) pats String.EmptyString) pats) by (apply nth_In; lia).
    pose proof (Hvp _ Hin) as H1. unfold slen in H1. lia. }
  assert (HPt : Ptot xp = Z.of_nat (list_sum (map String.length pats))).
  { unfold Ptot.
    rewrite (zsum_ext_in _ (fun i => Z.of_nat (String.length (nth (Z.to_nat (φ i)) pats String.EmptyString)))).
    - rewrite Hm, zsum_iseq_list, firstn_all; [reflexivity | lia | rewrite wB_val; lia].
    - intros i Hi. apply iseq_In in Hi; [| rewrite wB_val; lia]. apply Hplen. exact Hi. }
  unfold total_length in Hvtot.
  assert (HmP : (m xp <= Ptot xp)%Z).
  { unfold Ptot.
    assert (E1 : zsum (fun _ => 1%Z) (iseq (m xp)) = m xp) by (rewrite zsum_one, iseq_len; lia).
    rewrite <- E1 at 1. apply zsum_le. intros i Hi.
    apply iseq_In in Hi; [| rewrite wB_val; lia]. pose proof (Hpos i Hi). lia. }
  assert (HTl : (Z.of_nat (List.length (T xt)) <= 4194303)%Z)
    by (rewrite HT, codes_len; unfold slen in Hvt; lia).
  destruct (impl_core xp xt Hpos ltac:(lia) ltac:(lia) HTl) as [HR1 HR2].
  set (res := multimatch_impl xp xt) in *.
  exists (map (fun k => map Z.to_N (Full xp xt (of_Z (Z.of_nat k)))) (seq 0 (List.length pats))).
  split.
  - split.
    + rewrite length_map, length_seq. rewrite <- Hm. symmetry. exact HR1.
    + intros k Hk. rewrite length_map, length_seq in Hk.
      exists (map Z.to_N (Full xp xt (of_Z (Z.of_nat k)))). split.
      * rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec k (List.length pats)); [reflexivity | lia].
      * assert (Hi : ((φ (of_Z (Z.of_nat k))) < m xp)%Z) by (rewrite phi_of_Z; [lia | rewrite wB_val; lia]).
        destruct (HR2 _ Hi) as [Hl Hc].
        split.
        -- rewrite length_map. symmetry. exact Hl.
        -- intros k' Hk'. rewrite length_map in Hk'.
           exists (Z.to_N (nth k' (Full xp xt (of_Z (Z.of_nat k))) 0%Z)). split.
           ++ rewrite nth_error_map. rewrite (nth_error_nth' _ 0%Z) by exact Hk'. reflexivity.
           ++ unfold repr, repr_uint. f_equal.
              assert (Hk2 : ((φ (of_Z (Z.of_nat k'))) < Z.of_nat (List.length (Full xp xt (of_Z (Z.of_nat k)))))%Z)
                by (rewrite phi_of_Z; [lia | rewrite wB_val; pose proof (Full_len xp xt (of_Z (Z.of_nat k))); lia]).
              pose proof (Hc _ Hk2) as Hc2.
              rewrite phi_of_Z, Nat2Z.id in Hc2 by (rewrite wB_val; pose proof (Full_len xp xt (of_Z (Z.of_nat k))); lia).
              exact Hc2.
  - split.
    + unfold len. rewrite length_map, length_seq. reflexivity.
    + intros i Hi. unfold len in Hi.
      set (k := N.to_nat i).
      assert (Hk : (k < List.length pats)%nat) by lia.
      unfold get_row, get_pattern. fold k. rewrite nth_map_seq by exact Hk.
      set (ii := of_Z (Z.of_nat k)).
      assert (Hii : ((φ ii) < m xp)%Z) by (unfold ii; rewrite phi_of_Z; [lia | rewrite wB_val; lia]).
      set (pat := nth k pats String.EmptyString).
      assert (HP : pw xp ii = codes pat) by (apply Hpw; exact Hk).
      assert (HPl : plen xp ii = Z.of_nat (List.length (codes pat))) by (rewrite <- HP; symmetry; apply plen_len).
      assert (HPne : codes pat <> []).
      { intro E. pose proof (Hpos ii Hii). rewrite HPl, E in H. simpl in H. lia. }
      unfold Full, Acc_. rewrite map_map.
      set (L := filter (occb xp xt ii) (seq 0 (List.length (T xt)))).
      assert (HLpos : forall a, In a L -> (0 <= pos xp a ii)%Z).
      { intros a Ha. apply filter_In in Ha as [_ Ha]. unfold occb in Ha. apply suffixb_spec in Ha.
        apply suffix_length in Ha. rewrite length_firstn in Ha. unfold pos. rewrite HPl, <- HP. lia. }
      split.
      * unfold ascending, get_list_N, len. rewrite length_map. intros t u Htu.
        apply map_sorted; [ | | lia].
        -- intros t' u' Htu'. apply filter_seq_sorted. exact Htu'.
        -- intros a b Ha Hb Hab. pose proof (HLpos a Ha). pose proof (HLpos b Hb).
           apply Z2N.inj_lt; [lia | lia |]. unfold pos. lia.
      * intros p. rewrite in_map_iff, occurs_codes, <- (list_occ (codes pat) (codes txt) p HPne).
        split.
        -- intros (j & Hgj & Hj). unfold L in Hj. apply filter_In in Hj as [Hj1 Hj2]. apply in_seq in Hj1.
           unfold occb in Hj2. apply suffixb_spec in Hj2. rewrite HP, HT in Hj2.
           exists j. split; [rewrite <- HT; lia|]. split; [exact Hj2|].
           rewrite <- Hgj. unfold pos. rewrite HPl. reflexivity.
        -- intros (j & Hj & Hs & Hp). exists j. split.
           ++ rewrite Hp. unfold pos. rewrite HPl. reflexivity.
           ++ unfold L. apply filter_In. split; [apply in_seq; rewrite HT; lia|].
              unfold occb. apply suffixb_spec. rewrite HP, HT. exact Hs.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition multimatch : array PrimString.string -> PrimString.string ->
                        array (array uint) := multimatch_impl.
Elpi complexity multimatch.

Definition multimatch_correct :
  forall (pats : list String.string) (txt : String.string)
         (xp : array PrimString.string) (xt : PrimString.string),
  valid_input pats txt -> repr xp pats -> repr xt txt ->
  exists rows : list (list N),
    repr (multimatch xp xt) rows /\ multimatch_spec pats txt rows
  := multimatch_impl_correct.


(* ================================================================== *)
(* Cost: multimatch_time                                               *)
(* ================================================================== *)

(* The cost translation is the Elpi complexity lines above (callee
   first).  The bound: every loop is bounded on its cost twin by
   induction on a nat bound of its measure, the potential where its work
   is amortised (see implementation_README.md, "Complexity").  The fix of
   a loop is named (set Gf) before the step, so that cost_simpl's
   rewrites never touch its body and the induction hypothesis applies
   syntactically. *)

From Stdlib Require PrimStringAxioms.
(* ---- cost proofs, part devA ---- *)
#[local] Arguments Uint63.to_Z : simpl never.

Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; cbn; lia. Qed.

Fixpoint lok (chr ns : array int) (c : int) (k : nat) (v : int) : Prop :=
  match k with
  | O => False
  | S k' => v = 0 \/ chr.[v] = c \/ (ns.[v] <? v) = false \/ lok chr ns c k' ns.[v]
  end.

Ltac zpart :=
  repeat match goal with
  | |- context [cost (extract (extract (extract (set_cost ?a ?b ?c) ?d ?e) ?f ?g) ?h ?i)] =>
      change (cost (extract (extract (extract (set_cost a b c) d e) f g) h i)) with 1%nat
  | |- context [cost (extract (extract (make_cost ?a ?b ?c) ?d ?e) ?f ?g)] =>
      change (cost (extract (extract (make_cost a b c) d e) f g)) with 1%nat
  end;
  repeat match goal with |- context [cost ?X] => change (cost X) with 0%nat end.

Lemma tchr_c t tC : cost (tchr_cost stepsCM t tC) = 1%nat. Proof. destruct t; reflexivity. Qed.
Lemma tpar_c t tC : cost (tpar_cost stepsCM t tC) = 1%nat. Proof. destruct t; reflexivity. Qed.
Lemma tfc_c t tC : cost (tfc_cost stepsCM t tC) = 1%nat. Proof. destruct t; reflexivity. Qed.
Lemma tns_c t tC : cost (tns_cost stepsCM t tC) = 1%nat. Proof. destruct t; reflexivity. Qed.
Lemma tdep_c t tC : cost (tdep_cost stepsCM t tC) = 1%nat. Proof. destruct t; reflexivity. Qed.
Lemma tn_c t tC : cost (tn_cost stepsCM t tC) = 1%nat. Proof. destruct t; reflexivity. Qed.
Lemma bact_c t tC : cost (bact_cost stepsCM t tC) = 1%nat. Proof. destruct t; reflexivity. Qed.
Lemma bcur_c t tC : cost (bcur_cost stepsCM t tC) = 1%nat. Proof. destruct t; reflexivity. Qed.
Lemma bw_c t tC : cost (bw_cost stepsCM t tC) = 1%nat. Proof. destruct t; reflexivity. Qed.
Lemma bt_c t tC : cost (bt_cost stepsCM t tC) = 1%nat. Proof. destruct t; reflexivity. Qed.
Lemma fst_c A AC B BC p pC : cost (extract (extract (fst_cost stepsCM A AC) B BC) p pC) = 1%nat.
Proof. destruct p; reflexivity. Qed.
Lemma snd_c A AC B BC p pC : cost (extract (extract (snd_cost stepsCM A AC) B BC) p pC) = 1%nat.
Proof. destruct p; reflexivity. Qed.
Ltac projc := rewrite ?tchr_c, ?tpar_c, ?tfc_c, ?tns_c, ?tdep_c, ?tn_c, ?bact_c, ?bcur_c, ?bw_c, ?bt_c, ?fst_c, ?snd_c.

Lemma lookup_from_time chr chrC ns nsC c cC v vC H HC k :
  lok chr ns c k v ->
  (cost (extract (extract (extract (extract (lookup_from_cost stepsCM chr chrC) ns nsC) c cC) v vC) H HC)
     <= k * 60 + 10)%nat.
Proof.
  unfold lookup_from_cost. cbn.
  match goal with |- context [@cost ?T (?G chr chrC ns nsC c cC v vC H HC)] =>
    assert (HG : forall k v vC H HC, lok chr ns c k v ->
       (cost (G chr chrC ns nsC c cC v vC H HC) <= k * 60 + 10)%nat) end.
  { induction k0 as [|k0 IH]; intros v' vC' [g] HC' Hk; [destruct Hk|].
    cost_simpl.
    pose proof (bdec_time (v' =? 0) (bool_w (v' =? 0))) as HB.
    cost_destruct (bdec (v' =? 0)); cost_simpl; [lia|].
    destruct (chr.[v'] =? c) eqn:Ec; cost_simpl; [lia|].
    pose proof (bdec_time (ns.[v'] <? v') (bool_w (ns.[v'] <? v'))) as HB2.
    cost_destruct (bdec (ns.[v'] <? v')); cost_simpl; [|lia].
    assert (Hk' : lok chr ns c k0 ns.[v']).
    { destruct Hk as [E|[E|[E|E]]]; [subst v'; discriminate | | congruence | exact E].
      rewrite E, eqb_refl in Ec. discriminate. }
    match goal with |- context [@cost ?T (?G' chr chrC ns nsC c cC ?v2 ?vC2 ?h ?e)] =>
      pose proof (IH v2 vC2 h e Hk' : (@cost T (G' chr chrC ns nsC c cC v2 vC2 h e) <= _)%nat) as HI end.
    lia. }
  intros Hk.
  match goal with |- context [@cost ?T (?G chr chrC ns nsC c cC v vC H HC)] =>
    exact (HG _ v vC H HC Hk : (@cost T (G chr chrC ns nsC c cC v vC H HC) <= _)%nat) end.
Qed.

Lemma lookup_time t tC u uC c cC k :
  lok (tchr t) (tns t) c k ((tfc t).[u]) ->
  (cost (extract (extract (lookup_cost stepsCM t tC) u uC) c cC) <= k * 60 + 30)%nat.
Proof.
  intros Hk. unfold lookup_cost. cost_simpl. zpart. projc.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (extract (extract (lookup_from_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?v ?vC) ?H ?HC =>
        pose proof (lookup_from_time a aC b bC c cC v vC H HC k Hk : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.
  lia.
Qed.

Lemma add_child_time t tC u uC c cC k :
  lok (tchr t) (tns t) c k ((tfc t).[u]) ->
  (cost (extract (extract (add_child_cost stepsCM t tC) u uC) c cC) <= k * 60 + 300)%nat.
Proof.
  intros Hk. unfold add_child_cost. cost_simpl. zpart. projc.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (lookup_cost stepsCM ?t ?tC) ?u ?uC) ?c ?cC =>
        pose proof (lookup_time t tC u uC c cC k Hk : (@cost T X <= _)%nat) as Hc;
        revert Hc; generalize (@cost T X); intros ? Hc
    end end.
  cost_destruct (lookup t u c =? 0); cost_simpl; zpart; projc.
  all: lia.
Qed.

Ltac bound X pf :=
  match goal with |- context [@cost ?T X] =>
    let Hc := fresh "Hc" in
    pose proof (pf : (@cost T X <= _)%nat) as Hc; revert Hc; generalize (@cost T X); intros ? Hc end.

Definition WalkHyp (t : trie) (fl : array int) (c : int) (D : int -> nat) (K : nat) (x : int) : Prop :=
  (forall y, (φ y <= φ x)%Z -> lok (tchr t) (tns t) c K ((tfc t).[y])) /\
  (forall y, (0 < φ y <= φ x)%Z -> (φ fl.[y] < φ y)%Z -> (D fl.[y] < D y)%nat) /\
  (forall y, (φ y <= φ x)%Z -> lookup t y c <> 0 -> D (lookup t y c) = S (D y)).

Lemma walk_time t tC fl flC c cC x xC H HC (D : int -> nat) K A :
  D 0 = 0%nat -> (K * 60 + 200 <= A)%nat -> WalkHyp t fl c D K x ->
  (cost (extract (extract (extract (extract (walk_cost stepsCM t tC) fl flC) c cC) x xC) H HC)
     + D (walk t fl c x H) * A <= D x * A + A + A)%nat.
Proof.
  intros HD0 HA. unfold walk_cost. cbn.
  match goal with |- context [@cost ?T (?G t tC fl flC c cC x xC H HC)] =>
    assert (HG : forall N x xC H HC, (Z.to_nat (φ x) <= N)%nat -> WalkHyp t fl c D K x ->
       (cost (G t tC fl flC c cC x xC H HC) + D (walk t fl c x H) * A <= D x * A + A + A)%nat) end.
  { intros N. induction N as [N IH] using lt_wf_ind. intros x' xC' [g] HC' HN [HL [HDl HY]].
    cost_simpl. zpart. projc.
    bound (extract (extract (lookup_cost stepsCM t tC) x' xC') c cC)
          (lookup_time t tC x' xC' c cC K (HL x' (Z.le_refl _))).
    pose proof (bdec_time (lookup t x' c =? 0) (bool_w (lookup t x' c =? 0))) as HB.
    cost_destruct (bdec (lookup t x' c =? 0)); cost_simpl; zpart; projc.
    - pose proof (bdec_time (x' =? 0) (bool_w (x' =? 0))) as HB2.
      cost_destruct (bdec (x' =? 0)); cost_simpl; zpart; projc.
      + rewrite HD0. lia.
      + pose proof (bdec_time (fl.[x'] <? x') (bool_w (fl.[x'] <? x'))) as HB3.
        cost_destruct (bdec (fl.[x'] <? x')); cost_simpl; zpart; projc.
        * pose proof (ltb_true _ _ e1) as Hlt.
          assert (Hx0 : (0 < φ x')%Z) by (apply pos_of_nz; apply eqb_false; exact e0).
          pose proof (HDl x' ltac:(lia) Hlt) as HDx.
          assert (HW : WalkHyp t fl c D K fl.[x']).
          { split; [|split].
            - intros y Hy. apply HL. lia.
            - intros y Hy. apply HDl. lia.
            - intros y Hy. apply HY. lia. }
          assert (HN' : (Z.to_nat (φ fl.[x']) < N)%nat) by lia.
          match goal with |- context [@cost ?T (?G' t tC fl flC c cC ?x2 ?xC2 ?h ?e)] =>
            pose proof (IH _ HN' x2 xC2 h e (le_n _) HW : (@cost T (G' t tC fl flC c cC x2 xC2 h e) + _ <= _)%nat) as HI end.
          assert (Hm : ((D fl.[x'] + 1) * A <= D x' * A)%nat) by (apply Nat.mul_le_mono_r; lia).
          lia.
        * rewrite HD0. lia.
    - pose proof (eqb_false _ _ e) as Hne. rewrite (HY x' (Z.le_refl _) Hne). lia. }
  intros HW.
  match goal with |- context [@cost ?T (?G t tC fl flC c cC x xC H HC)] =>
    exact (HG _ x xC H HC (le_n _) HW : (@cost T (G t tC fl flC c cC x xC H HC) + _ <= _)%nat) end.
Qed.

#[local] Arguments gap : simpl never.

Lemma gap_step n i : (i <? n) = true -> (Z.to_nat (gap n (i + 1)) = Z.to_nat (gap n i) - 1 /\ 0 < Z.to_nat (gap n i))%nat.
Proof.
  intros H. apply ltb_true in H. unfold gap.
  assert (φ (i + 1) = φ i + 1)%Z by (rewrite phi_add1; [lia | pose proof (phi_bnd n); lia]). lia.
Qed.

Lemma sums_time pats patsC m mC i iC P PC L LC H HC :
  (cost (extract (extract (extract (extract (extract (sums_cost stepsCM pats patsC) m mC) i iC) P PC) L LC) H HC)
     <= Z.to_nat (gap m i) * 40 + 20)%nat.
Proof.
  unfold sums_cost. cbn.
  match goal with |- context [@cost ?T (?G pats patsC m mC i iC P PC L LC H HC)] =>
    assert (HG : forall N i iC P PC L LC H HC, (Z.to_nat (gap m i) <= N)%nat ->
       (cost (G pats patsC m mC i iC P PC L LC H HC) <= N * 40 + 20)%nat) end.
  { induction N as [|N IH]; intros i' iC' P' PC' L' LC' [g] HC' HN;
      cost_simpl; zpart; projc;
      pose proof (bdec_time (i' <? m) (bool_w (i' <? m))) as HB;
      cost_destruct (bdec (i' <? m)); cost_simpl; zpart; projc.
    - exfalso. pose proof (gap_step _ _ e). lia.
    - lia.
    - pose proof (gap_step _ _ e) as [Hg1 Hg2].
      assert (HN' : (Z.to_nat (gap m (i' + 1)) <= N)%nat) by lia.
      cost_destruct (L' <? PrimString.length pats.[i']); cost_simpl; zpart; projc;
      (match goal with |- context [@cost ?T (?G' pats patsC m mC (i' + 1)%uint63 ?w ?a ?aC ?b ?bC ?h ?e)] =>
        pose proof (IH (i' + 1)%uint63 w a aC b bC h e HN' : (@cost T (G' pats patsC m mC (i' + 1)%uint63 w a aC b bC h e) <= _)%nat) as HI end);
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G pats patsC m mC i iC P PC L LC H HC)] =>
    exact (HG _ i iC P PC L LC H HC (le_n _) : (@cost T (G pats patsC m mC i iC P PC L LC H HC) <= _)%nat) end.
Qed.

Lemma iota_time m mC i iC a aC H HC :
  (cost (extract (extract (extract (iota_cost stepsCM m mC) i iC) a aC) H HC)
     <= Z.to_nat (gap m i) * 40 + 20)%nat.
Proof.
  unfold iota_cost. cbn.
  match goal with |- context [@cost ?T (?G m mC i iC a aC H HC)] =>
    assert (HG : forall N i iC a aC H HC, (Z.to_nat (gap m i) <= N)%nat ->
       (cost (G m mC i iC a aC H HC) <= N * 40 + 20)%nat) end.
  { induction N as [|N IH]; intros i' iC' a' aC' [g] HC' HN;
      cost_simpl; zpart; projc;
      pose proof (bdec_time (i' <? m) (bool_w (i' <? m))) as HB;
      cost_destruct (bdec (i' <? m)); cost_simpl; zpart; projc.
    - exfalso. pose proof (gap_step _ _ e). lia.
    - lia.
    - pose proof (gap_step _ _ e) as [Hg1 Hg2].
      assert (HN' : (Z.to_nat (gap m (i' + 1)) <= N)%nat) by lia.
      match goal with |- context [@cost ?T (?G' m mC (i' + 1)%uint63 ?w ?a ?aC ?h ?e)] =>
        pose proof (IH (i' + 1)%uint63 w a aC h e HN' : (@cost T (G' m mC (i' + 1)%uint63 w a aC h e) <= _)%nat) as HI end.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G m mC i iC a aC H HC)] =>
    exact (HG _ i iC a aC H HC (le_n _) : (@cost T (G m mC i iC a aC H HC) <= _)%nat) end.
Qed.

Lemma plist_loop_time cur curC m mC i iC fp fpC np npC H HC :
  (cost (extract (extract (extract (extract (extract (plist_loop_cost stepsCM cur curC) m mC) i iC) fp fpC) np npC) H HC)
     <= Z.to_nat (gap m i) * 80 + 20)%nat.
Proof.
  unfold plist_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G cur curC m mC i iC fp fpC np npC H HC)] =>
    assert (HG : forall N i iC fp fpC np npC H HC, (Z.to_nat (gap m i) <= N)%nat ->
       (cost (G cur curC m mC i iC fp fpC np npC H HC) <= N * 80 + 20)%nat) end.
  { induction N as [|N IH]; intros i' iC' a' aC' b' bC' [g] HC' HN;
      cost_simpl; zpart; projc;
      pose proof (bdec_time (i' <? m) (bool_w (i' <? m))) as HB;
      cost_destruct (bdec (i' <? m)); cost_simpl; zpart; projc.
    - exfalso. pose proof (gap_step _ _ e). lia.
    - lia.
    - pose proof (gap_step _ _ e) as [Hg1 Hg2].
      assert (HN' : (Z.to_nat (gap m (i' + 1)) <= N)%nat) by lia.
      match goal with |- context [@cost ?T (?G' cur curC m mC (i' + 1)%uint63 ?w ?a ?aC ?b ?bC ?h ?e)] =>
        pose proof (IH (i' + 1)%uint63 w a aC b bC h e HN' : (@cost T (G' cur curC m mC (i' + 1)%uint63 w a aC b bC h e) <= _)%nat) as HI end.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G cur curC m mC i iC fp fpC np npC H HC)] =>
    exact (HG _ i iC fp fpC np npC H HC (le_n _) : (@cost T (G cur curC m mC i iC fp fpC np npC H HC) <= _)%nat) end.
Qed.

Lemma alloc_loop_time cnt cntC m mC i iC rows rowsC H HC :
  (cost (extract (extract (extract (extract (alloc_loop_cost stepsCM cnt cntC) m mC) i iC) rows rowsC) H HC)
     <= Z.to_nat (gap m i) * 80 + 20)%nat.
Proof.
  unfold alloc_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G cnt cntC m mC i iC rows rowsC H HC)] =>
    assert (HG : forall N i iC rows rowsC H HC, (Z.to_nat (gap m i) <= N)%nat ->
       (cost (G cnt cntC m mC i iC rows rowsC H HC) <= N * 80 + 20)%nat) end.
  { induction N as [|N IH]; intros i' iC' a' aC' [g] HC' HN;
      cost_simpl; zpart; projc;
      pose proof (bdec_time (i' <? m) (bool_w (i' <? m))) as HB;
      cost_destruct (bdec (i' <? m)); cost_simpl; zpart; projc.
    - exfalso. pose proof (gap_step _ _ e). lia.
    - lia.
    - pose proof (gap_step _ _ e) as [Hg1 Hg2].
      assert (HN' : (Z.to_nat (gap m (i' + 1)) <= N)%nat) by lia.
      match goal with |- context [@cost ?T (?G' cnt cntC m mC (i' + 1)%uint63 ?w ?a ?aC ?h ?e)] =>
        pose proof (IH (i' + 1)%uint63 w a aC h e HN' : (@cost T (G' cnt cntC m mC (i' + 1)%uint63 w a aC h e) <= _)%nat) as HI end.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G cnt cntC m mC i iC rows rowsC H HC)] =>
    exact (HG _ i iC rows rowsC H HC (le_n _) : (@cost T (G cnt cntC m mC i iC rows rowsC H HC) <= _)%nat) end.
Qed.

(* ---- cost proofs, part devB ---- *)
#[local] Arguments Uint63.to_Z : simpl never.
#[local] Arguments gap : simpl never.

#[local] Arguments emit_list : simpl never.
#[local] Arguments emit_chain : simpl never.
#[local] Arguments scan : simpl never.

Lemma emit_list_unf Sx f np p e s g :
  emit_list Sx f np p e s (Acc_intro _ g) =
  match bdec (e =? 0) with
  | left _ => s
  | right _ =>
    match bdec (np.[e] <? e) with
    | left He => emit_list Sx f np p np.[e] (f s (e - 1) p) (g _ (stringmultimatching_implem.dec_lt e np.[e] He))
    | right _ => f s (e - 1) p
    end
  end.
Proof. reflexivity. Qed.

Definition cntf (k : nat) (_ _ : int) : nat := S k.
Lemma cntf_S k a b : cntf k a b = S k. Proof. reflexivity. Qed.

Lemma emit_list_add np p e k H :
  emit_list nat cntf np p e k H = (k + emit_list nat cntf np p e 0 H)%nat.
Proof.
  assert (G : forall N e H k, (Z.to_nat (φ e) <= N)%nat ->
            emit_list nat cntf np p e k H = (k + emit_list nat cntf np p e 0 H)%nat).
  { intros N. induction N as [N IH] using lt_wf_ind. intros e' [g] k' HN. rewrite !emit_list_unf.
    destruct (bdec (e' =? 0)); [lia|].
    destruct (bdec (np.[e'] <? e')) as [Hl|]; [|unfold cntf; lia].
    pose proof (ltb_true _ _ Hl).
    rewrite (IH (Z.to_nat (φ np.[e'])) ltac:(lia) _ _ (cntf k' (e' - 1) p) (le_n _)).
    rewrite (IH (Z.to_nat (φ np.[e'])) ltac:(lia) _ _ (cntf 0 (e' - 1) p) (le_n _)).
    unfold cntf. lia. }
  apply (G _ e H k (le_n _)).
Qed.

Ltac fbound Hf cf :=
  match goal with |- context [@cost ?T3 (@extract ?C3 ?U3 (@extract ?C2 ?U2 (?fC ?a ?b) ?c ?d) ?q ?r)] =>
    match goal with |- context [@cost ?T1 (fC a b)] =>
      match goal with |- context [@cost ?T2 (@extract ?C2' ?U2' (fC a b) c d)] =>
        let Hf1 := fresh "Hf1" in
        assert (Hf1 : (@cost T1 (fC a b) + @cost T2 (@extract C2' U2' (fC a b) c d)
                       + @cost T3 (@extract C3 U3 (@extract C2 U2 (fC a b) c d) q r) <= cf)%nat)
          by exact (Hf a b c d q r) end end end.

Lemma emit_list_time Sx SxC f fC np npC p pC e eC s sC H HC cf C :
  (cf + 60 <= C)%nat ->
  (forall s sC i iC q qC, (cost (fC s sC) + cost (extract (fC s sC) i iC) + cost (extract (extract (fC s sC) i iC) q qC) <= cf)%nat) ->
  (cost (extract (extract (extract (extract (extract (extract (emit_list_cost stepsCM Sx SxC) f fC) np npC) p pC) e eC) s sC) H HC)
     <= emit_list nat cntf np p e 0 H * C + 20)%nat.
Proof.
  intros HCf Hf. unfold emit_list_cost. cbn.
  match goal with |- context [@cost ?T (?G p pC e eC s sC H HC)] =>
    assert (HG : forall N e eC s sC H HC, (Z.to_nat (φ e) <= N)%nat ->
       (cost (G p pC e eC s sC H HC) <= emit_list nat cntf np p e 0 H * C + 20)%nat) end.
  { intros N. induction N as [N IH] using lt_wf_ind. intros e' eC' s' sC' [g] HC' HN.
    rewrite (emit_list_unf nat cntf).
    cost_simpl. zpart. projc.
    pose proof (bdec_time (e' =? 0) (bool_w (e' =? 0))) as HB.
    cost_destruct (bdec (e' =? 0)); cost_simpl; zpart; projc; [lia|].
    fbound Hf cf.
    pose proof (bdec_time (np.[e'] <? e') (bool_w (np.[e'] <? e'))) as HB2.
    cost_destruct (bdec (np.[e'] <? e')); cost_simpl; zpart; projc.
    - pose proof (ltb_true _ _ e1) as Hlt.
      assert (HN' : (Z.to_nat (φ np.[e']) < N)%nat) by lia.
      rewrite emit_list_add.
      match goal with |- context [@cost ?T (?G' p pC np.[e'] ?w ?a ?aC ?h ?e)] =>
        pose proof (IH _ HN' np.[e'] w a aC h e (le_n _) : (@cost T (G' p pC np.[e'] w a aC h e) <= _)%nat) as HI;
        revert HI; generalize (@cost T (G' p pC np.[e'] w a aC h e)); intros CR HI end.
      rewrite cntf_S, Nat.mul_add_distr_r.
      revert HI. match goal with |- context [(emit_list ?a ?b ?c ?d ?e 0%nat ?h * ?k)%nat] => generalize (emit_list a b c d e 0%nat h * k)%nat end.
      intros Y HI. lia.
    - rewrite ?cntf_S. lia. }
  match goal with |- context [@cost ?T (?G p pC e eC s sC H HC)] =>
    exact (HG _ e eC s sC H HC (le_n _) : (@cost T (G p pC e eC s sC H HC) <= _)%nat) end.
Qed.

Lemma emit_list_pos np p e k H : e <> 0 -> (S k <= emit_list nat cntf np p e k H)%nat.
Proof.
  intros He. destruct H as [g]. rewrite emit_list_unf.
  destruct (bdec (e =? 0)) as [E|]; [apply eqb_true in E; contradiction|].
  destruct (bdec (np.[e] <? e)); [|rewrite cntf_S; lia].
  rewrite emit_list_add, cntf_S. lia.
Qed.

Lemma emit_chain_unf Sx f t out fp np je x s g :
  emit_chain Sx f t out fp np je x s (Acc_intro _ g) =
  match bdec (x =? 0) with
  | left _ => s
  | right _ =>
    match bdec (out.[x] <? x) with
    | left Ho => emit_chain Sx f t out fp np je out.[x]
                   (emit_list Sx f np (je - (tdep t).[x]) fp.[x] s (Zwf_well_founded 0 (φ fp.[x])))
                   (g _ (stringmultimatching_implem.dec_lt x out.[x] Ho))
    | right _ => emit_list Sx f np (je - (tdep t).[x]) fp.[x] s (Zwf_well_founded 0 (φ fp.[x]))
    end
  end.
Proof. reflexivity. Qed.

Lemma emit_chain_add t out fp np je x k H :
  emit_chain nat cntf t out fp np je x k H = (k + emit_chain nat cntf t out fp np je x 0 H)%nat.
Proof.
  assert (G : forall N x H k, (Z.to_nat (φ x) <= N)%nat ->
            emit_chain nat cntf t out fp np je x k H = (k + emit_chain nat cntf t out fp np je x 0 H)%nat).
  { intros N. induction N as [N IH] using lt_wf_ind. intros x' [g] k' HN. rewrite !emit_chain_unf.
    destruct (bdec (x' =? 0)); [lia|].
    destruct (bdec (out.[x'] <? x')) as [Hl|].
    - pose proof (ltb_true _ _ Hl).
      rewrite (IH (Z.to_nat (φ out.[x'])) ltac:(lia) _ _ (emit_list _ _ _ _ _ k' _) (le_n _)).
      rewrite (IH (Z.to_nat (φ out.[x'])) ltac:(lia) _ _ (emit_list _ _ _ _ _ 0%nat _) (le_n _)).
      rewrite (emit_list_add np _ _ k'). lia.
    - rewrite (emit_list_add np _ _ k'). lia. }
  apply (G _ x H k (le_n _)).
Qed.

Definition OutHyp (out fp : array int) (x : int) : Prop :=
  forall y, (0 < φ y <= φ x)%Z -> (φ out.[y] < φ y)%Z -> out.[y] <> 0 -> fp.[out.[y]] <> 0.

Ltac bound_emit_list Hf HCf :=
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (extract (extract (extract (extract (emit_list_cost stepsCM ?Sx ?SxC) ?f ?fC) ?np ?npC) ?p ?pC) ?e ?eC) ?s ?sC) ?H ?HC =>
        bound X (emit_list_time Sx SxC f fC np npC p pC e eC s sC H HC _ _ HCf Hf)
    end end.

Lemma emit_chain_time Sx SxC f fC t tC out outC fp fpC np npC je jeC x xC s sC H HC cf C :
  (cf + 60 <= C)%nat ->
  (forall s sC i iC q qC, (cost (fC s sC) + cost (extract (fC s sC) i iC) + cost (extract (extract (fC s sC) i iC) q qC) <= cf)%nat) ->
  OutHyp out fp x ->
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (extract (emit_chain_cost stepsCM Sx SxC) f fC) t tC) out outC) fp fpC) np npC) je jeC) x xC) s sC) H HC)
     <= emit_chain nat cntf t out fp np je x 0 H * (C + 200) + 300)%nat.
Proof.
  intros HCf Hf. unfold emit_chain_cost. cbn.
  match goal with |- context [@cost ?T (?G je jeC x xC s sC H HC)] => set (Gf := G) end.
  assert (HG : forall N x xC s sC H HC, (Z.to_nat (φ x) <= N)%nat -> OutHyp out fp x ->
       (cost (Gf je jeC x xC s sC H HC) <= emit_chain nat cntf t out fp np je x 0 H * (C + 200) + 300)%nat /\
       ((x = 0 \/ fp.[x] <> 0) ->
        (cost (Gf je jeC x xC s sC H HC) <= emit_chain nat cntf t out fp np je x 0 H * (C + 200) + 100)%nat)).
  { intros N. induction N as [N IH] using lt_wf_ind. intros x' xC' s' sC' [g] HC' HN HO.
    rewrite (emit_chain_unf nat cntf).
    unfold Gf at 1. cbn. fold Gf. clearbody Gf.
    cost_simpl. zpart. projc.
    pose proof (bdec_time (x' =? 0) (bool_w (x' =? 0))) as HB.
    cost_destruct (bdec (x' =? 0)); cost_simpl; zpart; projc; [split; [lia|intros; lia]|].
    bound_emit_list Hf HCf.
    pose proof (bdec_time (out.[x'] <? x') (bool_w (out.[x'] <? x'))) as HB2.
    cost_destruct (bdec (out.[x'] <? x')); cost_simpl; zpart; projc.
    - pose proof (ltb_true _ _ e0) as Hlt.
      assert (Hx0 : (0 < φ x')%Z) by (apply pos_of_nz; apply eqb_false; exact e).
      assert (HN' : (Z.to_nat (φ out.[x']) < N)%nat) by lia.
      assert (HO' : OutHyp out fp out.[x']) by (intros y Hy; apply HO; lia).
      assert (Ho : out.[x'] = 0 \/ fp.[out.[x']] <> 0).
      { destruct (int_eq_dec out.[x'] 0) as [E|E]; [left; exact E | right; apply HO; [lia | exact Hlt | exact E]]. }
      match goal with |- context [@cost ?T (Gf je jeC out.[x'] ?w ?a ?aC ?h ?e)] =>
        pose proof (proj2 (IH _ HN' out.[x'] w a aC h e (le_n _) HO') Ho) as HI end.
      cost_align HI.
      rewrite emit_chain_add.
      set (EL := emit_list nat cntf np _ _ 0%nat _).
      set (ECo := emit_chain nat cntf t out fp np je out.[x'] 0%nat _) in *.
      assert (HEL : fp.[x'] <> 0 -> (1 <= EL)%nat) by (intros Hn; apply emit_list_pos; exact Hn).
      rewrite !Nat.mul_add_distr_r, !Nat.mul_add_distr_l.
      split; [lia|]. intros [E|E]; [exfalso; exact (eqb_false _ _ e E)|].
      specialize (HEL E). lia.
    - set (EL := emit_list nat cntf np _ _ 0%nat _).
      assert (HEL : fp.[x'] <> 0 -> (1 <= EL)%nat) by (intros Hn; apply emit_list_pos; exact Hn).
      rewrite !Nat.mul_add_distr_l.
      split; [lia|]. intros [E|E]; [exfalso; exact (eqb_false _ _ e E)|].
      specialize (HEL E). lia. }
  intros HO. exact (proj1 (HG _ x xC s sC H HC (le_n _) HO)).
Qed.

Lemma scan_unf Sx f t fl out fp np txt n j st s g :
  scan Sx f t fl out fp np txt n j st s (Acc_intro _ g) =
  match bdec (j <? n) with
  | left Hj =>
      scan Sx f t fl out fp np txt n (j + 1) (walk t fl (PrimString.get txt j) st (Zwf_well_founded 0 (φ st)))
        (emit_chain Sx f t out fp np (j + 1) (walk t fl (PrimString.get txt j) st (Zwf_well_founded 0 (φ st))) s
           (Zwf_well_founded 0 (φ (walk t fl (PrimString.get txt j) st (Zwf_well_founded 0 (φ st))))))
        (g _ (dec_step n j Hj))
  | right _ => s
  end.
Proof. reflexivity. Qed.

Lemma scan_add t fl out fp np txt n j st k H :
  scan nat cntf t fl out fp np txt n j st k H = (k + scan nat cntf t fl out fp np txt n j st 0 H)%nat.
Proof.
  assert (G : forall N j st H k, (Z.to_nat (gap n j) <= N)%nat ->
            scan nat cntf t fl out fp np txt n j st k H = (k + scan nat cntf t fl out fp np txt n j st 0 H)%nat).
  { induction N as [|N IH]; intros j' st' [g] k' HN; rewrite !scan_unf;
      (destruct (bdec (j' <? n)) as [Hl|]; [|lia]); pose proof (gap_step _ _ Hl) as [Hg1 Hg2].
    { lia. }
    rewrite (IH (j' + 1) _ _ (emit_chain _ _ _ _ _ _ _ _ k' _) ltac:(lia)).
    rewrite (IH (j' + 1) _ _ (emit_chain _ _ _ _ _ _ _ _ 0%nat _) ltac:(lia)).
    rewrite (emit_chain_add _ _ _ _ _ _ k'). lia. }
  apply (G _ j st H k (le_n _)).
Qed.

Lemma scan_time Sx SxC f fC t tC fl flC out outC fp fpC np npC txt txtC n nC j jC st stC s sC H HC
    cf C (D : int -> nat) K A (Nn : int) :
  (cf + 60 <= C)%nat ->
  (forall s sC i iC q qC, (cost (fC s sC) + cost (extract (fC s sC) i iC) + cost (extract (extract (fC s sC) i iC) q qC) <= cf)%nat) ->
  D 0 = 0%nat -> (K * 60 + 200 <= A)%nat ->
  (forall c y, (φ y < φ Nn)%Z -> WalkHyp t fl c D K y) ->
  (forall c y Hy, (φ y < φ Nn)%Z -> (φ (walk t fl c y Hy) < φ Nn)%Z) ->
  (forall y, (φ y < φ Nn)%Z -> OutHyp out fp y) ->
  (φ st < φ Nn)%Z ->
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract
     (scan_cost stepsCM Sx SxC) f fC) t tC) fl flC) out outC) fp fpC) np npC) txt txtC) n nC) j jC) st stC) s sC) H HC)
     <= Z.to_nat (gap n j) * (A + A + 500) + D st * A + scan nat cntf t fl out fp np txt n j st 0 H * (C + 200) + 50)%nat.
Proof.
  intros HCf Hf HD0 HA HW HWN HOut. unfold scan_cost. cbn.
  match goal with |- context [@cost ?T (?G n nC j jC st stC s sC H HC)] => set (Gf := G) end.
  assert (HG : forall N j jC st stC s sC H HC, (Z.to_nat (gap n j) <= N)%nat -> (φ st < φ Nn)%Z ->
       (cost (Gf n nC j jC st stC s sC H HC) <=
        Z.to_nat (gap n j) * (A + A + 500) + D st * A + scan nat cntf t fl out fp np txt n j st 0 H * (C + 200) + 50)%nat).
  { induction N as [|N IH]; intros j' jC' st' stC' s' sC' [g] HC' HN Hst;
      rewrite (scan_unf nat cntf);
      unfold Gf at 1; cbn; fold Gf; clearbody Gf;
      cost_simpl; zpart; projc;
      pose proof (bdec_time (j' <? n) (bool_w (j' <? n))) as HB;
      cost_destruct (bdec (j' <? n)); cost_simpl; zpart; projc.
    - exfalso. pose proof (gap_step _ _ e). lia.
    - lia.
    - pose proof (gap_step _ _ e) as [Hg1 Hg2].
      match goal with |- context [@cost ?T ?X] =>
        lazymatch X with
        | extract (extract (extract (extract (walk_cost stepsCM ?t ?tC) ?fl ?flC) ?c ?cC) ?x ?xC) ?H ?HC =>
            let Hc := fresh "Hw" in
            pose proof (walk_time t tC fl flC c cC x xC H HC D K A HD0 HA (HW c x Hst) : (@cost T X + _ <= _)%nat) as Hc;
            revert Hc; generalize (@cost T X); intros ? Hc
        end end.
      set (st2 := walk t fl (PrimString.get txt j') st' _) in *.
      assert (Hst2 : (φ st2 < φ Nn)%Z) by apply HWN, Hst.
      match goal with |- context [@cost ?T ?X] =>
        lazymatch X with
        | extract (extract (extract (extract (extract (extract (extract (extract (extract (emit_chain_cost stepsCM ?Sx ?SxC) ?f ?fC) ?t ?tC) ?out ?outC) ?fp ?fpC) ?np ?npC) ?je ?jeC) ?x ?xC) ?s ?sC) ?H ?HC =>
            bound X (emit_chain_time Sx SxC f fC t tC out outC fp fpC np npC je jeC x xC s sC H HC cf C HCf Hf (HOut x Hst2))
        end end.
      assert (HN' : (Z.to_nat (gap n (j' + 1)) <= N)%nat) by lia.
      match goal with |- context [@cost ?T (Gf n nC (j' + 1)%uint63 ?w ?a ?aC ?b ?bC ?h ?e)] =>
        pose proof (IH (j' + 1)%uint63 w a aC b bC h e HN' Hst2) as HI end.
      cost_align HI.
      rewrite scan_add.
      set (EC := emit_chain nat cntf t out fp np _ st2 0%nat _) in *.
      set (SC := scan nat cntf t fl out fp np txt n (j' + 1) st2 0%nat _) in *.
      replace (Z.to_nat (gap n j')) with (S (Z.to_nat (gap n (j' + 1)))) by lia.
      rewrite Nat.mul_succ_l, Nat.mul_add_distr_r.
      lia.
    - lia. }
  intros Hst. exact (HG _ j jC st stC s sC H HC (le_n _) Hst).
Qed.

(* ---- cost proofs, part devC ---- *)
#[local] Arguments Uint63.to_Z : simpl never.
#[local] Arguments gap : simpl never.
#[local] Arguments fst_cost : simpl never.
#[local] Arguments snd_cost : simpl never.

Ltac zpart1 :=
  repeat match goal with
  | |- context [cost ?X] => first [change (cost X) with 0%nat | change (cost X) with 1%nat]
  | |- context [price ?X] => first [change (price X) with 0%nat | change (price X) with 1%nat]
  end.

Lemma char_lt256 (s : PrimString.string) (k : int) : (0 <= φ (PrimString.get s k) < 256)%Z.
Proof.
  rewrite PrimStringAxioms.get_spec.
  pose proof (PrimStringAxioms.to_list_char63_valid s) as HV.
  destruct (Nat.lt_ge_cases (Z.to_nat (φ k)) (List.length (PrimStringAxioms.to_list s))) as [Hl|Hl].
  - pose proof (nth_In _ 0 Hl) as Hin. rewrite Forall_forall in HV.
    specialize (HV _ Hin). unfold PrimStringAxioms.char63_valid in HV.
    set (z := nth _ _ _) in *. rewrite <- HV.
    rewrite Uint63.land_spec'. pose proof (phi_bnd z).
    change (φ 255) with (Z.ones 8). rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound (φ z) (2 ^ 8) ltac:(lia)). change (2 ^ 8)%Z with 256%Z in *. lia.
  - rewrite nth_overflow by exact Hl. change (φ 0) with 0%Z. lia.
Qed.

Lemma pstr_lt256 s z : In z (pstr s) -> (0 <= z < 256)%Z.
Proof.
  unfold pstr. intros Hz. apply in_map_iff in Hz as [k [<- _]]. apply char_lt256.
Qed.

Lemma pref_chr pats t cap W : TrieInv t cap W -> Pref pats t W ->
  forall v, (0 < φ v < φ (tn t))%Z -> (0 <= φ (tchr t).[v] < 256)%Z.
Proof.
  intros Ht HP v Hv. destruct (ti_par _ _ _ Ht v Hv) as [_ Ew].
  destruct (HP v ltac:(lia)) as [E | [i [_ [r Er]]]].
  - rewrite E in Ew. destruct (W (tpar t).[v]); discriminate.
  - apply (pstr_lt256 pats.[i]). change (pstr pats.[i]) with (pw pats i). rewrite Er, Ew.
    apply in_or_app. left. apply in_or_app. right. left. reflexivity.
Qed.

Lemma nodup_256 (S : list Z) : NoDup S -> (forall z, In z S -> (0 <= z < 256)%Z) -> (List.length S <= 256)%nat.
Proof.
  intros HN HS.
  assert (Hi : incl S (map Z.of_nat (seq 0 256))).
  { intros z Hz. specialize (HS z Hz). apply in_map_iff. exists (Z.to_nat z). split; [lia|].
    apply in_seq. lia. }
  pose proof (NoDup_incl_length HN Hi) as Hl. rewrite length_map, length_seq in Hl. exact Hl.
Qed.

Lemma lok_of_inv t cap W u c : TrieInv t cap W ->
  (forall v, (0 < φ v < φ (tn t))%Z -> (0 <= φ (tchr t).[v] < 256)%Z) ->
  (φ u < φ (tn t))%Z -> lok (tchr t) (tns t) c 257 ((tfc t).[u]).
Proof.
  intros Ht Hc Hu.
  assert (G : forall k v (S : list Z), (v = 0 \/ Reach (tns t) ((tfc t).[u]) v) -> NoDup S ->
            (forall z, In z S -> (0 <= z < 256)%Z) ->
            (forall y, Reach (tns t) v y -> ~ In (φ (tchr t).[y]) S) ->
            (257 <= k + List.length S)%nat -> lok (tchr t) (tns t) c k v).
  { induction k as [|k IH]; intros v S Hv HN HS HY Hk.
    - pose proof (nodup_256 S HN HS). lia.
    - simpl. destruct (int_eq_dec v 0) as [E|Hv0]; [left; exact E|]. right.
      destruct Hv as [E|Hr]; [contradiction|].
      destruct (int_eq_dec (tchr t).[v] c) as [E|Hcv]; [left; exact E|]. right.
      destruct ((tns t).[v] <? v) eqn:El; [|left; reflexivity]. right.
      apply ltb_true in El.
      pose proof (proj1 (ti_ch _ _ _ Ht u Hu v) Hr) as [Hvn Hpv].
      apply IH with (S := (φ (tchr t).[v]) :: S).
      + destruct (int_eq_dec (tns t).[v] 0) as [E|E]; [left; exact E|right].
        apply (Reach_trans _ _ v); [exact Hr|]. apply R_next; [exact Hv0|]. apply R_here. exact E.
      + constructor; [|exact HN]. apply HY. apply R_here. exact Hv0.
      + intros z [<-|Hz]; [apply Hc; exact Hvn | apply HS; exact Hz].
      + intros y Hy [E|Hin].
        * assert (Hyl : (φ y <= φ (tns t).[v])%Z).
          { apply (Reach_le (tns t) (φ v)); [| lia | exact Hy].
            intros x Hx. apply (ti_ns _ _ _ Ht). lia. }
          assert (Hry : Reach (tns t) ((tfc t).[u]) y).
          { apply (Reach_trans _ _ v); [exact Hr|]. apply R_next; [exact Hv0| exact Hy]. }
          pose proof (proj1 (ti_ch _ _ _ Ht u Hu y) Hry) as [Hyn Hpy].
          destruct (ti_par _ _ _ Ht v Hvn) as [_ Ewv]. destruct (ti_par _ _ _ Ht y Hyn) as [_ Ewy].
          assert (y = v).
          { apply (ti_inj _ _ _ Ht); [lia | lia |]. rewrite Ewv, Ewy, Hpv, Hpy, E. reflexivity. }
          subst y. lia.
        * apply (HY y); [apply R_next; [exact Hv0 | exact Hy] | exact Hin].
      + simpl. lia. }
  apply (G 257%nat _ []).
  - destruct (int_eq_dec (tfc t).[u] 0) as [E|E]; [left; exact E | right; apply R_here; exact E].
  - constructor.
  - intros z [].
  - intros y _ [].
  - simpl. lia.
Qed.

Lemma RI_lok pats dd kk st (k na : int) :
  (φ na = Z.of_nat (List.length (Ld pats dd)))%Z -> (φ k = Z.of_nat kk)%Z -> (k <? na) = true ->
  RI pats (1 + Ptot pats) dd kk st -> forall c,
  lok (tchr (bt st)) (tns (bt st)) c 257 ((tfc (bt st)).[(bcur st).[(bact st).[k]]]).
Proof.
  intros Hna Hk Hlt HI c. apply ltb_true in Hlt.
  destruct HI as (W & Ht & HPf & Hdp & HN & Hlc & Hla & Hc1 & Hc2 & Ha1 & Hw & Ha2).
  assert (Ei : (bact st).[k] = nth kk (Ld pats dd) 0) by (rewrite (Ha1 k ltac:(lia)); f_equal; lia).
  assert (Hin : In ((bact st).[k]) (Ld pats dd)) by (rewrite Ei; apply nth_In; lia).
  apply Ld_In in Hin as [Him _].
  assert (Hnin : ~ In ((bact st).[k]) (firstn kk (Ld pats dd)))
    by (rewrite Ei; apply nth_not_in_firstn; [apply Ld_NoDup | lia]).
  destruct (Hc2 _ Him Hnin) as [Hu _].
  apply (lok_of_inv (bt st) (1 + Ptot pats) W); [exact Ht | apply (pref_chr pats _ _ W Ht HPf) | exact Hu].
Qed.

Lemma round_loop_time pats patsC d dC na naC k kC st stC H HC (dd kk : nat) A :
  (257 * 60 + 400 <= A)%nat ->
  (φ d = Z.of_nat dd)%Z -> (φ na = Z.of_nat (List.length (Ld pats dd)))%Z -> (φ k = Z.of_nat kk)%Z ->
  (kk <= List.length (Ld pats dd))%nat -> RI pats (1 + Ptot pats) dd kk st ->
  (cost (extract (extract (extract (extract (extract (round_loop_cost stepsCM pats patsC) d dC) na naC) k kC) st stC) H HC)
     <= Z.to_nat (gap na k) * A + 50)%nat.
Proof.
  intros HA Hd Hna. unfold round_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G pats patsC d dC na naC k kC st stC H HC)] => set (Gf := G) end.
  assert (HG : forall N kk k kC st stC H HC, (Z.to_nat (gap na k) <= N)%nat ->
       (φ k = Z.of_nat kk)%Z -> (kk <= List.length (Ld pats dd))%nat -> RI pats (1 + Ptot pats) dd kk st ->
       (cost (Gf pats patsC d dC na naC k kC st stC H HC) <= Z.to_nat (gap na k) * A + 50)%nat).
  { induction N as [|N IH]; intros kk' k' kC' st' stC' [g] HC' HN Hk Hkk HI;
      unfold Gf at 1; cbn; fold Gf; clearbody Gf;
      cost_simpl; zpart; projc;
      pose proof (bdec_time (k' <? na) (bool_w (k' <? na))) as HB;
      cost_destruct (bdec (k' <? na)); cost_simpl; zpart; projc.
    - exfalso. pose proof (gap_step _ _ e). lia.
    - lia.
    - pose proof (gap_step _ _ e) as [Hg1 Hg2].
      pose proof (RI_lok pats dd kk' st' k' na Hna Hk e HI) as Hlok.
      match goal with |- context [@cost ?T ?X] =>
        lazymatch X with
        | extract (extract (add_child_cost stepsCM ?t ?tC) ?u ?uC) ?c ?cC =>
            bound X (add_child_time t tC u uC c cC 257 (Hlok c))
        end end.
      pose proof (round_loop_step pats _ eq_refl dd d Hd na Hna kk' k' st' Hk e HI) as HS.
      unfold round_next in HS. cbv zeta in HS.
      assert (HN' : (Z.to_nat (gap na (k' + 1)) <= N)%nat) by lia.
      assert (Hk1 : (φ (k' + 1) = Z.of_nat (S kk'))%Z).
      { pose proof (ltb_true _ _ e). rewrite phi_add1; [lia|]. pose proof (phi_bnd na). lia. }
      assert (Hkk1 : (S kk' <= List.length (Ld pats dd))%nat) by (pose proof (ltb_true _ _ e); lia).
      replace (Z.to_nat (gap na k')) with (S (Z.to_nat (gap na (k' + 1)))) by lia.
      rewrite Nat.mul_succ_l.
      destruct (d + 1 <? PrimString.length pats.[(bact st').[k']]) eqn:Eb; cost_simpl; zpart; projc.
      + match goal with |- context [@cost ?T (?Gf' pats patsC d dC na naC (k' + 1)%uint63 ?w ?st2 ?stC2 ?h ?e)] =>
         assert (HI2 : RI pats (1 + Ptot pats) dd (S kk') st2) by exact HS;
         pose proof (IH _ (k' + 1)%uint63 w st2 stC2 h e HN' Hk1 Hkk1 HI2) as HIH end;
        cost_align HIH; zpart1; lia.
      + match goal with |- context [@cost ?T (?Gf' pats patsC d dC na naC (k' + 1)%uint63 ?w ?st2 ?stC2 ?h ?e)] =>
         assert (HI2 : RI pats (1 + Ptot pats) dd (S kk') st2) by exact HS;
         pose proof (IH _ (k' + 1)%uint63 w st2 stC2 h e HN' Hk1 Hkk1 HI2) as HIH end;
        cost_align HIH; zpart1; lia.
    - lia. }
  intros Hk Hkk HI. exact (HG _ kk k kC st stC H HC (le_n _) Hk Hkk HI).
Qed.

Lemma RS_RI0 pats cap d st : RS pats cap d st -> RI pats cap d 0 (mkB (bact st) (bcur st) 0 (bt st)).
Proof.
  intros (W & Ht & HPf & Hdp & HN & Hlc & Hla & Hc & Hw & Ha).
  exists W. cbn [bt bcur bact bw]. split; [exact Ht|]. split; [exact HPf|].
  split; [intros x Hx; specialize (Hdp x Hx); lia|].
  split; [lia|]. split; [exact Hlc|]. split; [exact Hla|].
  split; [intros i []|].
  split; [intros i Hi _; exact (Hc i Hi)|].
  split; [intros j Hj; apply Ha; lia|].
  split; [reflexivity|]. intros j Hj. rewrite phi0 in Hj. pose proof (phi_bnd j). lia.
Qed.

Lemma RS_bw pats cap d st : RS pats cap d st -> (φ (bw st) = Z.of_nat (List.length (Ld pats d)))%Z.
Proof. intros (W & Ht & HPf & Hdp & HN & Hlc & Hla & Hc & Hw & Ha). exact Hw. Qed.

Lemma rounds_time pats patsC L LC dm dmC st stC H HC (d : nat) A :
  (257 * 60 + 400 <= A)%nat ->
  (φ dm = Z.of_nat d)%Z -> RS pats (1 + Ptot pats) d st ->
  (cost (extract (extract (extract (extract (rounds_cost stepsCM pats patsC) L LC) dm dmC) st stC) H HC)
     <= Z.to_nat (Ptot pats - sumd pats d) * A + Z.to_nat (gap L dm) * 200 + 50)%nat.
Proof.
  intros HA. unfold rounds_cost. cbn.
  match goal with |- context [@cost ?T (?G pats patsC L LC dm dmC st stC H HC)] => set (Gf := G) end.
  assert (HG : forall N d dm dmC st stC H HC, (Z.to_nat (gap L dm) <= N)%nat ->
       (φ dm = Z.of_nat d)%Z -> RS pats (1 + Ptot pats) d st ->
       (cost (Gf pats patsC L LC dm dmC st stC H HC) <= Z.to_nat (Ptot pats - sumd pats d) * A + Z.to_nat (gap L dm) * 200 + 50)%nat).
  { induction N as [|N IH]; intros d' dm' dmC' st' stC' [g] HC' HN Hd HS;
      unfold Gf at 1; cbn; fold Gf; clearbody Gf;
      cost_simpl; zpart; projc;
      pose proof (bdec_time (dm' <? L) (bool_w (dm' <? L))) as HB;
      cost_destruct (bdec (dm' <? L)); cost_simpl; zpart; projc; zpart1.
    - exfalso. pose proof (gap_step _ _ e). lia.
    - generalize (Z.to_nat (Ptot pats - sumd pats d') * A)%nat. intros. lia.
    - pose proof (gap_step _ _ e) as [Hg1 Hg2].
      pose proof (RS_bw _ _ _ _ HS) as Hbw.
      match goal with |- context [@cost ?T ?X] =>
        lazymatch X with
        | extract (extract (extract (extract (extract (round_loop_cost stepsCM ?p ?pC) ?a ?aC) ?b ?bC) ?c ?cC) ?s ?sC) ?h ?hC =>
            bound X (round_loop_time p pC a aC b bC c cC s sC h hC d' 0 A HA Hd Hbw phi0 (Nat.le_0_l _) (RS_RI0 _ _ _ _ HS))
        end end.
      pose proof (round_step pats _ eq_refl d' dm' Hd st' HS) as HS2.
      assert (HN' : (Z.to_nat (gap L (dm' + 1)) <= N)%nat) by lia.
      assert (Hd1 : (φ (dm' + 1) = Z.of_nat (S d'))%Z).
      { pose proof (ltb_true _ _ e). rewrite phi_add1; [lia|]. pose proof (phi_bnd L). lia. }
      match goal with |- context [@cost ?T (?Gf' pats patsC L LC (dm' + 1)%uint63 ?w ?st2 ?stC2 ?h ?e)] =>
         assert (HI2 : RS pats (1 + Ptot pats) (S d') st2) by exact HS2;
         pose proof (IH (S d') (dm' + 1)%uint63 w st2 stC2 h e HN' Hd1 HI2) as HIH end.
      cost_align HIH. zpart1.
      pose proof (sumd_S pats d') as ES. pose proof (sumd_le pats (S d')) as ESl.
      replace (Z.to_nat (gap L dm')) with (S (Z.to_nat (gap L (dm' + 1)))) by lia.
      replace (Z.to_nat (Ptot pats - sumd pats d')) with (List.length (Ld pats d') + Z.to_nat (Ptot pats - sumd pats (S d')))%nat by lia.
      assert (Eg : Z.to_nat (gap (bw st') 0) = List.length (Ld pats d')) by (unfold gap; rewrite phi0; lia).
      rewrite Eg in Hc. rewrite Nat.mul_succ_l, Nat.mul_add_distr_r. lia.
    - generalize (Z.to_nat (Ptot pats - sumd pats d') * A)%nat. intros. lia. }
  intros Hd HS. exact (HG _ d dm dmC st stC H HC (le_n _) Hd HS).
Qed.

(* ---- cost proofs, part devD ---- *)
#[local] Arguments Uint63.to_Z : simpl never.
#[local] Arguments gap : simpl never.
#[local] Arguments fst_cost : simpl never.
#[local] Arguments snd_cost : simpl never.

Lemma fail_loop_unf t fp N v fl out g :
  fail_loop t fp N v fl out (Acc_intro _ g) =
  match bdec (v <? N) with
  | left Hv =>
      fail_loop t fp N (v + 1)
        fl.[v <- if (tpar t).[v] =? 0 then 0 else walk t fl (tchr t).[v] fl.[(tpar t).[v]] (Zwf_well_founded 0 (φ fl.[(tpar t).[v]]))]
        out.[v <- if fp.[if (tpar t).[v] =? 0 then 0 else walk t fl (tchr t).[v] fl.[(tpar t).[v]] (Zwf_well_founded 0 (φ fl.[(tpar t).[v]]))] =? 0
                  then out.[if (tpar t).[v] =? 0 then 0 else walk t fl (tchr t).[v] fl.[(tpar t).[v]] (Zwf_well_founded 0 (φ fl.[(tpar t).[v]]))]
                  else if (tpar t).[v] =? 0 then 0 else walk t fl (tchr t).[v] fl.[(tpar t).[v]] (Zwf_well_founded 0 (φ fl.[(tpar t).[v]]))]
        (g _ (dec_step N v Hv))
  | right _ => (fl, out)
  end.
Proof. reflexivity. Qed.

Lemma fail_loop_pi t fp N : forall v fl out H1 H2,
  fail_loop t fp N v fl out H1 = fail_loop t fp N v fl out H2.
Proof.
  assert (G : forall n v fl out H1 H2, (Z.to_nat (gap N v) <= n)%nat ->
            fail_loop t fp N v fl out H1 = fail_loop t fp N v fl out H2).
  { induction n as [|n IH]; intros v fl out [g1] [g2] Hn; rewrite !fail_loop_unf;
      destruct (bdec (v <? N)) as [Hv|]; try reflexivity; pose proof (gap_step _ _ Hv) as [Hg1 Hg2].
    - lia.
    - apply IH. lia. }
  intros. apply (G _ v fl out H1 H2 (le_n _)).
Qed.

Lemma fail_loop_frame t fp N : forall v fl out H y, (φ y < φ v)%Z ->
  (fst (fail_loop t fp N v fl out H)).[y] = fl.[y].
Proof.
  assert (G : forall n v fl out H y, (Z.to_nat (gap N v) <= n)%nat -> (φ y < φ v)%Z ->
            (fst (fail_loop t fp N v fl out H)).[y] = fl.[y]).
  { induction n as [|n IH]; intros v fl out [g] y Hn Hy; rewrite !fail_loop_unf;
      destruct (bdec (v <? N)) as [Hv|]; try reflexivity; pose proof (gap_step _ _ Hv) as [Hg1 Hg2].
    - lia.
    - pose proof (ltb_true _ _ Hv).
      rewrite IH; [| lia | rewrite phi_add1; [lia | pose proof (phi_bnd N); lia]].
      apply aget_set_other. intro E. subst. lia. }
  intros. apply (G _ v fl out H y (le_n _)); assumption.
Qed.

Fixpoint hsum (h : int -> nat) (a : Z) (n : nat) : nat :=
  match n with
  | O => 0%nat
  | S n' => (h (of_Z a) + hsum h (a + 1) n')%nat
  end.

Definition hF (t : trie) (D : int -> nat) (F : array int) (A : nat) (w : int) : nat :=
  ((S (D F.[(tpar t).[w]]) - D F.[w]) * A)%nat.
#[local] Arguments hF : simpl never.
#[local] Arguments hsum : simpl never.

Lemma hsum_S h a n : hsum h a (S n) = (h (of_Z a) + hsum h (a + 1) n)%nat.
Proof. reflexivity. Qed.

Lemma fail_loop_time t tC fp fpC N NC v vC fl flC out outC H HC (D : int -> nat) K A (F : array int) :
  D 0 = 0%nat -> (K * 60 + 200 <= A)%nat ->
  (forall c y, (φ y < φ N)%Z -> lok (tchr t) (tns t) c K ((tfc t).[y])) ->
  (forall y, (0 < φ y < φ N)%Z -> (φ F.[y] < φ y)%Z /\ (D F.[y] < D y)%nat) ->
  (forall c y, (φ y < φ N)%Z -> lookup t y c <> 0 -> D (lookup t y c) = S (D y)) ->
  (forall w, (0 < φ w < φ N)%Z -> (φ (tpar t).[w] < φ w)%Z /\ (D F.[w] <= S (D F.[(tpar t).[w]]))%nat) ->
  (φ N <= φ (PArray.length fl))%Z -> (1 <= φ v)%Z ->
  fst (fail_loop t fp N v fl out H) = F ->
  (cost (extract (extract (extract (extract (extract (extract (fail_loop_cost stepsCM t tC) fp fpC) N NC) v vC) fl flC) out outC) H HC)
     <= Z.to_nat (gap N v) * (A + 100) + hsum (hF t D F A) (φ v) (Z.to_nat (gap N v)) + 50)%nat.
Proof.
  intros HD0 HA HL HDF HY Hpar. unfold fail_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G t tC fp fpC N NC v vC fl flC out outC H HC)] => set (Gf := G) end.
  assert (HG : forall n v vC fl flC out outC H HC, (Z.to_nat (gap N v) <= n)%nat ->
       (φ N <= φ (PArray.length fl))%Z -> (1 <= φ v)%Z -> fst (fail_loop t fp N v fl out H) = F ->
       (cost (Gf t tC fp fpC N NC v vC fl flC out outC H HC) <=
        Z.to_nat (gap N v) * (A + 100) + hsum (hF t D F A) (φ v) (Z.to_nat (gap N v)) + 50)%nat).
  { induction n as [|n IH]; intros v' vC' fl' flC' out' outC' [g] HC' Hn Hlen Hv1 Hfin;
      unfold Gf at 1; cbn; fold Gf; clearbody Gf;
      cost_simpl; zpart; projc; zpart1;
      pose proof (bdec_time (v' <? N) (bool_w (v' <? N))) as HB;
      cost_destruct (bdec (v' <? N)); cost_simpl; zpart; projc; zpart1.
    - exfalso. pose proof (gap_step _ _ e). lia.
    - generalize (hsum (hF t D F A) (φ v') (Z.to_nat (gap N v'))). intros. lia.
    - pose proof (gap_step _ _ e) as [Hg1 Hg2]. pose proof (ltb_true _ _ e) as Hlt.
      rewrite fail_loop_unf in Hfin.
      destruct (bdec (v' <? N)) as [Hv|Hv]; [| rewrite e in Hv; discriminate].
      assert (Hv1' : (φ (v' + 1) = φ v' + 1)%Z) by (rewrite phi_add1; [lia | pose proof (phi_bnd N); lia]).
      assert (HFy : forall y, (φ y < φ v')%Z -> F.[y] = fl'.[y]).
      { intros y Hy. rewrite <- Hfin, fail_loop_frame by lia. apply aget_set_other. intro E. subst. lia. }
      assert (HFv : F.[v'] = (if (tpar t).[v'] =? 0 then 0 else walk t fl' (tchr t).[v'] fl'.[(tpar t).[v']] (Zwf_well_founded 0 (φ fl'.[(tpar t).[v']])))).
      { rewrite <- Hfin, fail_loop_frame by lia. apply aget_set_same. apply ltb_spec. lia. }
      assert (HN' : (Z.to_nat (gap N (v' + 1)) <= n)%nat) by lia.
      replace (Z.to_nat (gap N v')) with (S (Z.to_nat (gap N (v' + 1)))) by lia.
      rewrite hsum_S, Uint63.of_to_Z, <- Hv1', Nat.mul_succ_l.
      pose proof (Hpar v' ltac:(lia)) as [Hpv HDv].
      destruct ((tpar t).[v'] =? 0) eqn:Eu.
      + apply eqb_true in Eu.
        destruct (fp.[0] =? 0) eqn:Eo; cost_simpl; zpart; projc; zpart1;
        (match goal with |- context [@cost ?T (?Gf' t tC fp fpC N NC (v' + 1)%uint63 ?w ?fl2 ?flC2 ?o2 ?oC2 ?h ?e)] =>
          assert (Hf2 : fst (fail_loop t fp N (v' + 1) fl2 o2 h) = F) by (rewrite <- Hfin; f_equal; apply fail_loop_pi);
          pose proof (IH (v' + 1)%uint63 w fl2 flC2 o2 oC2 h e HN' ltac:(rewrite alength_set; exact Hlen) ltac:(lia) Hf2) as HIH end);
        cost_align HIH; zpart1;
        generalize (hF t D F A v'); intros; lia.
      + pose proof (eqb_false _ _ Eu) as Hu0. pose proof (pos_of_nz _ Hu0) as Hu1.
        destruct (HDF ((tpar t).[v']) ltac:(lia)) as [HFu1 HFu2].
        try rewrite Eu in HFv.
        pose proof (HFy _ Hpv) as HFp.
        assert (HWk : WalkHyp t fl' (tchr t).[v'] D K fl'.[(tpar t).[v']]).
        { rewrite <- HFp. split; [|split].
          - intros y Hy. apply HL. lia.
          - intros y Hy Hfy. rewrite <- (HFy y) by lia. rewrite <- (HFy y) in Hfy by lia.
            apply (HDF y). lia.
          - intros y Hy. apply HY. lia. }
        match goal with |- context [@cost ?T ?X] =>
          lazymatch X with
          | extract (extract (extract (extract (walk_cost stepsCM ?t ?tC) ?fl ?flC) ?c ?cC) ?x ?xC) ?H ?HC =>
              let Hc := fresh "Hw" in
              pose proof (walk_time t tC fl flC c cC x xC H HC D K A HD0 HA HWk : (@cost T X + _ <= _)%nat) as Hc;
              revert Hc; generalize (@cost T X); intros ? Hc
          end end.
        rewrite <- HFv, <- HFp in Hw.
        assert (Hh : (hF t D F A v' + D F.[v'] * A = D F.[(tpar t).[v']] * A + A)%nat).
        { unfold hF. transitivity ((S (D F.[(tpar t).[v']]) - D F.[v'] + D F.[v']) * A)%nat;
            [symmetry; apply Nat.mul_add_distr_r|]. rewrite Nat.sub_add by lia. simpl. lia. }
        set (f := walk _ _ _ _ _) in *.
        destruct (fp.[f] =? 0) eqn:Eo; cost_simpl; zpart; projc; zpart1;
        (match goal with |- context [@cost ?T (?Gf' t tC fp fpC N NC (v' + 1)%uint63 ?w ?fl2 ?flC2 ?o2 ?oC2 ?h ?e)] =>
          assert (Hf2 : fst (fail_loop t fp N (v' + 1) fl2 o2 h) = F) by (rewrite <- Hfin; f_equal; apply fail_loop_pi);
          pose proof (IH (v' + 1)%uint63 w fl2 flC2 o2 oC2 h e HN' ltac:(rewrite alength_set; exact Hlen) ltac:(lia) Hf2) as HIH end);
        cost_align HIH; zpart1; lia.
    - generalize (hsum (hF t D F A) (φ v') (Z.to_nat (gap N v'))). intros. lia. }
  intros Hlen Hv1 Hfin. exact (HG _ v vC fl flC out outC H HC (le_n _) Hlen Hv1 Hfin).
Qed.

(* ---- cost proofs, part devE ---- *)
#[local] Arguments Uint63.to_Z : simpl never.
#[local] Arguments gap : simpl never.

Lemma sum_remove (h : int -> nat) a l : NoDup l ->
  (list_sum (map h l) <= h a + list_sum (map h (remove int_eq_dec a l)))%nat.
Proof.
  induction l as [|x l IH]; intros HN; simpl; [lia|].
  inversion HN as [|? ? Hx HN']; subst.
  destruct (int_eq_dec a x) as [->|Hne].
  - rewrite notin_remove by exact Hx. lia.
  - simpl. specialize (IH HN'). lia.
Qed.

Lemma nodup_remove a (l : list int) : NoDup l -> NoDup (remove int_eq_dec a l).
Proof.
  induction l as [|x l IH]; intros HN; simpl; [constructor|].
  inversion HN as [|? ? Hx HN']; subst.
  destruct (int_eq_dec a x); [apply IH; exact HN'|].
  constructor; [|apply IH; exact HN']. intro Hin. apply in_remove in Hin as [Hin _]. contradiction.
Qed.

Lemma sum_surj {B} (h : int -> nat) (g : B -> int) (l2 : list B) : forall l1, NoDup l1 ->
  (forall x, In x l1 -> exists y, In y l2 /\ g y = x) ->
  (list_sum (map h l1) <= list_sum (map (fun y => h (g y)) l2))%nat.
Proof.
  induction l2 as [|y l2 IH]; intros l1 HN Hs.
  - destruct l1 as [|x l1]; [simpl; lia|]. destruct (Hs x (or_introl eq_refl)) as [y [[] _]].
  - simpl. pose proof (sum_remove h (g y) l1 HN) as Hr.
    assert (IH' := IH (remove int_eq_dec (g y) l1) (nodup_remove (g y) l1 HN)).
    enough (list_sum (map h (remove int_eq_dec (g y) l1)) <= list_sum (map (fun y0 => h (g y0)) l2))%nat by lia.
    apply IH'. intros x Hx. apply in_remove in Hx as [Hx Hne].
    destruct (Hs x Hx) as [y' [[<-|Hy'] Eg]]; [congruence|]. exists y'. split; assumption.
Qed.

Lemma hsum_list h : forall n a, hsum h a n = list_sum (map h (map (fun k => of_Z (a + Z.of_nat k)) (seq 0 n))).
Proof.
  induction n as [|n IH]; intros a; [reflexivity|].
  rewrite hsum_S, IH. simpl. rewrite Z.add_0_r. f_equal. f_equal.
  rewrite <- seq_shift, !map_map. apply map_ext. intros k. f_equal. lia.
Qed.

Lemma zsum_list (u : int -> Z) l : (forall i, In i l -> 0 <= u i)%Z ->
  Z.of_nat (list_sum (map (fun i => Z.to_nat (u i)) l)) = zsum u l.
Proof.
  induction l as [|x l IH]; intros Hu; [reflexivity|].
  simpl. rewrite Nat2Z.inj_add, IH by (intros; apply Hu; right; assumption).
  rewrite Z2Nat.id by (apply Hu; left; reflexivity). reflexivity.
Qed.

Section Fsum.
  Variable pats : array PrimString.string.
  Variables (t : trie) (cap : Z) (W : int -> list Z) (cur F : array int).
  Hypothesis Ht : TrieInv t cap W.
  Hypothesis HPf : Pref pats t W.
  Hypothesis Hcur : forall i, (φ i < m pats)%Z -> (φ cur.[i] < φ (tn t))%Z /\ W cur.[i] = pw pats i.
  Hypothesis HF0 : List.length (W F.[0]) = 0%nat.
  Hypothesis HFp : forall w, (0 < φ w < φ (tn t))%Z ->
    (List.length (W F.[w]) <= S (List.length (W F.[(tpar t).[w]])))%nat.

  Definition Dw (w : int) : nat := List.length (W w).
  Definition h0 (w : int) : nat := (S (Dw F.[(tpar t).[w]]) - Dw F.[w])%nat.

  Lemma isnode_app y z : IsNode t W (y ++ z) -> IsNode t W y.
  Proof.
    induction z as [|a z IH] using rev_ind; intros Hn; [rewrite app_nil_r in Hn; exact Hn|].
    rewrite app_assoc in Hn. apply IH. exact (isnode_prefix _ _ _ _ _ Ht Hn).
  Qed.

  Definition nd (i : int) (k : nat) : int :=
    match find (fun z => if list_eq_dec Z.eq_dec (W z) (firstn k (pw pats i)) then true else false)
               (iseq (φ (tn t))) with
    | Some z => z
    | None => 0
    end.

  Lemma tn_wB : (φ (tn t) < wB)%Z.
  Proof. pose proof (ti_cap _ _ _ Ht). pose proof (ti_n _ _ _ Ht). rewrite wB_val. lia. Qed.

  Lemma nd_spec i k : (φ i < m pats)%Z ->
    (φ (nd i k) < φ (tn t))%Z /\ W (nd i k) = firstn k (pw pats i).
  Proof.
    intros Hi.
    assert (Hn : IsNode t W (firstn k (pw pats i))).
    { apply (isnode_app _ (skipn k (pw pats i))). rewrite firstn_skipn.
      destruct (Hcur i Hi) as [H1 H2]. exists cur.[i]. split; assumption. }
    unfold nd. destruct (find _ _) as [z|] eqn:E.
    - apply find_some in E as [Hin Hp].
      destruct (list_eq_dec Z.eq_dec (W z) (firstn k (pw pats i))) as [Ew|]; [|discriminate].
      apply (iseq_In _ _ tn_wB) in Hin. split; assumption.
    - exfalso. destruct Hn as [z [Hz Ew]].
      assert (Hin : In z (iseq (φ (tn t)))) by (apply iseq_In; [exact tn_wB | exact Hz]).
      pose proof (find_none _ _ E z Hin) as Hp. cbv beta in Hp.
      destruct (list_eq_dec Z.eq_dec (W z) (firstn k (pw pats i))); [discriminate | contradiction].
  Qed.

  Lemma nd_0 i : (φ i < m pats)%Z -> nd i 0 = 0.
  Proof.
    intros Hi. destruct (nd_spec i 0 Hi) as [H1 H2].
    apply (ti_nil _ _ _ _ Ht H1). rewrite H2. reflexivity.
  Qed.

  Lemma nd_par i k : (φ i < m pats)%Z -> (k < Z.to_nat (plen pats i))%nat ->
    (0 < φ (nd i (S k)))%Z /\ (tpar t).[nd i (S k)] = nd i k.
  Proof.
    intros Hi Hk. pose proof (plen_len pats i) as Hl.
    destruct (nd_spec i (S k) Hi) as [H1 H2]. destruct (nd_spec i k Hi) as [H3 H4].
    rewrite firstn_snoc in H2 by lia.
    assert (Hnz : nd i (S k) <> 0).
    { intro E. rewrite E, (ti_root _ _ _ Ht) in H2. destruct (firstn k (pw pats i)); discriminate. }
    pose proof (pos_of_nz _ Hnz) as Hp. split; [exact Hp|].
    destruct (ti_par _ _ _ Ht (nd i (S k)) ltac:(lia)) as [Hpl Ew].
    rewrite H2 in Ew. apply app_inj_tail in Ew as [Ew _].
    apply (ti_inj _ _ _ Ht); [lia | exact H3 | rewrite <- Ew, H4; reflexivity].
  Qed.

  Lemma tele i : (φ i < m pats)%Z -> forall L, (L <= Z.to_nat (plen pats i))%nat ->
    (list_sum (map (fun k => h0 (nd i k)) (seq 1 L)) + Dw F.[nd i L] = L)%nat.
  Proof.
    intros Hi L. induction L as [|L IH]; intros HL.
    - simpl. rewrite nd_0 by exact Hi. exact HF0.
    - rewrite seq_S, map_app, list_sum_app. simpl.
      destruct (nd_par i L Hi ltac:(lia)) as [Hp Epar].
      pose proof (HFp (nd i (S L)) ltac:(split; [exact Hp | apply (nd_spec i (S L) Hi)])) as Hle.
      rewrite Epar in Hle. specialize (IH ltac:(lia)).
      unfold h0 at 2. rewrite Epar. unfold Dw in *. lia.
  Qed.

  Lemma pairs_sum (l : list int) : (forall i, In i l -> (φ i < m pats)%Z) ->
    (list_sum (map (fun y => h0 (nd (fst y) (snd y)))
       (flat_map (fun i => map (fun k => (i, k)) (seq 1 (Z.to_nat (plen pats i)))) l))
     <= list_sum (map (fun i => Z.to_nat (plen pats i)) l))%nat.
  Proof.
    induction l as [|i l IH]; intros Hl; [simpl; lia|].
    simpl. rewrite map_app, list_sum_app, map_map. cbn [fst snd].
    pose proof (tele i (Hl i (or_introl eq_refl)) _ (le_n _)).
    specialize (IH ltac:(intros; apply Hl; right; assumption)). lia.
  Qed.

  Lemma fsum : (hsum h0 1 (Z.to_nat (φ (tn t) - 1)) <= Z.to_nat (Ptot pats))%nat.
  Proof.
    pose proof tn_wB as HwB. pose proof (ti_n _ _ _ Ht) as HN.
    rewrite hsum_list.
    set (l1 := map (fun k => of_Z (1 + Z.of_nat k)) (seq 0 (Z.to_nat (φ (tn t) - 1)))).
    assert (Hl1 : forall x, In x l1 -> (1 <= φ x < φ (tn t))%Z).
    { intros x Hx. unfold l1 in Hx. apply in_map_iff in Hx as [k [<- Hk]]. apply in_seq in Hk.
      rewrite phi_of_Z by lia. lia. }
    assert (HN1 : NoDup l1).
    { unfold l1. apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
      intros a b Ha Hb E. apply in_seq in Ha, Hb.
      assert (E' : φ (of_Z (1 + Z.of_nat a)) = φ (of_Z (1 + Z.of_nat b))) by (rewrite E; reflexivity).
      rewrite !phi_of_Z in E' by lia. lia. }
    pose proof (m_bound pats) as Hm.
    eapply Nat.le_trans.
    - apply (sum_surj h0 (fun y => nd (fst y) (snd y))
               (flat_map (fun i => map (fun k => (i, k)) (seq 1 (Z.to_nat (plen pats i)))) (iseq (m pats)))
               l1 HN1).
      intros x Hx. specialize (Hl1 x Hx).
      destruct (HPf x ltac:(lia)) as [E | [i [Hi [r Er]]]].
      + exfalso. pose proof (ti_nil _ _ _ x Ht ltac:(lia) E). subst. rewrite phi0 in Hl1. lia.
      + assert (HWx : W x <> []).
        { intro E. pose proof (ti_nil _ _ _ x Ht ltac:(lia) E). subst. rewrite phi0 in Hl1. lia. }
        pose proof (plen_len pats i) as Hpl. rewrite Er, length_app in Hpl.
        exists (i, List.length (W x)). split.
        * apply in_flat_map. exists i. split; [apply iseq_In; [rewrite wB_val; lia | exact Hi]|].
          apply in_map_iff. exists (List.length (W x)). split; [reflexivity|].
          apply in_seq. destruct (W x); [contradiction|]. simpl in *. lia.
        * cbn [fst snd]. destruct (nd_spec i (List.length (W x)) Hi) as [H1 H2].
          apply (ti_inj _ _ _ Ht); [exact H1 | lia |]. rewrite H2, Er, firstn_app, Nat.sub_diag, firstn_all.
          simpl. apply app_nil_r.
    - eapply Nat.le_trans; [apply pairs_sum; intros i Hi; apply iseq_In in Hi; [exact Hi | rewrite wB_val; lia]|].
      apply Nat.eq_le_incl. apply Nat2Z.inj. rewrite zsum_list; [|intros; apply plen_bnd].
      unfold Ptot. rewrite Z2Nat.id; [reflexivity|]. apply zsum_nonneg. intros; apply plen_bnd.
  Qed.
End Fsum.

(* ---- cost proofs, part devF ---- *)
#[local] Arguments Uint63.to_Z : simpl never.
#[local] Arguments gap : simpl never.
#[local] Arguments fst_cost : simpl never.
#[local] Arguments snd_cost : simpl never.

Lemma zsum_elem f l i : In i l -> (forall j, In j l -> 0 <= f j)%Z -> (f i <= zsum f l)%Z.
Proof.
  induction l as [|x l IH]; intros Hi Hf; [destruct Hi|]. simpl.
  destruct Hi as [<-|Hi].
  - pose proof (zsum_nonneg f l ltac:(intros; apply Hf; right; assumption)). lia.
  - pose proof (Hf x (or_introl eq_refl)). specialize (IH Hi ltac:(intros; apply Hf; right; assumption)). lia.
Qed.

Lemma plen_le_Ptot pats i : (φ i < m pats)%Z -> (plen pats i <= Ptot pats)%Z.
Proof.
  intros Hi. pose proof (m_bound pats). unfold Ptot. apply zsum_elem.
  - apply iseq_In; [rewrite wB_val; lia | exact Hi].
  - intros; apply plen_bnd.
Qed.

Lemma sums_snd_le pats : forall n i P L H, (Z.to_nat (gap (PArray.length pats) i) <= n)%nat ->
  (φ L <= Ptot pats)%Z -> (φ (snd (sums pats (PArray.length pats) i P L H)) <= Ptot pats)%Z.
Proof.
  induction n as [|n IH]; intros i P L [g] Hn HL; cbn [sums];
    (destruct (bdec (i <? PArray.length pats)) as [Hl|]; [|exact HL]); pose proof (gap_step _ _ Hl) as [Hg1 Hg2].
  - lia.
  - apply IH; [lia|]. pose proof (ltb_true _ _ Hl).
    pose proof (plen_le_Ptot pats i ltac:(unfold m; lia)) as Hp. unfold plen in Hp.
    destruct (L <? PrimString.length pats.[i]); lia.
Qed.

Lemma build_RS0 pats :
  (forall i, ((φ i) < m pats)%Z -> (0 < plen pats i)%Z) -> (Ptot pats < 4194303)%Z ->
  let mm := PArray.length pats in
  let PL := sums pats mm 0 0 0 (Zwf_well_founded 0 (gap mm 0)) in
  let cap := fst PL + 1 in
  let t0 := mkT (PArray.make cap 0) (PArray.make cap 0) (PArray.make cap 0)
                (PArray.make cap 0) (PArray.make cap 0) 1 in
  let act0 := iota mm 0 (PArray.make mm 0) (Zwf_well_founded 0 (gap mm 0)) in
  (φ cap) = (1 + Ptot pats)%Z /\ (φ (snd PL) <= Ptot pats)%Z /\
  RS pats (1 + Ptot pats) 0 (mkB act0 (PArray.make mm 0) mm t0).
Proof.
  intros Hpos HP. cbv zeta.
  pose proof (m_bound pats) as Hm.
  pose proof (zsum_nonneg (plen pats) (iseq (m pats)) (fun j _ => proj1 (plen_bnd pats j))) as HP0.
  fold (Ptot pats) in HP0.
  destruct (sums_spec pats HP _ 0 0 0 (Zwf_well_founded 0 (gap (PArray.length pats) 0)) eq_refl
              ltac:(rewrite phi0; lia) ltac:(rewrite phi0; reflexivity)
              ltac:(intros i' Hi'; rewrite phi0 in Hi'; pose proof (phi_bnd i'); lia)) as [HPs HLs].
  set (PL := sums _ _ _ _ _ _) in *.
  assert (HLle : (φ (snd PL) <= Ptot pats)%Z) by (apply sums_snd_le with (n := Z.to_nat (gap (PArray.length pats) 0)); [lia | rewrite phi0; lia]).
  assert (Hcap : (φ (fst PL + 1)) = (1 + Ptot pats)%Z) by (rewrite phi_add1; [lia | rewrite wB_val; lia]).
  split; [exact Hcap|]. split; [exact HLle|].
  set (cap := fst PL + 1) in *.
  assert (Hmk : forall b : int, PArray.length (PArray.make cap b) = cap) by (intros b; apply amake_len; lia).
  assert (Hmm : PArray.length (PArray.make (PArray.length pats) 0) = PArray.length pats).
  { apply amake_len. exact (proj2 Hm). }
  destruct (iota_spec (PArray.length pats) _ 0 (PArray.make (PArray.length pats) 0)
              (Zwf_well_founded 0 (gap (PArray.length pats) 0)) eq_refl Hmm
              ltac:(rewrite phi0; pose proof (phi_bnd (PArray.length pats)); lia)
              ltac:(intros j Hj; rewrite phi0 in Hj; pose proof (phi_bnd j); lia)) as [Hla Hia].
  set (act0 := iota _ _ _ _) in *.
  set (t0 := mkT _ _ _ _ _ 1).
  exists (fun _ => []). cbn [bt bcur bact bw]. unfold t0. cbn [tn tchr tpar tfc tns tdep].
  split; [constructor; cbn [tn tchr tpar tfc tns tdep] |].
  - rewrite Hmk. exact Hcap.
  - rewrite Hmk. exact Hcap.
  - rewrite Hmk. exact Hcap.
  - rewrite Hmk. exact Hcap.
  - rewrite Hmk. exact Hcap.
  - rewrite phi1. lia.
  - reflexivity.
  - intros v Hv. rewrite phi1 in Hv. lia.
  - intros v Hv. rewrite aget_make. reflexivity.
  - intros u v Hu Hv _. rewrite phi1 in Hu, Hv. apply phi_inj.
    pose proof (phi_bnd u). pose proof (phi_bnd v). lia.
  - intros u v _ _ _. reflexivity.
  - intros v Hv. rewrite phi1 in Hv. lia.
  - intros u Hu v. rewrite aget_make. split; [intros F; exfalso; exact (Reach_0 _ _ F)|].
    rewrite phi1. lia.
  - intros u _. apply aget_make.
  - split; [intros x _; left; reflexivity|].
    split; [intros x _; simpl; lia|].
    split; [rewrite phi1, sumd_0; lia|].
    split; [rewrite Hmm; reflexivity|].
    split; [unfold m; exact (f_equal to_Z Hla)|].
    split; [intros i Hi; rewrite aget_make, phi0, phi1; split; [lia | reflexivity]|].
    split; [rewrite (Ld0 pats Hpos), iseq_len, Z2Nat.id by lia; reflexivity|].
    intros j Hj. rewrite (Ld0 pats Hpos). unfold act0. rewrite Hia by exact Hj.
    symmetry. apply iseq_nth; [exact Hj | rewrite wB_val; lia].
Qed.

Lemma fail_step t cap W F : TrieInv t cap W ->
  (forall y, (0 < φ y < φ (tn t))%Z -> FailOK t W F y) ->
  forall w, (0 < φ w < φ (tn t))%Z ->
  (List.length (W F.[w]) <= S (List.length (W F.[(tpar t).[w]])))%nat.
Proof.
  intros Ht HF w Hw. destruct (ti_par _ _ _ Ht w Hw) as [Hpw Ew].
  destruct (HF w Hw) as (Hf1 & Hf2 & Hf3 & Hf4).
  rewrite Ew in Hf2, Hf3.
  destruct (suffix_snoc_cases _ _ _ Hf2) as [E | (y & Ey & Hy)]; [rewrite E; simpl; lia|].
  rewrite Ey in Hf3 |- *. rewrite length_app in Hf3 |- *. rewrite length_app in Hf3. simpl in Hf3 |- *.
  destruct (int_eq_dec (tpar t).[w] 0) as [E0|E0].
  - rewrite E0, (ti_root _ _ _ Ht) in Hf3. simpl in Hf3. lia.
  - pose proof (pos_of_nz _ E0).
    destruct (HF ((tpar t).[w]) ltac:(lia)) as (_ & _ & _ & Hu4).
    assert (Hn : IsNode t W y).
    { apply (isnode_prefix _ _ _ _ (φ (tchr t).[w]) Ht). exists F.[w]. split; [exact Hf1 | exact Ey]. }
    pose proof (Hu4 y Hy ltac:(lia) Hn). lia.
Qed.

Lemma walk_lt t cap W fl c : TrieInv t cap W ->
  (forall y, (0 < φ y < φ (tn t))%Z -> (φ fl.[y] < φ (tn t))%Z) ->
  forall x H, (φ x < φ (tn t))%Z -> (φ (walk t fl c x H) < φ (tn t))%Z.
Proof.
  intros Ht Hfl.
  assert (G : forall n x H, (Z.to_nat (φ x) <= n)%nat -> (φ x < φ (tn t))%Z -> (φ (walk t fl c x H) < φ (tn t))%Z).
  { induction n as [|n IH]; intros x [g] Hn Hx; cbn [walk];
    destruct (lookup_spec t cap W x c Ht Hx) as [L1 _];
    (destruct (bdec (lookup t x c =? 0)) as [E|E]; [| pose proof (L1 (eqb_false _ _ E)); lia]);
    (destruct (bdec (x =? 0)) as [E0|E0]; [rewrite phi0; pose proof (ti_n _ _ _ Ht); lia|]);
    (destruct (bdec (fl.[x] <? x)) as [Hl|]; [|rewrite phi0; pose proof (ti_n _ _ _ Ht); lia]);
    pose proof (ltb_true _ _ Hl); pose proof (phi_bnd fl.[x]).
    - pose proof (pos_of_nz _ (eqb_false _ _ E0)). lia.
    - apply IH; [lia|]. apply Hfl. pose proof (pos_of_nz _ (eqb_false _ _ E0)). lia. }
  intros x H Hx. exact (G _ x H (le_n _) Hx).
Qed.

Lemma hsum_hF t D F A : forall n a,
  hsum (hF t D F A) a n = (hsum (fun w => S (D F.[(tpar t).[w]]) - D F.[w]) a n * A)%nat.
Proof.
  induction n as [|n IH]; intros a; [reflexivity|].
  rewrite !hsum_S, IH. unfold hF. rewrite Nat.mul_add_distr_r. reflexivity.
Qed.

Lemma f_cnt_hf s sC i iC q qC :
  (cost (f_cnt_cost stepsCM s sC) + cost (extract (f_cnt_cost stepsCM s sC) i iC)
   + cost (extract (extract (f_cnt_cost stepsCM s sC) i iC) q qC) <= 40)%nat.
Proof. unfold f_cnt_cost. cost_simpl. zpart. projc. zpart1. lia. Qed.

Lemma f_fill_hf s sC i iC q qC :
  (cost (f_fill_cost stepsCM s sC) + cost (extract (f_fill_cost stepsCM s sC) i iC)
   + cost (extract (extract (f_fill_cost stepsCM s sC) i iC) q qC) <= 60)%nat.
Proof. unfold f_fill_cost. cost_simpl. zpart. projc. zpart1. lia. Qed.

Lemma zsum_upd (A : int -> list Z) i x l : NoDup l -> In i l ->
  zsum (fun i' => Z.of_nat (List.length (if i' =? i then A i ++ [x] else A i'))) l
  = (zsum (fun i' => Z.of_nat (List.length (A i'))) l + 1)%Z.
Proof.
  induction l as [|y l IH]; intros HN Hi; [destruct Hi|].
  inversion HN as [|? ? Hy HN']; subst. simpl.
  destruct (y =? i) eqn:E.
  - apply eqb_true in E. subst y. rewrite length_app. simpl.
    rewrite (zsum_ext_in _ (fun i' => Z.of_nat (List.length (A i')))); [lia|].
    intros j Hj. destruct (j =? i) eqn:Ej; [apply eqb_true in Ej; subst; contradiction | reflexivity].
  - destruct Hi as [Hi|Hi]; [subst; rewrite eqb_refl in E; discriminate|].
    rewrite IH by assumption. lia.
Qed.

Lemma scan_count pats t cap W cur fp np fl out txt n H :
  TrieInv t cap W ->
  (forall i, (φ i < m pats)%Z -> (φ cur.[i] < φ (tn t))%Z /\ W cur.[i] = pw pats i) ->
  (forall i, (φ i < m pats)%Z -> (0 < plen pats i)%Z) ->
  (m pats < 4194303)%Z ->
  (forall v, (φ v < φ (tn t))%Z -> forall e, Reach np fp.[v] e <-> ((1 <= φ e <= m pats)%Z /\ cur.[e - 1] = v)) ->
  (forall e, (1 <= φ e <= m pats)%Z -> (φ np.[e] < φ e)%Z) ->
  FI pats t cap W cur (φ (tn t)) fl out ->
  (φ n = Z.of_nat (List.length (T txt)))%Z ->
  Longest t W (firstn 0%nat (T txt)) 0 ->
  Z.of_nat (scan nat cntf t fl out fp np txt n 0 0 0%nat H)
  = zsum (fun i => Z.of_nat (List.length (Full pats txt i))) (iseq (m pats)).
Proof.
  intros Ht Hcur Hpos Hm1 HP1 HP2 HFI Hn HL.
  pose proof (m_bound pats) as Hm.
  apply (scan_spec pats t cap W cur Ht Hcur Hpos Hm1 fp np HP1 HP2 fl out HFI txt nat
           (fun k A => Z.of_nat k = zsum (fun i => Z.of_nat (List.length (A i))) (iseq (m pats))) cntf)
    with (z := gap n 0) (j := 0%nat); try reflexivity; try lia.
  - intros s A B HAB HR. rewrite HR. apply zsum_ext_in. intros i Hi. apply iseq_In in Hi; [|rewrite wB_val; lia].
    rewrite HAB by exact Hi. reflexivity.
  - intros s A i p HR Hi _. unfold cntf. rewrite zsum_upd.
    + rewrite <- HR. lia.
    + apply iseq_NoDup. rewrite wB_val. lia.
    + apply iseq_In; [rewrite wB_val; lia | exact Hi].
  - exact HL.
  - unfold zsum. induction (iseq (m pats)) as [|a l IHl]; [reflexivity|].
    cbn [fold_right]. rewrite <- IHl. reflexivity.
Qed.

(* ---- cost proofs, part dev ---- *)
#[local] Arguments Uint63.to_Z : simpl never.
#[local] Arguments gap : simpl never.
#[local] Arguments fst_cost : simpl never.
#[local] Arguments snd_cost : simpl never.

Lemma hsum_hF0 t W F A n a :
  hsum (hF t (fun w => List.length (W w)) F A) a n = (hsum (h0 t W F) a n * A)%nat.
Proof. rewrite hsum_hF. reflexivity. Qed.

Ltac const_summands :=
  repeat match goal with |- context [@cost ?T ?E] =>
    lazymatch E with
    | context [sums_cost] => fail
    | context [iota_cost] => fail
    | context [rounds_cost] => fail
    | context [plist_loop_cost] => fail
    | context [fail_loop_cost] => fail
    | context [scan_cost] => fail
    | context [alloc_loop_cost] => fail
    | _ => let HE := fresh "HE" in
           assert (HE : (@cost T E <= 60)%nat) by (cost_simpl; zpart; projc; zpart1; lia);
           revert HE; generalize (@cost T E); intros ? HE
    end end.

Ltac summand f B tac :=
  match goal with |- context [@cost ?T ?E] =>
    lazymatch E with
    | context [f] =>
      let HE := fresh "HL" in
      assert (HE : (@cost T E <= B)%nat) by (cost_simpl; zpart; projc; zpart1; tac);
      revert HE; generalize (@cost T E); intros ? HE
    end end.

Lemma multimatch_impl_time pats patsC txt txtC A :
  (257 * 60 + 400 <= A)%nat ->
  (forall i, (φ i < m pats)%Z -> (0 < plen pats i)%Z) -> (Ptot pats < 4194303)%Z -> (m pats < 4194303)%Z ->
  (Z.of_nat (List.length (T txt)) <= 4194303)%Z ->
  (cost (extract (multimatch_impl_cost stepsCM pats patsC) txt txtC) <=
     (Z.to_nat (Ptot pats) + Z.to_nat (φ (PrimString.length txt))
      + Z.to_nat (zsum (fun i => Z.of_nat (List.length (Full pats txt i))) (iseq (m pats)))) * (4 * A + 1000) + 2000)%nat.
Proof.
  intros HA Hpos HP Hm1 HT.
  unfold multimatch_impl_cost.
  match goal with |- context [extract (pure ?f) ?a ?b] => change (extract (pure f) a b) with (f a b) end.
  cbv beta.
  repeat (match goal with |- context [pure (extract ?E)] => generalize (extract E); intro end).
  repeat rewrite cost_expr_seq.
  const_summands.
  summand sums_cost (Z.to_nat (gap (PArray.length pats) 0) * 40 + 100)%nat
    ltac:(match goal with |- context [@cost ?T ?X] => lazymatch X with
          | extract (extract (extract (extract (extract (sums_cost stepsCM ?a ?b) ?c ?d) ?e ?f) ?g ?h) ?i ?j) ?k ?l =>
            bound X (sums_time a b c d e f g h i j k l) end end; lia).
  summand iota_cost (Z.to_nat (gap (PArray.length pats) 0) * 40 + 100)%nat
    ltac:(match goal with |- context [@cost ?T ?X] => lazymatch X with
          | extract (extract (extract (iota_cost stepsCM ?a ?b) ?c ?d) ?e ?f) ?g ?h =>
            bound X (iota_time a b c d e f g h) end end; lia).
  pose proof (m_bound pats) as Hm.
  pose proof (zsum_nonneg (plen pats) (iseq (m pats)) (fun j _ => proj1 (plen_bnd pats j))) as HP0.
  fold (Ptot pats) in HP0.
  pose proof (build_RS0 pats Hpos HP) as HB0. cbv zeta in HB0. destruct HB0 as [Hcap [HLle HRS0]].
  summand rounds_cost (Z.to_nat (Ptot pats) * A + Z.to_nat (Ptot pats) * 200 + 100)%nat
    ltac:(match goal with |- context [@cost ?T ?X] => lazymatch X with
          | extract (extract (extract (extract (rounds_cost stepsCM ?a ?b) ?c ?d) ?e ?f) ?g ?h) ?i ?j =>
            bound X (rounds_time a b c d e f g h i j 0 A HA phi0 HRS0) end end;
          rewrite sumd_0, Z.sub_0_r in *; unfold gap in *; rewrite phi0 in *; lia).
  pose proof (build_spec pats Hpos HP) as B. cbv zeta in B. destruct B as [_ [W [Ht [HPf [Hlc Hcur]]]]].
  match type of Ht with TrieInv (bt ?st0) _ _ => set (stv := st0) in * end.
  set (trv := bt stv) in *. set (curv := bcur stv) in *.
  set (capv := fst (sums pats (length pats) 0 0 0 (Zwf_well_founded 0 (gap (length pats) 0))) + 1) in *.
  pose proof (ti_n _ _ _ Ht) as HN.
  assert (Hmk : forall bz : int, PArray.length (PArray.make capv bz) = capv)
    by (intros bz; apply amake_len; lia).
  assert (Hm1' : (φ (PArray.length pats + 1)) = (m pats + 1)%Z) by (apply phi_add1; unfold m in *; rewrite wB_val; lia).
  assert (HPL0 : PLI pats trv (1 + Ptot pats) curv (φ 0) (PArray.make capv 0)
                   (PArray.make (PArray.length pats + 1) 0)).
  { split; [rewrite Hmk; exact Hcap|].
    split; [rewrite amake_len; [exact Hm1' | rewrite Hm1'; lia]|].
    split; [|split].
    - intros vz Hv ez. rewrite aget_make. split; [intros Fz; exfalso; exact (Reach_0 _ _ Fz)|].
      rewrite phi0. lia.
    - intros ez He. rewrite phi0 in He. lia.
    - intros vz _. rewrite aget_make, phi0. lia. }
  pose proof (plist_loop_spec pats trv _ W curv Ht Hcur Hm1 _ 0 _ _
                (Zwf_well_founded 0 (gap (PArray.length pats) 0)) eq_refl ltac:(rewrite phi0; lia) HPL0)
    as (Hlfp & Hlnp & HP1 & HP2 & _).
  set (plv := plist_loop _ _ _ _ _ _) in *.
  summand plist_loop_cost (Z.to_nat (gap (PArray.length pats) 0) * 80 + 100)%nat
    ltac:(match goal with |- context [@cost ?T ?X] => lazymatch X with
          | extract (extract (extract (extract (extract (plist_loop_cost stepsCM ?a ?b) ?c ?d) ?e ?f) ?g ?h) ?i ?j) ?k ?l =>
            bound X (plist_loop_time a b c d e f g h i j k l) end end; lia).
  assert (HFI1 : FI pats trv (1 + Ptot pats) W curv (φ 1) (PArray.make capv 0) (PArray.make capv 0)).
  { split; [rewrite Hmk; exact Hcap|]. split; [rewrite Hmk; exact Hcap|].
    split; [intros xz Hx; rewrite phi1 in Hx; lia|].
    intros xz Hx. rewrite phi1 in Hx.
    assert (xz = 0) by (apply phi_inj; pose proof (phi_bnd xz); rewrite phi0; lia). subst xz.
    unfold OutOK. rewrite aget_make. split; [rewrite phi0; lia|]. split; [intros Fz; exfalso; apply Fz; reflexivity|].
    intros iz _ _ Hl. rewrite (ti_root _ _ _ Ht) in Hl. simpl in Hl. lia. }
  pose proof (fail_loop_spec pats trv _ W curv Ht Hcur Hm1 (fst plv) (snd plv) HP1 _ 1 _ _
                (Zwf_well_founded 0 (gap (tn trv) 1)) eq_refl ltac:(rewrite phi1; lia) HFI1) as HFI.
  set (fo := fail_loop _ _ _ _ _ _ _) in *.
  set (F := fst fo) in *.
  pose proof HFI as (HlF & HlO & HFok & HOok).
  set (D := fun w => List.length (W w)).
  assert (HF0 : List.length (W F.[0]) = 0%nat).
  { unfold F, fo. rewrite fail_loop_frame by (rewrite phi0, phi1; lia). rewrite aget_make, (ti_root _ _ _ Ht). reflexivity. }
  assert (HDF : forall y, (0 < φ y < φ (tn trv))%Z -> (φ F.[y] < φ y)%Z /\ (D F.[y] < D y)%nat).
  { intros y Hy. destruct (HFok y Hy) as (Hf1 & _ & Hf3 & _). split; [|exact Hf3].
    apply (ti_lt _ _ _ _ _ Ht); [exact Hf1 | lia | exact Hf3]. }
  assert (HLk : forall c y, (φ y < φ (tn trv))%Z -> lok (tchr trv) (tns trv) c 257 ((tfc trv).[y])).
  { intros c y Hy. apply (lok_of_inv trv (1 + Ptot pats) W); [exact Ht | apply (pref_chr pats _ _ W Ht HPf) | exact Hy]. }
  assert (HYl : forall c y, (φ y < φ (tn trv))%Z -> lookup trv y c <> 0 -> D (lookup trv y c) = S (D y)).
  { intros c y Hy Hl. destruct (lookup_spec trv _ W y c Ht Hy) as [L1 _]. destruct (L1 Hl) as [_ Ew].
    unfold D. rewrite Ew, length_app. simpl. lia. }
  assert (Hstep : forall w, (0 < φ w < φ (tn trv))%Z -> (D F.[w] <= S (D F.[(tpar trv).[w]]))%nat)
    by exact (fail_step trv _ W F Ht HFok).
  assert (Hpar : forall w, (0 < φ w < φ (tn trv))%Z -> (φ (tpar trv).[w] < φ w)%Z /\ (D F.[w] <= S (D F.[(tpar trv).[w]]))%nat).
  { intros w Hw. split; [exact (proj1 (ti_par _ _ _ Ht w Hw)) | exact (Hstep w Hw)]. }
  assert (HA' : (257 * 60 + 200 <= A)%nat) by lia.
  assert (HD0 : D 0 = 0%nat) by (unfold D; rewrite (ti_root _ _ _ Ht); reflexivity).
  pose proof (fsum pats trv _ W curv F Ht HPf Hcur HF0 Hstep) as Hfs.
  pose proof (Nat.mul_le_mono_r _ _ A Hfs) as HfsA.
  summand fail_loop_cost (Z.to_nat (φ (tn trv) - 1)%Z * (A + 100) + Z.to_nat (Ptot pats) * A + 100)%nat
    ltac:(match goal with |- context [@cost ?T ?X] => lazymatch X with
          | extract (extract (extract (extract (extract (extract (fail_loop_cost stepsCM ?a ?b) ?c ?d) ?e ?f) ?g ?h) ?i ?j) ?k ?l) ?mm ?nn =>
            bound X (fail_loop_time a b c d e f g h i j k l mm nn D 257 A F HD0 HA' HLk HDF HYl Hpar
                       ltac:(match goal with |- (_ <= φ ?y)%Z => replace y with capv by (symmetry; exact (Hmk 0)) end; rewrite Hcap; lia)
                       ltac:(rewrite phi1; lia) eq_refl) end end;
          match goal with Hc : _ |- _ => unfold D in Hc; rewrite hsum_hF0 in Hc; unfold gap in Hc; rewrite phi1 in Hc end; lia).
  assert (HFN : forall y, (0 < φ y < φ (tn trv))%Z -> (φ F.[y] < φ (tn trv))%Z)
    by (intros y Hy; exact (proj1 (HFok y Hy))).
  assert (HW : forall c y, (φ y < φ (tn trv))%Z -> WalkHyp trv F c D 257 y).
  { intros c y Hy. split; [|split].
    - intros y' Hy'. apply HLk. lia.
    - intros y' Hy' _. apply (HDF y'). lia.
    - intros y' Hy'. apply HYl. lia. }
  assert (HWN : forall c y Hy, (φ y < φ (tn trv))%Z -> (φ (walk trv F c y Hy) < φ (tn trv))%Z)
    by (intros c y Hy Hyl; exact (walk_lt trv _ W F c Ht HFN y Hy Hyl)).
  assert (HOut : forall y, (φ y < φ (tn trv))%Z -> OutHyp (snd fo) (fst plv) y).
  { intros y Hy y' Hy' _ Hn0. destruct (HOok y' ltac:(lia)) as (Ho1 & Ho2 & _).
    destruct (Ho2 Hn0) as [HT' _]. apply (term_fp pats trv curv Hm1 (fst plv) (snd plv) HP1 _ Ho1). exact HT'. }
  assert (Hst0 : (φ 0 < φ (tn trv))%Z) by (rewrite phi0; lia).
  assert (Hn : (φ (PrimString.length txt)) = Z.of_nat (List.length (T txt))) by (unfold T; rewrite pstr_len; reflexivity).
  assert (HLg : Longest trv W (firstn 0%nat (T txt)) 0).
  { split; [rewrite phi0; lia|]. split; [rewrite (ti_root _ _ _ Ht); apply suffix_nil|].
    intros z _ Hs. apply suffix_length in Hs. simpl in Hs. lia. }
  set (KK := zsum (fun i => Z.of_nat (List.length (Full pats txt i))) (iseq (m pats))).
  assert (HKK : forall H, scan nat cntf trv F (snd fo) (fst plv) (snd plv) txt (PrimString.length txt) 0 0 0%nat H = Z.to_nat KK).
  { intros H. apply Nat2Z.inj. rewrite Z2Nat.id.
    - exact (scan_count pats trv _ W curv (fst plv) (snd plv) F (snd fo) txt _ H Ht Hcur Hpos Hm1 HP1 HP2 HFI Hn HLg).
    - unfold KK. apply zsum_nonneg. intros; lia. }
  assert (HC1 : (40 + 60 <= 100)%nat) by lia.
  summand scan_cost (Z.to_nat (φ (PrimString.length txt)) * (A + A + 500) + Z.to_nat KK * 300 + 100)%nat
    ltac:(match goal with |- context [@cost ?T ?X] => lazymatch X with
          | extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract
              (scan_cost stepsCM ?Sx ?SxC) ?f ?fC) ?t ?tC) ?fl ?flC) ?out ?outC) ?fp ?fpC) ?np ?npC) ?tx ?txC) ?n ?nC) ?j ?jC) ?st ?stC) ?s ?sC) ?H ?HC =>
            bound X (scan_time Sx SxC f fC t tC fl flC out outC fp fpC np npC tx txC n nC j jC st stC s sC H HC
                       40 100 D 257 A (tn trv) HC1 f_cnt_hf HD0 HA' HW HWN HOut Hst0) end end;
          match goal with Hc : _ |- _ => rewrite HKK, HD0 in Hc; unfold gap in Hc; rewrite phi0, Z.sub_0_r in Hc end; lia).
  summand alloc_loop_cost (Z.to_nat (gap (PArray.length pats) 0) * 80 + 100)%nat
    ltac:(match goal with |- context [@cost ?T ?X] => lazymatch X with
          | extract (extract (extract (extract (alloc_loop_cost stepsCM ?a ?b) ?c ?d) ?e ?f) ?g ?h) ?i ?j =>
            bound X (alloc_loop_time a b c d e f g h i j) end end; lia).
  assert (HC2 : (60 + 60 <= 120)%nat) by lia.
  summand scan_cost (Z.to_nat (φ (PrimString.length txt)) * (A + A + 500) + Z.to_nat KK * 320 + 100)%nat
    ltac:(match goal with |- context [@cost ?T ?X] => lazymatch X with
          | extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract (extract
              (scan_cost stepsCM ?Sx ?SxC) ?f ?fC) ?t ?tC) ?fl ?flC) ?out ?outC) ?fp ?fpC) ?np ?npC) ?tx ?txC) ?n ?nC) ?j ?jC) ?st ?stC) ?s ?sC) ?H ?HC =>
            bound X (scan_time Sx SxC f fC t tC fl flC out outC fp fpC np npC tx txC n nC j jC st stC s sC H HC
                       60 120 D 257 A (tn trv) HC2 f_fill_hf HD0 HA' HW HWN HOut Hst0) end end;
          match goal with Hc : _ |- _ => rewrite HKK, HD0 in Hc; unfold gap in Hc; rewrite phi0, Z.sub_0_r in Hc end; lia).
  assert (HmP : (m pats <= Ptot pats)%Z).
  { unfold Ptot.
    assert (E1 : zsum (fun _ => 1%Z) (iseq (m pats)) = m pats) by (rewrite zsum_one, iseq_len; lia).
    rewrite <- E1 at 1. apply zsum_le. intros iz Hiz.
    apply iseq_In in Hiz; [| rewrite wB_val; lia]. pose proof (Hpos iz Hiz). lia. }
  unfold gap in *. rewrite phi0, Z.sub_0_r in *.
  change (φ (PArray.length pats)) with (m pats) in *.
  fold KK.
  set (Pn := Z.to_nat (Ptot pats)) in *. set (nn := Z.to_nat (φ (PrimString.length txt))) in *.
  set (Kn := Z.to_nat KK) in *. set (Nn := Z.to_nat (φ (tn trv) - 1)) in *.
  assert (HNn : (Nn <= Pn)%nat) by (unfold Nn, Pn; lia).
  assert (Hmn : (Z.to_nat (m pats) <= Pn)%nat) by (unfold Pn; lia).
  pose proof (Nat.mul_le_mono_r _ _ (A + 100) HNn).
  pose proof (Nat.le_0_l (Pn * A)). pose proof (Nat.le_0_l (nn * A)). pose proof (Nat.le_0_l (Kn * A)).
  lia.
Qed.

Lemma fold_sum (f : nat -> nat) l a : List.fold_left (fun acc i => (acc + f i)%nat) l a = (a + list_sum (map f l))%nat.
Proof. revert a. induction l as [|x l IH]; intros a; simpl; [lia|]. rewrite IH. lia. Qed.

Lemma sizes_iseq {B} `{Size B} (t : array B) :
  sizes t = list_sum (map (fun i => size t.[i]) (iseq (φ (PArray.length t)))).
Proof.
  unfold sizes. rewrite fold_sum. unfold iseq. rewrite map_map. reflexivity.
Qed.

Lemma zsum_list_nat (u : int -> nat) l : Z.of_nat (list_sum (map u l)) = zsum (fun i => Z.of_nat (u i)) l.
Proof. induction l as [|x l IH]; [reflexivity|]. simpl. rewrite Nat2Z.inj_add, IH. reflexivity. Qed.

Local Opaque multimatch_impl_cost.
Theorem multimatch_time : exists c1 c2 : nat,
  forall (patterns : list String.string) (text : String.string)
  (patterns_arr : array PrimString.string)
  (text_str : PrimString.string),
  valid_input patterns text -> repr patterns_arr patterns ->
  repr text_str text ->
  (cost2 multimatch_cost patterns_arr text_str <= c1 * (sizes patterns_arr + size text_str + sizes (multimatch patterns_arr text_str) + 1) + c2)%nat.
Proof.
  exists (4 * (257 * 60 + 400) + 1000)%nat, 3000%nat. intros pats txt xp xt Hv Hxp Hxt.
  remember ((4 * (257 * 60 + 400) + 1000) * (sizes xp + size xt + sizes (multimatch xp xt) + 1) + 3000)%nat as RHS eqn:ERHS.
  unfold cost2. rewrite call_cost2_eq. unfold multimatch_cost. unfold multimatch in *.
  change (cost (multimatch_impl_cost stepsCM xp (witness xp))) with 0%nat.
  destruct Hv as [Hvp Hvtot Hvt].
  pose proof Hxp as [Hlp Hcp].
  assert (Hm : m xp = Z.of_nat (List.length pats)) by (unfold m; symmetry; exact Hlp).
  pose proof (m_bound xp) as Hmb.
  assert (Hpw : forall k, (k < List.length pats)%nat ->
            pw xp (of_Z (Z.of_nat k)) = codes (nth k pats String.EmptyString)).
  { intros k Hk. destruct (Hcp k Hk) as [s [Hs Hr]]. rewrite (nth_error_nth _ _ _ Hs).
    unfold pw. apply pstr_codes. exact Hr. }
  assert (Hpw' : forall i, ((φ i) < m xp)%Z ->
            pw xp i = codes (nth (Z.to_nat (φ i)) pats String.EmptyString)).
  { intros i Hi. rewrite <- Hpw by lia. f_equal. apply phi_inj. rewrite phi_of_Z.
    - pose proof (phi_bnd i). lia.
    - pose proof (phi_bnd i). rewrite wB_val. lia. }
  assert (Hplen : forall i, ((φ i) < m xp)%Z ->
            plen xp i = Z.of_nat (String.length (nth (Z.to_nat (φ i)) pats String.EmptyString))).
  { intros i Hi. rewrite <- plen_len, Hpw', codes_len by exact Hi. reflexivity. }
  assert (HT : T xt = codes txt) by (unfold T; apply pstr_codes; exact Hxt).
  assert (Hpos : forall i, ((φ i) < m xp)%Z -> (0 < plen xp i)%Z).
  { intros i Hi. rewrite Hplen by exact Hi. rewrite Forall_forall in Hvp.
    assert (Hin : In (nth (Z.to_nat (φ i)) pats String.EmptyString) pats) by (apply nth_In; lia).
    pose proof (Hvp _ Hin) as H1. unfold slen in H1. lia. }
  assert (HPt : Ptot xp = Z.of_nat (list_sum (map String.length pats))).
  { unfold Ptot.
    rewrite (zsum_ext_in _ (fun i => Z.of_nat (String.length (nth (Z.to_nat (φ i)) pats String.EmptyString)))).
    - rewrite Hm, zsum_iseq_list, firstn_all; [reflexivity | lia | rewrite wB_val; lia].
    - intros i Hi. apply iseq_In in Hi; [| rewrite wB_val; lia]. apply Hplen. exact Hi. }
  unfold total_length in Hvtot.
  assert (HmP : (m xp <= Ptot xp)%Z).
  { unfold Ptot.
    assert (E1 : zsum (fun _ => 1%Z) (iseq (m xp)) = m xp) by (rewrite zsum_one, iseq_len; lia).
    rewrite <- E1 at 1. apply zsum_le. intros i Hi.
    apply iseq_In in Hi; [| rewrite wB_val; lia]. pose proof (Hpos i Hi). lia. }
  assert (HTl : (Z.of_nat (List.length (T xt)) <= 4194303)%Z)
    by (rewrite HT, codes_len; unfold slen in Hvt; lia).
  pose proof (multimatch_impl_time xp (witness xp) xt (witness xt) (257 * 60 + 400) (le_n _) Hpos ltac:(lia) ltac:(lia) HTl) as HM.
  destruct (impl_core xp xt Hpos ltac:(lia) ltac:(lia) HTl) as [HR1 HR2].
  assert (ES1 : sizes xp = Z.to_nat (Ptot xp)).
  { rewrite sizes_iseq. apply Nat2Z.inj. rewrite zsum_list_nat, Z2Nat.id by lia.
    unfold Ptot. apply zsum_ext_in. intros i Hi. unfold size, size_string. rewrite Z2Nat.id; [reflexivity|].
    apply phi_bnd. }
  assert (ES2 : sizes (multimatch_impl xp xt) = Z.to_nat (zsum (fun i => Z.of_nat (List.length (Full xp xt i))) (iseq (m xp)))).
  { rewrite sizes_iseq. apply Nat2Z.inj. rewrite zsum_list_nat, Z2Nat.id
      by (apply zsum_nonneg; intros; lia).
    match goal with |- zsum _ (iseq ?a) = _ => replace a with (m xp) by (symmetry; exact HR1) end.
    apply zsum_ext_in. intros i Hi.
    apply iseq_In in Hi; [|rewrite wB_val; lia].
    unfold size, size_array. destruct (HR2 i Hi) as [Hl _].
    rewrite Z2Nat.id by (apply phi_bnd). exact Hl. }
  assert (ES3 : size xt = Z.to_nat (φ (PrimString.length xt))) by reflexivity.
  subst RHS. rewrite ES1, ES2, ES3.
  match goal with |- context [@cost ?T ?X] => pose proof (HM : (@cost T X <= _)%nat) as HM2 end.
  revert HM2. match goal with |- context [@cost ?T ?X] => generalize (@cost T X) end.
  intros C0 HM2. clear - HM2. lia.
Qed.

