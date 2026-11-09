(* Executable implementation and its required termination dependencies.
   Correctness proofs are in isahasa_proofs.v. *)
(* Implementation of isahasa (isahasa.spec): a chained hash table on the
   class names, then one Floyd-Warshall transitive closure on bit-packed
   rows of a layered graph.

   Code.
   - Names.  Every name of the n given lines goes through [intern]: a hash
     table with chaining, in flat arrays.  [hkeys.[i]] is the name of id i,
     [hnxt.[i]] the next id of its chain (encoded i+1, 0 = end of chain),
     [hhead.[b]] the first id of bucket b (encoded).  A new name gets the
     next id and is pushed at the front of its bucket.  The chains point to
     strictly smaller encoded ids, which is the termination measure of the
     chain walk (checked dynamically, [q <? p]).  The ids of the two names of
     line l are stored in [ia.[l]], [ib.[l]].
   - Closure.  k distinct names give a layered graph on N = 2k vertices:
     vertex a (a < k) is "name a, no has-a step yet", vertex a+k is "name
     a, a has-a step used".  A given line "a is-a b" gives the edges
     a -> b and a+k -> b+k, a line "a has-a b" the edges a -> b+k and
     a+k -> b+k.  One flat table of N rows of W = ceil(N/63) Uint63 words
     each, 63 bits per word, bit v of row u at word u*W + v/63, bit v mod 63.
     TRANSITIVE-CLOSURE (Floyd-Warshall, the intermediate vertex w
     outermost): for every row u whose bit w is set, row u |= row w, a
     whole-word [lor] per word.
   - Queries.  Two hash lookups; "x is-a y" is x = y or bit (x, y), "x
     has-a y" is bit (x, y+k).

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) _] proof (the template's device); no nat, no fuel.  Every
   array is threaded linearly. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Bool.
From Stdlib Require Import Relations String Ascii.
From Stdlib Require PrimString PrimStringAxioms PString.
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

Lemma dec_lt : forall q p : int, (q <? p) = true -> Zwf 0 (φ q) (φ p).
Proof.
  intros q p H. rewrite ltb_spec in H. pose proof (to_Z_bounded q).
  unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program: the hash table                                         *)
(* ------------------------------------------------------------------ *)

Definition pstr := PrimString.string.

Fixpoint hloop (s : pstr) (len i h : int) (H : Acc (Zwf 0) (gap len i))
    {struct H} : int :=
  match bdec (i <? len) with
  | left Hi =>
      hloop s len (i + 1) (h * 31 + PrimString.get s i)
        (Acc_inv H (dec_step len i Hi))
  | right _ => h
  end.

(* the bucket of s, among 1024 *)
Definition hash (s : pstr) : int :=
  let len := PrimString.length s in
  (hloop s len 0 0 (Zwf_well_founded 0 (gap len 0))) land 1023.

(* Walk a chain from encoded id p: the encoded id of s, or 0. *)
Fixpoint walk (s : pstr) (keys : array pstr) (nxt : array int) (p : int)
    (H : Acc (Zwf 0) (φ p)) {struct H} : int :=
  match bdec (p =? 0) with
  | left _ => 0
  | right _ =>
      match PrimString.compare keys.[p - 1] s with
      | Eq => p
      | _ =>
          let q := nxt.[p - 1] in
          match bdec (q <? p) with
          | left Hq => walk s keys nxt q (Acc_inv H (dec_lt q p Hq))
          | right _ => 0
          end
      end
  end.

Record ht := mkht {
  hkeys : array pstr;
  hnxt : array int;
  hhead : array int;
  hcnt : int }.

(* the encoded id of s (id + 1), or 0 when s is not in the table *)
Definition lookup (st : ht) (s : pstr) : int :=
  let p := (hhead st).[hash s] in
  walk s (hkeys st) (hnxt st) p (Zwf_well_founded 0 (φ p)).

(* the table with s in it, and the id of s *)
Definition intern (st : ht) (s : pstr) : ht * int :=
  let b := hash s in
  let hb := (hhead st).[b] in
  let p := walk s (hkeys st) (hnxt st) hb (Zwf_well_founded 0 (φ hb)) in
  if p =? 0 then
    let c := hcnt st in
    (mkht (hkeys st).[c <- s] (hnxt st).[c <- hb] (hhead st).[b <- c + 1] (c + 1), c)
  else (st, p - 1).

(* lines i .. n-1: intern both names, record their ids *)
Fixpoint iloop (xsrc xdst : array pstr) (n i : int) (st : ht) (ia ib : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : ht * array int * array int :=
  match bdec (i <? n) with
  | left Hi =>
      let (st1, a) := intern st xsrc.[i] in
      let (st2, b) := intern st1 xdst.[i] in
      iloop xsrc xdst n (i + 1) st2 ia.[i <- a] ib.[i <- b]
        (Acc_inv H (dec_step n i Hi))
  | right _ => (st, ia, ib)
  end.

(* ------------------------------------------------------------------ *)
(* The program: the packed table and the closure                       *)
(* ------------------------------------------------------------------ *)

(* bit v of row u *)
Definition getbit (T : array int) (W u v : int) : bool :=
  ((T.[u * W + v / 63] >> (v mod 63)) land 1) =? 1.

(* set bit v of row u *)
Definition setbit (T : array int) (W u v : int) : array int :=
  let i := u * W + v / 63 in
  T.[i <- T.[i] lor (1 << (v mod 63))].

(* the edges of lines l .. n-1 *)
Fixpoint eloop (xrs : array relkind) (ia ib : array int) (k W n l : int)
    (T : array int) (H : Acc (Zwf 0) (gap n l)) {struct H} : array int :=
  match bdec (l <? n) with
  | left Hl =>
      let a := ia.[l] in
      let b := ib.[l] in
      let T' := match xrs.[l] with
                | IsA => setbit (setbit T W a b) W (a + k) (b + k)
                | HasA => setbit (setbit T W a (b + k)) W (a + k) (b + k)
                end in
      eloop xrs ia ib k W n (l + 1) T' (Acc_inv H (dec_step n l Hl))
  | right _ => T
  end.

(* words j .. W-1 of row u |= those of row w *)
Fixpoint rowor (T : array int) (W u w j : int) (H : Acc (Zwf 0) (gap W j))
    {struct H} : array int :=
  match bdec (j <? W) with
  | left Hj =>
      rowor T.[u * W + j <- T.[u * W + j] lor T.[w * W + j]] W u w (j + 1)
        (Acc_inv H (dec_step W j Hj))
  | right _ => T
  end.

(* intermediate vertex w, rows u .. N-1 *)
Fixpoint fw_inner (T : array int) (N W w u : int) (H : Acc (Zwf 0) (gap N u))
    {struct H} : array int :=
  match bdec (u <? N) with
  | left Hu =>
      fw_inner (if getbit T W u w
                then rowor T W u w 0 (Zwf_well_founded 0 (gap W 0)) else T)
        N W w (u + 1) (Acc_inv H (dec_step N u Hu))
  | right _ => T
  end.

(* intermediate vertices w .. N-1 *)
Fixpoint fw_outer (T : array int) (N W w : int) (H : Acc (Zwf 0) (gap N w))
    {struct H} : array int :=
  match bdec (w <? N) with
  | left Hw =>
      fw_outer (fw_inner T N W w 0 (Zwf_well_founded 0 (gap N 0))) N W (w + 1)
        (Acc_inv H (dec_step N w Hw))
  | right _ => T
  end.

(* ------------------------------------------------------------------ *)
(* The program: the queries                                            *)
(* ------------------------------------------------------------------ *)

Fixpoint fill (f : int -> bool) (m j : int) (out : array bool)
    (H : Acc (Zwf 0) (gap m j)) {struct H} : array bool :=
  match bdec (j <? m) with
  | left Hj => fill f m (j + 1) out.[j <- f j] (Acc_inv H (dec_step m j Hj))
  | right _ => out
  end.

Definition answer (st : ht) (T : array int) (W k : int) (s1 s2 : pstr)
    (r : relkind) : bool :=
  let a := lookup st s1 in
  let b := lookup st s2 in
  if a =? 0 then false
  else if b =? 0 then false
  else match r with
       | IsA => if a =? b then true else getbit T W (a - 1) (b - 1)
       | HasA => getbit T W (a - 1) (b - 1 + k)
       end.

Definition isahasa_impl (xsrc : array pstr) (xrs : array relkind)
    (xdst : array pstr) (xqsrc : array pstr) (xqrs : array relkind)
    (xqdst : array pstr) : array bool :=
  let n := PArray.length xsrc in
  let cap := n + n in
  let st0 := mkht (PArray.make@{Set} cap (PrimString.make 0 0)) (PArray.make@{Set} cap 0)
                  (PArray.make@{Set} 1024 0) 0 in
  let '(st, ia, ib) := iloop xsrc xdst n 0 st0 (PArray.make@{Set} n 0) (PArray.make@{Set} n 0)
                         (Zwf_well_founded 0 (gap n 0)) in
  let k := hcnt st in
  let N := k + k in
  let W := (N + 62) / 63 in
  let T0 := eloop xrs ia ib k W n 0 (PArray.make@{Set} (N * W) 0)
              (Zwf_well_founded 0 (gap n 0)) in
  let T := fw_outer T0 N W 0 (Zwf_well_founded 0 (gap N 0)) in
  let m := PArray.length xqsrc in
  fill (fun j => answer st T W k xqsrc.[j] xqdst.[j] xqrs.[j]) m 0
    (PArray.make@{Set} m false) (Zwf_well_founded 0 (gap m 0)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition isahasa :
  array PrimString.string -> array relkind -> array PrimString.string ->
  array PrimString.string -> array relkind -> array PrimString.string ->
  array bool := isahasa_impl.
