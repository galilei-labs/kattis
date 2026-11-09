(* Executable implementation and its required termination dependencies.
   Correctness proofs are in fulltank_proofs.v. *)
(* Implementation of fulltank (fulltank.spec). *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import FinFun.
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
  unfold Zwf, gap. pose proof (to_Z_bounded m). lia.
Qed.

Lemma dec_cnt : forall c : int, (0 <? c) = true -> Zwf 0 (φ (c - 1)) (φ c).
Proof.
  intros c H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  unfold Zwf. sia.
Qed.

Lemma dec_lt : forall a b : int, (a <? b) = true -> Zwf 0 (φ a) (φ b).
Proof.
  intros a b H. rewrite ltb_spec in H. unfold Zwf.
  pose proof (to_Z_bounded a). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The Fibonacci heap (CLRS ch. 19), in flat arrays indexed by node    *)
(* ------------------------------------------------------------------ *)

(* The null pointer: above every array index. *)
Definition nil : int := 9223372036854775807.

Record fh : Type := FH {
  hkey : array int;   (* key *)
  hpar : array int;   (* parent, nil for a root *)
  hchd : array int;   (* some child *)
  hlft : array int;   (* left sibling *)
  hrgt : array int;   (* right sibling *)
  hdeg : array int;   (* number of children *)
  hmrk : array int;   (* mark, 0 or 1 *)
  hbuf : array int;   (* CONSOLIDATE's array A, indexed by degree *)
  hmin : int          (* the minimum root, nil when empty *)
}.

Definition s_key h i v := FH (hkey h).[i <- v] (hpar h) (hchd h) (hlft h) (hrgt h) (hdeg h) (hmrk h) (hbuf h) (hmin h).
Definition s_par h i v := FH (hkey h) (hpar h).[i <- v] (hchd h) (hlft h) (hrgt h) (hdeg h) (hmrk h) (hbuf h) (hmin h).
Definition s_chd h i v := FH (hkey h) (hpar h) (hchd h).[i <- v] (hlft h) (hrgt h) (hdeg h) (hmrk h) (hbuf h) (hmin h).
Definition s_lft h i v := FH (hkey h) (hpar h) (hchd h) (hlft h).[i <- v] (hrgt h) (hdeg h) (hmrk h) (hbuf h) (hmin h).
Definition s_rgt h i v := FH (hkey h) (hpar h) (hchd h) (hlft h) (hrgt h).[i <- v] (hdeg h) (hmrk h) (hbuf h) (hmin h).
Definition s_deg h i v := FH (hkey h) (hpar h) (hchd h) (hlft h) (hrgt h) (hdeg h).[i <- v] (hmrk h) (hbuf h) (hmin h).
Definition s_mrk h i v := FH (hkey h) (hpar h) (hchd h) (hlft h) (hrgt h) (hdeg h) (hmrk h).[i <- v] (hbuf h) (hmin h).
Definition s_buf h i v := FH (hkey h) (hpar h) (hchd h) (hlft h) (hrgt h) (hdeg h) (hmrk h) (hbuf h).[i <- v] (hmin h).
Definition s_min h v := FH (hkey h) (hpar h) (hchd h) (hlft h) (hrgt h) (hdeg h) (hmrk h) (hbuf h) v.

(* Splice x into a circular doubly linked list, right after a. *)
Definition ring_ins (h : fh) (a x : int) : fh :=
  let b := (hrgt h).[a] in
  s_lft (s_rgt (s_lft (s_rgt h a x) x a) x b) b x.

(* Add the detached node x to the root list, updating the minimum. *)
Definition root_add (h : fh) (x : int) : fh :=
  let m := hmin h in
  if m =? nil then s_min (s_rgt (s_lft h x x) x x) x
  else
    let h1 := ring_ins h m x in
    if (hkey h1).[x] <? (hkey h1).[m] then s_min h1 x else h1.

(* INSERT *)
Definition fh_insert (h : fh) (x k : int) : fh :=
  root_add (s_mrk (s_deg (s_chd (s_par (s_key h x k) x nil) x nil) x 0) x 0) x.

(* CUT(x, y): x, a child of y, becomes a root. *)
Definition fh_cut (h : fh) (x y : int) : fh :=
  let h1 :=
    if (hdeg h).[y] =? 1 then s_chd h y nil
    else
      let a := (hlft h).[x] in
      let b := (hrgt h).[x] in
      let h' := s_lft (s_rgt h a b) b a in
      if (hchd h').[y] =? x then s_chd h' y b else h' in
  let h2 := s_deg h1 y ((hdeg h1).[y] - 1) in
  root_add (s_mrk (s_par h2 x nil) x 0) x.

(* CASCADING-CUT(y); the counter only bounds the climb. *)
Fixpoint ccut (h : fh) (y cnt : int) (H : Acc (Zwf 0) (φ cnt)) {struct H} : fh :=
  match bdec (0 <? cnt) with
  | left Hc =>
      let z := (hpar h).[y] in
      if z =? nil then h
      else if (hmrk h).[y] =? 0 then s_mrk h y 1
      else ccut (fh_cut h y z) z (cnt - 1) (Acc_inv H (dec_cnt cnt Hc))
  | right _ => h
  end.

(* DECREASE-KEY(x, k) *)
Definition fh_decrease (h : fh) (x k : int) : fh :=
  let h1 := s_key h x k in
  let y := (hpar h1).[x] in
  let h2 :=
    if y =? nil then h1
    else if k <? (hkey h1).[y] then
      let N := PArray.length (hpar h1) in
      ccut (fh_cut h1 x y) y N (Zwf_well_founded 0 (φ N))
    else h1 in
  if k <? (hkey h2).[hmin h2] then s_min h2 x else h2.

(* LINK(y, x): the detached root y becomes a child of x. *)
Definition fh_link (h : fh) (y x : int) : fh :=
  let h1 :=
    if (hdeg h).[x] =? 0 then s_rgt (s_lft (s_chd h x y) y y) y y
    else ring_ins h (hchd h).[x] y in
  s_mrk (s_deg (s_par h1 y x) x ((hdeg h1).[x] + 1)) y 0.

(* CONSOLIDATE's inner loop: the tree x of degree d meets A[d], A[d+1], ... *)
Fixpoint link_loop (h : fh) (x d N : int) (H : Acc (Zwf 0) (gap N d)) {struct H}
    : fh * int :=
  match bdec (d <? N) with
  | left Hd =>
      let y := (hbuf h).[d] in
      if y =? nil then (s_buf h d x, d)
      else
        let h1 := s_buf h d nil in
        if (hkey h1).[y] <? (hkey h1).[x]
        then link_loop (fh_link h1 x y) y (d + 1) N (Acc_inv H (dec_step N d Hd))
        else link_loop (fh_link h1 y x) x (d + 1) N (Acc_inv H (dec_step N d Hd))
  | right _ => (h, d)
  end.

(* One root w of the list being consolidated; md is the largest degree used. *)
Definition proc (h : fh) (w md : int) : fh * int :=
  let h1 := s_par h w nil in
  let N := PArray.length (hbuf h1) in
  let r := link_loop h1 w (hdeg h1).[w] N (Zwf_well_founded 0 (gap N (hdeg h1).[w])) in
  (fst r, if md <? snd r then snd r else md).

(* Every node of the list from cur (included) to stop (excluded). *)
Fixpoint walk (h : fh) (cur stop md cnt : int) (H : Acc (Zwf 0) (φ cnt)) {struct H}
    : fh * int :=
  if cur =? stop then (h, md)
  else
    match bdec (0 <? cnt) with
    | left Hc =>
        let nx := (hrgt h).[cur] in
        let r := proc h cur md in
        walk (fst r) nx stop (snd r) (cnt - 1) (Acc_inv H (dec_cnt cnt Hc))
    | right _ => (h, md)
    end.

(* The new root list, from A[d .. M-1]. *)
Fixpoint rebuild (h : fh) (d M : int) (H : Acc (Zwf 0) (gap M d)) {struct H} : fh :=
  match bdec (d <? M) with
  | left Hd =>
      let x := (hbuf h).[d] in
      let h1 := if x =? nil then h else root_add (s_buf h d nil) x in
      rebuild h1 (d + 1) M (Acc_inv H (dec_step M d Hd))
  | right _ => h
  end.

(* EXTRACT-MIN: the old roots but z, then the children of z, are
   consolidated into A, and the root list is rebuilt from A. *)
Definition fh_extract (h : fh) : fh * int :=
  let z := hmin h in
  let c := (hchd h).[z] in
  let dz := (hdeg h).[z] in
  let N := PArray.length (hbuf h) in
  let h0 := s_min h nil in
  let r1 := walk h0 (hrgt h0).[z] z 0 N (Zwf_well_founded 0 (φ N)) in
  let r2 :=
    if dz =? 0 then r1
    else
      let nx := (hrgt (fst r1)).[c] in
      let r := proc (fst r1) c (snd r1) in
      walk (fst r) nx c (snd r) N (Zwf_well_founded 0 (φ N)) in
  let M := snd r2 + 1 in
  (rebuild (fst r2) 0 M (Zwf_well_founded 0 (gap M 0)), z).

(* ------------------------------------------------------------------ *)
(* The road network: forward star, half-edge 2j+1 is u_j -> v_j and   *)
(* 2j+2 is v_j -> u_j; 0 ends a list.                                  *)
(* ------------------------------------------------------------------ *)

Fixpoint build (U V head nxt : array int) (j m : int) (H : Acc (Zwf 0) (gap m j))
    {struct H} : array int * array int :=
  match bdec (j <? m) with
  | left Hj =>
      let a := U.[j] in
      let b := V.[j] in
      let e1 := 2 * j + 1 in
      let e2 := 2 * j + 2 in
      let nxt1 := nxt.[e1 <- head.[a]] in
      let head1 := head.[a <- e1] in
      let nxt2 := nxt1.[e2 <- head1.[b]] in
      let head2 := head1.[b <- e2] in
      build U V head2 nxt2 (j + 1) m (Acc_inv H (dec_step m j Hj))
  | right _ => (head, nxt)
  end.

(* ------------------------------------------------------------------ *)
(* Dijkstra over the states x * C + f (city x, f units of fuel)       *)
(* ------------------------------------------------------------------ *)

(* st: 0 never reached, 1 in the heap, 2 done. *)
Definition relax (h : fh) (st : array int) (v nk : int) : fh * array int :=
  let s := st.[v] in
  if s =? 0 then (fh_insert h v nk, st.[v <- 1])
  else if s =? 1 then
    (if nk <? (hkey h).[v] then (fh_decrease h v nk, st) else (h, st))
  else (h, st).

(* The roads out of the current city, half-edge e onwards. *)
Fixpoint edges (U V Dl nxt : array int) (C f kz : int) (hs : fh * array int)
    (e : int) (H : Acc (Zwf 0) (φ e)) {struct H} : fh * array int :=
  if e =? 0 then hs
  else
    let j := (e - 1) / 2 in
    let y := if (e - 1) mod 2 =? 0 then V.[j] else U.[j] in
    let l := Dl.[j] in
    let hs1 := if l <=? f then relax (fst hs) (snd hs) (y * C + (f - l)) kz else hs in
    let e' := nxt.[e] in
    match bdec (e' <? e) with
    | left He => edges U V Dl nxt C f kz hs1 e' (Acc_inv H (dec_lt e' e He))
    | right _ => hs1
    end.

(* The transitions out of state z: buy one unit, or drive a road. *)
Definition expand (P U V Dl head nxt : array int) (C cap : int)
    (hs : fh * array int) (z : int) : fh * array int :=
  let x := z / C in
  let f := z mod C in
  let kz := (hkey (fst hs)).[z] in
  let hs1 := if f <? cap then relax (fst hs) (snd hs) (z + 1) (kz + P.[x]) else hs in
  edges U V Dl nxt C f kz hs1 head.[x] (Zwf_well_founded 0 (φ (head.[x]))).

Fixpoint dijk (P U V Dl head nxt : array int) (C cap g : int) (hs : fh * array int)
    (cnt : int) (H : Acc (Zwf 0) (φ cnt)) {struct H} : option int :=
  if hmin (fst hs) =? nil then None
  else
    match bdec (0 <? cnt) with
    | left Hc =>
        let r := fh_extract (fst hs) in
        let z := snd r in
        let st1 := (snd hs).[z <- 2] in
        if z / C =? g then Some (hkey (fst r)).[z]
        else dijk P U V Dl head nxt C cap g
               (expand P U V Dl head nxt C cap (fst r, st1) z) (cnt - 1)
               (Acc_inv H (dec_cnt cnt Hc))
    | right _ => None
    end.

Definition query (n : int) (P U V Dl head nxt : array int) (cap s g : int)
    : option int :=
  let C := cap + 1 in
  let N := n * C in
  let h0 := FH (PArray.make N 0) (PArray.make N nil) (PArray.make N nil)
              (PArray.make N nil) (PArray.make N nil) (PArray.make N 0)
              (PArray.make N 0) (PArray.make N nil) nil in
  let src := s * C in
  dijk P U V Dl head nxt C cap g
    (fh_insert h0 src 0, (PArray.make N 0).[src <- 1]) N (Zwf_well_founded 0 (φ N)).

Fixpoint qloop (n : int) (P U V Dl head nxt Cs Ss Es : array int)
    (out : array (option int)) (i q : int) (H : Acc (Zwf 0) (gap q i)) {struct H}
    : array (option int) :=
  match bdec (i <? q) with
  | left Hi =>
      qloop n P U V Dl head nxt Cs Ss Es
        out.[i <- query n P U V Dl head nxt Cs.[i] Ss.[i] Es.[i]] (i + 1) q
        (Acc_inv H (dec_step q i Hi))
  | right _ => out
  end.

Definition fulltank_impl (n : uint) (p u v d c s e : array uint)
    : array (option uint) :=
  let m := PArray.length u in
  let hn := build u v (PArray.make n 0) (PArray.make (2 * m + 1) 0) 0 m
              (Zwf_well_founded 0 (gap m 0)) in
  let q := PArray.length c in
  qloop n p u v d (fst hn) (snd hn) c s e (PArray.make q None) 0 q
    (Zwf_well_founded 0 (gap q 0)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition fulltank : uint -> array uint -> array uint -> array uint ->
  array uint -> array uint -> array uint -> array uint ->
  array (option uint) := fulltank_impl.
