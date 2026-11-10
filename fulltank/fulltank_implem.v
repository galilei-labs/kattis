(* Implementation of fulltank (fulltank.spec). *)

From Fulltank.spec Require Import Prelude.
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

(* ================================================================== *)
(* Proofs                                                              *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Array and list plumbing                                             *)
(* ------------------------------------------------------------------ *)

Lemma gso : forall (t : array int) (i j : int) (a : int),
  i <> j -> t.[j <- a].[i] = t.[i].
Proof. intros t i j a H. exact (get_set_other int t j i a (fun E => H (eq_sym E))). Qed.

Lemma gss : forall (t : array int) (i : int) (a : int),
  ((φ i) < (φ (PArray.length t)))%Z -> t.[i <- a].[i] = a.
Proof. intros t i a H. apply (get_set_same int t i a). rewrite ltb_spec. exact H. Qed.

Lemma lset : forall (t : array int) (i : int) (a : int),
  PArray.length t.[i <- a] = PArray.length t.
Proof. intros t i a. exact (length_set int t i a). Qed.

Lemma lmake : forall (n : int) (a : int),
  ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n a) = n.
Proof.
  intros n a H.
  transitivity (if n ≤? max_length then n else max_length); [exact (length_make int n a)|].
  replace (n ≤? max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec. change (φ max_length) with 4194303%Z. exact H.
Qed.

Lemma gmake : forall (n i : int) (a : int), (PArray.make n a).[i] = a.
Proof. intros n i a. exact (get_make int a n i). Qed.

Lemma lbound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec in H. exact H.
Qed.

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma nil_val : (φ nil) = 9223372036854775807%Z.
Proof. reflexivity. Qed.

Lemma last_cons : forall (a : int) t d, last (a :: t) d = last t a.
Proof.
  intros a t. revert a. induction t as [| b t IH]; intros a d; [reflexivity|].
  change (last (a :: b :: t) d) with (last (b :: t) d).
  rewrite IH. rewrite IH. reflexivity.
Qed.

Lemma last_indep : forall (l : list int) d d', l <> [] -> last l d = last l d'.
Proof.
  intros l d d' H. destruct l as [| a t]; [congruence|].
  rewrite !last_cons. reflexivity.
Qed.

Lemma last_app_ne : forall (l1 l2 : list int) d, l2 <> [] -> last (l1 ++ l2) d = last l2 d.
Proof.
  induction l1 as [| a t IH]; intros l2 d H; [reflexivity|].
  rewrite <- app_comm_cons. rewrite last_cons, IH by exact H. apply last_indep. exact H.
Qed.


Lemma last_in : forall (l : list int) d, l <> [] -> In (last l d) l.
Proof.
  induction l as [| a t IH]; intros d H; [congruence|].
  rewrite last_cons. destruct t as [| b t]; [left; reflexivity|].
  right. apply IH. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Circular doubly linked lists                                        *)
(* ------------------------------------------------------------------ *)

(* Following R from each element of l gives the next one, the last
   one gives stop. *)
Fixpoint rseq (R : array int) (l : list int) (stop : int) : Prop :=
  match l with
  | [] => True
  | a :: t => R.[a] = hd stop t /\ rseq R t stop
  end.

(* Following L from each element of l gives the previous one, the first
   one gives start. *)
Fixpoint lseq (L : array int) (start : int) (l : list int) : Prop :=
  match l with
  | [] => True
  | a :: t => L.[a] = start /\ lseq L a t
  end.

Definition ring (L R : array int) (l : list int) : Prop :=
  match l with
  | [] => False
  | a :: _ => rseq R l a /\ lseq L (last l a) l
  end.

Lemma rseq_frame : forall R R' l s, rseq R l s ->
  (forall i, In i l -> R'.[i] = R.[i]) -> rseq R' l s.
Proof.
  intros R R' l s. induction l as [| a t IH]; simpl; [tauto|].
  intros [H1 H2] Hf. split.
  - rewrite Hf by (left; reflexivity). exact H1.
  - apply IH; [exact H2|]. intros i Hi. apply Hf. right. exact Hi.
Qed.

Lemma lseq_frame : forall L L' l s, lseq L s l ->
  (forall i, In i l -> L'.[i] = L.[i]) -> lseq L' s l.
Proof.
  intros L L' l. induction l as [| a t IH]; intros s; simpl; [tauto|].
  intros [H1 H2] Hf. split.
  - rewrite Hf by (left; reflexivity). exact H1.
  - apply IH; [exact H2|]. intros i Hi. apply Hf. right. exact Hi.
Qed.

Lemma ring_frame : forall L R L' R' l, ring L R l ->
  (forall i, In i l -> L'.[i] = L.[i] /\ R'.[i] = R.[i]) -> ring L' R' l.
Proof.
  intros L R L' R' [| a t]; simpl; [tauto|].
  intros [H1 H2] Hf. split.
  - apply (rseq_frame R R' (a :: t) a H1). intros i Hi. apply Hf. exact Hi.
  - apply (lseq_frame L L' (a :: t) _ H2). intros i Hi. apply Hf. exact Hi.
Qed.

Lemma hd_app : forall (l1 l2 : list int) s, hd s (l1 ++ l2) = hd (hd s l2) l1.
Proof. intros [| a t] l2 s; reflexivity. Qed.

Lemma rseq_app : forall R l1 l2 s,
  rseq R (l1 ++ l2) s <-> rseq R l1 (hd s l2) /\ rseq R l2 s.
Proof.
  intros R l1 l2 s. induction l1 as [| a t IH]; simpl; [tauto|].
  rewrite IH, hd_app. tauto.
Qed.

Lemma lseq_app : forall L l1 l2 st,
  lseq L st (l1 ++ l2) <-> lseq L st l1 /\ lseq L (last l1 st) l2.
Proof.
  intros L l1. induction l1 as [| a t IH]; intros l2 st; [cbn; tauto|].
  rewrite <- app_comm_cons. cbn [lseq]. rewrite IH, last_cons. tauto.
Qed.

Lemma ring_cons : forall L R a t,
  ring L R (a :: t) <->
  R.[a] = hd a t /\ rseq R t a /\ L.[a] = last t a /\ lseq L a t.
Proof.
  intros L R a t. unfold ring. cbn [rseq lseq]. rewrite last_cons. tauto.
Qed.

Lemma ring_iff : forall L R l, l <> [] ->
  (ring L R l <-> rseq R l (hd nil l) /\ lseq L (last l nil) l).
Proof.
  intros L R [| a t] H; [congruence|]. unfold ring.
  rewrite (last_indep (a :: t) a nil) by discriminate. reflexivity.
Qed.

Lemma ring_single : forall L R x, L.[x] = x -> R.[x] = x -> ring L R [x].
Proof. intros L R x H1 H2. apply ring_cons. cbn. tauto. Qed.

Lemma ring_rot : forall L R l1 l2, l1 <> [] -> l2 <> [] ->
  ring L R (l1 ++ l2) -> ring L R (l2 ++ l1).
Proof.
  intros L R l1 l2 H1 H2.
  assert (N12 : l1 ++ l2 <> []) by (destruct l1; [congruence | discriminate]).
  assert (N21 : l2 ++ l1 <> []) by (destruct l2; [congruence | discriminate]).
  rewrite (ring_iff L R _ N12), (ring_iff L R _ N21).
  rewrite !rseq_app, !lseq_app, !last_app_ne by assumption.
  assert (E1 : hd nil (l1 ++ l2) = hd nil l1) by (destruct l1; [congruence | reflexivity]).
  assert (E2 : hd nil (l2 ++ l1) = hd nil l2) by (destruct l2; [congruence | reflexivity]).
  rewrite E1, E2.
  assert (F1 : hd (hd nil l1) l2 = hd nil l2) by (destruct l2; [congruence | reflexivity]).
  assert (F2 : hd (hd nil l2) l1 = hd nil l1) by (destruct l1; [congruence | reflexivity]).
  rewrite F1, F2.
  rewrite (last_indep l1 (last l2 nil) nil H1), (last_indep l2 (last l1 nil) nil H2).
  tauto.
Qed.

Lemma ring_at : forall L R l x, ring L R l -> In x l ->
  exists t, ring L R (x :: t) /\ Permutation l (x :: t).
Proof.
  intros L R l x Hr Hx. apply in_split in Hx. destruct Hx as (l1 & l2 & E). subst l.
  destruct l1 as [| a t1].
  - exists l2. split; [exact Hr | reflexivity].
  - exists (l2 ++ a :: t1). split.
    + change (x :: l2 ++ a :: t1) with ((x :: l2) ++ (a :: t1)).
      apply ring_rot; [discriminate | discriminate | exact Hr].
    + change (x :: l2 ++ a :: t1) with ((x :: l2) ++ (a :: t1)).
      apply Permutation_app_comm.
Qed.

(* Splicing x right after the head a. *)
Lemma ring_ins_ok : forall (L R : array int) a t x,
  ring L R (a :: t) -> NoDup (a :: t) -> ~ In x (a :: t) ->
  (forall i, In i (x :: a :: t) ->
     ((φ i) < (φ (PArray.length L)))%Z /\ ((φ i) < (φ (PArray.length R)))%Z) ->
  ring (L.[x <- a].[R.[a] <- x]) (R.[a <- x].[x <- R.[a]]) (a :: x :: t).
Proof.
  intros L R a t x Hr Hnd Hx Hb.
  apply ring_cons in Hr. destruct Hr as (Ra & Rt & La & Lt).
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Hat Hnd].
  assert (Hxa : x <> a) by (intro E; apply Hx; left; congruence).
  assert (Hxt : ~ In x t) by (intro E; apply Hx; right; exact E).
  assert (Hb1 : In R.[a] (a :: t)).
  { rewrite Ra. destruct t as [| c t]; [left; reflexivity | right; left; reflexivity]. }
  assert (Hbx : R.[a] <> x) by (intro E; apply Hx; rewrite <- E; exact Hb1).
  destruct (Hb x ltac:(left; reflexivity)) as [BxL BxR].
  destruct (Hb a ltac:(right; left; reflexivity)) as [BaL BaR].
  destruct (Hb R.[a] ltac:(right; exact Hb1)) as [BbL BbR].
  apply ring_cons. split; [|split; [|split]].
  - rewrite gso by exact (not_eq_sym Hxa). rewrite gss by exact BaR. reflexivity.
  - cbn [rseq hd]. split.
    + rewrite gss by (rewrite lset; exact BxR). exact Ra.
    + apply (rseq_frame R); [exact Rt|]. intros i Hi.
      rewrite gso by (intro E; apply Hxt; congruence).
      rewrite gso by (intro E; apply Hat; congruence). reflexivity.
  - destruct t as [| c t].
    + cbn. rewrite Ra. cbn. rewrite gss by (rewrite lset; exact BaL). reflexivity.
    + rewrite last_cons. rewrite (last_indep (c :: t) x a) by discriminate.
      rewrite <- La.
      assert (Hab : a <> R.[a]) by (rewrite Ra; cbn; intro E; apply Hat; left; congruence).
      rewrite gso by exact Hab. rewrite gso by exact (not_eq_sym Hxa). reflexivity.
  - cbn [lseq]. split.
    + rewrite gso by exact (not_eq_sym Hbx). rewrite gss by exact BxL. reflexivity.
    + destruct t as [| c t]; cbn [lseq]; [exact I|].
      cbn [lseq] in Lt. destruct Lt as [Lc Lt'].
      assert (Ebc : R.[a] = c) by (rewrite Ra; reflexivity).
      split.
      * rewrite Ebc. rewrite gss by (rewrite lset; rewrite <- Ebc; exact BbL). reflexivity.
      * apply (lseq_frame L); [exact Lt'|]. intros i Hi.
        apply NoDup_cons_iff in Hnd. destruct Hnd as [Hct _].
        rewrite gso by (rewrite Ebc; intro E; subst; contradiction).
        rewrite gso by (intro E; apply Hxt; right; congruence). reflexivity.
Qed.

(* Unlinking the head x. *)
Lemma ring_del_ok : forall (L R : array int) x t,
  ring L R (x :: t) -> NoDup (x :: t) -> t <> [] ->
  (forall i, In i (x :: t) ->
     ((φ i) < (φ (PArray.length L)))%Z /\ ((φ i) < (φ (PArray.length R)))%Z) ->
  ring (L.[R.[x] <- L.[x]]) (R.[L.[x] <- R.[x]]) t /\ In L.[x] t /\ In R.[x] t.
Proof.
  intros L R x t Hr Hnd Ht Hb.
  apply ring_cons in Hr. destruct Hr as (Rx & Rt & Lx & Lt).
  destruct t as [| c t']; [congruence|].
  assert (Ea : L.[x] = last t' c) by (rewrite Lx; rewrite last_cons; reflexivity).
  cbn [hd] in Rx. rewrite Rx, Ea.
  cbn [rseq lseq] in Rt, Lt. destruct Rt as [Rc Rt']. destruct Lt as [Lc Lt'].
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Hx Hnd'].
  apply NoDup_cons_iff in Hnd'. destruct Hnd' as [Hc Hnd''].
  destruct (Hb c ltac:(right; left; reflexivity)) as [BcL BcR].
  split; [|split].
  - apply ring_cons. destruct t' as [| d t''] using rev_ind.
    + cbn. rewrite !gss by assumption. tauto.
    + clear IHt''. rewrite last_app_ne by discriminate. cbn [last].
      assert (Hd : In d (x :: c :: t'' ++ [d]))
        by (right; right; apply in_or_app; right; left; reflexivity).
      destruct (Hb d Hd) as [BdL BdR].
      assert (Hdc : d <> c) by (intro E; subst; apply Hc; apply in_or_app; right; left; reflexivity).
      split; [|split; [|split]].
      * rewrite gso by exact (not_eq_sym Hdc). rewrite Rc. destruct t''; reflexivity.
      * apply rseq_app in Rt'. destruct Rt' as [R1 R2]. apply rseq_app. split.
        -- apply (rseq_frame R); [exact R1|]. intros i Hi. rewrite gso; [reflexivity|].
           intro E; subst. apply NoDup_remove_2 with (l := t'') (l' := []) in Hnd''.
           rewrite app_nil_r in Hnd''. contradiction.
        -- cbn. split; [|exact I]. rewrite gss by exact BdR. reflexivity.
      * rewrite gss by exact BcL. reflexivity.
      * apply (lseq_frame L); [exact Lt'|]. intros i Hi. rewrite gso; [reflexivity|].
        intro E; subst. contradiction.
  - rewrite <- last_cons with (d := c). apply last_in. discriminate.
  - left. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The heap invariant                                                  *)
(* ------------------------------------------------------------------ *)

Ltac sx := cbn [s_key s_par s_chd s_lft s_rgt s_deg s_mrk s_buf s_min
                hkey hpar hchd hlft hrgt hdeg hmrk hbuf hmin] in *.

Definition kv (h : fh) (v : int) : Z := (φ ((hkey h).[v])).

Definition lens (h : fh) (N : int) : Prop :=
  PArray.length (hkey h) = N /\ PArray.length (hpar h) = N /\
  PArray.length (hchd h) = N /\ PArray.length (hlft h) = N /\
  PArray.length (hrgt h) = N /\ PArray.length (hdeg h) = N /\
  PArray.length (hmrk h) = N /\ PArray.length (hbuf h) = N.

Ltac lens_tac := unfold lens in *; sx; rewrite ?lset; tauto.

Lemma lens_key : forall h N i v, lens h N -> lens (s_key h i v) N. Proof. intros; lens_tac. Qed.
Lemma lens_par : forall h N i v, lens h N -> lens (s_par h i v) N. Proof. intros; lens_tac. Qed.
Lemma lens_chd : forall h N i v, lens h N -> lens (s_chd h i v) N. Proof. intros; lens_tac. Qed.
Lemma lens_lft : forall h N i v, lens h N -> lens (s_lft h i v) N. Proof. intros; lens_tac. Qed.
Lemma lens_rgt : forall h N i v, lens h N -> lens (s_rgt h i v) N. Proof. intros; lens_tac. Qed.
Lemma lens_deg : forall h N i v, lens h N -> lens (s_deg h i v) N. Proof. intros; lens_tac. Qed.
Lemma lens_mrk : forall h N i v, lens h N -> lens (s_mrk h i v) N. Proof. intros; lens_tac. Qed.
Lemma lens_buf : forall h N i v, lens h N -> lens (s_buf h i v) N. Proof. intros; lens_tac. Qed.
Lemma lens_min : forall h N v, lens h N -> lens (s_min h v) N. Proof. intros; lens_tac. Qed.

Lemma lens_N : forall h N, lens h N -> ((φ N) <= 4194303)%Z.
Proof. intros h N (E & _). rewrite <- E. apply lbound. Qed.

(* The children of p: none, or a ring of exactly the nodes whose parent
   is p, of length deg p, through which chd p enters. *)
Definition kids_ok (h : fh) (ns : list int) (p : int) : Prop :=
  ((hdeg h).[p] = 0 /\ forall v, In v ns -> (hpar h).[v] <> p) \/
  (exists l, ring (hlft h) (hrgt h) l /\ NoDup l /\ In (hchd h).[p] l /\
     (φ ((hdeg h).[p])) = Z.of_nat (List.length l) /\
     forall v, In v l <-> In v ns /\ (hpar h).[v] = p).

(* The forest: ns are the nodes; heap order holds except below ex. *)
Record core (h : fh) (N : int) (ns : list int) (ex : int) : Prop := {
  co_len : lens h N;
  co_nodup : NoDup ns;
  co_range : forall v, In v ns -> ((φ v) < (φ N))%Z;
  co_kids : forall p, In p ns -> kids_ok h ns p;
  co_order : forall v, In v ns -> v <> ex -> In (hpar h).[v] ns ->
               (kv h (hpar h).[v] <= kv h v)%Z;
  co_ht : exists ht : int -> nat, forall v, In v ns -> In (hpar h).[v] ns ->
            (ht v < ht (hpar h).[v])%nat
}.

(* The root ring Lr and the minimum (exception em). *)
Definition rr (h : fh) (Lr : list int) (em : int) : Prop :=
  (hmin h = nil /\ Lr = []) \/
  (ring (hlft h) (hrgt h) Lr /\ In (hmin h) Lr /\
   forall v, In v Lr -> v <> em -> (kv h (hmin h) <= kv h v)%Z).

Definition roots_ok (h : fh) (ns : list int) (em : int) : Prop :=
  exists Lr, NoDup Lr /\ (forall v, In v Lr <-> In v ns /\ (hpar h).[v] = nil) /\
             rr h Lr em.

Record HI (h : fh) (N : int) (ns : list int) (eo em : int) : Prop := {
  hi_core : core h N ns eo;
  hi_par : forall v, In v ns -> (hpar h).[v] = nil \/ In (hpar h).[v] ns;
  hi_buf : forall i, ((φ i) < (φ N))%Z -> (hbuf h).[i] = nil;
  hi_roots : roots_ok h ns em
}.

Lemma node_not_nil : forall h N ns ex v, core h N ns ex -> In v ns -> v <> nil.
Proof.
  intros h N ns ex v C Hv E. pose proof (co_range _ _ _ _ C v Hv).
  pose proof (lens_N _ _ (co_len _ _ _ _ C)). subst v. rewrite nil_val in *. lia.
Qed.

Lemma nil_notin : forall h N ns ex, core h N ns ex -> ~ In nil ns.
Proof. intros h N ns ex C H. exact (node_not_nil _ _ _ _ _ C H eq_refl). Qed.

Lemma core_frame : forall h h' N ns ex, core h N ns ex -> lens h' N ->
  (forall v, In v ns -> (hkey h').[v] = (hkey h).[v] /\ (hpar h').[v] = (hpar h).[v] /\
       (hchd h').[v] = (hchd h).[v] /\ (hdeg h').[v] = (hdeg h).[v]) ->
  (forall i, In i ns -> In (hpar h).[i] ns ->
       (hlft h').[i] = (hlft h).[i] /\ (hrgt h').[i] = (hrgt h).[i]) ->
  core h' N ns ex.
Proof.
  intros h h' N ns ex C Hl Ha Hlr. destruct C as [C1 C2 C3 C4 C5 [ht C6]].
  constructor; auto.
  - intros p Hp. destruct (Ha p Hp) as (Kp & Pp & Cp & Dp).
    destruct (C4 p Hp) as [[D1 D2] | (l & Hr & Hnd & Hc & Hd & Hm)].
    + left. split; [rewrite Dp; exact D1|].
      intros v Hv. destruct (Ha v Hv) as (_ & Pv & _). rewrite Pv. apply D2. exact Hv.
    + right. exists l. split; [|split; [exact Hnd|split; [|split]]].
      * apply (ring_frame _ _ _ _ _ Hr). intros i Hi. apply Hm in Hi. destruct Hi as [Hi1 Hi2].
        apply Hlr; [exact Hi1|]. rewrite Hi2. exact Hp.
      * rewrite Cp. exact Hc.
      * rewrite Dp. exact Hd.
      * intros v. rewrite Hm. split; intros [Hv1 Hv2]; split; auto;
          destruct (Ha v Hv1) as (_ & Pv & _); congruence.
  - intros v Hv Hx Hpv. destruct (Ha v Hv) as (Kv & Pv & _).
    rewrite Pv in *. unfold kv. rewrite Kv. destruct (Ha _ Hpv) as (Kq & _). rewrite Kq.
    apply C5; assumption.
  - exists ht. intros v Hv Hpv. destruct (Ha v Hv) as (_ & Pv & _). rewrite Pv in *. auto.
Qed.

Lemma rr_frame : forall h h' Lr em, rr h Lr em -> hmin h' = hmin h ->
  (forall v, In v Lr -> (hkey h').[v] = (hkey h).[v] /\
                        (hlft h').[v] = (hlft h).[v] /\ (hrgt h').[v] = (hrgt h).[v]) ->
  rr h' Lr em.
Proof.
  intros h h' Lr em [[H1 H2] | (Hr & Hm & Hk)] Hmin Ha; [left; rewrite Hmin; tauto|].
  right. split; [|split].
  - apply (ring_frame _ _ _ _ _ Hr). intros i Hi. destruct (Ha i Hi) as (_ & ? & ?). tauto.
  - rewrite Hmin. exact Hm.
  - intros v Hv Hne. unfold kv. rewrite Hmin. destruct (Ha v Hv) as (Kv & _).
    destruct (Ha _ Hm) as (Km & _). rewrite Kv, Km. apply Hk; assumption.
Qed.

Lemma roots_frame : forall h h' ns em, roots_ok h ns em -> hmin h' = hmin h ->
  (forall v, In v ns -> (hkey h').[v] = (hkey h).[v] /\ (hpar h').[v] = (hpar h).[v]) ->
  (forall i, In i ns -> (hpar h).[i] = nil ->
     (hlft h').[i] = (hlft h).[i] /\ (hrgt h').[i] = (hrgt h).[i]) ->
  roots_ok h' ns em.
Proof.
  intros h h' ns em (Lr & Hnd & Hm & Hr) Hmin Ha Hlr. exists Lr. split; [exact Hnd|split].
  - intros v. rewrite Hm. split; intros [Hv1 Hv2]; split; auto;
      destruct (Ha v Hv1) as (_ & Pv); congruence.
  - apply (rr_frame _ _ _ _ Hr Hmin). intros v Hv. apply Hm in Hv. destruct Hv as [Hv1 Hv2].
    destruct (Ha v Hv1). destruct (Hlr v Hv1 Hv2). tauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Adding a root                                                       *)
(* ------------------------------------------------------------------ *)

Lemma root_add_spec : forall h N Lr x,
  lens h N -> NoDup Lr -> (forall v, In v (x :: Lr) -> ((φ v) < (φ N))%Z) -> ~ In x Lr ->
  rr h Lr nil ->
  let h' := root_add h x in
  lens h' N /\
  (exists Lr', Permutation Lr' (x :: Lr) /\ rr h' Lr' nil) /\
  hkey h' = hkey h /\ hpar h' = hpar h /\ hchd h' = hchd h /\ hdeg h' = hdeg h /\
  hmrk h' = hmrk h /\ hbuf h' = hbuf h /\
  (forall i, ~ In i (x :: Lr) -> (hlft h').[i] = (hlft h).[i] /\ (hrgt h').[i] = (hrgt h).[i]).
Proof.
  intros h N Lr x Hl Hnd Hb Hx Hrr h'.
  pose proof (lens_N _ _ Hl) as HN.
  pose proof Hl as (_ & _ & _ & LL & LR & _).
  assert (Bx : ((φ x) < (φ N))%Z) by (apply Hb; left; reflexivity).
  unfold h', root_add.
  destruct (hmin h =? nil) eqn:Em.
  - apply eqb_spec in Em.
    assert (ELr : Lr = []).
    { destruct Hrr as [[_ E] | (_ & Hm & _)]; [exact E|].
      exfalso. pose proof (Hb _ (or_intror Hm)) as B. rewrite Em, nil_val in B. lia. }
    subst Lr. split; [apply lens_min, lens_rgt, lens_lft, Hl|].
    split; [|sx; repeat split; try reflexivity].
    + exists [x]. split; [reflexivity|]. right. sx. split; [|split].
      * apply ring_single.
        -- rewrite gss by (rewrite LL; exact Bx). reflexivity.
        -- rewrite gss by (rewrite LR; exact Bx). reflexivity.
      * left; reflexivity.
      * intros v [E|[]] _. subst v. lia.
    + match goal with H : ~ In _ _ |- _ =>
        rewrite !gso by (intro E; apply H; left; congruence) end; reflexivity.
    + match goal with H : ~ In _ _ |- _ =>
        rewrite !gso by (intro E; apply H; left; congruence) end; reflexivity.
  - apply eqb_false_spec in Em.
    destruct Hrr as [[E _] | (Hr & Hm & Hk)]; [contradiction|].
    destruct (ring_at _ _ _ _ Hr Hm) as (t & Hr' & Hp).
    assert (Hnd' : NoDup (hmin h :: t)) by (apply (Permutation_NoDup Hp); exact Hnd).
    assert (Hx' : ~ In x (hmin h :: t)) by (intro E; apply Hx; apply (Permutation_in _ (Permutation_sym Hp)); exact E).
    assert (Hb' : forall i, In i (x :: hmin h :: t) ->
        ((φ i) < (φ (PArray.length (hlft h))))%Z /\ ((φ i) < (φ (PArray.length (hrgt h))))%Z).
    { intros i Hi. rewrite LL, LR.
      assert (In i (x :: Lr)).
      { destruct Hi as [E|Hi]; [left; exact E|right]. apply (Permutation_in _ (Permutation_sym Hp)). exact Hi. }
      split; apply Hb; assumption. }
    pose proof (ring_ins_ok _ _ _ _ _ Hr' Hnd' Hx' Hb') as Hri.
    assert (Hb1 : In (hrgt h).[hmin h] Lr).
    { apply ring_cons in Hr'. destruct Hr' as (Ra & _).
      apply (Permutation_in _ (Permutation_sym Hp)). rewrite Ra.
      destruct t; [left; reflexivity | right; left; reflexivity]. }
    assert (Hfr : forall i, ~ In i (x :: Lr) ->
      ((hlft h).[x <- hmin h].[(hrgt h).[hmin h] <- x]).[i] = (hlft h).[i] /\
      ((hrgt h).[hmin h <- x].[x <- (hrgt h).[hmin h]]).[i] = (hrgt h).[i]).
    { intros i Hi. split; rewrite !gso; try reflexivity; intro E; apply Hi; subst i;
        first [left; reflexivity | right; exact Hb1 | right; exact Hm]. }
    assert (Hperm : Permutation (hmin h :: x :: t) (x :: Lr)).
    { rewrite Hp. apply perm_swap. }
    unfold ring_ins.
    destruct (_ <? _) eqn:Ek; sx.
    + split; [apply lens_min, lens_lft, lens_rgt, lens_lft, lens_rgt, Hl|].
      split; [|repeat split; try reflexivity; apply Hfr; assumption].
      exists (hmin h :: x :: t). split; [exact Hperm|]. right. sx. split; [exact Hri|split].
      * right; left; reflexivity.
      * intros v Hv _. unfold kv. sx. rewrite ltb_spec in Ek.
        destruct Hv as [E|[E|Hv]]; [subst v; lia | subst v; lia|].
        assert (Hv' : In v Lr) by (apply (Permutation_in _ (Permutation_sym Hp)); right; exact Hv).
        assert (Hvn : v <> nil).
        { intro E. pose proof (Hb v (or_intror Hv')) as B. subst v. rewrite nil_val in B. lia. }
        specialize (Hk v Hv' Hvn). unfold kv in Hk. lia.
    + split; [apply lens_lft, lens_rgt, lens_lft, lens_rgt, Hl|].
      split; [|repeat split; try reflexivity; apply Hfr; assumption].
      exists (hmin h :: x :: t). split; [exact Hperm|]. right. sx. split; [exact Hri|split].
      * left; reflexivity.
      * intros v Hv _. unfold kv. sx. rewrite <- Bool.not_true_iff_false, ltb_spec in Ek.
        destruct Hv as [E|[E|Hv]]; [subst v; lia | subst v; lia|].
        assert (Hv' : In v Lr) by (apply (Permutation_in _ (Permutation_sym Hp)); right; exact Hv).
        assert (Hvn : v <> nil).
        { intro E. pose proof (Hb v (or_intror Hv')) as B. subst v. rewrite nil_val in B. lia. }
        specialize (Hk v Hv' Hvn). unfold kv in Hk. lia.
Qed.

Lemma lt_N_not_nil : forall N v, ((φ N) <= 4194303)%Z -> ((φ v) < (φ N))%Z -> v <> nil.
Proof. intros N v H1 H2 E. subst v. rewrite nil_val in H2. lia. Qed.

Lemma core_add : forall h N ns ex x, core h N ns ex -> ~ In x ns -> ((φ x) < (φ N))%Z ->
  (hpar h).[x] = nil -> (hdeg h).[x] = 0 -> (forall v, In v ns -> (hpar h).[v] <> x) ->
  core h N (x :: ns) ex.
Proof.
  intros h N ns ex x C Hx Bx Px Dx Hv.
  pose proof (lens_N _ _ (co_len _ _ _ _ C)) as HN.
  assert (Xn : x <> nil) by (apply (lt_N_not_nil N); assumption).
  destruct C as [C1 C2 C3 C4 C5 [ht C6]]. constructor; auto.
  - constructor; assumption.
  - intros v [E|Hv']; [subst; exact Bx | auto].
  - intros p [E|Hp].
    + subst p. left. split; [exact Dx|]. intros v [E|Hv']; [subst v; rewrite Px; congruence | auto].
    + assert (Pn : p <> nil) by (apply (lt_N_not_nil N); auto).
      destruct (C4 p Hp) as [[D1 D2] | (l & Hr & Hnd & Hc & Hd & Hm)].
      * left. split; [exact D1|]. intros v [E|Hv']; [subst v; rewrite Px; congruence | auto].
      * right. exists l. repeat (split; [assumption|]). intros v. rewrite Hm. split.
        -- intros [H1 H2]. split; [right|]; assumption.
        -- intros [[E|H1] H2]; [subst v; congruence | split; assumption].
  - intros v [E|Hv'] Hne Hp.
    + subst v. rewrite Px in Hp. destruct Hp as [E|Hp]; [congruence|].
      exfalso. apply (lt_N_not_nil N nil HN (C3 _ Hp)). reflexivity.
    + destruct Hp as [E|Hp]; [exfalso; apply (Hv v Hv'); auto|]. auto.
  - exists ht. intros v [E|Hv'] Hp.
    + subst v. rewrite Px in Hp. destruct Hp as [E|Hp]; [congruence|].
      exfalso. apply (lt_N_not_nil N nil HN (C3 _ Hp)). reflexivity.
    + destruct Hp as [E|Hp]; [exfalso; apply (Hv v Hv'); auto|]. auto.
Qed.

Lemma roots_bound : forall h N ns ex em, core h N ns ex -> roots_ok h ns em ->
  exists Lr, NoDup Lr /\ (forall v, In v Lr <-> In v ns /\ (hpar h).[v] = nil) /\ rr h Lr em /\
    (forall v, In v Lr -> ((φ v) < (φ N))%Z).
Proof.
  intros h N ns ex em C (Lr & H1 & H2 & H3). exists Lr. repeat (split; [assumption|]).
  intros v Hv. apply H2 in Hv. apply (co_range _ _ _ _ C). tauto.
Qed.

(* INSERT *)
Lemma insert_spec : forall h N ns x k, HI h N ns nil nil -> ~ In x ns -> ((φ x) < (φ N))%Z ->
  HI (fh_insert h x k) N (x :: ns) nil nil /\ hkey (fh_insert h x k) = (hkey h).[x <- k].
Proof.
  intros h N ns x k [C Hp Hbuf Hro] Hx Bx.
  pose proof (co_len _ _ _ _ C) as Hl. pose proof (lens_N _ _ Hl) as HN.
  pose proof Hl as (LK & LP & LC & LL & LR & LD & LM & LB).
  assert (Xn : x <> nil) by (apply (lt_N_not_nil N); assumption).
  assert (Hne : forall v, In v ns -> v <> x) by (intros v Hv E; subst; contradiction).
  unfold fh_insert.
  set (h1 := s_mrk (s_deg (s_chd (s_par (s_key h x k) x nil) x nil) x 0) x 0).
  assert (L1 : lens h1 N) by (apply lens_mrk, lens_deg, lens_chd, lens_par, lens_key, Hl).
  assert (C1 : core h1 N ns nil).
  { apply (core_frame h); [exact C | exact L1 | |].
    - intros v Hv. unfold h1; sx. rewrite !gso by (apply Hne; exact Hv). tauto.
    - intros i _ _. unfold h1; sx. tauto. }
  assert (C1' : core h1 N (x :: ns) nil).
  { apply core_add; try assumption.
    - unfold h1; sx. rewrite gss by (rewrite LP; exact Bx). reflexivity.
    - unfold h1; sx. rewrite gss by (rewrite LD; exact Bx). reflexivity.
    - intros v Hv. unfold h1; sx. rewrite gso by (apply Hne; exact Hv).
      destruct (Hp v Hv) as [E|E]; [congruence|]. intro E'. rewrite E' in E. contradiction. }
  assert (R1 : roots_ok h1 ns nil).
  { apply (roots_frame h); [exact Hro | reflexivity | |].
    - intros v Hv. unfold h1; sx. rewrite !gso by (apply Hne; exact Hv). tauto.
    - intros i _ _. unfold h1; sx. tauto. }
  destruct (roots_bound _ _ _ _ _ C1 R1) as (Lr & Hnd & Hm & Hrr & Hb).
  assert (HxL : ~ In x Lr) by (intro E; apply Hm in E; tauto).
  destruct (root_add_spec h1 N Lr x L1 Hnd ltac:(intros v [E|Hv]; [subst; exact Bx | auto]) HxL Hrr)
    as (L2 & (Lr' & Hperm & Hrr') & K2 & P2 & Ch2 & D2 & M2 & B2 & F2).
  split; [|rewrite K2; reflexivity].
  constructor.
  - apply (core_frame h1); [exact C1' | exact L2 | |].
    + intros v _. rewrite K2, P2, Ch2, D2. tauto.
    + intros i Hi Hpi. apply F2. intros [E|E].
      * subst i. unfold h1 in Hpi; sx. rewrite gss in Hpi by (rewrite LP; exact Bx).
        apply (nil_notin _ _ _ _ C1' Hpi).
      * apply Hm in E. destruct E as [_ E]. rewrite E in Hpi. apply (nil_notin _ _ _ _ C1' Hpi).
  - intros v [E|Hv]; rewrite P2; unfold h1; sx.
    + subst v. rewrite gss by (rewrite LP; exact Bx). left; reflexivity.
    + rewrite gso by (apply Hne; exact Hv). destruct (Hp v Hv); [left; assumption | right; right; assumption].
  - intros i Hi. rewrite B2. unfold h1; sx. apply Hbuf. exact Hi.
  - exists Lr'. split; [|split].
    + apply (Permutation_NoDup (Permutation_sym Hperm)). constructor; assumption.
    + intros v. split.
      * intros Hv. apply (Permutation_in _ Hperm) in Hv. rewrite P2. destruct Hv as [E|Hv].
        -- subst v. split; [left; reflexivity|]. unfold h1; sx. apply gss. rewrite LP. exact Bx.
        -- apply Hm in Hv. destruct Hv as [Hv1 Hv2]. split; [right; exact Hv1 | exact Hv2].
      * rewrite P2. intros [[E|Hv1] Hv2]; apply (Permutation_in _ (Permutation_sym Hperm)).
        -- left; exact E.
        -- right. apply Hm. split; assumption.
    + exact Hrr'.
Qed.

Lemma list_max_in : forall (l : list nat) a, In a l -> (a <= list_max l)%nat.
Proof.
  intros l a H. pose proof (proj1 (list_max_le l (list_max l)) (le_n _)) as F.
  rewrite Forall_forall in F. apply F. exact H.
Qed.

Lemma below_root : forall h N ns, core h N ns nil ->
  (forall v, In v ns -> (hpar h).[v] = nil \/ In (hpar h).[v] ns) ->
  forall v, In v ns -> exists r, In r ns /\ (hpar h).[r] = nil /\ (kv h r <= kv h v)%Z.
Proof.
  intros h N ns C Hp.
  pose proof C as [_ _ _ _ Co [ht Ht]].
  set (M := list_max (map ht ns)).
  assert (HM : forall v, In v ns -> (ht v <= M)%nat).
  { intros v Hv. apply list_max_in. apply in_map. exact Hv. }
  assert (K : forall n v, In v ns -> (M - ht v <= n)%nat ->
            exists r, In r ns /\ (hpar h).[r] = nil /\ (kv h r <= kv h v)%Z).
  { induction n as [| n IH]; intros v Hv Hn;
      (destruct (Hp v Hv) as [P|P]; [exists v; split; [exact Hv|split; [exact P | lia]]|]).
    - exfalso. pose proof (Ht v Hv P). pose proof (HM _ P). lia.
    - pose proof (Ht v Hv P). pose proof (HM _ P).
      destruct (IH _ P ltac:(lia)) as (r & Hr1 & Hr2 & Hr3).
      exists r. split; [exact Hr1|split; [exact Hr2|]].
      pose proof (Co v Hv (node_not_nil _ _ _ _ _ C Hv) P). lia. }
  intros v Hv. apply (K (M - ht v)%nat v Hv). lia.
Qed.

Lemma HI_min : forall h N ns, HI h N ns nil nil -> forall v, In v ns ->
  In (hmin h) ns /\ (hpar h).[hmin h] = nil /\ (kv h (hmin h) <= kv h v)%Z.
Proof.
  intros h N ns [C Hp _ Hro] v Hv.
  destruct (below_root _ _ _ C Hp v Hv) as (r & Hr & Pr & Kr).
  destruct (roots_bound _ _ _ _ _ C Hro) as (Lr & _ & Hm & Hrr & Hb).
  assert (HrL : In r Lr) by (apply Hm; tauto).
  destruct Hrr as [[_ E] | (_ & Hmin & Hk)]; [subst Lr; contradiction|].
  apply Hm in Hmin. destruct Hmin as [Hm1 Hm2]. split; [exact Hm1|split; [exact Hm2|]].
  pose proof (Hk r HrL (node_not_nil _ _ _ _ _ C Hr)). lia.
Qed.

Lemma HI_empty : forall h N ns, HI h N ns nil nil -> (hmin h = nil <-> ns = []).
Proof.
  intros h N ns HI0. split.
  - intros E. destruct ns as [| v ns]; [reflexivity|].
    destruct (HI_min _ _ _ HI0 v (or_introl eq_refl)) as (Hm & _).
    exfalso. rewrite E in Hm. exact (nil_notin _ _ _ _ (hi_core _ _ _ _ _ HI0) Hm).
  - intros E. subst ns. destruct HI0 as [C _ _ (Lr & _ & Hm & Hrr)].
    destruct Hrr as [[E _] | (_ & Hmin & _)]; [exact E|].
    apply Hm in Hmin. destruct Hmin as [[] _].
Qed.

(* ------------------------------------------------------------------ *)
(* CUT                                                                 *)
(* ------------------------------------------------------------------ *)

Lemma cut_finish : forall h h3 N ns x,
  HI h N ns x nil -> In x ns -> In (hpar h).[x] ns ->
  lens h3 N -> hkey h3 = hkey h -> hpar h3 = (hpar h).[x <- nil] ->
  hbuf h3 = hbuf h -> hmin h3 = hmin h ->
  (forall p, p <> (hpar h).[x] -> (hchd h3).[p] = (hchd h).[p] /\ (hdeg h3).[p] = (hdeg h).[p]) ->
  (forall i, (hpar h).[i] <> (hpar h).[x] ->
     (hlft h3).[i] = (hlft h).[i] /\ (hrgt h3).[i] = (hrgt h).[i]) ->
  kids_ok h3 ns (hpar h).[x] ->
  HI (root_add h3 x) N ns nil nil /\ hkey (root_add h3 x) = hkey h /\
  hpar (root_add h3 x) = (hpar h).[x <- nil].
Proof.
  intros h h3 N ns x [C Hp Hbuf Hro] Hx Hy L3 K3 P3 B3 M3 CD3 LR3 Ky.
  set (y := (hpar h).[x]) in *.
  pose proof (co_len _ _ _ _ C) as Hl. pose proof (lens_N _ _ Hl) as HN.
  pose proof Hl as (LK & LP & LC & LL & LR & LD & LM & LB).
  pose proof (co_range _ _ _ _ C x Hx) as Bx.
  assert (Yn : y <> nil) by (apply (node_not_nil _ _ _ _ _ C Hy)).
  assert (P3x : (hpar h3).[x] = nil) by (rewrite P3; apply gss; rewrite LP; exact Bx).
  assert (P3v : forall v, v <> x -> (hpar h3).[v] = (hpar h).[v]) by (intros v Hv; rewrite P3; apply gso; exact Hv).
  assert (NN : forall v, In v ns -> v <> nil) by (intros v Hv; exact (node_not_nil _ _ _ _ _ C Hv)).
  assert (C3 : core h3 N ns nil).
  { pose proof C as [C1 C2 Cr C4 C5 [ht C6]]. constructor; auto.
    - intros p Hp'. destruct (Uint63.eq_dec p y) as [E|E]; [subst p; exact Ky|].
      destruct (CD3 p E) as [Cp Dp].
      destruct (C4 p Hp') as [[D1 D2] | (l & Hr & Hnd & Hc & Hd & Hm)].
      + left. split; [rewrite Dp; exact D1|]. intros v Hv.
        destruct (Uint63.eq_dec v x) as [Ev|Ev].
        * subst v. rewrite P3x. intro E'. apply (NN p Hp'). congruence.
        * rewrite P3v by exact Ev. apply D2. exact Hv.
      + right. exists l. split; [|split; [exact Hnd|split; [|split]]].
        * apply (ring_frame _ _ _ _ _ Hr). intros i Hi. apply Hm in Hi. apply LR3.
          destruct Hi as [_ Hi]. rewrite Hi. exact E.
        * rewrite Cp. exact Hc.
        * rewrite Dp. exact Hd.
        * intros v. rewrite Hm. destruct (Uint63.eq_dec v x) as [Ev|Ev].
          -- subst v. rewrite P3x. split; intros [H1 H2]; [|split; [exact H1|]].
             ++ exfalso. apply E. rewrite <- H2. reflexivity.
             ++ exfalso. apply (NN p Hp'). congruence.
          -- rewrite P3v by exact Ev. tauto.
    - intros v Hv _ Hpv. destruct (Uint63.eq_dec v x) as [Ev|Ev].
      + subst v. rewrite P3x in Hpv. exfalso. exact (NN _ Hpv eq_refl).
      + rewrite P3v in * by exact Ev. unfold kv. rewrite K3. apply C5; assumption.
    - exists ht. intros v Hv Hpv. destruct (Uint63.eq_dec v x) as [Ev|Ev].
      + subst v. rewrite P3x in Hpv. exfalso. exact (NN _ Hpv eq_refl).
      + rewrite P3v in * by exact Ev. auto. }
  destruct (roots_bound _ _ _ _ _ C Hro) as (Lr & Hnd & Hm & Hrr & Hb).
  assert (HxL : ~ In x Lr) by (intro E; apply Hm in E; destruct E as [_ E]; contradiction).
  assert (Hrr3 : rr h3 Lr nil).
  { apply (rr_frame h); [exact Hrr | exact M3 |]. intros v Hv. rewrite K3. split; [reflexivity|].
    apply LR3. apply Hm in Hv. destruct Hv as [_ Hv]. rewrite Hv. intro E. apply Yn. rewrite <- E. reflexivity. }
  destruct (root_add_spec h3 N Lr x L3 Hnd ltac:(intros v [E|Hv]; [subst; exact Bx | auto]) HxL Hrr3)
    as (L2 & (Lr' & Hperm & Hrr') & K2 & P2 & Ch2 & D2 & M2 & B2 & F2).
  split; [|split; [rewrite K2; exact K3 | rewrite P2; exact P3]].
  constructor.
  - apply (core_frame h3); [exact C3 | exact L2 | |].
    + intros v _. rewrite K2, P2, Ch2, D2. tauto.
    + intros i Hi Hpi. apply F2. intros [E|E].
      * subst i. rewrite P3x in Hpi. exact (NN _ Hpi eq_refl).
      * apply Hm in E. destruct E as [_ E]. rewrite P3v in Hpi by (intro E'; subst; contradiction).
        rewrite E in Hpi. exact (NN _ Hpi eq_refl).
  - intros v Hv. rewrite P2. destruct (Uint63.eq_dec v x) as [Ev|Ev].
    + subst v. left. exact P3x.
    + rewrite P3v by exact Ev. apply Hp. exact Hv.
  - intros i Hi. rewrite B2, B3. apply Hbuf. exact Hi.
  - exists Lr'. split; [|split].
    + apply (Permutation_NoDup (Permutation_sym Hperm)). constructor; assumption.
    + intros v. rewrite P2. split.
      * intros Hv. apply (Permutation_in _ Hperm) in Hv. destruct Hv as [E|Hv].
        -- subst v. split; [exact Hx | exact P3x].
        -- apply Hm in Hv. destruct Hv as [Hv1 Hv2]. split; [exact Hv1|].
           rewrite P3v; [exact Hv2|]. intro E; subst; contradiction.
      * intros [Hv1 Hv2]; apply (Permutation_in _ (Permutation_sym Hperm)).
        destruct (Uint63.eq_dec v x) as [Ev|Ev]; [left; congruence|].
        right. apply Hm. rewrite P3v in Hv2 by exact Ev. split; assumption.
    + exact Hrr'.
Qed.

Lemma cut_spec : forall h N ns x, HI h N ns x nil -> In x ns -> In (hpar h).[x] ns ->
  HI (fh_cut h x (hpar h).[x]) N ns nil nil /\ hkey (fh_cut h x (hpar h).[x]) = hkey h /\
  hpar (fh_cut h x (hpar h).[x]) = (hpar h).[x <- nil].
Proof.
  intros h N ns x HI0 Hx Hy.
  pose proof HI0 as [C Hp Hbuf Hro].
  pose proof (co_len _ _ _ _ C) as Hl. pose proof (lens_N _ _ Hl) as HN.
  pose proof Hl as (LK & LP & LC & LL & LR & LD & LM & LB).
  pose proof (co_range _ _ _ _ C x Hx) as Bx.
  pose proof (co_range _ _ _ _ C _ Hy) as By.
  assert (NN : forall v, In v ns -> v <> nil) by (intros v Hv; exact (node_not_nil _ _ _ _ _ C Hv)).
  destruct (co_kids _ _ _ _ C _ Hy) as [[D1 D2] | (l & Hr & Hnd & Hc & Hd & Hm)].
  { exfalso. apply (D2 x Hx). reflexivity. }
  assert (Hxl : In x l) by (apply Hm; split; [exact Hx | reflexivity]).
  set (y := (hpar h).[x]) in *.
  unfold fh_cut.
  destruct ((hdeg h).[y] =? 1) eqn:E1.
  - apply eqb_spec in E1.
    assert (El : l = [x]).
    { rewrite E1 in Hd. change (φ 1) with 1%Z in Hd.
      destruct l as [| a [| b l]]; cbn [List.length] in Hd; try lia.
      destruct Hxl as [E|[]]. subst. reflexivity. }
    cbv beta iota zeta. sx.
    apply cut_finish; sx; try assumption; try reflexivity.
    + apply lens_mrk, lens_par, lens_deg, lens_chd, Hl.
    + intros p Hpy. rewrite !gso by exact Hpy. tauto.
    + intros i _. tauto.
    + unfold kids_ok; sx; change (hpar h).[x] with y. left. split.
      * rewrite gss by (rewrite LD; exact By). rewrite E1. reflexivity.
      * intros v Hv. destruct (Uint63.eq_dec v x) as [Ev|Ev].
        -- subst v. rewrite gss by (rewrite LP; exact Bx). intro E. apply (NN y Hy). congruence.
        -- rewrite gso by exact Ev. intro E. assert (Hvl : In v l) by (apply Hm; tauto).
           rewrite El in Hvl. destruct Hvl as [E'|[]]. congruence.
  - apply eqb_false_spec in E1.
    destruct (ring_at _ _ _ _ Hr Hxl) as (t & Hr' & Hperm).
    assert (Hnd' : NoDup (x :: t)) by (apply (Permutation_NoDup Hperm); exact Hnd).
    pose proof (Permutation_length Hperm) as Hlen. cbn [List.length] in Hlen.
    assert (Ht : t <> []).
    { intro E. subst t. apply E1. apply to_Z_inj. rewrite Hd, Hlen. reflexivity. }
    assert (Hb' : forall i, In i (x :: t) ->
        ((φ i) < (φ (PArray.length (hlft h))))%Z /\ ((φ i) < (φ (PArray.length (hrgt h))))%Z).
    { intros i Hi. rewrite LL, LR. apply (Permutation_in _ (Permutation_sym Hperm)) in Hi.
      apply Hm in Hi. destruct Hi as [Hi _]. pose proof (co_range _ _ _ _ C i Hi). lia. }
    destruct (ring_del_ok _ _ _ _ Hr' Hnd' Ht Hb') as (Hrt & Hat & Hbt).
    apply NoDup_cons_iff in Hnd'. destruct Hnd' as [Hxt Hndt].
    assert (Htl : forall i, In i t -> In i l /\ i <> x).
    { intros i Hi. split; [apply (Permutation_in _ (Permutation_sym Hperm)); right; exact Hi|].
      intro E; subst; contradiction. }
    assert (Pt : forall i, In i t -> (hpar h).[i] = y).
    { intros i Hi. apply Htl in Hi. apply Hm. tauto. }
    set (a := (hlft h).[x]) in *. set (b := (hrgt h).[x]) in *.
    assert (Hdeg1 : (1 <= (φ ((hdeg h).[y])))%Z) by lia.
    cbv beta iota zeta. sx.
    destruct ((hchd h).[y] =? x) eqn:E2; sx.
    + apply eqb_spec in E2.
      apply cut_finish; sx; try assumption; try reflexivity.
      * apply lens_mrk, lens_par, lens_deg, lens_chd, lens_lft, lens_rgt, Hl.
      * intros p Hpy. rewrite !gso by exact Hpy. tauto.
      * intros i Hi. rewrite !gso; [tauto | |]; intro E; subst i; apply Hi; apply Pt; assumption.
      * unfold kids_ok; sx; change (hpar h).[x] with y. right. exists t. split; [exact Hrt|split; [exact Hndt|split; [|split]]].
        -- rewrite gss by (rewrite LC; exact By). exact Hbt.
        -- rewrite gss by (rewrite LD; exact By).
           assert ((φ ((hdeg h).[y] - 1)) = (φ ((hdeg h).[y])) - 1)%Z by sia. lia.
        -- intros v. split.
           ++ intros Hv. destruct (Htl v Hv) as [Hv1 Hv2]. apply Hm in Hv1.
              rewrite gso by exact Hv2. tauto.
           ++ intros [Hv1 Hv2]. destruct (Uint63.eq_dec v x) as [Ev|Ev].
              ** subst v. rewrite gss in Hv2 by (rewrite LP; exact Bx). exfalso. apply (NN y Hy). congruence.
              ** rewrite gso in Hv2 by exact Ev.
                 assert (Hvl : In v l) by (apply Hm; tauto).
                 apply (Permutation_in _ Hperm) in Hvl. destruct Hvl as [E|E]; [congruence | exact E].
    + apply eqb_false_spec in E2.
      apply cut_finish; sx; try assumption; try reflexivity.
      * apply lens_mrk, lens_par, lens_deg, lens_lft, lens_rgt, Hl.
      * intros p Hpy. rewrite !gso by exact Hpy. tauto.
      * intros i Hi. rewrite !gso; [tauto | |]; intro E; subst i; apply Hi; apply Pt; assumption.
      * unfold kids_ok; sx; change (hpar h).[x] with y. right. exists t. split; [exact Hrt|split; [exact Hndt|split; [|split]]].
        -- apply (Permutation_in _ Hperm) in Hc. destruct Hc as [E|E]; [congruence | exact E].
        -- rewrite gss by (rewrite LD; exact By).
           assert ((φ ((hdeg h).[y] - 1)) = (φ ((hdeg h).[y])) - 1)%Z by sia. lia.
        -- intros v. split.
           ++ intros Hv. destruct (Htl v Hv) as [Hv1 Hv2]. apply Hm in Hv1.
              rewrite gso by exact Hv2. tauto.
           ++ intros [Hv1 Hv2]. destruct (Uint63.eq_dec v x) as [Ev|Ev].
              ** subst v. rewrite gss in Hv2 by (rewrite LP; exact Bx). exfalso. apply (NN y Hy). congruence.
              ** rewrite gso in Hv2 by exact Ev.
                 assert (Hvl : In v l) by (apply Hm; tauto).
                 apply (Permutation_in _ Hperm) in Hvl. destruct Hvl as [E|E]; [congruence | exact E].
Qed.

(* ------------------------------------------------------------------ *)
(* CASCADING-CUT and DECREASE-KEY                                      *)
(* ------------------------------------------------------------------ *)

Lemma HI_mrk : forall h N ns eo em i v, HI h N ns eo em -> HI (s_mrk h i v) N ns eo em.
Proof.
  intros h N ns eo em i v [C Hp Hb Hr]. constructor.
  - apply (core_frame h); [exact C | apply lens_mrk, (co_len _ _ _ _ C) | |]; intros; sx; tauto.
  - sx. exact Hp.
  - sx. exact Hb.
  - apply (roots_frame h); [exact Hr | reflexivity | |]; intros; sx; tauto.
Qed.

Lemma HI_ex : forall h N ns em x, HI h N ns nil em -> HI h N ns x em.
Proof.
  intros h N ns em x [C Hp Hb Hr]. constructor; auto.
  destruct C as [C1 C2 C3 C4 C5 C6]. constructor; auto.
  intros v Hv _ Hpv. apply C5; auto.
  intro E. subst v. pose proof (C3 _ Hv). pose proof (lens_N _ _ C1). rewrite nil_val in *. lia.
Qed.

Lemma HI_ex_m : forall h N ns eo x, HI h N ns eo nil -> HI h N ns eo x.
Proof.
  intros h N ns eo x [C Hp Hb (Lr & Hnd & Hm & Hrr)]. constructor; auto.
  exists Lr. split; [exact Hnd|split; [exact Hm|]].
  destruct Hrr as [H1 | (Hr & Hmin & Hk)]; [left; exact H1|]. right. split; [exact Hr|split; [exact Hmin|]].
  intros v Hv _. apply Hk; [exact Hv|]. apply (node_not_nil _ _ _ _ _ C). apply Hm in Hv. tauto.
Qed.

Lemma ccut_eq : forall h y cnt H, ccut h y cnt H =
  match bdec (0 <? cnt) with
  | left Hc =>
      let z := (hpar h).[y] in
      if z =? nil then h
      else if (hmrk h).[y] =? 0 then s_mrk h y 1
      else ccut (fh_cut h y z) z (cnt - 1) (Acc_inv H (dec_cnt cnt Hc))
  | right _ => h
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma ccut_spec : forall z cnt (H : Acc (Zwf 0) (φ cnt)) h N ns y,
  (φ cnt) = z -> HI h N ns nil nil -> In y ns ->
  HI (ccut h y cnt H) N ns nil nil /\ hkey (ccut h y cnt H) = hkey h /\
  (forall v, (hpar h).[v] = nil -> (hpar (ccut h y cnt H)).[v] = nil).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros cnt H h N ns y Hz HI0 Hy.
  rewrite ccut_eq. destruct (bdec (0 <? cnt)) as [Hc|Hc]; [|tauto].
  cbv zeta. destruct ((hpar h).[y] =? nil) eqn:E1; [tauto|].
  destruct ((hmrk h).[y] =? 0) eqn:E2.
  - split; [apply HI_mrk; exact HI0|]. sx. tauto.
  - apply eqb_false_spec in E1.
    assert (Hpy : In (hpar h).[y] ns) by (destruct (hi_par _ _ _ _ _ HI0 y Hy); [contradiction | assumption]).
    destruct (cut_spec h N ns y (HI_ex _ _ _ _ _ HI0) Hy Hpy) as (HI1 & K1 & P1).
    destruct (IH (φ (cnt - 1)) ltac:(rewrite <- Hz; apply dec_cnt; exact Hc) (cnt - 1)
                (Acc_inv H (dec_cnt cnt Hc)) _ N ns (hpar h).[y] eq_refl HI1 Hpy)
      as (HI2 & K2 & P2).
    split; [exact HI2|]. split; [rewrite K2; exact K1|].
    intros v Hv. apply P2. rewrite P1. destruct (Uint63.eq_dec v y) as [E|E].
    + subst v. apply gss. rewrite (proj1 (proj2 (co_len _ _ _ _ (hi_core _ _ _ _ _ HI0)))).
      apply (co_range _ _ _ _ (hi_core _ _ _ _ _ HI0)). exact Hy.
    + rewrite gso by exact E. exact Hv.
Qed.

(* Lowering the key of x keeps the order everywhere but above x. *)
Lemma core_key : forall h N ns x k, core h N ns nil -> In x ns -> ((φ k) <= kv h x)%Z ->
  core (s_key h x k) N ns x.
Proof.
  intros h N ns x k C Hx Hk.
  pose proof (co_len _ _ _ _ C) as Hl. pose proof Hl as (LK & _).
  pose proof (co_range _ _ _ _ C x Hx) as Bx.
  destruct C as [C1 C2 C3 C4 C5 C6].
  constructor; [apply lens_key; exact C1 | exact C2 | exact C3 | exact C4 | | exact C6].
  - intros v Hv Hne Hpv. sx. unfold kv; sx.
    assert (NNv : v <> nil) by (intro E; subst v; pose proof (C3 _ Hv); pose proof (lens_N _ _ C1); rewrite nil_val in *; lia).
    pose proof (C5 v Hv NNv Hpv) as O. unfold kv in O.
    rewrite (gso _ v x) by exact Hne.
    destruct (Uint63.eq_dec (hpar h).[v] x) as [E|E].
    + rewrite E. rewrite gss by (rewrite LK; exact Bx). rewrite E in O. unfold kv in Hk. lia.
    + rewrite gso by exact E. exact O.
Qed.

Lemma core_noex : forall h N ns x, core h N ns x ->
  (In (hpar h).[x] ns -> (kv h (hpar h).[x] <= kv h x)%Z) -> core h N ns nil.
Proof.
  intros h N ns x [C1 C2 C3 C4 C5 C6] Hx.
  constructor; [exact C1 | exact C2 | exact C3 | exact C4 | | exact C6].
  intros v Hv _ Hpv. destruct (Uint63.eq_dec v x) as [E|E]; [subst; auto | apply C5; auto].
Qed.

(* The final test of DECREASE-KEY. *)
Lemma fixmin_spec : forall h N ns x, HI h N ns nil x -> In x ns ->
  ((hpar h).[x] = nil \/ (kv h (hmin h) <= kv h x)%Z) ->
  HI (if (hkey h).[x] <? (hkey h).[hmin h] then s_min h x else h) N ns nil nil.
Proof.
  intros h N ns x [C Hp Hb Hro] Hx Hc.
  destruct (roots_bound _ _ _ _ _ C Hro) as (Lr & Hnd & Hm & Hrr & HbL).
  assert (NN : forall v, In v ns -> v <> nil) by (intros v Hv; exact (node_not_nil _ _ _ _ _ C Hv)).
  destruct ((hkey h).[x] <? (hkey h).[hmin h]) eqn:E; constructor; sx; auto.
  - apply (core_frame h); [exact C | apply lens_min, (co_len _ _ _ _ C) | |]; intros; sx; tauto.
  - rewrite ltb_spec in E.
    assert (Px : (hpar h).[x] = nil) by (destruct Hc as [Hc|Hc]; [exact Hc | unfold kv in Hc; lia]).
    exists Lr. split; [exact Hnd | split; [intros v; sx; apply Hm|]].
    right. sx. destruct Hrr as [[E1 E2] | (Hr & Hmin & Hk)].
    + exfalso. assert (In x Lr) by (apply Hm; tauto). subst Lr. contradiction.
    + split; [exact Hr|split; [apply Hm; tauto|]].
      intros v Hv _. unfold kv; sx. destruct (Uint63.eq_dec v x) as [Ev|Ev]; [subst; lia|].
      pose proof (Hk v Hv Ev). unfold kv in *. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E.
    exists Lr. split; [exact Hnd | split; [exact Hm|]].
    destruct Hrr as [[E1 E2] | (Hr & Hmin & Hk)]; [left; tauto|].
    right. split; [exact Hr|split; [exact Hmin|]].
    intros v Hv _. destruct (Uint63.eq_dec v x) as [Ev|Ev]; [subst; unfold kv; lia|].
    apply Hk; assumption.
Qed.

Lemma roots_key : forall h ns x k, roots_ok h ns nil -> (hpar h).[x] <> nil ->
  roots_ok (s_key h x k) ns nil.
Proof.
  intros h ns x k (Lr & Hnd & Hm & Hrr) Px. exists Lr. split; [exact Hnd|split; [exact Hm|]].
  destruct Hrr as [H1 | (Hr & Hmin & Hk)]; [left; exact H1|]. right. sx.
  split; [exact Hr|split; [exact Hmin|]].
  assert (Hmx : hmin h <> x) by (intro E; apply Px; rewrite <- E; apply Hm; exact Hmin).
  intros v Hv Hvn. unfold kv; sx. rewrite (gso _ (hmin h)) by exact Hmx.
  rewrite (gso _ v) by (intro E; subst v; apply Px; apply Hm; exact Hv).
  apply Hk; assumption.
Qed.

Lemma decrease_spec : forall h N ns x k, HI h N ns nil nil -> In x ns -> ((φ k) <= kv h x)%Z ->
  HI (fh_decrease h x k) N ns nil nil /\ hkey (fh_decrease h x k) = (hkey h).[x <- k].
Proof.
  intros h N ns x k HI0 Hx Hk.
  pose proof HI0 as [C Hp Hb Hro].
  pose proof (co_len _ _ _ _ C) as Hl. pose proof Hl as (LK & LP & _).
  pose proof (co_range _ _ _ _ C x Hx) as Bx.
  assert (Kx : (hkey (s_key h x k)).[x] = k) by (sx; apply gss; rewrite LK; exact Bx).
  pose proof (core_key _ _ _ _ _ C Hx Hk) as C1.
  unfold fh_decrease. cbv zeta.
  destruct ((hpar (s_key h x k)).[x] =? nil) eqn:E1.
  - apply eqb_spec in E1. sx. rewrite <- Kx at 1.
    split; [|destruct (_ <? _); reflexivity].
    apply (fixmin_spec (s_key h x k)); [| exact Hx | left; exact E1].
    constructor; sx.
    + apply (core_noex _ _ _ x C1). sx. rewrite E1. intro E. exfalso. exact (nil_notin _ _ _ _ C E).
    + exact Hp.
    + exact Hb.
    + destruct Hro as (Lr & Hnd & Hm & Hrr). exists Lr. split; [exact Hnd|split; [exact Hm|]].
      destruct Hrr as [H1 | (Hr & Hmin & Hkk)]; [left; exact H1|]. right. sx.
      split; [exact Hr|split; [exact Hmin|]].
      intros v Hv Hvx. unfold kv; sx. rewrite (gso _ v) by exact Hvx.
      destruct (Uint63.eq_dec (hmin h) x) as [Em|Em].
      * rewrite Em. rewrite gss by (rewrite LK; exact Bx).
        pose proof (Hkk v Hv (node_not_nil _ _ _ _ _ C (proj1 (proj1 (Hm v) Hv)))) as O.
        unfold kv in *. rewrite Em in O. lia.
      * rewrite gso by exact Em. apply Hkk; [exact Hv|].
        exact (node_not_nil _ _ _ _ _ C (proj1 (proj1 (Hm v) Hv))).
  - apply eqb_false_spec in E1. sx.
    assert (Hpx : In (hpar h).[x] ns) by (destruct (Hp x Hx); [contradiction | assumption]).
    assert (HI1 : HI (s_key h x k) N ns x nil).
    { constructor; sx; [exact C1 | exact Hp | exact Hb |]. apply roots_key; assumption. }
    destruct (k <? (hkey h).[x <- k].[(hpar h).[x]]) eqn:E2.
    + destruct (cut_spec _ _ _ _ HI1 Hx ltac:(sx; exact Hpx)) as (HI2 & K2 & P2).
      sx.
      set (h2 := fh_cut (s_key h x k) x (hpar h).[x]) in *.
      destruct (ccut_spec _ (PArray.length (hpar h)) (Zwf_well_founded 0 _) h2 N ns
                  (hpar h).[x] eq_refl HI2 Hpx) as (HI3 & K3 & P3).
      set (h3 := ccut h2 (hpar h).[x] (PArray.length (hpar h)) _) in *.
      assert (K3x : (hkey h3).[x] = k) by (rewrite K3, K2; exact Kx).
      rewrite <- K3x at 1. split; [|destruct (k <? (hkey h3).[hmin h3]); sx; rewrite K3, K2; reflexivity].
      apply (fixmin_spec h3); [| exact Hx | left].
      * constructor; [apply HI3 | apply HI3 | apply HI3 |]. destruct (hi_roots _ _ _ _ _ HI3) as (Lr & Hnd & Hm & Hrr).
        exists Lr. split; [exact Hnd|split; [exact Hm|]].
        destruct Hrr as [H1 | (Hr & Hmin & Hkk)]; [left; exact H1|]. right. split; [exact Hr|split; [exact Hmin|]].
        intros v Hv _. apply Hkk; [exact Hv|]. apply (node_not_nil _ _ _ _ _ (hi_core _ _ _ _ _ HI3)).
        apply Hm in Hv. tauto.
      * apply P3. rewrite P2. apply gss. rewrite LP. exact Bx.
    + rewrite <- Kx at 1. split; [|destruct (k <? (hkey (s_key h x k)).[hmin (s_key h x k)]); reflexivity].
      rewrite <- Bool.not_true_iff_false, ltb_spec in E2.
      assert (HI2 : HI (s_key h x k) N ns nil nil).
      { constructor; sx; [| exact Hp | exact Hb | apply roots_key; assumption].
        apply (core_noex _ _ _ x C1). intros _. unfold kv. sx. rewrite Kx.
        lia. }
      apply (fixmin_spec (s_key h x k)); [| exact Hx | right].
      * apply HI_ex_m. exact HI2.
      * destruct (HI_min _ _ _ HI2 x Hx) as (_ & _ & O). exact O.
Qed.

(* ------------------------------------------------------------------ *)
(* List helpers                                                        *)
(* ------------------------------------------------------------------ *)

Definition rem (z : int) (l : list int) : list int := filter (fun v => negb (v =? z)) l.

Lemma rem_In : forall z l v, In v (rem z l) <-> In v l /\ v <> z.
Proof.
  intros z l v. unfold rem. rewrite filter_In. rewrite Bool.negb_true_iff, eqb_false_spec. tauto.
Qed.

Lemma rem_NoDup : forall z l, NoDup l -> NoDup (rem z l).
Proof. intros z l H. apply NoDup_filter. exact H. Qed.

Lemma rem_length : forall z l, NoDup l -> In z l -> S (List.length (rem z l)) = List.length l.
Proof.
  intros z l. induction l as [| a t IH]; intros Hnd Hz; [destruct Hz|].
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Ha Hnd]. unfold rem. cbn [filter].
  destruct (eqb_spec a z) as [E1 _]. destruct (a =? z) eqn:E; cbn [negb].
  - specialize (E1 eq_refl). subst a. cbn [List.length]. f_equal.
    transitivity (List.length (filter (fun _ => true) t)).
    + f_equal. apply filter_ext_in. intros v Hv. destruct (eqb_spec v z) as [F _].
      destruct (v =? z) eqn:E'; [specialize (F eq_refl); subst; contradiction | reflexivity].
    + clear. induction t; cbn; congruence.
  - cbn [List.length]. f_equal. apply IH; [exact Hnd|].
    destruct Hz as [Hz|Hz]; [subst; rewrite eqb_refl in E; discriminate | exact Hz].
Qed.

Lemma len_bound : forall (l : list int) N, NoDup l -> (forall v, In v l -> ((φ v) < (φ N))%Z) ->
  (Z.of_nat (List.length l) <= (φ N))%Z.
Proof.
  intros l N Hnd Hb.
  assert (Hm : NoDup (map (fun v => Z.to_nat (φ v)) l)).
  { apply Injective_map_NoDup_in; [|exact Hnd].
    intros a b _ _ E. apply to_Z_inj. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). lia. }
  assert (Hi : incl (map (fun v => Z.to_nat (φ v)) l) (seq 0 (Z.to_nat (φ N)))).
  { intros a Ha. apply in_map_iff in Ha. destruct Ha as (v & E & Hv). subst a.
    apply in_seq. pose proof (Hb v Hv). pose proof (to_Z_bounded v). lia. }
  pose proof (NoDup_incl_length Hm Hi) as H. rewrite length_map, length_seq in H.
  pose proof (to_Z_bounded N). lia.
Qed.

Lemma deg_bound : forall h N ns ex p, core h N ns ex -> In p ns ->
  ((φ ((hdeg h).[p])) < (φ N))%Z.
Proof.
  intros h N ns ex p C Hp.
  pose proof (len_bound ns N (co_nodup _ _ _ _ C) (co_range _ _ _ _ C)) as Hns.
  pose proof (co_range _ _ _ _ C p Hp) as Bp.
  destruct (co_kids _ _ _ _ C p Hp) as [[D _] | (l & _ & Hnd & _ & Hd & Hm)].
  - rewrite D. change (φ 0) with 0%Z. lia.
  - destruct (co_ht _ _ _ _ C) as [ht Ht].
    assert (Hpl : ~ In p l).
    { intro E. apply Hm in E. destruct E as [E1 E2]. pose proof (Ht p E1) as F.
      rewrite E2 in F. specialize (F E1). lia. }
    assert (Hi : incl (p :: l) ns).
    { intros v [E|Hv]; [subst; exact Hp|]. apply Hm in Hv. tauto. }
    pose proof (NoDup_incl_length (NoDup_cons _ Hpl Hnd) Hi) as H. cbn [List.length] in H. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* LINK                                                                *)
(* ------------------------------------------------------------------ *)

Lemma link_core : forall h h' N ns x y, core h N ns nil -> In x ns -> In y ns -> x <> y ->
  (hpar h).[x] = nil -> (hpar h).[y] = nil -> (kv h x <= kv h y)%Z ->
  lens h' N -> hkey h' = hkey h -> hpar h' = (hpar h).[y <- x] ->
  (forall p, p <> x -> (hchd h').[p] = (hchd h).[p] /\ (hdeg h').[p] = (hdeg h).[p]) ->
  (forall i, i <> y -> (hpar h).[i] <> x ->
     (hlft h').[i] = (hlft h).[i] /\ (hrgt h').[i] = (hrgt h).[i]) ->
  kids_ok h' ns x -> core h' N ns nil.
Proof.
  intros h h' N ns x y C Hx Hy Hxy Px Py Kxy L' K' P' CD LR Kx.
  pose proof (co_len _ _ _ _ C) as Hl. pose proof Hl as (LK & LP & _).
  pose proof (co_range _ _ _ _ C y Hy) as By.
  assert (NN : forall v, In v ns -> v <> nil) by (intros v Hv; exact (node_not_nil _ _ _ _ _ C Hv)).
  assert (P'y : (hpar h').[y] = x) by (rewrite P'; apply gss; rewrite LP; exact By).
  assert (P'v : forall v, v <> y -> (hpar h').[v] = (hpar h).[v]) by (intros v Hv; rewrite P'; apply gso; exact Hv).
  pose proof C as [C1 C2 C3 C4 C5 [ht C6]].
  constructor; [exact L' | exact C2 | exact C3 | | |].
  - intros p Hp. destruct (Uint63.eq_dec p x) as [E|E]; [subst p; exact Kx|].
    destruct (CD p E) as [Cp Dp].
    destruct (C4 p Hp) as [[D1 D2] | (l & Hr & Hnd & Hc & Hd & Hm)].
    + left. split; [rewrite Dp; exact D1|]. intros v Hv.
      destruct (Uint63.eq_dec v y) as [Ev|Ev]; [subst v; rewrite P'y; congruence|].
      rewrite P'v by exact Ev. apply D2. exact Hv.
    + right. exists l. split; [|split; [exact Hnd|split; [|split]]].
      * apply (ring_frame _ _ _ _ _ Hr). intros i Hi. apply Hm in Hi. destruct Hi as [Hi1 Hi2].
        apply LR; [intro F; subst i; rewrite Py in Hi2; exact (NN p Hp (eq_sym Hi2)) | congruence].
      * rewrite Cp. exact Hc.
      * rewrite Dp. exact Hd.
      * intros v. rewrite Hm. destruct (Uint63.eq_dec v y) as [Ev|Ev].
        -- subst v. rewrite P'y, Py. split; intros [H1 H2]; [exfalso; exact (NN p Hp (eq_sym H2)) | congruence].
        -- rewrite P'v by exact Ev. tauto.
  - intros v Hv Hvn Hpv. unfold kv. rewrite K'. destruct (Uint63.eq_dec v y) as [Ev|Ev].
    + subst v. rewrite P'y. exact Kxy.
    + rewrite P'v in * by exact Ev. apply C5; assumption.
  - exists (fun v => if v =? x then Nat.max (ht x) (S (ht y)) else ht v).
    intros v Hv Hpv. destruct (Uint63.eq_dec v y) as [Ev|Ev].
    + subst v. rewrite P'y. rewrite eqb_refl.
      destruct (y =? x) eqn:E; [apply eqb_spec in E; congruence | lia].
    + rewrite P'v in * by exact Ev.
      assert (Evx : v <> x) by (intro F; subst v; rewrite Px in Hpv; exact (NN _ Hpv eq_refl)).
      destruct (v =? x) eqn:E; [apply eqb_spec in E; contradiction|].
      pose proof (C6 v Hv Hpv).
      destruct ((hpar h).[v] =? x) eqn:E'; [apply eqb_spec in E'; rewrite E' in H; lia | lia].
Qed.

Lemma link_spec : forall h N ns x y, core h N ns nil -> In x ns -> In y ns -> x <> y ->
  (hpar h).[x] = nil -> (hpar h).[y] = nil -> (kv h x <= kv h y)%Z ->
  let h' := fh_link h y x in
  core h' N ns nil /\ hpar h' = (hpar h).[y <- x] /\ hkey h' = hkey h /\ hbuf h' = hbuf h /\
  hmin h' = hmin h /\ (hdeg h').[x] = (hdeg h).[x] + 1 /\
  (forall i, i <> x -> (hdeg h').[i] = (hdeg h).[i]) /\
  (forall i, i <> y -> (hpar h).[i] <> x ->
     (hlft h').[i] = (hlft h).[i] /\ (hrgt h').[i] = (hrgt h).[i]).
Proof.
  intros h N ns x y C Hx Hy Hxy Px Py Kxy h'.
  pose proof (co_len _ _ _ _ C) as Hl. pose proof Hl as (LK & LP & LC & LL & LR & LD & LM & LB).
  pose proof (co_range _ _ _ _ C y Hy) as By. pose proof (co_range _ _ _ _ C x Hx) as Bx.
  pose proof (deg_bound _ _ _ _ _ C Hx) as Dx.
  assert (NN : forall v, In v ns -> v <> nil) by (intros v Hv; exact (node_not_nil _ _ _ _ _ C Hv)).
  assert (Hyx : y <> x) by congruence.
  unfold h', fh_link. destruct ((hdeg h).[x] =? 0) eqn:E.
  - apply eqb_spec in E. cbv beta iota zeta. sx.
    assert (K1 : forall v, In v ns -> (hpar h).[v] <> x).
    { destruct (co_kids _ _ _ _ C x Hx) as [[_ D2] | (l & Hr & _ & _ & Hd & _)]; [exact D2|].
      rewrite E in Hd. change (φ 0) with 0%Z in Hd. destruct l; [destruct Hr | cbn in Hd; lia]. }
    assert (D1 : (φ ((hdeg h).[x] + 1)) = 1%Z) by (rewrite E; reflexivity).
    split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|split]]]]].
    + apply (link_core h _ N ns x y C Hx Hy Hxy Px Py Kxy); sx.
      * apply lens_mrk, lens_deg, lens_par, lens_rgt, lens_lft, lens_chd, Hl.
      * reflexivity.
      * reflexivity.
      * intros p Hp. rewrite !gso by exact Hp. tauto.
      * intros i Hi _. rewrite !gso by exact Hi. tauto.
      * unfold kids_ok. sx. right. exists [y].
        split; [apply ring_single; rewrite gss; try reflexivity; rewrite ?lset; [rewrite LL | rewrite LR]; exact By|].
        split; [constructor; [intros []| constructor]|].
        split; [rewrite gss by (rewrite LC; exact Bx); left; reflexivity|].
        split; [rewrite gss by (rewrite LD; exact Bx); rewrite D1; reflexivity|].
        intros v. split.
        -- intros [E'|[]]. subst v. split; [exact Hy|]. apply gss. rewrite LP. exact By.
        -- intros [Hv1 Hv2]. destruct (Uint63.eq_dec v y) as [Ev|Ev]; [left; congruence|].
           rewrite gso in Hv2 by exact Ev. exfalso. exact (K1 v Hv1 Hv2).
    + rewrite gss by (rewrite LD; exact Bx). reflexivity.
    + split; [intros i Hi; rewrite gso by exact Hi; reflexivity|].
      intros i Hi _. rewrite !gso by exact Hi. tauto.
  - apply eqb_false_spec in E.
    destruct (co_kids _ _ _ _ C x Hx) as [[D1 _] | (l & Hr & Hnd & Hc & Hd & Hm)]; [contradiction|].
    destruct (ring_at _ _ _ _ Hr Hc) as (t & Hr' & Hperm).
    assert (Hyl : ~ In y l) by (intro F; apply Hm in F; destruct F as [_ F]; apply (NN x Hx); congruence).
    assert (Hyl' : ~ In y ((hchd h).[x] :: t)) by (intro F; apply Hyl; apply (Permutation_in _ (Permutation_sym Hperm)); exact F).
    assert (Hnd' : NoDup ((hchd h).[x] :: t)) by (apply (Permutation_NoDup Hperm); exact Hnd).
    assert (Hb' : forall i, In i (y :: (hchd h).[x] :: t) ->
        ((φ i) < (φ (PArray.length (hlft h))))%Z /\ ((φ i) < (φ (PArray.length (hrgt h))))%Z).
    { intros i [Ei|Hi]; [subst; rewrite LL, LR; split; exact By|].
      apply (Permutation_in _ (Permutation_sym Hperm)) in Hi. apply Hm in Hi.
      pose proof (co_range _ _ _ _ C i (proj1 Hi)). rewrite LL, LR. split; assumption. }
    pose proof (ring_ins_ok _ _ _ _ _ Hr' Hnd' Hyl' Hb') as Hri.
    assert (Pl : forall i, In i ((hchd h).[x] :: t) -> (hpar h).[i] = x).
    { intros i Hi. apply (Permutation_in _ (Permutation_sym Hperm)) in Hi. apply Hm in Hi. tauto. }
    assert (Hbin : In (hrgt h).[(hchd h).[x]] ((hchd h).[x] :: t)).
    { apply ring_cons in Hr'. destruct Hr' as (Ra & _). rewrite Ra. destruct t; [left|right; left]; reflexivity. }
    unfold ring_ins. cbv beta iota zeta. sx.
    split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|split]]]]].
    + apply (link_core h _ N ns x y C Hx Hy Hxy Px Py Kxy); sx.
      * apply lens_mrk, lens_deg, lens_par, lens_lft, lens_rgt, lens_lft, lens_rgt, Hl.
      * reflexivity.
      * reflexivity.
      * intros p Hp. rewrite !gso by exact Hp. tauto.
      * intros i Hi Hpi.
        assert (F1 : i <> (hchd h).[x]) by (intro F; subst i; apply Hpi; apply Pl; left; reflexivity).
        assert (F2 : i <> (hrgt h).[(hchd h).[x]]) by (intro F; subst i; apply Hpi; apply Pl; exact Hbin).
        rewrite !gso by assumption. tauto.
      * unfold kids_ok. sx. right. exists ((hchd h).[x] :: y :: t).
        split; [exact Hri|].
        split; [apply NoDup_cons_iff in Hnd'; destruct Hnd' as [Hn1 Hn2];
                constructor; [intros [F|F]; [congruence|contradiction] | constructor;
                [intro F; apply Hyl'; right; exact F | exact Hn2]]|].
        split; [left; reflexivity|].
        split.
        -- rewrite gss by (rewrite LD; exact Bx).
           pose proof (Permutation_length Hperm) as PL. cbn [List.length] in *.
           assert ((φ ((hdeg h).[x] + 1)) = (φ ((hdeg h).[x])) + 1)%Z by sia. lia.
        -- intros v. split.
           ++ intros Hv. destruct (Uint63.eq_dec v y) as [Ev|Ev].
              ** subst v. split; [exact Hy|]. apply gss. rewrite LP. exact By.
              ** rewrite gso by exact Ev.
                 assert (Hv' : In v ((hchd h).[x] :: t)) by (destruct Hv as [F|[F|F]]; [left; exact F | congruence | right; exact F]).
                 split; [|apply Pl; exact Hv'].
                 apply (Permutation_in _ (Permutation_sym Hperm)) in Hv'. apply Hm in Hv'. tauto.
           ++ intros [Hv1 Hv2]. destruct (Uint63.eq_dec v y) as [Ev|Ev]; [right; left; congruence|].
              rewrite gso in Hv2 by exact Ev.
              assert (Hv' : In v l) by (apply Hm; tauto).
              apply (Permutation_in _ Hperm) in Hv'. destruct Hv' as [F|F]; [left; exact F | right; right; exact F].
    + rewrite gss by (rewrite LD; exact Bx). reflexivity.
    + split; [intros i Hi; rewrite gso by exact Hi; reflexivity|].
      intros i Hi Hpi.
      assert (F1 : i <> (hchd h).[x]) by (intro F; subst i; apply Hpi; apply Pl; left; reflexivity).
      assert (F2 : i <> (hrgt h).[(hchd h).[x]]) by (intro F; subst i; apply Hpi; apply Pl; exact Hbin).
      rewrite !gso by assumption. tauto.
Qed.

(* ------------------------------------------------------------------ *)
(* CONSOLIDATE                                                         *)
(* ------------------------------------------------------------------ *)

(* During consolidation: the trees of A (as_) and the roots still to be
   processed (P) are the tops; A is indexed by degree; md bounds the
   degrees used. *)
Record CI (h : fh) (N : int) (ns as_ P : list int) (md : int) : Prop := {
  ci_core : core h N ns nil;
  ci_par : forall v, In v ns -> In (hpar h).[v] ns \/ In v as_ \/ In v P;
  ci_tops : forall v, In v as_ \/ In v P -> In v ns /\ ~ In (hpar h).[v] ns;
  ci_ndA : NoDup as_;
  ci_ndP : NoDup P;
  ci_dis : forall v, In v as_ -> ~ In v P;
  ci_aspar : forall v, In v as_ -> (hpar h).[v] = nil;
  ci_buf1 : forall v, In v as_ -> (hbuf h).[(hdeg h).[v]] = v;
  ci_buf2 : forall i, ((φ i) < (φ N))%Z ->
     (hbuf h).[i] = nil \/ (In (hbuf h).[i] as_ /\ (hdeg h).[(hbuf h).[i]] = i);
  ci_md : forall i, ((φ i) < (φ N))%Z -> ((φ md) < (φ i))%Z -> (hbuf h).[i] = nil;
  ci_mdN : ((φ md) < (φ N))%Z
}.

Lemma core_buf : forall h N ns ex i v, core h N ns ex -> core (s_buf h i v) N ns ex.
Proof.
  intros h N ns ex i v C. apply (core_frame h); [exact C | apply lens_buf, (co_len _ _ _ _ C) | |];
    intros; sx; tauto.
Qed.

Lemma link_step : forall h N ns as_ x P md d y w l,
  CI h N ns as_ (x :: P) md -> (hpar h).[x] = nil -> (hdeg h).[x] = d -> ((φ d) < (φ N))%Z ->
  (hbuf h).[d] = y -> In y as_ -> (hdeg h).[y] = d ->
  ((w = x /\ l = y) \/ (w = y /\ l = x)) -> (kv h w <= kv h l)%Z ->
  let h2 := fh_link (s_buf h d nil) l w in
  CI h2 N ns (rem y as_) (w :: P) md /\ (hpar h2).[w] = nil /\ (hdeg h2).[w] = d + 1 /\
  hkey h2 = hkey h /\ hmin h2 = hmin h /\ (forall i, In i P -> (hrgt h2).[i] = (hrgt h).[i]).
Proof.
  intros h N ns as_ x P md d y w l [C Cp Ct NA NP Dis Ap B1 B2 Md MdN] Px Dx Bd By Hy Dy Hwl Kwl h2.
  pose proof (co_len _ _ _ _ C) as Hl. pose proof Hl as (LK & LP & LC & LL & LR & LD & LM & LB).
  assert (NN : forall v, In v ns -> v <> nil) by (intros v Hv; exact (node_not_nil _ _ _ _ _ C Hv)).
  assert (Hx : In x ns /\ ~ In (hpar h).[x] ns) by (apply Ct; right; left; reflexivity).
  assert (Hy' : In y ns) by (apply Ct; left; exact Hy).
  assert (Hxy : x <> y) by (intro E; apply (Dis y Hy); left; exact E).
  apply NoDup_cons_iff in NP. destruct NP as [HxP NP].
  assert (Py : (hpar h).[y] = nil) by (apply Ap; exact Hy).
  assert (Hw : In w ns) by (destruct Hwl as [[-> ->]|[-> ->]]; tauto).
  assert (Hl' : In l ns) by (destruct Hwl as [[-> ->]|[-> ->]]; tauto).
  assert (Hwl' : w <> l) by (destruct Hwl as [[-> ->]|[-> ->]]; congruence).
  assert (Pw : (hpar h).[w] = nil) by (destruct Hwl as [[-> ->]|[-> ->]]; assumption).
  assert (Pl : (hpar h).[l] = nil) by (destruct Hwl as [[-> ->]|[-> ->]]; assumption).
  assert (Dw : (hdeg h).[w] = d) by (destruct Hwl as [[-> ->]|[-> ->]]; assumption).
  pose proof (core_buf _ _ _ _ d nil C) as C1.
  destruct (link_spec (s_buf h d nil) N ns w l C1 Hw Hl' Hwl' Pw Pl Kwl)
    as (C2 & P2 & K2 & B2' & M2 & D2w & D2 & LR2).
  fold h2 in C2, P2, K2, B2', M2, D2w, D2, LR2. clearbody h2. sx.
  assert (P2v : forall v, v <> l -> (hpar h2).[v] = (hpar h).[v]) by (intros v Hv; rewrite P2; apply gso; exact Hv).
  assert (P2l : (hpar h2).[l] = w) by (rewrite P2; apply gss; rewrite LP; apply (co_range _ _ _ _ C); exact Hl').
  assert (Inl : forall v, v = l -> v = x \/ v = y) by (intros v ->; destruct Hwl as [[-> ->]|[-> ->]]; tauto).
  assert (Inw : w = x \/ w = y) by (destruct Hwl as [[-> ->]|[-> ->]]; tauto).
  assert (NotAs : forall v, In v (rem y as_) -> v <> x /\ v <> y).
  { intros v Hv. apply rem_In in Hv. destruct Hv as [Hv1 Hv2]. split; [|exact Hv2].
    intro E; rewrite E in Hv1; apply (Dis x Hv1); left; reflexivity. }
  assert (B2d : (hbuf h2).[d] = nil) by (rewrite B2'; apply gss; rewrite LB; exact Bd).
  assert (B2o : forall i, i <> d -> (hbuf h2).[i] = (hbuf h).[i]) by (intros i Hi; rewrite B2'; apply gso; exact Hi).
  split; [|split; [rewrite P2v by exact Hwl'; exact Pw|split; [rewrite D2w; sx; rewrite Dw; reflexivity|
          split; [exact K2|split; [exact M2|]]]]].
  - constructor.
    + exact C2.
    + intros v Hv. destruct (Uint63.eq_dec v l) as [E|E]; [left; rewrite E, P2l; exact Hw|].
      rewrite P2v by exact E. destruct (Cp v Hv) as [H1|[H1|[H1|H1]]].
      * left; exact H1.
      * destruct (Uint63.eq_dec v y) as [Ev|Ev].
        -- right; right; left. subst v. destruct Inw as [Ew|Ew]; [|congruence].
           exfalso. destruct Hwl as [[_ ->]|[-> _]]; congruence.
        -- right; left. apply rem_In. tauto.
      * subst v. right; right; left. destruct Hwl as [[-> _]|[_ ->]]; [reflexivity | contradiction].
      * right; right; right. exact H1.
    + intros v Hv.
      assert (Hvl : v <> l /\ In v ns /\ ~ In (hpar h).[v] ns).
      { destruct Hv as [Hv|[Hv|Hv]].
        - destruct (NotAs v Hv). split; [intro E; destruct (Inl v E); contradiction|].
          apply Ct. left. apply rem_In in Hv. tauto.
        - subst v. split; [exact Hwl'|]. destruct Inw as [->| ->]; [tauto | apply Ct; left; exact Hy].
        - split; [intro E; destruct (Inl v E) as [E'|E']; rewrite E' in Hv;
                  [exact (HxP Hv) | exact (Dis y Hy (or_intror Hv))]|].
          apply Ct. right. right. exact Hv. }
      destruct Hvl as (Hvl & H1 & H2). split; [exact H1|]. rewrite P2v by exact Hvl. exact H2.
    + apply rem_NoDup. exact NA.
    + constructor; [|exact NP]. destruct Inw as [->| ->]; [exact HxP | intro F; exact (Dis y Hy (or_intror F))].
    + intros v Hv [E|E].
      * subst v. destruct (NotAs w Hv). destruct Inw; contradiction.
      * apply rem_In in Hv. exact (Dis v (proj1 Hv) (or_intror E)).
    + intros v Hv. destruct (NotAs v Hv).
      rewrite P2v by (intro E; destruct (Inl v E); contradiction). apply Ap. apply rem_In in Hv. tauto.
    + intros v Hv. destruct (NotAs v Hv) as [Hvx Hvy]. apply rem_In in Hv. destruct Hv as [Hv _].
      rewrite D2 by (intro E; subst; destruct Inw; contradiction). sx.
      assert (Ed : (hdeg h).[v] <> d) by (intro E; pose proof (B1 v Hv) as F; rewrite E, By in F; congruence).
      rewrite B2o by exact Ed. apply B1. exact Hv.
    + intros i Hi. destruct (Uint63.eq_dec i d) as [E|E]; [subst i; left; exact B2d|].
      rewrite B2o by exact E. destruct (B2 i Hi) as [F|[F1 F2]]; [left; exact F|right].
      assert (Fy : (hbuf h).[i] <> y) by (intro F; rewrite F, Dy in F2; congruence).
      assert (Fx : (hbuf h).[i] <> x) by (intro F; rewrite F in F1; exact (Dis x F1 (or_introl eq_refl))).
      split; [apply rem_In; tauto|].
      rewrite D2 by (destruct Inw as [->| ->]; congruence). sx. exact F2.
    + intros i Hi Hmi. destruct (Uint63.eq_dec i d) as [E|E]; [subst; exact B2d|].
      rewrite B2o by exact E. apply Md; assumption.
    + exact MdN.
  - intros i Hi.
    assert (F1 : i <> l).
    { intro E. subst i. destruct (Inl l eq_refl) as [E|E]; rewrite E in Hi;
        [exact (HxP Hi) | exact (Dis y Hy (or_intror Hi))]. }
    assert (F2 : (hpar h).[i] <> w).
    { intro E. apply (proj2 (Ct i (or_intror (or_intror Hi)))). rewrite E. exact Hw. }
    exact (proj2 (LR2 i F1 F2)).
Qed.

Lemma link_loop_eq : forall h x d N H, link_loop h x d N H =
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
Proof. intros. destruct H. reflexivity. Qed.

Lemma link_loop_spec : forall N z d (H : Acc (Zwf 0) (gap N d)) h ns as_ x P md,
  gap N d = z -> CI h N ns as_ (x :: P) md -> (hpar h).[x] = nil -> (hdeg h).[x] = d ->
  let r := link_loop h x d N H in
  (exists as', CI (fst r) N ns as' P (if md <? snd r then snd r else md)) /\
  hkey (fst r) = hkey h /\ hmin (fst r) = hmin h /\
  (forall i, In i P -> (hrgt (fst r)).[i] = (hrgt h).[i]).
Proof.
  intros N z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros d H h ns as_ x P md Hz HC Px Dx r. unfold r; clear r.
  pose proof HC as [C Cp Ct NA NP Dis Ap B1 B2 Md MdN].
  pose proof (co_len _ _ _ _ C) as Hl. pose proof Hl as (LK & LP & LC & LL & LR & LD & LM & LB).
  assert (Hx : In x ns /\ ~ In (hpar h).[x] ns) by (apply Ct; right; left; reflexivity).
  pose proof (deg_bound _ _ _ _ _ C (proj1 Hx)) as Bd. rewrite Dx in Bd.
  assert (NN : forall v, In v ns -> v <> nil) by (intros v Hv; exact (node_not_nil _ _ _ _ _ C Hv)).
  rewrite link_loop_eq. destruct (bdec (d <? N)) as [Hd|Hd];
    [| exfalso; rewrite <- Bool.not_true_iff_false, ltb_spec in Hd; lia].
  cbv zeta. destruct ((hbuf h).[d] =? nil) eqn:Ey.
  - apply eqb_spec in Ey. cbn [fst snd]. sx.
    split; [|split; [reflexivity|split; [reflexivity|intros; reflexivity]]].
    apply NoDup_cons_iff in NP. destruct NP as [HxP NP].
    assert (HxA : ~ In x as_) by (intro F; exact (Dis x F (or_introl eq_refl))).
    assert (Bx : (hbuf h).[d <- x].[d] = x) by (apply gss; rewrite LB; exact Bd).
    assert (Bo : forall i, i <> d -> (hbuf h).[d <- x].[i] = (hbuf h).[i]) by (intros; apply gso; assumption).
    exists (x :: as_). constructor; sx.
    + apply core_buf. exact C.
    + intros v Hv. destruct (Cp v Hv) as [H1|[H1|[H1|H1]]]; [left; exact H1| right; left; right; exact H1
        | right; left; left; exact H1 | right; right; exact H1].
    + intros v [[E|Hv]|Hv]; apply Ct; [right; left; exact E | left; exact Hv | right; right; exact Hv].
    + constructor; assumption.
    + exact NP.
    + intros v [E|Hv]; [rewrite <- E; exact HxP | intro F; exact (Dis v Hv (or_intror F))].
    + intros v [E|Hv]; [rewrite <- E; exact Px | apply Ap; exact Hv].
    + intros v [E|Hv]; [rewrite <- E, Dx; exact Bx|].
      assert (Ed : (hdeg h).[v] <> d).
      { intro E. pose proof (B1 v Hv) as F. rewrite E, Ey in F. apply (NN v); [apply Ct; left; exact Hv | auto]. }
      rewrite Bo by exact Ed. apply B1. exact Hv.
    + intros i Hi. destruct (Uint63.eq_dec i d) as [E|E].
      * subst i. right. rewrite Bx. split; [left; reflexivity | exact Dx].
      * rewrite Bo by exact E. destruct (B2 i Hi) as [F|[F1 F2]]; [left; exact F | right; split; [right; exact F1 | exact F2]].
    + intros i Hi Hmi. destruct (Uint63.eq_dec i d) as [E|E].
      * subst i. exfalso. destruct (md <? d) eqn:Em; [lia|].
        rewrite <- Bool.not_true_iff_false, ltb_spec in Em. lia.
      * rewrite Bo by exact E. apply Md; [exact Hi|]. destruct (md <? d) eqn:Em; [rewrite ltb_spec in Em|]; lia.
    + destruct (md <? d); lia.
  - apply eqb_false_spec in Ey.
    assert (Hd' : ((φ d) < (φ N))%Z) by exact Bd.
    destruct (B2 d Hd') as [F|[Hy Dy]]; [contradiction|].
    sx. destruct ((hkey h).[(hbuf h).[d]] <? (hkey h).[x]) eqn:Ek.
    + rewrite ltb_spec in Ek.
      destruct (link_step h N ns as_ x P md d (hbuf h).[d] (hbuf h).[d] x HC Px Dx Bd eq_refl Hy Dy
                 (or_intror (conj eq_refl eq_refl)) ltac:(unfold kv; lia))
        as (HC2 & P2 & D2 & K2 & M2 & R2).
      destruct (IH (gap N (d + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hd) (d + 1)
                 (Acc_inv H (dec_step N d Hd)) _ ns _ _ P md eq_refl HC2 P2 D2)
        as (Hc & K3 & M3 & R3).
      split; [exact Hc|]. split; [rewrite K3; exact K2|]. split; [rewrite M3; exact M2|].
      intros i Hi. rewrite R3 by exact Hi. apply R2. exact Hi.
    + rewrite <- Bool.not_true_iff_false, ltb_spec in Ek.
      destruct (link_step h N ns as_ x P md d (hbuf h).[d] x (hbuf h).[d] HC Px Dx Bd eq_refl Hy Dy
                 (or_introl (conj eq_refl eq_refl)) ltac:(unfold kv; lia))
        as (HC2 & P2 & D2 & K2 & M2 & R2).
      destruct (IH (gap N (d + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hd) (d + 1)
                 (Acc_inv H (dec_step N d Hd)) _ ns _ _ P md eq_refl HC2 P2 D2)
        as (Hc & K3 & M3 & R3).
      split; [exact Hc|]. split; [rewrite K3; exact K2|]. split; [rewrite M3; exact M2|].
      intros i Hi. rewrite R3 by exact Hi. apply R2. exact Hi.
Qed.

Lemma core_par_top : forall h N ns ex w q, core h N ns ex -> In w ns ->
  ~ In (hpar h).[w] ns -> ~ In q ns -> core (s_par h w q) N ns ex.
Proof.
  intros h N ns ex w q C Hw Pw Hq.
  pose proof (co_len _ _ _ _ C) as Hl. pose proof Hl as (LK & LP & _).
  pose proof (co_range _ _ _ _ C w Hw) as Bw.
  assert (P'w : (hpar (s_par h w q)).[w] = q) by (sx; apply gss; rewrite LP; exact Bw).
  assert (P'v : forall v, v <> w -> (hpar (s_par h w q)).[v] = (hpar h).[v]) by (intros; sx; apply gso; assumption).
  pose proof C as [C1 C2 C3 C4 C5 [ht C6]].
  constructor; [apply lens_par, C1 | exact C2 | exact C3 | | |].
  - intros p Hp. unfold kids_ok. destruct (C4 p Hp) as [[D1 D2] | (l & Hr & Hnd & Hc & Hd & Hm)]; sx.
    + left. split; [exact D1|]. intros v Hv. destruct (Uint63.eq_dec v w) as [E|E].
      * subst v. rewrite gss by (rewrite LP; exact Bw). intro F; subst; contradiction.
      * rewrite gso by exact E. apply D2. exact Hv.
    + right. exists l. split; [exact Hr|split; [exact Hnd|split; [exact Hc|split; [exact Hd|]]]].
      intros v. rewrite Hm. destruct (Uint63.eq_dec v w) as [E|E].
      * subst v. rewrite gss by (rewrite LP; exact Bw).
        split; intros [F1 F2]; [rewrite F2 in Pw; contradiction | subst; contradiction].
      * rewrite gso by exact E. tauto.
  - intros v Hv Hne Hpv. destruct (Uint63.eq_dec v w) as [E|E].
    + subst v. rewrite P'w in Hpv. contradiction.
    + rewrite P'v in * by exact E. unfold kv; sx. apply C5; assumption.
  - exists ht. intros v Hv Hpv. destruct (Uint63.eq_dec v w) as [E|E].
    + subst v. rewrite P'w in Hpv. contradiction.
    + rewrite P'v in * by exact E. auto.
Qed.

Lemma proc_spec : forall h N ns as_ w P md, CI h N ns as_ (w :: P) md ->
  let r := proc h w md in
  (exists as', CI (fst r) N ns as' P (snd r)) /\
  hkey (fst r) = hkey h /\ hmin (fst r) = hmin h /\
  (forall i, In i P -> (hrgt (fst r)).[i] = (hrgt h).[i]).
Proof.
  intros h N ns as_ w P md HC r. unfold r, proc; clear r. cbv zeta. cbn [fst snd].
  pose proof HC as [C Cp Ct NA NP Dis Ap B1 B2 Md MdN].
  pose proof (co_len _ _ _ _ C) as Hl. pose proof Hl as (LK & LP & LC & LL & LR & LD & LM & LB).
  assert (Hw : In w ns /\ ~ In (hpar h).[w] ns) by (apply Ct; right; left; reflexivity).
  pose proof (co_range _ _ _ _ C w (proj1 Hw)) as Bw.
  assert (P'w : (hpar (s_par h w nil)).[w] = nil) by (sx; apply gss; rewrite LP; exact Bw).
  assert (P'v : forall v, v <> w -> (hpar (s_par h w nil)).[v] = (hpar h).[v]) by (intros; sx; apply gso; assumption).
  assert (HC1 : CI (s_par h w nil) N ns as_ (w :: P) md).
  { constructor; sx; try assumption.
    - apply core_par_top; try tauto. exact (nil_notin _ _ _ _ C).
    - intros v Hv. destruct (Uint63.eq_dec v w) as [E|E]; [subst; right; right; left; reflexivity|].
      rewrite gso by exact E. apply Cp. exact Hv.
    - intros v Hv. destruct (Uint63.eq_dec v w) as [E|E].
      + subst v. rewrite gss by (rewrite LP; exact Bw). split; [tauto | exact (nil_notin _ _ _ _ C)].
      + rewrite gso by exact E. apply Ct. exact Hv.
    - intros v Hv. rewrite gso by (intro E; subst; exact (Dis w Hv (or_introl eq_refl))). apply Ap. exact Hv. }
  sx. revert HC1 P'w.
  generalize (Zwf_well_founded 0 (gap (PArray.length (hbuf h)) (hdeg h).[w])).
  rewrite LB. intros H HC1 P'w.
  destruct (link_loop_spec N _ (hdeg h).[w] H _ ns as_ w P md eq_refl HC1 P'w eq_refl)
    as (Hc & K & M & R). sx.
  split; [exact Hc|]. split; [exact K|]. split; [exact M|]. exact R.
Qed.

Lemma walk_eq : forall h cur stop md cnt H, walk h cur stop md cnt H =
  if cur =? stop then (h, md)
  else
    match bdec (0 <? cnt) with
    | left Hc =>
        let nx := (hrgt h).[cur] in
        let r := proc h cur md in
        walk (fst r) nx stop (snd r) (cnt - 1) (Acc_inv H (dec_cnt cnt Hc))
    | right _ => (h, md)
    end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma walk_spec : forall z cnt (H : Acc (Zwf 0) (φ cnt)) h N ns as_ rm Q stop md,
  (φ cnt) = z -> CI h N ns as_ (rm ++ Q) md -> rseq (hrgt h) rm stop -> ~ In stop rm ->
  (Z.of_nat (List.length rm) <= (φ cnt))%Z ->
  let r := walk h (hd stop rm) stop md cnt H in
  (exists as', CI (fst r) N ns as' Q (snd r)) /\
  hkey (fst r) = hkey h /\ hmin (fst r) = hmin h /\
  (forall i, In i Q -> (hrgt (fst r)).[i] = (hrgt h).[i]).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros cnt H h N ns as_ rm Q stop md Hz HC Hr Hs Hl r. unfold r; clear r.
  rewrite walk_eq. destruct rm as [| a rm'].
  - cbn [hd]. rewrite eqb_refl. cbn [fst snd]. split; [exists as_; exact HC|]. tauto.
  - cbn [hd]. destruct (a =? stop) eqn:E; [apply eqb_spec in E; exfalso; apply Hs; left; congruence|].
    cbn [List.length] in Hl.
    destruct (bdec (0 <? cnt)) as [Hc|Hc];
      [| exfalso; rewrite <- Bool.not_true_iff_false, ltb_spec in Hc; change (φ 0) with 0%Z in Hc; lia].
    cbv zeta. cbn [rseq] in Hr. destruct Hr as [Ra Hr'].
    destruct (proc_spec h N ns as_ a (rm' ++ Q) md HC) as ((as1 & HC1) & K1 & M1 & R1).
    assert (Hr1 : rseq (hrgt (fst (proc h a md))) rm' stop).
    { apply (rseq_frame (hrgt h)); [exact Hr'|]. intros i Hi. apply R1. apply in_or_app. left. exact Hi. }
    rewrite Ra.
    destruct (IH (φ (cnt - 1)) ltac:(rewrite <- Hz; apply dec_cnt; exact Hc) (cnt - 1)
                (Acc_inv H (dec_cnt cnt Hc)) _ N ns as1 rm' Q stop _ eq_refl HC1 Hr1
                ltac:(intro F; apply Hs; right; exact F) ltac:(sia))
      as (Hc2 & K2 & M2 & R2).
    split; [exact Hc2|]. split; [rewrite K2; exact K1|]. split; [rewrite M2; exact M1|].
    intros i Hi. rewrite R2 by exact Hi. apply R1. apply in_or_app. right. exact Hi.
Qed.

(* Rebuilding the root list from A. *)
Record RI (h : fh) (N : int) (ns as_ Lr : list int) (d md : int) : Prop := {
  ri_core : core h N ns nil;
  ri_par : forall v, In v ns -> In (hpar h).[v] ns \/ In v as_ \/ In v Lr;
  ri_tops : forall v, In v as_ \/ In v Lr -> In v ns /\ (hpar h).[v] = nil;
  ri_ndA : NoDup as_;
  ri_ndL : NoDup Lr;
  ri_dis : forall v, In v as_ -> ~ In v Lr;
  ri_buf1 : forall v, In v as_ -> (hbuf h).[(hdeg h).[v]] = v /\ ((φ d) <= (φ ((hdeg h).[v])))%Z;
  ri_buf2 : forall i, ((φ i) < (φ N))%Z ->
     (hbuf h).[i] = nil \/ (In (hbuf h).[i] as_ /\ (hdeg h).[(hbuf h).[i]] = i);
  ri_low : forall i, ((φ i) < (φ d))%Z -> (hbuf h).[i] = nil;
  ri_md : forall i, ((φ i) < (φ N))%Z -> ((φ md) < (φ i))%Z -> (hbuf h).[i] = nil;
  ri_mdN : ((φ md) < (φ N))%Z;
  ri_d : ((φ d) <= (φ md) + 1)%Z;
  ri_rr : rr h Lr nil
}.

Lemma rebuild_eq : forall h d M H, rebuild h d M H =
  match bdec (d <? M) with
  | left Hd =>
      let x := (hbuf h).[d] in
      let h1 := if x =? nil then h else root_add (s_buf h d nil) x in
      rebuild h1 (d + 1) M (Acc_inv H (dec_step M d Hd))
  | right _ => h
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma rebuild_spec : forall N md z d (H : Acc (Zwf 0) (gap (md + 1) d)) h ns as_ Lr,
  gap (md + 1) d = z -> RI h N ns as_ Lr d md ->
  HI (rebuild h d (md + 1) H) N ns nil nil /\ hkey (rebuild h d (md + 1) H) = hkey h.
Proof.
  intros N md z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros d H h ns as_ Lr Hz HR.
  pose proof HR as [C Rp Rt NA NL Dis B1 B2 Lo Md MdN Rd Rr].
  pose proof (co_len _ _ _ _ C) as Hl. pose proof Hl as (LK & LP & LC & LL & LR & LD & LM & LB).
  assert (NN : forall v, In v ns -> v <> nil) by (intros v Hv; exact (node_not_nil _ _ _ _ _ C Hv)).
  assert (HM : (φ (md + 1)) = ((φ md) + 1)%Z) by (pose proof (lens_N _ _ Hl); sia).
  rewrite rebuild_eq. destruct (bdec (d <? md + 1)) as [Hd|Hd].
  - assert (Hd' : ((φ d) < (φ md) + 1)%Z) by (rewrite <- HM; apply ltb_spec; exact Hd).
    assert (Hlt : Zwf 0 (gap (md + 1) (d + 1)) z) by (rewrite <- Hz; apply dec_step; exact Hd).
    cbv zeta.
    assert (Bd : ((φ d) < (φ N))%Z) by lia.
    assert (Hd1 : (φ (d + 1)) = ((φ d) + 1)%Z) by (pose proof (lens_N _ _ Hl); sia).
    destruct ((hbuf h).[d] =? nil) eqn:Ex.
    + apply eqb_spec in Ex.
      apply (IH _ Hlt) with (as_ := as_) (Lr := Lr); [reflexivity|].
      constructor; try assumption.
      * intros v Hv. destruct (B1 v Hv) as [F1 F2]. split; [exact F1|].
        rewrite Hd1. destruct (Z.eq_dec (φ d) (φ ((hdeg h).[v]))) as [E|E]; [|lia].
        exfalso. apply to_Z_inj in E. rewrite <- E, Ex in F1.
        apply (NN v); [apply Rt; left; exact Hv | auto].
      * intros i Hi. rewrite Hd1 in Hi. destruct (Z.eq_dec (φ i) (φ d)) as [E|E];
          [apply to_Z_inj in E; rewrite E; exact Ex | apply Lo; lia].
      * lia.
    + apply eqb_false_spec in Ex.
      destruct (B2 d Bd) as [F|[Hx Dx]]; [contradiction|].
      set (x := (hbuf h).[d]) in *.
      assert (HxL : ~ In x Lr) by (apply Dis; exact Hx).
      destruct (Rt x (or_introl Hx)) as [Hxn Px].
      assert (C1 : core (s_buf h d nil) N ns nil) by (apply core_buf; exact C).
      destruct (root_add_spec (s_buf h d nil) N Lr x (lens_buf _ _ _ _ Hl) NL
                 ltac:(intros v [E|Hv]; [rewrite <- E; exact (co_range _ _ _ _ C x Hxn) |
                       apply (co_range _ _ _ _ C); apply Rt; right; exact Hv])
                 HxL Rr)
        as (L2 & (Lr' & Hperm & Hrr') & K2 & P2 & Ch2 & D2 & M2 & B2' & FR).
      sx.
      assert (Bdn : (hbuf h).[d <- nil].[d] = nil) by (apply gss; rewrite LB; exact Bd).
      assert (Bo : forall i, i <> d -> (hbuf h).[d <- nil].[i] = (hbuf h).[i]) by (intros; apply gso; assumption).
      set (h2 := root_add (s_buf h d nil) x) in *.
      assert (Tops : forall v, In v (x :: Lr) -> (hpar h).[v] = nil) by
        (intros v [E|Hv]; [rewrite <- E; exact Px | apply Rt; right; exact Hv]).
      destruct (IH _ Hlt (d + 1) (Acc_inv H (dec_step (md + 1) d Hd)) h2 ns (rem x as_) Lr' eq_refl)
        as [HI2 K]; [| split; [exact HI2 | rewrite K, K2; reflexivity]].
      constructor; rewrite ?K2, ?P2, ?Ch2, ?D2, ?B2'; sx.
      * apply (core_frame (s_buf h d nil)); [exact C1 | exact L2 | |].
        -- intros v _. rewrite K2, P2, Ch2, D2. tauto.
        -- intros i Hi Hpi. apply FR. intro F. sx. rewrite (Tops i F) in Hpi.
           exact (NN _ Hpi eq_refl).
      * intros v Hv. destruct (Rp v Hv) as [F|[F|F]]; [left; exact F| |].
        -- destruct (Uint63.eq_dec v x) as [E|E].
           ++ right; right. apply (Permutation_in _ (Permutation_sym Hperm)). left. exact (eq_sym E).
           ++ right; left. apply rem_In. tauto.
        -- right; right. apply (Permutation_in _ (Permutation_sym Hperm)). right. exact F.
      * intros v [Hv|Hv].
        -- apply rem_In in Hv. apply Rt. left. tauto.
        -- apply (Permutation_in _ Hperm) in Hv. destruct Hv as [E|Hv];
             [rewrite <- E; split; [exact Hxn | exact Px] | apply Rt; right; exact Hv].
      * apply rem_NoDup. exact NA.
      * apply (Permutation_NoDup (Permutation_sym Hperm)). constructor; assumption.
      * intros v Hv F. apply rem_In in Hv. destruct Hv as [Hv1 Hv2].
        apply (Permutation_in _ Hperm) in F. destruct F as [E|F]; [exact (Hv2 (eq_sym E)) | exact (Dis v Hv1 F)].
      * intros v Hv. apply rem_In in Hv. destruct Hv as [Hv1 Hv2]. destruct (B1 v Hv1) as [F1 F2].
        assert (Ed : (hdeg h).[v] <> d) by (intro E; rewrite E in F1; apply Hv2; rewrite <- F1; reflexivity).
        rewrite Bo by exact Ed. split; [exact F1|].
        rewrite Hd1. assert ((φ ((hdeg h).[v])) <> (φ d)) by (intro E; apply Ed; apply to_Z_inj; exact E). lia.
      * intros i Hi. destruct (Uint63.eq_dec i d) as [E|E]; [rewrite E; left; exact Bdn|].
        rewrite Bo by exact E. destruct (B2 i Hi) as [F|[F1 F2]]; [left; exact F|right].
        split; [|exact F2]. apply rem_In. split; [exact F1|]. intro F. rewrite F, Dx in F2. congruence.
      * intros i Hi. rewrite Hd1 in Hi. destruct (Uint63.eq_dec i d) as [E|E]; [rewrite E; exact Bdn|].
        rewrite Bo by exact E. apply Lo. assert ((φ i) <> (φ d)) by (intro F; apply E; apply to_Z_inj; exact F). lia.
      * intros i Hi Hmi. destruct (Uint63.eq_dec i d) as [E|E]; [rewrite E; exact Bdn|].
        rewrite Bo by exact E. apply Md; assumption.
      * exact MdN.
      * lia.
      * exact Hrr'.
  - assert (Hd' : ((φ md) + 1 <= (φ d))%Z) by (rewrite <- HM; rewrite <- Bool.not_true_iff_false, ltb_spec in Hd; lia).
    assert (NoA : forall v, ~ In v as_).
    { intros v Hv. destruct (B1 v Hv) as [F1 F2].
      pose proof (deg_bound _ _ _ _ _ C (proj1 (Rt v (or_introl Hv)))) as F3.
      rewrite (Md _ F3 ltac:(lia)) in F1. apply (NN v); [apply Rt; left; exact Hv | auto]. }
    split; [|reflexivity]. constructor.
    + exact C.
    + intros v Hv. destruct (Rp v Hv) as [F|[F|F]]; [right; exact F | destruct (NoA v F) | left].
      apply Rt. right. exact F.
    + intros i Hi. destruct (Z_lt_le_dec (φ md) (φ i)) as [F|F]; [apply Md; assumption | apply Lo; lia].
    + exists Lr. split; [exact NL|split; [|exact Rr]]. intros v. split.
      * intros Hv. apply Rt. right. exact Hv.
      * intros [Hv1 Hv2]. destruct (Rp v Hv1) as [F|[F|F]]; [rewrite Hv2 in F; destruct (NN _ F eq_refl) | destruct (NoA v F) | exact F].
Qed.

Lemma core_rem_root : forall h N ns ex z, core h N ns ex -> In z ns -> (hpar h).[z] = nil ->
  core h N (rem z ns) ex.
Proof.
  intros h N ns ex z C Hz Pz.
  assert (NN : forall v, In v ns -> v <> nil) by (intros v Hv; exact (node_not_nil _ _ _ _ _ C Hv)).
  pose proof C as [C1 C2 C3 C4 C5 [ht C6]].
  constructor; [exact C1 | apply rem_NoDup; exact C2 | | | |].
  - intros v Hv. apply rem_In in Hv. apply C3. tauto.
  - intros p Hp. apply rem_In in Hp. destruct Hp as [Hp _].
    destruct (C4 p Hp) as [[D1 D2] | (l & Hr & Hnd & Hc & Hd & Hm)].
    + left. split; [exact D1|]. intros v Hv. apply rem_In in Hv. apply D2. tauto.
    + right. exists l. split; [exact Hr|split; [exact Hnd|split; [exact Hc|split; [exact Hd|]]]].
      intros v. rewrite Hm, rem_In. split; [|tauto].
      intros [H1 H2]. split; [split; [exact H1|] | exact H2].
      intro E. subst v. rewrite Pz in H2. exact (NN p Hp (eq_sym H2)).
  - intros v Hv Hne Hpv. apply rem_In in Hv. apply rem_In in Hpv. apply C5; tauto.
  - exists ht. intros v Hv Hpv. apply rem_In in Hv. apply rem_In in Hpv. apply C6; tauto.
Qed.

(* EXTRACT-MIN *)
Lemma extract_spec : forall h N ns, HI h N ns nil nil -> ns <> [] ->
  In (snd (fh_extract h)) ns /\
  (forall v, In v ns -> (kv h (snd (fh_extract h)) <= kv h v)%Z) /\
  HI (fst (fh_extract h)) N (rem (snd (fh_extract h)) ns) nil nil /\
  hkey (fst (fh_extract h)) = hkey h.
Proof.
  intros h N ns HI0 Hne.
  pose proof HI0 as [C Hp Hbuf Hro].
  pose proof (co_len _ _ _ _ C) as Hl. pose proof Hl as (LK & LP & LC & LL & LR & LD & LM & LB).
  assert (NN : forall v, In v ns -> v <> nil) by (intros v Hv; exact (node_not_nil _ _ _ _ _ C Hv)).
  destruct ns as [| v0 ns0] eqn:Ens; [congruence|]. rewrite <- Ens in *.
  destruct (HI_min _ _ _ HI0 v0 ltac:(rewrite Ens; left; reflexivity)) as (Hz & Pz & _).
  set (z := hmin h) in *.
  assert (Hmin : forall v, In v ns -> (kv h z <= kv h v)%Z) by (intros v Hv; apply (HI_min _ _ _ HI0 v Hv)).
  assert (Bz : ((φ z) < (φ N))%Z) by (apply (co_range _ _ _ _ C); exact Hz).
  pose proof (len_bound ns N (co_nodup _ _ _ _ C) (co_range _ _ _ _ C)) as Hns.
  (* the root ring around z *)
  destruct (roots_bound _ _ _ _ _ C Hro) as (Lr & NL & Hm & Hrr & HbL).
  destruct Hrr as [[E _] | (Hr & HzL & _)]; [exfalso; exact (NN z Hz E)|].
  destruct (ring_at _ _ _ _ Hr HzL) as (t & Hrt & Hpt).
  assert (NDzt : NoDup (z :: t)) by (apply (Permutation_NoDup Hpt); exact NL).
  apply ring_cons in Hrt. destruct Hrt as (Rz & Rt & _ & _).
  apply NoDup_cons_iff in NDzt. destruct NDzt as [Hzt NDt].
  assert (Ht : forall v, In v t -> In v ns /\ (hpar h).[v] = nil /\ v <> z).
  { intros v Hv. split; [|split].
    - apply Hm. apply (Permutation_in _ (Permutation_sym Hpt)). right. exact Hv.
    - apply Hm. apply (Permutation_in _ (Permutation_sym Hpt)). right. exact Hv.
    - intro E. subst v. contradiction. }
  (* the children of z *)
  assert (HK : exists K, NoDup K /\ (forall v, In v K <-> In v ns /\ (hpar h).[v] = z) /\
     (((hdeg h).[z] = 0 /\ K = []) \/
      (exists t2, (hdeg h).[z] <> 0 /\ K = (hchd h).[z] :: t2 /\
         rseq (hrgt h) t2 (hchd h).[z] /\ (hrgt h).[(hchd h).[z]] = hd (hchd h).[z] t2 /\
         ~ In (hchd h).[z] t2))).
  { destruct (co_kids _ _ _ _ C z Hz) as [[D1 D2] | (l & Hrl & Hnd & Hc & Hd & Hml)].
    - exists []. split; [constructor|]. split; [|left; split; [exact D1 | reflexivity]].
      intros v. split; [intros []|]. intros [H1 H2]. exact (D2 v H1 H2).
    - destruct (ring_at _ _ _ _ Hrl Hc) as (t2 & Hrt2 & Hpt2).
      exists ((hchd h).[z] :: t2). split; [apply (Permutation_NoDup Hpt2); exact Hnd|].
      split; [intros v; rewrite <- Hml; split; apply Permutation_in; [apply Permutation_sym|]; exact Hpt2|].
      right. exists t2. apply ring_cons in Hrt2. destruct Hrt2 as (Rc & Rt2 & _ & _).
      split; [|split; [reflexivity|split; [exact Rt2|split; [exact Rc|]]]].
      + intro E. rewrite E in Hd. change (φ 0) with 0%Z in Hd. destruct l; [destruct Hrl|cbn in Hd; lia].
      + pose proof (Permutation_NoDup Hpt2 Hnd) as F. apply NoDup_cons_iff in F. tauto. }
  destruct HK as (K & NK & HmK & HK).
  assert (HKz : forall v, In v K -> In v ns /\ (hpar h).[v] = z /\ v <> z).
  { intros v Hv. apply HmK in Hv. destruct Hv as [H1 H2]. split; [exact H1|split; [exact H2|]].
    intro E. rewrite E, Pz in H2. exact (NN z Hz (eq_sym H2)). }
  set (ns' := rem z ns).
  assert (Hlen : forall l, NoDup l -> (forall v, In v l -> In v ns') ->
            (Z.of_nat (List.length l) <= (φ (PArray.length (hbuf h))))%Z).
  { intros l Hnd Hi. rewrite LB.
    pose proof (NoDup_incl_length Hnd (fun v Hv => proj1 (proj1 (rem_In z ns v) (Hi v Hv)))). lia. }
  (* consolidation starts *)
  assert (CI0 : CI (s_min h nil) N ns' [] (t ++ K) 0).
  { constructor; sx.
    - apply (core_frame h); [| apply lens_min, Hl | intros; sx; tauto | intros; sx; tauto].
      apply core_rem_root; assumption.
    - intros v Hv. apply rem_In in Hv. destruct Hv as [Hv Hvz].
      destruct (Hp v Hv) as [P|P].
      + right; right. apply in_or_app. left.
        assert (In v Lr) by (apply Hm; tauto).
        apply (Permutation_in _ Hpt) in H. destruct H as [E|H]; [exfalso; apply Hvz; symmetry; exact E | exact H].
      + destruct (Uint63.eq_dec (hpar h).[v] z) as [E|E].
        * right; right. apply in_or_app. right. apply HmK. tauto.
        * left. apply rem_In. tauto.
    - intros v [[]|Hv]. apply in_app_or in Hv. destruct Hv as [Hv|Hv].
      + destruct (Ht v Hv) as (H1 & H2 & H3). split; [apply rem_In; tauto|].
        rewrite H2. intro F. apply rem_In in F. exact (NN _ (proj1 F) eq_refl).
      + destruct (HKz v Hv) as (H1 & H2 & H3). split; [apply rem_In; tauto|].
        rewrite H2. intro F. apply rem_In in F. tauto.
    - constructor.
    - apply NoDup_app; [exact NDt | exact NK |]. intros v Hv F.
      destruct (Ht v Hv) as (_ & H2 & _). destruct (HKz v F) as (_ & H3 & _).
      rewrite H2 in H3. exact (NN z Hz (eq_sym H3)).
    - intros v [].
    - intros v [].
    - intros v [].
    - intros i Hi. left. apply Hbuf. exact Hi.
    - intros i Hi _. apply Hbuf. exact Hi.
    - change (φ 0) with 0%Z. pose proof (to_Z_bounded z). lia. }
  unfold fh_extract. cbv zeta. fold z. cbn [fst snd].
  split; [exact Hz|]. split; [exact Hmin|].
  change (hrgt (s_min h nil)).[z] with (hrgt h).[z]. rewrite (Rz : (hrgt h).[z] = hd z t).
  destruct (walk_spec _ (PArray.length (hbuf h)) (Zwf_well_founded 0 _) (s_min h nil) N ns' [] t K z 0
              eq_refl CI0 Rt Hzt (Hlen t NDt (fun v Hv => proj2 (rem_In z ns v) (conj (proj1 (Ht v Hv)) (proj2 (proj2 (Ht v Hv)))))))
    as ((as1 & HC1) & K1 & M1 & R1).
  set (r1 := walk (s_min h nil) (hd z t) z 0 (PArray.length (hbuf h)) _) in *.
  assert (Fin : forall r2 as3, CI (fst r2) N ns' as3 [] (snd r2) -> hmin (fst r2) = nil ->
            hkey (fst r2) = hkey h ->
            forall H3, HI (rebuild (fst r2) 0 (snd r2 + 1) H3) N (rem z ns) nil nil /\
                       hkey (rebuild (fst r2) 0 (snd r2 + 1) H3) = hkey h).
  { intros r2 as3 [C3 Cp3 Ct3 NA3 NP3 Dis3 Ap3 B13 B23 Md3 MdN3] M3 K3 H3.
    destruct (rebuild_spec N (snd r2) _ 0 H3 (fst r2) ns' as3 [] eq_refl) as [HI4 K4];
      [| split; [exact HI4 | rewrite K4; exact K3]].
    constructor; try assumption.
    - intros v [Hv|[]]. split; [apply Ct3; left; exact Hv | apply Ap3; exact Hv].
    - intros v Hv. split; [apply B13; exact Hv|]. change (φ 0) with 0%Z. apply to_Z_bounded.
    - intros i Hi. change (φ 0) with 0%Z in Hi. pose proof (to_Z_bounded i). lia.
    - change (φ 0) with 0%Z. pose proof (to_Z_bounded (snd r2)). lia.
    - left. split; [exact M3 | reflexivity]. }
  destruct HK as [[Dz EK] | (t2 & Dz & EK & Rt2 & Rc & Hct2)].
  - rewrite Dz. cbn. subst K. rewrite app_nil_r in *.
    apply (Fin r1 as1 HC1); [rewrite M1; reflexivity | exact K1].
  - destruct ((hdeg h).[z] =? 0) eqn:E0; [apply eqb_spec in E0; contradiction|]. cbv zeta.
    subst K.
    rewrite R1 by (left; reflexivity). change (hrgt (s_min h nil)) with (hrgt h). rewrite Rc.
    destruct (proc_spec (fst r1) N ns' as1 (hchd h).[z] t2 (snd r1) HC1) as ((as2 & HC2) & K2 & M2 & R2).
    assert (Rt2' : rseq (hrgt (fst (proc (fst r1) (hchd h).[z] (snd r1)))) t2 (hchd h).[z]).
    { apply (rseq_frame (hrgt h)); [exact Rt2|]. intros i Hi. rewrite R2 by exact Hi. apply R1. right. exact Hi. }
    rewrite <- (app_nil_r t2) in HC2.
    destruct (walk_spec _ (PArray.length (hbuf h)) (Zwf_well_founded 0 _) _ N ns' as2 t2 [] (hchd h).[z] _
                eq_refl HC2 Rt2' Hct2
                (Hlen t2 ltac:(apply NoDup_cons_iff in NK; tauto)
                   (fun v Hv => proj2 (rem_In z ns v) (conj (proj1 (HKz v (or_intror Hv))) (proj2 (proj2 (HKz v (or_intror Hv))))))))
      as ((as3 & HC3) & K3 & M3 & _).
    apply (Fin _ as3 HC3); [rewrite M3, M2, M1; reflexivity | rewrite K3, K2, K1; reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(* The state graph and the trips of the spec                           *)
(* ------------------------------------------------------------------ *)

Section States.
Open Scope N_scope.

Variables (n : N) (p u v d : list N) (cap g : N).
Hypothesis Hends : forall j, j < len u -> Prelude.get u j < n /\ Prelude.get v j < n.

(* state x * (cap + 1) + f: city x, f units of fuel *)
Definition sedge (a b w : N) : Prop :=
  exists x f, x < n /\ f <= cap /\ a = x * (cap + 1) + f /\
    ((f < cap /\ b = a + 1 /\ w = Prelude.get p x) \/
     (exists y l, road u v d x y l /\ l <= f /\ b = y * (cap + 1) + (f - l) /\ w = 0)).

Inductive spath : N -> N -> N -> Prop :=
| sp_nil : forall a, spath a a 0
| sp_cons : forall a b c w k, sedge a b w -> spath b c k -> spath a c (w + k).

Lemma spath_snoc : forall a b k, spath a b k -> forall c w, sedge b c w -> spath a c (k + w).
Proof.
  intros a b k H. induction H as [a | a b c w0 k H1 H2 IH]; intros c' w Hs.
  - replace (0 + w) with (w + 0) by lia. apply sp_cons with c'; [exact Hs | apply sp_nil].
  - replace (w0 + k + w) with (w0 + (k + w)) by lia. apply sp_cons with b; [exact H1 | apply IH; exact Hs].
Qed.

Lemma spath_app : forall a b k1, spath a b k1 -> forall c k2, spath b c k2 -> spath a c (k1 + k2).
Proof.
  intros a b k1 H. induction H as [a | a b c0 w k H1 H2 IH]; intros c k2 H'.
  - exact H'.
  - replace (w + k + k2) with (w + (k + k2)) by lia. apply sp_cons with b; [exact H1 | apply IH; exact H'].
Qed.

Lemma road_ends : forall x y l, road u v d x y l -> x < n /\ y < n.
Proof.
  intros x y l (j & Hj & Hxy & _). destruct (Hends j Hj). destruct Hxy as [[<- <-]|[<- <-]]; tauto.
Qed.

Lemma decode : forall x f x' f', x * (cap + 1) + f = x' * (cap + 1) + f' ->
  f <= cap -> f' <= cap -> x = x' /\ f = f'.
Proof. intros x f x' f' E H1 H2. assert (x = x') by nia. subst. lia. Qed.

Lemma buys : forall x f b, x < n -> f + b <= cap ->
  spath (x * (cap + 1) + f) (x * (cap + 1) + (f + b)) (Prelude.get p x * b).
Proof.
  intros x f b Hx. induction b as [| b IH] using N.peano_ind; intros Hb.
  - rewrite N.add_0_r, N.mul_0_r. apply sp_nil.
  - replace (Prelude.get p x * N.succ b) with (Prelude.get p x * b + Prelude.get p x) by lia.
    apply spath_snoc with (x * (cap + 1) + (f + b)); [apply IH; lia|].
    exists x, (f + b). split; [exact Hx|]. split; [lia|]. split; [reflexivity|].
    left. split; [lia|]. split; [lia | reflexivity].
Qed.

(* A trip is a path of the state graph to a state of the goal city. *)
Lemma trip_path : forall x f k, trip p u v d cap g x f k -> x < n -> f <= cap ->
  exists f', f' <= cap /\ spath (x * (cap + 1) + f) (g * (cap + 1) + f') k.
Proof.
  intros x f k H. induction H as [f | x f b y l k Hfb Hr Hl Ht IH]; intros Hx Hf.
  - exists f. split; [exact Hf | apply sp_nil].
  - destruct (road_ends _ _ _ Hr) as [_ Hy].
    destruct (IH Hy ltac:(lia)) as (f' & Hf' & Hp). exists f'. split; [exact Hf'|].
    replace (Prelude.get p x * b + k) with (Prelude.get p x * b + (0 + k)) by lia.
    apply spath_app with (x * (cap + 1) + (f + b)); [apply buys; assumption|].
    apply sp_cons with (y * (cap + 1) + (f + b - l)); [|exact Hp].
    exists x, (f + b). split; [exact Hx|]. split; [exact Hfb|]. split; [reflexivity|].
    right. exists y, l. tauto.
Qed.

Lemma buy_back : forall x f k, trip p u v d cap g x (f + 1) k -> f + 1 <= cap ->
  exists k', k' <= Prelude.get p x + k /\ trip p u v d cap g x f k'.
Proof.
  intros x f k H. remember (f + 1) as f1 eqn:Ef. destruct H as [f0 | x0 f0 b y l k0 Hfb Hr Hl Ht]; intros Hc.
  - exists 0. split; [lia | apply trip_arrive].
  - exists (Prelude.get p x0 * (b + 1) + k0). split; [lia|].
    apply trip_drive with y l; [lia | exact Hr | lia |].
    replace (f + (b + 1) - l) with (f0 + b - l) by lia. exact Ht.
Qed.

(* A path to a state of the goal city gives a trip no dearer. *)
Lemma path_trip : forall a t k, spath a t k ->
  forall x f, a = x * (cap + 1) + f -> x < n -> f <= cap ->
  (exists f', f' <= cap /\ t = g * (cap + 1) + f') ->
  exists k', k' <= k /\ trip p u v d cap g x f k'.
Proof.
  intros a t k H. induction H as [a | a b c w k Hs Hp IH]; intros x f Ea Hx Hf (f' & Hf' & Et).
  - subst. destruct (decode _ _ _ _ Et Hf Hf') as [-> _]. exists 0. split; [lia | apply trip_arrive].
  - destruct Hs as (x0 & f0 & Hx0 & Hf0 & Ea0 & [(Hc & Eb & Ew) | (y & l & Hr & Hl & Eb & Ew)]);
      rewrite Ea in Ea0; destruct (decode _ _ _ _ Ea0 Hf Hf0) as [<- <-].
    + destruct (IH x (f + 1) ltac:(subst; lia) Hx ltac:(lia) (ex_intro _ f' (conj Hf' Et))) as (k1 & Hk1 & Ht1).
      destruct (buy_back x f k1 Ht1 ltac:(lia)) as (k2 & Hk2 & Ht2).
      exists k2. split; [subst; lia | exact Ht2].
    + destruct (road_ends _ _ _ Hr) as [_ Hy].
      destruct (IH y (f - l) Eb Hy ltac:(lia) (ex_intro _ f' (conj Hf' Et))) as (k1 & Hk1 & Ht1).
      exists (Prelude.get p x * 0 + k1). split; [subst; lia|].
      apply trip_drive with y l; [lia | exact Hr | lia |]. rewrite N.add_0_r. exact Ht1.
Qed.

(* Shortest paths to the goal states answer the query. *)
Lemma answer_of_paths : forall s (r : option N), s < n ->
  (match r with
   | Some k => (exists f', f' <= cap /\ spath (s * (cap + 1)) (g * (cap + 1) + f') k) /\
               (forall f' k', f' <= cap -> spath (s * (cap + 1)) (g * (cap + 1) + f') k' -> k <= k')
   | None => forall f' k', f' <= cap -> ~ spath (s * (cap + 1)) (g * (cap + 1) + f') k'
   end) ->
  answer p u v d cap s g r.
Proof.
  intros s r Hs. destruct r as [k|]; cbn.
  - intros [(f' & Hf' & Hp) Hmin].
    destruct (path_trip _ _ _ Hp s 0 ltac:(lia) Hs ltac:(lia) (ex_intro _ f' (conj Hf' eq_refl)))
      as (k1 & Hk1 & Ht1).
    destruct (trip_path _ _ _ Ht1 Hs ltac:(lia)) as (f2 & Hf2 & Hp2).
    rewrite N.add_0_r in Hp2. pose proof (Hmin _ _ Hf2 Hp2).
    split; [replace k with k1 by lia; exact Ht1|].
    intros k' Ht'. destruct (trip_path _ _ _ Ht' Hs ltac:(lia)) as (f3 & Hf3 & Hp3).
    rewrite N.add_0_r in Hp3. exact (Hmin _ _ Hf3 Hp3).
  - intros Hno (k & Ht). destruct (trip_path _ _ _ Ht Hs ltac:(lia)) as (f3 & Hf3 & Hp3).
    rewrite N.add_0_r in Hp3. exact (Hno _ _ Hf3 Hp3).
Qed.

End States.

(* ------------------------------------------------------------------ *)
(* Dijkstra                                                            *)
(* ------------------------------------------------------------------ *)

Definition toN (i : int) : N := Z.to_N (φ i).
Definition kN (h : fh) (x : int) : N := toN (hkey h).[x].

Lemma toN_inj : forall a b, toN a = toN b -> a = b.
Proof.
  intros a b E. unfold toN in E. apply to_Z_inj.
  pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). lia.
Qed.

Lemma toN_Z : forall a, Z.of_N (toN a) = (φ a).
Proof. intros a. unfold toN. pose proof (to_Z_bounded a). lia. Qed.

Lemma of_N_toN : forall b : N, (b < 9223372036854775808)%N -> toN (of_Z (Z.of_N b)) = b.
Proof.
  intros b H. unfold toN. rewrite of_Z_spec. rewrite Z.mod_small; [lia|].
  rewrite wB_val. lia.
Qed.

(* the half-edges of a forward-star list *)
Fixpoint hchain (nxt : array int) (e : int) (l : list int) : Prop :=
  match l with
  | [] => e = 0
  | a :: t => e = a /\ e <> 0 /\ ((φ (nxt.[e])) < (φ e))%Z /\ hchain nxt nxt.[e] t
  end.

Definition hsrc (U V : array int) (e : int) : int :=
  if (e - 1) mod 2 =? 0 then U.[(e - 1) / 2] else V.[(e - 1) / 2].
Definition hdst (U V : array int) (e : int) : int :=
  if (e - 1) mod 2 =? 0 then V.[(e - 1) / 2] else U.[(e - 1) / 2].

Definition handled (h : fh) (D ns : list int) (a : int) (b w : N) : Prop :=
  exists x : int, toN x = b /\ (In x D \/ (In x ns /\ (kN h x <= kN h a + w)%N)).

Lemma kv_kN : forall h a b, (kv h a <= kv h b)%Z -> (kN h a <= kN h b)%N.
Proof. unfold kv, kN, toN. intros. lia. Qed.

Lemma div_state : forall a c f, (f < c)%N -> ((a * c + f) / c = a)%N.
Proof. intros a c f H. rewrite N.div_add_l by lia. rewrite N.div_small by lia. lia. Qed.

Lemma he_idx : forall j : int, ((φ j) < 10000)%Z ->
  ((2 * j + 1) - 1) mod 2 = 0 /\ ((2 * j + 1) - 1) / 2 = j /\
  ((2 * j + 2) - 1) mod 2 = 1 /\ ((2 * j + 2) - 1) / 2 = j /\
  (φ (2 * j + 1)) = (2 * (φ j) + 1)%Z /\ (φ (2 * j + 2)) = (2 * (φ j) + 2)%Z.
Proof.
  intros j H. pose proof (to_Z_bounded j).
  repeat split; try (apply to_Z_inj); change (φ 0) with 0%Z; change (φ 1) with 1%Z; sia.
Qed.

Section Dijkstra.

Variables (n : N) (p u v d : list N) (cap g sN : N).
Local Notation SE := (sedge n p u v d cap).
Local Notation SP := (spath n p u v d cap).
Hypothesis Hends : forall j, (j < len u)%N -> (Prelude.get u j < n /\ Prelude.get v j < n)%N.
Hypothesis Hp100 : forall x, (x < n)%N -> (Prelude.get p x <= 100)%N.
Hypothesis Hcap : (cap <= 100)%N.
Hypothesis Hn : (n <= 1000)%N.
Hypothesis Hm : (len u <= 10000)%N.
Hypothesis Hlv : len v = len u.
Hypothesis Hld : len d = len u.
Hypothesis Hs : (sN < n)%N.
Hypothesis Hgn : (g < n)%N.

Variables (P U V Dl head nxt : array int) (capi Ci Ni gi srci : int).
Hypothesis Hcapi : toN capi = cap.
Hypothesis HCi : Ci = capi + 1.
Hypothesis HNi : toN Ni = (n * (cap + 1))%N.
Hypothesis Hgi : toN gi = g.
Hypothesis Hsrc : toN srci = (sN * (cap + 1))%N.
Hypothesis HP : forall x : int, (toN x < n)%N -> toN P.[x] = Prelude.get p (toN x).
Hypothesis HU : forall j : int, (toN j < len u)%N -> toN U.[j] = Prelude.get u (toN j).
Hypothesis HV : forall j : int, (toN j < len u)%N -> toN V.[j] = Prelude.get v (toN j).
Hypothesis HD : forall j : int, (toN j < len u)%N -> toN Dl.[j] = Prelude.get d (toN j).
Hypothesis HFS : forall x : int, (toN x < n)%N -> exists l, hchain nxt head.[x] l /\
  forall e, In e l <-> ((1 <= (φ e) <= 2 * Z.of_N (len u))%Z /\ hsrc U V e = x).

Lemma HCi' : toN Ci = (cap + 1)%N.
Proof.
  rewrite HCi. unfold toN in *. pose proof (to_Z_bounded capi).
  rewrite add_spec, Z.mod_small; change (φ 1) with 1%Z; [lia|]. rewrite wB_val. lia.
Qed.

Lemma HNi_small : ((φ Ni) <= 101000)%Z.
Proof. rewrite <- toN_Z, HNi. nia. Qed.

Record DIx (h : fh) (st : array int) (D ns : list int) (z : int) (Q : N -> N -> Prop) : Prop := {
  di_heap : HI h Ni ns nil nil;
  di_stlen : PArray.length st = Ni;
  di_st : forall x, ((φ x) < (φ Ni))%Z ->
     (st.[x] = 2 <-> In x D) /\ (st.[x] = 1 <-> In x ns) /\ (st.[x] = 0 \/ st.[x] = 1 \/ st.[x] = 2);
  di_Dnd : NoDup D;
  di_Drange : forall x, In x D -> ((φ x) < (φ Ni))%Z;
  di_reach : forall x, In x D \/ In x ns -> SP (toN srci) (toN x) (kN h x);
  di_min : forall x, In x D -> forall k, SP (toN srci) (toN x) k -> (kN h x <= k)%N;
  di_edge : forall a, In a D -> forall b w, SE (toN a) b w -> handled h D ns a b w \/ (a = z /\ Q b w);
  di_src : In srci D \/ (In srci ns /\ kN h srci = 0%N);
  di_bound : forall x, In x D \/ In x ns -> (kN h x <= 100 * N.of_nat (List.length D))%N;
  di_goal : forall x, In x D -> (toN x / (cap + 1) <> g)%N
}.

Lemma sedge_range : forall a b w, SE a b w -> (a < toN Ni)%N /\ (b < toN Ni)%N /\ (w <= 100)%N.
Proof.
  intros a b w (x & f & Hx & Hf & Ea & [(Hc & Eb & Ew) | (y & l & Hr & Hl & Eb & Ew)]); rewrite HNi.
  - subst. pose proof (Hp100 x Hx). nia.
  - destruct (road_ends n u v d Hends _ _ _ Hr) as [_ Hy]. subst. nia.
Qed.

(* No path leaves the done set but through the heap. *)
Lemma frontier : forall h st D ns z, DIx h st D ns z (fun _ _ => False) ->
  forall t k, SP (toN srci) t k -> (forall x, toN x = t -> ~ In x D) ->
  exists y, In y ns /\ (kN h y <= k)%N.
Proof.
  intros h st D ns z HD0 t k Hp Ht.
  assert (G : forall a t k, SP a t k -> forall xa, toN xa = a -> In xa D ->
            (forall x, toN x = t -> ~ In x D) -> exists y, In y ns /\ (kN h y <= kN h xa + k)%N).
  { intros a t' k' H. induction H as [a | a b c w k1 Hs' Hp' IH]; intros xa Ea Hxa Hn'.
    - exfalso. exact (Hn' xa Ea Hxa).
    - destruct (di_edge _ _ _ _ _ _ HD0 xa Hxa b w ltac:(rewrite Ea; exact Hs')) as [(x' & Ex' & [Hx'|[Hx' Hk]]) | [_ []]].
      + destruct (IH x' Ex' Hx' Hn') as (y & Hy & Hky). exists y. split; [exact Hy|].
        assert (SP (toN srci) b (kN h xa + w)).
        { apply spath_snoc with a; [rewrite <- Ea; apply (di_reach _ _ _ _ _ _ HD0); left; exact Hxa | exact Hs']. }
        pose proof (di_min _ _ _ _ _ _ HD0 x' Hx' (kN h xa + w)%N ltac:(rewrite Ex'; assumption)). lia.
      + exists x'. split; [exact Hx'|]. lia. }
  destruct (di_src _ _ _ _ _ _ HD0) as [Hs'|[Hs' Hk]].
  - destruct (G _ _ _ Hp srci eq_refl Hs' Ht) as (y & Hy & Hky). exists y. split; [exact Hy|].
    pose proof (di_min _ _ _ _ _ _ HD0 srci Hs' 0%N (sp_nil _ _ _ _ _ _ _)). lia.
  - exists srci. split; [exact Hs'|]. lia.
Qed.

Lemma i01 : (0:int) <> 1.
Proof. intro E. pose proof (eq_refl : (0 =? 1) = false) as F. rewrite E, eqb_refl in F. discriminate. Qed.
Lemma i02 : (0:int) <> 2.
Proof. intro E. pose proof (eq_refl : (0 =? 2) = false) as F. rewrite E, eqb_refl in F. discriminate. Qed.
Lemma i12 : (1:int) <> 2.
Proof. intro E. pose proof (eq_refl : (1 =? 2) = false) as F. rewrite E, eqb_refl in F. discriminate. Qed.

Lemma DIx_set : forall h st D ns z Q h' st' ns' x nk w,
  DIx h st D ns z Q -> In z D -> (kN h z + 100 <= 100 * N.of_nat (List.length D))%N ->
  ((φ x) < (φ Ni))%Z -> ~ In x D -> SE (toN z) (toN x) w -> toN nk = (kN h z + w)%N ->
  (In x ns -> (toN nk <= kN h x)%N) ->
  HI h' Ni ns' nil nil -> hkey h' = (hkey h).[x <- nk] ->
  (forall y, In y ns' <-> y = x \/ In y ns) ->
  PArray.length st' = Ni -> (forall y, ((φ y) < (φ Ni))%Z -> st'.[y] = if y =? x then 1 else st.[y]) ->
  DIx h' st' D ns' z Q /\ handled h' D ns' z (toN x) w /\ (hkey h').[z] = (hkey h).[z].
Proof.
  intros h st D ns z Q h' st' ns' x nk w HD0 Hz Bz Bx HxD Hse Hnk Hdec HI' K' Hns' L' S'.
  pose proof HD0 as [Hh Hl Hst Hnd Hr Hre Hmi He Hsr Hbo Hgo].
  pose proof (co_len _ _ _ _ (hi_core _ _ _ _ _ Hh)) as (LK & _).
  assert (Kx : kN h' x = toN nk) by (unfold kN; rewrite K', gss by (rewrite LK; exact Bx); reflexivity).
  assert (Ko : forall y, y <> x -> kN h' y = kN h y) by (intros y Hy; unfold kN; rewrite K', gso by exact Hy; reflexivity).
  assert (Hzx : z <> x) by (intro E; subst; contradiction).
  pose proof (sedge_range _ _ _ Hse) as (_ & _ & Hw).
  split; [|split; [|rewrite K', gso by exact Hzx; reflexivity]].
  - constructor; try assumption.
    + intros y Hy. rewrite (S' y Hy). destruct (Uint63.eq_dec y x) as [E|E].
      * subst y. rewrite eqb_refl. split; [split; [intro F; exfalso; exact (i12 F) | intro F; contradiction]|].
        split; [split; [intros _; apply Hns'; left; reflexivity | reflexivity]|]. right; left; reflexivity.
      * replace (y =? x) with false by (symmetry; apply eqb_false_spec; exact E).
        destruct (Hst y Hy) as (S2 & S1 & S0). split; [exact S2|split; [|exact S0]].
        rewrite S1, Hns'. split; [intros F; right; exact F | intros [F|F]; [contradiction | exact F]].
    + intros y Hy. destruct (Uint63.eq_dec y x) as [E|E].
      * subst y. rewrite Kx, Hnk. apply spath_snoc with (toN z); [apply Hre; left; exact Hz | exact Hse].
      * rewrite Ko by exact E. apply Hre. destruct Hy as [Hy|Hy]; [left; exact Hy|].
        apply Hns' in Hy. destruct Hy as [F|F]; [contradiction | right; exact F].
    + intros y Hy. rewrite Ko by (intro E; subst; contradiction). apply Hmi. exact Hy.
    + intros a Ha b w' Hs'. destruct (He a Ha b w' Hs') as [(x' & Ex' & Hx')|F]; [left|right; exact F].
      exists x'. split; [exact Ex'|]. destruct Hx' as [Hx'|[Hx' Hk]]; [left; exact Hx'|right].
      split; [apply Hns'; right; exact Hx'|].
      rewrite (Ko a) by (intro E; subst; contradiction).
      destruct (Uint63.eq_dec x' x) as [E|E].
      * subst x'. rewrite Kx. pose proof (Hdec Hx'). lia.
      * rewrite Ko by exact E. exact Hk.
    + destruct Hsr as [F|[F1 F2]]; [left; exact F|right]. split; [apply Hns'; right; exact F1|].
      destruct (Uint63.eq_dec srci x) as [E|E].
      * subst. rewrite Kx. pose proof (Hdec F1). lia.
      * rewrite Ko by exact E. exact F2.
    + intros y Hy. destruct (Uint63.eq_dec y x) as [E|E].
      * subst y. rewrite Kx, Hnk. lia.
      * rewrite Ko by exact E. apply Hbo. destruct Hy as [Hy|Hy]; [left; exact Hy|].
        apply Hns' in Hy. destruct Hy as [F|F]; [contradiction | right; exact F].
  - exists x. split; [reflexivity|]. right. split; [apply Hns'; left; reflexivity|].
    rewrite Kx, (Ko z Hzx). lia.
Qed.

Lemma relax_spec : forall h st D ns z Q x nk w,
  DIx h st D ns z Q -> In z D -> (kN h z + 100 <= 100 * N.of_nat (List.length D))%N ->
  ((φ x) < (φ Ni))%Z -> SE (toN z) (toN x) w -> toN nk = (kN h z + w)%N ->
  exists ns', DIx (fst (relax h st x nk)) (snd (relax h st x nk)) D ns' z Q /\
    handled (fst (relax h st x nk)) D ns' z (toN x) w /\
    (hkey (fst (relax h st x nk))).[z] = (hkey h).[z].
Proof.
  intros h st D ns z Q x nk w HD0 Hz Bz Bx Hse Hnk.
  pose proof HD0 as [Hh Hl Hst Hnd Hr Hre Hmi He Hsr Hbo Hgo].
  destruct (Hst x Bx) as (S2 & S1 & S0).
  unfold relax. cbv zeta.
  destruct (st.[x] =? 0) eqn:Z0.
  - pose proof (proj1 (eqb_spec _ _) Z0) as E0. cbn [fst snd].
    assert (HxD : ~ In x D) by (rewrite <- S2, E0; exact i02).
    assert (Hxn : ~ In x ns) by (rewrite <- S1, E0; exact i01).
    destruct (insert_spec h Ni ns x nk Hh Hxn Bx) as [HI' K'].
    exists (x :: ns). apply (DIx_set h st D ns z Q _ _ _ x nk w HD0 Hz Bz Bx HxD Hse Hnk
                               (fun F => False_ind _ (Hxn F)) HI' K').
    + intros y. cbn [In]. split; intros [F|F]; [left; exact (eq_sym F) | right; exact F | left; exact (eq_sym F) | right; exact F].
    + rewrite lset. exact Hl.
    + intros y Hy. destruct (Uint63.eq_dec y x) as [E|E].
      * subst. rewrite eqb_refl. apply gss. rewrite Hl. exact Bx.
      * replace (y =? x) with false by (symmetry; apply eqb_false_spec; exact E). apply gso. exact E.
  - destruct (st.[x] =? 1) eqn:Z1.
    + pose proof (proj1 (eqb_spec _ _) Z1) as E1.
      assert (HxD : ~ In x D) by (rewrite <- S2, E1; exact i12).
      assert (Hxn : In x ns) by (apply S1; exact E1).
      destruct (nk <? (hkey h).[x]) eqn:Ek; cbn [fst snd].
      * rewrite ltb_spec in Ek.
        destruct (decrease_spec h Ni ns x nk Hh Hxn ltac:(unfold kv; lia)) as [HI' K'].
        exists ns. apply (DIx_set h st D ns z Q _ _ _ x nk w HD0 Hz Bz Bx HxD Hse Hnk
                               (fun _ => ltac:(unfold kN, toN; lia)) HI' K').
        -- intros y. split; [intros F; right; exact F | intros [F|F]; [subst; exact Hxn | exact F]].
        -- exact Hl.
        -- intros y Hy. destruct (Uint63.eq_dec y x) as [E|E].
           ++ subst. rewrite eqb_refl. exact E1.
           ++ replace (y =? x) with false by (symmetry; apply eqb_false_spec; exact E). reflexivity.
      * rewrite <- Bool.not_true_iff_false, ltb_spec in Ek.
        exists ns. split; [exact HD0|split; [|reflexivity]].
        exists x. split; [reflexivity|]. right. split; [exact Hxn|].
        unfold kN, toN in *. lia.
    + destruct S0 as [F|[F|F]]; [apply eqb_false_spec in Z0; contradiction | apply eqb_false_spec in Z1; contradiction|].
      cbn [fst snd]. exists ns. split; [exact HD0|split; [|reflexivity]].
      exists x. split; [reflexivity|]. left. apply S2. exact F.
Qed.

Lemma DIx_weaken : forall h st D ns z Q Q', DIx h st D ns z Q ->
  (forall b w, SE (toN z) b w -> Q b w -> handled h D ns z b w \/ Q' b w) ->
  DIx h st D ns z Q'.
Proof.
  intros h st D ns z Q Q' [Hh Hl Hst Hnd Hr Hre Hmi He Hsr Hbo Hgo] HQ. constructor; try assumption.
  intros a Ha b w Hs'. destruct (He a Ha b w Hs') as [F|[E F]]; [left; exact F|].
  subst a. destruct (HQ b w Hs' F) as [G|G]; [left; exact G | right; split; [reflexivity | exact G]].
Qed.

Definition Qr (L : list int) (f : int) (b w : N) : Prop :=
  exists e', In e' L /\ (toN Dl.[(e' - 1) / 2] <= toN f)%N /\
    b = (toN (hdst U V e') * (cap + 1) + (toN f - toN Dl.[(e' - 1) / 2]))%N /\ w = 0%N.

Lemma edges_eq : forall C f kz hs e H, edges U V Dl nxt C f kz hs e H =
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
Proof. intros. destruct H. reflexivity. Qed.

(* the road of a half-edge *)
Lemma half_road : forall e x, (1 <= (φ e) <= 2 * Z.of_N (len u))%Z -> hsrc U V e = x ->
  (toN ((e - 1) / 2) < len u)%N /\
  road u v d (toN x) (toN (hdst U V e)) (toN Dl.[(e - 1) / 2]) /\ (toN (hdst U V e) < n)%N.
Proof.
  intros e x He Hx.
  assert (Hj : (toN ((e - 1) / 2) < len u)%N) by (unfold toN; sia).
  split; [exact Hj|].
  pose proof (Hends _ Hj) as [Hu Hv].
  unfold hsrc, hdst in *. destruct ((e - 1) mod 2 =? 0).
  - split; [|rewrite HV by exact Hj; exact Hv].
    exists (toN ((e - 1) / 2)). split; [exact Hj|]. split; [left; split|].
    + rewrite <- HU by exact Hj. rewrite Hx. reflexivity.
    + rewrite HV by exact Hj. reflexivity.
    + rewrite HD by exact Hj. reflexivity.
  - split; [|rewrite HU by exact Hj; exact Hu].
    exists (toN ((e - 1) / 2)). split; [exact Hj|]. split; [right; split|].
    + rewrite HU by exact Hj. reflexivity.
    + rewrite <- HV by exact Hj. rewrite Hx. reflexivity.
    + rewrite HD by exact Hj. reflexivity.
Qed.

Lemma state_val : forall y c f l : int, ((φ y) < 1000)%Z -> ((φ c) <= 101)%Z ->
  ((φ l) <= (φ f))%Z -> ((φ f) <= 100)%Z -> (φ (y * c + (f - l))) = ((φ y) * (φ c) + ((φ f) - (φ l)))%Z.
Proof.
  intros y c f l H1 H2 H3 H4.
  pose proof (to_Z_bounded l). pose proof (to_Z_bounded c). pose proof (to_Z_bounded y).
  assert (E1 : (φ (f - l)) = ((φ f) - (φ l))%Z) by (rewrite sub_spec; apply Z.mod_small; rewrite wB_val; lia).
  assert (E2 : (φ (y * c)) = ((φ y) * (φ c))%Z) by (rewrite mul_spec; apply Z.mod_small; rewrite wB_val; nia).
  rewrite add_spec, E1, E2. apply Z.mod_small. rewrite wB_val. nia.
Qed.

Lemma edges_spec : forall L e (H : Acc (Zwf 0) (φ e)) hs D ns z x f kz,
  hchain nxt e L ->
  (forall e', In e' L -> (1 <= (φ e') <= 2 * Z.of_N (len u))%Z /\ hsrc U V e' = x) ->
  toN z = (toN x * (cap + 1) + toN f)%N -> (toN x < n)%N -> (toN f <= cap)%N ->
  kz = (hkey (fst hs)).[z] ->
  DIx (fst hs) (snd hs) D ns z (Qr L f) -> In z D ->
  (kN (fst hs) z + 100 <= 100 * N.of_nat (List.length D))%N ->
  exists ns', DIx (fst (edges U V Dl nxt Ci f kz hs e H)) (snd (edges U V Dl nxt Ci f kz hs e H))
                  D ns' z (fun _ _ => False).
Proof.
  induction L as [| a L IH]; intros e H hs D ns z x f kz Hc HL Ez Hx Hf Hkz HD0 Hz Bz.
  - cbn [hchain] in Hc. subst e. rewrite edges_eq. rewrite eqb_refl. exists ns.
    apply (DIx_weaken _ _ _ _ _ _ _ HD0). intros b w _ (e' & [] & _).
  - cbn [hchain] in Hc. destruct Hc as (Ea & Hne & Hlt & Hc). subst a.
    rewrite edges_eq. destruct (e =? 0) eqn:E0; [apply eqb_spec in E0; contradiction|].
    cbv zeta.
    destruct (HL e (or_introl eq_refl)) as [He Hsx].
    destruct (half_road e x He Hsx) as (Hj & Hr & Hy).
    fold (hdst U V e).
    set (y := hdst U V e) in *. set (l := Dl.[(e - 1) / 2]) in *.
    assert (Hlt' : (nxt.[e] <? e) = true) by (apply ltb_spec; exact Hlt).
    destruct (bdec (nxt.[e] <? e)) as [Hb|Hb]; [| rewrite Hlt' in Hb; discriminate].
    pose proof HCi' as HC'.
    destruct (l <=? f) eqn:El.
    + rewrite leb_spec in El.
      assert (Hst : (toN (y * Ci + (f - l)) = toN y * (cap + 1) + (toN f - toN l))%N).
      { apply N2Z.inj. rewrite N2Z.inj_add, N2Z.inj_mul, N2Z.inj_sub by (unfold toN; lia).
        rewrite !toN_Z. rewrite <- HC', toN_Z.
        apply state_val; [rewrite <- toN_Z; lia | rewrite <- toN_Z, HC'; lia | exact El |
                          rewrite <- toN_Z; lia]. }
      assert (Bst : ((φ (y * Ci + (f - l))) < (φ Ni))%Z).
      { assert (Hm1 : ((toN y + 1) * (cap + 1) <= n * (cap + 1))%N) by (apply N.mul_le_mono_r; lia).
        rewrite <- !toN_Z, Hst, HNi. lia. }
      assert (Hse : SE (toN z) (toN (y * Ci + (f - l))) 0).
      { exists (toN x), (toN f). split; [exact Hx|]. split; [exact Hf|]. split; [exact Ez|].
        right. exists (toN y), (toN l). split; [exact Hr|]. split; [unfold toN; lia|]. split; [exact Hst | reflexivity]. }
      destruct (relax_spec (fst hs) (snd hs) D ns z (Qr (e :: L) f) _ kz 0 HD0 Hz Bz Bst Hse
                 ltac:(rewrite Hkz; unfold kN; lia)) as (ns1 & HD1 & Hh1 & Hk1).
      apply (IH _ _ _ D ns1 z x f kz Hc (fun e' He' => HL e' (or_intror He')) Ez Hx Hf
               ltac:(rewrite Hk1; exact Hkz)); [| exact Hz | unfold kN; rewrite Hk1; exact Bz].
      apply (DIx_weaken _ _ _ _ _ _ _ HD1). intros b w _ (e' & [E'|He'] & H1 & H2 & H3).
      * subst e'. left. subst b w. fold y l. rewrite <- Hst. exact Hh1.
      * right. exists e'. tauto.
    + rewrite <- Bool.not_true_iff_false, leb_spec in El.
      apply (IH _ _ _ D ns z x f kz Hc (fun e' He' => HL e' (or_intror He')) Ez Hx Hf Hkz); [| exact Hz | exact Bz].
      apply (DIx_weaken _ _ _ _ _ _ _ HD0). intros b w _ (e' & [E'|He'] & H1 & H2 & H3).
      * subst e'. exfalso. unfold toN in H1. fold l in H1. lia.
      * right. exists e'. tauto.
Qed.

Lemma drive_in : forall z x f L, toN z = (toN x * (cap + 1) + toN f)%N -> (toN x < n)%N ->
  (forall e, In e L <-> ((1 <= (φ e) <= 2 * Z.of_N (len u))%Z /\ hsrc U V e = x)) ->
  forall y l, road u v d (toN x) y l -> (l <= toN f)%N ->
  Qr L f (y * (cap + 1) + (toN f - l))%N 0%N.
Proof.
  intros z x f L Ez Hx HL y l (j & Hj & Hxy & El) Hl.
  set (ji := of_Z (Z.of_N j)).
  assert (Tj : toN ji = j) by (apply of_N_toN; lia).
  assert (Bj : ((φ ji) < 10000)%Z) by (rewrite <- toN_Z, Tj; lia).
  destruct (he_idx ji Bj) as (M1 & D1 & M2 & D2 & P1 & P2).
  assert (Hj' : (toN ji < len u)%N) by (rewrite Tj; exact Hj).
  destruct Hxy as [[Eu Ev]|[Eu Ev]].
  - exists (2 * ji + 1). split; [|split; [|split; [|reflexivity]]].
    + apply HL. split; [rewrite P1, <- toN_Z, Tj; lia|].
      unfold hsrc. rewrite M1, D1. cbn. apply toN_inj. rewrite HU by exact Hj'. rewrite Tj. exact Eu.
    + rewrite D1, HD by exact Hj'. rewrite Tj, <- El. exact Hl.
    + unfold hdst. rewrite M1, D1. cbn. rewrite HV, HD by exact Hj'. rewrite Tj, Ev, El. reflexivity.
  - exists (2 * ji + 2). split; [|split; [|split; [|reflexivity]]].
    + apply HL. split; [rewrite P2, <- toN_Z, Tj; lia|].
      unfold hsrc. rewrite M2, D2. cbn. apply toN_inj. rewrite HV by exact Hj'. rewrite Tj. exact Ev.
    + rewrite D2, HD by exact Hj'. rewrite Tj, <- El. exact Hl.
    + unfold hdst. rewrite M2, D2. cbn. rewrite HU, HD by exact Hj'. rewrite Tj, Eu, El. reflexivity.
Qed.

Lemma state_split : forall z : int, ((φ z) < (φ Ni))%Z ->
  toN z = (toN (z / Ci) * (cap + 1) + toN (z mod Ci))%N /\ (toN (z / Ci) < n)%N /\
  (toN (z mod Ci) <= cap)%N.
Proof.
  intros z Hz. pose proof HCi' as HC. pose proof HNi as HN.
  assert (EC : (φ Ci) = Z.of_N (cap + 1)) by (rewrite <- toN_Z, HC; reflexivity).
  assert (EN : (φ Ni) = Z.of_N (n * (cap + 1))) by (rewrite <- toN_Z, HN; reflexivity).
  unfold toN. rewrite div_spec, mod_spec, EC. rewrite EN in Hz.
  pose proof (to_Z_bounded z).
  assert (Q1 : ((φ z) / Z.of_N (cap + 1) < Z.of_N n)%Z) by (apply Z.div_lt_upper_bound; lia).
  pose proof (Z.div_mod (φ z) (Z.of_N (cap + 1)) ltac:(lia)).
  pose proof (Z.mod_pos_bound (φ z) (Z.of_N (cap + 1)) ltac:(lia)).
  pose proof (Z.div_pos (φ z) (Z.of_N (cap + 1)) ltac:(lia) ltac:(lia)).
  split; [|split]; lia.
Qed.

Lemma succ_small : forall z N : int, ((φ z) < (φ N))%Z -> ((φ N) <= 101000)%Z -> toN (z + 1) = (toN z + 1)%N.
Proof.
  intros z N H1 H2. unfold toN. rewrite add_spec. change (φ 1) with 1%Z. pose proof (to_Z_bounded z).
  rewrite Z.mod_small; [lia|]. rewrite wB_val. lia.
Qed.

Lemma add_small_N : forall a b : int, ((φ a) + (φ b) < 4611686018427387904)%Z ->
  toN (a + b) = (toN a + toN b)%N.
Proof.
  intros a b H. unfold toN. rewrite add_spec. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  rewrite Z.mod_small; [lia|]. rewrite wB_val. lia.
Qed.

Lemma expand_spec : forall h st D ns z, DIx h st D ns z (fun b w => SE (toN z) b w) -> In z D ->
  (kN h z + 100 <= 100 * N.of_nat (List.length D))%N ->
  exists ns', DIx (fst (expand P U V Dl head nxt Ci capi (h, st) z))
                  (snd (expand P U V Dl head nxt Ci capi (h, st) z)) D ns' z (fun _ _ => False).
Proof.
  intros h st D ns z HD0 Hz Bz.
  pose proof (di_Drange _ _ _ _ _ _ HD0 z Hz) as Bzi.
  destruct (state_split z Bzi) as (Ez & Hx & Hf).
  pose proof HCi' as HC.
  unfold expand. cbv zeta. cbn [fst snd].
  set (x := z / Ci) in *. set (f := z mod Ci) in *.
  destruct (HFS x Hx) as (L & Hc & HL).
  assert (HL' : forall e', In e' L -> (1 <= (φ e') <= 2 * Z.of_N (len u))%Z /\ hsrc U V e' = x)
    by (intros e' He'; apply HL; exact He').
  assert (Drive : forall b w, SE (toN z) b w -> ~ (toN f < cap /\ b = toN z + 1 /\ w = Prelude.get p (toN x))%N ->
            Qr L f b w).
  { intros b w (x0 & f0 & Hx0 & Hf0 & Ez0 & [Hb|(y & l & Hr & Hl & Eb & Ew)]) Hnb.
    - rewrite Ez in Ez0. destruct (decode cap _ _ _ _ Ez0 Hf Hf0) as [<- <-]. contradiction.
    - rewrite Ez in Ez0. destruct (decode cap _ _ _ _ Ez0 Hf Hf0) as [<- <-].
      subst b w. apply (drive_in z x f L Ez Hx HL y l Hr Hl). }
  destruct (f <? capi) eqn:Eb.
  - rewrite ltb_spec in Eb.
    assert (Hfc : (toN f < cap)%N) by (rewrite <- Hcapi; unfold toN; lia).
    assert (Tz1 : toN (z + 1) = (toN z + 1)%N) by (apply (succ_small z Ni Bzi HNi_small)).
    assert (Bz1 : ((φ (z + 1)) < (φ Ni))%Z).
    { assert (Hm1 : ((toN x + 1) * (cap + 1) <= n * (cap + 1))%N) by (apply N.mul_le_mono_r; lia).
      rewrite <- !toN_Z, Tz1, HNi, Ez. clear - Hm1 Hfc. lia. }
    assert (Hse : SE (toN z) (toN (z + 1)) (Prelude.get p (toN x))).
    { exists (toN x), (toN f). split; [exact Hx|]. split; [exact Hf|]. split; [exact Ez|].
      left. split; [exact Hfc|]. split; [exact Tz1 | reflexivity]. }
    assert (Tk : toN ((hkey h).[z] + P.[x]) = (kN h z + Prelude.get p (toN x))%N).
    { pose proof (Hp100 _ Hx) as Hp1. rewrite <- (HP x Hx) in *. unfold kN.
      pose proof (len_bound D Ni (di_Dnd _ _ _ _ _ _ HD0) (di_Drange _ _ _ _ _ _ HD0)) as LD.
      pose proof HNi_small as NS.
      apply add_small_N. unfold kN in Bz. rewrite <- !toN_Z. clear - Hp1 LD NS Bz. lia. }
    destruct (relax_spec h st D ns z _ (z + 1) ((hkey h).[z] + P.[x]) _ HD0 Hz Bz Bz1 Hse Tk)
      as (ns1 & HD1 & Hh1 & Hk1).
    apply (edges_spec L _ _ _ D ns1 z x f (hkey h).[z] Hc HL' Ez Hx Hf); [rewrite Hk1; reflexivity| | exact Hz |
      unfold kN; rewrite Hk1; exact Bz].
    apply (DIx_weaken _ _ _ _ _ _ _ HD1). intros b w Hs' _.
    destruct (N.eq_dec b (toN z + 1)) as [E1|E1].
    + destruct Hs' as (x0 & f0 & Hx0 & Hf0 & Ez0 & [(Hc0 & Eb0 & Ew0)|(y & l & Hr & Hl & Eb0 & Ew0)]);
        rewrite Ez in Ez0; destruct (decode cap _ _ _ _ Ez0 Hf Hf0) as [<- <-].
      * left. rewrite E1, <- Tz1, Ew0. exact Hh1.
      * right. subst b w. apply (drive_in z x f L Ez Hx HL y l Hr Hl).
    + right. apply Drive; [exact Hs'|]. intros (_ & F & _). contradiction.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Eb.
    apply (edges_spec L _ _ _ D ns z x f (hkey h).[z] Hc HL' Ez Hx Hf); [reflexivity| | exact Hz | exact Bz].
    apply (DIx_weaken _ _ _ _ _ _ _ HD0). intros b w Hs' _. right. apply Drive; [exact Hs'|].
    intros (F & _). rewrite <- Hcapi in F. unfold toN in F. lia.
Qed.

Lemma goal_notD : forall h st D ns z Q f', DIx h st D ns z Q -> (f' <= cap)%N ->
  forall x, toN x = (g * (cap + 1) + f')%N -> ~ In x D.
Proof.
  intros h st D ns z Q f' HD0 Hf x Ex Hx. apply (di_goal _ _ _ _ _ _ HD0 x Hx). rewrite Ex.
  apply div_state. lia.
Qed.

Lemma DN_bound : forall h st D ns z Q, DIx h st D ns z Q ->
  (Z.of_nat (List.length D) + Z.of_nat (List.length ns) <= (φ Ni))%Z.
Proof.
  intros h st D ns z Q HD0.
  pose proof (hi_core _ _ _ _ _ (di_heap _ _ _ _ _ _ HD0)) as C.
  assert (ND : NoDup (D ++ ns)).
  { apply NoDup_app; [exact (di_Dnd _ _ _ _ _ _ HD0) | exact (co_nodup _ _ _ _ C) |].
    intros a Ha Hb. pose proof (di_Drange _ _ _ _ _ _ HD0 a Ha) as Ba.
    destruct (di_st _ _ _ _ _ _ HD0 a Ba) as (S2 & S1 & _).
    apply i12. rewrite <- (proj2 S1 Hb). exact (proj2 S2 Ha). }
  pose proof (len_bound (D ++ ns) Ni ND) as L. rewrite length_app in L.
  assert (forall v, In v (D ++ ns) -> ((φ v) < (φ Ni))%Z).
  { intros w Hw. apply in_app_or in Hw. destruct Hw as [Hw|Hw];
      [exact (di_Drange _ _ _ _ _ _ HD0 w Hw) | exact (co_range _ _ _ _ C w Hw)]. }
  specialize (L H). lia.
Qed.

Lemma extract_step : forall h st D ns z0, DIx h st D ns z0 (fun _ _ => False) -> ns <> [] ->
  (toN (snd (fh_extract h)) / (cap + 1) <> g)%N ->
  DIx (fst (fh_extract h)) (st.[snd (fh_extract h) <- 2]) (snd (fh_extract h) :: D)
      (rem (snd (fh_extract h)) ns) (snd (fh_extract h)) (fun b w => SE (toN (snd (fh_extract h))) b w) /\
  (kN (fst (fh_extract h)) (snd (fh_extract h)) + 100 <=
     100 * N.of_nat (List.length (snd (fh_extract h) :: D)))%N.
Proof.
  intros h st D ns z0 HD0 Hne Hg.
  pose proof HD0 as [Hh Hl Hst Hnd Hr Hre Hmi He Hsr Hbo Hgo].
  destruct (extract_spec h Ni ns Hh Hne) as (Hz & Hmin & HI1 & K1).
  set (z := snd (fh_extract h)) in *. set (h1 := fst (fh_extract h)) in *.
  pose proof (co_range _ _ _ _ (hi_core _ _ _ _ _ Hh) z Hz) as Bz.
  assert (KN : forall y, kN h1 y = kN h y) by (intros y; unfold kN; rewrite K1; reflexivity).
  assert (HzD : ~ In z D).
  { intro F. destruct (Hst z Bz) as (S2 & S1 & _). apply i12. rewrite <- (proj2 S1 Hz). exact (proj2 S2 F). }
  assert (Mz : forall k, SP (toN srci) (toN z) k -> (kN h z <= k)%N).
  { intros k Hp. destruct (frontier h st D ns z0 HD0 (toN z) k Hp) as (y & Hy & Hk).
    - intros x Ex. apply toN_inj in Ex. subst x. exact HzD.
    - exact (N.le_trans _ _ _ (kv_kN _ _ _ (Hmin y Hy)) Hk). }
  split.
  - constructor.
    + exact HI1.
    + rewrite lset. exact Hl.
    + intros x Bx. destruct (Hst x Bx) as (S2 & S1 & S0). destruct (Uint63.eq_dec x z) as [E|E].
      * subst x. rewrite gss by (rewrite Hl; exact Bz). split; [split; [intros _; left; reflexivity | reflexivity]|].
        split; [split; [intro F; exfalso; exact (i12 (eq_sym F)) | intro F; apply rem_In in F; tauto]|].
        right; right; reflexivity.
      * rewrite gso by exact E. split; [|split; [|exact S0]].
        -- rewrite S2. split; [intro F; right; exact F | intros [F|F]; [congruence | exact F]].
        -- rewrite S1, rem_In. tauto.
    + constructor; assumption.
    + intros x [E|Hx]; [subst; exact Bz | apply Hr; exact Hx].
    + intros x Hx. rewrite KN. apply Hre. destruct Hx as [[E|Hx]|Hx];
        [subst; right; exact Hz | left; exact Hx | apply rem_In in Hx; right; tauto].
    + intros x [E|Hx] k Hp; rewrite KN; [subst x; apply Mz; exact Hp | apply Hmi; assumption].
    + intros a [E|Ha] b w Hs'; [right; split; [exact (eq_sym E) | rewrite E; exact Hs']|].
      destruct (He a Ha b w Hs') as [(x' & Ex' & Hx')|[_ []]]; left.
      exists x'. split; [exact Ex'|]. rewrite !KN.
      destruct Hx' as [Hx'|[Hx' Hk]]; [left; right; exact Hx'|].
      destruct (Uint63.eq_dec x' z) as [E|E]; [left; left; exact (eq_sym E)|].
      right. split; [apply rem_In; tauto | exact Hk].
    + destruct Hsr as [F|[F1 F2]]; [left; right; exact F|].
      destruct (Uint63.eq_dec srci z) as [E|E]; [left; left; exact (eq_sym E)|].
      right. split; [apply rem_In; tauto | rewrite KN; exact F2].
    + intros x Hx. rewrite KN. cbn [List.length]. rewrite Nat2N.inj_succ.
      assert (Hx' : In x D \/ In x ns) by (destruct Hx as [[E|F]|F]; [subst; right; exact Hz | left; exact F | apply rem_In in F; right; tauto]).
      pose proof (Hbo x Hx'). lia.
    + intros x [E|Hx]; [subst x; exact Hg | apply Hgo; exact Hx].
  - rewrite KN. cbn [List.length]. rewrite Nat2N.inj_succ. pose proof (Hbo z (or_intror Hz)). lia.
Qed.

Definition Rel (r : option int) : Prop :=
  match r with
  | Some k => (exists f', (f' <= cap)%N /\ SP (toN srci) (g * (cap + 1) + f') (toN k)) /\
              (forall f' k', (f' <= cap)%N -> SP (toN srci) (g * (cap + 1) + f') k' -> (toN k <= k')%N)
  | None => forall f' k', (f' <= cap)%N -> ~ SP (toN srci) (g * (cap + 1) + f') k'
  end.

Lemma dijk_eq : forall C cp gg hs cnt H, dijk P U V Dl head nxt C cp gg hs cnt H =
  if hmin (fst hs) =? nil then None
  else
    match bdec (0 <? cnt) with
    | left Hc =>
        let r := fh_extract (fst hs) in
        let z := snd r in
        let st1 := (snd hs).[z <- 2] in
        if z / C =? gg then Some (hkey (fst r)).[z]
        else dijk P U V Dl head nxt C cp gg
               (expand P U V Dl head nxt C cp (fst r, st1) z) (cnt - 1)
               (Acc_inv H (dec_cnt cnt Hc))
    | right _ => None
    end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma dijk_spec : forall zc cnt (H : Acc (Zwf 0) (φ cnt)) hs D ns z,
  (φ cnt) = zc -> DIx (fst hs) (snd hs) D ns z (fun _ _ => False) ->
  ((φ cnt) + Z.of_nat (List.length D) = (φ Ni))%Z ->
  Rel (dijk P U V Dl head nxt Ci capi gi hs cnt H).
Proof.
  intros zc. induction zc as [zc IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros cnt H hs D ns z Hz HD0 Hc.
  rewrite dijk_eq. destruct (hmin (fst hs) =? nil) eqn:Em.
  - apply eqb_spec in Em. apply (HI_empty _ _ _ (di_heap _ _ _ _ _ _ HD0)) in Em. subst ns.
    cbn. intros f' k' Hf Hp.
    destruct (frontier _ _ _ _ _ HD0 _ _ Hp (goal_notD _ _ _ _ _ _ f' HD0 Hf)) as (y & [] & _).
  - apply eqb_false_spec in Em.
    assert (Hne : ns <> []) by (intro E; apply Em; apply (HI_empty _ _ _ (di_heap _ _ _ _ _ _ HD0)); exact E).
    pose proof (DN_bound _ _ _ _ _ _ HD0) as DB.
    assert (Hcp : (0 < (φ cnt))%Z) by (destruct ns; [congruence | cbn [List.length] in DB; lia]).
    destruct (bdec (0 <? cnt)) as [Hc'|Hc'];
      [| exfalso; rewrite <- Bool.not_true_iff_false, ltb_spec in Hc'; change (φ 0) with 0%Z in Hc'; lia].
    cbv zeta.
    destruct (extract_spec (fst hs) Ni ns (di_heap _ _ _ _ _ _ HD0) Hne) as (Hzz & Hmin & HI1 & K1).
    set (zz := snd (fh_extract (fst hs))) in *.
    pose proof (co_range _ _ _ _ (hi_core _ _ _ _ _ (di_heap _ _ _ _ _ _ HD0)) zz Hzz) as Bzz.
    destruct (state_split zz Bzz) as (Ez & Hx & Hf).
    destruct (zz / Ci =? gi) eqn:Eg.
    + apply eqb_spec in Eg. cbn [Rel]. rewrite K1. rewrite Eg, Hgi in Ez.
      split.
      * exists (toN (zz mod Ci)). split; [exact Hf|]. rewrite <- Ez.
        apply (di_reach _ _ _ _ _ _ HD0). right. exact Hzz.
      * intros f' k' Hf' Hp.
        destruct (frontier _ _ _ _ _ HD0 _ _ Hp (goal_notD _ _ _ _ _ _ f' HD0 Hf')) as (y & Hy & Hk).
        exact (N.le_trans _ _ _ (kv_kN _ _ _ (Hmin y Hy)) Hk).
    + apply eqb_false_spec in Eg.
      assert (Hg' : (toN zz / (cap + 1) <> g)%N).
      { intro F. apply Eg. apply toN_inj. rewrite Hgi. rewrite <- F, Ez.
        symmetry. apply div_state. lia. }
      destruct (extract_step _ _ _ _ _ HD0 Hne Hg') as [HD1 B1].
      fold zz in HD1, B1.
      destruct (expand_spec _ _ _ _ _ HD1 (or_introl eq_refl) B1) as (ns2 & HD2).
      apply (IH (φ (cnt - 1)) ltac:(rewrite <- Hz; apply dec_cnt; exact Hc') (cnt - 1)
               _ _ (zz :: D) ns2 zz eq_refl HD2).
      cbn [List.length]. assert ((φ (cnt - 1)) = (φ cnt) - 1)%Z by sia. lia.
Qed.

End Dijkstra.

(* ------------------------------------------------------------------ *)
(* The forward star                                                    *)
(* ------------------------------------------------------------------ *)

Lemma hchain_frame : forall nxt nxt' l e, hchain nxt e l ->
  (forall i, In i l -> nxt'.[i] = nxt.[i]) -> hchain nxt' e l.
Proof.
  intros nxt nxt' l. induction l as [| a t IH]; intros e Hc Hf; cbn [hchain] in *; [exact Hc|].
  destruct Hc as (E & Hne & Hlt & Hc). rewrite Hf by (left; exact (eq_sym E)).
  split; [exact E|]. split; [exact Hne|]. split; [exact Hlt|]. apply IH; [exact Hc|].
  intros i Hi. apply Hf. right. exact Hi.
Qed.

Lemma hchain_head : forall nxt l e, hchain nxt e l -> e = 0 \/ In e l.
Proof. intros nxt [| a t] e Hc; cbn [hchain] in Hc; [left; exact Hc | right; left; symmetry; apply Hc]. Qed.

Definition FSinv (U V head nxt : array int) (n : N) (B : Z) : Prop :=
  forall x : int, (toN x < n)%N -> exists l, hchain nxt head.[x] l /\
    forall e, In e l <-> ((1 <= (φ e) <= B)%Z /\ hsrc U V e = x).

Lemma fs_push : forall U V head nxt n B e a,
  FSinv U V head nxt n B -> (φ e) = (B + 1)%Z -> (0 <= B)%Z -> hsrc U V e = a -> (toN a < n)%N ->
  ((φ e) < (φ (PArray.length nxt)))%Z -> (Z.of_N n <= (φ (PArray.length head)))%Z ->
  FSinv U V (head.[a <- e]) (nxt.[e <- head.[a]]) n (B + 1).
Proof.
  intros U V head nxt n B e a HF He HB Hs Ha Bn Bh x Hx.
  destruct (HF x Hx) as (l & Hc & Hm).
  assert (Hle : forall i, In i l -> ((φ i) <= B)%Z) by (intros i Hi; apply Hm in Hi; lia).
  assert (Fr : forall i, In i l -> (nxt.[e <- head.[a]]).[i] = nxt.[i]).
  { intros i Hi. apply gso. intro E. subst i. pose proof (Hle e Hi). lia. }
  assert (Ba : ((φ a) < (φ (PArray.length head)))%Z) by (pose proof (toN_Z a); lia).
  destruct (Uint63.eq_dec x a) as [E|E].
  - subst x. exists (e :: l). split.
    + cbn [hchain]. rewrite gss by exact Ba. split; [reflexivity|].
      split; [intro F; subst e; change (φ 0) with 0%Z in He; lia|].
      rewrite gss by exact Bn. split.
      * destruct (hchain_head _ _ _ Hc) as [F|F]; [rewrite F; change (φ 0) with 0%Z; lia|].
        pose proof (Hle _ F). lia.
      * apply (hchain_frame nxt); assumption.
    + intros e'. split.
      * intros [F|F]; [subst e'; split; [lia | exact Hs]|]. apply Hm in F. destruct F as [F1 F2]. split; [lia | exact F2].
      * intros [F1 F2]. destruct (Z.eq_dec (φ e') (B + 1)) as [F|F].
        -- left. apply to_Z_inj. lia.
        -- right. apply Hm. split; [lia | exact F2].
  - exists l. split.
    + rewrite gso by exact E. apply (hchain_frame nxt); assumption.
    + intros e'. rewrite Hm. split.
      * intros [F1 F2]. split; [lia | exact F2].
      * intros [F1 F2]. split; [|exact F2]. destruct (Z.eq_dec (φ e') (B + 1)) as [F|F]; [|lia].
        exfalso. assert (e' = e) by (apply to_Z_inj; lia). subst e'. congruence.
Qed.

Lemma build_eq : forall U V head nxt j m H, build U V head nxt j m H =
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
Proof. intros. destruct H. reflexivity. Qed.

Lemma build_spec : forall (U V : array int) (n : N) (m : int) z j (H : Acc (Zwf 0) (gap m j)) head nxt,
  gap m j = z -> ((φ m) <= 10000)%Z -> ((φ j) <= (φ m))%Z ->
  (forall k : int, ((φ k) < (φ m))%Z -> (toN U.[k] < n /\ toN V.[k] < n)%N) ->
  PArray.length nxt = 2 * m + 1 -> (Z.of_N n <= (φ (PArray.length head)))%Z ->
  FSinv U V head nxt n (2 * (φ j))%Z ->
  FSinv U V (fst (build U V head nxt j m H)) (snd (build U V head nxt j m H)) n (2 * (φ m))%Z.
Proof.
  intros U V n m z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j H head nxt Hz Hm Hj Hends Ln Lh HF.
  rewrite build_eq. destruct (bdec (j <? m)) as [Hjm|Hjm].
  - pose proof Hjm as Hjm'. rewrite ltb_spec in Hjm'. cbv zeta.
    destruct (he_idx j ltac:(lia)) as (M1 & D1 & M2 & D2 & P1 & P2).
    destruct (Hends j Hjm') as [Hu Hv].
    assert (Ln' : (φ (PArray.length nxt)) = (2 * (φ m) + 1)%Z) by (rewrite Ln; pose proof (to_Z_bounded m); sia).
    assert (S1 : hsrc U V (2 * j + 1) = U.[j]) by (unfold hsrc; rewrite M1, D1; reflexivity).
    assert (S2 : hsrc U V (2 * j + 2) = V.[j]) by (unfold hsrc; rewrite M2, D2; reflexivity).
    pose proof (fs_push U V head nxt n (2 * (φ j))%Z (2 * j + 1) U.[j] HF ltac:(rewrite P1; lia)
                  ltac:(pose proof (to_Z_bounded j); lia) S1 Hu ltac:(rewrite P1, Ln'; lia) Lh) as HF1.
    pose proof (fs_push U V _ _ n (2 * (φ j) + 1)%Z (2 * j + 2) V.[j] HF1 ltac:(rewrite P2; lia)
                  ltac:(pose proof (to_Z_bounded j); lia) S2 Hv
                  ltac:(rewrite lset, P2, Ln'; lia) ltac:(rewrite lset; exact Lh)) as HF2.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    apply (IH (gap m (j + 1))); [rewrite <- Hz; apply dec_step; exact Hjm | reflexivity | exact Hm | lia
           | exact Hends | rewrite !lset; exact Ln | rewrite !lset; exact Lh |].
    rewrite Hj1. replace (2 * ((φ j) + 1))%Z with (2 * (φ j) + 1 + 1)%Z by lia. exact HF2.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hjm. cbn [fst snd].
    replace (φ m) with (φ j) by lia. exact HF.
Qed.

(* ------------------------------------------------------------------ *)
(* One query                                                           *)
(* ------------------------------------------------------------------ *)

Lemma HI_init : forall N : int, ((φ N) <= 4194303)%Z ->
  HI (FH (PArray.make N 0) (PArray.make N nil) (PArray.make N nil) (PArray.make N nil)
         (PArray.make N nil) (PArray.make N 0) (PArray.make N 0) (PArray.make N nil) nil) N [] nil nil.
Proof.
  intros N HN. constructor.
  - constructor.
    + unfold lens; sx. rewrite !lmake by exact HN. tauto.
    + constructor.
    + intros v [].
    + intros q [].
    + intros w [].
    + exists (fun _ => O). intros w [].
  - intros w [].
  - intros i _. sx. apply gmake.
  - exists []. split; [constructor|]. split; [intros w; split; [intros []| intros [[] _]]|].
    left. sx. split; reflexivity.
Qed.

Lemma query_correct : forall (n : N) (p u v d : list N) (P U V Dl head nxt : array int)
    (ni capi si gi : int),
  toN ni = n -> (n <= 1000)%N -> (len u <= 10000)%N -> len v = len u -> len d = len u ->
  (forall j, (j < len u)%N -> (Prelude.get u j < n /\ Prelude.get v j < n)%N) ->
  (forall x, (x < n)%N -> (Prelude.get p x <= 100)%N) ->
  (toN capi <= 100)%N -> (toN si < n)%N -> (toN gi < n)%N ->
  (forall x : int, (toN x < n)%N -> toN P.[x] = Prelude.get p (toN x)) ->
  (forall j : int, (toN j < len u)%N -> toN U.[j] = Prelude.get u (toN j)) ->
  (forall j : int, (toN j < len u)%N -> toN V.[j] = Prelude.get v (toN j)) ->
  (forall j : int, (toN j < len u)%N -> toN Dl.[j] = Prelude.get d (toN j)) ->
  (forall x : int, (toN x < n)%N -> exists l, hchain nxt head.[x] l /\
     forall e, In e l <-> ((1 <= (φ e) <= 2 * Z.of_N (len u))%Z /\ hsrc U V e = x)) ->
  answer p u v d (toN capi) (toN si) (toN gi)
    (option_map toN (query ni P U V Dl head nxt capi si gi)).
Proof.
  intros n p u v d P U V Dl head nxt ni capi si gi Hni Hn Hm Hlv Hld Hends Hp Hcap Hs Hg HP HU HV HD HFS.
  set (cap := toN capi) in *.
  assert (TC : toN (capi + 1) = (cap + 1)%N).
  { unfold cap, toN in *. rewrite add_spec. change (φ 1) with 1%Z. pose proof (to_Z_bounded capi).
    rewrite Z.mod_small; [lia|]. rewrite wB_val. lia. }
  assert (TN : toN (ni * (capi + 1)) = (n * (cap + 1))%N).
  { rewrite <- TC, <- Hni. apply N2Z.inj. rewrite N2Z.inj_mul, !toN_Z. rewrite mul_spec.
    apply Z.mod_small. rewrite <- !toN_Z, TC, Hni. rewrite wB_val. nia. }
  assert (TS : toN (si * (capi + 1)) = (toN si * (cap + 1))%N).
  { rewrite <- TC. apply N2Z.inj. rewrite N2Z.inj_mul, !toN_Z. rewrite mul_spec.
    apply Z.mod_small. rewrite <- !toN_Z, TC. rewrite wB_val. nia. }
  set (Ci := capi + 1) in *. set (Ni := ni * Ci) in *. set (srci := si * Ci) in *.
  assert (BN : ((φ Ni) <= 101000)%Z) by (rewrite <- toN_Z, TN; nia).
  assert (Bs : ((φ srci) < (φ Ni))%Z).
  { rewrite <- !toN_Z, TS, TN.
    assert (((toN si + 1) * (cap + 1) <= n * (cap + 1))%N) by (apply N.mul_le_mono_r; lia). lia. }
  unfold query. cbv zeta. fold Ci Ni srci.
  set (h0 := FH (PArray.make Ni 0) (PArray.make Ni nil) (PArray.make Ni nil) (PArray.make Ni nil)
         (PArray.make Ni nil) (PArray.make Ni 0) (PArray.make Ni 0) (PArray.make Ni nil) nil).
  pose proof (HI_init Ni ltac:(lia)) as HI0. fold h0 in HI0.
  destruct (insert_spec h0 Ni [] srci 0 HI0 (fun F => F) Bs) as [HI1 K1].
  assert (K0 : forall x, (hkey (fh_insert h0 srci 0)).[x] = 0).
  { intros x. rewrite K1. unfold h0; sx. destruct (Uint63.eq_dec x srci) as [E|E].
    - subst. apply gss. rewrite lmake by lia. exact Bs.
    - rewrite gso by exact E. apply gmake. }
  assert (HD0 : DIx n p u v d cap (toN gi) Ni srci (fh_insert h0 srci 0) ((PArray.make Ni 0).[srci <- 1])
                    [] [srci] srci (fun _ _ => False)).
  { constructor.
    - exact HI1.
    - rewrite lset, lmake by lia. reflexivity.
    - intros x Bx. destruct (Uint63.eq_dec x srci) as [E|E].
      + subst x. rewrite gss by (rewrite lmake by lia; exact Bs).
        split; [split; [intro F; exfalso; exact (i12 F) | intros []]|].
        split; [split; [intros _; left; reflexivity | reflexivity]|]. right; left; reflexivity.
      + rewrite gso by exact E. rewrite gmake.
        split; [split; [intro F; exfalso; exact (i02 F) | intros []]|].
        split; [split; [intro F; exfalso; exact (i01 F) | intros [F|[]]; congruence]|]. left; reflexivity.
    - constructor.
    - intros x [].
    - intros x [[]|[E|[]]]. subst x. unfold kN. rewrite K0. apply sp_nil.
    - intros x [].
    - intros a [].
    - right. split; [left; reflexivity|]. unfold kN. rewrite K0. reflexivity.
    - intros x _. unfold kN. rewrite K0. cbn. lia.
    - intros x []. }
  pose proof (dijk_spec n p u v d cap (toN gi) (toN si) Hends Hp Hcap Hn Hm Hlv Hld Hs Hg
                P U V Dl head nxt capi Ci Ni gi srci eq_refl eq_refl TN eq_refl TS HP HU HV HD HFS
                _ Ni (Zwf_well_founded 0 (φ Ni)) (fh_insert h0 srci 0, (PArray.make Ni 0).[srci <- 1])
                [] [srci] srci eq_refl HD0 ltac:(cbn; lia)) as R.
  apply (answer_of_paths n p u v d cap (toN gi) Hends (toN si) _ Hs).
  destruct (dijk P U V Dl head nxt Ci capi gi _ Ni _) as [k|]; unfold Rel in R; cbn [option_map];
    rewrite TS in R; exact R.
Qed.

(* ------------------------------------------------------------------ *)
(* Reading the inputs, writing the output                              *)
(* ------------------------------------------------------------------ *)

Lemma repr_len_u : forall (x : array uint) (l : list N), repr x l -> toN (PArray.length x) = len l.
Proof.
  intros x l [Hl _].
  assert (E : (φ (PArray.length x)) = Z.of_nat (List.length l)) by exact (eq_sym Hl).
  unfold toN, len. rewrite E. lia.
Qed.

Lemma repr_get_u : forall (x : array uint) (l : list N), repr x l ->
  forall i : int, (toN i < len l)%N -> toN x.[i] = Prelude.get l (toN i).
Proof.
  intros x l [_ Hc] i Hi. unfold len in Hi.
  destruct (Hc (N.to_nat (toN i)) ltac:(lia)) as (m & Hm & Hr).
  assert (Ei : of_nat (N.to_nat (toN i)) = i).
  { apply to_Z_inj. rewrite of_Z_spec. unfold toN. pose proof (to_Z_bounded i).
    rewrite Z.mod_small; rewrite ?wB_val; lia. }
  rewrite Ei in Hr. unfold repr, repr_uint in Hr.
  assert (E : toN x.[i] = m) by exact Hr.
  rewrite E. unfold Prelude.get. symmetry. apply nth_error_nth. exact Hm.
Qed.

Lemma gsoO : forall (t : array (option int)) (i j : int) (a : option int),
  i <> j -> t.[j <- a].[i] = t.[i].
Proof. intros t i j a H. exact (get_set_other (option int) t j i a (fun E => H (eq_sym E))). Qed.

Lemma gssO : forall (t : array (option int)) (i : int) (a : option int),
  ((φ i) < (φ (PArray.length t)))%Z -> t.[i <- a].[i] = a.
Proof. intros t i a H. apply (get_set_same (option int) t i a). rewrite ltb_spec. exact H. Qed.

Lemma lsetO : forall (t : array (option int)) (i : int) (a : option int),
  PArray.length t.[i <- a] = PArray.length t.
Proof. intros t i a. exact (length_set (option int) t i a). Qed.

Lemma lmakeO : forall (n : int) (a : option int),
  ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n a) = n.
Proof.
  intros n a H.
  transitivity (if n ≤? max_length then n else max_length); [exact (length_make (option int) n a)|].
  replace (n ≤? max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec. change (φ max_length) with 4194303%Z. exact H.
Qed.

Lemma qloop_eq : forall n P U V Dl head nxt Cs Ss Es out i q H,
  qloop n P U V Dl head nxt Cs Ss Es out i q H =
  match bdec (i <? q) with
  | left Hi =>
      qloop n P U V Dl head nxt Cs Ss Es
        out.[i <- query n P U V Dl head nxt Cs.[i] Ss.[i] Es.[i]] (i + 1) q
        (Acc_inv H (dec_step q i Hi))
  | right _ => out
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma qloop_spec : forall n P U V Dl head nxt Cs Ss Es q z i out H,
  gap q i = z -> PArray.length out = q -> ((φ i) <= (φ q))%Z ->
  (forall k, ((φ k) < (φ i))%Z -> out.[k] = query n P U V Dl head nxt Cs.[k] Ss.[k] Es.[k]) ->
  PArray.length (qloop n P U V Dl head nxt Cs Ss Es out i q H) = q /\
  forall k, ((φ k) < (φ q))%Z ->
    (qloop n P U V Dl head nxt Cs Ss Es out i q H).[k] = query n P U V Dl head nxt Cs.[k] Ss.[k] Es.[k].
Proof.
  intros n P U V Dl head nxt Cs Ss Es q z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i out H Hz Hl Hi Hc. rewrite qloop_eq. destruct (bdec (i <? q)) as [Hq|Hq].
  - pose proof Hq as Hq'. rewrite ltb_spec in Hq'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    apply (IH (gap q (i + 1))); [rewrite <- Hz; apply dec_step; exact Hq | reflexivity | rewrite lsetO; exact Hl | lia |].
    intros k Hk. destruct (Uint63.eq_dec k i) as [E|E].
    + subst k. apply gssO. rewrite Hl. exact Hq'.
    + rewrite gsoO by exact E. apply Hc. assert ((φ k) <> (φ i)) by (intro F; apply E; apply to_Z_inj; exact F). lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hq. split; [exact Hl|].
    intros k Hk. apply Hc. lia.
Qed.

Lemma z2n2z : forall x : int, Z.of_nat (Z.to_nat (φ x)) = (φ x).
Proof. intros x. pose proof (to_Z_bounded x). lia. Qed.

Lemma repr_out : forall (out : array (option int)),
  repr (out : array (option uint))
       (map (fun k => option_map toN out.[of_nat k]) (seq 0 (Z.to_nat (φ (PArray.length out))))).
Proof.
  intros out. split.
  - rewrite length_map, length_seq. apply z2n2z.
  - intros k Hk. rewrite length_map, length_seq in Hk.
    exists (option_map toN out.[of_nat k]). split.
    + rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec k (Z.to_nat (φ (PArray.length out)))); [reflexivity | lia].
    + change (PArray.get@{repr_array.u0} out (of_nat k)) with (out.[of_nat k]).
      destruct (out.[of_nat k]) as [a|]; cbn; reflexivity.
Qed.

Lemma Forall_get : forall (P : N -> Prop) (l : list N) j, Forall P l -> (j < len l)%N -> P (Prelude.get l j).
Proof.
  intros P l j H Hj. unfold Prelude.get, len in *. rewrite Forall_forall in H. apply H.
  apply nth_In. lia.
Qed.

Lemma fulltank_impl_correct : forall (n : N) (p u v d c s e : list N)
    (xn : uint) (xp xu xv xd xc xs xe : array uint),
  valid_input n p u v d c s e ->
  repr xn n -> repr xp p -> repr xu u -> repr xv v -> repr xd d ->
  repr xc c -> repr xs s -> repr xe e ->
  exists o : list (option N),
    repr (fulltank_impl xn xp xu xv xd xc xs xe) o /\ fulltank_spec n p u v d c s e o.
Proof.
  intros n p u v d c s e xn xp xu xv xd xc xs xe Hv Rn Rp Ru Rv Rd Rc Rs Re.
  destruct Hv as [Vn Vpl Vp Vm Vvl Vdl Vu Vv Vd Vq Vsl Vel Vc Vs Ve].
  assert (Tn : toN xn = n) by exact Rn.
  pose proof (repr_len_u _ _ Ru) as Lu. pose proof (repr_len_u _ _ Rc) as Lc.
  assert (HP : forall x : int, (toN x < n)%N -> toN xp.[x] = Prelude.get p (toN x))
    by (intros x Hx; apply (repr_get_u xp p Rp); rewrite Vpl; exact Hx).
  assert (HU : forall j : int, (toN j < len u)%N -> toN xu.[j] = Prelude.get u (toN j))
    by (intros j Hj; apply (repr_get_u xu u Ru); exact Hj).
  assert (HV : forall j : int, (toN j < len u)%N -> toN xv.[j] = Prelude.get v (toN j))
    by (intros j Hj; apply (repr_get_u xv v Rv); rewrite Vvl; exact Hj).
  assert (HD : forall j : int, (toN j < len u)%N -> toN xd.[j] = Prelude.get d (toN j))
    by (intros j Hj; apply (repr_get_u xd d Rd); rewrite Vdl; exact Hj).
  assert (HC : forall j : int, (toN j < len c)%N -> toN xc.[j] = Prelude.get c (toN j))
    by (intros j Hj; apply (repr_get_u xc c Rc); exact Hj).
  assert (HS : forall j : int, (toN j < len c)%N -> toN xs.[j] = Prelude.get s (toN j))
    by (intros j Hj; apply (repr_get_u xs s Rs); rewrite Vsl; exact Hj).
  assert (HE : forall j : int, (toN j < len c)%N -> toN xe.[j] = Prelude.get e (toN j))
    by (intros j Hj; apply (repr_get_u xe e Re); rewrite Vel; exact Hj).
  assert (Hends : forall j, (j < len u)%N -> (Prelude.get u j < n /\ Prelude.get v j < n)%N).
  { intros j Hj. split; [apply (Forall_get (fun x => x < n)%N u j Vu Hj)|].
    apply (Forall_get (fun x => x < n)%N v j Vv). rewrite Vvl. exact Hj. }
  assert (Hp100 : forall x, (x < n)%N -> (Prelude.get p x <= 100)%N).
  { intros x Hx. pose proof (Forall_get (fun x => 1 <= x <= 100)%N p x Vp ltac:(rewrite Vpl; exact Hx)) as F.
    cbv beta in F. lia. }
  assert (Bn : ((φ xn) <= 1000)%Z) by (rewrite <- toN_Z, Tn; lia).
  assert (Bm : ((φ (PArray.length xu)) <= 10000)%Z) by (rewrite <- toN_Z, Lu; lia).
  unfold fulltank_impl. cbv zeta.
  set (m := PArray.length xu) in *.
  assert (Lnxt : PArray.length (PArray.make (2 * m + 1) 0) = 2 * m + 1).
  { apply lmake. pose proof (to_Z_bounded m). sia. }
  assert (Lhd : (Z.of_N n <= (φ (PArray.length (PArray.make xn 0%uint63))))%Z).
  { assert (E : PArray.length (PArray.make xn 0) = xn) by (exact (lmake xn 0 ltac:(lia))).
    rewrite E. rewrite <- Tn, toN_Z. lia. }
  assert (Hends' : forall k : int, ((φ k) < (φ m))%Z -> (toN xu.[k] < n /\ toN xv.[k] < n)%N).
  { intros k Hk. assert (Hk' : (toN k < len u)%N) by (rewrite <- Lu; unfold toN; lia).
    rewrite HU, HV by exact Hk'. apply Hends; exact Hk'. }
  pose proof (build_spec xu xv n m _ 0 (Zwf_well_founded 0 (gap m 0)) (PArray.make xn 0)
                (PArray.make (2 * m + 1) 0) eq_refl Bm ltac:(change (φ 0) with 0%Z; apply to_Z_bounded)
                Hends'
                Lnxt Lhd
                ltac:(intros x _; exists []; split; [apply gmake|];
                      intros e'; split; [intros []|]; change (φ 0) with 0%Z; lia)) as HF.
  set (bld := build xu xv (PArray.make xn 0) (PArray.make (2 * m + 1) 0) 0 m _) in *.
  assert (HFS : forall x : int, (toN x < n)%N -> exists l, hchain (snd bld) (fst bld).[x] l /\
     forall e', In e' l <-> ((1 <= (φ e') <= 2 * Z.of_N (len u))%Z /\ hsrc xu xv e' = x)).
  { intros x Hx. rewrite <- Lu, toN_Z. exact (HF x Hx). }
  set (q := PArray.length xc) in *.
  destruct (qloop_spec xn xp xu xv xd (fst bld) (snd bld) xc xs xe q _ 0 (PArray.make q None)
              (Zwf_well_founded 0 (gap q 0)) eq_refl ltac:(apply lmakeO; unfold q; exact (lbound xc))
              ltac:(change (φ 0) with 0%Z; apply to_Z_bounded)
              ltac:(intros k Hk; change (φ 0) with 0%Z in Hk; pose proof (to_Z_bounded k); lia))
    as [Lr Hr].
  set (r := qloop xn xp xu xv xd (fst bld) (snd bld) xc xs xe (PArray.make q None) 0 q _) in *.
  exists (map (fun k => option_map toN r.[of_nat k]) (seq 0 (Z.to_nat (φ (PArray.length r))))).
  split; [apply repr_out|].
  split.
  - unfold len in Lc |- *. rewrite length_map, length_seq, Lr. rewrite <- Lc. unfold toN. lia.
  - intros i Hi.
    assert (Hi' : (N.to_nat i < Z.to_nat (φ (PArray.length r)))%nat) by (rewrite Lr, <- toN_Z, Lc in *; unfold len in *; lia).
    erewrite nth_error_nth; [|rewrite nth_error_map, nth_error_seq;
      destruct (Nat.ltb_spec (N.to_nat i) (Z.to_nat (φ (PArray.length r)))); [reflexivity | lia]].
    cbn [Nat.add option_map].
    set (k := of_Z (Z.of_nat (N.to_nat i))).
    assert (Tk : toN k = i).
    { unfold k. replace (Z.of_nat (N.to_nat i)) with (Z.of_N i) by lia. apply of_N_toN.
      unfold len in *. lia. }
    assert (Hk' : (toN k < len c)%N) by (rewrite Tk; exact Hi).
    assert (Bk : ((φ k) < (φ q))%Z) by (rewrite <- !toN_Z, Tk, Lc; unfold len in *; lia).
    rewrite (Hr k Bk).
    rewrite <- Tk. rewrite <- (HC k Hk'), <- (HS k Hk'), <- (HE k Hk').
    assert (Bc : (1 <= toN xc.[k] <= 100)%N)
      by (rewrite (HC k Hk'); exact (Forall_get (fun x => 1 <= x <= 100)%N c _ Vc Hk')).
    assert (Bs : (toN xs.[k] < n)%N)
      by (rewrite (HS k Hk'); apply (Forall_get (fun x => x < n)%N s _ Vs); rewrite Vsl; exact Hk').
    assert (Be : (toN xe.[k] < n)%N)
      by (rewrite (HE k Hk'); apply (Forall_get (fun x => x < n)%N e _ Ve); rewrite Vel; exact Hk').
    apply (query_correct n p u v d xp xu xv xd (fst bld) (snd bld) xn xc.[k] xs.[k] xe.[k]
             Tn ltac:(lia) Vm Vvl Vdl Hends Hp100 ltac:(lia) Bs Be HP HU HV HD HFS).
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition fulltank : uint -> array uint -> array uint -> array uint ->
  array uint -> array uint -> array uint -> array uint ->
  array (option uint) := fulltank_impl.

Definition fulltank_correct :
  forall (n : N) (p u v d c s e : list N)
         (xn : uint) (xp xu xv xd xc xs xe : array uint),
  valid_input n p u v d c s e ->
  repr xn n -> repr xp p -> repr xu u -> repr xv v -> repr xd d ->
  repr xc c -> repr xs s -> repr xe e ->
  exists o : list (option N),
    repr (fulltank xn xp xu xv xd xc xs xe) o /\
    fulltank_spec n p u v d c s e o
  := fulltank_impl_correct.
